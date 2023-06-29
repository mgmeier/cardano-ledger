{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Epoch (
  ConwayEPOCH,
  PredicateFailure,
  ConwayEpochEvent (..),
)
where

import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.CertState (certDStateL, dsUnifiedL)
import Cardano.Ledger.Compactible (Compactible (..))
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Era (ConwayEPOCH)
import Cardano.Ledger.Conway.Governance (ConwayGovernance (..), GovernanceActionId, GovernanceActionState (..), RatifyState (..), cgPropDepositsL)
import Cardano.Ledger.Credential (Credential (..))
import Cardano.Ledger.EpochBoundary (SnapShots)
import Cardano.Ledger.Shelley.LedgerState (
  CertState (..),
  EpochState,
  LedgerState (..),
  PState (..),
  UTxOState (..),
  asReserves,
  esAccountState,
  esLState,
  esNonMyopic,
  esPp,
  esPrevPp,
  esSnapshots,
  lsCertState,
  lsCertStateL,
  lsUTxOState,
  lsUTxOStateL,
  obligationCertState,
  utxosGovernanceL,
  pattern EpochState,
 )
import Cardano.Ledger.Shelley.Rewards ()
import Cardano.Ledger.Shelley.Rules (
  ShelleyEpochPredFailure (..),
  ShelleyPOOLREAP,
  ShelleyPoolreapEvent,
  ShelleyPoolreapPredFailure,
  ShelleyPoolreapState (..),
  ShelleySNAP,
  ShelleySnapPredFailure,
  SnapEnv (..),
  UpecPredFailure,
 )
import qualified Cardano.Ledger.Shelley.Rules as Shelley
import Cardano.Ledger.Slot (EpochNo)
import Cardano.Ledger.UMap (UMap, UView (..), (∪+))
import Control.SetAlgebra (eval, (⨃))
import Control.State.Transition (
  Embed (..),
  STS (..),
  TRC (..),
  TransitionRule,
  judgmentContext,
  trans,
 )
import Data.Foldable (Foldable (..))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Set as Set
import Lens.Micro ((%~), (&))

data ConwayEpochEvent era
  = PoolReapEvent (Event (EraRule "POOLREAP" era))
  | SnapEvent (Event (EraRule "SNAP" era))

instance
  ( EraTxOut era
  , EraGovernance era
  , Embed (EraRule "SNAP" era) (ConwayEPOCH era)
  , Environment (EraRule "SNAP" era) ~ SnapEnv era
  , State (EraRule "SNAP" era) ~ SnapShots (EraCrypto era)
  , Signal (EraRule "SNAP" era) ~ ()
  , Embed (EraRule "POOLREAP" era) (ConwayEPOCH era)
  , Environment (EraRule "POOLREAP" era) ~ PParams era
  , State (EraRule "POOLREAP" era) ~ ShelleyPoolreapState era
  , Signal (EraRule "POOLREAP" era) ~ EpochNo
  , Eq (UpecPredFailure era)
  , Show (UpecPredFailure era)
  , GovernanceState era ~ ConwayGovernance era
  ) =>
  STS (ConwayEPOCH era)
  where
  type State (ConwayEPOCH era) = EpochState era
  type Signal (ConwayEPOCH era) = EpochNo
  type Environment (ConwayEPOCH era) = ()
  type BaseM (ConwayEPOCH era) = ShelleyBase
  type PredicateFailure (ConwayEPOCH era) = ShelleyEpochPredFailure era
  type Event (ConwayEPOCH era) = ConwayEpochEvent era
  transitionRules = [epochTransition]

returnProposalDeposits' ::
  ConwayGovernance era ->
  StrictSeq (GovernanceActionId (EraCrypto era), GovernanceActionState era) ->
  UMap (EraCrypto era) ->
  UMap (EraCrypto era)
returnProposalDeposits' ConwayGovernance {..} gaids m =
  RewDepUView m ∪+ foldl' addRew mempty gaids
  where
    addRew m' (gaid, gas) =
      Map.insertWith
        (<>)
        (KeyHashObj $ gasReturnAddr gas)
        (fromMaybe mempty $ toCompact =<< Map.lookup gaid cgPropDeposits)
        m'

returnProposalDeposits ::
  forall era.
  GovernanceState era ~ ConwayGovernance era =>
  LedgerState era ->
  LedgerState era
returnProposalDeposits ls@LedgerState {..} =
  ls
    & lsCertStateL . certDStateL %~ dstate
    & lsUTxOStateL . utxosGovernanceL . cgPropDepositsL %~ removeDeps
  where
    govSt = utxosGovernance lsUTxOState
    ratifyState = cgRatify govSt
    removedProposals = rsRemoved ratifyState
    dstate = dsUnifiedL %~ returnProposalDeposits' govSt removedProposals
    removeDeps m = Map.withoutKeys m . Set.fromList . toList $ fst <$> removedProposals

epochTransition ::
  forall era.
  ( Embed (EraRule "SNAP" era) (ConwayEPOCH era)
  , Environment (EraRule "SNAP" era) ~ SnapEnv era
  , State (EraRule "SNAP" era) ~ SnapShots (EraCrypto era)
  , Signal (EraRule "SNAP" era) ~ ()
  , Embed (EraRule "POOLREAP" era) (ConwayEPOCH era)
  , Environment (EraRule "POOLREAP" era) ~ PParams era
  , State (EraRule "POOLREAP" era) ~ ShelleyPoolreapState era
  , Signal (EraRule "POOLREAP" era) ~ EpochNo
  , GovernanceState era ~ ConwayGovernance era
  ) =>
  TransitionRule (ConwayEPOCH era)
epochTransition = do
  TRC
    ( _
      , EpochState
          { esAccountState = acnt
          , esSnapshots = ss
          , esLState = ls
          , esPrevPp = pr
          , esPp = pp
          , esNonMyopic = nm
          }
      , e
      ) <-
    judgmentContext
  let utxoSt = lsUTxOState ls
  let CertState vstate pstate dstate = lsCertState ls
  ss' <-
    trans @(EraRule "SNAP" era) $ TRC (SnapEnv ls pp, ss, ())

  let PState pParams fPParams _ _ = pstate
      ppp = eval (pParams ⨃ fPParams)
      pstate' =
        pstate
          { psStakePoolParams = ppp
          , psFutureStakePoolParams = Map.empty
          }
  PoolreapState utxoSt' acnt' dstate' pstate'' <-
    trans @(EraRule "POOLREAP" era) $
      TRC (pp, PoolreapState utxoSt acnt dstate pstate', e)

  let adjustedCertState = CertState vstate pstate'' dstate'
      adjustedLState =
        ls
          { lsUTxOState = utxoSt'
          , lsCertState = adjustedCertState
          }
      epochState' =
        EpochState
          acnt'
          ss'
          (returnProposalDeposits adjustedLState)
          pr
          pp
          nm

  let
    utxoSt''' = utxoSt' {utxosDeposited = obligationCertState adjustedCertState}
    acnt'' = acnt' {asReserves = asReserves acnt'}
  pure $
    epochState'
      { esAccountState = acnt''
      , esLState = (esLState epochState') {lsUTxOState = utxoSt'''}
      , esPrevPp = pp
      , esPp = pp
      }

instance
  ( Era era
  , STS (ShelleyPOOLREAP era)
  , PredicateFailure (EraRule "POOLREAP" era) ~ ShelleyPoolreapPredFailure era
  , Event (EraRule "POOLREAP" era) ~ ShelleyPoolreapEvent era
  ) =>
  Embed (ShelleyPOOLREAP era) (ConwayEPOCH era)
  where
  wrapFailed = PoolReapFailure
  wrapEvent = PoolReapEvent

instance
  ( EraTxOut era
  , PredicateFailure (EraRule "SNAP" era) ~ ShelleySnapPredFailure era
  , Event (EraRule "SNAP" era) ~ Shelley.SnapEvent era
  ) =>
  Embed (ShelleySNAP era) (ConwayEPOCH era)
  where
  wrapFailed = SnapFailure
  wrapEvent = SnapEvent
