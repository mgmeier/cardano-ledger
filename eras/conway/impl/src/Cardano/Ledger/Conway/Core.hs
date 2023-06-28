{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Cardano.Ledger.Conway.Core (
  module X,
  ConwayEraTxBody (..),
  ConwayEraPParams (..),
)
where

import Cardano.Ledger.Babbage.Core as X
import Cardano.Ledger.BaseTypes (EpochNo)
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Conway.Governance (ProposalProcedure, VotingProcedure)
import Cardano.Ledger.HKD (HKD, HKDFunctor)
import Data.Map.Strict (Map)
import Data.Sequence.Strict (StrictSeq)
import Lens.Micro (Lens')
import Numeric.Natural (Natural)

class BabbageEraTxBody era => ConwayEraTxBody era where
  votingProceduresTxBodyL :: Lens' (TxBody era) (StrictSeq (VotingProcedure era))
  proposalProceduresTxBodyL :: Lens' (TxBody era) (StrictSeq (ProposalProcedure era))

class BabbageEraPParams era => ConwayEraPParams era where
  hkdVotingThresholdsL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f (Map Natural Natural))
  hkdMinCCSizeL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f Natural)
  hkdCCTermLimitL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f Natural)
  hkdGovExpirationL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f Natural)
  hkdGovDepositL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f Coin)
  hkdDRepDepositL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f Coin)
  hkdDRepActivityL :: HKDFunctor f => Lens' (PParamsHKD f era) (HKD f EpochNo)
