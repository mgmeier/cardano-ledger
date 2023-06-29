{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Ledger.Conway.Rules.Utxo (ConwayUTXO) where

import Cardano.Ledger.Alonzo.Rules (AlonzoUtxoEvent (..), AlonzoUtxoPredFailure (..), AlonzoUtxosPredFailure)
import Cardano.Ledger.Babbage.Rules (
  BabbageUtxoPredFailure (..),
  babbageUtxoTransition,
 )
import Cardano.Ledger.BaseTypes (ShelleyBase)
import Cardano.Ledger.Conway.Core (BabbageEraTxBody, Era, EraRule, EraTx (..))
import Cardano.Ledger.Conway.Era (ConwayUTXO, ConwayUTXOS)
import Cardano.Ledger.Conway.Governance (EraGovernance)
import Cardano.Ledger.Conway.Tx (AlonzoTx)
import Cardano.Ledger.Conway.TxWits (AlonzoEraTxWits)
import Cardano.Ledger.Rules.ValidationMode (Inject)
import Cardano.Ledger.Shelley.API (UtxoEnv)
import qualified Cardano.Ledger.Shelley.API as Shelley
import Cardano.Ledger.Shelley.LedgerState (PPUPPredFailure)
import Cardano.Ledger.UTxO (EraUTxO)
import Control.State.Transition.Extended (Embed (..), STS (..))

instance
  ( EraGovernance era
  , EraTx era
  , EraUTxO era
  , AlonzoEraTxWits era
  , BabbageEraTxBody era
  , Eq (PredicateFailure (EraRule "UTXO" era))
  , Show (PredicateFailure (EraRule "UTXO" era))
  , PredicateFailure (EraRule "UTXO" era) ~ BabbageUtxoPredFailure era
  , Signal (EraRule "UTXOS" era) ~ Tx era
  , Environment (EraRule "UTXOS" era) ~ UtxoEnv era
  , Embed (EraRule "UTXOS" era) (EraRule "UTXO" era)
  , STS (EraRule "UTXO" era)
  , Inject (PPUPPredFailure era) (PredicateFailure (EraRule "UTXOS" era))
  , EraRule "UTXO" era ~ ConwayUTXO era
  , State (EraRule "UTXOS" era) ~ Shelley.UTxOState era
  , Tx era ~ AlonzoTx era
  ) =>
  STS (ConwayUTXO era)
  where
  type State (ConwayUTXO era) = Shelley.UTxOState era
  type Signal (ConwayUTXO era) = AlonzoTx era
  type Environment (ConwayUTXO era) = UtxoEnv era
  type BaseM (ConwayUTXO era) = ShelleyBase
  type PredicateFailure (ConwayUTXO era) = BabbageUtxoPredFailure era
  type Event (ConwayUTXO era) = AlonzoUtxoEvent era

  initialRules = []
  transitionRules = [babbageUtxoTransition]

instance
  ( Era era
  , STS (ConwayUTXOS era)
  , PredicateFailure (EraRule "UTXOS" era) ~ AlonzoUtxosPredFailure era
  , Event (EraRule "UTXOS" era) ~ Event (ConwayUTXOS era)
  , BaseM (ConwayUTXOS era) ~ ShelleyBase
  , PredicateFailure (ConwayUTXOS era) ~ AlonzoUtxosPredFailure era
  ) =>
  Embed (ConwayUTXOS era) (ConwayUTXO era)
  where
  wrapEvent = UtxosEvent
  wrapFailed = AlonzoInBabbageUtxoPredFailure . UtxosFailure
