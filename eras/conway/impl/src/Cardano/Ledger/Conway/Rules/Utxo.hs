module Cardano.Ledger.Conway.Rules.Utxo () where

import Control.State.Transition.Extended (STS)
import Cardano.Ledger.Conway.Era (ConwayUTXO)

instance STS (ConwayUTXO era) where
