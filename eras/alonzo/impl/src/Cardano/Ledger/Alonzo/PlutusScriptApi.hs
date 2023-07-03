{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Alonzo.PlutusScriptApi (
  -- Figure 8
  getSpendingTxIn,
  getDatumAlonzo,
  evalScripts,
  -- Figure 12
  scriptsNeeded,
  scriptsNeededFromBody,
  language,
  CollectError (..),
  collectTwoPhaseScriptInputs,
  knownToNotBe1Phase,
)
where

import Cardano.Ledger.Alonzo.Core hiding (TranslationError)
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript (..), CostModel, CostModels (..), ExUnits (..))
import Cardano.Ledger.Alonzo.Scripts.Data (getPlutusData)
import Cardano.Ledger.Alonzo.Tx (Data, ScriptPurpose (..), indexedRdmrs)
import Cardano.Ledger.Alonzo.TxInfo (
  EraPlutusContext,
  ExtendedUTxO (..),
  ScriptResult (..),
  TranslationError (..),
  runPlutusScript,
  valContext,
 )
import Cardano.Ledger.Alonzo.TxWits (AlonzoEraTxWits (..), unTxDats)
import Cardano.Ledger.Alonzo.UTxO (AlonzoScriptsNeeded (..))
import Cardano.Ledger.BaseTypes (ProtVer, StrictMaybe (..))
import Cardano.Ledger.Binary (DecCBOR (..), EncCBOR (..))
import Cardano.Ledger.Binary.Coders
import Cardano.Ledger.Language (BinaryPlutus (..), Language (..), Plutus (..))
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.UTxO (EraUTxO (..), UTxO (..))
import Cardano.Slotting.EpochInfo (EpochInfo)
import Cardano.Slotting.Time (SystemStart)
import Data.ByteString.Short (ShortByteString)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Proxy (Proxy (..))
import qualified Data.Set as Set
import Data.Text (Text)
import Debug.Trace (traceEvent)
import GHC.Generics
import Lens.Micro
import NoThunks.Class (NoThunks)

-- ===============================================================
-- From the specification, Figure 8 "Scripts and their Arguments"
-- ===============================================================

-- | Only the Spending ScriptPurpose contains TxIn
getSpendingTxIn :: ScriptPurpose era -> Maybe (TxIn (EraCrypto era))
getSpendingTxIn = \case
  Spending txin -> Just txin
  Minting _policyid -> Nothing
  Rewarding _rewaccnt -> Nothing
  Certifying _dcert -> Nothing

-- | Get the Data associated with a ScriptPurpose. Only the Spending
--   ScriptPurpose contains Data. The null list is returned for the other kinds.
getDatumAlonzo ::
  (AlonzoEraTxWits era, AlonzoEraTxOut era, EraTx era) =>
  Tx era ->
  UTxO era ->
  ScriptPurpose era ->
  Maybe (Data era)
getDatumAlonzo tx (UTxO m) sp = do
  txIn <- getSpendingTxIn sp
  txOut <- Map.lookup txIn m
  SJust hash <- Just $ txOut ^. dataHashTxOutL
  Map.lookup hash (unTxDats $ tx ^. witsTxL . datsTxWitsL)

-- ========================================================================

-- | When collecting inputs for two phase scripts, 3 things can go wrong.
data CollectError era
  = NoRedeemer !(ScriptPurpose era)
  | NoWitness !(ScriptHash (EraCrypto era))
  | NoCostModel !Language
  | BadTranslation !(TranslationError (EraCrypto era))
  deriving (Generic)

deriving instance (Era era, Eq (TxCert era)) => Eq (CollectError era)
deriving instance (Era era, Show (TxCert era)) => Show (CollectError era)
deriving instance (Era era, NoThunks (TxCert era)) => NoThunks (CollectError era)

instance EraTxCert era => EncCBOR (CollectError era) where
  encCBOR (NoRedeemer x) = encode $ Sum NoRedeemer 0 !> To x
  encCBOR (NoWitness x) = encode $ Sum (NoWitness @era) 1 !> To x
  encCBOR (NoCostModel x) = encode $ Sum NoCostModel 2 !> To x
  encCBOR (BadTranslation x) = encode $ Sum (BadTranslation @era) 3 !> To x

instance (Era era, DecCBOR (TxCert era)) => DecCBOR (CollectError era) where
  decCBOR = decode (Summands "CollectError" dec)
    where
      dec 0 = SumD NoRedeemer <! From
      dec 1 = SumD NoWitness <! From
      dec 2 = SumD NoCostModel <! From
      dec 3 = SumD BadTranslation <! From
      dec n = Invalid n

-- Given a script purpose and a script hash, determine if it is *not*
-- a simple 1-phase script by looking up the script hash in a mapping
-- of script hashes to labeled scripts.
-- If the script is determined to not be a 1-phase script, we return
-- a triple: the script purpose, the language, and the script bytes.
--
-- The formal spec achieves the same filtering as knownToNotBe1Phase
-- by use of the (partial) language function, which is not defined on 1-phase scripts.
knownToNotBe1Phase ::
  Map.Map (ScriptHash (EraCrypto era)) (AlonzoScript era) ->
  (ScriptPurpose era, ScriptHash (EraCrypto era)) ->
  Maybe (ScriptPurpose era, Plutus)
knownToNotBe1Phase scriptsAvailable (sp, sh) = do
  PlutusScript plutus <- sh `Map.lookup` scriptsAvailable
  Just (sp, plutus)

-- | Collect the inputs for twophase scripts. If any script can't find ist data return
--     a list of CollectError, if all goes well return a list of quadruples with the inputs.
--     Previous PredicateFailure tests should ensure we find Data for every script, BUT
--     the consequences of not finding Data means scripts can get dropped, so things
--     might validate that shouldn't. So we double check that every Script has its Data, and
--     if that is not the case, a PredicateFailure is raised in the Utxos rule.
collectTwoPhaseScriptInputs ::
  forall era.
  ( EraTx era
  , MaryEraTxBody era
  , AlonzoEraTxWits era
  , EraUTxO era
  , ScriptsNeeded era ~ AlonzoScriptsNeeded era
  , ExtendedUTxO era
  , Script era ~ AlonzoScript era
  , AlonzoEraPParams era
  , EraPlutusContext 'PlutusV1 era
  ) =>
  EpochInfo (Either Text) ->
  SystemStart ->
  PParams era ->
  Tx era ->
  UTxO era ->
  Either [CollectError era] [(ShortByteString, Language, [Data era], ExUnits, CostModel)]
collectTwoPhaseScriptInputs ei sysS pp tx utxo =
  map unwrap <$> collectPlutusScripts ei sysS pp tx utxo
  where
    unwrap (Plutus lang (BinaryPlutus scriptBytes), args, exUnits, costModel) =
      (scriptBytes, lang, args, exUnits, costModel)

collectPlutusScripts ::
  forall era.
  ( EraTx era
  , MaryEraTxBody era
  , AlonzoEraTxWits era
  , EraUTxO era
  , ScriptsNeeded era ~ AlonzoScriptsNeeded era
  , ExtendedUTxO era
  , Script era ~ AlonzoScript era
  , AlonzoEraPParams era
  , EraPlutusContext 'PlutusV1 era
  ) =>
  EpochInfo (Either Text) ->
  SystemStart ->
  PParams era ->
  Tx era ->
  UTxO era ->
  Either [CollectError era] [(Plutus, [Data era], ExUnits, CostModel)]
collectPlutusScripts ei sysS pp tx utxo =
  let usedLanguages = Set.fromList [lang | (_, Plutus lang _) <- neededAndConfirmedToBePlutus]
      costModels = costModelsValid $ pp ^. ppCostModelsL
      missingCMs = Set.filter (`Map.notMember` costModels) usedLanguages
   in case Set.lookupMin missingCMs of
        Just l -> Left [NoCostModel l]
        Nothing ->
          merge
            (apply costModels)
            (map getScriptWithRedeemer neededAndConfirmedToBePlutus)
            (Right [])
  where
    scriptsAvailable = txscripts utxo tx
    txinfo lang = txInfo pp lang ei sysS utxo tx
    AlonzoScriptsNeeded scriptsNeeded' = getScriptsNeeded utxo (tx ^. bodyTxL)
    neededAndConfirmedToBePlutus =
      mapMaybe (knownToNotBe1Phase scriptsAvailable) scriptsNeeded'
    getScriptWithRedeemer (sp, script) =
      case indexedRdmrs tx sp of
        Just (d, eu) -> Right (script, sp, d, eu)
        Nothing -> Left (NoRedeemer sp)
    apply costs (script@(Plutus lang _), sp, d, eu) =
      case txinfo lang of
        Right inf ->
          let datums = maybe id (:) (getDatum tx utxo sp) [d, valContext inf sp]
           in Right (script, datums, eu, costs Map.! lang)
        Left te -> Left $ BadTranslation te

-- | Merge two lists (the first of which may have failures, i.e. (Left _)), collect all the failures
--   but if there are none, use 'f' to construct a success.
merge :: forall t b a. (t -> Either a b) -> [Either a t] -> Either [a] [b] -> Either [a] [b]
merge _f [] answer = answer
merge f (x : xs) zs = merge f xs (gg x zs)
  where
    gg :: Either a t -> Either [a] [b] -> Either [a] [b]
    gg (Right t) (Right cs) =
      case f t of
        Right c -> Right $ c : cs
        Left e -> Left [e]
    gg (Left a) (Right _) = Left [a]
    gg (Right _) (Left cs) = Left cs
    gg (Left a) (Left cs) = Left (a : cs)

language :: AlonzoScript era -> Maybe Language
language (PlutusScript (Plutus lang _)) = Just lang
language (TimelockScript _) = Nothing

-- | evaluate a list of scripts, All scripts in the list must be True.
--   There are two kinds of scripts, evaluate each kind using the
--   appropriate mechanism.
evalScripts ::
  forall era.
  (EraTx era, Script era ~ AlonzoScript era) =>
  ProtVer ->
  Tx era ->
  [(ShortByteString, Language, [Data era], ExUnits, CostModel)] ->
  ScriptResult
evalScripts pv tx scripts =
  evalPlutusScripts pv tx scripts'
  where
    scripts' =
      [ (Plutus lang (BinaryPlutus pscript), ds, units, cost)
      | (pscript, lang, ds, units, cost) <- scripts
      ]
{-# DEPRECATED evalScripts "In favor of `evalPlutusScripts`" #-}

-- | Evaluate a list of Plutus scripts. All scripts in the list must evaluate to `True`.
evalPlutusScripts ::
  forall era.
  (EraTx era, Script era ~ AlonzoScript era) =>
  ProtVer ->
  Tx era ->
  [(Plutus, [Data era], ExUnits, CostModel)] ->
  ScriptResult
evalPlutusScripts _pv _tx [] = mempty
evalPlutusScripts pv tx ((plutus, ds, units, cost) : rest) =
  let beginMsg =
        intercalate
          ","
          [ "[LEDGER][PLUTUS_SCRIPT]"
          , "BEGIN"
          ]
      !res = traceEvent beginMsg $ runPlutusScript (Proxy @era) pv plutus cost units (map getPlutusData ds)
      endMsg =
        intercalate
          ","
          [ "[LEDGER][PLUTUS_SCRIPT]"
          , "END"
          ]
   in traceEvent endMsg res <> evalPlutusScripts pv tx rest

-- Collect information (purpose and ScriptHash) about all the
-- Credentials that refer to scripts, that might be run in a Tx.
-- THE SPEC CALLS FOR A SET, BUT THAT NEEDS A BUNCH OF ORD INSTANCES (TxCert)
-- See additional comments about 'scriptsNeededFromBody' below.
scriptsNeeded ::
  ( EraTx era
  , EraUTxO era
  , ScriptsNeeded era ~ [(ScriptPurpose (EraCrypto era), ScriptHash (EraCrypto era))]
  ) =>
  UTxO era ->
  Tx era ->
  [(ScriptPurpose (EraCrypto era), ScriptHash (EraCrypto era))]
scriptsNeeded utxo tx = scriptsNeededFromBody utxo (tx ^. bodyTxL)
{-# DEPRECATED scriptsNeeded "In favor of `getScritpsNeeded`" #-}

scriptsNeededFromBody ::
  forall era.
  ( EraUTxO era
  , ScriptsNeeded era ~ [(ScriptPurpose (EraCrypto era), ScriptHash (EraCrypto era))]
  ) =>
  UTxO era ->
  TxBody era ->
  [(ScriptPurpose (EraCrypto era), ScriptHash (EraCrypto era))]
scriptsNeededFromBody = getScriptsNeeded
{-# DEPRECATED scriptsNeededFromBody "In favor of `getScritpsNeeded`" #-}
