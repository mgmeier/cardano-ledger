{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Cardano.Ledger.Constrained.Preds.Tx where

import Cardano.Ledger.Address (BootstrapAddress, Withdrawals (..))
import Cardano.Ledger.Alonzo.Core (AlonzoEraTxBody (..), AlonzoEraTxOut (..))
import Cardano.Ledger.Api (setMinFeeTx)
import Cardano.Ledger.BaseTypes (EpochNo (..), StrictMaybe (..), maybeToStrictMaybe, strictMaybeToMaybe)
import Cardano.Ledger.Coin (Coin (..))
import Cardano.Ledger.Conway.TxCert (
  ConwayDelegCert (..),
  ConwayTxCert (..),
  Delegatee (..),
 )
import Cardano.Ledger.Core (EraScript (..), EraTx (..), EraTxBody (..), TxWits, bodyTxL, coinTxOutL, feeTxBodyL)
import Cardano.Ledger.Credential (StakeCredential)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (GenDelegPair (..), GenDelegs (..), Hash, KeyHash, KeyRole (..))
import Cardano.Ledger.Pretty (PDoc, ppMap, ppSet, ppSexp)
import Cardano.Ledger.Shelley.AdaPots (consumedTxBody, producedTxBody)
import Cardano.Ledger.Shelley.Core (ShelleyEraTxBody (..))
import Cardano.Ledger.Shelley.TxCert (
  PoolCert (..),
  ShelleyDelegCert (..),
  ShelleyTxCert (..),
 )
import Cardano.Ledger.TxIn (TxIn (..))
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Debug.Trace
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Examples (checkForSoundness)
import Test.Cardano.Ledger.Constrained.Monad (Typed, failT, monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.Certs (certsStage)
import Test.Cardano.Ledger.Constrained.Preds.DPState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Preds.TxOut (txOutPreds)
import Test.Cardano.Ledger.Constrained.Preds.Universes hiding (main)
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..), Size (..))
import Test.Cardano.Ledger.Constrained.Solver (toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.Fields (TxBodyField (..), TxField (..), WitnessesField (..))
import Test.Cardano.Ledger.Generic.PrettyCore

-- (pcScriptHash, pcScriptPurpose, pcScriptsNeeded, pcTxBody, pcTxIn, pcTxOut, pcKeyHash,pcGenDelegPair)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.Updaters (Merge (..), newTx, newTxBody, newWitnesses)
import Test.QuickCheck

import Cardano.Crypto.Signing (SigningKey)
import Cardano.Ledger.Address (Addr (..), RewardAcnt (..))
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript (..), ExUnits (..))
import Cardano.Ledger.Alonzo.Scripts.Data (Data (..), hashData)
import Cardano.Ledger.Alonzo.Tx (IsValid (..), ScriptPurpose (..), rdptr)
import Cardano.Ledger.Alonzo.TxWits (
  RdmrPtr (..),
  Redeemers (..),
  TxDats (..),
 )
import Cardano.Ledger.Alonzo.UTxO (AlonzoScriptsNeeded (..), getInputDataHashesTxBody)
import Cardano.Ledger.Core (EraTxOut (..), Value)
import Cardano.Ledger.Credential (Credential (..), StakeReference (..))
import Cardano.Ledger.Hashes (DataHash, EraIndependentTxBody, ScriptHash (..))
import Cardano.Ledger.Keys.Bootstrap (BootstrapWitness)
import Cardano.Ledger.Mary.Core (MaryEraTxBody)
import Cardano.Ledger.Mary.Value (AssetName (..), MaryValue (..))
import Cardano.Ledger.SafeHash (SafeHash, extractHash, hashAnnotated)
import Cardano.Ledger.Shelley.LedgerState (keyCertsRefunds, totalCertsDeposits)
import Cardano.Ledger.Shelley.Rules (witsVKeyNeededFromBody)
import Cardano.Ledger.Shelley.UTxO (ShelleyScriptsNeeded (..))
import Cardano.Ledger.UTxO (EraUTxO (..), UTxO (..))
import Cardano.Ledger.Val (Val (coin, inject, (<->)))
import qualified Cardano.Ledger.Val as Val (scale)
import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word16)
import qualified Data.Word as Word
import System.IO.Unsafe
import Test.Cardano.Ledger.Generic.Functions (scriptsNeeded')

import Cardano.Crypto.DSIGN.Ed25519 (Ed25519DSIGN)
import Cardano.Ledger.Alonzo.Core (ScriptIntegrityHash)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Api.Tx (getMinFeeTx)
import Cardano.Ledger.Crypto (DSIGN)
import Cardano.Ledger.Shelley.TxBody (WitVKey (..))
import Test.Cardano.Ledger.Core.KeyPair (KeyPair (..), mkWitnessVKey)
import Test.Cardano.Ledger.Generic.Updaters (newScriptIntegrityHash)
import Test.Cardano.Ledger.Constrained.Preds.LedgerState(ledgerStateStage)
-- =======================================================================================
-- How to construct an actual TxBody from an (Env era) that stores a
-- variable for each of the 'bodyNames'. If one of these vars is not
-- in the Env them, that component of the TxBody will use the default value
-- stored in Test.Cardano.Ledger.Generic.Fields(initialTxBody)

bodyNames :: [String]
bodyNames =
  [ "inputs"
  , "collateral"
  , "refInputs"
  , "outputs"
  , "collateralReturn"
  , "totalCol"
  , "certs"
  , "withdrawals"
  , "txfee"
  , "validityInterval"
  , "ttl"
  , "update"
  , "reqSignerHashes"
  , "mint"
  , "wppHash"
  , "adHash"
  , "networkID"
  -- , "govProcs"
  ]

lookupTxBody :: Env era -> String -> [TxBodyField era]
lookupTxBody (Env m) name = case (name, Map.lookup name m) of
  ("inputs", Just (Payload (SetR TxInR) t _)) -> [Inputs t]
  ("refInputs", Just (Payload (SetR TxInR) t _)) -> [RefInputs t]
  ("collateral", Just (Payload (SetR TxInR) t _)) -> [Collateral t]
  ("outputs", Just (Payload (ListR (TxOutR _)) ts _)) -> [Outputs' (map unTxOut ts)]
  ("collateralReturn", Just (Payload (TxOutR _) x _)) -> [CollateralReturn (SJust (unTxOut x))]
  ("totalCol", Just (Payload (MaybeR CoinR) x _)) -> [TotalCol (maybeToStrictMaybe x)]
  ("certs", Just (Payload (ListR (TxCertR _)) xs _)) -> [Certs' (map unTxCertF xs)]
  ("withdrawals", Just (Payload (MapR RewardAcntR CoinR) mp _)) -> [Withdrawals' (Withdrawals mp)]
  ("txfee", Just (Payload CoinR x _)) -> [Txfee x]
  ("ttl", Just (Payload SlotNoR x _)) -> [TTL x]
  ("validityInterval", Just (Payload ValidityIntervalR x _)) -> [Vldt x]
  ("mint", Just (Payload (MapR ScriptHashR (MapR AssetNameR IntegerR)) x _)) -> [Mint (liftMultiAsset x)]
  ("reqSignerHashes", Just (Payload (SetR WitHashR) x _)) -> [ReqSignerHashes x]
  ("networkID", Just (Payload (MaybeR NetworkR) x _)) -> [Txnetworkid (maybeToStrictMaybe x)]
  ("adHash", Just (Payload (MaybeR AuxiliaryDataHashR) x _)) -> [AdHash (maybeToStrictMaybe x)]
  ("wppHash", Just (Payload (MaybeR ScriptIntegrityHashR) x _)) -> [WppHash (maybeToStrictMaybe x)]
  _ -> []

txBodyFromEnv :: Proof era -> Env era -> TxBody era
txBodyFromEnv proof env = unReflect newTxBody proof (concat (map (lookupTxBody env) bodyNames))

-- ==============================================================

getUtxoCoinT ::
  Reflect era =>
  Term era (TxIn (EraCrypto era)) ->
  Term era (Map (TxIn (EraCrypto era)) (TxOutF era)) ->
  Target era Coin
getUtxoCoinT feeinput spending = Constr "getUtxoCoin" getUtxoCoin ^$ feeinput ^$ spending
  where
    getUtxoCoin input mp = case Map.lookup input mp of
      Just (TxOutF _ txout) -> txout ^. coinTxOutL
      Nothing -> error "feeinput not in spending"

-- outputCoinL
getNTxOut :: Reflect era => Size -> TxOutF era -> [TxOutF era] -> [TxOutF era]
getNTxOut (SzExact n) feeoutput outputuniv =
  (feeoutput & outputCoinL .~ (Coin 1000000)) : take (n - 1) outputuniv
getNTxOut x _ _ =
  error
    ( "Non (SzExact n): "
        ++ show x
        ++ " in getNTxOut. Use (MetaSize size x) to get a random (SzExact n)."
    )

-- ==============================================================
-- Using constraints to generate a TxBody

txBodyPreds :: forall era. Reflect era => Proof era -> [Pred era]
txBodyPreds p =
  (txOutPreds p balanceCoin (outputs p))
    ++ [ Sized (Range 0 3) mint
       , Subset (Dom mint) (Dom (nonSpendScriptUniv p))
       , Random networkID
       , -- inputs
         Sized (Range 2 10) inputs
       , Member (Left feeTxIn) inputs
       , Subset inputs (Dom (utxo p))
       , -- collateral
         Disjoint inputs collateral
       , Sized (Range 2 3) collateral
       , Subset collateral (Dom colUtxo)
       , Member (Left colInput) collateral 
       , colRestriction :=: Restrict collateral colUtxo
       , SumsTo (Right (Coin 1)) sumCol EQL [ProjMap CoinR outputCoinL colRestriction]
       , totalCol :<-: (justTarget sumCol)
         -- withdrawals
       , Sized (Range 0 2) withdrawals
       , Subset (ProjS getRwdCredL CredR (Dom withdrawals)) (Dom nonZeroRewards)
       , nonZeroRewards :<-: (Constr "filter (/=0)" (Map.filter (/= (Coin 0))) ^$ rewards)
         -- refInputs
       , Sized (Range 0 1) refInputs
       , Subset refInputs (Dom (utxo p))
       , Sized (Range 1 2) reqSignerHashes
       , Subset reqSignerHashes (Dom keymapUniv)
       , ttl :<-: (Constr "(+5)" (\x -> x + 5) ^$ currentSlot)
       , tempTxFee :<-: (constTarget (Coin 0))
       , spending :=: Restrict inputs (utxo p)
       , SumsTo
          (Right (Coin 1))
          balanceCoin
          EQL
          [ProjMap CoinR outputCoinL spending, SumMap withdrawals, One txrefunds, One txdeposits]
       , txrefunds :<-: (Constr "certsRefunds" certsRefunds ^$ pparams p ^$ stakeDeposits ^$ certs)
       , txdeposits :<-: (Constr "certsDeposits" certsDeposits ^$ pparams p ^$ regPools ^$ certs)
       , scriptsNeeded :<-: (needT p ^$ tempTxBody ^$ (utxo p))
       , Elems (ProjM fstL IsValidR (Restrict (Dom scriptWits) plutusUniv)) :=: valids
       , txisvalid :<-: (Constr "allValid" allValid ^$ valids)
       , Maybe txauxdata (Simple oneAuxdata) [Random oneAuxdata]
       , adHash :<-: (Constr "hashMaybe" (hashTxAuxDataF <$>) ^$ txauxdata)
       , Random tempWppHash
       , tempTxBody :<-: txbodyTarget tempTxFee tempWppHash
       , tempTx :<-: txTarget tempTxBody tempBootWits tempKeyWits
         --  , txterm :<-: (Constr "minFeeTx" computeFinalTx ^$ (pparams p) ^$ tempTx)
         --  , txbodyterm :<-: (Constr "getBody" (\ (TxF pr tx) -> TxBodyF pr (tx ^. bodyTxL)) ^$ txterm)
       , txfee :<-: (Constr "finalFee" computeFinalFee ^$ (pparams p) ^$ tempTx)
       , txbodyterm :<-: txbodyTarget txfee wppHash
       , txterm :<-: txTarget txbodyterm bootWits keyWits
       ]
    ++ case whichUTxO p of
      UTxOShelleyToMary ->
        [ scriptWits :=: Restrict (Proj smNeededL (SetR ScriptHashR) scriptsNeeded) (allScriptUniv p)
        , tempBootWits :<-: (Constr "boots" (bootWitsT p) ^$ spending ^$ tempTxBody ^$ byronAddrUniv)
        , tempKeyWits :<-: witsVKeyTarget tempTxBody (constTarget Set.empty)
        , bootWits :<-: (Constr "boots" (bootWitsT p) ^$ spending ^$ txbodyterm ^$ byronAddrUniv)
        , keyWits :<-: witsVKeyTarget txbodyterm (constTarget Set.empty)
        ]
      UTxOAlonzoToConway ->
        [ Proj acNeededL (ListR (PairR (ScriptPurposeR p) ScriptHashR)) scriptsNeeded :=: acNeeded
        , neededHashSet :<-: (Constr "toSet" (\x -> Set.fromList (map snd x)) ^$ acNeeded)
        , scriptWits :=: Restrict neededHashSet (allScriptUniv p)
        , rdmrPtrs :<-: (rdmrPtrsT ^$ tempTxBody ^$ acNeeded ^$ plutusUniv)
        , rdmrPtrs :=: Dom redeemers
        , SumsTo (Left (ExUnits 1 1)) (maxTxExUnits p) EQL [ProjMap ExUnitsR sndL redeemers]
        , -- Unfortunately SumsTo at ExUnits does not work except at EQL OrdCond.
          -- the problem is that (toI x + toI y) /= toI(x + y)
          plutusDataHashes
            :<-: ( Constr "plutusDataHashes" getPlutusDataHashes
                    ^$ utxo p
                    ^$ tempTxBody
                    ^$ allScriptUniv p
                 )
        , Restrict plutusDataHashes dataUniv :=: dataWits
        , tempBootWits :<-: (Constr "boots" (bootWitsT p) ^$ spending ^$ tempTxBody ^$ byronAddrUniv)
        , tempKeyWits :<-: witsVKeyTarget tempTxBody (Simple reqSignerHashes)
        , bootWits :<-: (Constr "boots" (bootWitsT p) ^$ spending ^$ txbodyterm ^$ byronAddrUniv)
        , keyWits :<-: witsVKeyTarget txbodyterm (Simple reqSignerHashes)
        , langs :<-: (Constr "languages" scriptWitsLangs ^$ scriptWits)
        , wppHash :<-: integrityHash p (pparams p) langs redeemers dataWits
        , owed
            :<-: ( Constr "owed" (\percent (Coin fee) -> Coin (div ((fromIntegral percent) * fee) 100))
                    ^$ (collateralPercentage p)
                    ^$ txfee
                 )
        , -- we need to add e 'extraCol' to the range of 'colInput', in the 'utxo' to pay the fee.
          -- we arrange this so the 'extraCol' will make the 'totalCol' one more than 'owed'
          extraCol
            :<-: ( Constr
                    "neededCol"
                    ( \(Coin tot) percent (Coin fee) ->
                        Coin (div ((fromIntegral percent * fee) - (100 * tot) + 100) 100)
                    ) --  ^ adding 100, makes the result (Coin 1) larger.
                    ^$ sumCol
                    ^$ (collateralPercentage p)
                    ^$ txfee
                 )
        , Member (Right colRetAddr) addrUniv
        , -- This depends on the Coin in the TxOut being (Coin 1). The computation of 'owed' and 'extraCol" should ensure this.
          collateralReturn p :<-: (Constr "colReturn" (\ad -> TxOutF p (mkBasicTxOut ad (inject (Coin 1)))) ^$ colRetAddr)
        , -- We compute this, so that we can test that the (Coin 1) invariant holds.
          colRetCoin :<-: (Constr "-" (\sumc extra owe -> (sumc <> extra) <-> owe) ^$ sumCol ^$ extraCol ^$ owed)
        ]
  where
    spending = Var (V "spending" (MapR TxInR (TxOutR p)) No)
    withoutfee = Var (V "withoutfee" (MapR TxInR (TxOutR p)) No)
    colUtxo = Var (V "colUtxo" (MapR TxInR (TxOutR p)) No)
    colRestriction = Var (V "colRestriction" (MapR TxInR (TxOutR p)) No)
    nonZeroRewards = var "nonZeroRewards" (MapR CredR CoinR)
    balanceCoin = Var (V "balanceCoin" CoinR No)
    certsRefunds (PParamsF _ pp) depositsx certsx = keyCertsRefunds pp (`Map.lookup` depositsx) (map unTxCertF certsx)
    certsDeposits (PParamsF _ pp) regpools certsx = Coin (-n)
      where
        (Coin n) = totalCertsDeposits pp (`Map.member` regpools) (map unTxCertF certsx)
    txrefunds = Var (V "txrefunds" CoinR No)
    txdeposits = Var (V "txdeposits" CoinR No)

    utxoSize = Var (V "utxoSize" SizeR No)
    utxoTxOuts = Var (V "utxoTxOuts" (ListR (TxOutR p)) No)
    noScriptAddr = Var (V "noScriptAddr" (SetR AddrR) No)
    feeInput = Var (V "feeInput" TxInR No)
    feeAddr = Var (V "feeAddr" AddrR No)
    preUtxo = Var (V "preUtxo" (MapR TxInR (TxOutR p)) No)
    acNeeded :: Term era [(ScriptPurpose era, ScriptHash (EraCrypto era))]
    acNeeded = Var $ V "acNeeded" (ListR (PairR (ScriptPurposeR p) ScriptHashR)) No
    neededHashSet = Var $ V "neededHashSet" (SetR ScriptHashR) No
    rdmrPtrs = Var $ V "rdmrPtrs" (SetR RdmrPtrR) No
    plutusDataHashes = Var $ V "plutusDataHashes" (SetR DataHashR) No
    oneAuxdata = Var $ V "oneAuxdata" (TxAuxDataR reify) No
    tempTxFee = Var $ V "tempTxFee" CoinR No
    tempTx = Var $ V "tempTx" (TxR p) No
    tempTxBody = Var $ V "tempTxBody" (TxBodyR reify) No
    tempWppHash = Var $ V "tempWppHash" (MaybeR ScriptIntegrityHashR) No
    tempBootWits = Var $ V "tempBootWits" (SetR (BootstrapWitnessR @era)) No
    tempKeyWits = Var $ V "tempKeyWits" (SetR (WitVKeyR reify)) No
    langs = Var $ V "langs" (SetR LanguageR) No

txBodyStage ::
  (Reflect era) =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
txBodyStage proof subst0 = do
  let preds = txBodyPreds proof
  subst <- toolChainSub proof standardOrderInfo preds subst0
  (_env, status) <- pure (undefined,Nothing) -- monadTyped $ checkForSoundness preds subst
  case status of
    Nothing -> pure subst
    Just msg -> error msg

main :: IO ()
main = do
  let proof = -- Conway Standard
       Babbage Standard
  -- Alonzo Standard
  -- Mary Standard
  -- Shelley Standard
  env0 <-
    generate
      ( pure []
          >>= pParamsStage proof
          >>= universeStage proof
          >>= vstateStage proof
          >>= pstateStage proof
          >>= dstateStage proof
          >>= certsStage proof
          >>= ledgerStateStage proof
          >>= txBodyStage proof
          >>= (\subst -> monadTyped $ substToEnv subst emptyEnv)
      )
  -- rewritten <- snd <$> generate (rewriteGen (1, txBodyPreds proof))
  -- putStrLn (show rewritten)
  -- Compute the TxBody from the fixed Env
  env <- monadTyped $ adjustFeeInput env0
  env1 <- monadTyped $ adjustColInput colInput sumCol extraCol env
  displayTerm env1 txfee
  displayTerm env1 txterm

  -- compute Produced and Consumed
  (TxBodyF _ txb) <- monadTyped (findVar (unVar txbodyterm) env)
  certState <- monadTyped $ runTarget env1 dpstateT
  (PParamsF _ ppV) <- monadTyped (findVar (unVar (pparams proof)) env)
  utxoV <- monadTyped (findVar (unVar (utxo proof)) env)
  putStrLn (show (producedTxBody txb ppV certState))
  putStrLn (show (consumedTxBody txb ppV certState (liftUTxO utxoV)))

  goRepl proof env1 ""

-- ================================================
-- Auxiliary functions and Targets

computeFinalTx :: EraTx era => PParamsF era -> TxF era -> TxF era
computeFinalTx (PParamsF _ ppV) (TxF p txV) = TxF p newtx
  where
    newtx = setMinFeeTx ppV txV

computeFinalFee :: EraTx era => PParamsF era -> TxF era -> Coin
computeFinalFee (PParamsF _ ppV) (TxF _ txV) = newtx ^. (bodyTxL . feeTxBodyL)
  where
    newtx = setMinFeeTx ppV txV

integrityHash ::
  Era era1 =>
  Proof era1 ->
  Term era2 (PParamsF era1) ->
  Term era2 (Set Language) ->
  Term era2 (Map RdmrPtr (Data era1, ExUnits)) ->
  Term era2 (Map (DataHash (EraCrypto era1)) (Data era1)) ->
  Target era2 (Maybe (ScriptIntegrityHash (EraCrypto era1)))
integrityHash p pp langs rs ds = (Constr "integrityHash" hashfun ^$ pp ^$ langs ^$ rs ^$ ds)
  where
    hashfun (PParamsF _ ppp) ls r d =
      strictMaybeToMaybe $ newScriptIntegrityHash p ppp (Set.toList ls) (Redeemers r) (TxDats d)

txFL :: Lens' (TxF era) (Tx era)
txFL = lens (\(TxF _ x) -> x) (\(TxF p _) x -> TxF p x)

-- | "Construct the Needed Scripts from the UTxO and the partial TxBody
needT ::
  EraUTxO era =>
  Proof era ->
  Target
    era
    ( TxBodyF era ->
      Map (TxIn (EraCrypto era)) (TxOutF era) ->
      ScriptsNeededF era
    )
needT proof = Constr "neededScripts" (needed proof)
  where
    needed p (TxBodyF _ txbodyV) ut = ScriptsNeededF p (getScriptsNeeded (liftUTxO ut) txbodyV)

rdmrPtrsT ::
  MaryEraTxBody era =>
  Target
    era
    ( TxBodyF era ->
      [((ScriptPurpose era), (ScriptHash (EraCrypto era)))] ->
      Map (ScriptHash (EraCrypto era)) any ->
      Set RdmrPtr
    )
rdmrPtrsT = Constr "getRdmrPtrs" getRdmrPtrs

getRdmrPtrs ::
  MaryEraTxBody era =>
  TxBodyF era ->
  [((ScriptPurpose era), (ScriptHash (EraCrypto era)))] ->
  Map (ScriptHash (EraCrypto era)) any ->
  Set RdmrPtr
getRdmrPtrs (TxBodyF _ txbodyV) xs allplutus = List.foldl' accum Set.empty xs
  where
    accum ans (sp, hash) = case (rdptr txbodyV sp, Map.member hash allplutus) of
      (SJust x, True) -> Set.insert x ans
      _ -> ans

sndL :: Lens' (a, b) b
sndL = lens snd (\(x, _) y -> (x, y))

fstL :: Lens' (a, b) a
fstL = lens fst (\(_, y) x -> (x, y))

getPlutusDataHashes ::
  (AlonzoEraTxOut era, EraTxBody era, EraScript era) =>
  Map (TxIn (EraCrypto era)) (TxOutF era) ->
  TxBodyF era ->
  Map (ScriptHash (EraCrypto era)) (ScriptF era) ->
  Set (DataHash (EraCrypto era))
getPlutusDataHashes ut (TxBodyF _ txbodyV) m =
  fst $ getInputDataHashesTxBody (liftUTxO ut) txbodyV (Map.map unScriptF m)

bootWitsT ::
  forall era.
  (EraTxOut era) =>
  Proof era ->
  Map (TxIn (EraCrypto era)) (TxOutF era) ->
  TxBodyF era ->
  Map (KeyHash 'Payment (EraCrypto era)) (Addr (EraCrypto era), SigningKey) ->
  Set (BootstrapWitness (EraCrypto era))
bootWitsT proof spend (TxBodyF _ txb) byronUniv =
  case getCrypto proof of
    Mock -> error "Can only use StandardCrypto in bootWitsT"
    Standard -> bootWitness h boots byronUniv
      where
        boots :: [BootstrapAddress (EraCrypto era)] -- Not every Addr has a BootStrapAddress
        boots = Map.foldl' accum [] spend -- Compute a list of them.
          where
            accum ans (TxOutF _ out) = case out ^. addrTxOutL of
              AddrBootstrap b -> b : ans
              _ -> ans
        h = hashBody proof txb

hashBody :: forall era. Proof era -> TxBody era -> Hash (EraCrypto era) EraIndependentTxBody
hashBody (Shelley _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)
hashBody (Allegra _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)
hashBody (Mary _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)
hashBody (Alonzo _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)
hashBody (Babbage _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)
hashBody (Conway _) txb = extractHash @(EraCrypto era) (hashAnnotated txb)

-- =======================================

-- | Compute the needed key witnesses from a transaction body.
--   First find all the key hashes from every use of keys in the transaction
--   Then find the KeyPair's associated with those hashes, then
--   using the hash of the TxBody, turn the KeyPair into a witness.
--   In Eras Shelley to Mary, 'reqsigners' should be empty. In Eras Alonzo to Conway
--   we will need to add the witnesses for the required signer hashes, so they are
--   passed in. To compute the witnsses we need the hash of the TxBody. We will call this function
--   twice. Once when we have constructed the 'tempTxBody' used to estimate the fee, and a second time
--   with 'txBodyTerm' where the fee is correct.
computeWitsVKey ::
  forall era.
  (Reflect era) =>
  TxBodyF era ->
  Map (TxIn (EraCrypto era)) (TxOutF era) ->
  Map (KeyHash 'Genesis (EraCrypto era)) (GenDelegPair (EraCrypto era)) ->
  Map (KeyHash 'Witness (EraCrypto era)) (KeyPair 'Witness (EraCrypto era)) ->
  Set (KeyHash 'Witness (EraCrypto era)) -> -- Only in Eras Alonzo To Conway,
  Set (WitVKey 'Witness (EraCrypto era))
computeWitsVKey (TxBodyF _ txb) u gd keyUniv reqsigners = keywits
  where
    bodyhash :: SafeHash (EraCrypto era) EraIndependentTxBody
    bodyhash = hashAnnotated txb
    keyhashes :: Set (KeyHash 'Witness (EraCrypto era))
    keyhashes = Set.union (witsVKeyNeededFromBody (liftUTxO u) txb (GenDelegs gd)) reqsigners
    keywits :: Set (WitVKey 'Witness (EraCrypto era))
    keywits = Set.foldl' accum Set.empty keyhashes
      where
        accum ans hash = case Map.lookup hash keyUniv of
          Nothing -> ans
          Just keypair -> Set.insert (mkWitnessVKey bodyhash keypair) ans

witsVKeyTarget ::
  Reflect era =>
  Term era (TxBodyF era) ->
  Target era (Set (KeyHash 'Witness (EraCrypto era))) ->
  Target era (Set (WitVKey 'Witness (EraCrypto era)))
witsVKeyTarget txbodyparam reqSignersTarget =
  ( Constr "keywits" computeWitsVKey
      ^$ txbodyparam
      ^$ (utxo reify)
      ^$ genDelegs
      ^$ keymapUniv
      :$ reqSignersTarget
  )

allValid :: [IsValid] -> IsValid
allValid xs = IsValid (all valid xs)
  where
    valid (IsValid b) = b

scriptWitsLangs :: Map k (ScriptF era) -> Set Language
scriptWitsLangs m = Map.foldl' accum Set.empty m
  where
    accum :: Set Language -> ScriptF era -> Set Language
    accum ans (ScriptF (Alonzo _) (PlutusScript l _)) = Set.insert l ans
    accum ans (ScriptF (Babbage _) (PlutusScript l _)) = Set.insert l ans
    accum ans (ScriptF (Conway _) (PlutusScript l _)) = Set.insert l ans
    accum ans _ = ans

-- ===============================================================

balanceMap :: Ord k => [(k, Coin)] -> Map k t -> Lens' t Coin -> Map k t
balanceMap pairs m0 l = List.foldl' accum m0 pairs
  where
    accum m (k, thecoin) = Map.adjust (\t -> t & l .~ (thecoin <> t ^. l)) k m

-- | Adjust the Coin part of the TxOut in the 'utxo' map for the TxIn 'feeTxIn' by adding 'txfee'
adjustFeeInput :: Reflect era => Env era -> Typed (Env era)
adjustFeeInput env = case utxo reify of
  u@(Var utxoV) -> do
    feeinput <- runTerm env feeTxIn
    feecoin <- runTerm env txfee
    utxomap <- runTerm env u
    pure (storeVar utxoV (balanceMap [(feeinput, feecoin)] utxomap outputCoinL) env)
  other -> failT ["utxo does not match a Var Term: " ++ show other]

-- | Adjust UTxO image of 'collateral' to pay for the collateral fees. Do this by
--   adding 'extraCol' to the TxOut associated with 'colInput'
adjustColInput ::
  Reflect era =>
  Term era (TxIn (EraCrypto era)) ->
  Term era Coin ->
  Term era Coin ->
  Env era ->
  Typed (Env era)
adjustColInput colInputt sumColt extraColt env = case (utxo reify) of
  u@(Var utxoV) -> do
    colinput <- runTerm env colInputt
    extracoin <- runTerm env extraColt
    utxomap <- runTerm env u
    let env2 = storeVar utxoV (balanceMap [(colinput, extracoin)] utxomap outputCoinL) env
        adjust (Just x) y = Just (x <> y)
        adjust Nothing _ = Nothing
    env3 <- updateVar (<>) sumColt extraColt env2
    env4 <- updateVar adjust totalCol extraColt env3
    pure env4
  other -> failT ["utxo does not match a Var Term: " ++ show other]

updateVar :: (a -> b -> a) -> Term era a -> Term era b -> Env era -> Typed (Env era)
updateVar adjust term@(Var v) delta env = do
  varV <- runTerm env term
  deltaV <- runTerm env delta
  pure $ storeVar v (adjust varV deltaV) env
updateVar _ v _ _ = failT ["Non Var in updateVar: " ++ show v]

colRetAddr :: Term era (Addr (EraCrypto era))
colRetAddr = Var $ V "colRetAddr" AddrR No

colRetCoin :: Term era Coin
colRetCoin = Var $ V "colRetCoin" CoinR No

colTxOutT :: forall era. Reflect era => Proof era -> Target era (TxOutF era)
colTxOutT p = Constr "colReturn" (\c ad -> TxOutF p (mkBasicTxOut ad (inject c))) ^$ colRetCoin ^$ colRetAddr
