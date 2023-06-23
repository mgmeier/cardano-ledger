{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

-- ==============================================

module Test.Cardano.Ledger.Constrained.Preds.Tx where

import Cardano.Crypto.Signing (SigningKey)
import Cardano.Ledger.Address (Addr (..), BootstrapAddress,RewardAcnt(..))
import Cardano.Ledger.Alonzo.Core (AlonzoEraTxOut (..), ScriptIntegrityHash)
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.Scripts (AlonzoScript (..), ExUnits (..))
import Cardano.Ledger.Alonzo.Scripts.Data (Data (..))
import Cardano.Ledger.Alonzo.Tx (IsValid (..), ScriptPurpose (..), rdptr)
import Cardano.Ledger.Alonzo.TxWits (
  RdmrPtr (..),
  Redeemers (..),
  TxDats (..),
 )
import Cardano.Ledger.Alonzo.UTxO (getInputDataHashesTxBody)
import Cardano.Ledger.Api (setMinFeeTx)
import Cardano.Ledger.BaseTypes (StrictMaybe (..), strictMaybeToMaybe,Network(..))
import Cardano.Ledger.Coin (Coin (..),rationalToCoinViaCeiling)
import Cardano.Ledger.Core (EraScript (..), EraTx (..), EraTxBody (..), EraTxOut (..), bodyTxL, coinTxOutL, feeTxBodyL, Value)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Hashes (DataHash, EraIndependentTxBody, ScriptHash (..))
import Cardano.Ledger.Keys (GenDelegPair (..), GenDelegs (..), Hash, KeyHash, KeyRole (..))
import Cardano.Ledger.Keys.Bootstrap (BootstrapWitness)
import Cardano.Ledger.Mary.Core (MaryEraTxBody)
import Cardano.Ledger.Mary.Value(MaryValue(..),MultiAsset(..),AssetName,PolicyID(..))
import Cardano.Ledger.Pretty (PrettyA (..), ppList, ppSet)
import Cardano.Ledger.SafeHash (SafeHash, extractHash, hashAnnotated)
import Cardano.Ledger.Shelley.AdaPots (consumedTxBody, producedTxBody)
import Cardano.Ledger.Shelley.LedgerState (AccountState (..), LedgerState, keyCertsRefunds, totalCertsDeposits)
import Cardano.Ledger.Shelley.Rules (LedgerEnv (..), witsVKeyNeededFromBody)
import Cardano.Ledger.Shelley.TxBody (WitVKey (..))
import Cardano.Ledger.TxIn (TxIn (..))
import Cardano.Ledger.UTxO (EraUTxO (..))
import Cardano.Ledger.Val (Val (inject, (<->),(<+>)))
import Control.State.Transition.Extended (TRC (..))
import Data.Coerce (coerce)
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word(Word64)
import Data.Ratio((%))
import Lens.Micro
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Examples (checkForSoundness)
import Test.Cardano.Ledger.Constrained.Monad (Typed, failT, monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.CertState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.Certs (certsStage)
import Test.Cardano.Ledger.Constrained.Preds.LedgerState (ledgerStateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Preds.TxOut (txOutPreds)
import Test.Cardano.Ledger.Constrained.Preds.Universes hiding (main)
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..), Size (..))
import Test.Cardano.Ledger.Constrained.Solver (toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars hiding (totalAda)
import Test.Cardano.Ledger.Core.KeyPair (KeyPair (..), mkWitnessVKey)
import Test.Cardano.Ledger.Generic.Functions (TotalAda (totalAda), isValid')
import Test.Cardano.Ledger.Generic.PrettyCore -- (pcLedgerState, pcTx, pcTxBody)
import Test.Cardano.Ledger.Generic.Proof
import Test.Cardano.Ledger.Generic.TxGen (applySTSByProof)
import Test.Cardano.Ledger.Generic.Updaters (newScriptIntegrityHash)
import Test.QuickCheck
import Data.Foldable(fold,foldl')
import Debug.Trace(trace)

-- ===============================================
-- Helpful Lenses

sndL :: Lens' (a, b) b
sndL = lens snd (\(x, _) y -> (x, y))

fstL :: Lens' (a, b) a
fstL = lens fst (\(_, y) x -> (x, y))

txFL :: Lens' (TxF era) (Tx era)
txFL = lens (\(TxF _ x) -> x) (\(TxF p _) x -> TxF p x)

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
computeWitsVKey (TxBodyF _ txb) u gd keyUniv reqsigners = trace ("REAL KEYWIT\n"++show (ppSet (pcWitVKey @era reify) keywits)) keywits
  where
    bodyhash :: SafeHash (EraCrypto era) EraIndependentTxBody
    bodyhash = hashAnnotated txb
    keyhashes :: Set (KeyHash 'Witness (EraCrypto era))
    keyhashes = Set.union (witsVKeyNeededFromBody (liftUTxO u) txb (GenDelegs gd)) reqsigners
    keywits :: Set (WitVKey 'Witness (EraCrypto era))
    keywits = Set.foldl' accum Set.empty (trace ("HASHES TO SIGN\n"++show(ppSet pcKeyHash keyhashes)++"\n"++show bodyhash) keyhashes)
      where
        accum ans hash = case Map.lookup hash keyUniv of
          Nothing -> error ("hash not in keyUniv "++show hash++"\n"++show(pcTxBody reify txb))
          Just keypair -> trace ("PREIMAGE\n  "++show hash++"\n  "++show keypair) (Set.insert (mkWitnessVKey bodyhash keypair) ans)

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

getNTxOut :: Reflect era => Size -> TxOutF era -> [TxOutF era] -> [TxOutF era]
getNTxOut (SzExact n) feeoutput outputuniv =
  (feeoutput & outputCoinL .~ (Coin 1000000)) : take (n - 1) outputuniv
getNTxOut x _ _ =
  error
    ( "Non (SzExact n): "
        ++ show x
        ++ " in getNTxOut. Use (MetaSize size x) to get a random (SzExact n)."
    )

-- | Compute the sum of all the Values in a List(Set,Map, ...) of TxOut  
txoutSum :: forall era t. (Foldable t, Reflect era) => t (TxOutF era) -> Value era
txoutSum xs = foldl' accum mempty xs
  where accum ans (TxOutF _ txout) = txout ^. valueTxOutL <+> ans

    
minusMultiValue :: forall era. Reflect era => Proof era -> Value era -> Value era -> Map (ScriptHash (EraCrypto era)) (Map AssetName Integer)
minusMultiValue p v1 v2 = case whichValue p of
  ValueMaryToConway -> case v1 <-> v2 of MaryValue _ (MultiAsset m)-> Map.mapKeys (\ (PolicyID x) -> x) m
  ValueShelleyToAllegra -> mempty


-- ==============================================================
-- Using constraints to generate a TxBody
-- ==============================================================

txBodyPreds :: forall era. Reflect era => Proof era -> [Pred era]
txBodyPreds p =
  (txOutPreds p balanceCoin (outputs p))
    ++ [ -- Sized (Range 0 3) mint
     --  , Subset (Dom mint) (Dom (nonSpendScriptUniv p))
        mint :<-: (Constr "sumAssets" (\ out spend -> minusMultiValue p (txoutSum out) (txoutSum spend)) ^$ (outputs p) ^$ spending)
       , networkID :<-: justTarget network
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
       , tempTotalCol :=: sumCol
       , -- withdrawals
         Sized (Range 0 2) prewithdrawal
       , Subset prewithdrawal (Dom nonZeroRewards)
       , withdrawals :<-: (Constr "mkRwrdAcnt" (\ s r -> Map.fromList (map (\ x -> (RewardAcnt Testnet x, r Map.! x)) (Set.toList s)))
                            ^$ prewithdrawal ^$ rewards)
       , nonZeroRewards :<-: (Constr "filter (/=0)" (Map.filter (/= (Coin 0))) ^$ rewards)
       , -- refInputs
         Sized (Range 0 1) refInputs
       , Subset refInputs (Dom (utxo p))
       , Sized (Range 1 2) reqSignerHashes
       , Subset reqSignerHashes (Dom keymapUniv)
       , ttl :<-: (Constr "(+5)" (\x -> x + 5) ^$ currentSlot)
       , spending :=: Restrict inputs (utxo p)
       , SumsTo
          (Right (Coin 1))
          balanceCoin
          EQL
          [ProjMap CoinR outputCoinL spending, SumMap withdrawals, One txrefunds, One txdeposits]
       {-
       , SumsTo ? balanceMultiAsset EQL [SumSet inputs,One mint]
  
       -}
       , txrefunds :<-: (Constr "certsRefunds" certsRefunds ^$ pparams p ^$ stakeDeposits ^$ certs)
       , txdeposits :<-: (Constr "certsDeposits" certsDeposits ^$ pparams p ^$ regPools ^$ certs)
       , scriptsNeeded :<-: (needT p ^$ tempTxBody ^$ (utxo p))
       , Elems (ProjM fstL IsValidR (Restrict (Dom scriptWits) plutusUniv)) :=: valids
       , txisvalid :<-: (Constr "allValid" allValid ^$ valids)
       , Maybe txauxdata (Simple oneAuxdata) [Random oneAuxdata]
       , adHash :<-: (Constr "hashMaybe" (hashTxAuxDataF <$>) ^$ txauxdata)
       , -- Construct a temporary 'Tx' with a size close to the size of the Tx we want.
         -- We will use this to compute the 'txfee' using a fix-point approach.
         Random tempWppHash
       , tempTxFee :<-: (constTarget (Coin (fromIntegral (maxBound :: Word64))))
       , tempTxBody :<-: txbodyTarget tempTxFee tempWppHash (Lit CoinR  (Coin (fromIntegral (maxBound :: Word64))))
       , tempTx :<-: txTarget tempTxBody tempBootWits tempKeyWits
       , -- Compute the the real fee, and then recompute the TxBody and the Tx
         txfee :<-: (Constr "finalFee" computeFinalFee ^$ (pparams p) ^$ tempTx)
       , txbodyterm :<-: txbodyTarget txfee wppHash totalCol
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
          -- Unfortunately SumsTo at ExUnits does not work except at EQL OrdCond.
          -- the problem is that (toI x + toI y) /= toI(x + y)
        , plutusDataHashes
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
        , owed :<-: ( Constr "owed" ( \ percent (Coin fee) -> rationalToCoinViaCeiling ((fromIntegral percent * fee) % 100))
                    ^$ (collateralPercentage p)
                    ^$ txfee )
          -- we need to add 'extraCol' to the range of 'colInput', in the 'utxo' to pay the collateral fee.
          -- we arrange this so adding the 'extraCol' will make the sum of the all the collateral inputs, one more than 'owed'
        , extraCol :<-: ( Constr "extraCol" (\ (Coin suminputs) (Coin owe) -> (Coin (owe + 1 - suminputs))) ^$ sumCol ^$ owed)
        , totalCol :<-: (Constr "(<+>)" (\ x y -> x <+> y <-> Coin 1) ^$ extraCol ^$ sumCol)
        , Member (Right colRetAddr) addrUniv
          -- This depends on the Coin in the TxOut being (Coin 1). The computation of 'owed' and 'extraCol" should ensure this.
        , collateralReturn p :<-: (Constr "colReturn" (\ad -> TxOutF p (mkBasicTxOut ad (inject (Coin 1)))) ^$ colRetAddr)
          -- We compute this, so that we can test that the (Coin 1) invariant holds.
        , colRetCoin :<-: (Constr "-" (\sumc extra owe -> (sumc <> extra) <-> owe) ^$ sumCol ^$ extraCol ^$ owed)
        ]
  where
    spending = Var (V "spending" (MapR TxInR (TxOutR p)) No)
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
    tempTotalCol = Var $ V "tempTotalCol" CoinR No
    prewithdrawal = Var $ V "preWithdrawal" (SetR CredR) No

txBodyStage ::
  (Reflect era) =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
txBodyStage proof subst0 = do
  let preds = txBodyPreds proof
  toolChainSub proof standardOrderInfo preds subst0

main :: IO ()
main = do
  let proof =
        -- Conway Standard
        Babbage Standard
  -- Alonzo Standard
  -- Mary Standard
  -- Shelley Standard
  subst <-
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
      )
  -- rewritten <- snd <$> generate (rewriteGen (1, txBodyPreds proof))
  -- putStrLn (show rewritten)
  (_, status) <- monadTyped $ checkForSoundness (txBodyPreds proof) subst
  case status of
    Nothing -> pure ()
    Just msg -> error msg
  env0 <- monadTyped $ substToEnv subst emptyEnv
  env1 <- monadTyped $ adjustFeeInput env0
  env2 <- monadTyped $ adjustColInput {- colInput sumCol extraCol -} env1
  displayTerm env2 txfee
  displayTerm env2 txterm
  -- compute Produced and Consumed
  (TxBodyF _ txb) <- monadTyped (findVar (unVar txbodyterm) env2)
  certState <- monadTyped $ runTarget env1 dpstateT
  (PParamsF _ ppV) <- monadTyped (findVar (unVar (pparams proof)) env2)
  utxoV <- monadTyped (findVar (unVar (utxo proof)) env2)
  putStrLn (show (producedTxBody txb ppV certState))
  putStrLn (show (consumedTxBody txb ppV certState (liftUTxO utxoV)))

  goRepl proof env2 ""

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
  -- Term era (TxIn (EraCrypto era)) ->
  -- Term era Coin ->
  -- Term era Coin ->
  Env era ->
  Typed (Env era)
adjustColInput {- colInputt sumColt extraColt -} env = do
  let utxoterm = utxo reify
      utxoV = unVar utxoterm
  colinput <- runTerm env colInput
  extracoin <- runTerm env extraCol
  utxomap <- runTerm env utxoterm
  let env2 = storeVar utxoV (balanceMap [(colinput, extracoin)] utxomap outputCoinL) env
      -- adjust (Just x) y = Just (x <> y)
      -- adjust Nothing _ = Nothing
  -- env3 <- updateVal (<>) sumCol extracoin env2
  -- env4 <- updateVal (<+>) totalCol extracoin env3
  (env5, body) <- updateTarget override txbodyterm (txbodyTarget txfee wppHash totalCol) env2
  (env6, _) <- updateTarget override txterm (txTarget (Lit (TxBodyR reify) body) bootWits keyWits) env5
  pure env6

updateVal :: (a -> b -> a) -> Term era a -> b -> Env era -> Typed (Env era)
updateVal adjust term@(Var v) delta env = do
  varV <- runTerm env term
  pure $ storeVar v (adjust varV delta) env
updateVal _ v _ _ = failT ["Non Var in updateVal: " ++ show v]

updateTerm :: (a -> b -> a) -> Term era a -> Term era b -> Env era -> Typed (Env era)
updateTerm adjust term@(Var v) delta env = do
  varV <- runTerm env term
  deltaV <- runTerm env delta
  pure $ storeVar v (adjust varV deltaV) env
updateTerm _ v _ _ = failT ["Non Var in updateTerm: " ++ show v]

updateTarget :: (a -> b -> a) -> Term era a -> Target era b -> Env era -> Typed (Env era, b)
updateTarget adjust term@(Var v) delta env = do
  varV <- runTerm env term
  deltaV <- runTarget env delta
  pure $ (storeVar v (adjust varV deltaV) env, deltaV)
updateTarget _ v _ _ = failT ["Non Var in updateTarget: " ++ show v]

override :: x -> x -> x
override _ y = y

-- ========================================

genTxAndLedger :: Reflect era => Proof era -> Gen (LedgerState era, Tx era, Env era)
genTxAndLedger proof = do
  subst <-
    ( pure []
        >>= pParamsStage proof
        >>= universeStage proof
        >>= vstateStage proof
        >>= pstateStage proof
        >>= dstateStage proof
        >>= certsStage proof
        >>= ledgerStateStage proof
        >>= txBodyStage proof
      )
  env0 <- monadTyped $ substToEnv subst emptyEnv
  env1 <- monadTyped $ adjustFeeInput env0
  env2 <- monadTyped $ adjustColInput env1
  ledger <- monadTyped $ runTarget env2 (ledgerStateT proof)
  (TxF _ tx) <- monadTyped (findVar (unVar txterm) env2)
  pure (ledger, tx, env2)



gone :: Gen (IO ())
gone = do
  txIx <- arbitrary
  let proof = Babbage Standard
  (ledgerstate, tx, env) <- genTxAndLedger proof
  slot <- monadTyped (findVar (unVar currentSlot) env)
  (PParamsF _ pp) <- monadTyped (findVar (unVar (pparams proof)) env)
  let lenv = LedgerEnv slot txIx pp (AccountState (Coin 0) (Coin 0))
  -- putStrLn (show (pcTx (Babbage Standard) tx))
  pure $ case applySTSByProof proof (TRC (lenv, ledgerstate, tx)) of
    Right ledgerState' ->
      -- UTxOState and CertState after applying the transaction $$$
      pure ()
    Left errs -> do
      putStrLn
        ( show (pcLedgerState proof ledgerstate)
            ++ "\n\n"
            ++ show (pcTx proof tx)
            ++ "\n\n"
            ++ show (ppList prettyA errs)
        )
      goRepl (Babbage Standard) env ""
