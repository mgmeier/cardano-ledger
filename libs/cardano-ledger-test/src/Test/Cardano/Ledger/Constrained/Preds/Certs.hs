{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Cardano.Ledger.Constrained.Preds.Certs where

import Cardano.Ledger.BaseTypes (EpochNo (..), maybeToStrictMaybe)
import Cardano.Ledger.Coin (Coin (..), DeltaCoin (..))
import Cardano.Ledger.Conway.TxCert (
  ConwayDelegCert (..),
  ConwayTxCert (..),
  Delegatee (..),
 )
import Cardano.Ledger.Credential (Credential (..), StakeCredential)
import Cardano.Ledger.Era (Era (EraCrypto))
import Cardano.Ledger.Keys (KeyHash, KeyRole (..))
import Cardano.Ledger.PoolParams (PoolParams (..))
import Cardano.Ledger.Pretty (ppList)
import Cardano.Ledger.Shelley.TxCert (
  GenesisDelegCert (..),
  MIRCert (..),
  MIRPot (..),
  MIRTarget (..),
  PoolCert (..),
  ShelleyDelegCert (..),
  ShelleyTxCert (..),
 )
import Data.Map (Map)
import Lens.Micro (lens)
import Test.Cardano.Ledger.Constrained.Ast
import Test.Cardano.Ledger.Constrained.Classes
import Test.Cardano.Ledger.Constrained.Env
import Test.Cardano.Ledger.Constrained.Monad (generateWithSeed, monadTyped)
import Test.Cardano.Ledger.Constrained.Preds.CertState (dstateStage, pstateStage, vstateStage)
import Test.Cardano.Ledger.Constrained.Preds.PParams (pParamsStage)
import Test.Cardano.Ledger.Constrained.Preds.Repl (goRepl)
import Test.Cardano.Ledger.Constrained.Preds.Universes (universeStage)
import Test.Cardano.Ledger.Constrained.Rewrite
import Test.Cardano.Ledger.Constrained.Size (OrdCond (..))
import Test.Cardano.Ledger.Constrained.Solver (toolChainSub)
import Test.Cardano.Ledger.Constrained.TypeRep
import Test.Cardano.Ledger.Constrained.Vars
import Test.Cardano.Ledger.Generic.PrettyCore (pcTxCert)
import Test.Cardano.Ledger.Generic.Proof
import Test.QuickCheck

import Cardano.Crypto.Hash.Class (Hash)
import Cardano.Crypto.VRF.Class (VerKeyVRF)
import Cardano.Ledger.Address (RewardAcnt (..))
import Cardano.Ledger.Crypto (HASH, VRF)
import Cardano.Ledger.Shelley.LedgerState (availableAfterMIR)

-- =============================================
-- Shelley Cert Targets

sRegKey :: Target era (StakeCredential (EraCrypto era) -> ShelleyTxCert era)
sRegKey = Constr "sRegKey" (\x -> ShelleyTxCertDelegCert (ShelleyRegCert x))

sUnRegKey :: Target era (StakeCredential (EraCrypto era) -> ShelleyTxCert era)
sUnRegKey = Constr "UnRegKey" (\x -> ShelleyTxCertDelegCert (ShelleyUnRegCert x))

sDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> ShelleyTxCert era)
sDelegStake = Constr "sDelegStake" (\x y -> ShelleyTxCertDelegCert (ShelleyDelegCert x y))

sRegPool :: Target era (PoolParams (EraCrypto era) -> ShelleyTxCert era)
sRegPool = Constr "sRegPool" (\x -> ShelleyTxCertPool (RegPool x))

sRetirePool :: Target era (KeyHash 'StakePool (EraCrypto era) -> EpochNo -> ShelleyTxCert era)
sRetirePool = Constr "sRetirePool" (\x e -> ShelleyTxCertPool (RetirePool x e))

sMirDistribute :: Target era (Coin -> MIRPot -> Map (Credential 'Staking (EraCrypto era)) DeltaCoin -> ShelleyTxCert era)
sMirDistribute = Constr "sMirDistribute" (\_avail x m -> ShelleyTxCertMir (MIRCert x (StakeAddressesMIR m)))

sMirShift :: Target era (Coin -> MIRPot -> Coin -> ShelleyTxCert era)
sMirShift = Constr "sMirShift" (\_avail x c -> ShelleyTxCertMir (MIRCert x (SendToOppositePotMIR c)))

sGovern ::
  Target
    era
    ( KeyHash 'Genesis (EraCrypto era) ->
      KeyHash 'GenesisDelegate (EraCrypto era) ->
      Hash (HASH (EraCrypto era)) (VerKeyVRF (VRF (EraCrypto era))) ->
      ShelleyTxCert era
    )
sGovern = Constr "sGovern" (\a b c -> ShelleyTxCertGenesisDeleg (GenesisDelegCert a b c))

-- | Given a MIRPot (ReservesMIR or TreasuryMIR) compute the amount available for
--   a transfer. Takes into account the 'treasury', 'reserves' and the instaneousRewards
--   in the LedgerState by looking them up in the Env.
availableT :: Term era MIRPot -> Target era Coin
availableT pot = Constr "available" availableAfterMIR ^$ pot :$ accountStateT :$ instantaneousRewardsT

-- ==========================================
-- Conway Cert Targets

cRegKey :: Target era (StakeCredential (EraCrypto era) -> Maybe Coin -> ConwayTxCert era)
cRegKey = Constr "cRegKey" (\x y -> ConwayTxCertDeleg (ConwayRegCert x (maybeToStrictMaybe y)))

cUnRegKey :: Target era (StakeCredential (EraCrypto era) -> Maybe Coin -> ConwayTxCert era)
cUnRegKey = Constr "cUnRegKey" (\x y -> ConwayTxCertDeleg (ConwayUnRegCert x (maybeToStrictMaybe y)))

cDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> ConwayTxCert era)
cDelegStake = Constr "cDelegStake" (\x y -> ConwayTxCertDeleg (ConwayDelegCert x (DelegStake y)))

cDelegVote :: Target era (StakeCredential (EraCrypto era) -> Credential 'Voting (EraCrypto era) -> ConwayTxCert era)
cDelegVote = Constr "cDelegVote" (\x y -> ConwayTxCertDeleg (ConwayDelegCert x (DelegVote y)))

cDelegStakeVote ::
  Target
    era
    ( StakeCredential (EraCrypto era) ->
      KeyHash 'StakePool (EraCrypto era) ->
      Credential 'Voting (EraCrypto era) ->
      ConwayTxCert era
    )
cDelegStakeVote = Constr "cDelegStakeVote" (\x y z -> ConwayTxCertDeleg (ConwayDelegCert x (DelegStakeVote y z)))

cRegDelegStake :: Target era (StakeCredential (EraCrypto era) -> KeyHash 'StakePool (EraCrypto era) -> Coin -> ConwayTxCert era)
cRegDelegStake = Constr "cRegDelegStake" (\x y c -> ConwayTxCertDeleg (ConwayRegDelegCert x (DelegStake y) c))

cRegDelegVote :: Target era (StakeCredential (EraCrypto era) -> Credential 'Voting (EraCrypto era) -> Coin -> ConwayTxCert era)
cRegDelegVote = Constr "cRegDelegVote" (\x y c -> ConwayTxCertDeleg (ConwayRegDelegCert x (DelegVote y) c))

cRegDelegStakeVote ::
  Target
    era
    ( StakeCredential (EraCrypto era) ->
      KeyHash 'StakePool (EraCrypto era) ->
      Credential 'Voting (EraCrypto era) ->
      Coin ->
      ConwayTxCert era
    )
cRegDelegStakeVote = Constr "cRegDelegStakeVote" (\w x y c -> ConwayTxCertDeleg (ConwayRegDelegCert w (DelegStakeVote x y) c))

cRegPool :: Target era (PoolParams (EraCrypto era) -> ConwayTxCert era)
cRegPool = Constr "cRegPool" (\x -> ConwayTxCertPool (RegPool x))

cRetirePool :: Target era (KeyHash 'StakePool (EraCrypto era) -> EpochNo -> ConwayTxCert era)
cRetirePool = Constr "cRetirePool" (\x e -> ConwayTxCertPool (RetirePool x e))

{-
cGovern ::
  Target
    era
    ( KeyHash 'Genesis (EraCrypto era) ->
      KeyHash 'GenesisDelegate (EraCrypto era) ->
      Hash (HASH (EraCrypto era)) (VerKeyVRF (VRF (EraCrypto era))) ->
      ConwayTxCert era
    )
cGovern = Constr "cGovernT" (\a b c -> ConwayTxCertConstitutional (ConstitutionalDelegCert a b c))
-}
-- =====================================

certsPreds :: forall era. Reflect era => Proof era -> [Pred era]
certsPreds p = case whichTxCert p of
  TxCertShelleyToBabbage ->
    [ certs :<-: (Constr "TxCertF" (fmap (TxCertF p)) ^$ shelleycerts)
    , Sized (Range 1 6) epochDelta
    , Choose
        (Range 0 5)
        shelleycerts
        [ (sRegKey ^$ stakeCred, [NotMember stakeCred (Dom rewards)])
        , (sUnRegKey ^$ deregkey, [MapMember deregkey (Lit CoinR (Coin 0)) (Left rewards)])
        ,
          ( sDelegStake ^$ stakeCred ^$ poolHash
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools)]
          )
        ,
          ( sRetirePool ^$ poolHash ^$ epoch
          , [Member (Left poolHash) (Dom regPools), epoch :<-: (Constr "+" (+) ^$ currentEpoch ^$ epochDelta)]
          )
        ,
          ( sRegPool ^$ poolParams
          ,
            [ -- Pick a random PoolParams, except constrain the poolId and the poolRewAcnt, by the additional Preds
              Component
                (Right poolParams)
                [field PoolParamsR poolId, field PoolParamsR poolRewAcnt, field PoolParamsR poolOwners]
            , Member (Left poolId) poolHashUniv
            , poolRewAcnt :<-: (Constr "mkRewAcnt" RewardAcnt ^$ network ^$ rewCred)
            , Member (Right rewCred) credsUniv
            , Subset poolOwners stakeHashUniv
            ]
          )
        ,
          ( sMirDistribute ^$ available ^$ pot ^$ mirdistr
          ,
            [ Random pot
            , available :<-: availableT pot
            , SumsTo (Left (DeltaCoin (-100))) (Delta available) GTE [SumMap mirdistr]
            ]
          )
        ,
          ( sMirShift ^$ available ^$ pot ^$ mircoin
          ,
            [ Random pot
            , available :<-: availableT pot
            , SumsTo (Left (Coin 1)) available GTE [One mircoin]
            ]
          )
        ]
    ]
  TxCertConwayToConway ->
    [ certs :<-: (Constr "TxCertF" (fmap (TxCertF p)) ^$ conwaycerts)
    , Sized (Range 1 6) epochDelta
    , Choose
        (Range 4 6)
        conwaycerts
        [
          ( cRegKey ^$ stakeCred ^$ mkeydeposit
          ,
            [ NotMember stakeCred (Dom rewards)
            , Maybe mkeydeposit (idTarget kd) [kd :=: (keyDepAmt p)]
            ]
          )
        ,
          ( cUnRegKey ^$ stakeCred ^$ mkeydeposit
          ,
            [ MapMember stakeCred (Lit CoinR (Coin 0)) (Left rewards)
            , Maybe mkeydeposit (idTarget kd) [MapMember stakeCred kd (Left stakeDeposits)]
            ]
          )
        ,
          ( cDelegStake ^$ stakeCred ^$ poolHash
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools)]
          )
        , (cDelegVote ^$ stakeCred ^$ vote, [Member (Left stakeCred) (Dom rewards), Member (Left vote) voteUniv])
        ,
          ( cRegDelegStake ^$ stakeCred ^$ poolHash ^$ kd
          , [Member (Left stakeCred) (Dom rewards), Member (Left poolHash) (Dom regPools), kd :=: (keyDepAmt p)]
          )
        ,
          ( cRegDelegVote ^$ stakeCred ^$ vote ^$ kd
          , [Member (Left stakeCred) (Dom rewards), Member (Left vote) voteUniv, kd :=: (keyDepAmt p)]
          )
        ,
          ( cRegDelegStakeVote ^$ stakeCred ^$ poolHash ^$ vote ^$ kd
          ,
            [ Member (Left stakeCred) (Dom rewards)
            , Member (Left vote) voteUniv
            , Member (Left poolHash) (Dom regPools)
            , kd :=: (keyDepAmt p)
            ]
          )
        ,
          ( cRegPool ^$ poolParams
          ,
            [ -- Pick a random PoolParams, except constrain the poolId and the poolRewAcnt, by the additional Preds
              Component
                (Right poolParams)
                [field PoolParamsR poolId, field PoolParamsR poolRewAcnt, field PoolParamsR poolOwners]
            , Member (Left poolId) poolHashUniv
            , poolRewAcnt :<-: (Constr "mkRewAcnt" RewardAcnt ^$ network ^$ rewCred)
            , Member (Right rewCred) credsUniv
            , Subset poolOwners stakeHashUniv
            ]
          )
        ,
          ( cRetirePool ^$ poolHash ^$ epoch
          , [Member (Left poolHash) (Dom regPools), epoch :<-: (Constr "+" (+) ^$ currentEpoch ^$ epochDelta)]
          )
        ]
    ]
  where
    stakeCred = var "stakeCred" CredR
    deregkey = var "destakeCred" CredR
    poolHash = var "poolHash" PoolHashR
    epoch = var "epoch" EpochR
    shelleycerts = var "shelleycerts" (ListR ShelleyTxCertR)
    conwaycerts = var "conwaycerts" (ListR ConwayTxCertR)
    poolParams = var "poolParams" PoolParamsR
    pot = var "pot" MIRPotR
    mirdistr = var "mirdistr" (MapR CredR DeltaCoinR)
    mircoin = var "mircoin" CoinR
    mkeydeposit = var "mkeyDeposit" (MaybeR CoinR)
    kd = var "kd" CoinR
    vote = var "vote" VCredR
    epochDelta = var "epochDelta" EpochR
    -- poolId and poolRewAcnt are used as 'Fields' in the 'Component' Pred, they need 'Yes' Access
    -- Component [f1,f1] , means a random value except fo constraining the fields given.
    poolId = Var (V "poolId" PoolHashR (Yes PoolParamsR (lens ppId (\x i -> x {ppId = i}))))
    poolOwners = Var (V "poolOwners" (SetR StakeHashR) (Yes PoolParamsR (lens ppOwners (\x i -> x {ppOwners = i}))))
    poolRewAcnt = Var (V "poolRewAcnt" RewardAcntR (Yes PoolParamsR (lens ppRewardAcnt (\x r -> x {ppRewardAcnt = r}))))
    rewCred = Var (V "rewCred" CredR No)
    available = Var (V "available" CoinR No)

certsStage ::
  Reflect era =>
  Proof era ->
  Subst era ->
  Gen (Subst era)
certsStage proof subst0 = do
  let preds = certsPreds proof
  toolChainSub proof standardOrderInfo preds subst0

main :: Int -> IO ()
main seed = do
  let proof =
        -- Conway Standard
        Babbage Standard
  env <-
    generateWithSeed
      seed
      ( pure []
          >>= pParamsStage proof
          >>= universeStage proof
          >>= vstateStage proof
          >>= pstateStage proof
          >>= dstateStage proof
          >>= certsStage proof
          >>= (\subst -> monadTyped (substToEnv subst emptyEnv))
      )
  -- rewritten <- snd <$> generate (rewriteGen (1,  certsPreds proof))
  -- putStrLn (show rewritten)
  certsv <- monadTyped (findVar (unVar certs) env)
  putStrLn (show (ppList (\(TxCertF _ x) -> pcTxCert proof x) certsv))
  _ <- goRepl proof env ""
  pure ()
