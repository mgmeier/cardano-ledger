{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- | This module contains the type of protocol parameters and EraPParams instance
module Cardano.Ledger.Conway.PParams (
  BabbagePParams (..),
  ConwayPParams (..),
  getLanguageView,
  LangDepView (..),
  encodeLangViews,
  upgradeConwayPParams,
  UpgradeConwayPParams (..),
)
where

import Cardano.Ledger.Alonzo.PParams (OrdExUnits (..))
import Cardano.Ledger.Alonzo.Scripts (CostModels, ExUnits (..), Prices (Prices), emptyCostModels)
import Cardano.Ledger.Babbage (BabbageEra)
import Cardano.Ledger.Babbage.Core
import Cardano.Ledger.Babbage.PParams
import Cardano.Ledger.BaseTypes (EpochNo (EpochNo), NonNegativeInterval, ProtVer (ProtVer), UnitInterval)
import Cardano.Ledger.Binary
import Cardano.Ledger.Binary.Coders
import Cardano.Ledger.Coin (Coin (Coin))
import Cardano.Ledger.Conway.Core
import Cardano.Ledger.Conway.Era (ConwayEra)
import Cardano.Ledger.Conway.Governance (ConwayGovernance)
import Cardano.Ledger.Crypto
import Cardano.Ledger.HKD (HKD, HKDFunctor (..))
import Control.DeepSeq (NFData)
import Data.Aeson hiding (Encoding, decode, encode)
import qualified Data.Aeson as Aeson
import Data.Default.Class (Default (def))
import Data.Functor.Identity (Identity)
import qualified Data.Map.Strict as Map
import Data.Maybe.Strict (StrictMaybe (..), isSNothing)
import Data.Proxy
import GHC.Generics (Generic)
import Lens.Micro
import NoThunks.Class (NoThunks)
import Numeric.Natural (Natural)

-- | Conway Protocol parameters. Ways in which parameters have changed from Babbage:
-- addition of @drepDeposit@
data ConwayPParams f era = ConwayPParams
  { cppMinFeeA :: !(HKD f Coin)
  -- ^ The linear factor for the minimum fee calculation
  , cppMinFeeB :: !(HKD f Coin)
  -- ^ The constant factor for the minimum fee calculation
  , cppMaxBBSize :: !(HKD f Natural)
  -- ^ Maximal block body size
  , cppMaxTxSize :: !(HKD f Natural)
  -- ^ Maximal transaction size
  , cppMaxBHSize :: !(HKD f Natural)
  -- ^ Maximal block header size
  , cppKeyDeposit :: !(HKD f Coin)
  -- ^ The amount of a key registration deposit
  , cppPoolDeposit :: !(HKD f Coin)
  -- ^ The amount of a pool registration deposit
  , cppEMax :: !(HKD f EpochNo)
  -- ^ Maximum number of epochs in the future a pool retirement is allowed to
  -- be scheduled for.
  , cppNOpt :: !(HKD f Natural)
  -- ^ Desired number of pools
  , cppA0 :: !(HKD f NonNegativeInterval)
  -- ^ Pool influence
  , cppRho :: !(HKD f UnitInterval)
  -- ^ Monetary expansion
  , cppTau :: !(HKD f UnitInterval)
  -- ^ Treasury expansion
  , cppProtocolVersion :: !(HKD f ProtVer)
  -- ^ Protocol version
  , cppMinPoolCost :: !(HKD f Coin)
  -- ^ Minimum Stake Pool Cost
  , cppCoinsPerUTxOByte :: !(HKD f CoinPerByte)
  -- ^ Cost in lovelace per byte of UTxO storage
  , cppCostModels :: !(HKD f CostModels)
  -- ^ Cost models for non-native script languages
  , cppPrices :: !(HKD f Prices)
  -- ^ Prices of execution units (for non-native script languages)
  , cppMaxTxExUnits :: !(HKD f OrdExUnits)
  -- ^ Max total script execution resources units allowed per tx
  , cppMaxBlockExUnits :: !(HKD f OrdExUnits)
  -- ^ Max total script execution resources units allowed per block
  , cppMaxValSize :: !(HKD f Natural)
  -- ^ Max size of a Value in an output
  , cppCollateralPercentage :: !(HKD f Natural)
  -- ^ Percentage of the txfee which must be provided as collateral when
  -- including non-native scripts.
  , cppMaxCollateralInputs :: !(HKD f Natural)
  -- ^ Maximum number of collateral inputs allowed in a transaction
  , cppVotingThresholds :: !(HKD f (Map.Map Natural Natural)) -- New ones for Conway

  -- ^ TODO: Write a description here.
  , cppMinCCSize :: !(HKD f Natural)
  -- ^ Minimum size of the Constitutional Committee
  , cppCCTermLimit :: !(HKD f Natural)
  -- ^ The Constitutional Committee Term limit in number of Slots
  , cppGovExpiration :: !(HKD f Natural)
  -- ^ Governance action expiration in number of Slots
  , cppGovDeposit :: !(HKD f Coin)
  -- ^ The amount of the Governance Action deposit
  , cppDRepDeposit :: !(HKD f Coin)
  -- ^ The amount of a DRep registration deposit
  , cppDRepActivity :: !(HKD f EpochNo)
  -- ^ The number of Epochs that a DRep can perform no activity without loosing their @Active@ status.
  }
  deriving (Generic)

deriving instance Eq (ConwayPParams Identity era)

deriving instance Ord (ConwayPParams Identity era)

deriving instance Show (ConwayPParams Identity era)

instance NoThunks (ConwayPParams Identity era)

instance NFData (ConwayPParams Identity era)

deriving instance Eq (ConwayPParams StrictMaybe era)

deriving instance Ord (ConwayPParams StrictMaybe era)

deriving instance Show (ConwayPParams StrictMaybe era)

instance NoThunks (ConwayPParams StrictMaybe era)

instance NFData (ConwayPParams StrictMaybe era)

data UpgradeConwayPParams f = UpgradeConwayPParams
  { ucppVotingThresholds :: !(HKD f (Map.Map Natural Natural))
  , ucppMinCCSize :: !(HKD f Natural)
  , ucppCCTermLimit :: !(HKD f Natural)
  , ucppGovExpiration :: !(HKD f Natural)
  , ucppGovDeposit :: !(HKD f Coin)
  , ucppDRepDeposit :: !(HKD f Coin)
  , ucppDRepActivity :: !(HKD f EpochNo)
  }
  deriving (Generic)

deriving instance Eq (UpgradeConwayPParams Identity)

deriving instance Ord (UpgradeConwayPParams Identity)

deriving instance Show (UpgradeConwayPParams Identity)

instance NoThunks (UpgradeConwayPParams Identity)

instance NFData (UpgradeConwayPParams Identity)

deriving instance Eq (UpgradeConwayPParams StrictMaybe)

deriving instance Ord (UpgradeConwayPParams StrictMaybe)

deriving instance Show (UpgradeConwayPParams StrictMaybe)

instance NoThunks (UpgradeConwayPParams StrictMaybe)

instance NFData (UpgradeConwayPParams StrictMaybe)

instance Default (UpgradeConwayPParams Identity) where
  def =
    UpgradeConwayPParams
      { ucppVotingThresholds = Map.empty
      , ucppMinCCSize = 0
      , ucppCCTermLimit = 0
      , ucppGovExpiration = 0
      , ucppGovDeposit = Coin 0
      , ucppDRepDeposit = Coin 0
      , ucppDRepActivity = EpochNo 0
      }

instance Default (UpgradeConwayPParams StrictMaybe) where
  def =
    UpgradeConwayPParams
      { ucppVotingThresholds = SNothing
      , ucppMinCCSize = SNothing
      , ucppCCTermLimit = SNothing
      , ucppGovExpiration = SNothing
      , ucppGovDeposit = SNothing
      , ucppDRepDeposit = SNothing
      , ucppDRepActivity = SNothing
      }

instance Crypto c => EraPParams (ConwayEra c) where
  type PParamsHKD f (ConwayEra c) = ConwayPParams f (ConwayEra c)
  type UpgradePParams f (ConwayEra c) = UpgradeConwayPParams f
  type DowngradePParams f (ConwayEra c) = ()

  emptyPParamsIdentity = emptyConwayPParams
  emptyPParamsStrictMaybe = emptyConwayPParamsUpdate

  upgradePParamsHKD = upgradeConwayPParams
  downgradePParamsHKD () = downgradeConwayPParams

  hkdMinFeeAL = lens cppMinFeeA $ \pp x -> pp {cppMinFeeA = x}
  hkdMinFeeBL = lens cppMinFeeB $ \pp x -> pp {cppMinFeeB = x}
  hkdMaxBBSizeL = lens cppMaxBBSize $ \pp x -> pp {cppMaxBBSize = x}
  hkdMaxTxSizeL = lens cppMaxTxSize $ \pp x -> pp {cppMaxTxSize = x}
  hkdMaxBHSizeL = lens cppMaxBHSize $ \pp x -> pp {cppMaxBHSize = x}
  hkdKeyDepositL = lens cppKeyDeposit $ \pp x -> pp {cppKeyDeposit = x}
  hkdPoolDepositL = lens cppPoolDeposit $ \pp x -> pp {cppPoolDeposit = x}
  hkdEMaxL = lens cppEMax $ \pp x -> pp {cppEMax = x}
  hkdNOptL = lens cppNOpt $ \pp x -> pp {cppNOpt = x}
  hkdA0L = lens cppA0 $ \pp x -> pp {cppA0 = x}
  hkdRhoL = lens cppRho $ \pp x -> pp {cppRho = x}
  hkdTauL = lens cppTau $ \pp x -> pp {cppTau = x}
  hkdProtocolVersionL = lens cppProtocolVersion $ \pp x -> pp {cppProtocolVersion = x}
  hkdMinPoolCostL = lens cppMinPoolCost $ \pp x -> pp {cppMinPoolCost = x}

  ppDG = to (const minBound)
  hkdDL = notSupportedInThisEraL
  hkdExtraEntropyL = notSupportedInThisEraL
  hkdMinUTxOValueL = notSupportedInThisEraL

instance Crypto c => AlonzoEraPParams (ConwayEra c) where
  hkdCoinsPerUTxOWordL = notSupportedInThisEraL
  hkdCostModelsL = lens cppCostModels $ \pp x -> pp {cppCostModels = x}
  hkdPricesL = lens cppPrices $ \pp x -> pp {cppPrices = x}
  hkdMaxTxExUnitsL :: forall f. HKDFunctor f => Lens' (PParamsHKD f (ConwayEra c)) (HKD f ExUnits)
  hkdMaxTxExUnitsL =
    lens (hkdMap (Proxy @f) unOrdExUnits . cppMaxTxExUnits) $ \pp x ->
      pp {cppMaxTxExUnits = hkdMap (Proxy @f) OrdExUnits x}
  hkdMaxBlockExUnitsL :: forall f. HKDFunctor f => Lens' (PParamsHKD f (ConwayEra c)) (HKD f ExUnits)
  hkdMaxBlockExUnitsL =
    lens (hkdMap (Proxy @f) unOrdExUnits . cppMaxBlockExUnits) $ \pp x ->
      pp {cppMaxBlockExUnits = hkdMap (Proxy @f) OrdExUnits x}
  hkdMaxValSizeL = lens cppMaxValSize $ \pp x -> pp {cppMaxValSize = x}
  hkdCollateralPercentageL =
    lens cppCollateralPercentage $ \pp x -> pp {cppCollateralPercentage = x}
  hkdMaxCollateralInputsL =
    lens cppMaxCollateralInputs $ \pp x -> pp {cppMaxCollateralInputs = x}

instance Crypto c => BabbageEraPParams (ConwayEra c) where
  hkdCoinsPerUTxOByteL = lens cppCoinsPerUTxOByte (\pp x -> pp {cppCoinsPerUTxOByte = x})

instance Crypto c => ConwayEraPParams (ConwayEra c) where
  hkdVotingThresholdsL = lens cppVotingThresholds (\pp x -> pp {cppVotingThresholds = x})
  hkdMinCCSizeL = lens cppMinCCSize (\pp x -> pp {cppMinCCSize = x})
  hkdCCTermLimitL = lens cppCCTermLimit (\pp x -> pp {cppCCTermLimit = x})
  hkdGovExpirationL = lens cppGovExpiration (\pp x -> pp {cppGovExpiration = x})
  hkdGovDepositL = lens cppGovDeposit (\pp x -> pp {cppGovDeposit = x})
  hkdDRepDepositL = lens cppDRepDeposit (\pp x -> pp {cppDRepDeposit = x})
  hkdDRepActivityL = lens cppDRepActivity (\pp x -> pp {cppDRepActivity = x})

instance Crypto c => EraGovernance (ConwayEra c) where
  type GovernanceState (ConwayEra c) = ConwayGovernance (ConwayEra c)

instance Era era => EncCBOR (ConwayPParams Identity era) where
  encCBOR ConwayPParams {..} =
    encodeListLen (29 + listLen cppProtocolVersion)
      <> encCBOR cppMinFeeA
      <> encCBOR cppMinFeeB
      <> encCBOR cppMaxBBSize
      <> encCBOR cppMaxTxSize
      <> encCBOR cppMaxBHSize
      <> encCBOR cppKeyDeposit
      <> encCBOR cppPoolDeposit
      <> encCBOR cppEMax
      <> encCBOR cppNOpt
      <> encCBOR cppA0
      <> encCBOR cppRho
      <> encCBOR cppTau
      <> encCBORGroup cppProtocolVersion
      <> encCBOR cppMinPoolCost
      <> encCBOR cppCoinsPerUTxOByte
      <> encCBOR cppCostModels
      <> encCBOR cppPrices
      <> encCBOR cppMaxTxExUnits
      <> encCBOR cppMaxBlockExUnits
      <> encCBOR cppMaxValSize
      <> encCBOR cppCollateralPercentage
      <> encCBOR cppMaxCollateralInputs
      -- New for Conway
      <> encCBOR cppVotingThresholds
      <> encCBOR cppMinCCSize
      <> encCBOR cppCCTermLimit
      <> encCBOR cppGovExpiration
      <> encCBOR cppGovDeposit
      <> encCBOR cppDRepDeposit
      <> encCBOR cppDRepActivity

instance Era era => ToCBOR (ConwayPParams Identity era) where
  toCBOR = toEraCBOR @era

instance Era era => DecCBOR (ConwayPParams Identity era) where
  decCBOR =
    decodeRecordNamed "PParams" (\pp -> 29 + fromIntegral (listLen (cppProtocolVersion pp))) $ do
      cppMinFeeA <- decCBOR
      cppMinFeeB <- decCBOR
      cppMaxBBSize <- decCBOR
      cppMaxTxSize <- decCBOR
      cppMaxBHSize <- decCBOR
      cppKeyDeposit <- decCBOR
      cppPoolDeposit <- decCBOR
      cppEMax <- decCBOR
      cppNOpt <- decCBOR
      cppA0 <- decCBOR
      cppRho <- decCBOR
      cppTau <- decCBOR
      cppProtocolVersion <- decCBORGroup
      cppMinPoolCost <- decCBOR
      cppCoinsPerUTxOByte <- decCBOR
      cppCostModels <- decCBOR
      cppPrices <- decCBOR
      cppMaxTxExUnits <- decCBOR
      cppMaxBlockExUnits <- decCBOR
      cppMaxValSize <- decCBOR
      cppCollateralPercentage <- decCBOR
      cppMaxCollateralInputs <- decCBOR
      -- New for Conway
      cppVotingThresholds <- decCBOR
      cppMinCCSize <- decCBOR
      cppCCTermLimit <- decCBOR
      cppGovExpiration <- decCBOR
      cppGovDeposit <- decCBOR
      cppDRepDeposit <- decCBOR
      cppDRepActivity <- decCBOR
      pure ConwayPParams {..}

instance Era era => FromCBOR (ConwayPParams Identity era) where
  fromCBOR = fromEraCBOR @era

instance Crypto c => ToJSON (ConwayPParams Identity (ConwayEra c)) where
  toJSON = object . conwayPParamsPairs
  toEncoding = pairs . mconcat . conwayPParamsPairs

conwayPParamsPairs ::
  forall era a.
  (ConwayEraPParams era, KeyValue a) =>
  PParamsHKD Identity era ->
  [a]
conwayPParamsPairs pp =
  uncurry (.=) <$> conwayPParamsHKDPairs (Proxy @Identity) pp

-- | Returns a basic "empty" `PParams` structure with all zero values.
emptyConwayPParams :: forall era. Era era => ConwayPParams Identity era
emptyConwayPParams =
  ConwayPParams
    { cppMinFeeA = Coin 0
    , cppMinFeeB = Coin 0
    , cppMaxBBSize = 0
    , cppMaxTxSize = 2048
    , cppMaxBHSize = 0
    , cppKeyDeposit = Coin 0
    , cppPoolDeposit = Coin 0
    , cppEMax = EpochNo 0
    , cppNOpt = 100
    , cppA0 = minBound
    , cppRho = minBound
    , cppTau = minBound
    , cppProtocolVersion = ProtVer (eraProtVerLow @era) 0
    , cppMinPoolCost = mempty
    , cppCoinsPerUTxOByte = CoinPerByte $ Coin 0
    , cppCostModels = emptyCostModels
    , cppPrices = Prices minBound minBound
    , cppMaxTxExUnits = OrdExUnits $ ExUnits 0 0
    , cppMaxBlockExUnits = OrdExUnits $ ExUnits 0 0
    , cppMaxValSize = 0
    , cppCollateralPercentage = 150
    , cppMaxCollateralInputs = 5
    , -- New in Conway
      cppVotingThresholds = Map.empty
    , cppMinCCSize = 0
    , cppCCTermLimit = 0
    , cppGovExpiration = 0
    , cppGovDeposit = Coin 0
    , cppDRepDeposit = Coin 0
    , cppDRepActivity = EpochNo 0
    }

emptyConwayPParamsUpdate :: ConwayPParams StrictMaybe era
emptyConwayPParamsUpdate =
  ConwayPParams
    { cppMinFeeA = SNothing
    , cppMinFeeB = SNothing
    , cppMaxBBSize = SNothing
    , cppMaxTxSize = SNothing
    , cppMaxBHSize = SNothing
    , cppKeyDeposit = SNothing
    , cppPoolDeposit = SNothing
    , cppEMax = SNothing
    , cppNOpt = SNothing
    , cppA0 = SNothing
    , cppRho = SNothing
    , cppTau = SNothing
    , cppProtocolVersion = SNothing
    , cppMinPoolCost = SNothing
    , cppCoinsPerUTxOByte = SNothing
    , cppCostModels = SNothing
    , cppPrices = SNothing
    , cppMaxTxExUnits = SNothing
    , cppMaxBlockExUnits = SNothing
    , cppMaxValSize = SNothing
    , cppCollateralPercentage = SNothing
    , cppMaxCollateralInputs = SNothing
    , -- New for Conway
      cppVotingThresholds = SNothing
    , cppMinCCSize = SNothing
    , cppCCTermLimit = SNothing
    , cppGovExpiration = SNothing
    , cppGovDeposit = SNothing
    , cppDRepDeposit = SNothing
    , cppDRepActivity = SNothing
    }

encodePParamsUpdate ::
  ConwayPParams StrictMaybe era ->
  Encode ('Closed 'Sparse) (ConwayPParams StrictMaybe era)
encodePParamsUpdate ppup =
  Keyed ConwayPParams
    !> omitStrictMaybe 0 (cppMinFeeA ppup) encCBOR
    !> omitStrictMaybe 1 (cppMinFeeB ppup) encCBOR
    !> omitStrictMaybe 2 (cppMaxBBSize ppup) encCBOR
    !> omitStrictMaybe 3 (cppMaxTxSize ppup) encCBOR
    !> omitStrictMaybe 4 (cppMaxBHSize ppup) encCBOR
    !> omitStrictMaybe 5 (cppKeyDeposit ppup) encCBOR
    !> omitStrictMaybe 6 (cppPoolDeposit ppup) encCBOR
    !> omitStrictMaybe 7 (cppEMax ppup) encCBOR
    !> omitStrictMaybe 8 (cppNOpt ppup) encCBOR
    !> omitStrictMaybe 9 (cppA0 ppup) encCBOR
    !> omitStrictMaybe 10 (cppRho ppup) encCBOR
    !> omitStrictMaybe 11 (cppTau ppup) encCBOR
    !> omitStrictMaybe 14 (cppProtocolVersion ppup) encCBOR
    !> omitStrictMaybe 16 (cppMinPoolCost ppup) encCBOR
    !> omitStrictMaybe 17 (cppCoinsPerUTxOByte ppup) encCBOR
    !> omitStrictMaybe 18 (cppCostModels ppup) encCBOR
    !> omitStrictMaybe 19 (cppPrices ppup) encCBOR
    !> omitStrictMaybe 20 (cppMaxTxExUnits ppup) encCBOR
    !> omitStrictMaybe 21 (cppMaxBlockExUnits ppup) encCBOR
    !> omitStrictMaybe 22 (cppMaxValSize ppup) encCBOR
    !> omitStrictMaybe 23 (cppCollateralPercentage ppup) encCBOR
    !> omitStrictMaybe 24 (cppMaxCollateralInputs ppup) encCBOR
    -- New for Conway
    !> omitStrictMaybe 25 (cppVotingThresholds ppup) encCBOR
    !> omitStrictMaybe 26 (cppMinCCSize ppup) encCBOR
    !> omitStrictMaybe 27 (cppCCTermLimit ppup) encCBOR
    !> omitStrictMaybe 28 (cppGovExpiration ppup) encCBOR
    !> omitStrictMaybe 29 (cppGovDeposit ppup) encCBOR
    !> omitStrictMaybe 30 (cppDRepDeposit ppup) encCBOR
    !> omitStrictMaybe 31 (cppDRepActivity ppup) encCBOR
  where
    omitStrictMaybe ::
      Word -> StrictMaybe a -> (a -> Encoding) -> Encode ('Closed 'Sparse) (StrictMaybe a)
    omitStrictMaybe key x enc = Omit isSNothing (Key key (E (enc . fromSJust) x))

    fromSJust :: StrictMaybe a -> a
    fromSJust (SJust x) = x
    fromSJust SNothing = error "SNothing in fromSJust. This should never happen, it is guarded by isSNothing."

instance Era era => EncCBOR (ConwayPParams StrictMaybe era) where
  encCBOR ppup = encode (encodePParamsUpdate ppup)

updateField :: Word -> Field (ConwayPParams StrictMaybe era)
updateField = \case
  0 -> field (\x up -> up {cppMinFeeA = SJust x}) From
  1 -> field (\x up -> up {cppMinFeeB = SJust x}) From
  2 -> field (\x up -> up {cppMaxBBSize = SJust x}) From
  3 -> field (\x up -> up {cppMaxTxSize = SJust x}) From
  4 -> field (\x up -> up {cppMaxBHSize = SJust x}) From
  5 -> field (\x up -> up {cppKeyDeposit = SJust x}) From
  6 -> field (\x up -> up {cppPoolDeposit = SJust x}) From
  7 -> field (\x up -> up {cppEMax = SJust x}) From
  8 -> field (\x up -> up {cppNOpt = SJust x}) From
  9 -> field (\x up -> up {cppA0 = SJust x}) From
  10 -> field (\x up -> up {cppRho = SJust x}) From
  11 -> field (\x up -> up {cppTau = SJust x}) From
  14 -> field (\x up -> up {cppProtocolVersion = SJust x}) From
  16 -> field (\x up -> up {cppMinPoolCost = SJust x}) From
  17 -> field (\x up -> up {cppCoinsPerUTxOByte = SJust x}) From
  18 -> field (\x up -> up {cppCostModels = SJust x}) From
  19 -> field (\x up -> up {cppPrices = SJust x}) From
  20 -> field (\x up -> up {cppMaxTxExUnits = SJust x}) From
  21 -> field (\x up -> up {cppMaxBlockExUnits = SJust x}) From
  22 -> field (\x up -> up {cppMaxValSize = SJust x}) From
  23 -> field (\x up -> up {cppCollateralPercentage = SJust x}) From
  24 -> field (\x up -> up {cppMaxCollateralInputs = SJust x}) From
  -- New for Conway
  25 -> field (\x up -> up {cppVotingThresholds = SJust x}) From
  26 -> field (\x up -> up {cppMinCCSize = SJust x}) From
  27 -> field (\x up -> up {cppCCTermLimit = SJust x}) From
  28 -> field (\x up -> up {cppGovExpiration = SJust x}) From
  29 -> field (\x up -> up {cppGovDeposit = SJust x}) From
  30 -> field (\x up -> up {cppDRepDeposit = SJust x}) From
  31 -> field (\x up -> up {cppDRepActivity = SJust x}) From
  k -> field (\_x up -> up) (Invalid k)

instance Era era => DecCBOR (ConwayPParams StrictMaybe era) where
  decCBOR = decode (SparseKeyed "PParamsUpdate" emptyConwayPParamsUpdate updateField [])

instance Era era => ToCBOR (ConwayPParams StrictMaybe era) where
  toCBOR = toEraCBOR @era

instance Era era => FromCBOR (ConwayPParams StrictMaybe era) where
  fromCBOR = fromEraCBOR @era

instance
  forall era.
  ( ConwayEraPParams era
  , PParamsHKD StrictMaybe era ~ ConwayPParams StrictMaybe era
  ) =>
  ToJSON (ConwayPParams StrictMaybe era)
  where
  toJSON = object . conwayPParamsUpdatePairs
  toEncoding = pairs . mconcat . conwayPParamsUpdatePairs

conwayPParamsUpdatePairs ::
  forall era a.
  (ConwayEraPParams era, KeyValue a) =>
  PParamsHKD StrictMaybe era ->
  [a]
conwayPParamsUpdatePairs pp =
  [ k .= v
  | (k, SJust v) <- conwayPParamsHKDPairs (Proxy @StrictMaybe) pp
  ]

conwayPParamsHKDPairs ::
  forall era f.
  (ConwayEraPParams era, HKDFunctor f) =>
  Proxy f ->
  PParamsHKD f era ->
  [(Key, HKD f Aeson.Value)]
conwayPParamsHKDPairs px pp = babbagePParamsHKDPairs px pp <> conwayUpgradePParamsHKDPairs px pp

conwayUpgradePParamsHKDPairs ::
  forall era f.
  (ConwayEraPParams era, HKDFunctor f) =>
  Proxy f ->
  PParamsHKD f era ->
  [(Key, HKD f Aeson.Value)]
conwayUpgradePParamsHKDPairs px pp =
  [ ("votingThresholds", hkdMap px (toJSON @(Map.Map Natural Natural)) (pp ^. hkdVotingThresholdsL @era @f))
  , ("minCCSize", hkdMap px (toJSON @Natural) (pp ^. hkdMinCCSizeL @era @f))
  , ("cCTermLimit", hkdMap px (toJSON @Natural) (pp ^. hkdCCTermLimitL @era @f))
  , ("govExpiration", hkdMap px (toJSON @Natural) (pp ^. hkdGovExpirationL @era @f))
  , ("govDeposit", hkdMap px (toJSON @Coin) (pp ^. hkdGovDepositL @era @f))
  , ("dRepDeposit", hkdMap px (toJSON @Coin) (pp ^. hkdDRepDepositL @era @f))
  , ("dRepActivity", hkdMap px (toJSON @EpochNo) (pp ^. hkdDRepActivityL @era @f))
  ]

upgradeConwayPParams ::
  forall f c.
  UpgradeConwayPParams f ->
  PParamsHKD f (BabbageEra c) ->
  ConwayPParams f (ConwayEra c)
upgradeConwayPParams UpgradeConwayPParams {..} BabbagePParams {..} =
  ConwayPParams
    { cppMinFeeA = bppMinFeeA
    , cppMinFeeB = bppMinFeeB
    , cppMaxBBSize = bppMaxBBSize
    , cppMaxTxSize = bppMaxTxSize
    , cppMaxBHSize = bppMaxBHSize
    , cppKeyDeposit = bppKeyDeposit
    , cppPoolDeposit = bppPoolDeposit
    , cppEMax = bppEMax
    , cppNOpt = bppNOpt
    , cppA0 = bppA0
    , cppRho = bppRho
    , cppTau = bppTau
    , cppProtocolVersion = bppProtocolVersion
    , cppMinPoolCost = bppMinPoolCost
    , cppCoinsPerUTxOByte = bppCoinsPerUTxOByte
    , cppCostModels = bppCostModels
    , cppPrices = bppPrices
    , cppMaxTxExUnits = bppMaxTxExUnits
    , cppMaxBlockExUnits = bppMaxBlockExUnits
    , cppMaxValSize = bppMaxValSize
    , cppCollateralPercentage = bppCollateralPercentage
    , cppMaxCollateralInputs = bppMaxCollateralInputs
    , -- New for Conway
      cppVotingThresholds = ucppVotingThresholds
    , cppMinCCSize = ucppMinCCSize
    , cppCCTermLimit = ucppCCTermLimit
    , cppGovExpiration = ucppGovExpiration
    , cppGovDeposit = ucppGovDeposit
    , cppDRepDeposit = ucppDRepDeposit
    , cppDRepActivity = ucppDRepActivity
    }

downgradeConwayPParams ::
  forall f c.
  ConwayPParams f (ConwayEra c) ->
  PParamsHKD f (BabbageEra c)
downgradeConwayPParams ConwayPParams {..} =
  BabbagePParams
    { bppMinFeeA = cppMinFeeA
    , bppMinFeeB = cppMinFeeB
    , bppMaxBBSize = cppMaxBBSize
    , bppMaxTxSize = cppMaxTxSize
    , bppMaxBHSize = cppMaxBHSize
    , bppKeyDeposit = cppKeyDeposit
    , bppPoolDeposit = cppPoolDeposit
    , bppEMax = cppEMax
    , bppNOpt = cppNOpt
    , bppA0 = cppA0
    , bppRho = cppRho
    , bppTau = cppTau
    , bppProtocolVersion = cppProtocolVersion
    , bppMinPoolCost = cppMinPoolCost
    , bppCoinsPerUTxOByte = cppCoinsPerUTxOByte
    , bppCostModels = cppCostModels
    , bppPrices = cppPrices
    , bppMaxTxExUnits = cppMaxTxExUnits
    , bppMaxBlockExUnits = cppMaxBlockExUnits
    , bppMaxValSize = cppMaxValSize
    , bppCollateralPercentage = cppCollateralPercentage
    , bppMaxCollateralInputs = cppMaxCollateralInputs
    }
