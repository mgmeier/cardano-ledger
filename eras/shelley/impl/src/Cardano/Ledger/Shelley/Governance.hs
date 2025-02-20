{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Cardano.Ledger.Shelley.Governance (
  EraGov (..),
  ShelleyGovState (..),
  Constitution (..),
  -- Lens
  proposalsL,
  futureProposalsL,
  curPParamsShelleyGovStateL,
  prevPParamsShelleyGovStateL,
  constitutionAnchorL,
  constitutionScriptL,
) where

import Cardano.Ledger.BaseTypes (Anchor, EpochNo, UnitInterval)
import Cardano.Ledger.Binary (
  DecCBOR (decCBOR),
  DecShareCBOR (..),
  EncCBOR (encCBOR),
  FromCBOR (..),
  ToCBOR (..),
  decNoShareCBOR,
  decodeNullStrictMaybe,
  encodeNullStrictMaybe,
 )
import Cardano.Ledger.Binary.Coders (Decode (..), Encode (..), decode, encode, (!>), (<!))
import Cardano.Ledger.CertState (Obligations)
import Cardano.Ledger.Coin (Coin, CompactForm)
import Cardano.Ledger.Core
import Cardano.Ledger.Credential (Credential)
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.DRep (DRep)
import Cardano.Ledger.Keys (KeyRole (..))
import Cardano.Ledger.Shelley.Era (ShelleyEra)
import Cardano.Ledger.Shelley.PParams (ProposedPPUpdates, emptyPPPUpdates)
import Cardano.Ledger.TreeDiff (ToExpr)
import Control.DeepSeq (NFData)
import Data.Aeson (
  FromJSON,
  KeyValue,
  ToJSON (..),
  object,
  pairs,
  withObject,
  (.:),
  (.:?),
  (.=),
 )
import Data.Aeson.Types (FromJSON (..))
import Data.Default.Class (Default (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe.Strict (StrictMaybe (..), maybeToStrictMaybe)
import GHC.Generics (Generic)
import Lens.Micro (Lens', lens)
import NoThunks.Class (NoThunks (..))

class
  ( EraPParams era
  , Eq (GovState era)
  , Show (GovState era)
  , NoThunks (GovState era)
  , NFData (GovState era)
  , EncCBOR (GovState era)
  , DecCBOR (GovState era)
  , DecShareCBOR (GovState era)
  , ToCBOR (GovState era)
  , FromCBOR (GovState era)
  , Default (GovState era)
  , ToJSON (GovState era)
  ) =>
  EraGov era
  where
  type GovState era = (r :: Type) | r -> era

  -- | Construct empty governance state
  emptyGovState :: GovState era
  emptyGovState = def

  -- | Returns `Nothing` for all eras starting with Conway, otherwise returns proposed
  -- pparams updates
  getProposedPPUpdates :: GovState era -> Maybe (ProposedPPUpdates era)
  getProposedPPUpdates _ = Nothing

  -- | Returns `Nothing` for all era preceding Conway, otherwise returns the hash of the constitution
  getConstitution :: GovState era -> Maybe (Constitution era)
  getConstitution = const Nothing

  getCommitteeMembers ::
    GovState era -> Maybe (Map (Credential 'ColdCommitteeRole (EraCrypto era)) EpochNo, UnitInterval)
  getCommitteeMembers = const Nothing

  -- | Lens for accessing current protocol parameters
  curPParamsGovStateL :: Lens' (GovState era) (PParams era)

  -- | Lens for accessing the previous protocol parameters
  prevPParamsGovStateL :: Lens' (GovState era) (PParams era)

  obligationGovState :: GovState era -> Obligations

  getDRepDistr :: GovState era -> Map (DRep (EraCrypto era)) (CompactForm Coin)

instance
  ( ToExpr (PParamsUpdate era)
  , ToExpr (PParams era)
  ) =>
  ToExpr (ShelleyGovState era)

instance Crypto c => EraGov (ShelleyEra c) where
  type GovState (ShelleyEra c) = ShelleyGovState (ShelleyEra c)

  getProposedPPUpdates = Just . proposals

  curPParamsGovStateL = curPParamsShelleyGovStateL

  prevPParamsGovStateL = prevPParamsShelleyGovStateL

  obligationGovState = const mempty -- No GovState obigations in ShelleyEra

  getDRepDistr = const Map.empty

data ShelleyGovState era = ShelleyGovState
  { proposals :: !(ProposedPPUpdates era)
  , futureProposals :: !(ProposedPPUpdates era)
  , sgovPp :: !(PParams era)
  , sgovPrevPp :: !(PParams era)
  }
  deriving (Generic)

proposalsL :: Lens' (ShelleyGovState era) (ProposedPPUpdates era)
proposalsL = lens proposals (\sgov x -> sgov {proposals = x})

futureProposalsL :: Lens' (ShelleyGovState era) (ProposedPPUpdates era)
futureProposalsL = lens futureProposals (\sgov x -> sgov {futureProposals = x})

curPParamsShelleyGovStateL :: Lens' (ShelleyGovState era) (PParams era)
curPParamsShelleyGovStateL = lens sgovPp (\sps x -> sps {sgovPp = x})

prevPParamsShelleyGovStateL :: Lens' (ShelleyGovState era) (PParams era)
prevPParamsShelleyGovStateL = lens sgovPrevPp (\sps x -> sps {sgovPrevPp = x})

deriving instance
  ( Show (PParamsUpdate era)
  , Show (PParams era)
  ) =>
  Show (ShelleyGovState era)

deriving instance
  ( Eq (PParamsUpdate era)
  , Eq (PParams era)
  ) =>
  Eq (ShelleyGovState era)

instance
  ( NFData (PParamsUpdate era)
  , NFData (PParams era)
  ) =>
  NFData (ShelleyGovState era)

instance
  ( NoThunks (PParamsUpdate era)
  , NoThunks (PParams era)
  ) =>
  NoThunks (ShelleyGovState era)

instance
  ( Era era
  , EncCBOR (PParamsUpdate era)
  , EncCBOR (PParams era)
  ) =>
  EncCBOR (ShelleyGovState era)
  where
  encCBOR (ShelleyGovState ppup fppup pp ppp) =
    encode $
      Rec ShelleyGovState
        !> To ppup
        !> To fppup
        !> To pp
        !> To ppp

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  DecShareCBOR (ShelleyGovState era)
  where
  decShareCBOR _ =
    decode $
      RecD ShelleyGovState
        <! From
        <! From
        <! From
        <! From

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  DecCBOR (ShelleyGovState era)
  where
  decCBOR = decNoShareCBOR

instance
  ( Era era
  , EncCBOR (PParamsUpdate era)
  , EncCBOR (PParams era)
  ) =>
  ToCBOR (ShelleyGovState era)
  where
  toCBOR = toEraCBOR @era

instance
  ( Era era
  , DecCBOR (PParamsUpdate era)
  , DecCBOR (PParams era)
  ) =>
  FromCBOR (ShelleyGovState era)
  where
  fromCBOR = fromEraCBOR @era

instance EraPParams era => ToJSON (ShelleyGovState era) where
  toJSON = object . toPPUPStatePairs
  toEncoding = pairs . mconcat . toPPUPStatePairs

toPPUPStatePairs :: (KeyValue e a, EraPParams era) => ShelleyGovState era -> [a]
toPPUPStatePairs ShelleyGovState {..} =
  [ "proposals" .= proposals
  , "futureProposals" .= futureProposals
  , "curPParams" .= sgovPp
  , "prevPParams" .= sgovPrevPp
  ]

instance EraPParams era => Default (ShelleyGovState era) where
  def =
    ShelleyGovState
      emptyPPPUpdates
      emptyPPPUpdates
      emptyPParams
      emptyPParams

data Constitution era = Constitution
  { constitutionAnchor :: !(Anchor (EraCrypto era))
  , constitutionScript :: !(StrictMaybe (ScriptHash (EraCrypto era)))
  }
  deriving (Generic, Ord)

instance ToExpr (Constitution era)

constitutionAnchorL :: Lens' (Constitution era) (Anchor (EraCrypto era))
constitutionAnchorL = lens constitutionAnchor (\x y -> x {constitutionAnchor = y})

constitutionScriptL :: Lens' (Constitution era) (StrictMaybe (ScriptHash (EraCrypto era)))
constitutionScriptL = lens constitutionScript (\x y -> x {constitutionScript = y})

instance Era era => ToJSON (Constitution era) where
  toJSON = object . toConstitutionPairs
  toEncoding = pairs . mconcat . toConstitutionPairs

instance Era era => FromJSON (Constitution era) where
  parseJSON = withObject "Constitution" $ \o ->
    Constitution
      <$> o .: "anchor"
      <*> (maybeToStrictMaybe <$> (o .:? "script"))

toConstitutionPairs :: (KeyValue e a, Era era) => Constitution era -> [a]
toConstitutionPairs c@(Constitution _ _) =
  let Constitution {..} = c
   in ["anchor" .= constitutionAnchor]
        <> ["script" .= cScript | SJust cScript <- [constitutionScript]]

deriving instance Eq (Constitution era)

deriving instance Show (Constitution era)

instance Era era => Default (Constitution era) where
  def = Constitution def def

instance Era era => DecCBOR (Constitution era) where
  decCBOR =
    decode $
      RecD Constitution
        <! From
        <! D (decodeNullStrictMaybe decCBOR)

instance Era era => EncCBOR (Constitution era) where
  encCBOR Constitution {..} =
    encode $
      Rec (Constitution @era)
        !> To constitutionAnchor
        !> E (encodeNullStrictMaybe encCBOR) constitutionScript

instance Era era => ToCBOR (Constitution era) where
  toCBOR = toEraCBOR @era

instance Era era => FromCBOR (Constitution era) where
  fromCBOR = fromEraCBOR @era

instance Era era => NFData (Constitution era)

instance Era era => NoThunks (Constitution era)
