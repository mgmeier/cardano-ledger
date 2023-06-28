{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Conway.Genesis (
  ConwayGenesis (..),
)
where

import Cardano.Ledger.Binary (
  DecCBOR (..),
  EncCBOR (..),
  FromCBOR (..),
  ToCBOR (..),
 )
import Cardano.Ledger.Binary.Coders
import Cardano.Ledger.Conway.Era (ConwayEra)
import Cardano.Ledger.Conway.PParams (UpgradeConwayPParams)
import Cardano.Ledger.Core
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Keys (GenDelegs (..))
import Data.Aeson (FromJSON (..), ToJSON, object, withObject, (.:))
import Data.Aeson.Types (KeyValue (..), ToJSON (..))
import Data.Functor.Identity (Identity)
import Data.Unit.Strict (forceElemsToWHNF)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks)

data ConwayGenesis c = ConwayGenesis
  { cgGenDelegs :: GenDelegs c
  , cgUpgradePParams :: UpgradeConwayPParams Identity
  }
  deriving (Eq, Generic, Show)

instance NoThunks (ConwayGenesis c)

-- | Genesis are always encoded with the version of era they are defined in.
instance Crypto c => DecCBOR (ConwayGenesis c)

instance Crypto c => EncCBOR (ConwayGenesis c)

instance Crypto c => ToCBOR (ConwayGenesis c) where
  toCBOR ConwayGenesis {..} =
    toEraCBOR @(ConwayEra c) $
      encode $
        Rec ConwayGenesis
          !> To cgGenDelegs
          !> To cgUpgradePParams

instance Crypto c => FromCBOR (ConwayGenesis c) where
  fromCBOR =
    eraDecoder @(ConwayEra c) $
      decode $
        RecD ConwayGenesis
          <! From
          <! From

instance Crypto c => ToJSON (ConwayGenesis c) where
  toJSON ConwayGenesis {..} =
    object
      [ "genDelegs" .= toJSON cgGenDelegs
      , "upgradePParams" .= toJSON cgUpgradePParams
      ]

instance Crypto c => FromJSON (ConwayGenesis c) where
  parseJSON = withObject "ConwayGenesis" $ \obj -> do
    cgGenDelegs <- forceElemsToWHNF obj .: "genDelegs"
    cgUpgradePParams <- forceElemsToWHNF obj .: "upgradePParams"
    pure $ ConwayGenesis {..}
