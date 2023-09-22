{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Cardano.Ledger.DRep (
  DRep (DRepCredential, DRepAlwaysAbstain, DRepAlwaysNoConfidence),
  DRepState (..),
  drepExpiryL,
  drepAnchorL,
  drepDepositL,
) where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Binary (DecCBOR (..), EncCBOR (..))
import Cardano.Ledger.Binary.Coders (Decode (..), Encode (..), decode, encode, (!>), (<!))
import Cardano.Ledger.Coin (Coin)
import Cardano.Ledger.Credential (Credential (..))
import Cardano.Ledger.Crypto (Crypto)
import Cardano.Ledger.Hashes (ScriptHash)
import Cardano.Ledger.Keys (KeyHash (..), KeyRole (..))
import Cardano.Ledger.TreeDiff (ToExpr)
import Control.DeepSeq (NFData (..))
import Data.Aeson (ToJSON (..))
import GHC.Generics (Generic)
import Lens.Micro
import NoThunks.Class (NoThunks (..))

-- =======================================
-- DRep and DRepState

data DRep c
  = DRepKeyHash !(KeyHash 'DRepRole c)
  | DRepScriptHash !(ScriptHash c)
  | DRepAlwaysAbstain
  | DRepAlwaysNoConfidence
  deriving (Show, Eq, Ord, Generic, NoThunks, NFData, ToExpr, ToJSON)

instance Crypto c => EncCBOR (DRep c) where
  encCBOR (DRepKeyHash kh) =
    encode $
      Sum DRepKeyHash 0
        !> To kh
  encCBOR (DRepScriptHash sh) =
    encode $
      Sum DRepScriptHash 1
        !> To sh
  encCBOR DRepAlwaysAbstain =
    encode $
      Sum DRepAlwaysAbstain 2
  encCBOR DRepAlwaysNoConfidence =
    encode $
      Sum DRepAlwaysNoConfidence 3

instance Crypto c => DecCBOR (DRep c) where
  decCBOR = decode $
    Summands "DRep" $ \case
      0 -> SumD DRepKeyHash <! From
      1 -> SumD DRepScriptHash <! From
      2 -> SumD DRepAlwaysAbstain
      3 -> SumD DRepAlwaysNoConfidence
      k -> Invalid k

dRepToCred :: DRep c -> Maybe (Credential 'DRepRole c)
dRepToCred (DRepKeyHash kh) = Just $ KeyHashObj kh
dRepToCred (DRepScriptHash sh) = Just $ ScriptHashObj sh
dRepToCred _ = Nothing

pattern DRepCredential :: Credential 'DRepRole c -> DRep c
pattern DRepCredential c <- (dRepToCred -> Just c)
  where
    DRepCredential c = case c of
      ScriptHashObj sh -> DRepScriptHash sh
      KeyHashObj kh -> DRepKeyHash kh

{-# COMPLETE DRepCredential, DRepAlwaysAbstain, DRepAlwaysNoConfidence :: DRep #-}

data DRepState c = DRepState
  { drepExpiry :: !EpochNo
  , drepAnchor :: !(StrictMaybe (Anchor c))
  , drepDeposit :: !Coin
  }
  deriving (Show, Eq, Ord, Generic)

instance NoThunks (DRepState era)

instance Crypto c => NFData (DRepState c)

instance Crypto c => DecCBOR (DRepState c) where
  decCBOR =
    decode $
      RecD DRepState
        <! From
        <! From
        <! From

instance Crypto c => EncCBOR (DRepState c) where
  encCBOR DRepState {..} =
    encode $
      Rec DRepState
        !> To drepExpiry
        !> To drepAnchor
        !> To drepDeposit

instance ToExpr (DRepState c)

instance Crypto c => ToJSON (DRepState c)

drepExpiryL :: Lens' (DRepState c) EpochNo
drepExpiryL = lens drepExpiry (\x y -> x {drepExpiry = y})

drepAnchorL :: Lens' (DRepState c) (StrictMaybe (Anchor c))
drepAnchorL = lens drepAnchor (\x y -> x {drepAnchor = y})

drepDepositL :: Lens' (DRepState c) Coin
drepDepositL = lens drepDeposit (\x y -> x {drepDeposit = y})
