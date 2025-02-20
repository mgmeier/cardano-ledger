{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Conway.Governance.Proposals (
  Proposals,
  proposalsIds,
  proposalsAddVote,
  proposalsInsertGovAction,
  proposalsActions,
  proposalsRemoveIds,
  proposalsLookupId,
  fromGovActionStateSeq,
  proposalsGovActionStates,
  -- Testing
  isConsistent_,
) where

import Cardano.Ledger.Binary (DecCBOR (..), DecShareCBOR (..), EncCBOR (..))
import Cardano.Ledger.Conway.Core (Era (..), EraPParams)
import Cardano.Ledger.Conway.Governance.Procedures (
  GovActionId,
  GovActionState (..),
  Vote,
  Voter (..),
  gasCommitteeVotesL,
  gasDRepVotesL,
  gasStakePoolVotesL,
 )
import Cardano.Ledger.TreeDiff (ToExpr)
import Control.DeepSeq (NFData)
import Data.Aeson (ToJSON)
import Data.Default.Class (Default (..))
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import qualified Data.OMap.Strict as OMap
import Data.Sequence.Strict (StrictSeq (..))
import Data.Set (Set)
import GHC.Generics (Generic)
import Lens.Micro (Lens', (%~))
import NoThunks.Class (NoThunks)

newtype Proposals era
  = Proposals
      (OMap.OMap (GovActionId (EraCrypto era)) (GovActionState era))
  deriving newtype (Show, Eq)
  deriving stock (Generic)

instance EraPParams era => ToExpr (Proposals era)

instance EraPParams era => ToJSON (Proposals era)

instance EraPParams era => NFData (Proposals era)

instance EraPParams era => NoThunks (Proposals era)

instance Default (Proposals era) where
  def = Proposals def

instance EraPParams era => EncCBOR (Proposals era) where
  encCBOR = encCBOR . proposalsActions

instance EraPParams era => DecCBOR (Proposals era) where
  decCBOR = fromGovActionStateSeq <$> decCBOR

-- TODO: Implement Sharing: https://github.com/input-output-hk/cardano-ledger/issues/3486
instance EraPParams era => DecShareCBOR (Proposals era) where
  decShareCBOR _ = fromGovActionStateSeq <$> decCBOR

-- | Insert a `GovActionState`, overwriting an entry of it if the
-- corresponding `GovActionId` already exists.
proposalsInsertGovAction ::
  GovActionState era ->
  Proposals era ->
  Proposals era
proposalsInsertGovAction gas (Proposals omap) =
  Proposals (omap OMap.||> gas)

-- | Get the sequence of `GovActionState`s
proposalsActions ::
  Proposals era ->
  StrictSeq (GovActionState era)
proposalsActions (Proposals omap) = OMap.toStrictSeq omap

-- | Get the sequence of `GovActionId`s
proposalsIds ::
  Proposals era ->
  StrictSeq (GovActionId (EraCrypto era))
proposalsIds (Proposals omap) = OMap.toStrictSeqOKeys omap

-- | Get the unordered map of `GovActionId`s and `GovActionState`s
proposalsGovActionStates ::
  Proposals era ->
  Map (GovActionId (EraCrypto era)) (GovActionState era)
proposalsGovActionStates (Proposals omap) = OMap.toMap omap

-- | Add a vote to an existing `GovActionState` This is a no-op if the .
-- provided `GovActionId` does not already exist                       .
proposalsAddVote ::
  Voter (EraCrypto era) ->
  Vote ->
  GovActionId (EraCrypto era) ->
  Proposals era ->
  Proposals era
proposalsAddVote voter vote gai (Proposals omap) =
  Proposals $ OMap.adjust updateVote gai omap
  where
    insertVote ::
      Ord k =>
      Lens' (GovActionState era) (Map k Vote) ->
      k ->
      GovActionState era ->
      GovActionState era
    insertVote l k = l %~ Map.insert k vote
    updateVote = case voter of
      DRepVoter c -> insertVote gasDRepVotesL c
      StakePoolVoter kh -> insertVote gasStakePoolVotesL kh
      CommitteeVoter c -> insertVote gasCommitteeVotesL c

-- | Extract `GovActionState`s for the given set of `GovActionId`s from the `Proposals`
proposalsRemoveIds ::
  Set (GovActionId (EraCrypto era)) ->
  Proposals era ->
  (Proposals era, Map.Map (GovActionId (EraCrypto era)) (GovActionState era))
proposalsRemoveIds gais (Proposals omap) =
  let (retained, removed) = OMap.extractKeys gais omap
   in (Proposals retained, removed)

proposalsLookupId ::
  GovActionId (EraCrypto era) ->
  Proposals era ->
  Maybe (GovActionState era)
proposalsLookupId gai (Proposals omap) = OMap.lookup gai omap

-- | Converts a sequence of `GovActionState`s to a `Proposals`.
--
-- /Warning/ - This function expects `GovActionState`'s to have unique
-- `GovActionId`s, because duplicate Ids will result in `GovActionStates`
-- to be dropped.
fromGovActionStateSeq :: StrictSeq (GovActionState era) -> Proposals era
fromGovActionStateSeq = Proposals . OMap.fromFoldable

-- | Internal function for checking if the invariants are maintained
isConsistent_ :: Proposals era -> Bool
isConsistent_ (Proposals omap) = OMap.invariantHolds' omap
