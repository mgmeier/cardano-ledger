module Delegation.StakePool
  ( StakePool(..)
  , Delegation(..)
  ) where

import           Data.Map        (Map)

import           Coin            (Coin)
import           Keys

-- |A stake pool.
data StakePool = StakePool
                   { poolPubKey  :: VKey
                   , poolPledges :: Map VKey Coin
                   , poolCost    :: Coin
                   , poolMargin  :: Float -- TODO is float okay?
                   , poolAltAcnt :: Maybe HashKey
                   } deriving (Show, Eq, Ord)

-- |The delegation of one stake key to another.
data Delegation = Delegation { delegator :: VKey
                             , delegatee :: VKey }
                             deriving (Show, Eq, Ord)
