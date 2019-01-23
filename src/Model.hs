-- |

{-# LANGUAGE OverloadedLists, LambdaCase #-}

module Model where

import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

-- The type of truth values.
type T = Bool

-- The type of individuals.
data E = Hubert | Paul deriving (Eq, Show, Bounded, Enum)

-- The type of possible worlds.
data S = W1 | W2 | W3 | W4 deriving (Eq, Show, Bounded, Enum, Ord)

worlds :: Set S
worlds = [W1 .. W4]

-- One-place assertive predicates
_smokesNow :: E -> Set S
_smokesNow = \case
  Paul   -> [W1, W2]
  Hubert -> [W1, W3]

_didSmoke :: E -> Set S
_didSmoke = \case
  Paul   -> [W1, W3]
  Hubert -> [W1, W2]

_vapes :: E -> Set S
_vapes = \case
  Paul   -> [W1, W2]
  Hubert -> [W3, W4]
