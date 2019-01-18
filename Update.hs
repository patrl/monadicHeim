{-# LANGUAGE OverloadedLists, LambdaCase #-}

module Update where

import           Control.Monad.State
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

-- unicode set theory symbols for readability

(∩) :: Ord a => Set a -> Set a -> Set a
(∩) = Set.intersection

(∪) :: Ord a => Set a -> Set a -> Set a
(∪) = Set.union

(∖) :: Ord a => Set a -> Set a -> Set a
(∖) = (Set.\\)

(⊆) :: Ord a => Set a -> Set a -> Bool
(⊆) = Set.isSubsetOf

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

-- Some basic propositional operators. Note that I've supplied them with an additional parameter -- a contextual domain of worlds.
-- The reason for this will become clear later on.

propNeg :: Set S -> Set S -> Set S
propNeg = (∖)

propImplic :: Set S -> Set S -> Set S -> Set S
propImplic dom p q = dom ∖ p ∪ q

propConj :: Set S -> Set S -> Set S -> Set S
propConj dom p q = dom ∩ p ∩ q

propDisj :: Set S -> Set S -> Set S -> Set S
propDisj dom p q = dom ∩ (p ∪ q)

propEntails :: Set S -> Set S -> Bool
propEntails = (⊆)

-- The type of (partial) Stalnakerian update.
type U = StateT (Set S) Maybe
-- N.b. that without the boilerplate, this is:
-- U a = Set S -> Maybe (a, Set S)

-- A presuppositional predicate
_stoppedSmoking :: E -> U (Set S)
_stoppedSmoking = toPresuppPred _didSmoke (propNeg worlds <$> _smokesNow)

-- _stoppedSmoking' :: E -> S -> Maybe T
-- _stoppedSmoking' x w = if w Set.member _didSmoke x then undefined else undefined


-- a helper function from a presupposition and an assertion to the corresponding presuppositional predicate.
toPresuppPred :: (E -> Set S) -> (E -> Set S) -> E -> U (Set S)
toPresuppPred presupp assertion x = StateT
  (\c -> if c `propEntails` presupp x
    then Just (assertion x, c ∩ assertion x)
    else Nothing
  )

-- update the common ground.
assert :: U (Set S) -> U (Set S)
assert m = StateT
  (\c ->
    let outputVal   = evalStateT m c
        outputState = execStateT m c
    in  case (outputVal, outputState) of
          (Just p, Just c') -> Just (p, c' ∩ p)
          _                 -> Nothing
  )

-- Lift into the monad and update.
assertLift :: Set S -> U (Set S)
assertLift = assert . return

-- a helper function to update an ignorance context
updIgnorance :: U (Set S) -> Maybe (Set S, Set S)
updIgnorance = ($ worlds) . runStateT

---
-- Heimian connectives.
--
-- N.b. that the following definitions assume that every propositional node is asserted.
---

heimConj :: U (Set S) -> U (Set S) -> U (Set S)
m `heimConj` n = StateT
  (\c ->
    let iVal   = evalStateT m c -- first, feed the input state into the first conjunct.
        iState = execStateT m c
    in  case (iVal, iState) of
          (Just p, Just c') ->
            let oVal   = evalStateT n c' -- feed the first output state into the second conjunct, just in case it is defined.
                oState = execStateT n c'
            in  case (oVal, oState) of
                  (Just q, Just c'') -> Just (p ∩ q, c'')
                  _                  -> Nothing
          _ -> Nothing -- undefinedness at any stage results in overall undefinedness (strong Kleene)
  )

heimImplic :: U (Set S) -> U (Set S) -> U (Set S)
m `heimImplic` n = StateT
  (\c ->
    let interVal   = evalStateT m c
        interState = execStateT m c
    in  case (interVal, interState) of
          (Just p, Just c') ->
            let outVal   = evalStateT n c'
                outState = execStateT n c'
            in  case (outVal, outState) of
                  (Just q, Just c'') -> Just (worlds ∖ p ∪ q, c ∖ c' ∪ c'')
                  _                  -> Nothing
          _ -> Nothing
  )

heimNeg :: U (Set S) -> U (Set S)
heimNeg m = StateT
  (\c ->
    let outputVal   = evalStateT m c
        outputState = execStateT m c
    in  case (outputVal, outputState) of
          (Just p, Just c') -> Just (worlds ∖ p, c ∖ c')
          _                 -> Nothing
  )

heimDisj :: U (Set S) -> U (Set S) -> U (Set S)
m `heimDisj` n = StateT
  (\c ->
    let interVal   = evalStateT m c
        interState = execStateT m c
    in  case (interVal, interState) of
          (Just p, Just c') ->
            let outVal   = evalStateT n (c ∖ c') -- here is the weirdness of disjunction!
                outState = execStateT n (c ∖ c')
            in  case (outVal, outState) of
                  (Just q, Just c'') -> Just (p ∪ q, c' ∪ c'')
                  _                  -> Nothing
          _ -> Nothing
  )

-- Now, we'll define a couple of functions to lift propositional connectives into their Heimian
-- counterparts. This will work for everything except for disjunction.

dynLift :: (Set S -> Set S -> Set S) -> U (Set S) -> U (Set S)
dynLift op m = StateT
  (\c ->
    let outVal   = evalStateT m c
        outState = execStateT m c
    in  case (outVal, outState) of
          (Just p, Just c') -> Just (op worlds p, op c c')
          _                 -> Nothing
  )

dynLift2
  :: (Set S -> Set S -> Set S -> Set S) -> U (Set S) -> U (Set S) -> U (Set S)
dynLift2 op m n = StateT
  (\c ->
    let interVal   = evalStateT m c
        interState = execStateT m c
    in  case (interVal, interState) of
          (Just p, Just c') ->
            let outVal   = evalStateT n c'
                outState = execStateT n c'
            in  case (outVal, outState) of
                  (Just q, Just c'') -> Just (op worlds p q, op c c' c'')
                  _                  -> Nothing
          _ -> Nothing
  )

-- We can rescue our deviant prediction for disjunction by invoking an exhaustivity operator.
-- To simplify, we assume that a proposition is exhaustified relative to a single alternative.

exh :: Set S -> U (Set S) -> U (Set S)
exh alt m = StateT
  (\c ->
    let c' = c ∖ (c ∩ alt)
    in  let oVal   = evalStateT m c'
            oState = execStateT m c'
        in  case (oVal, oState) of
              (Just p, Just c'') -> Just (p, c'')
              _                  -> Nothing
  )

-- "Either Paul didn't smoke or (EXH) Paul stopped smoking"

-- >>> updIgnorance $ (dynLift2 propDisj) ((dynLift propNeg) $ assertLift $ _didSmoke Paul) (exh (propNeg worlds $ _didSmoke Paul) (_stoppedSmoking Paul))
-- Just (fromList [W2,W3,W4],fromList [W2,W4])

---
-- Facts demonstrated in the examples below:
--
-- heimConj == dynLift2 propConj
-- heimImplic == dynLift2 propImplic
-- heimNeg == dynLift propNeg
-- heimDisj != dynLift2 propDisj
---

-- "Paul did smoke and Paul stopped smoking." (presupposition satisfaction)

-- (a) with Heimian conjunction:
-- >>> updIgnorance $ (assertLift $ _didSmoke Paul) `heimConj` (_stoppedSmoking Paul)
-- Just (fromList [W3],fromList [W3])

-- (b) with lifted static conjunction:
-- >>> updIgnorance $ (dynLift2 propConj) (assertLift $ _didSmoke Paul) (_stoppedSmoking Paul)
-- Just (fromList [W3],fromList [W3])

-- "Paul stopped smoking and Paul did smoke." (presupposition failure)

-- (a) with Heimian conjunction:
-- >>> updIgnorance $ (_stoppedSmoking Paul) `heimConj` (assertLift $ _didSmoke Paul)
-- Nothing

-- (b) with lifted static conjunction:
-- >>> updIgnorance $ (dynLift2 propConj) (_stoppedSmoking Paul) (assertLift $ _didSmoke Paul)
-- Nothing

-- "Paul didn't stop smoking." (presupposition failure)

-- (a) with Heimian negation.
-- >>> updIgnorance $ heimNeg $ _stoppedSmoking Paul
-- Nothing

-- (b) with lifted propositional negation.
-- >>> updIgnorance $ (dynLift propNeg) $ _stoppedSmoking Paul
-- Nothing

-- "Paul did smoke and Paul didn't stop smoking." (presupposition satisfaction)

-- (a) with Heimian negation.
-- >>> updIgnorance $ (assertLift $ _didSmoke Paul) `heimConj` (heimNeg $ _stoppedSmoking Paul)
-- Just (fromList [W1],fromList [W1])

-- (b) with lifted propositional operators
-- >>> updIgnorance $ (dynLift2 propConj) (assertLift $ _didSmoke Paul) (dynLift propNeg $ _stoppedSmoking Paul)
-- Just (fromList [W1],fromList [W1])

-- "If Paul did smoke then Paul stopped smoking." (presupposition satisfaction)

-- (a) with Heimian implication:

-- >>> updIgnorance $ (assertLift $ _didSmoke Paul) `heimImplic` (_stoppedSmoking Paul)
-- Just (fromList [W2,W3,W4],fromList [W2,W3,W4])

-- (b) with lifted propositional implication:
-- >>> updIgnorance $ (dynLift2 propImplic) (assertLift $ _didSmoke Paul) (_stoppedSmoking Paul)
-- Just (fromList [W2,W3,W4],fromList [W2,W3,W4])

-- "If Paul didn't smoke then Paul stopped smoking." (presupposition failure)

-- (a) with Heimian operators:
-- >>> updIgnorance $ (heimNeg $ assertLift $ _didSmoke Paul) `heimImplic` (_stoppedSmoking Paul)
-- Nothing

-- (b) with lifted prop operators:
-- >>> updIgnorance $ (dynLift2 propImplic) (dynLift propNeg $ assertLift $ _didSmoke Paul) (_stoppedSmoking Paul)
-- Nothing

-- "Either Paul didn't smoke or Paul stopped smoking" (presupposition satisfaction)
-- >>> updIgnorance $ (heimNeg $ assertLift $ _didSmoke Paul) `heimDisj` (_stoppedSmoking Paul)
-- Just (fromList [W2,W3,W4],fromList [W2,W3,W4])

-- "Either Paul smoked or Paul stopped smoking" (presupposition failure)
-- >>> updIgnorance $ (assertLift $ _didSmoke Paul) `heimDisj` (_stoppedSmoking Paul)
-- Nothing

-- If we just lift propositional disjunction we get the wrong result.
-- >>> updIgnorance $ (dynLift2 propDisj) (dynLift propNeg $ assertLift $ _didSmoke Paul) (_stoppedSmoking Paul)
-- Nothing

-- >>> updIgnorance $ (dynLift2 propDisj) (assertLift $ _didSmoke Paul) (_stoppedSmoking Paul)
-- Just (fromList [W1,W3,W4],fromList [W1,W3])
