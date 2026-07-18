-- | The library's own proof-of-laws: every exported class instance and both
-- | operator types exercised against `Data.Order.Laws` with QuickCheck
-- | generators. Two worked examples double as documentation:
-- |
-- |   * the multiples connection `(_ * k) ⊣ (_ `div` k)` on `Ordered Int` —
-- |     the classic floor-division adjunction, integer-only;
-- |   * transitive closure of a small relation, built with `fixpointFrom`,
-- |     verified as a lawful `ClosureOperator`.
module Test.Main where

import Prelude hiding (join)

import Control.Apply (lift2, lift3)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Order.Closure (ClosureOperator(..), close, closedBy)
import Data.Order.Fixpoint (fixpointFrom, fixpointFromN)
import Data.Order.Galois (GaloisConnection(..), closureOf, kernelOf)
import Data.Order.Laws (absorption, closureExtensive, closureIdempotent, closureMonotone, galoisAdjunction, galoisCounit, galoisUnit, joinAssociative, joinCommutative, joinIdempotent, meetAssociative, meetCommutative, meetIdempotent, monotone, ordersAgree)
import Data.Order.Semilattice (Joined(..), Ordered(..), join, joins, leq)
import Data.Map (Map)
import Data.Map as Map
import Data.Newtype (unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)
import Test.Assert (assertEqual, assertTrue)
import Test.QuickCheck (quickCheckGen)
import Test.QuickCheck.Gen (Gen, arrayOf, chooseInt)

-- Generators ------------------------------------------------------------------

genSet :: Gen (Set Int)
genSet = Set.fromFoldable <$> arrayOf (chooseInt 0 20)

genOrdered :: Gen (Ordered Int)
genOrdered = Ordered <$> chooseInt (-50) 50

genMap :: Gen (Map Int (Ordered Int))
genMap = Map.fromFoldable <$> arrayOf (lift2 Tuple (chooseInt 0 5) genOrdered)

genMaybeSet :: Gen (Maybe (Set Int))
genMaybeSet = do
  b <- chooseInt 0 3
  case b of
    0 -> pure Nothing
    _ -> Just <$> genSet

-- | A relation over the universe {0..5}.
genRel :: Gen (Set (Tuple Int Int))
genRel = Set.fromFoldable <$> arrayOf (lift2 Tuple (chooseInt 0 5) (chooseInt 0 5))

-- Worked example 1: the multiples connection ---------------------------------

-- | `(_ * k) ⊣ (_ \`div\` k)` for positive k: `n * k ≤ m ⟺ n ≤ m / k`
-- | (floor division). The floor/ceiling adjunction, integers only.
multiples :: Int -> GaloisConnection (Ordered Int) (Ordered Int)
multiples k = GaloisConnection
  { lower: \(Ordered n) -> Ordered (n * k)
  , upper: \(Ordered m) -> Ordered (m `div` k)
  }

-- Worked example 2: transitive closure ---------------------------------------

-- | One composition pass: add `(a, c)` wherever `(a, b)` and `(b, c)` exist.
composeStep :: Set (Tuple Int Int) -> Set (Tuple Int Int)
composeStep r = join r new
  where
  pairs = Array.fromFoldable r
  new = Set.fromFoldable do
    Tuple a b <- pairs
    Tuple b' c <- pairs
    if b == b' then pure (Tuple a c) else []

transitiveClosure :: ClosureOperator (Set (Tuple Int Int))
transitiveClosure = ClosureOperator (fixpointFrom composeStep)

-- Main ------------------------------------------------------------------------

main :: Effect Unit
main = do
  log "-- Semilattice laws: Set Int (union/intersection) --"
  quickCheckGen $ lift3 joinAssociative genSet genSet genSet
  quickCheckGen $ lift2 joinCommutative genSet genSet
  quickCheckGen $ joinIdempotent <$> genSet
  quickCheckGen $ lift3 meetAssociative genSet genSet genSet
  quickCheckGen $ lift2 meetCommutative genSet genSet
  quickCheckGen $ meetIdempotent <$> genSet
  quickCheckGen $ lift2 (absorption :: Set Int -> Set Int -> Boolean) genSet genSet
  quickCheckGen $ lift2 (ordersAgree :: Set Int -> Set Int -> Boolean) genSet genSet
  -- the derived order IS inclusion
  quickCheckGen $ lift2 (\x y -> leq x y == Set.subset x y) genSet genSet

  log "-- Semilattice laws: Ordered Int (max/min) --"
  quickCheckGen $ lift3 joinAssociative genOrdered genOrdered genOrdered
  quickCheckGen $ lift2 joinCommutative genOrdered genOrdered
  quickCheckGen $ joinIdempotent <$> genOrdered
  quickCheckGen $ lift2 (absorption :: Ordered Int -> Ordered Int -> Boolean) genOrdered genOrdered
  quickCheckGen $ lift2 (ordersAgree :: Ordered Int -> Ordered Int -> Boolean) genOrdered genOrdered
  -- the derived order IS <=
  quickCheckGen $ lift2 (\x y -> leq x y == (unwrap x <= (unwrap y :: Int))) genOrdered genOrdered

  log "-- Semilattice laws: Map Int (Ordered Int) (pointwise) --"
  quickCheckGen $ lift3 joinAssociative genMap genMap genMap
  quickCheckGen $ lift2 joinCommutative genMap genMap
  quickCheckGen $ joinIdempotent <$> genMap

  log "-- Semilattice laws: Maybe (Set Int) (adjoined bottom) --"
  quickCheckGen $ lift3 joinAssociative genMaybeSet genMaybeSet genMaybeSet
  quickCheckGen $ lift2 joinCommutative genMaybeSet genMaybeSet
  quickCheckGen $ joinIdempotent <$> genMaybeSet

  log "-- Galois connection: (_ * k) ⊣ (_ `div` k), k ∈ 1..9 --"
  quickCheckGen do
    k <- chooseInt 1 9
    lift2 (galoisAdjunction (multiples k)) genOrdered genOrdered
  quickCheckGen do
    k <- chooseInt 1 9
    galoisUnit (multiples k) <$> genOrdered
  quickCheckGen do
    k <- chooseInt 1 9
    galoisCounit (multiples k) <$> genOrdered
  -- the induced closure on the lower side (here trivially identity) is lawful
  quickCheckGen do
    k <- chooseInt 1 9
    closureIdempotent (closureOf (multiples k)) <$> genOrdered
  -- the induced kernel rounds down to a multiple and is deflationary
  quickCheckGen do
    k <- chooseInt 1 9
    m <- genOrdered
    pure (leq (kernelOf (multiples k) m) m)

  log "-- Closure operator: transitive closure via fixpointFrom --"
  quickCheckGen $ closureExtensive transitiveClosure <$> genRel
  quickCheckGen $ lift2 (closureMonotone transitiveClosure) genRel genRel
  quickCheckGen $ closureIdempotent transitiveClosure <$> genRel
  quickCheckGen $ lift2 (monotone (close transitiveClosure)) genRel genRel
  -- bounded iteration agrees with the unbounded fixpoint
  quickCheckGen $
    (\r -> fixpointFromN 100 composeStep r == Just (close transitiveClosure r)) <$> genRel

  log "-- Deterministic spot checks --"
  let r = Set.fromFoldable [ Tuple 0 1, Tuple 1 2, Tuple 2 3 ]
  assertTrue (closedBy transitiveClosure (close transitiveClosure r))
  assertTrue (Set.member (Tuple 0 3) (close transitiveClosure r))
  -- Joined: the union-not-sum fold — shared contributions count once
  let s1 = Set.fromFoldable [ 1, 2 ]
  let s2 = Set.fromFoldable [ 2, 3 ]
  assertEqual
    { actual: unwrap (Joined s1 <> Joined s2 <> Joined s1)
    , expected: Set.fromFoldable [ 1, 2, 3 ]
    }
  assertEqual
    { actual: joins Set.empty [ s1, s2, s1 ]
    , expected: join s1 s2
    }
  log "All order-theory tests passed."
