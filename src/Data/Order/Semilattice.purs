-- | Semilattices: partial orders presented by their merge operation.
-- |
-- | The design principle of this library is that the ORDER IS DERIVED, never
-- | axiomatized separately. A `JoinSemilattice` is a `Semigroup` with two extra
-- | laws (commutativity and idempotence), and those laws are exactly what make
-- |
-- | ```purescript
-- | leq x y = (x `join` y) == y
-- | ```
-- |
-- | a partial order: "x ≤ y" MEANS "merging x into y changes nothing". Set
-- | inclusion is `union x y == y`; numeric order is `max x y == y`. One class,
-- | three laws, and `leq` is a consequence rather than a second axiomatization
-- | kept consistent by hand.
-- |
-- | Idempotence is the load-bearing law that separates this from `Semigroup`:
-- | it is why a semilattice fold counts a shared contribution ONCE however many
-- | paths deliver it (union-not-sum), and why CRDT-style merge tolerates
-- | duplicated delivery.
-- |
-- | The Prelude's `HeytingAlgebra` is the special case of a bounded distributive
-- | lattice aimed at logic-valued types; these classes are the general subject.
module Data.Order.Semilattice
  ( class JoinSemilattice
  , join
  , class MeetSemilattice
  , meet
  , class Lattice
  , leq
  , geq
  , leqMeet
  , joins
  , meets
  , Ordered(..)
  , Dual(..)
  , Joined(..)
  ) where

import Prelude hiding (join)

import Data.Foldable (class Foldable, foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))

-- | Least upper bound. Laws (beyond `Semigroup`-style associativity):
-- |
-- | * associative: `join x (join y z) == join (join x y) z`
-- | * commutative: `join x y == join y x`
-- | * idempotent: `join x x == x`
class JoinSemilattice a where
  join :: a -> a -> a

-- | Greatest lower bound. Same three laws, dually read.
class MeetSemilattice a where
  meet :: a -> a -> a

-- | Both structures, tied together by the absorption laws:
-- |
-- | * `join x (meet x y) == x`
-- | * `meet x (join x y) == x`
-- |
-- | Absorption is what guarantees `leq` and `leqMeet` agree.
class (JoinSemilattice a, MeetSemilattice a) <= Lattice a

infixr 5 join as \/
infixr 6 meet as /\

-- | The derived partial order: `x ≤ y` iff merging x into y changes nothing.
leq :: forall a. JoinSemilattice a => Eq a => a -> a -> Boolean
leq x y = join x y == y

geq :: forall a. JoinSemilattice a => Eq a => a -> a -> Boolean
geq x y = leq y x

-- | The order as presented by `meet`: `x ≤ y` iff x survives restriction to y.
-- | In a `Lattice` this agrees with `leq` (by absorption); tested, not assumed.
leqMeet :: forall a. MeetSemilattice a => Eq a => a -> a -> Boolean
leqMeet x y = meet x y == x

-- | Fold a non-empty-ish collection by `join`, from a starting element. The
-- | seed is absorbed if it is below everything else (idempotence at work), so
-- | `joins bottom xs` is the honest supremum when a least element exists.
joins :: forall f a. Foldable f => JoinSemilattice a => a -> f a -> a
joins = foldl join

meets :: forall f a. Foldable f => MeetSemilattice a => a -> f a -> a
meets = foldl meet

-- Instances -------------------------------------------------------------------

-- | Truth values: `join` is disjunction, `meet` conjunction; `leq` is
-- | implication read backwards (`false ≤ true`).
instance JoinSemilattice Boolean where
  join = (||)

instance MeetSemilattice Boolean where
  meet = (&&)

instance Lattice Boolean

instance JoinSemilattice Unit where
  join _ _ = unit

instance MeetSemilattice Unit where
  meet _ _ = unit

instance Lattice Unit

-- | Sets under union/intersection; the derived order is inclusion.
instance Ord a => JoinSemilattice (Set a) where
  join = Set.union

instance Ord a => MeetSemilattice (Set a) where
  meet = Set.intersection

instance Ord a => Lattice (Set a)

-- | Maps merge pointwise, joining values on collision. The derived order:
-- | `m1 ≤ m2` iff every key of m1 is present in m2 with a value at least as
-- | large. (No `Meet` instance: pointwise meet on the key intersection is
-- | lawful, but its absorption against this join fails for maps with
-- | disjoint keys — a lattice needs matching carriers.)
instance (Ord k, JoinSemilattice v) => JoinSemilattice (Map k v) where
  join = Map.unionWith join

-- | `Maybe` adjoins a bottom element: `Nothing` is the identity of `join`.
instance JoinSemilattice a => JoinSemilattice (Maybe a) where
  join = case _, _ of
    Nothing, y -> y
    x, Nothing -> x
    Just x, Just y -> Just (join x y)

-- | Products order componentwise.
instance (JoinSemilattice a, JoinSemilattice b) => JoinSemilattice (Tuple a b) where
  join (Tuple x1 y1) (Tuple x2 y2) = Tuple (join x1 x2) (join y1 y2)

instance (MeetSemilattice a, MeetSemilattice b) => MeetSemilattice (Tuple a b) where
  meet (Tuple x1 y1) (Tuple x2 y2) = Tuple (meet x1 x2) (meet y1 y2)

instance (Lattice a, Lattice b) => Lattice (Tuple a b)

-- | A total order read as a lattice: `join` is `max`, `meet` is `min`. Wraps
-- | rather than instancing `Int`/`Number` directly, because "which lattice?"
-- | is a choice for totally ordered types (divisibility orders `Int` too).
newtype Ordered a = Ordered a

derive instance Newtype (Ordered a) _
derive newtype instance Eq a => Eq (Ordered a)
derive newtype instance Ord a => Ord (Ordered a)
derive newtype instance Show a => Show (Ordered a)

instance Ord a => JoinSemilattice (Ordered a) where
  join (Ordered x) (Ordered y) = Ordered (max x y)

instance Ord a => MeetSemilattice (Ordered a) where
  meet (Ordered x) (Ordered y) = Ordered (min x y)

instance Ord a => Lattice (Ordered a)

-- | The opposite order: swaps `join` and `meet`. Dualizing is how one theory
-- | of closure operators also covers interior (kernel) operators.
newtype Dual a = Dual a

derive instance Newtype (Dual a) _
derive newtype instance Eq a => Eq (Dual a)
derive newtype instance Show a => Show (Dual a)

instance MeetSemilattice a => JoinSemilattice (Dual a) where
  join (Dual x) (Dual y) = Dual (meet x y)

instance JoinSemilattice a => MeetSemilattice (Dual a) where
  meet (Dual x) (Dual y) = Dual (join x y)

instance Lattice a => Lattice (Dual a)

-- | A semilattice read as a `Semigroup`, for `foldMap`-style accumulation
-- | (the union-not-sum fold: shared contributions count once).
newtype Joined a = Joined a

derive instance Newtype (Joined a) _
derive newtype instance Eq a => Eq (Joined a)
derive newtype instance Show a => Show (Joined a)

instance JoinSemilattice a => Semigroup (Joined a) where
  append (Joined x) (Joined y) = Joined (join x y)
