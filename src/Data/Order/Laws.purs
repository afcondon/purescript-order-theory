-- | The laws as ordinary Boolean predicates — no test-framework dependency.
-- | A consumer pairs these with its own generators (QuickCheck, enumeration,
-- | golden cases); the library's claim is only WHAT must hold, never how to
-- | sample it.
-- |
-- | One idiom to note: universally quantified implications over an order
-- | ("∀ x ≤ y, …") sample terribly — random pairs are rarely comparable. Every
-- | such law here instead MANUFACTURES a comparable pair from arbitrary input:
-- | `x ≤ x ∨ y` always holds, so monotonicity of `f` is tested as
-- | `f x ≤ f (x ∨ y)`. Full coverage from unconstrained generators.
module Data.Order.Laws
  ( joinAssociative
  , joinCommutative
  , joinIdempotent
  , meetAssociative
  , meetCommutative
  , meetIdempotent
  , absorption
  , ordersAgree
  , monotone
  , closureExtensive
  , closureMonotone
  , closureIdempotent
  , galoisAdjunction
  , galoisUnit
  , galoisCounit
  ) where

import Prelude hiding (join)

import Data.Order.Closure (ClosureOperator, close)
import Data.Order.Galois (GaloisConnection, lower, upper)
import Data.Order.Semilattice (class JoinSemilattice, class Lattice, class MeetSemilattice, join, leq, leqMeet, meet)

-- Semilattice laws ------------------------------------------------------------

joinAssociative :: forall a. JoinSemilattice a => Eq a => a -> a -> a -> Boolean
joinAssociative x y z = join x (join y z) == join (join x y) z

joinCommutative :: forall a. JoinSemilattice a => Eq a => a -> a -> Boolean
joinCommutative x y = join x y == join y x

-- | The law that separates a semilattice from a plain `Semigroup`, and the
-- | reason semilattice folds count shared contributions once.
joinIdempotent :: forall a. JoinSemilattice a => Eq a => a -> Boolean
joinIdempotent x = join x x == x

meetAssociative :: forall a. MeetSemilattice a => Eq a => a -> a -> a -> Boolean
meetAssociative x y z = meet x (meet y z) == meet (meet x y) z

meetCommutative :: forall a. MeetSemilattice a => Eq a => a -> a -> Boolean
meetCommutative x y = meet x y == meet y x

meetIdempotent :: forall a. MeetSemilattice a => Eq a => a -> Boolean
meetIdempotent x = meet x x == x

-- | Both absorption laws — the glue that makes join and meet present the SAME
-- | order.
absorption :: forall a. Lattice a => Eq a => a -> a -> Boolean
absorption x y = join x (meet x y) == x && meet x (join x y) == x

-- | The join-derived and meet-derived orders agree (a consequence of
-- | absorption; cheap to test directly).
ordersAgree :: forall a. Lattice a => Eq a => a -> a -> Boolean
ordersAgree x y = leq x y == leqMeet x y

-- Monotone maps ---------------------------------------------------------------

-- | `f` preserves order, tested on the manufactured comparable pair
-- | `(x, x ∨ y)`.
monotone
  :: forall a b
   . JoinSemilattice a
  => Eq a
  => JoinSemilattice b
  => Eq b
  => (a -> b)
  -> a
  -> a
  -> Boolean
monotone f x y = leq (f x) (f (join x y))

-- Closure-operator laws -------------------------------------------------------

-- | `x ≤ c x`: completing never loses anything. For rule saturation this is
-- | the no-retraction guarantee.
closureExtensive :: forall a. JoinSemilattice a => Eq a => ClosureOperator a -> a -> Boolean
closureExtensive c x = leq x (close c x)

-- | `x ≤ y ⇒ c x ≤ c y`, via the manufactured pair. For rule saturation this
-- | is the NEGATION-AS-FAILURE DETECTOR: a rule that concludes from the
-- | absence of a fact breaks exactly this law (a new axiom kills an old
-- | conclusion), so the property test convicts it automatically.
closureMonotone :: forall a. JoinSemilattice a => Eq a => ClosureOperator a -> a -> a -> Boolean
closureMonotone c x y = leq (close c x) (close c (join x y))

-- | `c (c x) == c x`: re-completing a completed value is a no-op — the
-- | cheap-`still?` guarantee.
closureIdempotent :: forall a. JoinSemilattice a => Eq a => ClosureOperator a -> a -> Boolean
closureIdempotent c x = close c (close c x) == close c x

-- Galois-connection laws ------------------------------------------------------

-- | The one biconditional: `lower a ≤ b ⟺ a ≤ upper b`. Everything else
-- | about the pair (monotonicity of both legs, the unit inequalities, the
-- | induced closure's laws) follows from this.
galoisAdjunction
  :: forall a b
   . JoinSemilattice a
  => Eq a
  => JoinSemilattice b
  => Eq b
  => GaloisConnection a b
  -> a
  -> b
  -> Boolean
galoisAdjunction gc a b = leq (lower gc a) b == leq a (upper gc b)

-- | `a ≤ upper (lower a)` — a free theorem of the adjunction, exposed
-- | separately as a sharper diagnostic when the biconditional fails.
galoisUnit
  :: forall a b
   . JoinSemilattice a
  => Eq a
  => GaloisConnection a b
  -> a
  -> Boolean
galoisUnit gc a = leq a (upper gc (lower gc a))

-- | `lower (upper b) ≤ b` — the dual free theorem.
galoisCounit
  :: forall a b
   . JoinSemilattice b
  => Eq b
  => GaloisConnection a b
  -> b
  -> Boolean
galoisCounit gc b = leq (lower gc (upper gc b)) b
