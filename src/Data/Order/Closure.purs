-- | Closure operators: functions that "complete" a value, characterized by
-- | three laws over the derived order (see `Data.Order.Laws`):
-- |
-- | * extensive: `x ≤ close c x` — completing never loses anything
-- | * monotone: `x ≤ y ⇒ close c x ≤ close c y` — more input, more output
-- | * idempotent: `close c (close c x) == close c x` — complete is complete
-- |
-- | Transitive closure, dependency resolution, convex hulls, and rule
-- | saturation (a JTMS's `saturate`) are all values of this type. Values with
-- | `close c x == x` are the CLOSED elements — the saturated knowledge bases,
-- | the convex shapes.
-- |
-- | The newtype carries no proof; the laws are checked by property tests
-- | (`Data.Order.Laws.closureExtensive` etc.), which is the point — a claimed
-- | closure operator that fails monotonicity is a bug detector firing (for
-- | saturation it is precisely a negation-as-failure detector).
module Data.Order.Closure
  ( ClosureOperator(..)
  , close
  , closedBy
  ) where

import Prelude

import Data.Newtype (class Newtype)

newtype ClosureOperator a = ClosureOperator (a -> a)

derive instance Newtype (ClosureOperator a) _

close :: forall a. ClosureOperator a -> a -> a
close (ClosureOperator f) = f

-- | Is `x` a fixed point of the operator — already complete?
closedBy :: forall a. Eq a => ClosureOperator a -> a -> Boolean
closedBy c x = close c x == x
