-- | Galois connections: a pair of monotone maps in opposite directions,
-- | locked together by one biconditional (over the derived orders of
-- | `Data.Order.Semilattice`):
-- |
-- | ```
-- | lower a ≤ b   ⟺   a ≤ upper b
-- | ```
-- |
-- | The law pins each side as the BEST approximation compatible with the
-- | other: `floor` is the upper adjoint of the Int→Number inclusion, a
-- | snap-down quantiser is the upper adjoint of a pitch-set's inclusion into
-- | all pitches, abstraction in static analysis is an upper adjoint of
-- | concretization. Monotonicity of both maps and the two unit inequalities
-- | (`a ≤ upper (lower a)`, `lower (upper b) ≤ b`) are consequences, not
-- | extra axioms — see `Data.Order.Laws`.
-- |
-- | Composing the two legs yields a closure operator on the lower side
-- | (`closureOf`) and an interior (kernel) operator on the upper side
-- | (`kernelOf`): every Galois connection manufactures a closure, and every
-- | closure arises this way.
module Data.Order.Galois
  ( GaloisConnection(..)
  , lower
  , upper
  , composeGC
  , closureOf
  , kernelOf
  ) where

import Prelude

import Data.Newtype (class Newtype)
import Data.Order.Closure (ClosureOperator(..))

-- | `lower : a → b` and `upper : b → a` with `lower x ≤ y ⟺ x ≤ upper y`.
-- | (`lower` is also called the left adjoint, `upper` the right.)
newtype GaloisConnection a b = GaloisConnection
  { lower :: a -> b
  , upper :: b -> a
  }

derive instance Newtype (GaloisConnection a b) _

lower :: forall a b. GaloisConnection a b -> a -> b
lower (GaloisConnection gc) = gc.lower

upper :: forall a b. GaloisConnection a b -> b -> a
upper (GaloisConnection gc) = gc.upper

-- | Adjoints compose: the composite's lower is the composite of lowers, and
-- | the adjunction law for the composite is inherited — chains of lawful
-- | connections need no re-verification.
composeGC :: forall a b c. GaloisConnection b c -> GaloisConnection a b -> GaloisConnection a c
composeGC (GaloisConnection g) (GaloisConnection f) = GaloisConnection
  { lower: g.lower <<< f.lower
  , upper: f.upper <<< g.upper
  }

-- | `upper <<< lower` — the closure operator every connection induces on its
-- | lower side ("round-trip through the other world and come back bigger").
closureOf :: forall a b. GaloisConnection a b -> ClosureOperator a
closureOf (GaloisConnection gc) = ClosureOperator (gc.upper <<< gc.lower)

-- | `lower <<< upper` — the interior operator on the upper side: deflationary,
-- | monotone, idempotent (a closure operator in the dual order).
kernelOf :: forall a b. GaloisConnection a b -> b -> b
kernelOf (GaloisConnection gc) = gc.lower <<< gc.upper
