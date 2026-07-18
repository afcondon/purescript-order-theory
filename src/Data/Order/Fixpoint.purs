-- | Fixpoint iteration: run a function until it stops changing its input.
-- |
-- | The Knaster–Tarski guarantee, informally: a MONOTONE function on a lattice
-- | with no infinite ascending chains, started from below its least fixed
-- | point, reaches that fixed point by iteration — "a pass that changes
-- | nothing is the fixpoint and one must come". This is the shape of every
-- | saturation loop (a JTMS engine's `go`), of transitive closure, of
-- | worklist dataflow analysis.
-- |
-- | The function itself cannot check monotonicity or chain finiteness; those
-- | are the caller's obligations (checkable via `Data.Order.Laws.monotone`).
-- | `fixpointFromN` bounds the iteration for callers who cannot promise a
-- | finite lattice.
module Data.Order.Fixpoint
  ( fixpointFrom
  , fixpointFromN
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Iterate `f` from `x0` until `f x == x`. Diverges if no fixed point is
-- | reachable — use only where the ascending-chain argument holds.
fixpointFrom :: forall a. Eq a => (a -> a) -> a -> a
fixpointFrom f = go
  where
  go x =
    let y = f x
    in if y == x then x else go y

-- | As `fixpointFrom`, but gives up (`Nothing`) after `n` steps.
fixpointFromN :: forall a. Eq a => Int -> (a -> a) -> a -> Maybe a
fixpointFromN n f = go n
  where
  go k x
    | k < 0 = Nothing
    | otherwise =
        let y = f x
        in if y == x then Just x else go (k - 1) y
