# purescript-order-theory

Order theory as a first-class PureScript library: semilattices with the
partial order **derived from the merge operation**, closure operators and
Galois connections as values, and their laws as plain Boolean predicates.

```purescript
class JoinSemilattice a where
  join :: a -> a -> a          -- associative, commutative, IDEMPOTENT

leq :: forall a. JoinSemilattice a => Eq a => a -> a -> Boolean
leq x y = join x y == y        -- "x ≤ y" MEANS "merging x into y changes nothing"
```

## Modules

- **`Data.Order.Semilattice`** — `JoinSemilattice` / `MeetSemilattice` /
  `Lattice`, the derived order (`leq`), instances (`Boolean`, `Set`, `Map`,
  `Maybe`, `Tuple`, `Ordered` for max/min, `Dual` for the opposite order),
  and `Joined` — a semilattice read as a `Semigroup` for union-not-sum folds.
- **`Data.Order.Closure`** — `ClosureOperator`: extensive, monotone,
  idempotent. Transitive closure, dependency resolution, rule saturation.
- **`Data.Order.Galois`** — `GaloisConnection`: `lower a ≤ b ⟺ a ≤ upper b`.
  Floor/ceiling, quantisers, abstraction/concretization. Connections compose
  (`composeGC`); every connection induces a closure (`closureOf`) and an
  interior operator (`kernelOf`).
- **`Data.Order.Laws`** — every law as an ordinary predicate, **no
  test-framework dependency**: pair them with your own generators.
  Implication-shaped laws manufacture their comparable pair (`f x ≤ f (x ∨ y)`)
  so unconstrained generators give full coverage.
- **`Data.Order.Fixpoint`** — `fixpointFrom`: iterate to the least fixed
  point (Knaster–Tarski, informally: monotone + no infinite ascending chains
  ⇒ "a pass that changes nothing is the fixpoint and one must come").

## Why laws-as-predicates

The laws are bug detectors with specific names. For a rule-saturation engine
modelled as a `ClosureOperator` over sets of claims:

- `closureExtensive` — the no-retraction guarantee;
- `closureIdempotent` — re-saturating is a no-op (cheap staleness checks);
- `closureMonotone` — **an automatic negation-as-failure detector**: a rule
  that concludes from the *absence* of a fact fails exactly this law.

For a quantiser: one `galoisAdjunction` check implies snap-down/snap-up are
the best approximations, members are fixed points, and outputs are members —
free theorems instead of hand-maintained companion laws.

## Provenance

Class granularity mirrors Haskell's
[`lattices`](https://hackage.haskell.org/package/lattices)
(`Algebra.Lattice` / `Algebra.PartialOrd`); the closure/Galois half with
executable laws has no packaged precedent there — it is distilled from this
ecosystem's own artifacts (a JTMS saturation engine, a eurorack pitch
quantiser). Both are consumers.

## Tests

```bash
spago test
```

Law coverage for every shipped instance, plus two worked examples: the
multiples connection `(_ * k) ⊣ (_ \`div\` k)` on `Ordered Int`, and
transitive closure built with `fixpointFrom` and verified as a lawful
`ClosureOperator`.
