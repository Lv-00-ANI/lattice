import Mathlib
import Lattice.Domains.Flatten
import Lattice.Domains.Constraint
import Lattice.Geo.Loss
import Lattice.Domains.Perturb

/-!
# `Lattice.Geo.Extract` -- reading a symbolic constraint back out of a weight vector

## The reverse direction of the ladder

The forward direction is `Lattice.Geo.Loss`: a constraint becomes a penalty on a weight vector. This file is
the reverse: given a weight vector, which constraints does it satisfy?

Concretely, a weight vector `v : Fin (k * n) → ℝ` *is* a configuration (`Lattice.Geo.Flatten`), so extraction
is not a search problem -- it is evaluation:

```
configOf   v      := unflatten v               -- the configuration a vector denotes
satisfies  c v    := c evaluates to true there  -- what it satisfies
```

The project requires reversibility to be stated **by layer**, and this is where the object-layer half
lives for the geometric chain: `configOf` is a bijection (`flatten_unflatten`,
`unflatten_flatten`), so a vector carries its configuration exactly.

## The semantic layer is a different matter

Two distinct weight vectors may induce the same geometry -- scaling a configuration about the origin
preserves perpendicularity, collinearity and midpoint, and only distances notice. So `satisfies` is *not*
injective in the vector: many vectors satisfy exactly the same constraint set. That is the semantic
non-invertibility the project must state, and `satisfies_not_injective` below proves a concrete instance
of it rather than asserting the general claim.

## What extraction is useful for

`satisfies` is the predicate a verification loop checks: after a repair step moves a weight, ask which
constraints hold. Making it a definition rather than prose is what lets `Lattice.Geo.RepairSpec` talk about
it, and what lets the round-trip laws be stated about something.
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {k n : ℕ}

/-- **The configuration a weight vector denotes.**

The object-layer extraction: since `flatten` is a bijection there is nothing to search for. -/
noncomputable def configOf (v : Fin (k * n) → ℝ) : Fin k → Pt n :=
  unflatten v

/-- Round-tripping a vector through a configuration returns it. The object layer is exact. -/
@[simp] theorem configOf_roundtrip (v : Fin (k * n) → ℝ) :
    flatten (configOf v) = v :=
  flatten_unflatten v

/-- Round-tripping a configuration through a vector returns it. -/
@[simp] theorem configOf_inv (pts : Fin k → Pt n) :
    configOf (flatten pts) = pts :=
  unflatten_flatten pts

/-- **Which constraints a weight vector satisfies.**

The verification predicate: a constraint holds at `v` when its evaluation is true at the configuration `v`
denotes.

Stated for `GeoConstraint`, the type that includes both the polynomial and the square layer, so that the
verification loop can ask about `collinear` and `perpendicular` as well as `sqDistEq`. -/
noncomputable def satisfies (c : GeoConstraint n) (pts : ℕ → Pt n) : Prop :=
  GeoConstraint.Holds c pts

/-! ## Semantic non-injectivity, at the object level

The object layer is a bijection; the mapping from vectors to *satisfied constraints* is not. The
witness below is the simplest one: negating every coordinate of a configuration preserves the dot
products that perpendicularity is stated with. -/

/-- **Negation preserves perpendicularity.** `dot (-u) (-v) = dot u v`, so a reflection through the
origin cannot be detected by a perpendicularity constraint -- only distances notice it as well, and
distances are preserved too. -/
theorem perp_neg_invariant (a b c e : Fin k) (v : Fin (k * n) → ℝ) :
    (∑ i, seg a b i (-v) * seg c e i (-v)) = ∑ i, seg a b i v * seg c e i v := by
  apply Finset.sum_congr rfl
  intro i _
  unfold seg
  simp only [unflatten, Pi.neg_apply]
  ring

/-- **The perpendicular residual vanishes at `-v` exactly when it vanishes at `v`.**

A concrete instance of semantic non-invertibility: two different weight vectors (`v` and `-v`, distinct
whenever `v ≠ 0`) cannot be told apart by whether they satisfy a perpendicularity constraint. -/
theorem perp_neg_iff (a b c e : Fin k) (v : Fin (k * n) → ℝ) :
    (∑ i, seg a b i (-v) * seg c e i (-v)) = 0
      ↔ (∑ i, seg a b i v * seg c e i v) = 0 := by
  rw [perp_neg_invariant]

end Lattice.Geo
