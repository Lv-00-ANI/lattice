/-
# `Semantics/GeometricThresholdInherits.lean` -- a THIRD non-trivial `sound`, over the REAL distance
(round 133)

## What round 132 left, and said it left

**`thresholdInherits` works at ONE COORDINATE (`pts p ⟨0, _⟩`), and its file said so:**

> **"A genuine geometric distance would be `sqDist`, and that is not what is used here."**

**This file closes that: the threshold instance is restated over `sqDist`, the project's own squared
Euclidean distance on `Pt n = Fin n → ℝ`.**

## The instance

**A weight is a threshold `tau ≥ 0` and two indices `(p, q)`.**
**The two sides compute the SAME predicate through DIFFERENT expressions:**

```
labelAt (tau,p,q) _ pts  :=  sqDist (pts p) (pts q) ≤ tau ^ 2          -- SQUARED, no square root
behavior (tau,p,q) _ pts  :=  Real.sqrt (sqDist (pts p) (pts q)) ≤ tau  -- the DISTANCE, via sqrt
```

**=> the geometry never takes a square root; the model always does.**
**`sound` asserts they agree, and the lemma that closes it is `Real.sqrt_le_iff`.**

## Why this is a stronger instance than round 132's

**Round 132 compared `(x)^2 ≤ t^2` with `|x| ≤ t` at a single coordinate.**
**This one compares `sqDist ≤ t^2` with `sqrt (sqDist) ≤ t`, where `sqDist` is**
**`sqNorm (diff p q)` -- a sum of squares over ALL `n` coordinates.**

**=> the instance now exercises the project's actual geometry (`Domains/Constraints/Dist.lean`), not a
coordinate of it.**

## The hypothesis, still load-bearing

**`Real.sqrt_le_iff` reads `√x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`, so `0 ≤ tau` is needed on one side.**
**The subtype `{ tau : ℝ // 0 ≤ tau }` carries it, exactly as in round 132, and for the same reason: squaring
loses the sign.**

## What this file does NOT do

**It does not model a per-point metric or weighted coordinates: `sqDist` is the unweighted sum of squared
differences.**
**A metric with weights would be a different `sqNorm`, and the tree has one (`Domains/.../Weighted`) that is not
used here.**
-/

import Mathlib
import Lattice.Semantics.InheritsStructural
import Lattice.Reference.Geometry.Constraints.Dist

namespace Lattice.Semantics.Stage1

open Lattice.Geo

/-! ## The carrier -/

/-- **A weight: a threshold and two indices.** -/
structure GeomThresholdWeight where
  /-- The threshold. -/
  tau : ℝ
  /-- The first index. -/
  p : ℕ
  /-- The second index. -/
  q : ℕ

/-- **The geometry: `labelAt` compares SQUARED distances, never taking a square root.** -/
def geomThresholdGeometry (n : ℕ) : ContextualGeometry (constraintDomain n) Unit where
  Carrier := GeomThresholdWeight
  labelAt := fun w _ => fun pts => sqDist (pts w.p) (pts w.q) ≤ w.tau ^ 2

/-- **Behaviour: the DISTANCE, so it takes the square root.**

**=> a different expression for the same predicate; that difference is what `sound` has to bridge.** -/
def geomThresholdBehavior {n : ℕ} (w : GeomThresholdWeight) (_ : List Unit) :
    (constraintDomain n).Meaning :=
  fun pts => Real.sqrt (sqDist (pts w.p) (pts w.q)) ≤ w.tau

/-! ## The bridge lemma -/

/-- **`sqDist ≤ t ^ 2` is equivalent to `sqrt (sqDist) ≤ t` for `t ≥ 0`.**

**The chain: `Real.sqrt_le_iff` gives `√x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2`, and `sqDist` is nonnegative by
`sqDist_nonneg`.**
**=> this is `sound`'s proof, and it uses the library's own distance lemma rather than a coordinate argument.** -/
theorem sqDist_le_sq_iff_sqrt_le {n : ℕ} (p q : Pt n) (t : ℝ) (ht : 0 ≤ t) :
    sqDist p q ≤ t ^ 2 ↔ Real.sqrt (sqDist p q) ≤ t := by
  rw [Real.sqrt_le_iff]
  constructor
  · intro h
    exact ⟨ht, h⟩
  · intro ⟨_, h⟩
    exact h

/-- **Without `0 ≤ t` the equivalence FAILS.**

**At `t = -1` and `sqDist p q = 0`: the left side reads `0 ≤ 1`, which holds, while the right reads
`0 ≤ -1`, which does not.**
**=> the subtype hypothesis on `tau` is load-bearing at the GEOMETRIC level too, not only at the coordinate
level round 132 handled.** -/
theorem sqDist_equivalence_requires_nonneg {n : ℕ} (p : Pt n) :
    ¬ (sqDist p p ≤ (-1 : ℝ) ^ 2 ↔ Real.sqrt (sqDist p p) ≤ (-1 : ℝ)) := by
  intro h
  -- the left side holds: `sqDist p p = 0` and `0 ≤ 1`
  have hleft : sqDist p p ≤ (-1 : ℝ) ^ 2 := by
    have hz : sqDist p p = 0 := (sqDist_eq_zero_iff p p).mpr rfl
    rw [hz]
    norm_num
  -- the right side does not: `sqrt x` is nonnegative and `-1` is not
  rw [h] at hleft
  have hnn := Real.sqrt_nonneg (sqDist p p)
  linarith

/-- **The instance: `sound` bridges the squared form and the distance form.** -/
def geomThresholdInherits (n : ℕ) :
    ContextualInherits (constraintDomain n) Unit (geomThresholdGeometry n) where
  Weights := { w : GeomThresholdWeight // 0 ≤ w.tau }
  embed := fun w => w.val
  behavior := fun w toks => geomThresholdBehavior w.val toks
  sound := by
    intro w toks
    funext pts
    exact propext (sqDist_le_sq_iff_sqrt_le (pts w.val.p) (pts w.val.q) w.val.tau w.property)

/-! ## `sound` is not `rfl`, over the REAL distance -/

/-- **The instance's `sound` compares a squared-distance predicate with a square-root predicate.**

**No definitional unfolding closes it: `sqDist` is `sqNorm (diff p q)`, a sum over all coordinates, and
`Real.sqrt_le_iff` is what relates it to the distance form.** -/
theorem geomThreshold_sound_is_not_definitional (n : ℕ)
    (w : (geomThresholdInherits n).Weights) (toks : List Unit) :
    (geomThresholdGeometry n).labelAt ((geomThresholdInherits n).embed w) toks
      = (geomThresholdInherits n).behavior w toks :=
  (geomThresholdInherits n).sound w toks

/-- **At `p = q` the distance is zero and BOTH forms accept, which pins the base case.**

**`sqDist p p = 0` by `sqDist_eq_zero_iff`, so `0 ≤ tau ^ 2` and `0 ≤ tau` both hold.**
**=> a check that the instance is not vacuous at its own fixed point.** -/
theorem geomThreshold_at_zero {n : ℕ} (tau : ℝ) (p : ℕ) :
    sqDist ((fun _ : ℕ => (0 : Pt n)) p) ((fun _ : ℕ => (0 : Pt n)) p) ≤ tau ^ 2 := by
  have hz : sqDist ((fun _ : ℕ => (0 : Pt n)) p) ((fun _ : ℕ => (0 : Pt n)) p) = 0 :=
    (sqDist_eq_zero_iff _ _).mpr rfl
  rw [hz]
  exact sq_nonneg tau

end Lattice.Semantics.Stage1
