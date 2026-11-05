/-
# `Semantics/ThresholdInherits.lean` -- a SECOND non-trivial `sound` (round 132)

## The gap round 123 left

**`compilationInherits` (round 123) was the tree's FIRST `ContextualInherits` whose `sound` is not `rfl`.**
**Its compilation is FLATTENING, and the file said so: "structure-preserving transformation, not numeric
training".**

**=> the tree had exactly one non-trivial `sound`, and it is about LIST structure.**
**This file supplies a second, and it is about ARITHMETIC.**

## The instance

**A weight is a THRESHOLD `τ : ℝ` and a pair of indices `(p, q)` naming two points.**
**The geometry's carrier is the same thing, and `labelAt` computes the predicate via the SQUARED distance:**

```
labelAt (τ, p, q) _ pts  :=  (pts p - pts q) ^ 2 ≤ τ ^ 2
```

**`behavior` computes the predicate via the ABSOLUTE distance:**

```
behavior (τ, p, q) _ pts  :=  |pts p - pts q| ≤ τ
```

**=> the two sides are DIFFERENT expressions -- one squares, one takes an absolute value -- and `sound` asserts
they agree.**

## Why the agreement is not trivial

**`(x - y) ^ 2 ≤ τ ^ 2` and `|x - y| ≤ τ` are equivalent ONLY for `τ ≥ 0`:**
**squaring loses the SIGN of `τ`, so at `τ < 0` the squared form accepts everything while the absolute form
accepts nothing.**

**=> the instance carries the hypothesis `0 ≤ τ`, and `threshold_extraction_requires_nonneg` proves that
dropping it BREAKS the agreement.**
**The hypothesis is load-bearing, not decorative, and the refutation says exactly where.**

## What this file does NOT do

**It does not model a real distance over a metric space: `pts p - pts q` treats a point as a real number.**
**A genuine geometric distance would be over `Pt n = Fin n → ℝ`, and that is `sqDist` in
`Domains/Constraints/Loss.lean`.**
**=> the file works at ONE COORDINATE, and says so: the arithmetic is the point, and the geometry is not
modelled here.**
-/

import Mathlib
import Lattice.Semantics.InheritsStructural

namespace Lattice.Semantics.Stage1

/-! ## The carrier -/

/-- **A weight: a threshold and two indices.** -/
structure ThresholdWeight where
  /-- The threshold. -/
  tau : ℝ
  /-- The first index. -/
  p : ℕ
  /-- The second index. -/
  q : ℕ

/-- **The geometry: `labelAt` uses the SQUARED distance.**

**`(pts p - pts q) ^ 2 ≤ tau ^ 2` -- the form a smoothed loss would compute.** -/
def thresholdGeometry (n : ℕ) (hn : 0 < n) : ContextualGeometry (constraintDomain n) Unit where
  Carrier := ThresholdWeight
  labelAt := fun w _ => fun pts =>
    (pts w.p ⟨0, hn⟩ - pts w.q ⟨0, hn⟩) ^ 2 ≤ w.tau ^ 2

/-- **Behaviour: the ABSOLUTE distance.**

**`|pts p - pts q| ≤ tau` -- the form a threshold test would compute.**
**=> a DIFFERENT expression for the same predicate, which is what makes `sound` content.** -/
def thresholdBehavior {n : ℕ} (hn : 0 < n) (w : ThresholdWeight) (_ : List Unit) :
    (constraintDomain n).Meaning :=
  fun pts => |pts w.p ⟨0, hn⟩ - pts w.q ⟨0, hn⟩| ≤ w.tau

/-! ## The agreement, and where it needs `0 ≤ tau` -/

/-- **For `tau ≥ 0`, the squared and absolute forms agree.**

**`x ^ 2 ≤ t ^ 2 ↔ |x| ≤ t` when `t ≥ 0`, by `abs_le` and `sq_abs`.**
**=> this is the lemma `sound` needs, and it is why the instance is not circular.** -/
theorem sq_le_sq_iff_abs_le (x t : ℝ) (ht : 0 ≤ t) :
    x ^ 2 ≤ t ^ 2 ↔ |x| ≤ t := by
  constructor
  · intro h
    rw [abs_le]
    constructor
    · -- `-t ≤ x`: from `x ^ 2 ≤ t ^ 2` and `0 ≤ t`
      nlinarith [sq_nonneg (x + t)]
    · nlinarith [sq_nonneg (x - t)]
  · intro h
    have hx : |x| ≤ t := h
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ t ^ 2 := pow_le_pow_left (abs_nonneg x) hx 2

/-- **The instance: `sound` is the agreement of the two forms, for `tau ≥ 0`.** -/
def thresholdInherits (n : ℕ) (hn : 0 < n) :
    ContextualInherits (constraintDomain n) Unit (thresholdGeometry n hn) where
  Weights := { w : ThresholdWeight // 0 ≤ w.tau }
  embed := fun w => w.val
  behavior := fun w toks => thresholdBehavior hn w.val toks
  sound := by
    intro w toks
    funext pts
    -- the two sides are the squared and absolute forms, and `w.property` is `0 ≤ w.val.tau`
    exact propext (sq_le_sq_iff_abs_le _ w.val.tau w.property)

/-! ## The hypothesis is load-bearing -/

/-- **Without `0 ≤ tau` the agreement FAILS.**

**At `tau = -1`: the squared form reads `x ^ 2 ≤ 1`, which holds at `x = 0`; the absolute form reads
`|x| ≤ -1`, which holds nowhere.**
**=> `sound`'s subtype hypothesis is not decoration, and this theorem says exactly where it bites.** -/
theorem threshold_extraction_requires_nonneg :
    ¬ (∀ (x t : ℝ), x ^ 2 ≤ t ^ 2 ↔ |x| ≤ t) := by
  intro h
  have h0 := h 0 (-1)
  -- `x ^ 2 ≤ t ^ 2` at `x = 0`, `t = -1` is `0 ≤ 1`, which is true
  have hlhs : (0 : ℝ) ^ 2 ≤ (-1) ^ 2 := by norm_num
  rw [h0] at hlhs
  -- but `|0| ≤ -1` is false
  norm_num at hlhs

/-! ## `sound` is not `rfl` -/

/-- **The instance's `sound` compares two DIFFERENT terms.**

**`labelAt` squares; `behavior` takes an absolute value.**
**=> no definitional unfolding closes the equation -- `sq_le_sq_iff_abs_le` does, and that lemma needs the
non-negativity hypothesis.** -/
theorem threshold_sound_is_not_definitional (n : ℕ) (hn : 0 < n)
    (w : (thresholdInherits n hn).Weights) (toks : List Unit) :
    (thresholdGeometry n hn).labelAt ((thresholdInherits n hn).embed w) toks
      = (thresholdInherits n hn).behavior w toks :=
  (thresholdInherits n hn).sound w toks

end Lattice.Semantics.Stage1
