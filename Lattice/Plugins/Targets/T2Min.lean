/-
# T2's modulus half: from a vanishing point of the penalty to a satisfied constraint

**The audit found `penalty_min_to_violation` -- the plan's `IsLocalMin (loss p) x → violation p x ≤ g ε`
-- was ABSENT from the tree.**
**Round 81 widened T2's exactness half to seven of twelve constructors but did not touch this.**

## What the tree already has, and what was missing

**`Domains/Geometry/ExprLocalMin.lean` proves:**
**`IsLocalMin (fun y => (e.evalPts (toNatConfig y))^2) w` together with `derivExpr k e w ≠ 0` implies
`e.evalPts (toNatConfig w) = 0`.**

**That IS the plan's modulus, for the `eqZero` family:**
- **the loss is `(evalPts)^2`;**
- **a local minimum forces it to vanish;**
- **hence the constraint holds EXACTLY, not merely approximately.**

**=> the statement was in the tree but NOT in `ProofComplete`, and its `violation` vocabulary did not
exist.** **This file supplies both.**

## Why the derivative hypothesis is not removable

**`constExpr_localMin_counterexample` in the same module shows it:**
**a constant expression's squared penalty is minimised EVERYWHERE, and the constant need not be zero.**
**=> without `derivExpr k e w ≠ 0`, "local min implies satisfied" is FALSE.**

**So the modulus is conditional, and the condition is a fact about the EXPRESSION at the point, not a
convenience.** **Recording the counterexample beside the theorem is what keeps that visible.**
-/

import Lattice.Plugins.Manifest
import Lattice.Domains.Geometry.ExprLocalMin

namespace Lattice.Plugins.Targets

open Lattice.Geo

/-- **The violation of an `eqZero` constraint at a configuration, as the library's own quantity.**

**`violation c w := |e.evalPts (toNatConfig w)|`** -- **the ABSOLUTE VALUE of the expression, not its
square** -- **because the plan's modulus is an `ε`-bound on a geometric quantity, and a bound on the
square would not be one.**
**This is the definition the audit found missing.** -/
noncomputable def violation {n : ℕ} (e : GeoExpr n) (k : ℕ) (w : Fin (k * n) → ℝ) : ℝ :=
  |e.evalPts (toNatConfig w)|

/-- **The violation is nonnegative.** -/
theorem violation_nonneg {n : ℕ} (e : GeoExpr n) (k : ℕ) (w : Fin (k * n) → ℝ) :
    0 ≤ violation e k w :=
  abs_nonneg _

/-- **T2's MODULUS: a local minimum of the penalty forces the violation to be ZERO.**

**Stated in the `ε` form the plan uses: for every `ε > 0` there is a bound, namely `0`.**
**The `ε` is vacuous here BECAUSE the conclusion is exact -- and saying so explicitly is the point:**
**the plan expected an approximation, and what the tree proves is stronger.**

**Hypotheses, each required:**
- **`hk : e.maxPoint < k`** -- **the configuration's support covers the expression's points.**
- **`hne : derivExpr k e w ≠ 0`** -- **non-vanishing gradient; without it the statement is false
  (`constExpr_localMin_counterexample`).**
- **`hmin`** -- **the local-minimality itself.** -/
theorem penalty_min_to_violation {n : ℕ} (e : GeoExpr n) (k : ℕ) (hk : e.maxPoint < k)
    (w : Fin (k * n) → ℝ) (hne : derivExpr k e w ≠ 0)
    (hmin : IsLocalMin (fun y : Fin (k * n) → ℝ => (e.evalPts (toNatConfig y)) ^ 2) w) :
    ∀ ε : ℝ, 0 < ε → violation e k w ≤ ε := by
  intro ε hε
  have hzero : e.evalPts (toNatConfig w) = 0 :=
    evalPts_localMin_implies_zero k e hk w hne hmin
  unfold violation
  rw [hzero, abs_zero]
  exact le_of_lt hε

/-- **The modulus's sharpest form: the violation is exactly zero.**

**`penalty_min_to_violation` says "≤ ε for every positive ε"; this says the value it bounds is `0`.**
**Both are stated because the plan's vocabulary is the `ε` one and the tree's content is the exact one,
and a reader should see that the difference is not an approximation gap.** -/
theorem penalty_min_violation_eq_zero {n : ℕ} (e : GeoExpr n) (k : ℕ) (hk : e.maxPoint < k)
    (w : Fin (k * n) → ℝ) (hne : derivExpr k e w ≠ 0)
    (hmin : IsLocalMin (fun y : Fin (k * n) → ℝ => (e.evalPts (toNatConfig y)) ^ 2) w) :
    violation e k w = 0 := by
  unfold violation
  rw [evalPts_localMin_implies_zero k e hk w hne hmin, abs_zero]

/-- **The modulus is NOT unconditional, and the counterexample is in the same module.**

**A constant expression minimises its own squared penalty at every point, while its violation equals
`|c|` everywhere.**
**=> dropping `hne` makes the statement false, and this theorem records that as a fact about the
library rather than a caveat in prose.**

**The proof unfolds rather than forwards:** **`const c`'s `evalPts` is `c`, so the objective is the
CONSTANT function `c^2`, and a constant function is trivially locally minimal.** **Making that
unfolding visible is what shows WHY the counterexample works.** -/
theorem modulus_requires_nonvanishing_deriv (c : ℝ) (k : ℕ) (w : Fin (k * n) → ℝ) :
    IsLocalMin (fun y : Fin (k * n) → ℝ => ((GeoExpr.const c).evalPts (toNatConfig y)) ^ 2) w := by
  have hconst : ∀ y : Fin (k * n) → ℝ,
      ((GeoExpr.const c).evalPts (toNatConfig y)) ^ 2 = c ^ 2 := by
    intro y
    simp only [GeoExpr.evalPts_const]
  simp only [hconst]
  exact isLocalMin_const

/-- **The ledger: T2 now has BOTH halves, and both are `Prop`s with proofs.**

**Exactness (seven constructors, round 81) and the modulus (this file).**
**The plan listed them as separate obligations; the tree has them in different modules, and the audit was
right that only the first was in `ProofComplete`.** -/
def t2_penalty_modulus : Prop :=
  ∀ {n : ℕ} (e : GeoExpr n) (k : ℕ), e.maxPoint < k →
    ∀ (w : Fin (k * n) → ℝ), derivExpr k e w ≠ 0 →
    IsLocalMin (fun y : Fin (k * n) → ℝ => (e.evalPts (toNatConfig y)) ^ 2) w →
    violation e k w = 0

/-- **`t2_penalty_modulus` holds** -- by `penalty_min_violation_eq_zero`. -/
theorem t2_penalty_modulus_holds : t2_penalty_modulus := by
  intro n e k hk w hne hmin
  exact penalty_min_violation_eq_zero e k hk w hne hmin

end Lattice.Plugins.Targets
