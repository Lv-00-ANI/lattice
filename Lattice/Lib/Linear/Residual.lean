import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Core.RepairModule.ConstraintProofs
import Lattice.Core.RepairModule.Repair
import Lattice.Runtime.PenaltyEmbedding
/-!
# `Lattice.Lib.Linear.Residual` -- the first real instance of the repair framework

## Why this file exists

`Lattice.Core.Repair` was instantiated only by `parityRepair`, a pure-arithmetic toy: it repairs
a natural number to be even. That exercise shows the three obligations are *satisfiable*, but
not that they are satisfiable by a mathematical object the project actually cares about.

Here the repair operator is the one a verification loop really needs: given a linear constraint
`a·x + b = 0`, repair a point until the constraint holds. The measure is `|a·x + b|`, the
residual, and the obligation `decreases` is the statement that a repair step strictly shrinks it.

## Why the carrier is `ℚ`

The linear fragment could be stated over `ℤ`, as the legacy tree did. Over `ℤ` a repair step
needs divisibility and the argument acquires side conditions that have nothing to do with
verification. Over `ℚ` the step is `x ↦ x - (a·x + b)/a`, division is total and exact, and the
fragment is still linear -- no topology, no measure theory. Rationals are the smallest carrier
on which the obligation is honest.

## Why `a ≠ 0` is a hypothesis rather than an assumption

A one-variable constraint with `a = 0` is either vacuous (`b = 0`) or unsatisfiable
(`b ≠ 0`), and in the unsatisfiable case no repair can converge. `zero_slope_unsolvable` below
is the machine-checked form of that, and it is why `a ≠ 0` appears as an explicit parameter
everywhere rather than being silently guaranteed.
-/

namespace Lattice.Lib.Linear

open Lattice.Core
open Lattice.Lift

/-- The residual of a one-variable linear constraint: `a·x + b`.

This is `LinearForm.denote` at arity one, named here so the repair statements read as
mathematics rather than as applications of a denotation function. -/
def residual (a b x : ℚ) : ℚ := a * x + b

/-- The residual coincides with the core denotation at arity one.

Not a redefinition: the equality is proved, so there is exactly one notion of "the value of a
linear form" in the project. -/
theorem residual_eq_denote (a b x : ℚ) :
    residual a b x = (⟨fun _ => a, b⟩ : LinearForm ℚ 1).denote (fun _ => x) := by
  unfold residual LinearForm.denote
  simp

/-- **The slope is load-bearing.** A constraint with zero slope and nonzero constant has no
solution at all, so no repair operator can converge on it.

This is the necessity witness for the `a ≠ 0` hypothesis of `linearRepair`. -/
theorem zero_slope_unsolvable (b : ℚ) (hb : b ≠ 0) : ¬ ∃ x : ℚ, residual 0 b x = 0 := by
  rintro ⟨x, hx⟩
  unfold residual at hx
  simp only [zero_mul, zero_add] at hx
  exact hb hx

/-! ## The repair operator -/

/-- A repair step for `a·x + b = 0`: move `x` by the amount that zeroes the residual.

When the constraint already holds the step is the identity, which is what the `absorbs`
obligation requires. -/
def linearFix (a b x : ℚ) : ℚ := if residual a b x = 0 then x else x - residual a b x / a

/-- A repair step zeroes the residual, and the new point also satisfies the constraint.

The second half is what makes the loop terminate in one step; the first is the "strictly
improves" half. -/
theorem linearFix_residual (a b x : ℚ) (ha : a ≠ 0) : residual a b (linearFix a b x) = 0 := by
  unfold linearFix
  by_cases h : residual a b x = 0
  · simp only [h, if_true, linearFix]
  · simp only [h, if_false]
    unfold residual
    field_simp
    ring

/-- A point that already satisfies the constraint is not moved. -/
theorem linearFix_absorbs (a b x : ℚ) (h : residual a b x = 0) :
    linearFix a b x = x := by
  unfold linearFix
  simp only [h, if_true]

/-- The repair operator for `a·x + b = 0` with `a ≠ 0`, as a `Lattice.Core.Repair` instance.

The slope hypothesis is a parameter, not a convenience: a constraint with zero slope is either
vacuous or unsatisfiable (`zero_slope_unsolvable`), and in the latter case no repair can
converge. Building the instance only for non-degenerate constraints keeps `decreases` provable
without pretending the degenerate case is repairable.

The measure records "satisfied or not" as `0` or `1`. That is crude on purpose: the real
strength here is `linearFix_residual`, which shows the step zeroes the residual in one move, and
a fancier measure would only obscure which fact does the work. -/
def linearRepair (a b : ℚ) (ha : a ≠ 0) : Repair ℚ where
  Sat := fun x => residual a b x = 0
  fix := linearFix a b
  μ := fun x => if residual a b x = 0 then 0 else 1
  absorbs := linearFix_absorbs a b
  decreases := by
    intro x hx
    have hzero := linearFix_residual a b x ha
    show (if residual a b (linearFix a b x) = 0 then 0 else 1) < (if residual a b x = 0 then 0 else 1)
    rw [if_neg hx, hzero]
    norm_num
  atomic := by
    intro x hx
    by_contra h
    simp only [h, if_false] at hx
    omega

/-- **The measure genuinely drops** at a failing point, so `decreases` is not vacuous. -/
theorem linearRepair_measure_drops (a b x : ℚ) (ha : a ≠ 0) (hx : residual a b x ≠ 0) :
    (linearRepair a b ha).μ ((linearRepair a b ha).fix x) < (linearRepair a b ha).μ x :=
  (linearRepair a b ha).decreases x (by simpa using hx)

/-- **Convergence of the linear repair loop.**

One step suffices whenever the slope is nonzero: the repaired point satisfies the constraint.
This is T4 (`Repair.progress`) applied to a concrete mathematical object rather than to a
parity toy. -/
theorem linear_converges (a b x : ℚ) (ha : a ≠ 0) :
    ∃ k : ℕ, (linearRepair a b ha).Sat ((linearRepair a b ha).iterate k x) :=
  Repair.progress (linearRepair a b ha) x

/-- And the repair is immediate: the first iterate already satisfies the constraint. -/
theorem linear_converges_in_one (a b x : ℚ) (ha : a ≠ 0) :
    (linearRepair a b ha).Sat ((linearRepair a b ha).iterate 1 x) :=
  linearFix_residual a b x ha

/-! ## The squared-residual penalty, and its two levels

The legacy `ConstraintEmbeddingSoundness` proved, for `Int`-valued constraints, that a zero of
`(a·x + b)^2` satisfies the constraint. That is level A for one specific penalty and one specific
carrier. Here the same penalty is put on the rationals and its levels are derived from the general
framework:

* non-negativity, by `sq_nonneg`;
* level A, by `exact_implies_sound` once level B is available;
* level B itself is *not* proved -- it is the open obligation `lift.embed.local_minimiser_exact`,
  and `sqPenalty_exact_gives_sound` shows precisely what it would buy.

That is the honest arrangement: the cheap half is discharged, the expensive half stays a named
obligation instead of being folded into a hypothesis nobody tracks. -/

/-- The squared-residual penalty for a one-variable constraint.

The loss is `Real`-valued, as `PenaltyEmbedding` requires; the constraint's own carrier stays
`Rational`, which is what the repair operator works on. `Sat` is stated through the same coercion
the loss uses, so the two levels talk about one term rather than two statements that merely look
alike -- the defect a first draft had, where `loss` coerced to `Real` while `Sat` compared in
`Rational`.

Keeping the loss and the predicate on a shared term is also why `residual` is reused instead of a
fresh expression: the repair loop and the penalty must agree on what "solving" means. -/
def sqPenalty (a b : ℚ) : PenaltyEmbedding Unit ℚ where
  loss := fun _ x => ((residual a b x : ℚ) : ℝ) ^ 2
  Sat := fun _ x => ((residual a b x : ℚ) : ℝ) = 0

/-- The penalty is non-negative. -/
theorem sqPenalty_nonneg (a b : ℚ) (x : ℚ) : 0 ≤ (sqPenalty a b).loss () x := by
  simp only [sqPenalty]
  positivity

/-- A zero of the penalty is a zero of the residual, by `sq_eq_zero_iff` on `Real`.

Proved as its own lemma so that level A below is a one-line consequence and so that the coercion
appears exactly once. -/
theorem sqPenalty_zero_iff (a b x : ℚ) :
    (sqPenalty a b).loss () x = 0 ↔ (sqPenalty a b).Sat () x := by
  simp only [sqPenalty, sq_eq_zero_iff]

/-- **Level A.** A zero of the squared residual satisfies the constraint.

This is the legacy `embedding_soundness`, obtained from the algebraic lemma `sq_eq_zero_iff`
rather than re-proved for a fixed carrier. -/
theorem sqPenalty_levelA (a b : ℚ) : PenaltySound (sqPenalty a b) :=
  fun _ x h => (sqPenalty_zero_iff a b x).mp h

/-- **Level B gives level A for this penalty.** If the penalty is exact at local minimisers, then a
zero of the residual satisfies the constraint -- the nesting theorem applied to a concrete
embedding, which is what makes `exact_implies_sound` worth its proof. -/
theorem sqPenalty_exact_gives_sound (a b : ℚ)
    (hexact : PenaltyExact (sqPenalty a b)) : PenaltySound (sqPenalty a b) :=
  exact_implies_sound (fun _ x => sqPenalty_nonneg a b x) hexact

end Lattice.Lib.Linear
