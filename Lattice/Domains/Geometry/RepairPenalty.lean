import Lattice.Domains.Geometry.PartialReinjection
import Mathlib
import Lattice.Domains.Geometry.Loop
import Lattice.Domains.Constraints.Loss
import Lattice.Domains.Geometry.RepairBridge

/-!
# `Lattice.Geo.RepairPenalty` -- the loop's criterion *is* a penalty's zero set

## Why a separate file

Two files have to meet here and neither may import the other:

* `Lattice.Geo.Loop` defines `samePointRepair`, whose `Sat` is `Holds (.samePoint a b)`;
* `Lattice.Geo.Loss` defines `EqConstraint.loss` and proves `loss = 0 ↔ Holds (eqToGeo c)`.

`Loop` cannot import `Loss` (the penalty is downstream of the constraints the loop operates on), and `Loss`
cannot import `Loop` (that would put the repair machinery under the penalty layer). A third file that imports
both is the ordinary resolution: the join lives above the two things it joins, which is also where a reader
would look for it.

## What the join says

The objective's fourth target asks that the verification loop *not destroy semantics*, and the second says that
a constraint is embedded reliably when its penalty decides it. Put together: **a repair that stops is a repair
whose penalty has reached zero**. Neither theorem states that alone --

* `Repair.progress` says the loop reaches `Sat`;
* `loss_eq_zero_toGeo_samePoint` says `Sat` and "penalty zero" are the same condition;

and the composition is what lets a training procedure read a zero penalty as evidence about the symbolic side.

## Liveness note

Every theorem below is outside any comment and reachable from `Lattice.Geo`'s public surface; `gov/audit_liveness.py`
checks that mechanically, because a theorem written inside a docstring is one Lean never sees.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The `samePoint` repair's criterion is the `samePoint` penalty's zero set.**

`samePointRepair`'s `Sat` is `Holds (.samePoint a b)`, and `EqConstraint.loss` vanishes exactly on that
constraint through `eqToGeo`. Chaining the two is the T4-to-T2 join for the one repair the geometry layer ships. -/
theorem samePoint_penalty_iff_sat (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) pts = 0
      ↔ (samePointRepair a b).Sat pts := by
  rw [loss_eq_zero_toGeo_samePoint]
  rfl

/-- **The `samePoint` loop reaches a zero of the penalty.**

An instance of `Lattice.Core.Repair.repair_success_is_penalty_zero` at the geometry repair, with the equivalence
supplied by `samePoint_penalty_iff_sat`. The conclusion is about the penalty, not about `Sat`: this is the form a
caller who has been watching a loss curve can use. -/
theorem samePoint_loop_reaches_penalty_zero (a b : ℕ) (pts : ℕ → Pt n) :
    ∃ k : ℕ, EqConstraint.loss (.samePoint a b) ((samePointRepair a b).fix^[k] pts) = 0 :=
  Lattice.Core.Repair.repair_success_is_penalty_zero
    (samePointRepair a b)
    (fun p => EqConstraint.loss (.samePoint a b) p)
    (fun p => (samePoint_penalty_iff_sat a b p).symm) pts

/-- **A satisfying state has zero penalty**, the converse direction, stated because a caller may arrive holding
satisfaction and need the penalty form. -/
theorem samePoint_sat_implies_penalty_zero (a b : ℕ) (pts : ℕ → Pt n)
    (h : (samePointRepair a b).Sat pts) :
    EqConstraint.loss (.samePoint a b) pts = 0 :=
  (samePoint_penalty_iff_sat a b pts).mpr h

/-- **The join is not vacuous**: `repair_success_is_penalty_zero` needs a real equivalence, and this records that
the one above is an equivalence rather than a one-way implication. -/
theorem samePoint_penalty_zero_iff_sat_iff (a b : ℕ) :
    (∀ pts : ℕ → Pt n,
        EqConstraint.loss (.samePoint a b) pts = 0 ↔ (samePointRepair a b).Sat pts) :=
  fun pts => samePoint_penalty_iff_sat a b pts

/-! ## 从「惩罚恰为零」到「惩罚有界」：修正不完全时的定量保证

本文件的定理都说**修正**到达**惩罚恰为零**：`samePoint_loop_reaches_penalty_zero` 等。
**但真实的修正循环往往只跑有限步，残差不会恰为零，只是不超过某个 `ε`。**

**`PartialReinjection.partial_reinject_bound` 正是为这个情形准备的：残差不超过 `ε` 则惩罚不超过 `ε²`。**
**⇒ 本节把它接到本文件：现在的结论不是「修正完全时惩罚为零」，而是「修正到 `ε` 以内时惩罚在 `ε²` 以内」。**
**这是定量的，而不只是定性的：`ε²` 随 `ε` 二次下降，因此把残差减半就把惩罚减到四分之一。** -/

/-- **修正不完全时的惩罚界。**

**若某约束的残差绝对值不超过 `ε ≥ 0`，则它的损失不超过 `ε²`。**

**=> 「修正完全」是 `ε = 0` 的特例，此时结论是 `loss ≤ 0` 即恰为零，与 `samePoint_loop_reaches_penalty_zero`
的结论一致；而 `ε > 0` 时本定理给出的是一条**定量**保证，那是本文件其余定理没有覆盖的。**
**⇒ 两条结论并列，`partial_reinject_bound` 严格覆盖更广：它把「恰为零」作为端点包含进来。** -/
theorem repair_loss_bounded_by_residual (c : EqConstraint n) (pts : ℕ → Pt n) {ε : ℝ}
    (hε : 0 ≤ ε) (h : |EqConstraint.poly c pts| ≤ ε) :
    EqConstraint.loss c pts ≤ ε ^ 2 :=
  Lattice.Geo.PartialReinjection.partial_reinject_bound c pts hε h

/-- **`ε = 0` 时定量界退化为「惩罚为零」。**

**=> 本文件的定性结论与 `partial_reinject_bound` 的定量结论**在端点处一致**，因此后者不是另一种说法，
而是前者的推广。**
**「把残差减半则惩罚减到四分之一」这一二次关系是额外的内容：定性结论在 `ε = 0` 处给不出任何信息。** -/
theorem repair_loss_zero_of_exact (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : |EqConstraint.poly c pts| ≤ 0) :
    EqConstraint.loss c pts ≤ 0 := by
  have hb := Lattice.Geo.PartialReinjection.partial_reinject_bound c pts (le_refl (0 : ℝ)) h
  simpa using hb


end Lattice.Geo
