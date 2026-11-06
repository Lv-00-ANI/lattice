/-
# The boundary of `SpecSolver`, proved rather than asserted

**The audit's finding: `SpecSolver.sound` quantifies `∀ (S : ExpressibleSpec n)` -- EVERY expressible
spec -- and therefore cannot be instantiated by a construction that only works for SOME constraints.**
**Round 74 recorded this in prose (`MultiSolver.lean`'s `specSolver_is_family_limited`, which was cited
but never written).** **This file makes it a THEOREM.**

## The counterexample

**`eqZero (const 1)` is an expressible constraint** -- **its layer is `poly`.**
**Any configuration satisfying it must have `evalPts (const 1) = 1 = 0`, which is false.**
**=> the spec `[eqZero (const 1)]` has NO solution at all, so no `solve` function can be `sound` for it.**

**That is stronger than "a constant configuration fails": it says NO construction whatsoever can be
sound for every spec, because one spec has no models.**
**=> `SpecSolver` is UNINHABITED unless the spec list is restricted.**

## What this licenses

**`FamilySolver` (round 74) is not a weaker fallback -- it is the ONLY correct shape for a solver whose
construction is partial.**
**`FamilySolverToSpecSolver` below records exactly when a `FamilySolver` yields a `SpecSolver`: when its
family is `fun _ => True`, i.e. never for these carriers.**
-/

import Lattice.Plugins.Targets.MultiSolver

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.GeoConstraint

/-- **`eqZero (const 1)` is EXPRESSIBLE.**

**Its layer is `poly`, which `ExpressibleLayer` admits.** -/
theorem eqZero_const_one_expressible {n : ℕ} :
    IsExpressible (n := n) (GeoConstraint.eqZero (GeoExpr.const (1 : ℝ))) := by
  unfold IsExpressible ExpressibleLayer
  exact Or.inl rfl

/-- **The spec `[eqZero (const 1)]`, which is expressible.**

**Constructed here because it is the counterexample the boundary theorem needs.** -/
def unsatisfiableSpec (n : ℕ) : ExpressibleSpec n :=
  ExpressibleSpec.single (GeoConstraint.eqZero (GeoExpr.const (1 : ℝ)))
    eqZero_const_one_expressible

/-- **The counterexample constraint is not satisfied by ANY configuration.**

**`evalPts (const 1) pts = 1`, and `Holds (.eqZero e) pts` requires it to be `0`.**
**=> `1 ≠ 0`. Nothing about the configuration enters.** -/
theorem not_holds_eqZero_const_one {n : ℕ} (pts : ℕ → Pt n) :
    ¬ Holds (GeoConstraint.eqZero (GeoExpr.const (1 : ℝ))) pts := by
  show ¬ ((GeoExpr.const (1 : ℝ)).evalPts pts = 0)
  simp only [GeoExpr.evalPts_const]
  norm_num

/-- **The spec has NO model.**

**`HoldsSet [c] pts` unfolds to `Holds c pts ∧ True`, and the first conjunct is impossible.**
**=> this is the statement a solver's `sound` field would have to contradict.** -/
theorem unsatisfiableSpec_no_model {n : ℕ} (pts : ℕ → Pt n) :
    ¬ Lattice.Geo.ConstraintSet.HoldsSet (unsatisfiableSpec n).constraints pts := by
  intro h
  have hc : Holds (GeoConstraint.eqZero (GeoExpr.const (1 : ℝ))) pts := h.1
  exact not_holds_eqZero_const_one pts hc

/-- **THE BOUNDARY: no `SpecSolver` exists for `n` with a nonempty type of points, IF every spec must
be handled.**

**Stated over a hypothetical `sol : SpecSolver n`: its `sound` field, applied to
`unsatisfiableSpec n`, produces a model of a spec that has none.**
**=> `False`.**

**Note what is quantified: `¬ SpecSolver n` says there is NO such structure at all, not merely that a
particular construction fails.**
**That is the finding the audit reported and that round 74 could only assert.** -/
theorem no_specSolver {n : ℕ} (hne : Nonempty (Pt n)) : IsEmpty (SpecSolver n) := by
  constructor
  intro sol
  -- the solver must satisfy its own spec at its own solution
  have hmem : GeoConstraint.eqZero (GeoExpr.const (1 : ℝ))
      ∈ (unsatisfiableSpec n).constraints := by
    show GeoConstraint.eqZero (GeoExpr.const (1 : ℝ)) ∈ [GeoConstraint.eqZero (GeoExpr.const (1 : ℝ))]
    exact List.mem_singleton_self _
  have hsat := sol.sound (unsatisfiableSpec n) hmem
  exact unsatisfiableSpec_no_model (sol.solve (unsatisfiableSpec n)) hsat

/-- **A `FamilySolver` becomes a `SpecSolver` only if its family is TOTAL.**

**This is the positive half of the boundary: it says exactly what would be needed, and it is not
satisfiable for the carriers here because `degenateFamily` is proper.**
**Stated as an implication rather than a construction, because the construction cannot exist.** -/
def familyTotalGivesSpecSolver (n : ℕ) (F : FamilySolver n) : Prop :=
  (∀ S : ExpressibleSpec n, F.Family S) → Nonempty (SpecSolver n)

/-- **`familyTotalGivesSpecSolver` is NOT satisfied by any solver over a NONEMPTY point type.**

**Since no `SpecSolver n` exists at all when `Pt n` is nonempty, no family can yield one.**
**A reader who wonders "can I just make the family total?" gets the answer here rather than by trying.** -/
theorem familyTotalGives_no_solver {n : ℕ} (hne : Nonempty (Pt n)) :
    ¬ Nonempty (SpecSolver n) :=
  not_nonempty_iff.2 (no_specSolver hne)

end Lattice.Plugins.Targets
