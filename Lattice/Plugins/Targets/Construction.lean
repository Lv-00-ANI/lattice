/-
# `Targets/Construction.lean` -- T0's constructor, stated at the only strength it can hold

## Why this file exists

**T0 of the execution plan is `construct_sound` / `construct_complete` / `construct_canonical` /
`construct_approx` / `construct_from_scratch`, all restricted to `ExpressibleSpec`.**

**Four of the five were OPEN for the whole project, and the ledger said so.**
**The reason was never laziness: round 80 proved that the UNIVERSAL constructor cannot exist.**
**`SolverBoundary.no_specSolver : IsEmpty (SpecSolver n)` -- a solver that works for EVERY
`ExpressibleSpec` is uninhabited, because `[eqZero (const 1)]` is expressible and unsatisfiable.**

**=> the honest form of T0's constructor is a `FamilySolver`: a construction that carries the FAMILY of
specs it handles, together with the proof that it handles them.**

**This file PROMOTES `FamilySolver` to the four T0 obligations.**
**It does not weaken them by fiat: each of the four has a precise statement, and the family restriction is
carried in the TYPE rather than hidden in a hypothesis.**

## A semantic detail that shapes the proofs

**`HoldsSet` is defined by STRUCTURAL RECURSION on the list, not as a `∀` over its members:**
`HoldsSet [] pts := True` and `HoldsSet (c :: cs) pts := Holds c pts ∧ HoldsSet cs pts`.
**=> a solver's per-constraint `sound` field does not immediately give `HoldsSet S.constraints`.**
**`holdsSet_of_forall` below is that step, and it is the real content of `construct_complete`.**

## What this file does NOT claim

**It does not produce a solver for any NEW family.**
**It turns the family-restricted construction into T0's four obligations, so that "T0 is done" means "a
family solver exists and its obligations are proved" rather than "a solver exists".**
**The degenerate family (`Targets/DegenerateSolver.lean`) and the `samePoint` family
(`Targets/MultiSolver.lean`) are the two instances that already discharge it.**
-/

import Mathlib
import Lattice.Plugins.Targets.MultiSolver
import Lattice.Plugins.Targets.DegenerateSolver
import Lattice.Plugins.Targets.SolverBoundary
import Lattice.Plugins.Targets.Statements

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-! ## From per-member `Holds` to `HoldsSet` -/

/-- **A predicate holding at every member of a list gives `HoldsSet` on that list.**

**This is the step `construct_complete` needs, and it is NOT definitional:**
**`HoldsSet` recurses on the list, so the induction hypothesis must be applied at the tail.** -/
theorem holdsSet_of_forall {n : ℕ} (l : List (GeoConstraint n)) (cfg : ℕ → Pt n)
    (h : ∀ c ∈ l, Holds c cfg) : HoldsSet l cfg := by
  induction l with
  | nil => exact trivial
  | cons c rest ih =>
    exact ⟨h c (List.mem_cons_self c rest),
           ih (fun d hd => h d (List.mem_cons_of_mem c hd))⟩

/-- **`HoldsSet` on the whole spec, from a `FamilySolver`.**

**This is `construct_complete` for the family: the model the solver returns makes every constraint of the
spec hold at once.**
**The proof goes through `holdsSet_of_forall` rather than by unfolding, because `HoldsSet` is recursive.** -/
theorem FamilySolver.holdsSet_all {n : ℕ} (F : FamilySolver n)
    (S : ExpressibleSpec n) (hS : F.Family S) :
    HoldsSet S.constraints (F.solve S hS) :=
  holdsSet_of_forall S.constraints (F.solve S hS)
    (fun c hc => by
      -- `sound` gives `HoldsSet [c]`, and `HoldsSet [c]` is `Holds c ∧ True`, so project it
      have h := F.sound S hS hc
      exact h.1)

/-! ## T0's four obligations, at family strength -/

/-- **`T0.construct_sound`, restricted to the family.**

**The construction is sound: every constraint of the spec holds at the produced configuration.** -/
def construct_sound {n : ℕ} (F : FamilySolver n) : Prop :=
  ∀ (S : ExpressibleSpec n) (hS : F.Family S) ⦃c : GeoConstraint n⦄,
    c ∈ S.constraints → HoldsSet [c] (F.solve S hS)

/-- **`construct_sound` holds for every `FamilySolver`.** -/
theorem construct_sound_holds {n : ℕ} (F : FamilySolver n) : construct_sound F :=
  fun S hS _ hc => F.sound S hS hc

/-- **`T0.construct_complete`, restricted to the family.**

**The construction is complete: the produced configuration satisfies the ENTIRE spec, not only its
individual constraints.**
**This is strictly stronger than `construct_sound`, and that gap is the real contribution of this file.** -/
def construct_complete {n : ℕ} (F : FamilySolver n) : Prop :=
  ∀ (S : ExpressibleSpec n) (hS : F.Family S), HoldsSet S.constraints (F.solve S hS)

/-- **`construct_complete` holds for every `FamilySolver`.** -/
theorem construct_complete_holds {n : ℕ} (F : FamilySolver n) : construct_complete F :=
  fun S hS => F.holdsSet_all S hS

/-- **`T0.construct_canonical`, restricted to the family.**

**Two specs with the SAME constraint list get the SAME configuration.**
**This is what makes the construction a function of the spec rather than of how the spec was written
down.** -/
def construct_canonical {n : ℕ} (F : FamilySolver n) : Prop :=
  ∀ (S T : ExpressibleSpec n) (hS : F.Family S) (hT : F.Family T),
    S.constraints = T.constraints → F.solve S hS = F.solve T hT

/-- **`construct_canonical` holds for every `FamilySolver`.** -/
theorem construct_canonical_holds {n : ℕ} (F : FamilySolver n) : construct_canonical F :=
  fun S T hS hT h => F.canonical S T hS hT h

/-- **`T0.construct_approx`, restricted to the family.**

**The construction achieves ZERO total penalty, not a bound on it.**
**Zero is the sharpest statement available, and `FamilySolver.cost_zero` supplies it** -- **so `approx`
here is stronger than "approximately", and the name is kept to match the plan's vocabulary.** -/
def construct_approx {n : ℕ} (F : FamilySolver n) : Prop :=
  ∀ (S : ExpressibleSpec n) (hS : F.Family S),
    (S.constraints.map (fun c => penaltyLoss c (F.solve S hS))).sum = 0

/-- **`construct_approx` holds for every `FamilySolver`.** -/
theorem construct_approx_holds {n : ℕ} (F : FamilySolver n) : construct_approx F :=
  fun S hS => F.cost_zero S hS

/-! ## The four obligations in one predicate -/

/-- **All four family-restricted T0 obligations at once.** -/
def ConstructsFor {n : ℕ} (F : FamilySolver n) : Prop :=
  construct_sound F ∧ construct_complete F ∧ construct_canonical F ∧ construct_approx F

/-- **EVERY `FamilySolver` discharges all four T0 obligations.**

**=> T0's constructor is a SHAPE, and any inhabitant of that shape proves the four obligations.**
**The two instances below show this is not vacuous.** -/
theorem constructsFor_of_familySolver {n : ℕ} (F : FamilySolver n) : ConstructsFor F :=
  ⟨construct_sound_holds F, construct_complete_holds F,
   construct_canonical_holds F, construct_approx_holds F⟩

/-- **T0's constructor EXISTS for the degenerate family.**

**A witness, not a schema: `degenerateSolver` is an actual `FamilySolver`, so T0's four obligations have a
real instance.** -/
theorem t0_constructor_exists {n : ℕ} (p : Pt n) :
    ∃ F : FamilySolver n, ConstructsFor F :=
  ⟨Lattice.Plugins.Targets.degenerateSolver n p,
   constructsFor_of_familySolver _⟩

/-- **T0's constructor EXISTS for the `samePoint` family.** -/
theorem t0_constructor_samePoint (p : Pt 1) :
    ∃ F : FamilySolver 1, ConstructsFor F :=
  ⟨Lattice.Plugins.Targets.samePointFamilySolver 1 p,
   constructsFor_of_familySolver _⟩

/-! ## The boundary this does NOT cross -/

/-- **No UNIVERSAL constructor exists, so T0 cannot be stated without a family.**

**This restates round 80's result here, because it is the reason the four obligations above are
family-restricted: a solver whose family is EVERYTHING would produce a model for the unsatisfiable spec.** -/
theorem no_universal_constructor {n : ℕ} (hn : 0 < n) :
    ¬ ∃ F : FamilySolver n, F.Family = fun _ => True := by
  intro ⟨F, hF⟩
  have hall : F.Family (Lattice.Plugins.Targets.unsatisfiableSpec n) := by
    rw [hF]; exact trivial
  have hmodel : HoldsSet (Lattice.Plugins.Targets.unsatisfiableSpec n).constraints
      (F.solve (Lattice.Plugins.Targets.unsatisfiableSpec n) hall) :=
    F.holdsSet_all _ hall
  exact Lattice.Plugins.Targets.unsatisfiableSpec_no_model
    (F.solve (Lattice.Plugins.Targets.unsatisfiableSpec n) hall) hmodel

end Lattice.Plugins.Targets
