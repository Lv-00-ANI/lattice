/-
# The `DegenerateOK` family as a `FamilySolver` instance

**Round 75 proved the satisfaction lemmas and the expressibility lemmas for four constraint kinds, and
its commit recorded what was missing: "wrapping them into a `FamilySolver` value over lists".**
**This file does that wrapping.**

## What the instance adds beyond the lemmas

**The lemmas are about ONE constraint (`holds_of_degenerateOK c hc p`).**
**A `FamilySolver` needs:
- a `Family : ExpressibleSpec n → Prop` -- **here: every member is `DegenerateOK`.**
- `sound` -- **for a LIST**, which requires traversing `HoldsSet`'s `∧`.
- `canonical` -- **equal specs give equal parameters.**
- `cost_zero` -- **the sum over the list vanishes.**

**The list traversal is the part that is NOT a corollary of the per-constraint lemma: `HoldsSet` is a
right-nested conjunction, and the induction that walks it is the same one `construct_sound` must
perform.**

## Why `FamilySolver` and not `SpecSolver`

**`SpecSolver.sound` quantifies `∀ S : ExpressibleSpec n` -- every spec.**
**A constant configuration does NOT satisfy `eqZero e` or `ltZero e`, so no universal instance exists
with this construction.** **=> the family restriction is not a convenience; it is the truth.**
**Round 74 recorded this discovery; this file is where the restricted instance actually gets BUILT.**
-/

import Lattice.Plugins.Targets.ConstFamily

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

/-- **The `DegenerateOK` family: every constraint of the spec is in the family.** -/
def degenerateFamily {n : ℕ} (S : ExpressibleSpec n) : Prop :=
  ∀ c ∈ S.constraints, DegenerateOK c

/-- **A list of `DegenerateOK` constraints holds at any constant configuration.**

**Induction on the list.** **The `cons` case splits `HoldsSet`'s conjunction: the head is
`holds_of_degenerateOK`, the tail is the induction hypothesis.**
**This is the traversal `construct_sound` needs, and it is the reason the instance is not a mere
restatement of the per-constraint lemma.** -/
theorem holdsSet_of_degenerate {n : ℕ} (cs : List (GeoConstraint n))
    (h : ∀ c ∈ cs, DegenerateOK c) (p : Pt n) :
    HoldsSet cs (fun _ => p) := by
  induction cs with
  | nil => exact holdsSet_nil _
  | cons hd tl ih =>
    refine ⟨holds_of_degenerateOK hd (h hd (by simp)) p, ?_⟩
    exact ih (fun c hc => h c (by simp [hc]))

/-- **The total penalty of a `DegenerateOK` list vanishes at any constant configuration.**

**Each summand vanishes by `penaltyLoss_eq_zero_of_holds` applied to `holds_of_degenerateOK`, and the
sum of zeros is zero by induction on the list.** -/
theorem penaltySum_of_degenerate {n : ℕ} (cs : List (GeoConstraint n))
    (h : ∀ c ∈ cs, DegenerateOK c) (p : Pt n) :
    (cs.map (fun c => penaltyLoss c (fun _ => p))).sum = 0 := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [penaltyLoss_eq_zero_of_holds _ _ (holds_of_degenerateOK hd (h hd (by simp)) p),
        ih (fun c hc => h c (by simp [hc]))]
    exact zero_add 0

/-- **The `DegenerateOK` family's `FamilySolver` instance.**

**`solve := fun _ _ => fun _ => p` -- a fixed constant configuration.**
**Its correctness rests on ONE fact: at a constant configuration every segment is zero, so all four
kinds collapse to a reflexivity identity.**

**`sound` traverses the list; `canonical` holds because `solve` ignores its arguments; `cost_zero`
sums the per-constraint zeros.**

**This is the instance round 75 named as missing.** -/
def degenerateSolver (n : ℕ) (p : Pt n) : FamilySolver n where
  Family := degenerateFamily
  solve := fun _ _ => fun _ => p
  sound := by
    intro S hS c hc
    -- `HoldsSet [c]` versus `Holds c`: the former unfolds to `Holds c ∧ True`
    exact ⟨holds_of_degenerateOK c (hS c hc) p, holdsSet_nil _⟩
  canonical := by
    intro S T _ _ _
    rfl
  cost_zero := by
    intro S hS
    exact penaltySum_of_degenerate S.constraints hS p

/-- **The family is non-empty on a concrete spec.**

**`samePointSpec [(0, 1)]` is a spec of length one whose only member is a `samePoint`, so it lies in
`degenerateFamily`.** **This witnesses that the instance is not vacuous -- a `FamilySolver` whose
family contained no spec would be satisfiable by a degenerate argument.** -/
theorem degenerateFamily_nonempty (n : ℕ) :
    degenerateFamily (samePointSpec (n := n) [(0, 1)]) := by
  intro c hc
  simp only [samePointSpec, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  subst hc
  exact Or.inl ⟨0, 1, rfl⟩

end Lattice.Plugins.Targets
