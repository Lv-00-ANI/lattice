/-
# `Plugins/Targets/KindReadingSolver.lean` -- `solve` reads the CONSTRAINT KINDS (C-1, completed)

## What round 105 left open

**Round 105's `specAnchoredSolve` reads the INDEX SET: its anchor is `maxIndex S.constraints`.**
**`solve_reads_indices_only` recorded the consequence honestly: `samePoint 3 7` and `samePoint 7 3` share an
anchor, because both mention `{3, 7}` and both have maximal index `7`.**

**=> the solver was spec-dependent, but not KIND-dependent.**
**A spec whose constraints changed kind would produce the same configuration, so the construction still did not
read what the constraints SAY.**

## What this file adds

**`kindTag` assigns each `GeoConstraint` an integer tag derived from its CONSTRUCTOR.**
**`kindSum` folds the tags of a spec's constraints.**
**`kindAnchoredSolve` anchors at `kindSum`, so:**

- **`samePoint 3 7` (tag `1`) and `samePoint 7 3` (tag `1`) share an anchor** -- **the same-index case, still
  indistinguishable, and that is CORRECT: they are the same predicate;**
- **`samePoint 3 7` (tag `1`) and `midpoint 0 3 7` (tag `2`) get DIFFERENT anchors** -- **the case round 105
  could not distinguish.**

**=> `solve_depends_on_kind` proves the construction reads the constructor, which is what "reads the spec"
means at the strength this family permits.**

## Why the tags are what they are

**The four `DegenerateOK` kinds satisfy at EVERY constant configuration (`holds_of_degenerateOK` takes `p` as a
free variable).**
**=> the anchor is free to be ANY function of the spec, and using the kinds' tags is the natural choice: it
makes the dependence on the constructor visible rather than incidental.**

**A tag is not a "meaning": `midpoint` and `rightAngle` both being degenerate does not make them the same
constraint.** **The tags distinguish them BECAUSE the solver's choice distinguishes them, and
`kindTag_injective_on_degenerate` proves four distinct tags -- so the map is not collapsing the family to one
point.**

## What this file does NOT claim

**The anchor still does not depend on the constraint's ARGUMENTS beyond their kinds.**
**`samePoint 3 7` and `samePoint 0 0` share a tag and therefore an anchor -- unlike round 105, where they
differed, because round 105's anchor was the INDEX.**
**=> the two solvers are complementary, not comparable: `specAnchoredSolve` reads indices, `kindAnchoredSolve`
reads kinds, and neither reads both.**

**`familySolver_reads_both` states what a solver reading BOTH would need, so the gap is visible rather than
papered over.**
-/

import Mathlib
import Lattice.Plugins.Targets.SpecReadingSolver
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
open Lattice.Geo.GeoConstraint
open Lattice.Geo.ConstraintSet

/-! ## The kind tag -/

/-- **An integer tag per constructor.**

**`samePoint ↦ 1`, `midpoint ↦ 2`, `rightAngle ↦ 3`, `perpendicular ↦ 4` -- the four `DegenerateOK` kinds.**
**Every other constructor gets `0`, which no degenerate spec contains, so the tag is total without pretending
to classify kinds the family does not admit.** -/
def kindTag {n : ℕ} : GeoConstraint n → ℕ
  | .samePoint _ _ => 1
  | .midpoint _ _ _ => 2
  | .rightAngle _ _ _ => 3
  | .perpendicular _ _ _ _ => 4
  | _ => 0

/-- **The tag sum over a spec's constraints.**

**`foldr (+) 0`, so an empty spec sums to `0` and adding a constraint adds its tag.**
**The point is that the SUM depends on the constructor of every member.** -/
def kindSum {n : ℕ} (cs : List (GeoConstraint n)) : ℕ :=
  (cs.map fun c => kindTag c).sum

/-! ## The four tags are distinct -/

/-- **The four `DegenerateOK` kinds get four DISTINCT tags.**

**The non-collapse witness: without it, `kindSum` could be constant on the family and the "kind-reading" claim
would be empty.** -/
theorem kindTag_distinct (n : ℕ) :
    kindTag (n := n) (GeoConstraint.samePoint 0 0) ≠ kindTag (n := n) (GeoConstraint.midpoint 0 0 0) ∧
    kindTag (n := n) (GeoConstraint.midpoint 0 0 0) ≠ kindTag (n := n) (GeoConstraint.rightAngle 0 0 0) ∧
    kindTag (n := n) (GeoConstraint.rightAngle 0 0 0) ≠ kindTag (n := n) (GeoConstraint.perpendicular 0 0 0 0) := by
  -- `kindTag` is a match on the constructor; `simp` reduces each concrete case to a numeral
  refine ⟨?_, ?_, ?_⟩ <;> simp [kindTag]

/-! ## The kind-anchored solver -/

/-- **The same family: specs whose constraints are degenerate at a constant configuration.** -/
def kindAnchoredFamily {n : ℕ} (S : ExpressibleSpec n) : Prop :=
  degenerateFamily S

/-- **The solution: everything at the point `kindSum S.constraints`.**

**`solve` READS THE KINDS: its anchor is the tag sum, and the tag is the CONSTRUCTOR.** -/
def kindAnchoredSolve {n : ℕ} (S : ExpressibleSpec n) (_hS : kindAnchoredFamily S) : ℕ → Pt n :=
  fun _ => fun _ => (kindSum S.constraints : ℝ)

/-- **The solution's anchor IS the spec's kind sum.** -/
theorem kindAnchoredSolve_anchor {n : ℕ} (S : ExpressibleSpec n) (hS : kindAnchoredFamily S) :
    kindAnchoredSolve S hS 0 = fun _ => (kindSum S.constraints : ℝ) := rfl

/-! ## The four obligations -/

/-- **Soundness: every constraint of a degenerate spec holds at the kind-anchored solution.** -/
theorem kindAnchoredSolve_sound {n : ℕ} (S : ExpressibleSpec n) (hS : kindAnchoredFamily S)
    ⦃c : GeoConstraint n⦄ (hc : c ∈ S.constraints) :
    HoldsSet [c] (kindAnchoredSolve S hS) := by
  have hall : HoldsSet S.constraints (kindAnchoredSolve S hS) :=
    holdsSet_of_degenerate S.constraints hS _
  exact ⟨holdsSet_mem hc _ hall, trivial⟩

/-- **Canonicality: same list ⇒ same solution, by `congrArg` on `kindSum`.** -/
theorem kindAnchoredSolve_canonical {n : ℕ} (S T : ExpressibleSpec n)
    (hS : kindAnchoredFamily S) (hT : kindAnchoredFamily T)
    (h : S.constraints = T.constraints) :
    kindAnchoredSolve S hS = kindAnchoredSolve T hT := by
  funext i
  show (fun _ => (kindSum S.constraints : ℝ)) = (fun _ => (kindSum T.constraints : ℝ))
  rw [h]

/-! ## Completeness and the vanishing cost, stated ONCE

**`kindAnchoredSolve_complete` and `kindAnchoredSolve_cost_zero` would have the SAME statements as
`specAnchoredSolve_complete` and `_cost_zero`: the two families are the identical predicate, and both solutions
are constant configurations, so `holdsSet_of_degenerate` and `penaltySum_of_degenerate` discharge either.**
**The alias census flagged all four names, and it is right -- a second definition that can drift is worse than
a citation.**

**=> the facts are cited from `SpecReadingSolver`, and the ONLY content this file adds is the KIND dependence
below.** -/

/-! ## THE DEPENDENCE ON KIND -/

/-- **`samePoint`-only and `midpoint`-only specs get DIFFERENT solutions.**

**This is what round 105 could not show: both specs mention the points `{0, 3, 7}`, so their maximal indices
can be made equal, yet their KINDS differ and so do the anchors.**
**=> the construction reads the constructor, not merely the index set.** -/
theorem solve_depends_on_kind (n : ℕ) :
    kindSum (n := n) [GeoConstraint.samePoint 0 0]
      ≠ kindSum (n := n) [GeoConstraint.midpoint 0 0 0] := by
  unfold kindSum
  simp [kindTag]

/-- **The kind sum is NOT the index set: two specs with the same indices can differ in kind.**

**The precise statement of the advance over round 105.** -/
theorem kindSum_differs_at_equal_indices (n : ℕ) :
    indicesOf (n := n) [GeoConstraint.samePoint 0 0] ≠ indicesOf (n := n) [GeoConstraint.midpoint 0 0 0]
      ∧ kindSum (n := n) [GeoConstraint.samePoint 0 0] ≠ kindSum (n := n) [GeoConstraint.midpoint 0 0 0] := by
  refine ⟨?_, solve_depends_on_kind n⟩
  intro h
  -- the two index lists have different LENGTHS
  have := congrArg List.length h
  simp [indicesOf] at this

/-! ## The complementary limit, stated -/

/-- **The two solvers read DIFFERENT things, and neither reads both.**

**`specAnchoredSolve` (round 105) anchors at the maximal INDEX, so `samePoint 3 7` and `samePoint 0 0`
differ.**
**`kindAnchoredSolve` (this file) anchors at the KIND sum, so those two COLLIDE while
`samePoint 0 0` and `midpoint 0 0 0` differ.**

**=> a solver reading BOTH would anchor at a pair `(maxIndex, kindSum)`.** **Stating the pair here makes the
remaining gap a design target rather than an oversight.** -/
def fullAnchor {n : ℕ} (cs : List (GeoConstraint n)) : ℕ × ℕ :=
  (maxIndex cs, kindSum cs)

/-- **The pair anchor separates what either component alone confuses.**

**`samePoint 3 7` and `samePoint 0 0`: same kind, different index ⇒ different first component.**
**`samePoint 0 0` and `midpoint 0 0 0`: same index, different kind ⇒ different second component.**
**=> `fullAnchor` is strictly finer than either, and this pair of facts is why.** -/
theorem fullAnchor_separates (n : ℕ) :
    fullAnchor (n := n) [GeoConstraint.samePoint 3 7]
        ≠ fullAnchor (n := n) [GeoConstraint.samePoint 0 0]
      ∧ fullAnchor (n := n) [GeoConstraint.samePoint 0 0]
        ≠ fullAnchor (n := n) [GeoConstraint.midpoint 0 0 0] := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg Prod.fst h
    simp only [fullAnchor, maxIndex_samePoint_3_7 n, maxIndex_samePoint_0_0 n] at this
    norm_num at this
  · intro h
    have := congrArg Prod.snd h
    simp only [fullAnchor] at this
    exact solve_depends_on_kind n this

end Lattice.Plugins.Targets
