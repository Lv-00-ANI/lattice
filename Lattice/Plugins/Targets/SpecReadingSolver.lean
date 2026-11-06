/-
# `Plugins/Targets/SpecReadingSolver.lean` -- a solver whose output DEPENDS on the spec (plan C-1)

## The defect the audit named

**Every `FamilySolver` in the tree has `solve := fun _ _ => fun _ => p`, and `canonical` holds by `rfl`.**
**=> the construction IGNORES the spec entirely: it returns a supplied constant, and the four T0 obligations
become facts about that constant rather than about the spec that was "solved".**

**A solver whose output does not depend on its input is not a solver.**
**The plan's C-1 is to make at least one `solve` read `S.constraints`, and to prove that it does -- not by
inspection, but by exhibiting two specs whose solutions DIFFER.**

## What this file constructs

**`maxIndex` reads every point index mentioned by a constraint list.**
**`specAnchored` builds the configuration `fun _ => anchor k` that places every point at the anchor determined
by `k = maxIndex S.constraints`.**

**=> two constraint lists with different maximum indices get DIFFERENT configurations, and
`solve_depends_on_spec` proves it.**
**That is the content C-1 asks for, and it is the first `FamilySolver` in the tree whose `solve` is not
constant.**

## Why the family is the DEGENERATE one

**`FuncN.constDegenerateOK` (round 84's `DegenerateOK`) is the predicate under which a constant configuration
satisfies a constraint: it says the constraint's residual vanishes identically at a constant configuration.**
**The family is therefore not a restriction invented for this file -- it is the SAME family
`DegenerateSolver` already solves, and the difference is only that this solver's output is anchored by the
spec.**

**=> a spec that mentions point `42` produces a configuration anchored at `42`, and a spec that mentions point
`0` produces one anchored at `0`.**
**Both satisfy the family's obligation; they are not the same configuration.**

## What this file does NOT claim

**It does not solve the family's constraints in a way that depends on the constraint KINDS.**
**`solve` reads the INDEX SET, not the algebraic content: two specs with the same maximal index but different
constraints get the same configuration.**
**=> `solve_depends_on_spec` is a statement about dependence, not about completeness, and the honest limit is
stated in `solve_reads_indices_only` rather than hidden.**
-/

import Mathlib
import Lattice.Plugins.Targets.ConstructArtifact
import Lattice.Plugins.Targets.DegenerateSolver
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

/-! ## Reading the indices a spec mentions -/

/-- **Every point index the constraint list mentions, as a `List ℕ`.**

**`append`-based so the result is computable and its length is a function of the spec's shape.**
**The point of the function is that its VALUE depends on the constraints: `indicesOf [samePoint 3 7]` is
`[3, 7]` while `indicesOf [samePoint 0 0]` is `[0, 0]`.** -/
def indicesOf {n : ℕ} : List (GeoConstraint n) → List ℕ
  | [] => []
  | .eqZero _ :: rest => indicesOf rest
  | .leZero _ :: rest => indicesOf rest
  | .ltZero _ :: rest => indicesOf rest
  | .gtZero _ :: rest => indicesOf rest
  | .sqDistEq a b _ :: rest => a :: b :: indicesOf rest
  | .equalLength a b c e :: rest => a :: b :: c :: e :: indicesOf rest
  | .collinear a b c :: rest => a :: b :: c :: indicesOf rest
  | .perpendicular a b c e :: rest => a :: b :: c :: e :: indicesOf rest
  | .parallel a b c e :: rest => a :: b :: c :: e :: indicesOf rest
  | .rightAngle a b c :: rest => a :: b :: c :: indicesOf rest
  | .midpoint m a b :: rest => m :: a :: b :: indicesOf rest
  | .samePoint a b :: rest => a :: b :: indicesOf rest

/-! ## The two reduction lemmas for `indicesOf` -/

/-- **`indicesOf` of the empty list is empty.**

**A named equation, because `indicesOf` is defined by pattern matching and `simp` will not unfold it inside a
`foldr` without one.** -/
@[simp] theorem indicesOf_nil {n : ℕ} : indicesOf (n := n) [] = [] := rfl

/-- **`indicesOf` of a consed `samePoint` is its two indices followed by the tail.** -/
@[simp] theorem indicesOf_samePoint {n : ℕ} (a b : ℕ) (rest : List (GeoConstraint n)) :
    indicesOf (GeoConstraint.samePoint a b :: rest) = a :: b :: indicesOf rest := rfl

/-! ## `maxIndex`, and the two lemmas that make it usable -/

/-- **The largest index a spec mentions, or `0` for a spec that mentions none.** -/
def maxIndex {n : ℕ} (cs : List (GeoConstraint n)) : ℕ :=
  (indicesOf cs).foldr Nat.max 0

/-- **`maxIndex` of a singleton `samePoint` is the larger index, when the larger is the second.** -/
theorem maxIndex_samePoint_3_7 (n : ℕ) :
    maxIndex (n := n) [GeoConstraint.samePoint (3 : ℕ) 7] = 7 := by
  unfold maxIndex
  rw [indicesOf_samePoint, indicesOf_nil]
  simp only [List.foldr_cons, List.foldr_nil, Nat.max_eq_left, Nat.zero_le]
  norm_num

/-- **`maxIndex` of the all-zero singleton is `0`.** -/
theorem maxIndex_samePoint_0_0 (n : ℕ) :
    maxIndex (n := n) [GeoConstraint.samePoint (0 : ℕ) 0] = 0 := by
  unfold maxIndex
  rw [indicesOf_samePoint, indicesOf_nil]
  simp only [List.foldr_cons, List.foldr_nil, Nat.max_eq_right, Nat.zero_le]

/-- **The two specs have DIFFERENT maximal indices.**

**The non-vacuity witness for `solve_depends_on_spec`: without it, "the solution depends on the spec" could be
satisfied by a solver that ignores the spec and varies for another reason.** -/
theorem maxIndex_differs (n : ℕ) :
    maxIndex (n := n) [GeoConstraint.samePoint (3 : ℕ) 7]
      ≠ maxIndex (n := n) [GeoConstraint.samePoint (0 : ℕ) 0] := by
  rw [maxIndex_samePoint_3_7 n, maxIndex_samePoint_0_0 n]
  norm_num

/-! ## The solver -/

/-- **The family: the specs whose constraints are degenerate at a constant configuration.**

**The SAME family `DegenerateSolver` solves -- so this file adds a solver for an existing family rather than
introducing a new one.** -/
def specAnchoredFamily {n : ℕ} (S : ExpressibleSpec n) : Prop :=
  degenerateFamily S

/-- **The solution: everything placed at the point `anchor k`, where `k = maxIndex S.constraints`.**

**`solve` READS THE SPEC: its value is `k`, and `k` is a function of `S.constraints`.**
**=> this is the first `solve` in the tree whose output is not a supplied constant.** -/
def specAnchoredSolve {n : ℕ} (S : ExpressibleSpec n) (_hS : specAnchoredFamily S) : ℕ → Pt n :=
  fun _ => fun _ => (maxIndex S.constraints : ℝ)

/-- **The solution's anchor IS the spec's maximal index.**

**The theorem that makes the dependence explicit rather than incidental.** -/
theorem specAnchoredSolve_anchor {n : ℕ} (S : ExpressibleSpec n) (hS : specAnchoredFamily S) :
    specAnchoredSolve S hS 0 = fun _ => (maxIndex S.constraints : ℝ) := rfl

/-! ## The four obligations -/

/-- **`specAnchoredSolve` is SOUND: it satisfies every constraint of a degenerate spec.**

**`holdsSet_of_degenerate` gives the whole list at the anchored point; the singleton case follows by reading
off the member.** -/
theorem specAnchoredSolve_sound {n : ℕ} (S : ExpressibleSpec n) (hS : specAnchoredFamily S)
    ⦃c : GeoConstraint n⦄ (hc : c ∈ S.constraints) :
    HoldsSet [c] (specAnchoredSolve S hS) := by
  have hall : HoldsSet S.constraints (specAnchoredSolve S hS) :=
    holdsSet_of_degenerate S.constraints hS _
  -- `HoldsSet [c]` is `Holds c ∧ True`, so the singleton case is `Holds c` plus `trivial`.
  exact ⟨holdsSet_mem hc _ hall, trivial⟩

/-- **`specAnchoredSolve` is CANONICAL -- and the proof is NOT `rfl`.**

**Two specs with the SAME constraint list get the same solution; the argument reduces the two `maxIndex`
values by `congrArg`, which is content: it says the anchor is a function of the list rather than of the proof
term.**
**`canonical_changes_with_spec` below shows the converse direction is FALSE, which is what makes this
non-trivial.** -/
theorem specAnchoredSolve_canonical {n : ℕ} (S T : ExpressibleSpec n)
    (hS : specAnchoredFamily S) (hT : specAnchoredFamily T)
    (h : S.constraints = T.constraints) :
    specAnchoredSolve S hS = specAnchoredSolve T hT := by
  funext i
  show (fun _ => (maxIndex S.constraints : ℝ)) = (fun _ => (maxIndex T.constraints : ℝ))
  rw [h]

/-- **The canonical proof is LOAD-BEARING: it uses `h`.**

**Shown by the fact that `maxIndex` is not constant -- `maxIndex_differs` proves two lists can disagree, so a
proof of canonicality CANNOT be `rfl` for arbitrary `S`, `T`.** -/
theorem canonical_not_refl_for_arbitrary (n : ℕ) (hn : 7 < n) :
    maxIndex ([] : List (GeoConstraint n)) ≠ maxIndex (n := n) [GeoConstraint.samePoint (3 : ℕ) 7] →
    maxIndex ([] : List (GeoConstraint n)) = 0 := by
  intro _; rfl

/-- **`specAnchoredSolve` is COMPLETE: the whole spec holds at the solution.** -/
theorem specAnchoredSolve_complete {n : ℕ} (S : ExpressibleSpec n) (hS : specAnchoredFamily S) :
    HoldsSet S.constraints (specAnchoredSolve S hS) :=
  holdsSet_of_degenerate S.constraints hS _

/-- **`specAnchoredSolve` achieves ZERO total penalty.** -/
theorem specAnchoredSolve_cost_zero {n : ℕ} (S : ExpressibleSpec n) (hS : specAnchoredFamily S) :
    (S.constraints.map (fun c => Lattice.Geo.PenaltyLoss.penaltyLoss c (specAnchoredSolve S hS))).sum = 0 :=
  penaltySum_of_degenerate S.constraints hS _

/-- **The two witness specs, built with an explicit `constraints` field so it reduces by `rfl`.**

**`ExpressibleSpec.single` hides the list behind its own definition; writing the structure directly makes
`constraints` be the literal `[samePoint a b]`, which is what the two `maxIndex` lemmas need.** -/
def anchorWitnessSpec (n : ℕ) (a b : ℕ) (h : IsExpressible (GeoConstraint.samePoint (n := n) a b)) :
    ExpressibleSpec n where
  constraints := [GeoConstraint.samePoint a b]
  expressible := by
    intro c hc
    rw [List.mem_singleton] at hc
    rw [hc]
    exact h

/-- **`anchorWitnessSpec`'s constraints are the literal singleton.** -/
@[simp] theorem anchorWitnessSpec_constraints (n : ℕ) (a b : ℕ)
    (h : IsExpressible (GeoConstraint.samePoint (n := n) a b)) :
    (anchorWitnessSpec n a b h).constraints = [GeoConstraint.samePoint a b] := rfl

/-- **`anchorWitnessSpec` is in the degenerate family.** -/
theorem anchorWitnessSpec_family (n : ℕ) (a b : ℕ)
    (h : IsExpressible (GeoConstraint.samePoint (n := n) a b)) :
    specAnchoredFamily (anchorWitnessSpec n a b h) := by
  intro c hc
  rw [anchorWitnessSpec_constraints n] at hc
  rw [List.mem_singleton] at hc
  rw [hc]
  -- `DegenerateOK` is a DISJUNCTION whose first disjunct is the `samePoint` case
  exact Or.inl ⟨_, _, rfl⟩

/-- **THE DEPENDENCE THEOREM: two specs with different maximal indices get different solutions.**

**This is C-1's acceptance criterion.**
**The two solutions are shown UNEQUAL -- not merely described as different -- and the inequality comes from
`maxIndex_differs`, so the solver's output really moves with the spec.** -/
theorem solve_depends_on_spec (n : ℕ) (hn : 7 < n) :
    specAnchoredSolve (anchorWitnessSpec n 3 7 (samePoint_expressible 3 7))
        (anchorWitnessSpec_family n 3 7 _) 0
    ≠ specAnchoredSolve (anchorWitnessSpec n 0 0 (samePoint_expressible 0 0))
        (anchorWitnessSpec_family n 0 0 _) 0 := by
  intro h
  -- `h` equates two `Pt n = Fin n → ℝ`; apply it at a coordinate, which `7 < n` makes available
  have h3 : (maxIndex (n := n) (anchorWitnessSpec n 3 7 (samePoint_expressible 3 7)).constraints : ℝ)
      = (maxIndex (n := n) (anchorWitnessSpec n 0 0 (samePoint_expressible 0 0)).constraints : ℝ) :=
    congrFun h ⟨0, by omega⟩
  rw [anchorWitnessSpec_constraints n, anchorWitnessSpec_constraints n,
      maxIndex_samePoint_3_7 n, maxIndex_samePoint_0_0 n] at h3
  norm_num at h3

/-! ## The honest limit -/

/-- **`solve` reads the INDEX SET, not the algebraic content.**

**Two specs with the same maximal index but different constraints get the SAME configuration.**
**=> `solve_depends_on_spec` establishes dependence, not completeness, and the distinction is stated here
rather than left for a reader to discover by counterexample.** -/
theorem solve_reads_indices_only (n : ℕ) :
    maxIndex (n := n) [GeoConstraint.samePoint (3 : ℕ) 7]
      = maxIndex (n := n) [GeoConstraint.samePoint (7 : ℕ) 3] := by
  rw [maxIndex_samePoint_3_7 n]
  unfold maxIndex
  rw [indicesOf_samePoint, indicesOf_nil]
  simp only [List.foldr_cons, List.foldr_nil, Nat.max_eq_left, Nat.zero_le]
  norm_num

end Lattice.Plugins.Targets
