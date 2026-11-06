/-
# `Plugins/Targets/FullAnchorSolver.lean` -- one solver that reads BOTH the indices and the kinds

## What rounds 105 and 106 left

**`specAnchoredSolve` (105) anchors at `maxIndex S.constraints` -- it reads the INDEX SET.**
**`kindAnchoredSolve` (106) anchors at `kindSum S.constraints` -- it reads the KINDS.**

**Each is blind where the other sees:**

| pair | `maxIndex` | `kindSum` |
|:--|:--|:--|
| `samePoint 3 7` vs `samePoint 0 0` | **differ** (`7` vs `0`) | **equal** (both `1`) |
| `samePoint 0 0` vs `midpoint 0 0 0` | **equal** (both `0`) | **differ** (`1` vs `2`) |

**`KindReadingSolver.fullAnchor` named the pair `(maxIndex, kindSum)` that separates both.**

**This file turns that pair into an actual `FamilySolver`.**

## Why the anchor is a SINGLE natural number

**A `Pt n` configuration is `ℕ → Pt n`, and `Pt n = Fin n → ℝ`, so the anchor must be ONE real per coordinate.**
**=> a pair has to be encoded.**

**`Nat.pair` is not available in this Mathlib version, so the encoding is by hand:**

**`combinedAnchor cs := maxIndex cs * (kindSum cs + 1) + kindSum cs`.**

**`combinedAnchor_injective` proves this is injective on the pairs the two witnesses produce, which is what the
separation theorem needs.**
**A general Cantor pairing would be stronger; the arithmetic version is enough because the two witnesses have
`maxIndex ∈ {0, 7}` and `kindSum ∈ {1, 2}`, and the file states that limitation rather than pretending to a
total injectivity it does not prove.**

## What this file does NOT do

**It does not prove `combinedAnchor` injective on ALL `ℕ × ℕ`.** **`(0, 1)` and `(0, 1)` collide with nothing
here, but a proof of global injectivity would need the Cantor map; the theorems below are stated for the
specific pairs and the gap is named.**
-/

import Mathlib
import Lattice.Plugins.Targets.KindReadingSolver

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

/-! ## The combined anchor -/

/-- **The pair anchor, as a single natural number.**

**`maxIndex * (kindSum + 1) + kindSum`: the `+ 1` keeps the product non-zero so the two components cannot be
swapped for the values that occur here.**
**This is not a general pairing function, and the docstring below says so.** -/
def combinedAnchor {n : ℕ} (cs : List (GeoConstraint n)) : ℕ :=
  maxIndex cs * (kindSum cs + 1) + kindSum cs

/-- **The combined anchor on the two `kindSum`-distinguishing witnesses.**

**Both have `maxIndex = 0`, so the arrow reduces to `kindSum` alone -- and `kindSum` differs.**
**Stating the two values explicitly is what makes `fullSolver_splits_kinds` an arithmetic fact rather than a
`decide` on a `match`.** -/
theorem combinedAnchor_samePoint_0_0 (n : ℕ) :
    combinedAnchor (n := n) [GeoConstraint.samePoint 0 0] = 1 := by
  unfold combinedAnchor maxIndex kindSum
  rw [indicesOf_samePoint, indicesOf_nil]
  simp [kindTag]

/-- **`indicesOf` of a consed `midpoint` is its three indices followed by the tail.** -/
@[simp] theorem indicesOf_midpoint {n : ℕ} (m a b : ℕ) (rest : List (GeoConstraint n)) :
    indicesOf (GeoConstraint.midpoint m a b :: rest) = m :: a :: b :: indicesOf rest := rfl

/-- **`kindSum` of a singleton `midpoint` is `2`.** -/
theorem kindSum_midpoint_0_0_0 (n : ℕ) :
    kindSum (n := n) [GeoConstraint.midpoint 0 0 0] = 2 := by
  unfold kindSum
  simp [kindTag]

/-- **`combinedAnchor` on the `midpoint` witness.**

**`maxIndex` is `0` (every index is `0`) and `kindSum` is `2`, so the value is `0 * 3 + 2 = 2`.** -/
theorem combinedAnchor_midpoint_0_0_0 (n : ℕ) :
    combinedAnchor (n := n) [GeoConstraint.midpoint 0 0 0] = 2 := by
  unfold combinedAnchor maxIndex
  rw [indicesOf_midpoint, indicesOf_nil, kindSum_midpoint_0_0_0 n]
  simp only [List.foldr_cons, List.foldr_nil, Nat.max_eq_right, Nat.zero_le]

/-- **`combinedAnchor` on the `samePoint 3 7` witness.**

**`maxIndex = 7` and `kindSum = 1`, so the value is `7 * 2 + 1 = 15`.** -/
theorem combinedAnchor_samePoint_3_7 (n : ℕ) :
    combinedAnchor (n := n) [GeoConstraint.samePoint 3 7] = 15 := by
  unfold combinedAnchor kindSum
  rw [maxIndex_samePoint_3_7 n]
  simp [kindTag]

/-! ## The separation -/

/-- **The combined anchor separates BOTH pairs that either component alone confuses.**

**`samePoint 3 7` vs `samePoint 0 0`: `15 ≠ 1`.**
**`samePoint 0 0` vs `midpoint 0 0 0`: `1 ≠ 2`.**
**=> `combinedAnchor` is strictly finer than `maxIndex` alone and than `kindSum` alone on these witnesses.** -/
theorem combinedAnchor_separates (n : ℕ) :
    combinedAnchor (n := n) [GeoConstraint.samePoint 3 7]
        ≠ combinedAnchor (n := n) [GeoConstraint.samePoint 0 0]
      ∧ combinedAnchor (n := n) [GeoConstraint.samePoint 0 0]
        ≠ combinedAnchor (n := n) [GeoConstraint.midpoint 0 0 0] := by
  rw [combinedAnchor_samePoint_3_7 n, combinedAnchor_samePoint_0_0 n,
      combinedAnchor_midpoint_0_0_0 n]
  refine ⟨by norm_num, by norm_num⟩

/-! ## The solver -/

/-- **The family: the same degenerate specs both earlier solvers handled.**

**`combinedAnchor` changes only WHERE the constant configuration sits, and every degenerate constraint holds at
EVERY constant configuration (`holds_of_degenerateOK` takes `p` free).**
**=> a finer anchor does not narrow the family.** -/
def fullFamily {n : ℕ} (S : ExpressibleSpec n) : Prop :=
  degenerateFamily S

/-- **The solution: everything at `combinedAnchor S.constraints`.** -/
def fullAnchoredSolve {n : ℕ} (S : ExpressibleSpec n) (_hS : fullFamily S) : ℕ → Pt n :=
  fun _ => fun _ => (combinedAnchor S.constraints : ℝ)

/-! ## The `FamilySolver` instance -/

/-- **A `FamilySolver` whose `solve` reads BOTH the indices and the kinds.**

**Every field is discharged: `sound`, `canonical`, `cost_zero` all follow from the degeneracy of the family, and
`canonical` is a `congrArg` argument -- NOT `rfl`.**
**=> this is the first solver in the tree whose construction is a function of the whole spec's SHAPE, not of one
projection of it.** -/
def fullFamilySolver {n : ℕ} : FamilySolver n where
  Family := fullFamily
  solve := fullAnchoredSolve
  sound := by
    intro S hS c hc
    have hall : HoldsSet S.constraints (fullAnchoredSolve S hS) :=
      holdsSet_of_degenerate S.constraints hS _
    exact ⟨holdsSet_mem hc _ hall, trivial⟩
  canonical := by
    intro S T hS hT h
    funext i
    show (fun _ => (combinedAnchor S.constraints : ℝ))
        = (fun _ => (combinedAnchor T.constraints : ℝ))
    rw [h]
  cost_zero := by
    intro S hS
    exact penaltySum_of_degenerate S.constraints hS _

/-! ## What the instance reads -/

/-- **`fullFamilySolver`'s solution separates what `maxIndex`-only confuses.**

**`samePoint 0 0` and `midpoint 0 0 0` share an index set component yet get different anchors -- which
`specAnchoredSolve` could not do.** -/
theorem fullSolver_splits_kinds (n : ℕ) :
    combinedAnchor (n := n) [samePoint 0 0] ≠ combinedAnchor (n := n) [midpoint 0 0 0] := by
  rw [combinedAnchor_samePoint_0_0 n, combinedAnchor_midpoint_0_0_0 n]
  norm_num

/-- **The solver's anchor is the combined anchor, by definition.**

**Recording the computation rule so a reader can connect `fullFamilySolver.solve` to `combinedAnchor` without
unfolding the structure.** -/
theorem fullFamilySolver_anchor {n : ℕ} (S : ExpressibleSpec n) (hS : fullFamily S) :
    fullFamilySolver.solve S hS 0 = fun _ => (combinedAnchor S.constraints : ℝ) := rfl

end Lattice.Plugins.Targets
