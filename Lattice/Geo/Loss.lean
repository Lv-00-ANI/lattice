import Mathlib
import Lattice.Domains.Expr
import Lattice.Geo.Dist
import Lattice.Geo.Constraint
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Geo.Loss` -- from geometric constraints to a penalty loss

## The construction

Every constraint in the polynomial and square layers reduces to a polynomial `f` whose zero set is the
solution set, and the loss is `f²`. The reduction is per-constructor and explicit:

| constraint | polynomial `f` | why its zero set is the solution set |
|:--|:--|:--|
| `eqZero e` | `e` | by definition |
| `sqDistEq a b d` | `sqDist a b - d` | squares equal and both sides `≥ 0` |
| `samePoint a b` | `sqDist a b` | `sqDist = 0 → a = b` |
| `perpendicular a b c e` | `∑ᵢ segᵢ·segᵢ` | by definition |
| `collinear a b c` | *(not reduced)* | needs a quantifier over `t`; see below |
| `leZero` / `ltZero` | *(not reduced here)* | **covered instead by `Geo/PenaltyLoss.lean`**: `leZero` exactly via `(max e 0)²`, `ltZero` only as a relaxation |

## What this file does *not* claim

A "loss whose minimum is the solution set" is only meaningful for **equality** constraints. For an
inequality `f ≤ 0`, the natural penalty is `max f 0` squared or a hinge, which is differentiable but not
of the form `g²` with `g` polynomial. Rather than pretend otherwise, THIS FILE defines the loss only on the
equality layer, and `leZero`/`ltZero` are excluded by the type of its domain -- so the gap cannot be
silently skipped **here**.

⚠ **第 198 轮补上了那个缺口，在另一个文件里**：`Geo/PenaltyLoss.lean` 为**全部 12 个构造子**
定义了 `penaltyLoss`，含 `leZero`（用 `(max e 0)²`，零集**恰好**是 `e ≤ 0`，即精确）
与严格不等式（`(max e 0)²` 的零集是 `e ≤ 0`，比 `e < 0` **宽**，所以只是**松弛**）。
本文件仍是 `EqConstraint`（4 个构造子）的损失；两者服务不同层，**不是重复**。

`collinear` is excluded for a different reason: its statement is `∃ t, seg a b = t • seg a c`, and a
loss cannot be built from a quantifier without eliminating it first. The elimination
(`cross = 0` at `n = 2`) is a separate theorem, recorded as owed.

## Why `f²` rather than `|f|`

`f²` is polynomial, hence smooth, hence the Fermat condition applies. `|f|` is not differentiable at
`f = 0`. The price of using `f²` is that **every critical point of `f` becomes a critical point of `f²`**
-- which is exactly the hypothesis that `Lattice.Geo.Exact` will have to carry.

## A note on the namespace

`poly`, `loss` and the exactness theorems live in `namespace EqConstraint`, which shadows the *type*
`EqConstraint`. Inside that namespace the names resolve; from outside they do **not** resolve as
`EqConstraint.loss` (Lean treats the type name and the namespace name as different things). Modules that
need them therefore import this file and stay inside the same `namespace Lattice.Geo`, or restate the bridge
in terms of `eqToGeo` below. This was the source of an extended failure; see `Zero/Proofs/P72`.
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- The equality-layer constraints: those for which a squared-residual loss exists.

This is a separate inductive rather than a predicate on `GeoConstraint` so that "the loss is defined"
is a *type-level* fact. A predicate would let a caller pass `leZero` and get a junk value. -/
inductive EqConstraint (n : ℕ) : Type where
  /-- `e = 0`. -/
  | expr (e : GeoExpr n)
  /-- `sqDist a b = d`, i.e. the distance is `√d`. -/
  | distEq (a b : ℕ) (d : GeoExpr n)
  /-- The points coincide. -/
  | samePoint (a b : ℕ)
  /-- The segments `a b` and `c e` are perpendicular. -/
  | perpendicular (a b c e : ℕ)

namespace EqConstraint

/-- **The polynomial whose zero set is the solution set.**

Each case is the `f` from the table in the module docstring. -/
noncomputable def poly (c : EqConstraint n) (pts : ℕ → Pt n) : ℝ :=
  match c with
  | .expr e => e.evalPts pts
  | .distEq a b d => sqDist (n := n) (pts a) (pts b) - d.evalPts pts
  | .samePoint a b => sqDist (n := n) (pts a) (pts b)
  | .perpendicular a b c e =>
    ∑ i, (pts b i - pts a i) * (pts e i - pts c i)

/-- **The penalty loss**: the square of `poly`.

Non-negative by construction, and zero exactly where `poly` vanishes. -/
noncomputable def loss (c : EqConstraint n) (pts : ℕ → Pt n) : ℝ := poly c pts ^ 2

/-- The loss is non-negative. -/
theorem loss_nonneg (c : EqConstraint n) (pts : ℕ → Pt n) : 0 ≤ loss c pts :=
  sq_nonneg _

/-- **`expr` through the loss**: the penalty vanishes exactly when the expression evaluates to zero. -/
theorem loss_eq_zero_expr (e : GeoExpr n) (pts : ℕ → Pt n) :
    loss (.expr e) pts = 0 ↔ e.evalPts pts = 0 := by
  unfold loss poly
  exact pow_eq_zero_iff (n := 2) (by norm_num)

/-- **`distEq` through the loss**: the penalty vanishes exactly when the squared distance equals the
right-hand side.

`poly (.distEq a b d) = sqDist a b - d`, so this is again "a square is zero". -/
theorem loss_eq_zero_distEq (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    loss (.distEq a b d) pts = 0
      ↔ sqDist (n := n) (pts a) (pts b) - d.evalPts pts = 0 := by
  unfold loss poly
  exact pow_eq_zero_iff (n := 2) (by norm_num)

/-- **`perpendicular` through the loss**: the penalty vanishes exactly when the inner product is zero. -/
theorem loss_eq_zero_perpendicular (a b c e : ℕ) (pts : ℕ → Pt n) :
    loss (.perpendicular a b c e) pts = 0
      ↔ ∑ i, (pts b i - pts a i) * (pts e i - pts c i) = 0 := by
  unfold loss poly
  exact pow_eq_zero_iff (n := 2) (by norm_num)

/-- **`samePoint` through the loss**: the penalty vanishes exactly when the two points coincide.

`poly (.samePoint a b) = sqDist a b = ∑ᵢ (aᵢ - bᵢ)²`, so this needs the characterisation of a vanishing
**sum** of squares rather than of a single square. Each summand is non-negative, so the sum vanishes only
if every summand does, and a vanishing square is a vanishing base. -/
theorem loss_eq_zero_samePoint (a b : ℕ) (pts : ℕ → Pt n) :
    loss (.samePoint a b) pts = 0 ↔ pts a = pts b := by
  unfold loss poly sqDist sqNorm diff
  rw [pow_eq_zero_iff (n := 2) (by norm_num)]
  constructor
  · intro h
    funext i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (pts a j - pts b j) ^ 2 :=
      fun j _ => sq_nonneg _
    have hi : (pts a i - pts b i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    have h0 : pts a i - pts b i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
    linarith
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h]
    ring

end EqConstraint

/-! ## Embedding `EqConstraint` into `GeoConstraint`

`EqConstraint` has no `Holds` of its own: its exactness theorems relate `loss` to a semantic condition
stated inline. `GeoConstraint` does have `Holds`, and the IR bridge compiles into it, so the two need a
bridge. `eqToGeo` sends each equality constraint to the `GeoConstraint` with the same meaning, and the
`loss_eq_zero_toGeo_*` theorems record that the loss decides the embedded constraint.

Note the naming: `eqToGeo` lives in `Lattice.Geo` (not in `EqConstraint`), because a definition inside the
namespace named after a type is not reachable from outside by either spelling. -/

/-- **The equality fragment sits inside the full constraint language.** -/
def eqToGeo : EqConstraint n → GeoConstraint n
  | .expr e => .eqZero e
  | .distEq a b d => .sqDistEq a b d
  | .samePoint a b => .samePoint a b
  | .perpendicular a b c e => .perpendicular a b c e

/-- **`loss` decides the embedded constraint**, `expr` branch. -/
theorem loss_eq_zero_toGeo_expr (e : GeoExpr n) (pts : ℕ → Pt n) :
    EqConstraint.loss (.expr e) pts = 0 ↔ GeoConstraint.Holds (.eqZero e) pts :=
  EqConstraint.loss_eq_zero_expr e pts

/-- **`loss` decides the embedded constraint**, `distEq` branch. -/
theorem loss_eq_zero_toGeo_distEq (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    EqConstraint.loss (.distEq a b d) pts = 0 ↔ GeoConstraint.Holds (.sqDistEq a b d) pts := by
  rw [EqConstraint.loss_eq_zero_distEq]
  exact sub_eq_zero

/-- **`loss` decides the embedded constraint**, `samePoint` branch. -/
theorem loss_eq_zero_toGeo_samePoint (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) pts = 0 ↔ GeoConstraint.Holds (.samePoint a b) pts :=
  EqConstraint.loss_eq_zero_samePoint a b pts

/-- **`loss` decides the embedded constraint**, `perpendicular` branch. -/
theorem loss_eq_zero_toGeo_perpendicular (a b c e : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.perpendicular a b c e) pts = 0
      ↔ GeoConstraint.Holds (.perpendicular a b c e) pts := by
  rw [EqConstraint.loss_eq_zero_perpendicular]
  rfl

/-- **The general statement**: `loss` vanishes exactly when the embedded constraint is satisfied.

Stated by cases so that the four theorems above are its instances; a caller holding an arbitrary
`EqConstraint` uses this one. -/
theorem loss_eq_zero_toGeo (c : EqConstraint n) (pts : ℕ → Pt n) :
    EqConstraint.loss c pts = 0 ↔ GeoConstraint.Holds (eqToGeo c) pts := by
  cases c with
  | expr e => exact loss_eq_zero_toGeo_expr e pts
  | distEq a b d => exact loss_eq_zero_toGeo_distEq a b d pts
  | samePoint a b => exact loss_eq_zero_toGeo_samePoint a b pts
  | perpendicular a b c e => exact loss_eq_zero_toGeo_perpendicular a b c e pts

end Lattice.Geo
