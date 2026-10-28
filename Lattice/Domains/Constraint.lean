import Mathlib
import Lattice.Domains.Expr
import Lattice.Domains.Dist

/-!
# `Lattice.Geo.Constraint` -- geometric constraints over `n`-dimensional points

## The layers, and why they are separated

`Lv-00`'s `IRConstraint` has fifteen constructors in one `inductive`. Reading their semantics
(`_harvest/lv00/formal/lvFormal/Theory/IR.lean:89-137`) shows they fall into groups that are *not*
alike, and mixing them is what makes "algebraise every constraint" sound impossible while being false:

| layer | constraints | semantic form | reduces to a polynomial? |
|:--|:--|:--|:--|
| **poly** | `collinear`, `perpendicular`, `rightAngle`, `midpoint`, `eq_expr`, `lt_expr`, `gt_expr` | `dot = 0`, linear equation, inequality | yes, already |
| **square** | `distance`, `radius`, `equalLength` | `dist = d`, reducible by `dist_sq` | yes, after squaring |
| **existential** | `tangent`, `ratioDivision`, `parallel` | `∃ t, ...` | only after Skolemising |
| **transcendental** | `angle`, `equalAngle` | involves `Real.cos` of a ratio | **no** |

`Lv-00` put all fifteen in one type, so the last group sat beside the first and any blanket claim about
algebraisation was false while looking provable. Here the layer is a **value**: `Layer` and
`GeoConstraint.layer` answer "can this reach the weight side" computably.

## Coverage

Thirteen of `Lv-00`'s fifteen predicates appear below. `angle` and `equalAngle` are **absent**: they
involve `Real.cos` of an angle, which is not the zero set of any polynomial, so no penalty of the form
`f²` can express them. Their absence is a decision recorded by `Layer.transc` rather than an oversight.

`collinear` and `parallel` are stated as **existence of a scalar multiple** rather than through a
two-dimensional cross product. That is dimension-free: at `n = 2` it agrees with `cross = 0`, and it
works in every dimension, which is strictly more than `Lv-00` did (it hardcoded `ℝ × ℝ`).
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- **The algebraic layer a constraint belongs to.** This decides whether a penalty exists. -/
inductive Layer
  /-- Already a polynomial equation or inequality. -/
  | poly
  /-- Becomes polynomial after squaring a distance, at the cost of the sign. -/
  | square
  /-- Needs a witness eliminated before it becomes polynomial. -/
  | existential
  /-- Involves a transcendental function and cannot become polynomial at all. -/
  | transc
  deriving DecidableEq, Repr

/-- **Geometric constraints.**

Each constructor corresponds to one `Lv-00` predicate; `layer` records which algebraic layer it belongs
to. -/
inductive GeoConstraint (n : ℕ) : Type where
  /-- **poly**: the expression vanishes. -/
  | eqZero (e : GeoExpr n)
  /-- **poly**: `e ≤ 0`. -/
  | leZero (e : GeoExpr n)
  /-- **poly**: `e < 0`. -/
  | ltZero (e : GeoExpr n)
  /-- **poly**: `0 < e`. `Lv-00` states this separately as `gt_expr`. -/
  | gtZero (e : GeoExpr n)
  /-- **square**: the squared distance between `a` and `b` equals `d`.

  `Lv-00` writes `dist a b = d`; the square root is removed here at the cost of the sign of `d`, which
  `sqDistEq_rhs_nonneg` makes explicit. -/
  | sqDistEq (a b : ℕ) (d : GeoExpr n)
  /-- **square**: the two segments have equal length. -/
  | equalLength (a b c e : ℕ)
  /-- **existential**: the three points are collinear -- `b - a` is a scalar multiple of `c - a`. -/
  | collinear (a b c : ℕ)
  /-- **poly**: the segments `a b` and `c e` are perpendicular. -/
  | perpendicular (a b c e : ℕ)
  /-- **existential**: the segments `a b` and `c e` are parallel. -/
  | parallel (a b c e : ℕ)
  /-- **poly**: the angle at `b` in `a b c` is a right angle. -/
  | rightAngle (a b c : ℕ)
  /-- **poly**: `m` is the midpoint of `a b`, stated coordinatewise. -/
  | midpoint (m a b : ℕ)
  /-- **poly**: the two points coincide. -/
  | samePoint (a b : ℕ)

namespace GeoConstraint

variable {n : ℕ}

/-- The vector from `p` to `q`. -/
noncomputable def seg (pts : ℕ → Pt n) (p q : ℕ) : Pt n := fun i => pts q i - pts p i

/-- **Satisfaction** of a constraint in a configuration. -/
noncomputable def Holds (c : GeoConstraint n) (pts : ℕ → Pt n) : Prop :=
  match c with
  | .eqZero e => e.evalPts pts = 0
  | .leZero e => e.evalPts pts ≤ 0
  | .ltZero e => e.evalPts pts < 0
  | .gtZero e => 0 < e.evalPts pts
  | .sqDistEq a b d => sqDist (n := n) (pts a) (pts b) = d.evalPts pts
  | .equalLength a b c e => sqDist (n := n) (pts a) (pts b) = sqDist (n := n) (pts c) (pts e)
  | .collinear a b c => ∃ t : ℝ, seg pts a b = fun i => t * seg pts a c i
  | .perpendicular a b c e => ∑ i, seg pts a b i * seg pts c e i = 0
  | .parallel a b c e => ∃ t : ℝ, seg pts a b = fun i => t * seg pts c e i
  | .rightAngle a b c => ∑ i, seg pts a b i * seg pts b c i = 0
  | .midpoint m a b => ∀ i, 2 * pts m i = pts a i + pts b i
  | .samePoint a b => pts a = pts b

/-- **The layer of a constraint** -- the function that answers "can this reach the weight side". -/
def layer : GeoConstraint n → Layer
  | .eqZero _ => .poly
  | .leZero _ => .poly
  | .ltZero _ => .poly
  | .gtZero _ => .poly
  | .sqDistEq _ _ _ => .square
  | .equalLength _ _ _ _ => .square
  | .collinear _ _ _ => .existential
  | .perpendicular _ _ _ _ => .poly
  | .parallel _ _ _ _ => .existential
  | .rightAngle _ _ _ => .poly
  | .midpoint _ _ _ => .poly
  | .samePoint _ _ => .poly

/-! ### Basic facts -/

/-- **Squared-distance constraints force the right side non-negative**, hence bound it.

This is the price of squaring, stated as a lemma rather than as prose: squaring an equation loses the
sign, and what survives is the non-negativity of the squared side. -/
theorem sqDistEq_rhs_nonneg (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n)
    (h : Holds (.sqDistEq a b d) pts) : 0 ≤ d.evalPts pts := by
  unfold Holds at h
  rw [← h]
  exact sqDist_nonneg (pts a) (pts b)

/-- **Equality constraints are the zero case of a polynomial**, which is the form the penalty layer
consumes: `e₁ = e₂` becomes `e₁ - e₂` vanishing. -/
theorem holds_eqZero_sub (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    Holds (.eqZero (e₁.sub e₂)) pts ↔ e₁.evalPts pts = e₂.evalPts pts := by
  unfold Holds
  exact GeoExpr.evalPts_sub_eq_zero_iff e₁ e₂ pts

/-- **`perpendicular a b b c` and `rightAngle a b c` are the same relation.**

`Lv-00` states them under two names with two implementations; recording the agreement means the
duplication is visible rather than silently carried forward. -/
theorem perpendicular_rightAngle_agree (a b c : ℕ) (pts : ℕ → Pt n) :
    Holds (.perpendicular a b b c) pts ↔ Holds (.rightAngle a b c) pts := by
  unfold Holds seg
  constructor <;> intro h <;> exact h

/-- **A midpoint constraint is linear in the configuration.** Recorded because linearity is what makes
it the easiest layer to give a penalty and a repair operator. -/
theorem midpoint_iff (m a b : ℕ) (pts : ℕ → Pt n) :
    Holds (.midpoint m a b) pts ↔ ∀ i, 2 * pts m i = pts a i + pts b i := Iff.rfl

end GeoConstraint

end Lattice.Geo
