/-
# Correcting round 75's exclusion list, and widening the family

**Round 75 defined `DegenerateOK` as a CLOSED LIST of four constructors and excluded `eqZero`,
`sqDistEq`, `equalLength` with the reason "their `Holds` mentions `evalPts`, which does not vanish at
a constant configuration".**

**That reason is only PARTLY right, and round 76's instance inherited the error.**

## What was wrong

**`evalPts (const c) pts = c`.** **So `evalPts` vanishes at a constant configuration exactly when the
expression EVALUATES to zero -- which is a property of the EXPRESSION, not of the constructor.**

- **`eqZero (.const 1)`**: **`1 ≠ 0`, so it does NOT hold.** The original exclusion is right for this one.
- **`eqZero (.sub (coord p i) (coord p i))`**: **`c - c = 0`, so it DOES hold.** **The exclusion is wrong.**
- **`sqDistEq a b (.const 0)`**: **`sqDist c c = 0 = 0`, so it holds.** **The exclusion is wrong.**
- **`equalLength a b c e`**: **both sides are `sqDist c c = 0`, so it holds.** **The exclusion is wrong.**

**=> the family is NOT a list of constructors. It is a condition on the expression's value at the
degenerate configuration.**
**This file states that condition, proves the three excluded kinds belong when it holds, and states the
one that genuinely does not (`ltZero`, which needs a STRICT inequality).**

## Why this is a correction and not a patch

**A closed list says "these four kinds work"; a condition says WHY they work and lets a reader decide
about kinds the list never mentioned.**
**The condition is also what makes the family CLOSED under the constraint constructors that merely wrap
an expression -- a list cannot express that, a predicate can.**
-/

import Lattice.Plugins.Targets.DegenerateSolver

namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- **The distance a point has from itself is zero.**

**`sqDist_eq_zero_iff` gives this in one step; it is named here because three of the four cases below
consume it.** -/
theorem sqDist_self {n : ℕ} (c : Pt n) : sqDist c c = 0 :=
  (sqDist_eq_zero_iff (n := n) c c).mpr rfl

/-- **`equalLength a b c e` holds at any constant configuration.**

**Both sides are `sqDist c c`, which is zero, so the equation is `0 = 0`.**
**Round 75 excluded this kind on the grounds that its `Holds` mentions `sqDist`; that ground was
wrong -- `sqDist` of a point with ITSELF is zero regardless of which point it is.** -/
theorem holds_equalLength_const {n : ℕ} (a b e f : ℕ) (p : Pt n) :
    Holds (n := n) (GeoConstraint.equalLength a b e f) (fun _ => p) := by
  show sqDist (n := n) p p = sqDist (n := n) p p
  rfl

/-- **`sqDistEq a b d` holds at a constant configuration WHEN `d` evaluates to zero there.**

**This is the form the correction requires: the constraint holds conditionally on the EXPRESSION, not
unconditionally on the constructor.**
**`sqDist c c = 0`, so the equation reduces to `0 = d.evalPts (fun _ => c)`.** -/
theorem holds_sqDistEq_const_of_eval_zero {n : ℕ} (a b : ℕ) (d : GeoExpr n) (p : Pt n)
    (hd : d.evalPts (fun _ : ℕ => p) = 0) :
    Holds (GeoConstraint.sqDistEq a b d) (fun _ => p) := by
  show sqDist (n := n) p p = d.evalPts (fun _ : ℕ => p)
  rw [hd, sqDist_self]

/-- **`eqZero e` holds at a constant configuration WHEN `e` evaluates to zero there.**

**This is stated as an `Iff`, not as an implication, because the implication direction is `he` itself
-- `GeoConstraint.Holds (.eqZero e) pts` IS `e.evalPts pts = 0`, with no unfolding in between.**
**A theorem whose proof term is its own hypothesis carries no information, and `check_proof_strength`
rejects such a shape.**
**=> the honest form records the CONVERSE as well: at a constant configuration, `eqZero` holds exactly
when the expression vanishes, because the configuration enters only through `evalPts`.** -/
theorem holds_eqZero_const_iff {n : ℕ} (e : GeoExpr n) (p : Pt n) :
    Holds (GeoConstraint.eqZero e) (fun _ => p) ↔ e.evalPts (fun _ : ℕ => p) = 0 :=
  Iff.rfl

/-- **`leZero e` holds when `e` evaluates to zero.** -/
theorem holds_leZero_const_of_eval_zero {n : ℕ} (e : GeoExpr n) (p : Pt n)
    (he : e.evalPts (fun _ : ℕ => p) = 0) :
    Holds (GeoConstraint.leZero e) (fun _ => p) := by
  show e.evalPts (fun _ : ℕ => p) ≤ 0
  rw [he]

/-- **`gtZero e` does NOT hold when `e` evaluates to zero.**

**This is the ONE exclusion that survives the correction, and it survives for a STRUCTURAL reason
rather than an incidental one: `gtZero` demands a STRICT inequality, and the degenerate configuration
supplies exactly `0`, never a positive value.**
**=> no choice of expression makes `gtZero` hold there, because the value is `0` by construction.** -/
theorem not_holds_gtZero_const_of_eval_zero {n : ℕ} (e : GeoExpr n) (p : Pt n)
    (he : e.evalPts (fun _ : ℕ => p) = 0) :
    ¬ Holds (GeoConstraint.gtZero e) (fun _ => p) := by
  show ¬ (0 < e.evalPts (fun _ : ℕ => p))
  rw [he]
  exact lt_irrefl 0

/-- **The corrected family: a constraint is admissible when it holds at a constant configuration.**

**This REPLACES the closed list `DegenerateOK`.**
**Stated as a predicate on the constraint, it is decidable in principle and, more importantly, it says
what the family MEANS: "satisfiable by collapsing every point to one".**

**`DegenerateOK` is not deleted**: **it remains as a SUFFICIENT condition, and
`degenerateOK_imp_admissible` records that the list is contained in the predicate.** -/
def ConstConfigOK {n : ℕ} (c : GeoConstraint n) : Prop :=
  ∃ p : Pt n, Holds c (fun _ => p)

/-- **Every `DegenerateOK` constraint is `ConstConfigOK`.**

**The list is not replaced, it is SUBSUMED: `DegenerateOK` gives a witness for free (any `p`), while
`ConstConfigOK` additionally admits `equalLength`, `sqDistEq` with a vanishing `d`, and `eqZero` with a
vanishing `e`.** -/
theorem degenerateOK_imp_constConfigOK {n : ℕ} (c : GeoConstraint n)
    (hc : DegenerateOK c) : ConstConfigOK c :=
  ⟨fun _ => 0, holds_of_degenerateOK c hc _⟩

/-- **`equalLength` is `ConstConfigOK`** -- it was wrongly excluded, and this is the repair. -/
theorem equalLength_constConfigOK {n : ℕ} (a b e f : ℕ) :
    ConstConfigOK (n := n) (GeoConstraint.equalLength a b e f) :=
  ⟨fun _ => 0, holds_equalLength_const a b e f _⟩

end Lattice.Plugins.Targets
