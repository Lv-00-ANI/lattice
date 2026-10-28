import Mathlib
import Lattice.Domains.Constraints.Loss
import Lattice.Domains.Geometry.ExprLocalMin
import Lattice.Domains.Constraints.Dist
import Lattice.Domains.Geometry.Derivative

/-!
# `Lattice.Geo.PolyNondegenerate` -- two ways a `poly` local minimum can be a zero

## The two principles

`EqConstraint.poly` has four branches, and the routes by which a local minimum of the squared penalty forces
the penalty to vanish split into two *different* arguments:

* **Non-degeneracy.** If the derivative does not vanish, a local minimum of the square is a zero
  (`Lattice.Geo.Derivative.localMin_implies_zero`). This covers `.perpendicular` (Round 99--103) and, through
  `Lattice.Geo.ExprLocalMin`, the `.expr` branch.
* **Non-negativity.** If the penalty is `≥ 0`, its local minima coincide with its global minima, and a zero is
  the global minimum. This covers `.samePoint`, whose penalty is `sqDist`.

The second is not a weakening of the first, and the first cannot cover it: a `sqDist`-type penalty has *zero*
derivative exactly at the point where the penalty vanishes, which is where the local minimum is. So
`HasNonzeroDeriv` is not merely hard to prove there present -- it is **false**, and a proof that demanded it
would be demanding something the statement does not have.

Keeping the two routes separate is the whole point of this file: an audit that asks "is every `poly` branch
covered by non-degeneracy?" would report `.samePoint` as an unclosed gap, when it is closed by a different
argument. -/

namespace Lattice.Geo

variable {n : ℕ}

/-! ## Route one: non-degeneracy through `ExprLocalMin` -/

/-- **The `.expr` branch is covered by the derivative argument.**

`EqConstraint.poly (.expr e) pts` is by definition `e.evalPts pts`, and `Lattice.Geo.ExprLocalMin` already bridges
`evalPts` to the local-minimum argument. The one thing this theorem adds is the change of variable: `ExprLocalMin`
phrases the statement over `Fin (k * n) → ℝ` through `toNatConfig`, so a caller holding a point sequence needs
`k` past `e.maxPoint` to read it back.

The hypothesis `hne` is `derivExpr k e w ≠ 0` -- the residual's derivative at the read-back configuration. It is
the honest hypothesis rather than a gap: a constant expression has zero derivative everywhere, and its penalty is
minimised at every point without vanishing (`Lattice.Geo.ExprLocalMin.constExpr_localMin_counterexample`). -/
theorem poly_expr_localMin_implies_zero
    (e : GeoExpr n) (k : ℕ) (hk : e.maxPoint < k) (w : Fin (k * n) → ℝ)
    (hne : derivExpr k e w ≠ 0)
    (hmin : IsLocalMin (fun y : Fin (k * n) → ℝ =>
      (EqConstraint.poly (.expr e) (toNatConfig y)) ^ 2) w) :
    EqConstraint.poly (.expr e) (toNatConfig w) = 0 :=
  evalPts_localMin_implies_zero k e hk w hne hmin

/-! ## Route two: non-negativity, without any derivative -/

/-- **The `.samePoint` branch's penalty is `sqDist`**, and therefore non-negative.

Recorded as its own statement because the branch is what makes the non-negativity route applicable, and because a
reader checking coverage should be able to see the reason at a glance. -/
theorem poly_samePoint_eq_sqDist (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.poly (.samePoint a b) pts = sqDist (n := n) (pts a) (pts b) :=
  rfl

/-- **The `.samePoint` penalty is non-negative.** -/
theorem poly_samePoint_nonneg (a b : ℕ) (pts : ℕ → Pt n) :
    0 ≤ EqConstraint.poly (.samePoint a b) pts := by
  rw [poly_samePoint_eq_sqDist]
  exact sqDist_nonneg (n := n) (pts a) (pts b)

/-- **The `.samePoint` penalty vanishes exactly on the coincident configurations.** -/
theorem poly_samePoint_eq_zero_iff (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.poly (.samePoint a b) pts = 0 ↔ pts a = pts b := by
  rw [poly_samePoint_eq_sqDist]
  exact sqDist_eq_zero_iff (n := n) (pts a) (pts b)

/-! ## What the non-negativity route does *not* give

The `.samePoint` branch is where an earlier draft of this file went wrong, and the mistake is worth recording
because it is the kind a reader would make too.

`sqDist ≥ 0` makes `0` the **global** minimum. It does **not** make every **local** minimum a zero: a configuration
where the two points differ can perfectly well be a local minimum of `sqDist` as far as non-negativity alone is
concerned, because non-negativity says nothing about which way the function moves nearby.

What forces the local minimum to be a zero is the same thing that forces it in the other branches -- some
direction in which the penalty strictly decreases -- and for `sqDist` that direction is easy to name: if `pts a`
and `pts b` differ in some coordinate, moving `pts a` toward `pts b` along that coordinate strictly decreases the
sum of squares. Turning that into a theorem needs `Function.update` arithmetic on the `ℕ → Pt n` carrier plus a
`Finset.sum` comparison, which is ordinary work of the kind `Lattice.Geo.RepairPerp` already does for the
perpendicular residual.

**The argument is not carried out in this file.** It is carried out in `Lattice.Geo.PathContinuity`, so the branch *is*
covered -- the claim being rebutted above is only that non-negativity alone covers it. The audit question "is every
`poly` branch covered?" should answer `.expr`: yes; `.perpendicular`: yes; `.samePoint`: yes (by the path argument);
`.distEq`: no.

-/
/-! ## Arithmetic toward the `.samePoint` branch

Round 113 recorded `.samePoint` as uncovered. The lemmas here are the arithmetic half of closing it: overwriting one
coordinate of `p` with `q`'s value removes exactly that coordinate's squared difference, so the sum of squares
strictly decreases whenever the coordinate differs. -/

/-- **`sqDist` splits off one coordinate.** -/
theorem sqDist_eq_coord_add_rest (p q : Pt n) (i : Fin n) :
    sqDist (n := n) p q =
      (p i - q i) ^ 2 + ∑ j in Finset.univ \ {i}, (p j - q j) ^ 2 := by
  rw [show sqDist (n := n) p q = ∑ j : Fin n, (p j - q j) ^ 2 from by
      simp [sqDist, Lib.Linear.PenaltyVector.sqNorm, diff]]
  exact Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i) (fun j => (p j - q j) ^ 2)

/-! ## The `.samePoint` branch: arithmetic here, limit step proved elsewhere

`sqDist_eq_coord_add_rest` is the arithmetic half of the argument: it isolates one coordinate's squared difference
from the sum. From it, overwriting coordinate `i` of `p` with `q`'s value removes exactly that term, so the sum
strictly decreases whenever the coordinate differs. The overwrite lemma itself is `Lattice.Geo.PathContinuity`'s
`sqDist_along_path_split`; the derivation of it is also spelled out in `Zero/Proofs/P100-samePoint分支.md`.

**The step that actually closes the branch is not arithmetic.** `IsLocalMin f a` is a *neighbourhood* condition
(`∀ᶠ x in 𝓝 a, f a ≤ f x`), so refuting it requires a point **near** `a` with a smaller value. The overwrite is exact
rather than small -- `Function.update` places `pts a i` at `pts b i`, which can be arbitrarily far -- so the witness it
produces need not lie in any neighbourhood. Closing the branch therefore needs a path argument: move coordinate `i` by
`t`, use continuity and strict decrease in `t`, then take `t` small enough to stay in the neighbourhood. That is a
`Tendsto`/`Continuous` argument on `ℕ → Pt n`, and it is precisely the step `.perpendicular` gets for free from
`HasFDerivAt` and `Lattice.Geo.Derivative.localMin_implies_zero`. It is carried out in `Lattice.Geo.PathContinuity`, and not
by a derivative: the carrier has no `SeminormedAddCommGroup`, so no `HasFDerivAt` is available to appeal to.

Coverage: `.expr` yes; `.perpendicular` yes (in `Lattice.Geo.NonDegenerate`); `.samePoint` yes, by the path argument in
`Lattice.Geo.PathContinuity.sqDist_samePoint_not_localMin`; `.distEq` not attempted. -/

/-! ## Which argument each branch needs, and why two of them cannot use the derivative

Measured in Round 116 by instance synthesis on `ℕ → Pt n` (an infinite product):

| instance | available? |
|:--|:--|
| `AddCommGroup` | yes |
| `Module ℝ` | yes |
| `TopologicalSpace` | yes |
| `SeminormedAddCommGroup` | **no** |
| `NormedAddCommGroup`, `NormedSpace` | **no** |

`HasFDerivAt` and `HasNonzeroDeriv` are stated for normed spaces, so on `ℕ → Pt n` they are unavailable. That is why
the derivative route cannot simply be lifted to this carrier, and it explains a difference between the branches that
otherwise looks arbitrary:

* `.perpendicular` and `.expr` **do** use the derivative -- but never on `ℕ → Pt n`. They carry a finite `k`, change
  variable through `toNatConfig` to `Fin (k * n) → ℝ`, do the calculus there, and read back. Both therefore need the
  bound `maxPoint` gives.
* `.samePoint` and `.distEq` have no such finite re-indexing: `sqDist` reads whichever two points are named, with no
  bound to exploit. So they cannot reach `Fin (k * n) → ℝ`, and they cannot use the derivative on the infinite
  carrier either. What they need is a route that stays in `ℕ → Pt n`.

For `.samePoint` that route has since been completed in `Lattice.Geo.PathContinuity`: the path is
`t ↦ Function.update pts a (Function.update (pts a) i (pts a i + t))`, it is continuous by
`continuous_samePoint_path`, the square of the penalty strictly decreases along it for a scaled `-d`
(`sqDist_along_path_lt`), and `exists_small_descent` places the witness at any prescribed scale. Composing the three
gives `sqDist_samePoint_not_localMin`: a configuration with `pts a ≠ pts b` is not a local minimum of the squared
penalty, hence, by non-negativity together with `poly_samePoint_eq_zero_iff`, every local minimum is a zero. Note
that this argument never mentions a derivative -- it could not, since the carrier admits none (table above) -- which
is exactly why the branch needed the route that stays in `ℕ → Pt n`. For `.distEq` the penalty `sqDist - d.evalPts`
is not non-negative, so the non-negativity route is closed to it as well, it has no finite re-indexing to reach
`Fin (k * n) → ℝ`, and no route has been established at all.

The table is the honest form of "is every branch covered?": `.expr` yes, `.perpendicular` yes, `.samePoint` yes,
`.distEq` no -- and the reason `.distEq` differs from the other three is a measurable property of the carrier, not
an accident of effort. -/


/-! ## Why `.distEq` needs a hypothesis, not a better proof

For `.samePoint` the penalty is `sqDist`, which is non-negative and attains `0`. That is what made the negative
statement -- "a non-coincident configuration is not a local minimum" -- provable.

`.distEq` is `sqDist (pts a) (pts b) - d.evalPts pts`. With `d` a negative constant the penalty is *strictly
positive everywhere*, its infimum is that positive constant, and the squared penalty therefore has a strictly
positive global minimum. No amount of work on the derivative or the topology changes that: the implication
"local minimum implies zero" is false for this branch, not merely unproved.

The two lemmas below pin the counterexample down. They are deliberately about the penalty alone -- no `IsLocalMin`,
no path, no derivative -- because the failure is prior to all three: the function whose local minima are supposed to
be zero does not have a zero to be at. -/

/-- **A negative constant makes the `.distEq` penalty strictly positive.** -/
theorem distEq_penalty_pos_of_neg_const (p q : Pt n) {c : ℝ} (hc : c < 0) :
    0 < sqDist (n := n) p q - c := by
  have h := sqDist_nonneg (n := n) p q
  linarith

/-- **The squared `.distEq` penalty is bounded below by a strictly positive number.**

`0 <= sqDist` forces `-c <= sqDist - c`, and `c < 0` makes `c ^ 2` positive, so the square never comes near zero.
This is the substantive form of the counterexample: it says the infimum of the squared penalty is not `0`, hence a
local minimum of it cannot be a zero of the penalty.

An earlier attempt stated the same idea with a hypothesis `sqDist p q = 0`. That hypothesis is not free: by
`Lattice.Geo.Dist.sqDist_eq_zero_iff` it forces `p = q`, so the resulting equation said nothing about `c` at all. The
bound below avoids the vacuity by comparing against `c ^ 2` rather than against an attained value. -/
theorem distEq_sq_penalty_ge_sq (p q : Pt n) {c : ℝ} (hc : c < 0) :
    c ^ 2 ≤ (sqDist (n := n) p q - c) ^ 2 := by
  have h := sqDist_nonneg (n := n) p q
  have hc' : c ≤ sqDist (n := n) p q - c := by linarith
  nlinarith [sq_nonneg (sqDist (n := n) p q - c), hc']

/-- **That lower bound is strictly positive.** -/
theorem neg_const_sq_pos {c : ℝ} (hc : c < 0) : 0 < c ^ 2 := by
  nlinarith

end Lattice.Geo
