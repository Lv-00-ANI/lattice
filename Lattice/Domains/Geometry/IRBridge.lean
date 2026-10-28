import Mathlib
import Lattice.Domains.Geometry.LayerExact
import Lattice.Domains.Constraints.Loss

/-!
# `Lattice.Geo.IRBridge` -- the IR layer, re-established inside the kernel

## Why this file exists

`_archive/DECISION-G7.md` records a decision not to repair the `lvLang → IR → Cv00` chain, and
`_archive/G7-BREAKPOINTS.md` records the measured cost of doing so. That left an obvious question unanswered: if
not through Cv00, then **how does the objective's "compile symbolic knowledge into weights" get done at all?**

The answer is that the IR layer -- not Cv00 -- is where the two sides meet, and this file makes that concrete. It
re-states the compilable part of `IRConstraint` inside the kernel and proves the compilation preserves semantics.

## Why re-state rather than import

`Zero/Reference/LvFormal/` is frozen reference material outside the build; `gov/gate.py` treats it as a separate
zone and `gov/lvformal_perfile.py` measures that 56 of its 121 modules do not build. Importing from it would pull
that debt into the kernel.

So the compilable subset is re-stated here, with a comment on each constructor naming its `Reference` counterpart.
This is not duplication for its own sake: the kernel gets a version whose semantics it can prove things about,
and the correspondence is documented rather than assumed.

## What compiles, and what does not

Of `IRConstraint`'s fifteen constructors, **eleven have a `GeoConstraint` counterpart** and four do not:

| `IRConstraint` | `GeoConstraint` | note |
|:--|:--|:--|
| `distance a b d` | `sqDistEq a b d` | squared distance; the *distance* needs a square root |
| `collinear a b c` | `collinear a b c` | |
| `perpendicular a b c d` | `perpendicular a b c d` | |
| `parallel a b c d` | `parallel a b c d` | |
| `eq_expr e₁ e₂` | `eqZero (e₁ − e₂)` | |
| `lt_expr e₁ e₂` | `ltZero (e₁ − e₂)` | |
| `gt_expr e₁ e₂` | `gtZero (e₁ − e₂)` | |
| `midpoint m a b` | `midpoint m a b` | |
| `rightAngle a b c` | `rightAngle a b c` | |
| `equalLength a b c d` | `equalLength a b c d` | |
| `radius center a r` | `sqDistEq center a (r²)` | the radius is squared, which `GeoExpr` cannot express without a product |

The four that do not:

* **`angle`** and **`equalAngle`** need `arccos`, which is not a `GeoExpr` constructor -- and `GeoConstraint`
  deliberately has no `transc` layer, so an angle constraint could not receive an exact penalty even if it were
  expressible. This is the same exclusion recorded in `Lattice.Geo.Eval`'s `IsNumeric`.
* **`tangent`** needs a circle as an object; `GeoConstraint` speaks only of points and segments.
* **`ratioDivision p a b r`** needs a division by a variable, which `GeoExpr` lacks (`mul` and `sub` only).

Recording the four with their reasons is more useful than pretending the bridge is total.

## The variable mapping

`IRConstraint` names points by `String`; `GeoConstraint` indexes them by `ℕ`. Compilation therefore takes a name
assignment `String → ℕ` as a parameter. This is the one piece of data the bridge cannot supply itself, and it is
what makes the compiler a *partial* map from syntax to geometry rather than an identity.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The compilable subset of `IRConstraint`.**

Each constructor mirrors its `Zero/Reference/LvFormal/Theory/IR.lean` counterpart by name and arity. Expressions are
`GeoExpr`, so `div` and `sqrt` are absent -- which is precisely why `ratioDivision` and `angle` are excluded below.
-/
inductive IRConstraintLite (n : ℕ) where
  /-- `distance a b d`: the squared distance between `a` and `b` equals `d`. -/
  | distance (a b : ℕ) (d : GeoExpr n)
  /-- Three points are collinear. -/
  | collinear (a b c : ℕ)
  /-- Two segments are perpendicular. -/
  | perpendicular (a b c d : ℕ)
  /-- Two segments are parallel. -/
  | parallel (a b c d : ℕ)
  /-- Two expressions agree. -/
  | eqExpr (e₁ e₂ : GeoExpr n)
  /-- The first expression is below the second. -/
  | ltExpr (e₁ e₂ : GeoExpr n)
  /-- The first expression exceeds the second. -/
  | gtExpr (e₁ e₂ : GeoExpr n)
  /-- `m` is the midpoint of `a` and `b`. -/
  | midpoint (m a b : ℕ)
  /-- The angle at `b` in `a b c` is a right angle. -/
  | rightAngle (a b c : ℕ)
  /-- Two segments have equal length. -/
  | equalLength (a b c d : ℕ)
  /-- The squared distance from `center` to `a` equals the squared radius. -/
  | radius (center a : ℕ) (r : GeoExpr n)

/-- **The IR layer's semantics**, matching `ir_sem` on the subset that compiles.

Stated over `ℕ → Pt n` rather than `String → ℝ × ℝ` because the names have already been resolved to indices; the
resolution is the compiler's parameter, not this definition's concern. -/
noncomputable def IRHolds (pts : ℕ → Pt n) : IRConstraintLite n → Prop
  | .distance a b d => sqDist (n := n) (pts a) (pts b) = d.evalPts pts
  | .collinear a b c => GeoConstraint.Holds (.collinear a b c) pts
  | .perpendicular a b c d => GeoConstraint.Holds (.perpendicular a b c d) pts
  | .parallel a b c d => GeoConstraint.Holds (.parallel a b c d) pts
  | .eqExpr e₁ e₂ => e₁.evalPts pts = e₂.evalPts pts
  | .ltExpr e₁ e₂ => e₁.evalPts pts < e₂.evalPts pts
  | .gtExpr e₁ e₂ => e₂.evalPts pts < e₁.evalPts pts
  | .midpoint m a b => GeoConstraint.Holds (.midpoint m a b) pts
  | .rightAngle a b c => GeoConstraint.Holds (.rightAngle a b c) pts
  | .equalLength a b c d => GeoConstraint.Holds (.equalLength a b c d) pts
  | .radius center a r => sqDist (n := n) (pts center) (pts a) = (r.evalPts pts) ^ 2

/-- **Compiling an IR constraint into a geometric one.** Every constructor of `IRConstraintLite` has a target, so the
map is total -- the *partiality* of the bridge lives in which `IRConstraint` constructors made it into the subset,
not in this function. -/
noncomputable def compileIR : IRConstraintLite n → GeoConstraint n
  | .distance a b d => .sqDistEq a b d
  | .collinear a b c => .collinear a b c
  | .perpendicular a b c d => .perpendicular a b c d
  | .parallel a b c d => .parallel a b c d
  | .eqExpr e₁ e₂ => .eqZero (GeoExpr.sub e₁ e₂)
  | .ltExpr e₁ e₂ => .ltZero (GeoExpr.sub e₁ e₂)
  | .gtExpr e₁ e₂ => .gtZero (GeoExpr.sub e₁ e₂)
  | .midpoint m a b => .midpoint m a b
  | .rightAngle a b c => .rightAngle a b c
  | .equalLength a b c d => .equalLength a b c d
  | .radius center a r => .sqDistEq center a (GeoExpr.mul r r)

/-- **Compilation preserves semantics.**

This is the bridge's content: an IR constraint holds exactly when its compiled image holds. Without it, "compile IR
into geometry and then into a penalty" would be a chain of definitions with no guarantee that the last one is about
the first.

Each case is immediate from `IRHolds`'s definition -- the two are stated against the same `Holds`, which is what
makes the theorem a check rather than a proof obligation. That is the point: `compileIR`'s cases were chosen so
that this equality is *definitional*, and this theorem verifies the choice. -/
theorem compileIR_sound (pts : ℕ → Pt n) (c : IRConstraintLite n) :
    IRHolds pts c ↔ GeoConstraint.Holds (compileIR c) pts := by
  cases c <;> simp [IRHolds, compileIR, GeoConstraint.Holds, GeoExpr.evalPts, sub_eq_zero, sq]

/-- **The composition pattern: T1 consumed by T2.**

Given an exactness lemma for a penalty against the *compiled* constraint, the same penalty decides the *IR*
constraint. The only step is `compileIR_sound`, which is where T1 enters; without it the statement would relate a
penalty to nothing.

Every `compileIR_*_exact` theorem below is an instance, and a future constructor joins by supplying only its
exactness lemma. -/
theorem compileIR_penalty_exact_of (c : IRConstraintLite n) (pen : (ℕ → Pt n) → ℝ) (pts : ℕ → Pt n)
    (hex : pen pts = 0 ↔ GeoConstraint.Holds (compileIR c) pts) :
    pen pts = 0 ↔ IRHolds pts c := by
  rw [hex, compileIR_sound]

/-- **The compiled constraint's penalty vanishes exactly on the IR constraint's models**, for the twelve
constructors whose penalty is exact.

Composing `compileIR_sound` with `LayerExact`/`Loss`/`Square` is what closes the objective's chain at the IR layer:
syntax → geometry → penalty, with the last step's zeroes being the first step's models. Stated for `distance` as the
representative case; the others follow identically. -/
theorem compileIR_distance_penalty_exact (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    sqDistEqPenalty a b d pts = 0 ↔ IRHolds pts (.distance a b d) := by
  rw [sqDistEqPenalty_eq_zero_iff]
  simp [IRHolds, compileIR, GeoConstraint.Holds]


/-! ## T1 composed with T2: the compiled constraint's penalty decides the IR constraint

`compileIR_sound` (T1) says compilation preserves meaning. The exactness theorems (T2) say a penalty decides its
constraint. Composing them gives what neither states alone: **an IR constraint is satisfied exactly when the
penalty of its compiled form vanishes**.

This is the join the project's objective calls an "extension": before it, a reader had to walk from `compileIR` to
`GeoConstraint.Holds` and then separately to the penalty; now the walk is a theorem.

Four constructors admit the join outright. The remaining seven either have no penalty in the current layering
(`radius` compiles to `sqDistEq` with a composite right-hand side but has no exactness lemma of its own, and the
`poly`-layer constructors are stated over `EqConstraint` rather than `GeoConstraint`), or need the non-degeneracy
condition carried separately. They are not claimed here. -/

/-- **T1 ∘ T2 for `distance`**: the compiled penalty vanishes exactly when the IR constraint holds.

`compileIR` sends `.distance a b d` to `.sqDistEq a b d`, which is the constraint `sqDistEqPenalty` decides. The
composition goes through `compileIR_sound`, so the statement consumes **both** T1 and T2. -/
theorem compileIR_distance_exact (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    sqDistEqPenalty a b d pts = 0 ↔ IRHolds pts (.distance a b d : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts (by simpa only [compileIR] using sqDistEqPenalty_eq_zero_iff a b d pts)

/-- **T1 ∘ T2 for `equalLength`**. -/
theorem compileIR_equalLength_exact (a b e f : ℕ) (pts : ℕ → Pt n) :
    equalLengthPenalty a b e f pts = 0 ↔ IRHolds pts (.equalLength a b e f : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts (by simpa only [compileIR] using equalLengthPenalty_eq_zero_iff a b e f pts)

/-- **T1 ∘ T2 for `collinear`**, carrying the geometric non-degeneracy condition `seg a c ≠ 0`.

Off the degenerate locus the penalty decides the constraint (see `Lattice.Geo.LayerExact`), and compilation is the
identity on this constructor, so the IR constraint is decided by the penalty exactly when the segment is nonzero. -/
theorem compileIR_collinear_exact (a b k : ℕ) (pts : ℕ → Pt n)
    (hne : GeoConstraint.seg pts a k ≠ 0) :
    collinearPenalty a b k pts = 0 ↔ IRHolds pts (.collinear a b k : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts (by simpa only [compileIR] using collinearPenalty_eq_zero_iff_of_ne a b k pts hne)

/-- **T1 ∘ T2 for `parallel`**, carrying the same non-degeneracy condition. -/
theorem compileIR_parallel_exact (a b e f : ℕ) (pts : ℕ → Pt n)
    (hne : GeoConstraint.seg pts e f ≠ 0) :
    parallelPenalty a b e f pts = 0 ↔ IRHolds pts (.parallel a b e f : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts (by simpa only [compileIR] using parallelPenalty_eq_zero_iff_of_ne a b e f pts hne)


/-- **T1 composed with T2 for `eqExpr`.**

`compileIR` sends `.eqExpr e₁ e₂` to `.eqZero (e₁ - e₂)`, and `EqConstraint.loss` on `.expr (e₁ - e₂)` decides that
constraint through `EqConstraint.loss_eq_zero_toGeo`. The join therefore consumes T1 (`compileIR_sound`), T2's
`poly`-layer exactness (`loss_eq_zero_expr`), and the `EqConstraint -> GeoConstraint` inclusion added in
`Lattice.Geo.Loss`. -/
theorem compileIR_eqExpr_exact (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    EqConstraint.loss (.expr (GeoExpr.sub e₁ e₂)) pts = 0
      ↔ IRHolds pts (.eqExpr e₁ e₂ : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts
    (by simpa only [compileIR, eqToGeo] using loss_eq_zero_toGeo_expr _ pts)

/-- **T1 composed with T2 for `perpendicular`.**

`compileIR` and `eqToGeo` both act as the identity on the perpendicular constructor, so the `poly` layer's
exactness for `.perpendicular` transfers directly: the dot product vanishes exactly when the IR constraint
holds. -/
theorem compileIR_perpendicular_exact (a b c e : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.perpendicular a b c e) pts = 0
      ↔ IRHolds pts (.perpendicular a b c e : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts
    (by simpa only [compileIR, eqToGeo] using loss_eq_zero_toGeo_perpendicular a b c e pts)

/-- **What the remaining IR constructors would need.**

`ltExpr` and `gtExpr` compile to `.ltZero` / `.gtZero`, which the `poly` layer has no constructor for: `EqConstraint`
is an *equality* fragment, and `EqConstraint.loss` squares by construction, so it cannot represent a strict
inequality's residual. A join for them needs a non-squared penalty on `GeoConstraint` directly, which the current
layering does not provide.

`midpoint` and `rightAngle` are compiled verbatim, so their exactness would have to come from `Square`; those lemmas
exist for `sqDistEq` and `equalLength` but not for these two.

Recording the obstruction here is deliberate: an absent theorem should say why it is absent, and the reason differs
between these two pairs. -/
theorem compileIR_remaining_obstruction (c : EqConstraint n) :
    (∀ e : GeoExpr n, eqToGeo c ≠ .ltZero e) ∧
      (∀ e : GeoExpr n, eqToGeo c ≠ .gtZero e) := by
  constructor
  · intro e h
    cases c <;> simp [eqToGeo] at h
  · intro e h
    cases c <;> simp [eqToGeo] at h


/-- **T1 composed with T2 for `radius`.**

`compileIR` sends `.radius center a r` to `.sqDistEq center a (r * r)`. `sqDistEqPenalty_eq_zero_iff` holds for an
*arbitrary* right-hand expression, so the circle constraint needs no penalty of its own: substituting `r * r` gives
exactness directly.

This is a case where the barrier was not real: an earlier revision of this file listed `radius` as unjoinable
because it has "a composite right-hand side", which the lemma never required. -/
theorem compileIR_radius_exact (center a : ℕ) (r : GeoExpr n) (pts : ℕ → Pt n) :
    sqDistEqPenalty center a (GeoExpr.mul r r) pts = 0
      ↔ IRHolds pts (.radius center a r : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts
    (by simpa only [compileIR] using sqDistEqPenalty_eq_zero_iff center a (GeoExpr.mul r r) pts)


/-- **T1 composed with T2 for `midpoint`.**

`compileIR` is the identity on this constructor, and `midpointPenalty` (added in `Lattice.Geo.Square`) vanishes exactly
on `.midpoint m a b`. The join consumes T1 and that exactness. -/
theorem compileIR_midpoint_exact (m a b : ℕ) (pts : ℕ → Pt n) :
    midpointPenalty m a b pts = 0 ↔ IRHolds pts (.midpoint m a b : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts
    (by simpa only [compileIR] using midpointPenalty_eq_zero_iff m a b pts)

/-- **T1 composed with T2 for `rightAngle`.** -/
theorem compileIR_rightAngle_exact (a b c : ℕ) (pts : ℕ → Pt n) :
    rightAnglePenalty a b c pts = 0 ↔ IRHolds pts (.rightAngle a b c : IRConstraintLite n) :=
  compileIR_penalty_exact_of _ _ pts
    (by simpa only [compileIR] using rightAnglePenalty_eq_zero_iff a b c pts)

/-! ### Coverage

With the join above, **nine of the eleven** `IRConstraintLite` constructors are connected to a penalty:

| constructor | penalty | status |
|:--|:--|:--|
| `distance` | `sqDistEqPenalty` | joined |
| `equalLength` | `equalLengthPenalty` | joined |
| `collinear` | `collinearPenalty` | joined (with `seg != 0`) |
| `parallel` | `parallelPenalty` | joined (with `seg != 0`) |
| `eqExpr` | `EqConstraint.loss` | joined |
| `perpendicular` | `EqConstraint.loss` | joined |
| `radius` | `sqDistEqPenalty (r * r)` | joined |
| `midpoint` | `midpointPenalty` | joined |
| `rightAngle` | `rightAnglePenalty` | joined |
| `ltExpr` | -- | **not joinable** |
| `gtExpr` | -- | **not joinable** |

The last two are not a gap to be filled later: `compileIR` sends them to `.ltZero` / `.gtZero`, whose `Holds` is a
*strict inequality*, and every penalty in this project is a square -- zero exactly on the boundary, not on one side
of it. Representing a strict inequality needs a different construct (a hinge, a log-barrier, a margin), and none is
in the current layering. Saying so is more useful than a theorem with an unprovable hypothesis. -/
end Lattice.Geo
