import Mathlib
import Lattice.Geo.Loss
import Lattice.Geo.Dist

/-!
# `Lattice.Geo.Square` -- penalties for the `square` layer

## What was missing

`Lattice.Geo.Loss` gives every `poly` constraint a residual and squares it, so seven of the twelve constructors of
`GeoConstraint` become optimisable. The five that did not are the two `square` constraints (`sqDistEq`,
`equalLength`) and the two `existential` ones (`collinear`, `parallel`).

This file closes the `square` half.

## Why the two `square` constraints share one penalty

`sqDistEq a b d` asserts `‖a - b‖² = d`. `equalLength a b c e` asserts `‖a - b‖² = ‖c - e‖²`. Both are equations
between **two real numbers**, so both reduce to "the difference of two values, squared":

```lean
def twoValuedPenalty (u v : ℝ) : ℝ := (u - v) ^ 2
```

That reduction is the whole content. The two constraints differ only in *which* numbers they compare --
a raw number against an expression's value in one case, two squared distances in the other -- and the exactness
argument is written once for the general form and specialised twice.

## Why the `existential` half does not follow

`collinear a b c` asserts the existence of a scalar `t` with `seg a b = t • seg a c`. There is no pair of numbers
to subtract; the assertion is about a witness, not an equation. A penalty for it exists in dimension `2`, where
collinearity is the vanishing of a cross product, but not uniformly in `n`. That is a different problem and is not
attempted here -- `Lattice.Geo.Eval` records why the value of a constraint is layer-dependent for the same reason.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The penalty for an equation between two real values.**

Zero exactly when the values agree, which is what makes it exact: a configuration minimising this penalty is one
where the constraint holds, with no spurious minima. -/
noncomputable def twoValuedPenalty (u v : ℝ) : ℝ := (u - v) ^ 2

/-- **The penalty vanishes exactly where the values agree.** The forward direction is what exactness needs; the
converse says the penalty carries no other information. -/
theorem twoValuedPenalty_eq_zero_iff (u v : ℝ) : twoValuedPenalty u v = 0 ↔ u = v := by
  unfold twoValuedPenalty
  constructor
  · intro h
    have h' : u - v = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linarith
  · intro h
    rw [h]
    ring

/-- **The penalty is non-negative**, so it is a legitimate loss rather than a signed quantity. -/
theorem twoValuedPenalty_nonneg (u v : ℝ) : 0 ≤ twoValuedPenalty u v := by
  unfold twoValuedPenalty
  positivity

/-- **`sqDistEq`'s penalty**: the squared distance between two points, compared against an expression's value. -/
noncomputable def sqDistEqPenalty (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) : ℝ :=
  twoValuedPenalty (sqDist (n := n) (pts a) (pts b)) (d.evalPts pts)

/-- **`equalLength`'s penalty**: two squared distances compared with each other. -/
noncomputable def equalLengthPenalty (a b c e : ℕ) (pts : ℕ → Pt n) : ℝ :=
  twoValuedPenalty (sqDist (n := n) (pts a) (pts b)) (sqDist (n := n) (pts c) (pts e))

/-- **`sqDistEq`'s penalty is exact**: it vanishes exactly on the configurations satisfying the constraint. -/
theorem sqDistEqPenalty_eq_zero_iff (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    sqDistEqPenalty a b d pts = 0 ↔ GeoConstraint.Holds (.sqDistEq a b d) pts := by
  unfold sqDistEqPenalty
  rw [twoValuedPenalty_eq_zero_iff]
  exact Iff.rfl

/-- **`equalLength`'s penalty is exact.** -/
theorem equalLengthPenalty_eq_zero_iff (a b c e : ℕ) (pts : ℕ → Pt n) :
    equalLengthPenalty a b c e pts = 0 ↔ GeoConstraint.Holds (.equalLength a b c e) pts := by
  unfold equalLengthPenalty
  rw [twoValuedPenalty_eq_zero_iff]
  exact Iff.rfl

/-- **Both `square` penalties are non-negative.** -/
theorem sqDistEqPenalty_nonneg (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    0 ≤ sqDistEqPenalty a b d pts :=
  twoValuedPenalty_nonneg _ _

theorem equalLengthPenalty_nonneg (a b c e : ℕ) (pts : ℕ → Pt n) :
    0 ≤ equalLengthPenalty a b c e pts :=
  twoValuedPenalty_nonneg _ _

/-! ## What is and is not claimed

The two exactness theorems above say the penalty's **zeroes are exactly the models**. That is the property a
training procedure needs from a loss, and it is now established for both `square` constraints.

A *local minimum* theorem -- "a local minimum satisfies the constraint" -- is **not** claimed here. The `poly` half
gets one (`Lattice.Geo.Unconditional.localMin_ofLinearForm_implies_zero`) because the derivative of the embedded form
is available and non-zero. For the `square` layer the penalty is a difference of two squared distances, whose
differentiability in the flattened carrier has not been established; asserting the local-minimum property without
that would be an unproven claim dressed as a theorem.

The gap is recorded rather than papered over: exactness is the substantive half, and it is proved.

-/


/-! ## Two penalties the layer table lists but no file supplied

`GeoConstraint.layer` classifies `.midpoint` and `.rightAngle` as `poly`, and their `Holds` conditions are equations
between real-valued expressions -- so an exact squared residual exists, exactly as it does for the other `poly`
constructors. What was missing was the definition and its exactness, which is what follows.

Both use the same device: a squared residual (or a square of a sum) is zero exactly when its inside is. -/

/-- The residual of `midpoint m a b`: `2 * pts m i - pts a i - pts b i`, squared and summed. -/
noncomputable def midpointPenalty (m a b : ℕ) (pts : ℕ → Pt n) : ℝ :=
  ∑ i : Fin n, (2 * pts m i - pts a i - pts b i) ^ 2

/-- **`midpointPenalty` vanishes exactly when the midpoint constraint holds.** -/
theorem midpointPenalty_eq_zero_iff (m a b : ℕ) (pts : ℕ → Pt n) :
    midpointPenalty m a b pts = 0 ↔ GeoConstraint.Holds (.midpoint m a b) pts := by
  unfold midpointPenalty GeoConstraint.Holds
  constructor
  · intro h i
    have hterm : (2 * pts m i - pts a i - pts b i) ^ 2 = 0 := by
      have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ (2 * pts m j - pts a j - pts b j) ^ 2 := by
        intro j _
        exact sq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i (Finset.mem_univ i)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
    linarith
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i]
    ring

/-- The residual of `rightAngle a b c`: the dot product `seg a b · seg b c`, squared. -/
noncomputable def rightAnglePenalty (a b c : ℕ) (pts : ℕ → Pt n) : ℝ :=
  (∑ i : Fin n, GeoConstraint.seg pts a b i * GeoConstraint.seg pts b c i) ^ 2

/-- **`rightAnglePenalty` vanishes exactly when the right-angle constraint holds.** -/
theorem rightAnglePenalty_eq_zero_iff (a b c : ℕ) (pts : ℕ → Pt n) :
    rightAnglePenalty a b c pts = 0 ↔ GeoConstraint.Holds (.rightAngle a b c) pts := by
  unfold rightAnglePenalty GeoConstraint.Holds
  exact pow_eq_zero_iff (n := 2) (by norm_num)

/-- Both penalties are non-negative, as squared residuals are. -/
theorem midpointPenalty_nonneg (m a b : ℕ) (pts : ℕ → Pt n) : 0 ≤ midpointPenalty m a b pts :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `rightAnglePenalty` is non-negative. -/
theorem rightAnglePenalty_nonneg (a b c : ℕ) (pts : ℕ → Pt n) : 0 ≤ rightAnglePenalty a b c pts :=
  sq_nonneg _

end Lattice.Geo
