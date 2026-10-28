import Mathlib
import Lattice.Domains.Constraint
import Lattice.Domains.Dist

/-!
# `Lattice.Geo.Eval` -- which constraints have a value, and why the answer is not "all of them"

## `KNOWN-GAPS` item 6, and what attempting it produced

The gap said "`GeoExpr` has `evalPts`, but there is no independent evaluation engine for constraints". Attempting
one produced a finding worth recording: **a constraint does not have a value in the singular**.

`eqZero e` asserts an expression is zero, so its "value" is that expression's number. `sqDistEq a b d` compares two
numbers. `collinear a b c` asserts a witness exists and has no number at all. Returning `ℝ` for all twelve would
require inventing a value for `collinear` -- the distance of what from what? -- and the invention would be
indistinguishable from a bug.

## What was tried, and where it stopped

The natural design indexes the value type by `Layer`:

```lean
def LayerValue : Layer → Sort _
  | .poly => ℝ
  | .square => ℝ × ℝ
  | .existential => Prop
```

The obstacles are real and so is the record of them:

* `Layer` lives in `Type`, so `LayerValue : Layer → Sort _` forces a universe bump that Lean then refuses to reduce
  in the per-constructor agreement lemmas;
* dependent `match` on the layer leaves free variables in the impossibility branches, which `decide` cannot
  discharge;
* the resulting definitions need `noncomputable`, which contradicts the point of calling them an evaluator.

This is the third obstruction of its kind in the project, after `_archive/KNOWN-GAPS.md`'s `variable-width` and
`multivar-penalty` items: the mathematics is settled and the elaborator will not carry the indexing.

## What the file does provide, and why it is the substantive half

`GeoConstraint.layer` already answers "which constraints can become penalties". This file states that answer
sharply enough for a caller to **branch on it before attempting an evaluation**:

* `IsNumeric` names the layers with a real value;
* `isNumeric_iff` proves that these are exactly `poly` and `square`;
* `exists_layer_not_numeric` exhibits a constraint with no numeric value at all.

That last theorem is what turns "not every constraint can be evaluated to a number" from a remark into a fact with
a witness -- and it is the reason a total evaluator returning `ℝ` cannot exist.

## What remains owed

A total evaluator needs either a `Sigma`-typed result (`Σ l, LayerValue l`) carrying the layer as *data* rather
than as an index, or one evaluator per layer. Both are mechanical: neither changes what is mathematically true.
The disposition is to record rather than to force, because a definition whose lemmas do not compile is not an
evaluator.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The constraints that evaluate to a single real number.**

`poly` and `square` are numeric; `existential` and `transc` are not. Stated on `Layer` so a caller can decide,
before attempting an evaluation, whether a constraint has a number at all. -/
def IsNumeric : Layer → Prop
  | .poly => True
  | .square => True
  | .existential => False
  | .transc => False

/-- **Exactly the `poly` and `square` layers are numeric.** -/
theorem isNumeric_iff (l : Layer) : IsNumeric l ↔ (l = .poly ∨ l = .square) := by
  cases l <;> simp [IsNumeric]

/-- **A constraint with no numeric value exists**, and it is one this project uses.

`collinear` asserts the existence of a scalar witness. There is no number it computes to, so any evaluator
returning `ℝ` must invent one. The witness is what makes the claim falsifiable rather than rhetorical. -/
theorem exists_layer_not_numeric : ∃ c : GeoConstraint n, ¬ IsNumeric c.layer :=
  ⟨.collinear 0 1 2, by simp [GeoConstraint.layer, IsNumeric]⟩

/-- **A `poly` constraint's value is its expression's number**, for the constructor the penalty layer consumes.

Stated as an identification rather than a computation: `holds_eqZero` is definitionally the vanishing of
`evalPts`, which is why `Lattice.Geo.Loss` can square it and `Lattice.Lib.Penalty.PolyExact` can reason about the square.

Only the `eqZero` case is recorded. The comparison cases (`leZero` and friends) read the same number against zero,
and the geometric ones (`perpendicular`, `midpoint`) have residuals given in `Lattice.Geo.Dot` and
`Lattice.Geo.Loss` -- there is no need to restate them under a second name. -/
theorem eqZero_value_is_eval (e : GeoExpr n) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.eqZero e) pts ↔ e.evalPts pts = 0 :=
  Iff.rfl

end Lattice.Geo
