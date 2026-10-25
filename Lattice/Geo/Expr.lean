import Mathlib
import Lattice.Core.Syntax

/-!
# `Lattice.Geo.Expr` -- geometric expressions over `n`-dimensional points

## Why this layer exists, and why it is not `Zero.LvFormal.Theory.IR`

`Lv-00`'s IR (`_harvest/lv00/formal/lvFormal/Theory/IR.lean`) defines geometric expressions as

```lean
inductive IRExpr where
  | var (name : String) | const (value : ℝ) | add | sub | mul | div | sqrt
def eval_expr (env : String → ℝ × ℝ) : IRExpr → ℝ
  | .var n => ptX (env n)      -- always the x coordinate
```

Four defects make it unusable as the symbolic side of this project
(`_archive/IR-DEFECTS.md` records them in full):

1. **`var` cannot address the `y` coordinate.** `eval_expr` discards it, so `eq_expr`,
   `lt_expr`, `distance` and `angle` can only mention `x`. This is not an inefficiency, it is a
   loss of expressiveness.
2. **`sqrt` is a constructor and appears in `dist`**, so every distance-bearing constraint is
   transcendental, while this project's weight side is affine. The two cannot be connected.
3. `collinear` uses the `ℝ × ℝ` subtraction instance while `perpendicular` writes the differences
   out by hand; equivalent, but it makes rewriting harder than it should be.
4. **The carrier is `ℝ × ℝ`** -- two dimensions, hardcoded. `zero/` already works over
   `Fin n → ℝ`, which is strictly wider.

So this file defines the expression layer again, fixing all four:

* coordinates carry their **point index and axis** (`coord p axis`), so no component is unreachable;
* there is **no `sqrt` and no `div`**: the fragment is polynomials. Removing `sqrt` is not a
  simplification but a decision -- the loss `f²` must be a polynomial for the penalty theorems to
  say anything, and a `sqrt` would make it transcendental;
* the carrier is `Pt n := Fin n → ℝ`, matching `Lattice.Lib.Linear`.

## What is deliberately absent

`div` and `sqrt` are absent, so this fragment cannot express `angle`, `equalAngle`, or distances
directly. That is the point: those are a *different* layer, recorded as owed rather than approximated
here. A constraint language that quietly includes a `sqrt` and then claims to reduce to a polynomial
would be the exact failure mode `_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md` describes.

## Design note on `coord`

`coord p axis : GeoExpr n` names "the `axis`-th coordinate of the `p`-th point". Points are indexed by
`ℕ` rather than by a finite type because a constraint *mentions* points; how many points the ambient
configuration has is a property of the interpretation (`pts : ℕ → Pt n`), not of the expression.
This keeps `GeoExpr n` independent of the number of points, which is what lets a constraint be
reused across configurations.
-/

namespace Lattice.Geo

/-- A point of `n`-dimensional real space.

This is `Lattice.Core.Syntax.Point` at `R = ℝ`, not a new abbreviation: defining a second `Point` would be
the exact duplication `Core` exists to prevent, and invariant I3 caught an earlier revision doing it. -/
abbrev Pt (n : ℕ) := Lattice.Core.Point ℝ n

/-- **Geometric polynomial expressions.**

Atoms are the coordinates of numbered points; the operations are addition, subtraction and
multiplication. There is no `div` and no `sqrt` -- see the module docstring.

The expression depends on `n` (the ambient dimension) but *not* on how many points the configuration
has, so the same constraint can be interpreted in any configuration. -/
inductive GeoExpr (n : ℕ) : Type where
  /-- The `axis`-th coordinate of point number `p`. -/
  | coord (p : ℕ) (axis : Fin n)
  /-- A real constant. -/
  | const (c : ℝ)
  | add (e₁ e₂ : GeoExpr n)
  | sub (e₁ e₂ : GeoExpr n)
  | mul (e₁ e₂ : GeoExpr n)

namespace GeoExpr

variable {n : ℕ}

/-- Zero as an expression. Convenient as a right-hand side for "this vanishes". -/
def zero : GeoExpr n := .const 0

/-- One as an expression. -/
def one : GeoExpr n := .const 1

/-- **Evaluation** in a configuration, i.e. for a family of points.

The interpretation is a function `ℕ → Pt n`: point index to coordinates. Coordinates are addressed
directly (`pts p axis`), which is what `IRExpr` could not do for the second component. -/
noncomputable def evalPts (e : GeoExpr n) (pts : ℕ → Pt n) : ℝ :=
  match e with
  | .coord p axis => pts p axis
  | .const c => c
  | .add e₁ e₂ => e₁.evalPts pts + e₂.evalPts pts
  | .sub e₁ e₂ => e₁.evalPts pts - e₂.evalPts pts
  | .mul e₁ e₂ => e₁.evalPts pts * e₂.evalPts pts

/-! ### Evaluation laws

These are what makes the fragment usable: each is a `rfl`-level fact about the definition, recorded
so that later proofs rewrite instead of unfolding. -/

@[simp] theorem evalPts_coord (p : ℕ) (axis : Fin n) (pts : ℕ → Pt n) :
    (coord p axis).evalPts pts = pts p axis := rfl

@[simp] theorem evalPts_const (c : ℝ) (pts : ℕ → Pt n) : (const c).evalPts pts = c := rfl

@[simp] theorem evalPts_add (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    (e₁.add e₂).evalPts pts = e₁.evalPts pts + e₂.evalPts pts := rfl

@[simp] theorem evalPts_sub (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    (e₁.sub e₂).evalPts pts = e₁.evalPts pts - e₂.evalPts pts := rfl

@[simp] theorem evalPts_mul (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    (e₁.mul e₂).evalPts pts = e₁.evalPts pts * e₂.evalPts pts := rfl

@[simp] theorem evalPts_zero (pts : ℕ → Pt n) : (zero : GeoExpr n).evalPts pts = 0 := rfl

@[simp] theorem evalPts_one (pts : ℕ → Pt n) : (one : GeoExpr n).evalPts pts = 1 := rfl

/-- The difference of two expressions vanishing is the same as the two values being equal.

This is the form every equality constraint reduces to, and it is `rfl`-adjacent, which is why it is
recorded: `eval a = eval b ↔ eval (sub a b) = 0` is what lets a constraint be turned into a
polynomial whose zero set is the solution set. -/
theorem evalPts_sub_eq_zero_iff (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) :
    (e₁.sub e₂).evalPts pts = 0 ↔ e₁.evalPts pts = e₂.evalPts pts := by
  simp [sub_eq_zero]

end GeoExpr

end Lattice.Geo
