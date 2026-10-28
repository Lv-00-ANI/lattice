import Mathlib
import Lattice.Domains.Expr
import Lattice.Geo.Flatten

/-!
# `Lattice.Geo.Finite` -- evaluating an expression in a configuration of known size

## The gap this closes

`GeoExpr.evalPts` takes `pts : ℕ → Pt n`: a constraint mentions points by number and does not know how
many the figure has. `Lattice.Geo.Flatten` turns a configuration of `k` points into a vector
`Fin (k * n) → ℝ`. To connect the two, one has to know that the expression does not mention a point
beyond `k` -- otherwise `evalPts` would read a coordinate that the finite configuration does not carry.

So the bound is **part of the data**, not a side condition discovered halfway through a proof:

```lean
GeoExpr.VarsBelow e k    -- every point index occurring in `e` is < k
GeoExpr.evalFin e h pts  -- evaluate, with `h : VarsBelow e k` supplying the index
```

Carrying `h` in the signature is what lets the recursive definition use `pts ⟨p, h⟩` directly, instead
of proving a bound again at every constructor. Putting the hypothesis in the statement and then
threading it through a separate correctness lemma would be the same information, arranged worse.

## Why this is where the hypothesis belongs

The project's discipline is that a theorem needing an unproved or restrictive fact takes it as an
explicit parameter. "The expression only mentions points that exist" is exactly such a fact, and it
belongs to the *expression*, not to the ambient configuration -- so it is defined on `GeoExpr` and
threaded through the evaluation, rather than asserted about `pts`.
-/

namespace Lattice.Geo

namespace GeoExpr

variable {n : ℕ}

/-- **The expression mentions only points numbered below `k`.**

Structural on the expression, so it is decided by inspecting the syntax rather than by reasoning about
the configuration. -/
def VarsBelow : GeoExpr n → ℕ → Prop
  | .coord p _, k => p < k
  | .const _, _ => True
  | .add a b, k => a.VarsBelow k ∧ b.VarsBelow k
  | .sub a b, k => a.VarsBelow k ∧ b.VarsBelow k
  | .mul a b, k => a.VarsBelow k ∧ b.VarsBelow k

@[simp] theorem varsBelow_coord (p : ℕ) (axis : Fin n) (k : ℕ) :
    VarsBelow (.coord p axis : GeoExpr n) k ↔ p < k := Iff.rfl

@[simp] theorem varsBelow_const (c : ℝ) (k : ℕ) :
    VarsBelow (.const c : GeoExpr n) k ↔ True := Iff.rfl

@[simp] theorem varsBelow_add (a b : GeoExpr n) (k : ℕ) :
    VarsBelow (.add a b) k ↔ a.VarsBelow k ∧ b.VarsBelow k := Iff.rfl

@[simp] theorem varsBelow_sub (a b : GeoExpr n) (k : ℕ) :
    VarsBelow (.sub a b) k ↔ a.VarsBelow k ∧ b.VarsBelow k := Iff.rfl

@[simp] theorem varsBelow_mul (a b : GeoExpr n) (k : ℕ) :
    VarsBelow (.mul a b) k ↔ a.VarsBelow k ∧ b.VarsBelow k := Iff.rfl

/-- **Evaluate in a configuration of exactly `k` points.**

The hypothesis `h` is what makes `pts ⟨p, h⟩` well-typed at every `coord`, which is why it is a
parameter of the definition rather than of a separate lemma. -/
noncomputable def evalFin {k : ℕ} (e : GeoExpr n) (h : e.VarsBelow k) (pts : Fin k → Pt n) : ℝ :=
  match e, h with
  | .coord p axis, h => pts ⟨p, h⟩ axis
  | .const c, _ => c
  | .add a b, h => a.evalFin h.1 pts + b.evalFin h.2 pts
  | .sub a b, h => a.evalFin h.1 pts - b.evalFin h.2 pts
  | .mul a b, h => a.evalFin h.1 pts * b.evalFin h.2 pts

/-- **`evalFin` agrees with `evalPts`** when the ambient family extends the finite configuration.

This is the coherence lemma: the finite evaluator is not a different semantics, it is the same one
restricted. Stated with an explicit `ext` hypothesis because extending `Fin k → Pt n` to `ℕ → Pt n`
requires choosing values for the extra points, and the choice must not matter -- which is exactly the
content of `VarsBelow`. -/
theorem evalFin_eq_evalPts {k : ℕ} (e : GeoExpr n) (h : e.VarsBelow k)
    (pts : Fin k → Pt n) (ext : ℕ → Pt n)
    (hagree : ∀ p (hp : p < k), ext p = pts ⟨p, hp⟩) :
    e.evalFin h pts = e.evalPts ext := by
  induction e with
  | coord p axis =>
      simp only [evalFin, evalPts]
      rw [hagree p h]
  | const c => rfl
  | add a b iha ihb =>
      simp only [evalFin, evalPts, varsBelow_add] at *
      rw [iha h.1, ihb h.2]
  | sub a b iha ihb =>
      simp only [evalFin, evalPts, varsBelow_sub] at *
      rw [iha h.1, ihb h.2]
  | mul a b iha ihb =>
      simp only [evalFin, evalPts, varsBelow_mul] at *
      rw [iha h.1, ihb h.2]

end GeoExpr

end Lattice.Geo
