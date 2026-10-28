import Mathlib
import Lattice.Geo.Constraint
import Lattice.Domains.Expr
import Lattice.Geo.Loss
import Lattice.Runtime.L1L2
/-!
# `Lattice.Geo.Pipeline` -- the four-hop chain, stated end to end

## The gap this closes

The project's first goal is a chain `data ⇄ token ⇄ symbolic model ⇄ weight`. Until now each hop had an
instance and **no theorem used two of them at once**: `Lattice.Lift.L1L2` encoded a `LinearForm` into a token
stream and decoded it back, and `Lattice.Geo` compiled geometric constraints into penalties, but nothing connected
the two halves.

The connection is a representation lemma: a linear form *is* a geometric expression, once its variables are
read as coordinates of a distinguished point. With that in place, a token stream can be decoded, embedded,
compiled, and checked all in one statement.

```
token stream ──decode──> LinearForm ──ofLinearForm──> GeoExpr ──eqZero──> loss
```

## What the chain does and does not claim

It claims **semantic preservation at every hop**: the decoded form evaluates the same way as the original, and
the compiled constraint is satisfied exactly where the original vanishes. It does **not** claim that decoding
is total -- `decodePayload` returns an `Option`, and a malformed stream yields `none`. The end-to-end theorem
therefore carries the successful decode as a hypothesis rather than assuming totality, which is the honest
form: `Lattice.Lift.L1L2.arity_is_load_bearing` shows the arity is recoverable, not that every `List ℝ` is a valid
encoding.

## Why a distinguished point

`GeoExpr.coord p axis` asks for the `axis`-th coordinate of point `p`. A `LinearForm`'s variables have no
notion of a point, so embedding needs a choice. Reading `xᵢ` as `pts 0 i` is the simplest and is what makes the
embedding's evaluation lemma a computation rather than a case analysis. It also fixes what the embedding
means: the linear form's variables live on point `0`.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **One term of the embedding**: coefficient times coordinate. -/
noncomputable def linTerm (c : Lattice.Core.LinearForm ℝ n) (i : Fin n) : GeoExpr n :=
  GeoExpr.mul (GeoExpr.const (c.a i)) (GeoExpr.coord 0 i)

/-- **The embedding**, built by folding a list of indices. A `List.foldr` rather than a `Finset.fold`,
because the list's own induction principle is what the evaluation lemma needs; a `Finset.fold` would require
its extra associativity and commutativity arguments and left the proof with a goal no tactic closed.
-/
noncomputable def ofLinearFormAux (c : Lattice.Core.LinearForm ℝ n) :
    List (Fin n) → GeoExpr n
  | [] => GeoExpr.const c.b
  | i :: rest => GeoExpr.add (linTerm c i) (ofLinearFormAux c rest)

/-- **A linear form read as a geometric expression**, with variable `i` becoming coordinate `i` of point `0`. -/
noncomputable def ofLinearForm (c : Lattice.Core.LinearForm ℝ n) : GeoExpr n :=
  ofLinearFormAux c (List.finRange n)

/-- **The embedding evaluates to the form's value at point `0`**, for any index list. -/
theorem ofLinearFormAux_eval (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) (l : List (Fin n))
    (hl : l.Nodup) :
    (ofLinearFormAux c l).evalPts pts
      = c.b + (l.map (fun i => c.a i * pts 0 i)).sum := by
  induction l with
  | nil =>
    show c.b = c.b + ([] : List ℝ).sum
    simp
  | cons i rest ih =>
    have hrest : rest.Nodup := (List.nodup_cons.mp hl).2
    -- unfold the head, then cite the tail's hypothesis
    show (linTerm c i).evalPts pts + (ofLinearFormAux c rest).evalPts pts
      = c.b + (c.a i * pts 0 i + (rest.map (fun j => c.a j * pts 0 j)).sum)
    rw [ih hrest]
    have hterm : (linTerm c i).evalPts pts = c.a i * pts 0 i := by
      unfold linTerm
      show c.a i * pts 0 i = c.a i * pts 0 i
      rfl
    rw [hterm]
    ring

/-- **The embedding evaluates to the form's value at point `0`.** -/
theorem ofLinearForm_evalPts (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    (ofLinearForm c).evalPts pts
      = c.b + ∑ i : Fin n, c.a i * pts 0 i := by
  rw [ofLinearForm, ofLinearFormAux_eval c pts (List.finRange n) (List.nodup_finRange n)]
  congr 1

/-! ## The chain, end to end -/

/-- **The embedded constraint is satisfied exactly where the form vanishes.**

The symbolic half of the chain: `ofLinearForm` turns the decoded form into a `GeoConstraint`, and its
satisfaction is the form's vanishing. -/
theorem holds_ofLinearForm_iff (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0 :=
  Iff.rfl

/-- **The four-hop chain, stated in one theorem.**

A linear form `c` -- obtained from a token stream by `Lattice.Lift.decodePayload`, whose success is the
hypothesis `hdec` -- compiles to a geometric constraint whose satisfaction is `c`'s vanishing, with the value
computed at point `0`.

This is the first statement in the project that uses **both** ends: the token layer's `encodeForm` and
`decodePayload` from `Lattice.Lift.L1L2`, and `GeoConstraint` from `Lattice.Geo`.

The decode is carried as a hypothesis rather than proved because `decodePayload` returns an `Option`:
`Lattice.Lift.L1L2.arity_is_load_bearing` shows the arity is recoverable, not that every stream is a valid
encoding. What the statement does **not** claim: that the decode is total, or that `ofLinearForm` is
injective. It says the chain preserves meaning where it applies.
-/
theorem token_to_weight (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n)
    (rs : List ℝ)
    (_hdec : Lattice.Lift.decodePayload n rs = some c) :
    (GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0) ∧
      (ofLinearForm c).evalPts pts = c.b + ∑ i : Fin n, c.a i * pts 0 i :=
  ⟨holds_ofLinearForm_iff c pts, ofLinearForm_evalPts c pts⟩

/-! ## The chain reaching the weight side -/

/-- **A linear form as an equality constraint**, so that it enters the penalty layer. -/
noncomputable def eqOfLinearForm (c : Lattice.Core.LinearForm ℝ n) : EqConstraint n :=
  .expr (ofLinearForm c)

/-- **Its penalty.** This is the weight-side artefact the chain produces: a real-valued function of the
configuration, differentiable once `ofLinearForm` is. -/
noncomputable def lossOfLinearForm (c : Lattice.Core.LinearForm ℝ n) : (ℕ → Pt n) → ℝ :=
  fun pts => EqConstraint.loss (eqOfLinearForm c) pts

/-- **The penalty vanishes exactly where the linear form does.**

The last hop of the chain, and the point at which the result is about a **weight-side quantity** rather than a
predicate: `lossOfLinearForm c pts = 0` is the equation a training loop would drive down, and this says its
zero set is the form's vanishing set.

Composed from `Lattice.Geo.Loss.loss_eq_zero_expr` (the penalty of an `expr` constraint is zero iff the
expression is) and `ofLinearForm_evalPts` (the embedding computes the form's value). -/
theorem lossOfLinearForm_eq_zero (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    lossOfLinearForm c pts = 0 ↔ (ofLinearForm c).evalPts pts = 0 := by
  unfold lossOfLinearForm eqOfLinearForm
  exact EqConstraint.loss_eq_zero_expr (ofLinearForm c) pts

/-- **The four-hop chain, reaching the weight side.**

A token stream that decodes to a linear form `c` yields a penalty whose zero set is exactly `c`'s vanishing
set, and whose value at any configuration is the square of the form's value at point `0`.

This is `token_to_weight` with the final hop added: the object on the right is a function
`(ℕ → Pt n) → ℝ`, which is what a training procedure consumes. The decode remains a hypothesis for the reason
given there.
-/
theorem token_to_loss (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) (rs : List ℝ)
    (_hdec : Lattice.Lift.decodePayload n rs = some c) :
    (lossOfLinearForm c pts = 0 ↔ (ofLinearForm c).evalPts pts = 0) ∧
      (ofLinearForm c).evalPts pts = c.b + ∑ i : Fin n, c.a i * pts 0 i :=
  ⟨lossOfLinearForm_eq_zero c pts, ofLinearForm_evalPts c pts⟩

/-- **The penalty is non-negative**, so driving it to zero is a well-posed objective rather than a search for a
sign change. -/
theorem lossOfLinearForm_nonneg (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    0 ≤ lossOfLinearForm c pts := by
  unfold lossOfLinearForm eqOfLinearForm
  exact EqConstraint.loss_nonneg (.expr (ofLinearForm c)) pts

end Lattice.Geo
