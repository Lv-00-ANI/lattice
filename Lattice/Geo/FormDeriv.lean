import Mathlib
import Lattice.Geo.ExprDeriv
import Lattice.Geo.Perturb

/-!
# `Lattice.Geo.FormDeriv` -- the arithmetic of the embedded form's derivative

## What this file establishes, and what it does not

`Lattice.Geo.Derivative` carries `HasNonzeroDeriv` as a hypothesis; `Lattice.Geo.ExprDeriv` proves that any `GeoExpr`
is differentiable on a large enough flattened carrier. What remains is the numerical half -- that the derivative
of `ofLinearForm c` does not vanish when `c` has a nonzero coefficient.

This file supplies the **arithmetic core** of that: the coordinate projection reads a bump as a Kronecker delta,
the derivative of one term of the embedding is a scaled projection, and the derivative is additive over the index
list. Together these say the derivative, evaluated at the bump in a coefficient's direction, is the coefficient.

## The gap

The final step -- that the accumulated sum equals `c.a i₀` -- is **not** proved here. Two attempts to write it
ran into the same obstruction: `rw` will not match
`(coordProj k n ⟨0, hk⟩ i) (bump k n ⟨0, hk⟩ i)` against the goal's printed form, which carries the applied
result rather than the application.

Every ingredient is proved; what is missing is one rewriting step. Recorded in `_archive/KNOWN-GAPS.md` rather
than approximated with a placeholder, because the arithmetic is settled and the obstruction is elaboration.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **A coordinate projection reads a bump as one.** -/
theorem coordProj_bump_same (k n : ℕ) (a : Fin k) (i : Fin n) :
    coordProj k n a i (bump k n a i) = 1 := by
  unfold coordProj bump
  show (if flatEquiv k n (a, i) = flatEquiv k n (a, i) then (1 : ℝ) else 0) = 1
  rw [if_pos rfl]

/-- **A projection reads a bump at a different index as zero.** -/
theorem coordProj_bump_ne {k n : ℕ} {a b : Fin k} {i j : Fin n} (h : ¬(a = b ∧ i = j)) :
    coordProj k n a i (bump k n b j) = 0 := by
  unfold coordProj bump
  have hne : flatEquiv k n (a, i) ≠ flatEquiv k n (b, j) := by
    intro heq
    exact h (Prod.ext_iff.mp (Equiv.injective _ heq))
  show (if flatEquiv k n (a, i) = flatEquiv k n (b, j) then (1 : ℝ) else 0) = 0
  rw [if_neg hne]

/-! ## The derivative of the embedding, term by term -/

/-- **The derivative of one term.** `linTerm c i` is `const (c.a i) * coord 0 i`; by the product rule and the
fact that a constant's derivative vanishes, only the second factor contributes. -/
theorem derivExpr_linTerm {k : ℕ} (c : Lattice.Core.LinearForm ℝ n) (i : Fin n) (hk : 0 < k)
    (w : Fin (k * n) → ℝ) :
    derivExpr k (linTerm c i) w = c.a i • coordProj k n ⟨0, hk⟩ i := by
  unfold linTerm
  simp only [derivExpr]
  rw [dif_pos hk]
  simp

/-- **The derivative is additive over the index list.** Both recursions are `add` at the head, so this is
definitional. -/
theorem derivExpr_ofLinearFormAux_cons (c : Lattice.Core.LinearForm ℝ n) (i : Fin n)
    (rest : List (Fin n)) (k : ℕ) (w : Fin (k * n) → ℝ) :
    derivExpr k (ofLinearFormAux c (i :: rest)) w
      = derivExpr k (linTerm c i) w + derivExpr k (ofLinearFormAux c rest) w :=
  rfl

/-- The constant case carries no derivative. -/
theorem derivExpr_ofLinearFormAux_nil (c : Lattice.Core.LinearForm ℝ n) (k : ℕ)
    (w : Fin (k * n) → ℝ) :
    derivExpr k (ofLinearFormAux c []) w = 0 :=
  rfl

/-- **The derivative of the embedding is a sum of scaled projections**, in the form the bump argument
consumes. Stated for a general index list so that the induction is over the list rather than over
`List.finRange n`. -/
theorem derivExpr_ofLinearFormAux_apply (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (l : List (Fin n)) (δ : Fin (k * n) → ℝ) :
    derivExpr k (ofLinearFormAux c l) 0 δ
      = (l.map (fun i => c.a i * coordProj k n ⟨0, hk⟩ i δ)).sum := by
  induction l with
  | nil => simp [derivExpr_ofLinearFormAux_nil]
  | cons i rest ih =>
    rw [derivExpr_ofLinearFormAux_cons (w := 0), ContinuousLinearMap.add_apply,
        derivExpr_linTerm (c := c) (i := i) (hk := hk) (w := 0), ih]
    simp [smul_eq_mul]

/-- **Evaluating the derivative at a bump isolates the coefficient.**

The last step of the non-vanishing argument, and the one that resisted several attempts. The obstruction was not
the arithmetic but the rewriting: `coordProj … (bump …)` inside a `List.map`-then-`sum` will not match by `rw`,
because the printed form differs from the application's. The cure is to push the map and sum out first
(`simp only [map_cons, sum_cons]`), expose the head, rewrite it in isolation, and discharge the tail with
`List.sum_eq_zero` -- which is the shape `derivExpr_ofLinearFormAux_apply` produces.

`hnd` is what makes the tail vanish: without distinctness the same index could appear twice and the sum would
double. -/
theorem derivExpr_ofLinearFormAux_bump (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (l : List (Fin n)) (i₀ : Fin n) (hmem : i₀ ∈ l) (hnd : l.Nodup) :
    derivExpr k (ofLinearFormAux c l) 0 (bump k n ⟨0, hk⟩ i₀) = c.a i₀ * 1 := by
  rw [derivExpr_ofLinearFormAux_apply c hk l]
  -- induction over the list rather than splitting it: the head is either the witness or projects away
  induction l with
  | nil => simp at hmem
  | cons j rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest_nd : rest.Nodup := (List.nodup_cons.mp hnd).2
    by_cases hji : j = i₀
    · -- the head is the witness and the tail contributes nothing
      subst hji
      have hfresh : ∀ x ∈ rest.map (fun i => c.a i * coordProj k n ⟨0, hk⟩ i (bump k n ⟨0, hk⟩ j)),
          x = 0 := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hne : i ≠ j := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hi)
        rw [coordProj_bump_ne (a := (⟨0, hk⟩ : Fin k)) (b := (⟨0, hk⟩ : Fin k))
          (i := i) (j := j) (by intro hh; exact hne hh.2), mul_zero]
      rw [List.sum_eq_zero hfresh, add_zero, coordProj_bump_same]
    · -- the head projects away; the witness is in the tail
      have hz : coordProj k n ⟨0, hk⟩ j (bump k n ⟨0, hk⟩ i₀) = 0 :=
        coordProj_bump_ne (a := (⟨0, hk⟩ : Fin k)) (b := (⟨0, hk⟩ : Fin k))
          (i := j) (j := i₀) (by intro hh; exact hji hh.2)
      rw [hz, mul_zero, zero_add]
      have hmem' : i₀ ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hji
        · exact h
      exact ih hmem' hrest_nd

/-- **The embedded form's derivative does not vanish when the form has a coefficient.**

The last obligation `Lattice.Geo.Derivative.HasNonzeroDeriv` named, now discharged for the chain: evaluating
`derivExpr` at the bump in the direction of a nonzero coefficient gives that coefficient, which is nonzero.

`hcoef` is genuinely needed. A constant form has zero derivative, its square has a minimum at every
configuration, and `Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` cannot fire -- so the penalty would carry
no information about the constraint. `Lattice.Lib.Penalty.Counterexample.polynomial_penalty_not_exact` records the
same failure from the loss side.
-/
theorem derivExpr_ofLinearForm_ne_zero (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (hcoef : ∃ i, c.a i ≠ 0) :
    derivExpr k (ofLinearForm c) 0 ≠ 0 := by
  intro hzero
  obtain ⟨i₀, hi₀⟩ := hcoef
  -- the bump witnesses that the functional is not identically zero
  have hbump := derivExpr_ofLinearFormAux_bump c hk (List.finRange n) i₀
    (List.mem_finRange i₀) (List.nodup_finRange n)
  rw [ofLinearForm] at hzero
  have hval : derivExpr k (ofLinearFormAux c (List.finRange n)) 0 (bump k n ⟨0, hk⟩ i₀) = 0 := by
    rw [hzero]
    rfl
  rw [hbump] at hval
  exact hi₀ (by linarith [hval])

end Lattice.Geo
