import Mathlib
import Lattice.Domains.Derive

/-!
# `Lattice.Geo.Shape` -- a computable, conservative structural comparison

## Why this file exists

`Lattice.Geo.Derive` states the engine's firing round relationally, because a functional version needs
`DecidableEq (GeoConstraint n)` and that instance does not exist: `GeoConstraint` carries `GeoExpr`, whose
`const` constructor holds a `ℝ`, and real equality is not decidable.

A relational engine can be *proved* sound but not *run*. This file supplies what a runnable engine needs: a
boolean comparison that is **computable** and **sound in one direction** -- `true` implies equality -- and is
therefore allowed to answer `false` for pairs that are in fact equal.

## The design, and why `false` is the safe answer

`const c₁` and `const c₂` are compared as **always unequal**. That is a conservative choice:

* `true` is only produced when the structures genuinely agree, so `beqShape e₁ e₂ = true → e₁ = e₂` holds;
* `false` may be produced for equal expressions, so the engine can miss a firing but never invent one.

An engine built on this therefore derives a **subset** of what a `DecidableEq` engine would. That is the correct
trade: the objective asks for a symbolic engine whose conclusions are certified, not for one that is complete.

## What is compared, and what is not

`ℕ` and `Fin n` fields are compared by `==`, whose soundness is available. `ℝ` fields are not compared at all.
`bool` fields, had they existed, would fall in the same category as `ℝ`.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Structural comparison of expressions**, answering `true` only when the structures agree.

The `const` case always answers `false`: comparing real numbers decidably is not possible in this setting, and a
wrong `true` would let the engine derive something it should not. Answering `false` costs completeness, never
soundness. -/
def GeoExpr.beqShape : GeoExpr n → GeoExpr n → Bool
  | .coord p₁ a₁, .coord p₂ a₂ => p₁ == p₂ && a₁ == a₂
  | .const _, .const _ => false
  | .add a₁ b₁, .add a₂ b₂ => beqShape a₁ a₂ && beqShape b₁ b₂
  | .sub a₁ b₁, .sub a₂ b₂ => beqShape a₁ a₂ && beqShape b₁ b₂
  | .mul a₁ b₁, .mul a₂ b₂ => beqShape a₁ a₂ && beqShape b₁ b₂
  | _, _ => false

/-- **The comparison is sound**: `true` implies genuine equality.

The `const` case holds vacuously, since it answers `false` -- which is exactly why the conservative choice is
safe rather than merely cautious. -/
theorem GeoExpr.beqShape_eq {e₁ e₂ : GeoExpr n} (h : e₁.beqShape e₂ = true) : e₁ = e₂ := by
  induction e₁ generalizing e₂ with
  | coord p₁ a₁ =>
    cases e₂ with
    | coord p₂ a₂ =>
      simp only [GeoExpr.beqShape, Bool.and_eq_true] at h
      rw [beq_iff_eq.mp h.1, beq_iff_eq.mp h.2]
    | const c => simp [GeoExpr.beqShape] at h
    | add _ _ => simp [GeoExpr.beqShape] at h
    | sub _ _ => simp [GeoExpr.beqShape] at h
    | mul _ _ => simp [GeoExpr.beqShape] at h
  | const c =>
    cases e₂ <;> simp [GeoExpr.beqShape] at h
  | add a₁ b₁ ih₁ ih₂ =>
    cases e₂ with
    | add a₂ b₂ =>
      simp only [GeoExpr.beqShape, Bool.and_eq_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    | coord _ _ => simp [GeoExpr.beqShape] at h
    | const _ => simp [GeoExpr.beqShape] at h
    | sub _ _ => simp [GeoExpr.beqShape] at h
    | mul _ _ => simp [GeoExpr.beqShape] at h
  | sub a₁ b₁ ih₁ ih₂ =>
    cases e₂ with
    | sub a₂ b₂ =>
      simp only [GeoExpr.beqShape, Bool.and_eq_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    | coord _ _ => simp [GeoExpr.beqShape] at h
    | const _ => simp [GeoExpr.beqShape] at h
    | add _ _ => simp [GeoExpr.beqShape] at h
    | mul _ _ => simp [GeoExpr.beqShape] at h
  | mul a₁ b₁ ih₁ ih₂ =>
    cases e₂ with
    | mul a₂ b₂ =>
      simp only [GeoExpr.beqShape, Bool.and_eq_true] at h
      rw [ih₁ h.1, ih₂ h.2]
    | coord _ _ => simp [GeoExpr.beqShape] at h
    | const _ => simp [GeoExpr.beqShape] at h
    | add _ _ => simp [GeoExpr.beqShape] at h
    | sub _ _ => simp [GeoExpr.beqShape] at h

/-- **Structural comparison of constraints**, with the same conservativity as `GeoExpr.beqShape`. -/
def GeoConstraint.beqShape : GeoConstraint n → GeoConstraint n → Bool
  | .eqZero e₁, .eqZero e₂ => e₁.beqShape e₂
  | .leZero e₁, .leZero e₂ => e₁.beqShape e₂
  | .ltZero e₁, .ltZero e₂ => e₁.beqShape e₂
  | .gtZero e₁, .gtZero e₂ => e₁.beqShape e₂
  | .sqDistEq a₁ b₁ d₁, .sqDistEq a₂ b₂ d₂ => a₁ == a₂ && b₁ == b₂ && d₁.beqShape d₂
  | .equalLength a₁ b₁ c₁ e₁, .equalLength a₂ b₂ c₂ e₂ =>
    a₁ == a₂ && b₁ == b₂ && c₁ == c₂ && e₁ == e₂
  | .collinear a₁ b₁ c₁, .collinear a₂ b₂ c₂ => a₁ == a₂ && b₁ == b₂ && c₁ == c₂
  | .perpendicular a₁ b₁ c₁ e₁, .perpendicular a₂ b₂ c₂ e₂ =>
    a₁ == a₂ && b₁ == b₂ && c₁ == c₂ && e₁ == e₂
  | .parallel a₁ b₁ c₁ e₁, .parallel a₂ b₂ c₂ e₂ =>
    a₁ == a₂ && b₁ == b₂ && c₁ == c₂ && e₁ == e₂
  | .rightAngle a₁ b₁ c₁, .rightAngle a₂ b₂ c₂ => a₁ == a₂ && b₁ == b₂ && c₁ == c₂
  | .midpoint m₁ a₁ b₁, .midpoint m₂ a₂ b₂ => m₁ == m₂ && a₁ == a₂ && b₁ == b₂
  | .samePoint a₁ b₁, .samePoint a₂ b₂ => a₁ == a₂ && b₁ == b₂
  | _, _ => false

/-- **The constraint comparison is sound**: `true` implies equality.

Each constructor pair is handled explicitly. The mismatched pairs are discharged by `Bool.noConfusion`, since
their comparison is `false` by definition; the matched pairs reduce to `GeoExpr.beqShape_eq` plus `beq_iff_eq` on
the `ℕ` and `Fin` fields. -/
theorem GeoConstraint.beqShape_eq {c₁ c₂ : GeoConstraint n} (h : c₁.beqShape c₂ = true) :
    c₁ = c₂ := by
  cases c₁ with
  | eqZero e₁ =>
    cases c₂ with
    | eqZero e₂ => rw [GeoExpr.beqShape_eq h]
    | leZero e₂ => simp [GeoConstraint.beqShape] at h
    | ltZero e₂ => simp [GeoConstraint.beqShape] at h
    | gtZero e₂ => simp [GeoConstraint.beqShape] at h
    | sqDistEq _ _ _ => simp [GeoConstraint.beqShape] at h
    | equalLength _ _ _ _ => simp [GeoConstraint.beqShape] at h
    | collinear _ _ _ => simp [GeoConstraint.beqShape] at h
    | perpendicular _ _ _ _ => simp [GeoConstraint.beqShape] at h
    | parallel _ _ _ _ => simp [GeoConstraint.beqShape] at h
    | rightAngle _ _ _ => simp [GeoConstraint.beqShape] at h
    | midpoint _ _ _ => simp [GeoConstraint.beqShape] at h
    | samePoint _ _ => simp [GeoConstraint.beqShape] at h
  | leZero e₁ =>
    cases c₂ with
    | leZero e₂ => rw [GeoExpr.beqShape_eq h]
    | _ => simp [GeoConstraint.beqShape] at h
  | ltZero e₁ =>
    cases c₂ with
    | ltZero e₂ => rw [GeoExpr.beqShape_eq h]
    | _ => simp [GeoConstraint.beqShape] at h
  | gtZero e₁ =>
    cases c₂ with
    | gtZero e₂ => rw [GeoExpr.beqShape_eq h]
    | _ => simp [GeoConstraint.beqShape] at h
  | samePoint a₁ b₁ =>
    cases c₂ with
    | samePoint a₂ b₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | midpoint m₁ a₁ b₁ =>
    cases c₂ with
    | midpoint m₂ a₂ b₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | collinear a₁ b₁ c₁ =>
    cases c₂ with
    | collinear a₂ b₂ c₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | rightAngle a₁ b₁ c₁ =>
    cases c₂ with
    | rightAngle a₂ b₂ c₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | perpendicular a₁ b₁ c₁ e₁ =>
    cases c₂ with
    | perpendicular a₂ b₂ c₂ e₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | parallel a₁ b₁ c₁ e₁ =>
    cases c₂ with
    | parallel a₂ b₂ c₂ e₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | equalLength a₁ b₁ c₁ e₁ =>
    cases c₂ with
    | equalLength a₂ b₂ c₂ e₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, h.2]
    | _ => simp [GeoConstraint.beqShape] at h
  | sqDistEq a₁ b₁ d₁ =>
    cases c₂ with
    | sqDistEq a₂ b₂ d₂ =>
      simp only [GeoConstraint.beqShape, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, GeoExpr.beqShape_eq h.2]
    | _ => simp [GeoConstraint.beqShape] at h

/-- **The comparison decides the pairs it can**: two coordinate expressions with the same index compare equal,
which is what makes the runner productive on the rules this project ships. -/
theorem GeoExpr.beqShape_refl_coord (p : ℕ) (axis : Fin n) :
    (GeoExpr.coord p axis).beqShape (GeoExpr.coord p axis) = true := by
  simp [GeoExpr.beqShape]

end Lattice.Geo
