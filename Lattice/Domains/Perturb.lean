import Mathlib
import Lattice.Domains.Flatten

/-!
# `Lattice.Geo.Perturb` -- algebraic properties of `unflatten` under perturbation

## Why this file exists separately

`Lattice.Geo.Nondegenerate` needs to show that the `perpendicular` residual has a nonzero gradient unless a
segment collapses. The strategy is a **coordinate bump**: perturb one entry of the flattened vector and
read off how the residual moves. That needs to know how `unflatten` responds to adding and scaling
vectors -- pure linear algebra on the layout equivalence, with nothing geometric about it.

Keeping it separate lets the geometric argument cite short lemmas instead of re-deriving index
bookkeeping inside a bilinear-form calculation.

## The three facts

```
unflatten (v + w) p q      = unflatten v p q + unflatten w p q     additive
unflatten (t • bump b i) b i = t                                   on the bumped entry
unflatten (t • bump b i) p q = 0                                   elsewhere
```

together giving `unflatten_add_smul_bump`, which is the form the geometry consumes -- and the three
segment lemmas at the end, which are what `perpResid_bump` will use.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **The unit bump at one entry of the flattened vector.**

`bump b i` is `1` at the slot the layout assigns to coordinate `i` of point `b`, and `0` elsewhere. It is
the dual of `Lattice.Geo.Differentiable.coordProj`, and like `coordProj` it is *named* rather than written
inline: an `if` inside a `•` inside a `HasFDerivAt` goal brings the elaborator no further. -/
noncomputable def bump (k n : ℕ) (b : Fin k) (i : Fin n) : Fin (k * n) → ℝ :=
  fun j => if j = flatEquiv k n (b, i) then 1 else 0

@[simp] theorem bump_self (b : Fin k) (i : Fin n) :
    bump k n b i (flatEquiv k n (b, i)) = 1 := by
  simp [bump]

theorem bump_ne {b : Fin k} {i : Fin n} {j : Fin (k * n)}
    (h : j ≠ flatEquiv k n (b, i)) : bump k n b i j = 0 := by
  simp [bump, h]

/-- **`unflatten` is additive**: it reads one entry, and reading is additive. -/
theorem unflatten_add (v w : Fin (k * n) → ℝ) (p : Fin k) (q : Fin n) :
    unflatten (v + w) p q = unflatten v p q + unflatten w p q := by
  simp [unflatten]

/-- **Reading the bumped entry gives the scale.** Here `flatEquiv`'s injectivity is used: equal images
force the pairs to be equal. -/
theorem unflatten_smul_bump_same (b : Fin k) (i : Fin n) (t : ℝ) :
    unflatten (t • bump k n b i) b i = t := by
  simp [unflatten, bump]

/-- **Reading any other entry of a bumped vector gives zero.** -/
theorem unflatten_smul_bump_ne {b p : Fin k} {i q : Fin n} (hpq : ¬(p = b ∧ q = i)) (t : ℝ) :
    unflatten (t • bump k n b i) p q = 0 := by
  simp only [unflatten, Pi.smul_apply, smul_eq_mul]
  have hne : flatEquiv k n (p, q) ≠ flatEquiv k n (b, i) := by
    intro h
    exact hpq (Prod.ext_iff.mp (Equiv.injective _ h))
  rw [bump_ne hne, mul_zero]

/-- **How `unflatten` responds to a bump**, in the single form the geometry cites. -/
theorem unflatten_add_smul_bump (b : Fin k) (i : Fin n) (t : ℝ) (v : Fin (k * n) → ℝ)
    (p : Fin k) (q : Fin n) :
    unflatten (v + t • bump k n b i) p q
      = unflatten v p q + (if p = b ∧ q = i then t else 0) := by
  by_cases h : p = b ∧ q = i
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    rw [unflatten_add, unflatten_smul_bump_same]
  · rw [if_neg h, unflatten_add, unflatten_smul_bump_ne h, add_zero]

/-! ### Segment lemmas

A segment component is a difference of two reads; the three lemmas below say how each read behaves when
the bumped point is, or is not, one of the segment's endpoints. These are the only facts
`perpResid_bump` needs. -/

/-- The `i`-th component of the displacement from `a` to `b`. -/
noncomputable def seg (a b : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) : ℝ :=
  unflatten v b i - unflatten v a i

/-- **Bumping `b`'s `i`-th coordinate raises the `i`-th component of `seg a b` by `t`**, provided the
bumped point is that segment's far endpoint. -/
theorem seg_bump_far (a b : Fin k) (i : Fin n) (t : ℝ) (v : Fin (k * n) → ℝ) (hba : b ≠ a) :
    seg a b i (v + t • bump k n b i) = seg a b i v + t := by
  unfold seg
  rw [unflatten_add_smul_bump, unflatten_add_smul_bump, if_pos (And.intro rfl rfl)]
  have hb : ¬(a = b ∧ i = i) := by
    intro h; exact hba h.1.symm
  rw [if_neg hb]
  ring

/-- **Bumping `b`'s `i`-th coordinate leaves the other components of `seg a b` alone.** -/
theorem seg_bump_far_ne (a b : Fin k) (i j : Fin n) (t : ℝ) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hji : j ≠ i) :
    seg a b j (v + t • bump k n b i) = seg a b j v := by
  unfold seg
  rw [unflatten_add_smul_bump, unflatten_add_smul_bump]
  have hb : ¬(b = b ∧ j = i) := by
    intro h; exact hji h.2
  have ha : ¬(a = b ∧ j = i) := by
    intro h; exact hba h.1.symm
  rw [if_neg hb, if_neg ha, add_zero, add_zero]

/-- **Bumping `b` leaves a segment that does not touch `b` unchanged.** -/
theorem seg_bump_other (c e b : Fin k) (i j : Fin n) (t : ℝ) (v : Fin (k * n) → ℝ)
    (hbc : b ≠ c) (hbe : b ≠ e) :
    seg c e j (v + t • bump k n b i) = seg c e j v := by
  unfold seg
  rw [unflatten_add_smul_bump, unflatten_add_smul_bump]
  have he : ¬(e = b ∧ j = i) := by
    intro h; exact hbe h.1.symm
  have hc : ¬(c = b ∧ j = i) := by
    intro h; exact hbc h.1.symm
  rw [if_neg he, if_neg hc, add_zero, add_zero]

end Lattice.Geo
