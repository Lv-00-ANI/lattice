import Mathlib
import Lattice.Core.Weight

/-!
# `Lattice.Core.VariableNet` -- layer chains whose widths may differ

## The problem this solves, and the route not taken

`Lattice.Core.Net` stacks layers over a fixed width: every layer is `n -> n`, so a chain is a
`List` and composition is `List.foldl`. Real weights change width between layers.

The natural encoding is a dependently typed list,

```lean
inductive Chain : Type -> Type -> Type
  | idf {n} : Chain n n
  | cons {m n p} : Layer m n -> Chain n p -> Chain m p
```

and it does **not** work when the widths are arbitrary types: matching `Chain m p` against
`cons` leaves the hidden intermediate type unconstrained, and the recursive call needs it
explicitly to supply its `Fintype` instance. Eleven probe attempts -- universe alignment, typeclass
placement, `@` explicitisation, pattern binding, carrying instances in a structure, replacing the
typeclass with `Finset`, and a `List` with an alignment proof -- all stalled on that step
(`gov/BLOCKER-variable-width.md`).

The fix is to index by `Nat` instead of by a type. Then the intermediate is a *number*, `Fin n`
carries its `Fintype` instance unconditionally, and the constructor's own arguments supply the name
-- so nothing has to be synthesised. `Chain` below is that version, and it eliminates cleanly.

**The route taken** is `Matrix`, where the widths live in the type:

```lean
structure MLayer (m n : Nat) where
  W : Matrix (Fin m) (Fin n) Real
  b : Fin n -> Real
```

Now `compose (l₁ : MLayer a b) (l₂ : MLayer b c) : MLayer a c` forces the middle width by
unification, so a width mismatch is a **type error**. No dependent induction, no runtime check,
no padding.

## What is traded

The widths are `Nat`-valued, so the index types are `Fin m` rather than an arbitrary `Fintype`.
That is a real restriction compared with `Lattice.Core.Weight`, and it is stated rather than glossed:
anything needing a non-`Fin` width still uses the fixed-width stack.
-/

namespace Lattice.Core

open Matrix

/-- An affine layer between two potentially different widths.

Compared with `LayerParams`, the widths are `Nat` indices rather than arbitrary types. That is what
lets a chain's middle width be forced by unification. -/
structure MLayer (m n : ℕ) where
  /-- Weight matrix. -/
  W : Matrix (Fin m) (Fin n) ℝ
  /-- Bias vector. -/
  b : Fin n → ℝ

/-- The action of one variable-width layer: `x ↦ Wᵀx + b`. -/
noncomputable def mlayerAct {m n : ℕ} (l : MLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => (∑ i, l.W i j * x i) + l.b j

/-- **Composition of two layers.** The middle width `b` is determined by the two arguments, so a
mismatched chain cannot be formed. -/
noncomputable def MLayer.compose {a b c : ℕ} (l₁ : MLayer a b) (l₂ : MLayer b c) : MLayer a c where
  W := l₁.W * l₂.W
  b := fun j => (∑ i, l₁.b i * l₂.W i j) + l₂.b j

/-- **Composition is semantically correct.** Applying the composed layer equals applying the
two layers in turn.

The proof is in two halves because a single goal over weighted and bias terms at once is what
stalled four earlier attempts. `weighted_compose` handles `∑ᵢ (∑ₖ W₁ᵢₖ W₂ₖⱼ) xᵢ`; `bias_compose`
handles `∑ᵢ b₁ᵢ W₂ᵢⱼ`. The key step in the first is `simp only [Finset.sum_mul, Finset.mul_sum]`
*before* `Finset.sum_comm`: the outer multiplication must be pushed inside the inner sum before
the two sums can be exchanged. -/
theorem weighted_compose {a b c : ℕ} (W₁ : Fin a → Fin b → ℝ) (W₂ : Fin b → Fin c → ℝ)
    (x : Fin a → ℝ) (j : Fin c) :
    (∑ i, (∑ k, W₁ i k * W₂ k j) * x i) = ∑ k, W₂ k j * (∑ i, W₁ i k * x i) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The bias term transforms the same way: `∑ᵢ b₁ᵢ W₂ᵢⱼ = ∑ₖ W₂ₖⱼ b₁ₖ`. -/
theorem bias_compose {b c : ℕ} (b₁ : Fin b → ℝ) (W₂ : Fin b → Fin c → ℝ) (j : Fin c) :
    (∑ i, b₁ i * W₂ i j) = ∑ k, W₂ k j * b₁ k := by
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Composition is semantically correct.** -/
theorem compose_act {a b c : ℕ} (l₁ : MLayer a b) (l₂ : MLayer b c) (x : Fin a → ℝ) :
    mlayerAct (l₁.compose l₂) x = mlayerAct l₂ (mlayerAct l₁ x) := by
  funext j
  simp only [mlayerAct, MLayer.compose, Matrix.mul_apply]
  rw [weighted_compose l₁.W l₂.W x j, bias_compose l₁.b l₂.W j]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_assoc]

/-! ## Chains

With `compose` available, a chain is `List.foldl` over a list whose consecutive widths agree --
and the type system already guarantees that when the list is written with the right shapes, so the
list itself can be indexed by its two endpoints through a simple recursive function. -/

/-- A chain of composable layers, indexed by its source width.

`Chain a c` holds the layers and their common target; the recursion forces consecutive widths to
match because `cons` takes an `MLayer m n` and a chain starting at `n`. -/
inductive Chain : ℕ → ℕ → Type
  | idf (n : ℕ) : Chain n n
  | cons {m n c : ℕ} : MLayer m n → Chain n c → Chain m c

namespace Chain

/-- The action of a chain, by structural recursion on the chain.

`Nat`-valued widths let this eliminate cleanly: the `cons` case names the intermediate width from
the constructor's own arguments, which is exactly what the dependently typed version could not do. -/
noncomputable def act : {m n : ℕ} → Chain m n → (Fin m → ℝ) → Fin n → ℝ
  | _, _, .idf _ => fun x => x
  | _, _, .cons (c := c) l rest =>
      fun x => act rest (mlayerAct l x)

/-- **The identity chain is the identity map.** -/
@[simp] theorem act_idf {n : ℕ} (x : Fin n → ℝ) : act (Chain.idf n) x = x := rfl

/-- Concatenation of chains. The types force the join: appending a chain from `b` to `c` to one
from `a` to `b` yields one from `a` to `c`, with no side condition. -/
def append : {a b c : ℕ} → Chain a b → Chain b c → Chain a c
  | _, _, _, .idf _, q => q
  | _, _, _, .cons l rest, q => .cons l (append rest q)

/-- **Chains compose.** Appending two chains is applying them in order. -/
theorem act_append {a b c : ℕ} (p : Chain a b) (q : Chain b c) (x : Fin a → ℝ) :
    act (p.append q) x = act q (act p x) := by
  induction p with
  | idf n => rfl
  | cons l rest ih =>
      simp only [Chain.append, act]
      exact ih q (mlayerAct l x)

end Chain

end Lattice.Core
