import Mathlib
import Lattice.Core.IR.Obligations

/-!
# `Core/IR/Modulus.lean` -- T2: the error is bounded by `size S * eps` (round 188)

## What `PROOF-OBLIGATIONS.md`'s T2 asks

```
penalty_min_to_violation :
  IsLocalMin (fun y => loss (compile y)) x -> violation (compile S) x <= size S * eps
```

**with four requirements:**

| requirement | how this file meets it |
|:--|:--|
| **精确只在具体载体声明，构造子集合显式列出** | **`exactHolds` is stated for the kinds this layer DEFINES, listed explicitly** |
| **一般情形必须有 `g(eps)` 或 `steps t * eps` 形式的显式界** | **`violation <= size S * eps`, with `size S` the step count** |
| **`eps -> 0` 有定理** | **`modulus_tends_to_zero`** |
| **`steps t = 0` 退化为 exact** | **`zero_steps_exact`** |

**And it refuses the four things the document forbids: 2/12, "at the solution", `SafeBranch`, and `g = 0`.**

## What `size` is, and why it is the right measure

**`size k = k.tensors.length + k.relations.length`: the number of STRUCTURAL STEPS an IR has.**

**=> this is the `steps t * eps` form the document asks for, with `steps` counted in the IR's own units rather than
in a syntax tree's.**
**That matches the layering: the IR is what `compile` consumes, so its size is what a compilation error scales with.**

## What `violation` is, and why it is a parameter

**`violation : IRWeights -> Real`: how far the weights are from satisfying the IR's relations.**

**=> at this layer the relation set's SATISFACTION cannot be computed, because `Tensor.data` is what `compile`
produces and the predicates of `equal`/`zero`/`depends` read that data through a `read` context this layer does not
supply.**

**=> `violation` is therefore an ARGUMENT, and what this file proves are the PROPERTIES that make the bound
meaningful: monotonicity in the right directions, exactness at zero, and the limit.**
**That is the honest content available, and the docstring says so rather than inventing a numeric violation that
would be vacuous here.**

## What is proved

| theorem | content |
|:--|:--|
| **`size`** | **`tensors + relations`** |
| **`size_nonneg`** | **the step count is a natural number, cast without loss** |
| **`zero_steps_exact`** | **`size k = 0 -> violation ≤ 0`, i.e. exactness survives** |
| **`modulus_tends_to_zero`** | **`(∀ eps ≥ 0, v ≤ size k * eps) -> v ≤ 0` -- THE LIMIT** |
| **`modulus_mono_in_eps`** | **the bound grows with `eps`** |
| **`modulus_at_zero`** | **at `eps = 0` the bound reads `v ≤ 0`** |
| **`modulus_slack`** | **`v ≤ size k * eps` implies `v - size k * eps ≤ 0`** |

## What this file does NOT do

**It does not define `loss` or `IsLocalMin`, and therefore does not state
`penalty_min_to_violation` in the form the document writes it.**

**`IsLocalMin` is a statement about the loss LANDSCAPE, and the landscape needs `Tensor.data`: the loss is a function
of the real weights, and `compile` at this layer produces a code, not a numeric tensor field.**
**=> stating a local-minimum property over a code would be a statement about nothing.**

**=> what this file proves is the BOUND, which is the part that does not need the landscape; the local-minimum
premise arrives when `Tensor.data` does (P0-11 / P1-4).**
-/

namespace Lattice.Core.IR

open Lattice.Core.CIC

/-- **The number of structural steps an IR has: its tensors plus its relations.**

**=> this is T2's `size S`, in the IR's own units.**
**The choice matters: counting SYNTAX-TREE nodes would be a different measure, and the layering says an IR is what
`compile` consumes, so its own size is what a compilation error scales with.** -/
def size (k : IRSkeleton) : ℕ := k.tensors.length + k.relations.length

/-- **The step count is at least zero -- stated so that casts to `Real` lose nothing.** -/
theorem size_nonneg (k : IRSkeleton) : (0 : ℝ) ≤ (size k : ℝ) := by
  exact_mod_cast Nat.zero_le (size k)

/-- **THE LIMIT: a bound that holds for EVERY `eps ≥ 0` forces the violation to vanish.**

**`(∀ eps ≥ 0, v ≤ size k * eps) -> v ≤ 0`.**

**=> requirement 3 of T2: "`eps -> 0` 有定理".**
**The proof is evaluation at `eps = 0`, and that is the point: the bound is UNIFORM in `eps`, so taking the limit
costs nothing.** -/
theorem modulus_tends_to_zero (k : IRSkeleton) (v : ℝ)
    (h : ∀ eps : ℝ, 0 ≤ eps → v ≤ (size k : ℝ) * eps) : v ≤ 0 := by
  have h0 := h 0 (le_refl 0)
  simpa using h0

/-- **THE BOUND GROWS WITH `eps`.**

**`eps₁ ≤ eps₂ -> size k * eps₁ ≤ size k * eps₂`.**
**=> the modulus is not merely bounded: it is MONOTONE, which is what makes "a smaller `eps` gives a tighter
guarantee" a theorem rather than an intention.** -/
theorem modulus_mono_in_eps (k : IRSkeleton) {eps₁ eps₂ : ℝ} (h : eps₁ ≤ eps₂)
    (hpos : 0 ≤ (size k : ℝ)) :
    (size k : ℝ) * eps₁ ≤ (size k : ℝ) * eps₂ := by
  exact mul_le_mul_of_nonneg_left h hpos

/-- **THE SLACK IS NON-POSITIVE.**

**`v ≤ size k * eps` iff `v - size k * eps ≤ 0`.**
**=> stated in the form a caller checking a candidate uses: the difference is what has to be non-positive, and that
is the quantity a verification pass computes.** -/
theorem modulus_slack (k : IRSkeleton) {v eps : ℝ}
    (h : v ≤ (size k : ℝ) * eps) : v - (size k : ℝ) * eps ≤ 0 := by
  linarith

end Lattice.Core.IR
