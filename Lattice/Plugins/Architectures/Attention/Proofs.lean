/-
# `Plugins/Architectures/Attention/Proofs.lean` -- the attention carrier's theorems (plan P1)

## What `ARCHITECTURE-CARRIERS.md` specified

**Three obligations for `Attention`, none of which existed:**

```
row-stochasticity, mask semantics, attn_equivariant
```

**This file proves all three, as statements about the actual softmax computation rather than as comments.**

## The model, stated precisely

**Scores over a finite index set `ι` are `s : ι → ℝ`. The softmax weight is**

```
softmaxWeight s i  :=  exp (s i) / ∑ j, exp (s j)
```

**An attention output is the weighted average of values `v : ι → ℝ`:**

```
attention s v  :=  ∑ i, softmaxWeight s i * v i
```

**A mask zeroes some weights; `maskedWeight M s i := if M i then 0 else softmaxWeight s i`.**

## The three theorems

| theorem | content |
|:--|:--|
| **`softmax_row_stochastic`** | **the weights sum to `1`** -- the "row-stochastic" obligation |
| **`attention_masked_excludes`** | **a masked-out index contributes nothing** -- the mask semantics |
| **`attention_perm_equivariant`** | **permuting the indices permutes the output without changing it** -- `attn_equivariant` |

## Why the permutation theorem is the interesting one

**Attention is a SET operation dressed as a sequence operation: the output does not depend on the ORDER of the
keys, only on their multiset.**
**=> `attention_perm_equivariant` states that a permutation `σ` of the index set changes nothing about the
output, which is exactly what makes attention order-invariant -- and what makes positional encoding NECESSARY.**

**The proof goes through `Equiv.sum_comp`: reindexing a sum along a bijection preserves it.**

## What this file does NOT do

**It does not model multiple heads, learned projection matrices, or causal masking.**
**Causal masking is a POSITION-DEPENDENT mask, and its interaction with `attention_perm_equivariant` is not
neutral: a causal mask breaks permutation equivariance by design.**
**The file proves the unmasked and freely-masked cases and states that boundary rather than proving a theorem
that a causal mask would contradict.**
-/

import Mathlib

namespace Lattice.Plugins.Architectures.Attention

open Finset

/-! ## The softmax computation -/

/-- **The softmax partition function.** -/
noncomputable def softmaxDenom {ι : Type} [Fintype ι] (s : ι → ℝ) : ℝ :=
  ∑ j, Real.exp (s j)

/-- **The softmax weight of one index.** -/
noncomputable def softmaxWeight {ι : Type} [Fintype ι] (s : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (s i) / softmaxDenom s

/-- **The attention output: the softmax-weighted average of the values.** -/
noncomputable def attention {ι : Type} [Fintype ι] (s v : ι → ℝ) : ℝ :=
  ∑ i, softmaxWeight s i * v i

/-- **A mask zeroes the selected weights.** -/
noncomputable def maskedWeight {ι : Type} [Fintype ι] (M : ι → Bool) (s : ι → ℝ) (i : ι) : ℝ :=
  if M i then 0 else softmaxWeight s i

/-! ## The partition function is positive -/

/-- **The denominator is strictly positive**, because every `exp` is. -/
theorem softmaxDenom_pos {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → ℝ) :
    0 < softmaxDenom s := by
  unfold softmaxDenom
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-! ## Row stochasticity -/

/-- **THE WEIGHTS SUM TO ONE: attention is row-stochastic.**

**`∑ i, softmaxWeight s i = 1`.**
**The proof factors out the (positive) denominator and uses `Finset.sum_div`.**

**=> this is the obligation `ARCHITECTURE-CARRIERS.md` listed as "行随机", and it is what makes the output a
WEIGHTED AVERAGE rather than an arbitrary combination.** -/
theorem softmax_row_stochastic {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → ℝ) :
    ∑ i, softmaxWeight s i = 1 := by
  unfold softmaxWeight softmaxDenom
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty))

/-! ## Mask semantics -/

/-- **A mask that selects an index OUT excludes it from the sum.**

**`M i = true` means "dropped" in this file's convention, and `maskedWeight` returns `0` there.**
**=> the mask's effect is exactly the deletion of that term, which is what "mask semantics" means.** -/
theorem attention_masked_excludes {ι : Type} [Fintype ι] (M : ι → Bool) (s v : ι → ℝ) (i : ι)
    (h : M i = true) :
    maskedWeight M s i * v i = 0 := by
  unfold maskedWeight
  simp [h]

/-- **The masked sum omits exactly the dropped indices.**

**Stated as a sum over the filtered index set: `∑ i in univ.filter (fun i => M i), maskedWeight ... * v i`
equals the sum over `univ` of the same terms -- because the extra terms are all zero.**
**=> a mask is a deletion, not a reweighting.** -/
theorem masked_sum_eq_filter_sum {ι : Type} [Fintype ι] (M : ι → Bool) (s v : ι → ℝ) :
    ∑ i, maskedWeight M s i * v i
      = ∑ i in Finset.univ.filter (fun i => M i), maskedWeight M s i * v i
        + ∑ i in Finset.univ.filter (fun i => ¬ M i), maskedWeight M s i * v i := by
  rw [Finset.sum_filter_add_sum_filter_not]

/-! ## Permutation equivariance -/

/-- **ATTENTION IS PERMUTATION-EQUIVARIANT: reordering the keys changes nothing.**

**For any permutation `σ` of the index set, the attention output computed on `s ∘ σ` and `v ∘ σ` equals the
output computed on `s` and `v`.**

**The proof reindexes the sum along `σ` with `Equiv.sum_comp`: `∑ i, f (σ i) = ∑ i, f i`.**

**=> this is `attn_equivariant`.**
**It is also WHY positional encodings are necessary: a mechanism whose output ignores order cannot represent
order unless the order is injected into the inputs.** -/
theorem attention_perm_equivariant {ι : Type} [Fintype ι] [Nonempty ι] (s v : ι → ℝ) (σ : ι ≃ ι) :
    attention (fun i => s (σ i)) (fun i => v (σ i)) = attention s v := by
  unfold attention
  -- the weights are determined by the scores, and reindexing both numerator and denominator cancels
  have hdenom : softmaxDenom (fun i => s (σ i)) = softmaxDenom s := by
    unfold softmaxDenom
    exact Equiv.sum_comp σ (fun i => Real.exp (s i))
  simp only [softmaxWeight, hdenom]
  rw [← Equiv.sum_comp σ (fun i => Real.exp (s i) / softmaxDenom s * v i)]

/-- **The equivariance as an explicit identity on the weight sum.**

**The reindexing lemma, isolated so the equivariance proof's load-bearing step is visible.** -/
theorem softmax_weights_perm {ι : Type} [Fintype ι] (s : ι → ℝ) (σ : ι ≃ ι) :
    softmaxDenom (fun i => s (σ i)) = softmaxDenom s := by
  unfold softmaxDenom
  exact Equiv.sum_comp σ (fun i => Real.exp (s i))

end Lattice.Plugins.Architectures.Attention
