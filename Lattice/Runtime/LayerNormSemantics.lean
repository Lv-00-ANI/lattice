import Mathlib
import Lattice.Runtime.ProgramAST

/-!
# `Lattice.Runtime.LayerNormSemantics` — `Instr.layernorm` 的第一条语义定理

## 为什么单独一个文件

`ProgramAST.lean` 已经有 600+ 行，而 `layernorm` 的语义证明与**编码/布局**无关：
它只谈 `applyInstr` 在 `layernorm` 上的值。**把它放进 `ProgramAST` 会让那个文件的主题变混**
——那是"语法与编码"的文件，不是"语义性质"的文件。

## 要证什么，以及为什么它比看起来干净

`layernorm` 的语义是

```lean
| .layernorm ε =>
    let mean : ℝ := (∑ i, x i) / (n : ℝ)
    let var : ℝ := (∑ i, (x i - mean) ^ 2) / (n : ℝ)
    fun j => (x j - mean) / Real.sqrt (var + ε)
```

定义性质是**输出均值为零**：`∑ j, applyInstr x (.layernorm ε) j = 0`。

**关键观察：分母与 `j` 无关。** 所以

    ∑ j, (x j − mean)/√(var+ε) = (∑ j, (x j − mean)) / √(var+ε) = 0 / √(var+ε) = 0

**而这个等式对【任意】 `ε` 成立**——包括使 `√(var+ε) = 0` 的那些——**因为 `0 / 0 = 0`（Lean 的除法是全函数）。**

⇒ ⭐ **这条定理不需要 `hε`，也不需要正的 `var + ε`。** 它只需要 `∑ j (x j − mean) = 0`，
而那只需要 `mean` 等于均值——**即 `n ≠ 0`。**

**这与 `softmax` 的性质形成对照**：那里 Lipschitz 界需要 `ε ≥ 0`，因为界本身依赖于分母的大小。
**均值性质不依赖于分母的【大小】，只依赖于它是常数。**

## 本文件给什么

1. `sum_centered_eq_zero` —— **可推广的那个引理**：任何 `m` 满足 `m * n = ∑ x` 都给出 `∑ (x j − m) = 0`；
2. `applyInstr_layernorm_mean_zero` —— 它的 `layernorm` 实例。

**第 1 条是有意一般化的**：它不谈 `layernorm`，只谈"中心化后的和为零"，
**所以任何做中心化的操作（`layernorm`、`batchnorm`、去均值）都能用它**。
-/

namespace Lattice.Lift.ProgramAST

open Finset

/-- ⭐ **中心化后的和为零**（一般形式）。

若 `m * n = ∑ i, x i`（即 `m` 是 `x` 的均值），则 `∑ j, (x j - m) = 0`。

**为什么一般化 `m` 而不直接写 `(∑ x) / n`**：这样引理不依赖除法的任何性质，
**也不要求 `n ≠ 0` 出现在陈述里**——`n` 只作为 `card univ` 出现在证明中。
`n = 0` 时 `Finset.univ` 为空，两边都是 `0`，**引理仍成立。** -/
theorem sum_centered_eq_zero {n : ℕ} (x : Fin n → ℝ) (m : ℝ) (hm : m * (n : ℝ) = ∑ i, x i) :
    ∑ j, (x j - m) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- goal: (∑ i, x i) - n • m = 0
  rw [nsmul_eq_mul]
  -- goal: (∑ i, x i) - (n:ℝ) * m = 0
  rw [mul_comm] at hm
  linarith

/-- ⭐⭐ **`layernorm` 的输出均值为零**——`Instr.layernorm` 的第一条语义定理。

**不需要 `hε`，也不需要 `0 < var + ε`**：分母与 `j` 无关，所以它能从求和里提出来，
而 `0 / 任何东西 = 0`。**这是"均值性质不依赖分母大小"的准确表述。** -/
theorem applyInstr_layernorm_mean_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (ε : ℝ) :
    ∑ j, applyInstr x (Instr.layernorm ε : Instr n) j = 0 := by
  -- name the two derived quantities so the goal is about them, not about the `let` chain
  set mean : ℝ := (∑ i, x i) / (n : ℝ) with hmean
  set var : ℝ := (∑ i, (x i - mean) ^ 2) / (n : ℝ) with hvar
  -- the denominator is constant in `j`, so it factors out of the sum
  have hterm : ∀ j : Fin n,
      applyInstr x (Instr.layernorm ε : Instr n) j = (x j - mean) / Real.sqrt (var + ε) := by
    intro j
    simp only [applyInstr, hmean, hvar]
  -- `mean` really is the mean, so the centred sum vanishes
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hm : mean * (n : ℝ) = ∑ i, x i := by
    rw [hmean]
    field_simp
  have hzero : ∑ j, (x j - mean) = 0 := sum_centered_eq_zero x mean hm
  calc ∑ j, applyInstr x (Instr.layernorm ε : Instr n) j
      = ∑ j, (x j - mean) / Real.sqrt (var + ε) :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = (∑ j, (x j - mean)) / Real.sqrt (var + ε) := (Finset.sum_div ..).symm
    _ = 0 / Real.sqrt (var + ε) := by rw [hzero]
    _ = 0 := zero_div _

end Lattice.Lift.ProgramAST
