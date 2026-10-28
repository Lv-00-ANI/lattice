/-
# 验证的健全性：从「采样点验证」到「全域带界成立」

## 0. 这一节解决什么

`Lattice.Lift.ApproxExact` 建立了「损失界 ⟹ 残差界」。但那仍然假设已知损失是小的。
工程上能拿到的更弱：**在有限个采样点上验证通过了**。

本文件补上这一环：**若残差在 δ-稠密集上为零、且残差是 L-Lipschitz 的，则全域
`|r x| ≤ L·δ`**。

这是「验证回路」的正确性根据：我们只能检查有限个点，公式要给出的正是
「检查过的地方为零 ⟹ 没检查的地方有多差」。

## 1. 证明思路

设 `S` 是 `Ω` 中 δ-稠密的，即每一点 `x ∈ Ω` 都有 `s ∈ Ω ∩ S` 使 `dist x s ≤ δ`；
`r` 在 `Ω` 上 `L`-Lipschitz；`r` 在 `S` 上为零。任取 `x ∈ Ω`：

1. 稠密性给出 `s ∈ Ω`、`s ∈ S`、`dist x s ≤ δ`；
2. `r s = 0`，故 `|r x| = |r x - r s|`；
3. Lipschitz 给出 `|r x - r s| ≤ L · dist x s ≤ L · δ`。

三步都是初等不等式。真正的要点是**稠密性的定义必须保证 `s ∈ Ω`**，
否则 Lipschitz 无法用在 `(x, s)` 上——这不是技术细节，而是命题能否成立的关键：
若 `s ∉ Ω`，`LipschitzOn` 对它一无所知。

## 2. 为什么这是「逼近精确」的核心

| 层 | 陈述 | 可验证性 |
|:--|:--|:--|
| 精确 | `r x = 0` 对**所有** `x ∈ Ω` | ❌ 需检查不可数多个点 |
| **本定理** | `\|r x\| ≤ L·δ` 对**所有** `x ∈ Ω` | ✅ 只需检查有限采样点 |
| `δ = 0` 的极限 | `L·0 = 0`，故 `r x = 0` | ✅ 见 `residual_eq_zero_of_zero_dense` |

**`δ = 0` 时界退化为精确**：`L·0 = 0`，`|r x| ≤ 0` 即 `r x = 0`。
这是界紧的判据（README §3.3 定的相容性检验）：界在端点处不收放。

第 167 轮修正：此处此前写 「verification_gap_vanishes」，**该名字不存在**（实际是
`residual_eq_zero_of_zero_dense`）。

## 3. 泛化

三条定理在**任意半度量空间**上成立：证明只用 `dist` 与 `LipschitzOn` 的结构，
不涉及 `ℝ` 的任何特殊性质。保留 `ℝ` 版本是因为下游 `RealVerifierReliable` 已在用。

## 4. 边界（必须一起说）

- **`LipschitzOn` 不是免费前提**：多项式残差（次数 ≥ 2）只在**有界域**上才有有限
  Lipschitz 常数。无界域上该前提不成立，定理不适用——这是域的约束，不是定理的弱点。
- **`δ`-稠密要求域有界**：`S` 有限时，无界域上不存在 δ-稠密子集。
- **本文不给收敛率**：`δ` 是自由参数，能压多小取决于采样策略，属数值分析，
  不在本定理范围。这一条与 `RealVerifierReliable` 头部记的边界同源。
-/
import Mathlib
import Lattice.Runtime.RealVerifierReliable
open scoped ContinuousLinearMap

namespace Lattice.Lift

/-! ## 一、一般半度量空间上的验证健全性 -/

section General

variable {X : Type*} [PseudoMetricSpace X]

/-- **验证的健全性（一般载体）。**

若 `r` 在 `Ω` 上 `L`-Lipschitz 且在 `δ`-稠密集 `S` 上为零，则 `Ω` 全域 `|r x| ≤ L·δ`。

`hL : 0 ≤ L` 不可省：`L < 0` 时 `L·δ` 可能为负，而 `|r x|` 非负，命题为假。

`hd` 要求 `s ∈ Ω`（不是只要求 `s ∈ S`）：`LipschitzOn` 只在 `Ω` 上有效，
若 `s ∉ Ω`，Lipschitz 条件对 `(x, s)` 一无所知。这一点写进定义而非留给读者推断，
是因为它就是命题成立与否的分界。 -/
theorem residual_le_of_zero_on_dense {r : X → ℝ} {L δ : ℝ} {Ω S : Set X}
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * dist x y)
    (hL : 0 ≤ L)
    (hd : ∀ x ∈ Ω, ∃ s ∈ Ω, s ∈ S ∧ dist x s ≤ δ)
    (h0 : ∀ s ∈ S, r s = 0) :
    ∀ x ∈ Ω, |r x| ≤ L * δ := by
  intro x hx
  obtain ⟨s, hsΩ, hsS, hxs⟩ := hd x hx
  have hEq : |r x| = |r x - r s| := by rw [h0 s hsS, sub_zero]
  rw [hEq]
  exact (hlip x hx s hsΩ).trans (mul_le_mul_of_nonneg_left hxs hL)

/-- **`δ = 0` 的退化：验证健全性变成精确性。**

若采样集在 `Ω` 上 `0`-稠密、`r` 在 `S` 上为零，则 `r` 在 `Ω` 上**处处**为零。
这就是 `ε → 0` 的相容性检验：界在端点处不收放。 -/
theorem eq_zero_of_zero_dense {r : X → ℝ} {L : ℝ} {Ω S : Set X}
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * dist x y)
    (hL : 0 ≤ L)
    (hd : ∀ x ∈ Ω, ∃ s ∈ Ω, s ∈ S ∧ dist x s ≤ 0)
    (h0 : ∀ s ∈ S, r s = 0) :
    ∀ x ∈ Ω, r x = 0 := by
  intro x hx
  have h := residual_le_of_zero_on_dense (r := r) (L := L) (δ := 0) hlip hL hd h0 x hx
  rw [mul_zero] at h
  exact abs_nonpos_iff.mp h

end General

/-! ## 二、`ℝ` 上的形式（与 `RealVerifierReliable` 的词汇对齐） -/

/-- **在稠密采样集上验证为零 ⟹ 全域带界。**

这是 `RealVerifierReliable.SampledVerified`/`DeltaDense` 的直接推论：把
`verifier_reliable_clean` 的 `g` 取为常数零、`ε₀` 取 `0`、`L'` 取 `0`。

它回答的是工程问题：**「我只检查了有限的点，能保证什么？」**
答案是 `|r x| ≤ L·δ`，其中 `L` 是残差的 Lipschitz 常数、`δ` 是采样密度。 -/
theorem residual_uniform_bound_of_zero_on_dense {r : ℝ → ℝ} {L δ : ℝ} {Ω S : Set ℝ}
    (hf : LipschitzOn r L Ω) (hL : 0 ≤ L)
    (hd : DeltaDense S δ Ω) (h0 : ∀ s : ℝ, s ∈ S → r s = 0) :
    ∀ x : ℝ, x ∈ Ω → |r x| ≤ L * δ := by
  intro x hx
  obtain ⟨s, hsΩ, hsS, hxs⟩ := hd x hx
  have hLips : |r x - r s| ≤ L * |x - s| := hf x s hx hsΩ
  have hEq : |r x| = |r x - r s| := by rw [h0 s hsS, sub_zero]
  rw [hEq]
  exact hLips.trans (mul_le_mul_of_nonneg_left hxs hL)

/-- **`δ = 0` 时在 `ℝ` 上退化为精确。** -/
theorem residual_eq_zero_of_zero_dense {r : ℝ → ℝ} {L : ℝ} {Ω S : Set ℝ}
    (hf : LipschitzOn r L Ω) (hL : 0 ≤ L)
    (hd : DeltaDense S 0 Ω) (h0 : ∀ s : ℝ, s ∈ S → r s = 0) :
    ∀ x : ℝ, x ∈ Ω → r x = 0 := by
  intro x hx
  have h := residual_uniform_bound_of_zero_on_dense (r := r) (L := L) (δ := 0)
    hf hL hd h0 x hx
  rw [mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- **非零采样误差的完整界。**

若采样点上已验证到 `ε₀`（即 `|r s| ≤ ε₀` 对 `s ∈ S`），则全域 `|r x| ≤ ε₀ + L·δ`。
这是「采样不完美」时的正确陈述：误差来自两处——采样点本身的误差 `ε₀`，
以及采样点之间的插值误差 `L·δ`。 -/
theorem residual_bound_of_sampled_tolerance {r : ℝ → ℝ} {L ε₀ δ : ℝ} {Ω S : Set ℝ}
    (hf : LipschitzOn r L Ω) (hL : 0 ≤ L) (hε : 0 ≤ ε₀)
    (hd : DeltaDense S δ Ω) (hv : ∀ s : ℝ, s ∈ S → |r s| ≤ ε₀) :
    ∀ x : ℝ, x ∈ Ω → |r x| ≤ ε₀ + L * δ := by
  intro x hx
  obtain ⟨s, hsΩ, hsS, hxs⟩ := hd x hx
  calc |r x| ≤ |r x - r s| + |r s| := by simpa using abs_sub_le (r x) (r s) 0
    _ ≤ L * |x - s| + ε₀ := by
        have := hf x s hx hsΩ
        have := hv s hsS
        linarith
    _ ≤ L * δ + ε₀ := by
        have := mul_le_mul_of_nonneg_left hxs hL
        linarith
    _ = ε₀ + L * δ := by ring

end Lattice.Lift
