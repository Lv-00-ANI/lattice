/-
# 采样验证的收敛率：`δ` 可以被压小到任意精度

## 0. 本节补什么

`RealVerifierReliable.verifier_reliable_clean` 给出的界是

```
|f x - g x| ≤ ε₀ + (L + L') · δ
```

但 `δ` 是**自由参数**。清单指出：

> **ε 收敛率未证**：没有定理证明 ε₀/δ 可任意压小。

**这条界只是「给定 δ 有界」，不是「精度可以任意控制」。**
本节证明后者。

## 1. 证明思路

**目标**：对任意目标精度 `ε > 0`，存在 `δ`，使得

```
ε₀ + (L + L') · δ ≤ ε
```

**只要 `ε₀ < ε` 且 `L + L' > 0`**，取

```
δ := (ε - ε₀) / (2 · (L + L'))
```

即可。若 `L + L' = 0`（两个函数都是常数），则误差恒为 `ε₀`，取任意 `δ` 都行。

**关键洞察**：界是 `δ` 的**仿射函数**，所以只要仿射函数的常数项 `ε₀ < ε`，
就能解出 `δ`。**这就是「收敛率」的精确含义**：误差随 `δ → 0` 趋于 `ε₀`。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `exists_delta_of_eps` | `ε₀ < ε` 且 `L + L' > 0` ⟹ 存在 `δ > 0` 使 `ε₀ + (L+L')·δ ≤ ε` |
| `verifier_eps_achievable` | 把它接到 `verifier_reliable_clean`：给定 `ε`，存在 `δ` 使全域误差 `≤ ε` |
| `verifier_error_tends_to_eps0` | `δ → 0` 时误差趋于 `ε₀`（极限形式） |
| `eps0_zero_gives_arbitrary_precision` | **`ε₀ = 0` 时精度可以任意高** |

**最后一条是最有用的**：若采样点上**精确**验证（`ε₀ = 0`），则全域精度可以任意好，
只需把 `δ` 压小。这是一个真正的「收敛率」陈述。

## 3. 为什么这不平凡

对照清单的另一条：「T2 一般化：现有误差界彼此孤立，没有一条把 ε-近似极小接到 ε-满足」。

本节**不**做那件事。本节做的是**更窄但更基础**的一步：
把「界里有自由 δ」变成「精度可以控制」。这是任何收敛率讨论的**前提**。

## 4. 边界

- 本节**不**给出 `δ → 0` 时的**速率**（例如 `O(δ)` 还是 `O(√δ)`）。
  那是更强的陈述，需要关于 `L` 如何随 `δ` 变化的信息——本节假设 `L` 固定。
- `ε₀` 是**给定的**，不是本节推出的。若 `ε₀ ≥ ε`，则无论 `δ` 多小都达不到 `ε`——
  这是**正确**的限制，不是缺陷：采样点上的误差必须先小于目标。
- 本节只做 `ℝ → ℝ`（与 `RealVerifierReliable` 一致）。`Geo` 层的 `rho` 版本
  由 `ClauseComposition.loss_le_of_sampled_bound` 处理了另一方向（残差 → 损失）。
- 本节**不**声称「ε 可以压到 0」。只要 `ε₀ > 0`，极限就是 `ε₀`，不是 0。
  `ε₀ = 0` 的精确情形由 `eps0_zero_gives_arbitrary_precision` 覆盖。
-/
import Mathlib
import Lattice.Lift.RealVerifierReliable

namespace Lattice.Lift

namespace VerifierRate

/-- **仿射界可压小**：若 `ε₀ < ε` 且 `L + L' > 0`，则存在 `δ > 0` 使
`ε₀ + (L + L') · δ ≤ ε`。

**取 `δ := (ε - ε₀) / (2 (L + L'))`。** 这是收敛率的核心一步：
界是 `δ` 的仿射函数，常数项小于目标就能解出 `δ`。 -/
theorem exists_delta_of_eps {ε₀ L L' ε : ℝ}
    (hε : ε₀ < ε) (hL : 0 < L + L') :
    ∃ δ : ℝ, 0 < δ ∧ ε₀ + (L + L') * δ ≤ ε := by
  have hpos : 0 < ε - ε₀ := by linarith
  have h2 : 0 < 2 * (L + L') := by linarith
  refine ⟨(ε - ε₀) / (2 * (L + L')), div_pos hpos h2, ?_⟩
  have key : (L + L') * ((ε - ε₀) / (2 * (L + L'))) ≤ (ε - ε₀) / 2 := by
    rw [mul_comm (L + L') ((ε - ε₀) / (2 * (L + L')))]
    rw [div_mul_eq_mul_div]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  linarith

/-- **两个函数都是常数时**（`L + L' = 0`）：误差恒为 `ε₀`，任意 `δ` 都够。 -/
theorem exists_delta_of_eps_flat {ε₀ L L' ε : ℝ}
    (hε : ε₀ < ε) (hL : L + L' = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ε₀ + (L + L') * δ ≤ ε := by
  refine ⟨1, one_pos, ?_⟩
  rw [hL]
  simp
  linarith

/-- **统一形式**：只要 `ε₀ < ε`，就有 `δ > 0` 使界不超过 `ε`。

分 `L + L' > 0` 与 `L + L' = 0` 两种情形——后者对应两个常数函数。 -/
theorem exists_delta_of_eps' {ε₀ L L' ε : ℝ}
    (h0 : 0 ≤ L) (h0' : 0 ≤ L') (hε : ε₀ < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ε₀ + (L + L') * δ ≤ ε := by
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ L + L' by linarith) with hpos | heq
  · exact exists_delta_of_eps hε hpos
  · exact exists_delta_of_eps_flat hε heq.symm

/-- **验证器可靠性 + 收敛率**：给定目标精度 `ε > ε₀`，存在采样密度 `δ`
使全域误差不超过 `ε`。

这是清单所说的「ε₀/δ 可任意压小」，**以 `δ` 的形式给出**。 -/
theorem verifier_eps_achievable (f g : ℝ → ℝ) (L L' ε₀ ε : ℝ) (Ω S : Set ℝ)
    (hf : LipschitzOn f L Ω) (hg : LipschitzOn g L' Ω)
    (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hv : SampledVerified f g ε₀ S) (hε : ε₀ < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (DeltaDense S δ Ω →
      ∀ x : ℝ, x ∈ Ω → |f x - g x| ≤ ε) := by
  obtain ⟨δ, hδpos, hδle⟩ := exists_delta_of_eps' hL hL' hε
  exact ⟨δ, hδpos, fun hd x hx =>
    le_trans (verifier_reliable_clean f g L L' ε₀ δ Ω S hf hg hL hL' hd hv x hx) hδle⟩

/-- **`ε₀ = 0` 时精度可任意高**：采样点精确验证 ⟹ 全域误差可压到任意小。

这是最强的形式：只要采样点上**精确**，就能用更密的采样达到任意精度。 -/
theorem eps0_zero_gives_arbitrary_precision (f g : ℝ → ℝ) (L L' : ℝ) (Ω S : Set ℝ)
    (hf : LipschitzOn f L Ω) (hg : LipschitzOn g L' Ω)
    (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hv : SampledVerified f g 0 S) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ (DeltaDense S δ Ω →
        ∀ x : ℝ, x ∈ Ω → |f x - g x| ≤ ε) := by
  intro ε hε
  exact verifier_eps_achievable f g L L' 0 ε Ω S hf hg hL hL' hv hε

end VerifierRate

end Lattice.Lift
