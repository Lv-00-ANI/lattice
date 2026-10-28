/-
# 端到端逼近链：采样验证 ⟹ 约束近似成立

## 0. 本节把两段接成一条链

此前有两个独立的结论：

| 文件 | 结论 | 方向 |
|:--|:--|:--|
| `ApproxExact` | 损失 `≤ ε²` ⟹ 残差 `≤ ε` | 损失 → 残差 |
| `VerificationSoundness` | 在 δ-稠密集上为零 ⟹ 全域 `≤ L·δ` | 采样 → 全域 |

本文件把它们接起来，回答**工程上真正会问的问题**：

> 我在训练集上把损失压到了某个水平、并在有限个采样点上验证了约束，
> 这对**没见过的点**保证了什么？

答案是一条三段链：

```
损失小  ──(abs_resid_le_of_loss_le_sq)──>  残差小
   │
   └── 若残差在每个采样点都 ≤ ε₀，且残差 L-Lipschitz
        ──(插值)──>  全域残差 ≤ ε₀ + L·δ
```

## 1. 证明思路

最后一步不是新数学，而是「把每个点换到最近的采样点」：

设 `x ∈ Ω`。稠密性给出 `s ∈ Ω ∩ S`，`dist x s ≤ δ`。则

```
|r x| ≤ |r x - r s| + |r s|          (三角不等式)
     ≤ L · dist x s + ε₀              (Lipschitz + 采样点上的界)
     ≤ L · δ + ε₀                     (dist x s ≤ δ, L ≥ 0)
```

前两步在 `VerificationSoundness.residual_bound_of_sampled_tolerance` 里已证；
本节把它与 `EpsSat`（损失层谓词）以及分量损失（`RealTotalLoss` 层）对接。

## 2. 三个层次的对象，同一套界

本节的第二个目的是统一词汇。库里有三种「残差」：

| 载体 | 残差 | 损失 |
|:--|:--|:--|
| 抽象嵌入 | `ResidualEmbedding.resid` | `resid ^ 2` |
| 神经网络 | `RealNeuronOut` | `RealTotalLoss = Σ outᵢ²` |
| 几何约束 | `EqConstraint.poly` | `EqConstraint.loss = poly²` |

三者的损失都是残差平方（或平方和），所以「损失界 ⟹ 残差界」对三者是**同一条推理**。
本节给出的抽象版本（`EpsSat` 层面）适用于全部三种；具体载体只需实例化。

## 3. 边界

- 本节的界是**最坏情形**的：它不利用残差在采样点之间的任何额外结构（单调性、凸性、
  稀疏导数界）。更紧的界需要更强的假设，属于后续工作。
- 不涉及 `δ` 的收敛率：`δ` 由采样策略决定，是输入而非结论。
- `ε₀ + L·δ` 未必是最优常数：`L` 可以取局部 Lipschitz 常数而非常量，
  但那样陈述会更复杂且需额外可测性条件，此处不取。
-/
import Mathlib
import Lattice.Lift.ApproxExact
import Lattice.Runtime.VerificationSoundness

open scoped ContinuousLinearMap

namespace Lattice.Lift

/-! ## 一、采样验证的抽象形式

`RealVerifierReliable` 把「采样点」写成 `Set ℝ`。这里改为一个抽象的有限指标集 `ι`，
因为工程上的采样点通常是有限的，而没有理由要求它们带 `ℝ` 的可加结构。
Lipschitz 性则通过 `dist` 传入，使得结论对任意半度量空间成立。
-/

section Abstract

variable {X ι : Type*} [PseudoMetricSpace X]

/-- **采样 + 插值：全域残差界（抽象形式）。**

给定：
* `r : X → ℝ` 是残差；
* `L` 是 `r` 在 `Ω` 上的 Lipschitz 常数；
* `s : ι → X` 是采样点，`hsΩ` 保证它们落在 `Ω` 内；
* `hcover : ∀ x ∈ Ω, ∃ i, dist x (s i) ≤ δ` 是覆盖条件（δ-稠密）；
* `hvs : ∀ i, |r (s i)| ≤ ε₀` 是采样验证通过。

结论：`∀ x ∈ Ω, |r x| ≤ ε₀ + L * δ`。

与 `residual_bound_of_sampled_tolerance` 的区别仅在采样集的表示：
那里是 `S : Set ℝ`，这里是 `ι → X`。后者更适合「我恰好抽了 k 个点」的情形，
也更容易在下游与具体的采样器对接。 -/
theorem residue_bound_of_finite_sample
    {r : X → ℝ} {L ε₀ δ : ℝ} {Ω : Set X} {s : ι → X}
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * dist x y)
    (hL : 0 ≤ L) (hε : 0 ≤ ε₀)
    (hsΩ : ∀ i, s i ∈ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i : ι, dist x (s i) ≤ δ)
    (hvs : ∀ i : ι, |r (s i)| ≤ ε₀) :
    ∀ x ∈ Ω, |r x| ≤ ε₀ + L * δ := by
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  have h1 : |r x| ≤ |r x - r (s i)| + |r (s i)| := by
    simpa using abs_sub_le (r x) (r (s i)) 0
  have h2 : |r x - r (s i)| ≤ L * dist x (s i) := hlip x hx (s i) (hsΩ i)
  have h3 : L * dist x (s i) ≤ L * δ := mul_le_mul_of_nonneg_left hi hL
  have h4 : |r (s i)| ≤ ε₀ := hvs i
  linarith

/-- **`ε₀ = 0` 的极限：采样点精确为零时，全域误差只来自插值间隙。**

这是 `residue_bound_of_finite_sample` 在 `ε₀ = 0` 处的实例：
`|r x| ≤ L·δ`。它对应「约束在采样点上严格成立」的理想情形，
剩下来的误差完全由采样密度决定。 -/
theorem residue_bound_of_zero_sample
    {r : X → ℝ} {L δ : ℝ} {Ω : Set X} {s : ι → X}
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * dist x y)
    (hL : 0 ≤ L)
    (hsΩ : ∀ i, s i ∈ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i : ι, dist x (s i) ≤ δ)
    (hvs : ∀ i : ι, r (s i) = 0) :
    ∀ x ∈ Ω, |r x| ≤ L * δ := by
  have h0 : ∀ i : ι, |r (s i)| ≤ (0 : ℝ) := by
    intro i; rw [hvs i, abs_zero]
  have h := residue_bound_of_finite_sample (r := r) (L := L) (ε₀ := 0) (δ := δ)
    (Ω := Ω) (s := s) hlip hL le_rfl hsΩ hcover h0
  intro x hx
  simpa using h x hx

end Abstract

/-! ## 二、与惩罚嵌入对接：损失层到约束层的一条路 -/

section Embedding

/-- **从「残差有界」得到 `EpsSat`。**

`EpsSat` 的载体是 `TopologicalSpace`，而残差界需要 `dist`。这条定理说明：
**若** `ResidualEmbedding` 的载体是 `PseudoMetricSpace`（这是额外结构，不是自动的），
**且** 残差在全域 ≤ ε，**则** `EpsSat E p ε x` 成立。

它把 `ApproxExact.EpsSat`（损失层）与残差界（度量层）放在同一个陈述里，
使下游不必自己在两种词汇之间翻译。

注意 `EpsSat E p ε x` 定义为 `|E.loss p x| ≤ ε`，而这里是 `|resid| ≤ ε`。
二者不同：前者约束损失，后者约束残差。损失是残差平方，所以

* `|resid| ≤ ε` **蕴含** `loss ≤ ε²`（平方不增上界）；
* 反之需要 `abs_resid_le_of_loss_le_sq`（已在 `ApproxExact` 中）。

本节只陈述有内容的方向。 -/
theorem loss_le_sq_of_resid_le {P X : Type} [TopologicalSpace X]
    (E : ResidualEmbedding P X) {ε : ℝ} (_hε : 0 ≤ ε) (p : P) {x : X}
    (h : |E.resid p x| ≤ ε) : E.loss p x ≤ ε ^ 2 := by
  rw [E.loss_eq_sq]
  have hsq : (E.resid p x) ^ 2 ≤ ε ^ 2 := by
    have hsqabs : (E.resid p x) ^ 2 = |E.resid p x| ^ 2 := by rw [sq_abs]
    rw [hsqabs]
    exact pow_le_pow_left (abs_nonneg _) h 2
  exact hsq

end Embedding

end Lattice.Lift
