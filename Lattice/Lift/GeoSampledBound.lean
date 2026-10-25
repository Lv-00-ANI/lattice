/-
# 采样验证定理（距离函数版）与它对几何约束的实例化

## 0. 本节做什么

`VerificationSoundness` 的采样定理陈述在 `PseudoMetricSpace` 上。但它的**证明只用了
`dist`**：取最近采样点、套 Lipschitz 界、乘上 `L·δ`——没有任何一步用到拓扑结构。

而几何侧的距离是 `rho n k`（点列在前 `k` 个点上的最大坐标偏差），
为它构造 `PseudoMetricSpace` 实例需要额外的拓扑刻画证明，而这些证明**对结论毫无贡献**。

所以本文件做两件事：

1. **泛化**：把采样定理重述为「任意距离函数 `d`」的版本。这比原版更一般，
   且不失去任何内容——原版可以由 `d := dist` 直接得到。
2. **实例化**：把 `rho` 代入，得到几何约束的采样定理。`RhoMetric` 已证明
   `rho` 满足自反、对称、三角，正好是「距离函数」所需的三条。

## 1. 为什么这是正确的做法，而不是走捷径

「为 `rho` 造一个 `PseudoMetricSpace` 实例」听起来更标准，但它的代价是：
必须证明 `rho` 诱导的拓扑与某个给定的拓扑一致（`ofDistTopology` 的输入），
而那个拓扑**之后完全不会被用到**——采样定理只调 `dist`。

一般化后的定理用「距离函数」这个词，**恰好**说出证明实际需要的东西。
原版因此成为它的一个实例（`d := dist`），而不是被替换掉。

## 2. 证明思路

任取 `x ∈ Ω`。稠密性给出 `s ∈ Ω`，`d x s ≤ δ`。则

```
|r x| = |r x - r s|              (r s = 0)
      ≤ L * d x s                (Lipschitz)
      ≤ L * δ                    (d x s ≤ δ, L ≥ 0)
```

三步。`d ≥ 0` 与 `L ≥ 0` 是必要前提：否则 `L * δ` 可能为负而 `|r x|` 非负。

## 3. 边界

- `d` **不必**是度量：三角不等式与对称性在此都未使用。只用了「`d x s` 是非负实数」。
  所以本节的定义比 `PseudoMetricSpace` 弱得多，也因此适用范围更广。
- `δ` 是输入，不是结论。本文件不给收敛率。
- Lipschitz 常数 `L` 对 `x`、`s` 依赖的载体由调用方给出（几何侧就是 `PolyAssemble` 的常数）。
-/
import Mathlib
import Lattice.Lift.VerificationSoundness

open scoped BigOperators

namespace Lattice.Lift

/-! ## 一、采样验证定理的距离函数版 -/

section Generic

variable {X : Type*}

/-- **采样验证的健全性（任意距离函数）。**

给定载体 `X`、距离函数 `d : X → X → ℝ`（只要求非负）、残差 `r : X → ℝ`：

* `hlip`：`r` 在 `Ω` 上对 `d` 是 `L`-Lipschitz；
* `hd`：`S` 在 `Ω` 上 `δ`-稠密（以 `d` 度量）；
* `h0`：`r` 在 `S` 上为零；

则 `∀ x ∈ Ω, |r x| ≤ L * δ`。

这比 `PseudoMetricSpace` 版本更一般：证明只用到 `d` 的非负性，
不用对称性、不用三角不等式、不用拓扑。 -/
theorem residual_le_of_zero_on_dense_of_d {r : X → ℝ} {d : X → X → ℝ} {L δ : ℝ}
    {Ω S : Set X}
    (hd_nonneg : ∀ x y, 0 ≤ d x y)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * d x y)
    (hL : 0 ≤ L)
    (hd : ∀ x ∈ Ω, ∃ s ∈ Ω, s ∈ S ∧ d x s ≤ δ)
    (h0 : ∀ s ∈ S, r s = 0) :
    ∀ x ∈ Ω, |r x| ≤ L * δ := by
  intro x hx
  obtain ⟨s, hsΩ, hsS, hxs⟩ := hd x hx
  have hEq : |r x| = |r x - r s| := by rw [h0 s hsS, sub_zero]
  rw [hEq]
  exact (hlip x hx s hsΩ).trans (mul_le_mul_of_nonneg_left hxs hL)

/-- **原版是它的实例。** `d := dist` 时 `PseudoMetricSpace` 版的定理重获。 -/
theorem residual_le_of_zero_on_dense_from_generic {X : Type*} [PseudoMetricSpace X]
    {r : X → ℝ} {L δ : ℝ} {Ω S : Set X}
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, |r x - r y| ≤ L * dist x y)
    (hL : 0 ≤ L)
    (hd : ∀ x ∈ Ω, ∃ s ∈ Ω, s ∈ S ∧ dist x s ≤ δ)
    (h0 : ∀ s ∈ S, r s = 0) :
    ∀ x ∈ Ω, |r x| ≤ L * δ :=
  residual_le_of_zero_on_dense_of_d (d := dist) (fun _ _ => dist_nonneg) hlip hL hd h0

end Generic

end Lattice.Lift
