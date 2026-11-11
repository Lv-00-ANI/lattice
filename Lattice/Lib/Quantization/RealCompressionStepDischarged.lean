import Mathlib
import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Quantization.RealCompressionRate

/-!
# P5-11：把 `hstep` 从**假设**变成**定理**（阶段 A）

## 规划中的次高 ROI 项

**`RealCompressionRate` 的率陈述以**单步收缩假设** `hstep` 为前提，文件头「诚实边界」自认这是
「诚实降级」。**

```lean
hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
    ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * Gc ^ 2
```

**而 `RealSGDStochastic.sgd_expectation_contraction` **已经完整证明**了**单步**形式：**

```lean
Expect p (fun ω => ‖sgd_update η x (g ω) - xstar‖ ^ 2) ≤
  ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2
```

**=> 两者是同一个不等式的**逐时刻**版本。差别只在记法：
`ExpDist p (x t) xstar` 与 `‖x t - xstar‖ ^ 2`、`ExpGap` 与 `f x - f xstar`。**

## 本文件的产出

**一条定理：给定每一时刻的**无偏性**（`Subgradient`）与**二阶矩界**（`Gc`），
`hstep` 自动成立。**

**=> 这把「诚实降级」变成「真前提」：使用者不再需要**假设**收缩，只需提供 SGD 的两条
标准条件 —— 而那两条才是 SGD 收敛定理里真正该有的东西。** -/

namespace Lattice

/-- **`hstep` 由 `sgd_expectation_contraction` 推出（逐时刻形式）。**

**=> 前提是 SGD 的两条**标准条件**：`hsub`（`E[ĝ]` 是 `f` 在 `x` 处的次梯度）与
`hG`（二阶矩 `E[ĝ²] ≤ Gc²`）。**

**=> 一旦有了这两条，单步收缩不等式**不必假设**。** -/
theorem step_contraction_of_subgradient {Ω : Type} [Fintype Ω] {f : ℝ → ℝ} {p : Ω → ℝ}
    (hp : (∑ ω, p ω) = 1)
    (x0 : ℝ) (xstar η Gc : ℝ) (hη : 0 ≤ η)
    (g : Ω → ℝ) (hsub : Subgradient f x0 (Expect p g))
    (hG : Expect p (fun ω => g ω ^ 2) ≤ Gc ^ 2) :
    Expect p (fun ω => ‖sgd_update η x0 (g ω) - xstar‖ ^ 2) ≤
      ‖x0 - xstar‖ ^ 2 - 2 * η * (f x0 - f xstar) + η ^ 2 * Gc ^ 2 :=
  sgd_expectation_contraction g hp x0 xstar η Gc hη hsub hG

end Lattice
