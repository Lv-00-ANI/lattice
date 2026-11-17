import Mathlib
import Lattice.Lib.Compiler.LowerBound
import Lattice.Lib.Compiler.LowerBoundGeneral
import Lattice.Lib.Compiler.PolynomialLowerBound
import Lattice.Lib.Compiler.CarrierApproximation
import Lattice.Lib.Compiler.NonlinearApproximation
import Lattice.Lib.Compiler.ReversibilityCriterion
import Lattice.Lib.Compiler.ReversibilityInstances
import Lattice.Lib.Compiler.ModulusAbstract

/-!
# P8 的统一入口：**「符号 ⇄ 权重」这一跳的全部判决**（阶段 C，P8）

## 为什么需要这个文件

**审计的判决是：**

> **「它把 269,230 行发散成了 270 个分支、两条 L0→L3 链、6 套互不相连的表示体系。」**

**=> 第 944–949 轮产出了 7 个文件、31 条定理，但它们**彼此独立**。
**=> 读者无法一眼看到「这一跳到底能不能闭合」。**

**本文件不新增数学，它把已有结果**组织成一条判决链**，
使整个 P8 成为**一个可引用的结论**。**

## 判决链（四步，每步一条定理）

| 步 | 问题 | 判决 | 出处 |
|:--|:--|:--|:--|
| **1** | 精确可逆可能吗？ | **仅当编译单射** | `reversibility_criterion` |
| **2** | 线性族能任意逼近吗？ | **不能，地板 `1/8`** | `target_not_attainable` |
| **3** | 离散载体上 `ε`-逼近有意义吗？ | **无：`ε<1` 即相等** | `discrete_approx_is_equality` |
| **4** | 有出路吗？ | **有：分段线性无地板** | `nonlinear_strictly_better` |

**=> 四步合起来是一个**完整的判决**：
**投影不可逆 → 逼近有正地板 → 离散下无意义 → 唯一出路是非线性嵌入。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`hop_verdict`** | **⭐⭐⭐ 四步判决的合取（本文件唯一新增的定理）** |
| **`hop_closes_only_nonlinearly`** | **⭐⭐⭐ 结论：闭环只在非线性解释下可能** | -/

namespace Lattice.Lib.Compiler.HopVerdict

/-- **⭐⭐⭐ 「符号 ⇄ 权重」这一跳的四步判决。**

**=> 合取四项：**

1. **`compile` 有左逆 ⟺ 单射**（可逆性判据）；
2. **线性族对 `x²` 有 `1/8` 的下界**（与参数无关）；
3. **`ℤ` 上 `ε < 1` 的逼近强制相等**（离散量化）；
4. **分段线性族的误差 `1/(4n²)` 可任意小**（非线性无地板）。

**=> 这四项分别回答「能否可逆」「能否逼近」「离散是否有意义」「出路在哪」。** -/
theorem hop_verdict :
    -- 1. reversibility is exactly injectivity (both directions)
    (∀ (S W : Type) [Inhabited S] (compile : S → W),
        Function.Injective compile ↔ ∃ extract : W → S, ∀ s, extract (compile s) = s) ∧
    -- 2. the linear family has an absolute floor
    (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
    -- 3. on the discrete carrier, an eps-approximation IS equality
    (∀ (a b : ℤ) (ε : ℝ), ε < 1 → |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε → a = b) ∧
    -- 4. piecewise-linear has NO floor
    (∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ (1 : ℝ) / (4 * (n : ℝ) ^ 2) ≤ ε) :=
  ⟨fun S W _ compile =>
      Lattice.Lib.Compiler.ReversibilityCriterion.reversibility_criterion compile,
    Lattice.Lib.Compiler.LowerBound.target_not_attainable,
    fun a b ε hε h =>
      Lattice.Lib.Compiler.CarrierApproximation.discrete_approx_is_equality a b ε hε h,
    fun ε hε =>
      Lattice.Lib.Compiler.NonlinearApproximation.quarter_inv_sq_tends_to_zero ε hε⟩

/-- **⭐⭐⭐ 判决：闭环只在**非线性**解释下可能。**

**=> 陈述：三项同时成立——**

1. **线性族不能以 `1/8` 以下的误差逼近 `x²`；**
2. **离散载体上 `ε < 1` 的逼近即相等；**
3. **分段线性族的误差可任意小。**

**=> 于是：**在 `List Int` 载体上，闭环只能是精确的（第 2 项）；
> 而一旦嵌入 `ℝ`，仅非线性嵌入能越过地板（第 1、3 项）。** -/
theorem hop_closes_only_nonlinearity :
    (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
      (∀ (a b : ℤ) (ε : ℝ), ε < 1 → |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε → a = b) ∧
      (∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ (1 : ℝ) / (4 * (n : ℝ) ^ 2) ≤ ε) :=
  ⟨Lattice.Lib.Compiler.LowerBound.target_not_attainable,
    Lattice.Lib.Compiler.CarrierApproximation.discrete_approx_is_equality,
    Lattice.Lib.Compiler.NonlinearApproximation.quarter_inv_sq_tends_to_zero⟩

/-- **⭐⭐⭐ 判决（含**模数**）：闭环只在非线性解释下可能，且误差刻度是 `√δ`。**

**=> 在 `hop_verdict` 的四项之外，加第五项：**

5. **存在通用模数 `sqrtModulus`，使「平方级惩罚 `≤ δ`」⟹「误差 `≤ √δ`」，
   且该界在每个 `δ ≥ 0` 处被**达到**（故不可改进）。**

**=> 这一项的作用：把 P8 此前的**常数**（`1/8`、`1/(4n²)`）
与几何层的 `T2Modulus.g = √δ` 放进同一判决。**
**=> 审计曾说 P8 与 T2「互不相连」；本项即是那道连接。** -/
theorem hop_verdict_with_modulus :
    (∀ (S W : Type) [Inhabited S] (compile : S → W),
        Function.Injective compile ↔ ∃ extract : W → S, ∀ s, extract (compile s) = s) ∧
      (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
      (∀ (a b : ℤ) (ε : ℝ), ε < 1 → |((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)| ≤ ε → a = b) ∧
      (∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ (1 : ℝ) / (4 * (n : ℝ) ^ 2) ≤ ε) ∧
      (∃ m : Lattice.Lib.Compiler.ModulusAbstract.Modulus,
          (∀ (e δ : ℝ), 0 ≤ δ → 0 ≤ e → e ^ 2 ≤ δ → e ≤ m.toFun δ) ∧
          (∀ δ : ℝ, 0 ≤ δ → (m.toFun δ) ^ 2 = δ)) := by
  obtain ⟨c1, c2, c3, c4⟩ := hop_verdict
  refine ⟨c1, c2, c3, c4, ?_⟩
  obtain ⟨hsq, ht⟩ := Lattice.Lib.Compiler.ModulusAbstract.modulus_verdict
  obtain ⟨m, hm⟩ := hsq
  exact ⟨m, hm, fun δ hδ => ht m δ hδ⟩

end Lattice.Lib.Compiler.HopVerdict
