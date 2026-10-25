/-
# LATTICE: RealSiluRemainder — M·Z^{n+1}/(n+1)! → 0

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）

## 诚实边界（**标注**）

1. ⭐ 分析腿已焊死（mathlib `FloorSemiring.tendsto_pow_div_factorial_atTop`），**无 sorry**。
2. ⭐ **本文件只证「余项量级 → 0」，不证余项本身** —— 即 `hbound`
   （`|σ z − P z| ≤ M·Z^(n+1)/(n+1)!`）是**传入的假设**（**标注**），**未证**。
   真正的 n 阶余项界由 mathlib `taylor_mean_remainder_bound` 提供，**留待**接线。
3. ⭐ **常数口径**：mathlib 的界分母为 `n!`，本文件为 `(n+1)!`，两者相差 `n+1` 倍
   （取 `M := C·(n+1)` 可对齐）；此为**已标注**的口径差，**未做**统一。
-/

import Mathlib.Analysis.SpecificLimits.Normed
-- ⚠ `FloorSemiring.tendsto_pow_div_factorial_atTop` 定义在
-- `Mathlib.Topology.Algebra.Order.Floor`（:48），**不是** `SpecificLimits.Normed`
-- （后者只提供已弃用的 `Real.*` 别名）。审核报告 §1.3 给了新名字但**未提**需要补此 import。
import Mathlib.Topology.Algebra.Order.Floor
import Lattice.Lib.Architectures.RealSiluSplit
namespace RealSiluRemainder

open RealLimitDiscrete RealSiluSplit

/-- 平移：Z^{n+1}/(n+1)! → 0。 -/
theorem tendsto_Zpow_fact (Z : ℝ) :
    Filter.Tendsto (fun n : ℕ => (Z ^ (n + 1) / ((n + 1).factorial : ℝ)))
      Filter.atTop (nhds 0) := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop Z
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  exact h.comp hshift

/-- **ε 形态**：M·Z^{n+1}/(n+1)! < ε 当 n 足够大。 -/
theorem eps_pow_fact_to_zero (M Z ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) < ε := by
  by_cases hM0 : M = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hM0, zero_mul, zero_div]
    exact hε
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have h1 := tendsto_Zpow_fact Z
    have h2 : Filter.Tendsto
        (fun n : ℕ => (M * (Z ^ (n + 1) / ((n + 1).factorial : ℝ))))
        Filter.atTop (nhds 0) := by
      simpa [mul_zero] using h1.const_mul M
    have h3 : Filter.Tendsto
        (fun n : ℕ => (M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)))
        Filter.atTop (nhds 0) := by
      have : (fun n : ℕ => (M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)))
          = fun n => M * (Z ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
        funext n
        ring
      rw [this]
      exact h2
    have hev : ∀ᶠ n in Filter.atTop,
        (M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) < ε :=
      h3.eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    exact ⟨N, fun n hn => hN n hn⟩

/-- 传递到 `PolyApproxOn`（ε→0 腿）。 -/
theorem polyApprox_eps_to (σ P : ℝ → ℝ) (Z M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n z, |z| ≤ Z →
      |σ z - P z| ≤ M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) :
    PolyApproxOn σ P Z (fun n => M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) where
  bound := hbound
  eps_to := fun ε hε => eps_pow_fact_to_zero M Z ε hM hε

/-! 分析腿已焊死（mathlib `FloorSemiring.tendsto_pow_div_factorial_atTop`）。**无 sorry**。
诚实边界：本文件**未证**余项界本身（`hbound` 为**显式假设**，**标注**）；
n 阶 Taylor 余项**留待**接线 mathlib；分母口径差 `n+1` 倍**已标注**。 -/

end RealSiluRemainder
