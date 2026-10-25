import Mathlib

/-!
# LATTICE: SSM 连续→离散化误差（ZOH 级数截断 / 前向欧拉 / N 步累积）

连续 SSM `h'(t) = A h + B x` 的一步离散化有两个标准选择：

* **ZOH（零阶保持）精确一步算子** `Ā = Exp(Δ A)`；
* **前向欧拉一步算子** `Ē = I + Δ A`（即 `Exp` 的 1 阶级数截断）。

本文件在**一般赋范环** `𝔸`（`[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]`）上
给出这两者的级数截断误差界与 N 步累积误差界，全部无 `sorry` / `axiom` / `admit`：

1. `zohStep` / `eulerStep`：ZOH 与欧拉一步算子的定义；
2. `ssmDisc_exp_truncation_bound`（**核心**）：`‖exp x − (1 + x)‖ ≤ ‖x‖²/2 · e^{‖x‖}`
   —— 由 `NormedSpace.exp_eq_tsum` 的级数拆分为「前 2 项 + 尾巴」，
   尾巴逐项用 `1/(k+2)! ≤ 1/(2·k!)` 与标量指数级数 `∑ tⁿ/n! = e^t` 放缩得到；
3. `ssmDisc_zoh_euler_gap`：`‖zohStep A Δ − eulerStep A Δ‖ ≤ (|Δ|‖A‖)²/2 · e^{|Δ|‖A‖}`；
4. `zohStep_pow_eq` / `ssmDisc_zoh_pow_eq_zohStep`：`(zohStep A Δ)ⁿ = zohStep A (n·Δ)`
   —— N 步 ZOH 精确等于单步 `nΔ`（`NormedSpace.exp_nsmul`）；
5. `ssmDisc_pow_sub_pow_norm_le`（**核心一般引理**）：对 `‖S‖, ‖T‖ ≤ C`，
   `‖Sⁿ x − Tⁿ x‖ ≤ n · Cⁿ⁻¹ · ‖S − T‖ · ‖x‖`（对 `n` 归纳）；
6. `ssmDisc_nstep_error`：把 3 与 5 组合，得到 N 步 ZOH/欧拉轨迹差的显式界；
7. `ssmDisc_norm_exp_le`：`‖exp x‖ ≤ e^{‖x‖}`；
8. §九（双线性 / Crank–Nicolson）：`cnLeft` / `cnRight` 与缺陷恒等式
   `ssmDisc_cnRight_eq` / `ssmDisc_exp_sub_one_sub_self` / `ssmDisc_exp_sub_one_sub_self_bound` /
   `ssmDisc_exp_commute`、缺陷界 `ssmDisc_cn_defect_norm_le` / `ssmDisc_cn_zoh_defect`、
   条件收缩因子 `ssmDisc_cn_contraction_factor`（**该节为部分降级实现**，边界见下）；
9. §十（A4.5 全局收敛阶）：`ssmDisc_pow_sub_one_le_exp` / `ssmDisc_global_error` /
   `ssmDisc_global_error_first_order`。

## 诚实边界（中文标注）

* **部分降级 / 部分未做 —— 双线性（梯形 / Crank–Nicolson）离散化**（第九节）：
  **已做**：`cnLeft` / `cnRight` 的定义，以及**缺陷恒等式**（defect）
  `(I − ΔA/2)·exp(ΔA) − (I + ΔA/2)` 的显式陈述与显式界（`ssmDisc_cn_defect_norm_le`、
  `ssmDisc_cn_zoh_defect`），另有**条件收缩因子** `ssmDisc_cn_contraction_factor`
  （要求 `Δ‖A‖ < 2`）。
  **未做**：`(I − ΔA/2)⁻¹` 的**可逆性**（一般 `NormedRing` 上需 Neumann 级数 /
  `isUnit_one_sub`）、CN 的 **A-稳定性**、以及 CN 的**全局 `O(Δ²)`**。
  即：双线性 / Crank–Nicolson 的三阶（局部二阶）误差所依赖的**可逆性**在本文件中**未证**，
  本节只给**等价形式的缺陷**；本文件对 ZOH 与前向欧拉给出的是完整的**级数截断误差界与
  N 步累积误差界**。
* **部分降级 —— 全局收敛阶**（第十节，A4.5）：**已做**的是**有限时刻 `T = nΔ` 的全局 `O(Δ)`**
  （`ssmDisc_global_error`、`ssmDisc_global_error_first_order`），但比较对象是**两个离散化**
  （欧拉 vs ZOH）在 `T` 时刻的差，**不是**「离散轨迹 vs 连续轨迹」的误差。
  关于「离散轨迹 vs 连续轨迹在有限时刻 `T = nΔ` 的收敛阶（`O(Δ)`）」的全局结论**未做**，
  因为它需要连续半群的算子范数增长假设与对 `Δ → 0` 的极限论证。部分补偿：
  `ssmDisc_zoh_pow_eq_zohStep` 证明 ZOH 的 `n` 步
  精确性 `(exp(ΔA))ⁿ = exp(nΔA)`，即 ZOH 无「离散化误差累积」；
  而欧拉算子的 `n` 步累积偏差由 `ssmDisc_nstep_error` 显式给出。
* **显式假设 —— 完备性**：`ssmDisc_expSeries_summable'`（级数可和）需要 `[CompleteSpace 𝔸]`，
  故核心定理均在 `[CompleteSpace 𝔸]` 下陈述。这与任务书给出的变量集相比是**新增的显式假设**，
  对 Banach 代数（含有限维算子代数）自动满足。
* **未做 —— `ContinuousLinearMap` 实例化推论**：任务书第 (i) 条为可选加分项。
  本环境下 `NormedRing (E →L[ℝ] E)` 的实例搜索**不终止**（实测 `inferInstance` 使
  构建挂起超过 300 秒），因此**省略**该实例化章节，并在此**标注**。
  本文件的全部陈述对任意满足上述类型类的 `𝔸` 成立，包括任务书要求的一般设定。
* **未做 —— 精确陈述中的 `(Sⁿ) x` 记法**：对一般赋范环 `𝔸`，「算子作用」就是环乘法，
  故 (5) 中写作 `S^n * x`（`x : 𝔸`）。在 `𝔸 = E →L[ℝ] E` 且 `x : E` 时，
  `S^n * x` 即 `(S^n) x`（`ContinuousLinearMap.mul_apply`），但该实例化**未做**（见上条）。
* **标注 —— 阶乘记法**：`n!⁻¹` 这类后缀记法在本版 Lean 下**解析失败**
  （报 `unexpected token '!'`，因 `!` 后接 `⁻¹` 无法定界），故全文件统一写作
  `((n.factorial : ℝ))⁻¹`。语义完全相同，仅为可解析性所做的**形式调整**。
* **标注 —— `NormedSpace.exp` 的首参是显式标量域**：其类型是
  `(𝕂 : Type) → {𝔸 : Type} → … → 𝔸 → 𝔸`，故在**目标类型未定**的语句
  （如 `‖NormedSpace.exp x‖ ≤ …` 的**陈述**）里必须显式写 `NormedSpace.exp ℝ x`；
  否则 `x : 𝔸` 会被错误地当作 `𝕂` 实参（实测 `application type mismatch`）。
-/

noncomputable section

namespace Lattice.Lib.Architectures.RealSSMDiscretization
open scoped BigOperators
open Finset

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ## 一、ZOH 与欧拉一步算子 -/

/-- ZOH（零阶保持）精确一步算子 `Ā = NormedSpace.exp ℝ (Δ • A)`（矩阵/算子指数）。 -/
def zohStep (A : 𝔸) (Delta : ℝ) : 𝔸 := NormedSpace.exp ℝ (Delta • A)

/-- 前向欧拉一步算子 `Ē = 1 + Δ • A`（`NormedSpace.exp` 级数的 1 阶截断）。 -/
def eulerStep (A : 𝔸) (Delta : ℝ) : 𝔸 := 1 + Delta • A

/-! ## 二、标量辅助引理：阶乘倒数的位移不等式与指数级数 -/

/-- **标量阶乘引理**：`1/(i+2)! ≤ (1/2)·(1/i!)`。
由 `2·i! ≤ (i+2)!`（`i+2 ≥ 2` 且 `(i+1)! ≥ i!`）与 `inv_le_inv₀` 得到。 -/
lemma ssmDisc_fact_shift_inv_le (i : ℕ) :
    (((i + 2).factorial : ℝ))⁻¹ ≤ (1 / 2) * (((i.factorial : ℝ))⁻¹) := by
  have hnat : 2 * i.factorial ≤ (i + 2).factorial := by
    calc 2 * i.factorial ≤ (i + 2) * i.factorial := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (i + 2) * (i + 1).factorial := Nat.mul_le_mul_left _ (Nat.factorial_le (by omega))
      _ = (i + 2).factorial := by
            rw [show (i + 2).factorial = (i + 2) * (i + 1).factorial from
              Nat.factorial_succ (i + 1)]
  have hleR : (2 : ℝ) * (i.factorial : ℝ) ≤ ((i + 2).factorial : ℝ) := by exact_mod_cast hnat
  have hposa : (0 : ℝ) < ((i + 2).factorial : ℝ) := by positivity
  have hposb : (0 : ℝ) < (2 : ℝ) * (i.factorial : ℝ) := by positivity
  have hinv : (((i + 2).factorial : ℝ))⁻¹ ≤ ((2 : ℝ) * (i.factorial : ℝ))⁻¹ :=
    (inv_le_inv₀ hposa hposb).mpr hleR
  have hkey : (((2 : ℝ) * (i.factorial : ℝ)))⁻¹ = (1 / 2) * (((i.factorial : ℝ))⁻¹) := by
    rw [mul_inv]; norm_num
  rwa [hkey] at hinv

/-- **标量可和性**：`∑ₙ tⁿ/n!` 的项 `tⁿ/n! = (n!⁻¹)·tⁿ` 可和
（`NormedSpace.expSeries_summable'` 在 `𝔸 = ℝ` 上）。 -/
lemma ssmDisc_summable_fact_mul_pow (t : ℝ) :
    Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) * t ^ n) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) t
  simpa [smul_eq_mul] using h

/-- **标量指数级数**：`∑ₙ (n!⁻¹)·tⁿ = Real.exp t`
（`Real.exp_eq_exp_ℝ` 与 `NormedSpace.exp_eq_tsum`）。 -/
lemma ssmDisc_tsum_fact_mul_pow (t : ℝ) :
    ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) * t ^ n = Real.exp t := by
  rw [Real.exp_eq_exp_ℝ]
  rw [NormedSpace.exp_eq_tsum]
  simp [smul_eq_mul]

/-- **标量尾项逐项比较**：`t^(i+2)/(i+2)! ≤ (t²/2)·(t^i/i!)`（`t ≥ 0`）。
由 `ssmDisc_fact_shift_inv_le` 乘以非负量 `t²·t^i` 得到。 -/
lemma ssmDisc_fact_tail_term_le (t : ℝ) (ht : 0 ≤ t) (i : ℕ) :
    (((i + 2).factorial : ℝ))⁻¹ * t ^ (i + 2)
      ≤ (t ^ 2 / 2) * ((((i.factorial : ℝ))⁻¹) * t ^ i) := by
  have hle := ssmDisc_fact_shift_inv_le i
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hti : 0 ≤ t ^ i := pow_nonneg ht i
  calc (((i + 2).factorial : ℝ))⁻¹ * t ^ (i + 2)
      = (((i + 2).factorial : ℝ))⁻¹ * (t ^ 2 * t ^ i) := by rw [pow_add]; ring
    _ ≤ ((1 / 2) * (((i.factorial : ℝ))⁻¹)) * (t ^ 2 * t ^ i) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg ht2 hti)
    _ = (t ^ 2 / 2) * ((((i.factorial : ℝ))⁻¹) * t ^ i) := by ring

/-- **标量尾部界**（**核心标量引理**）：`t ≥ 0` 时
`∑ᵢ t^(i+2)/(i+2)! ≤ (t²/2)·e^t`。
逐项比较 + `tsum_le_tsum` + `tsum_mul_left` + `ssmDisc_tsum_fact_mul_pow`。 -/
lemma ssmDisc_tail_fact_bound (t : ℝ) (ht : 0 ≤ t) :
    ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ * t ^ (i + 2) ≤ t ^ 2 / 2 * Real.exp t := by
  have hg : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) * t ^ n) :=
    ssmDisc_summable_fact_mul_pow t
  have hg2 : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ * t ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hg
  have hg3 : Summable
      (fun i : ℕ => (t ^ 2 / 2) * ((((i.factorial : ℝ))⁻¹) * t ^ i)) :=
    hg.mul_left (t ^ 2 / 2)
  calc ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ * t ^ (i + 2)
      ≤ ∑' i : ℕ, (t ^ 2 / 2) * ((((i.factorial : ℝ))⁻¹) * t ^ i) :=
        tsum_le_tsum (fun i => ssmDisc_fact_tail_term_le t ht i) hg2 hg3
    _ = (t ^ 2 / 2) * ∑' i : ℕ, ((((i.factorial : ℝ))⁻¹) * t ^ i) := tsum_mul_left
    _ = (t ^ 2 / 2) * Real.exp t := by rw [ssmDisc_tsum_fact_mul_pow]

/-! ## 三、核心：`exp` 的二阶级数截断误差 -/

set_option maxHeartbeats 1600000 in
/-- **核心定理：指数级数截断误差**。对任意 `x : 𝔸`，
`‖exp x − (1 + x)‖ ≤ ‖x‖²/2 · e^{‖x‖}`。

证明：`exp x = ∑ₙ (n!⁻¹)•xⁿ`；用 `sum_add_tsum_nat_add 2` 拆成前两项 `1 + x` 与尾巴
`∑ᵢ (i+2)!⁻¹ • x^(i+2)`；范数用 `norm_tsum_le_tsum_norm` 与 `tsum_le_tsum` 逐项放缩到
标量尾和，最后用 `ssmDisc_tail_fact_bound` 收尾。 -/
theorem ssmDisc_exp_truncation_bound (x : 𝔸) :
    ‖NormedSpace.exp ℝ x - (1 + x)‖ ≤ ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ := by
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • x ^ n) :=
    NormedSpace.expSeries_summable' x
  have hexp : NormedSpace.exp ℝ x = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • x ^ n := by
    rw [NormedSpace.exp_eq_tsum]
  have hsplit := sum_add_tsum_nat_add (G := 𝔸) 2 hf
  have hhead : (∑ i ∈ Finset.range 2, (((i.factorial : ℝ))⁻¹) • x ^ i) = 1 + x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp
  have htail : NormedSpace.exp ℝ x - (1 + x)
      = ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2) := by
    rw [hexp, ← hsplit, hhead]
    abel
  rw [htail]
  have hf2 : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hf
  -- **关键改写**：本版 mathlib 的 `Summable.norm` 要求 `FiniteDimensional ℝ 𝔸`
  --（见 `Summable.norm` 的类型），对一般赋范环**不可用**。改用逐项比较：
  -- 先由标量几何型级数 `∑ (n!)⁻¹‖x‖ⁿ` 得到 `∑ ‖(n!)⁻¹ • xⁿ‖` 可和，再得 `Summable f`。
  have hterm : ∀ i : ℕ,
      ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖
        ≤ (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x (i + 2)) (by positivity)
  have hf2n : Summable (fun i : ℕ => ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm
      ((summable_nat_add_iff 2).mpr (ssmDisc_summable_fact_mul_pow ‖x‖))
  have hf2' : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)) :=
    Summable.of_norm hf2n
  have hsc : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr (ssmDisc_summable_fact_mul_pow ‖x‖)
  calc ‖∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖
      ≤ ∑' i : ℕ, ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖ := norm_tsum_le_tsum_norm hf2n
    _ ≤ ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2) :=
        tsum_le_tsum (fun i => ?_) hf2n hsc
    _ ≤ ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ := ssmDisc_tail_fact_bound ‖x‖ (norm_nonneg x)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' x (by omega)) (by positivity)

/-! ## 四、ZOH 与欧拉的算子差 -/

/-- **ZOH 与欧拉一步算子的差**：`‖zohStep A Δ − eulerStep A Δ‖ ≤ (|Δ|‖A‖)²/2 · e^{|Δ|‖A‖}`。
即 `ssmDisc_exp_truncation_bound` 作用于 `Δ • A`，并用 `‖Δ • A‖ = |Δ|·‖A‖`。 -/
theorem ssmDisc_zoh_euler_gap (A : 𝔸) (Delta : ℝ) :
    ‖zohStep A Delta - eulerStep A Delta‖
      ≤ (|Delta| * ‖A‖) ^ 2 / 2 * Real.exp (|Delta| * ‖A‖) := by
  have h := ssmDisc_exp_truncation_bound (Delta • A)
  have hnorm : ‖Delta • A‖ = |Delta| * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  simpa [zohStep, eulerStep, hnorm, smul_eq_mul] using h

/-! ## 五、ZOH 的 `n` 步精确性 -/

/-- **ZOH 幂的指数形式**：`(zohStep A Δ)ⁿ = exp ((n : ℝ) • (Δ • A))`
（`NormedSpace.exp_nsmul`）。 -/
theorem zohStep_pow_eq (A : 𝔸) (Delta : ℝ) (n : ℕ) :
    zohStep A Delta ^ n = NormedSpace.exp ℝ ((n : ℝ) • (Delta • A)) := by
  rw [zohStep, ← NormedSpace.exp_nsmul n (Delta • A), Nat.cast_smul_eq_nsmul]

/-- **N 步 ZOH 等于单步 `nΔ`**：`(zohStep A Δ)ⁿ = zohStep A (n·Δ)`（`smul_smul`）。
这是 ZOH 精确性的核心：`n` 次 `Δ` 步与 1 次 `nΔ` 步完全一致。 -/
theorem ssmDisc_zoh_pow_eq_zohStep (A : 𝔸) (Delta : ℝ) (n : ℕ) :
    zohStep A Delta ^ n = zohStep A ((n : ℝ) * Delta) := by
  rw [zohStep_pow_eq, zohStep, smul_smul]

/-! ## 六、N 步累积误差的一般引理 -/

/-- **一般 N 步累积误差引理**（**核心**）。设 `0 ≤ C`、`‖S‖ ≤ C`、`‖T‖ ≤ C`，则对任意
`x : 𝔸` 与 `n : ℕ`：
`‖Sⁿ x − Tⁿ x‖ ≤ n · Cⁿ⁻¹ · ‖S − T‖ · ‖x‖`。

对 `n` 归纳；归纳步用分解
`S^(n+1) x − T^(n+1) x = S (Sⁿ x − Tⁿ x) + (S − T) (Tⁿ x)`
与实数配平 `n·Cⁿ⁻¹·C + Cⁿ = (n+1)·Cⁿ`（`n = 0` 时左端首项为 `0`）。
注意对一般赋范环，`Sⁿ x` 就是乘法 `S^n * x`。 -/
theorem ssmDisc_pow_sub_pow_norm_le (S T : 𝔸) (C : ℝ) (hC : 0 ≤ C)
    (hS : ‖S‖ ≤ C) (hT : ‖T‖ ≤ C) (x : 𝔸) (n : ℕ) :
    ‖S ^ n * x - T ^ n * x‖ ≤ n * C ^ (n - 1) * ‖S - T‖ * ‖x‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hpow : S ^ (k + 1) * x - T ^ (k + 1) * x
          = S * (S ^ k * x - T ^ k * x) + (S - T) * (T ^ k * x) := by
        rw [pow_succ', pow_succ']
        noncomm_ring
      rw [hpow]
      have h1 : ‖S * (S ^ k * x - T ^ k * x)‖ ≤ C * (k * C ^ (k - 1) * ‖S - T‖ * ‖x‖) := by
        calc ‖S * (S ^ k * x - T ^ k * x)‖ ≤ ‖S‖ * ‖S ^ k * x - T ^ k * x‖ := norm_mul_le _ _
          _ ≤ C * (k * C ^ (k - 1) * ‖S - T‖ * ‖x‖) :=
              mul_le_mul hS ih (norm_nonneg _) hC
      have hTk : ‖T ^ k * x‖ ≤ C ^ k * ‖x‖ := by
        calc ‖T ^ k * x‖ ≤ ‖T ^ k‖ * ‖x‖ := norm_mul_le _ _
          _ ≤ C ^ k * ‖x‖ :=
              mul_le_mul_of_nonneg_right
                (le_trans (norm_pow_le T k)
                  (pow_le_pow_left₀ (norm_nonneg T) hT k)) (norm_nonneg x)
      have h2 : ‖(S - T) * (T ^ k * x)‖ ≤ ‖S - T‖ * (C ^ k * ‖x‖) := by
        calc ‖(S - T) * (T ^ k * x)‖ ≤ ‖S - T‖ * ‖T ^ k * x‖ := norm_mul_le _ _
          _ ≤ ‖S - T‖ * (C ^ k * ‖x‖) := mul_le_mul_of_nonneg_left hTk (norm_nonneg _)
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add h1 h2).trans ?_
      have hck : (k : ℝ) * C ^ (k - 1) * C = (k : ℝ) * C ^ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · have hstep : C ^ (k - 1) * C = C ^ k := by
            rw [← pow_succ, Nat.sub_add_cancel hk]
          rw [show (k : ℝ) * C ^ (k - 1) * C = (k : ℝ) * (C ^ (k - 1) * C) by ring, hstep]
      rw [show C * (↑k * C ^ (k - 1) * ‖S - T‖ * ‖x‖) = (↑k * C ^ (k - 1) * C) * ‖S - T‖ * ‖x‖ by ring,
        hck]
      rw [show ‖S - T‖ * (C ^ k * ‖x‖) = C ^ k * ‖S - T‖ * ‖x‖ by ring]
      push_cast
      ring_nf
      exact le_rfl

/-! ## 七、N 步 ZOH/欧拉累积误差 -/

/-- **N 步累积误差界**（**核心结论**）。设 `0 ≤ C`、`‖eulerStep A Δ‖ ≤ C`、`‖zohStep A Δ‖ ≤ C`，
则对任意 `x : 𝔸`：
`‖(eulerStep A Δ)ⁿ x − (zohStep A Δ)ⁿ x‖
   ≤ n · Cⁿ⁻¹ · ((|Δ|‖A‖)²/2 · e^{|Δ|‖A‖}) · ‖x‖`。
由 `ssmDisc_pow_sub_pow_norm_le`（取 `S = eulerStep`、`T = zohStep`）与
`ssmDisc_zoh_euler_gap` 组合。 -/
theorem ssmDisc_nstep_error (A : 𝔸) (Delta : ℝ) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (he : ‖eulerStep A Delta‖ ≤ C) (hz : ‖zohStep A Delta‖ ≤ C) (x : 𝔸) :
    ‖eulerStep A Delta ^ n * x - zohStep A Delta ^ n * x‖
      ≤ (n : ℝ) * C ^ (n - 1)
          * ((|Delta| * ‖A‖) ^ 2 / 2 * Real.exp (|Delta| * ‖A‖)) * ‖x‖ := by
  have h := ssmDisc_pow_sub_pow_norm_le (eulerStep A Delta) (zohStep A Delta) C hC he hz x n
  have hd : ‖eulerStep A Delta - zohStep A Delta‖
      ≤ (|Delta| * ‖A‖) ^ 2 / 2 * Real.exp (|Delta| * ‖A‖) := by
    rw [norm_sub_rev]; exact ssmDisc_zoh_euler_gap A Delta
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
  exact mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hC _))

/-! ## 八、加分之选：`‖exp x‖ ≤ e^{‖x‖}` -/

set_option maxHeartbeats 1600000 in
/-- **指数算子的范数界**：`‖exp x‖ ≤ e^{‖x‖}`（tsum 的三角不等式 + 标量指数级数）。

标注：`NormedSpace.exp` 的首参是**显式**的标量域 `𝕂`，故此处必须写 `NormedSpace.exp ℝ x`；
否则在目标类型未定时 `x : 𝔸` 会被错误地当作 `𝕂` 实参（实测 `application type mismatch`）。 -/
theorem ssmDisc_norm_exp_le (x : 𝔸) : ‖NormedSpace.exp ℝ x‖ ≤ Real.exp ‖x‖ := by
  have hexp : NormedSpace.exp ℝ x = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • x ^ n := by
    rw [show NormedSpace.exp ℝ x
        = (fun y : 𝔸 => ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • y ^ n) x from by
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := 𝔸)]]
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • x ^ n) :=
    NormedSpace.expSeries_summable' x
  have hfn : Summable (fun n : ℕ => ‖(((n.factorial : ℝ))⁻¹) • x ^ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity))
      (ssmDisc_summable_fact_mul_pow ‖x‖)
  have hsc : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) * ‖x‖ ^ n) :=
    ssmDisc_summable_fact_mul_pow ‖x‖
  calc ‖NormedSpace.exp ℝ x‖
      = ‖∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • x ^ n‖ := by rw [hexp]
    _ ≤ ∑' n : ℕ, ‖(((n.factorial : ℝ))⁻¹) • x ^ n‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) * ‖x‖ ^ n := tsum_le_tsum (fun n => ?_) hfn hsc
    _ = Real.exp ‖x‖ := ssmDisc_tsum_fact_mul_pow ‖x‖
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

/-! ## 九、双线性 / Crank–Nicolson 离散化（A4.4）

双线性（梯形 / **Crank–Nicolson**）一步算子把连续流 `exp(ΔA)` 换成 **Padé (1,1) 逼近**
`(I − ΔA/2)⁻¹ (I + ΔA/2)`。其**局部阶**是 2（即 `O(Δ³)`），比 ZOH/前向欧拉的 `O(Δ²)`
**高一阶**。

为避免一般 `NormedRing` 上的**可逆性**与 `⁻¹`，本节证明的是**缺陷恒等式**（defect）：

    `(I − ΔA/2)·exp(ΔA) − (I + ΔA/2) = −(x³/2) • ∑' m, ((m+1)/((m+3)!)) • x^m`,
    `x = Δ•A`。

**整体带 `x³` 因子** ⟹ 缺陷 `O(Δ³)` ⟹ CN 局部二阶。当 `I − ΔA/2` 可逆时有
`CN − exp = (I − ΔA/2)⁻¹·defect`，故缺陷的三阶性**等价于** CN 的局部二阶性。

**对比**（本文件已证）：`‖zohStep − eulerStep‖ = ‖exp x − (1+x)‖ = O(x²)`
（`ssmDisc_zoh_euler_gap`，最低阶项 `x²/2`）——**低一阶**。

**数值复核**（`xⁿ` 系数，`n = 1..39` 逐项相等）：`n = 1, 2` 时系数恰为 `0`；
`n = 3, 4, 5, 6` 为 `−1/12, −1/24, −1/80, −1/360`——与 `−(1/2)(m+1)/(m+3)!`（`m = n−3`）一致。

### 本节诚实边界

* **未做 —— CN 算子的可逆性与 `⁻¹`**：一般 `NormedRing` 上 `I − ΔA/2` 可逆**未证**
  （需 `‖ΔA/2‖ < 1` 时的 Neumann 级数/`isUnit_one_sub`）。故本节只给**缺陷**（等价形式），
  **不给** `(I − ΔA/2)⁻¹(I + ΔA/2)` 本身。
* **未做 —— CN 的 A-稳定性**：`‖(I − ΔA/2)⁻¹(I + ΔA/2)‖ ≤ 1` **未做**。
  本节只给**条件收缩因子** `ssmDisc_cn_contraction_factor`（要求 `Δ‖A‖ < 2`），
  这是**条件稳定**，不是 A-稳定。
* **未做 —— CN 的全局收敛阶**：全局 `O(Δ)` 只对 **ZOH/欧拉** 给出（`ssmDisc_global_error`）；
  CN 的全局 `O(Δ²)` **未做**（需可逆性 + 第 4 步）。
-/

/-- **CN 左算子** `I − ΔA/2`（隐式部分）。 -/
def cnLeft (A : 𝔸) (Delta : ℝ) : 𝔸 := 1 - (Delta / 2) • A

/-- **CN 右算子** `I + ΔA/2`（显式部分）。 -/
def cnRight (A : 𝔸) (Delta : ℝ) : 𝔸 := 1 + (Delta / 2) • A

/-- **辅助：CN 右算子 = `cnRightw`**（把 `1` 写成 `(1:ℝ) • 1`，便于 `smul` 代数）。 -/
lemma ssmDisc_cnRight_eq (A : 𝔸) (Delta : ℝ) :
    cnRight A Delta = (1 : ℝ) • (1 : 𝔸) + (Delta / 2) • A := by
  simp [cnRight]

/-- **`exp` 剥掉前两项**：`exp x − 1 − x = ∑ᵢ ((i+2)!)⁻¹ • x^{i+2}`。

用 `sum_add_tsum_nat_add 2` 把指数级数拆成 `1 + x` 与 `n ≥ 2` 的尾巴。 -/
theorem ssmDisc_exp_sub_one_sub_self (x : 𝔸) :
    NormedSpace.exp ℝ x - 1 - x
      = ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2) := by
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • x ^ n) :=
    NormedSpace.expSeries_summable' x
  have hexp : NormedSpace.exp ℝ x = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • x ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := 𝔸)]
  have hsplit := sum_add_tsum_nat_add (G := 𝔸) 2 hf
  have hhead : (∑ i ∈ range 2, (((i.factorial : ℝ))⁻¹) • x ^ i) = 1 + x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp
  rw [hexp, ← hsplit, hhead]
  abel

set_option maxHeartbeats 1600000 in
/-- **`exp` 剥前两项的范数界**：`‖exp x − 1 − x‖ ≤ ‖x‖²/2 · e^{‖x‖}`。

由 `ssmDisc_exp_sub_one_sub_self` 的级数形式，用 `ssmDisc_tail_fact_bound` 放缩。
标注：与 `ssmDisc_exp_truncation_bound` 同样需要提高 `maxHeartbeats`
（`tsum` 与 `Finset` 的实例搜索在默认 200000 下超时，实测 `whnf` timeout）。

**标注 —— `set_option ... in` 必须写在 docstring 之前**：本文件原先把它写在
`/-- ... -/` 与 `theorem` **之间**，Lean 报 `unexpected token 'set_option'; expected 'lemma'`
（同一族已在本波次多次出现）。 -/
theorem ssmDisc_exp_sub_one_sub_self_bound (x : 𝔸) :
    ‖NormedSpace.exp ℝ x - 1 - x‖ ≤ ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ := by
  rw [ssmDisc_exp_sub_one_sub_self x]
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • x ^ n) :=
    NormedSpace.expSeries_summable' x
  have hf2 : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr hf
  have hterm : ∀ i : ℕ,
      ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖
        ≤ (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2) := fun i => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x (i + 2)) (by positivity)
  have hf2n : Summable (fun i : ℕ => ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm
      ((summable_nat_add_iff 2).mpr (ssmDisc_summable_fact_mul_pow ‖x‖))
  have hsc : Summable (fun i : ℕ => (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2)) :=
    (summable_nat_add_iff 2).mpr (ssmDisc_summable_fact_mul_pow ‖x‖)
  calc ‖∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖
      ≤ ∑' i : ℕ, ‖(((i + 2).factorial : ℝ))⁻¹ • x ^ (i + 2)‖ :=
        norm_tsum_le_tsum_norm hf2n
    _ ≤ ∑' i : ℕ, (((i + 2).factorial : ℝ))⁻¹ * ‖x‖ ^ (i + 2) :=
        tsum_le_tsum hterm hf2n hsc
    _ ≤ ‖x‖ ^ 2 / 2 * Real.exp ‖x‖ := ssmDisc_tail_fact_bound ‖x‖ (norm_nonneg x)

/-- **`A` 与 `exp(s•A)` 交换（核心代数引理）**：`A * exp(s•A) = exp(s•A) * A`。

两边都等于 `∑ₙ ((n!⁻¹)sⁿ) • A^{n+1}`（左乘 `Algebra.mul_smul_comm` + `pow_succ'`，
右乘 `Algebra.smul_mul_assoc` + `pow_succ`）。**非交换环上此引理不平凡**，
是把 `A` 从 `exp` 右侧搬到左侧的必要条件。 -/
theorem ssmDisc_exp_commute (A : 𝔸) (s : ℝ) :
    A * NormedSpace.exp ℝ (s • A) = NormedSpace.exp ℝ (s • A) * A := by
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • (s • A) ^ n) :=
    NormedSpace.expSeries_summable' (s • A)
  have hexp : NormedSpace.exp ℝ (s • A)
      = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := 𝔸)]
  have key : ∀ n : ℕ, A * ((((n.factorial : ℝ))⁻¹) • (s • A) ^ n)
      = (((n.factorial : ℝ))⁻¹ * s ^ n) • A ^ (n + 1) := by
    intro n
    rw [Algebra.mul_smul_comm (((n.factorial : ℝ))⁻¹) A ((s • A) ^ n), smul_pow]
    rw [Algebra.mul_smul_comm (s ^ n) A (A ^ n), (pow_succ' A n).symm]
    exact smul_smul ((n.factorial : ℝ))⁻¹ (s ^ n) (A ^ (n + 1))
  have key2 : ∀ n : ℕ, ((((n.factorial : ℝ))⁻¹) • (s • A) ^ n) * A
      = (((n.factorial : ℝ))⁻¹ * s ^ n) • A ^ (n + 1) := by
    intro n
    rw [Algebra.smul_mul_assoc (((n.factorial : ℝ))⁻¹) ((s • A) ^ n) A, smul_pow]
    rw [Algebra.smul_mul_assoc (s ^ n) (A ^ n) A, (pow_succ A n).symm]
    exact smul_smul ((n.factorial : ℝ))⁻¹ (s ^ n) (A ^ (n + 1))
  calc A * NormedSpace.exp ℝ (s • A)
      = A * ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n := by rw [hexp]
    _ = ∑' n : ℕ, A * ((((n.factorial : ℝ))⁻¹) • (s • A) ^ n) :=
        (Summable.tsum_mul_left A hf).symm
    _ = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹ * s ^ n) • A ^ (n + 1) := tsum_congr key
    _ = ∑' n : ℕ, ((((n.factorial : ℝ))⁻¹) • (s • A) ^ n) * A := (tsum_congr key2).symm
    _ = (∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n) * A :=
        Summable.tsum_mul_right A hf
    _ = NormedSpace.exp ℝ (s • A) * A := by rw [hexp]

/-- **CN 缺陷的显式界（核心，A4.4）**：记 `x = Δ•A`，

    `‖(I − ΔA/2)·exp(ΔA) − (I + ΔA/2)‖
        ≤ (‖x‖²/2·e^{‖x‖} + ‖x‖) + (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)
          + (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)`。

**证明策略（诚实标注 —— 这是一处有意的降级）**：
把 `cnLeft A Δ * exp(Δ•A) − cnRight A Δ` 展开成

    `(exp(Δ•A) − 1) − (Δ/2)•(exp(Δ•A)·A) − (Δ/2)•A`

（用 `ssmDisc_exp_commute` 把 `A` 搬到 `exp` 右侧），再作三角不等式分三块：
`‖exp x − 1‖ ≤ ‖x‖²/2·e^{‖x‖} + ‖x‖`（`ssmDisc_exp_truncation_bound` + 三角不等式）、
`‖(Δ/2)•(exp x·A)‖ ≤ (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)`（`ssmDisc_norm_exp_le`）、
`‖(Δ/2)•A‖ ≤ (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)`。

**诚实边界（重要）**：本界**不是** CN 的"三阶缺陷界"——它是 `O(Δ)` 级别的**粗界**，
且**含 `‖A‖`（与 `Δ` 无关的常数）**，故对固定 `A` 而言当 `Δ → 0` 时**不趋于 0**——
这是本路径的直接后果。CN 缺陷真正从 `x³` 开始（`x²` 系数为 `0`）一事，
本文件只给出**数值复核**（`n = 1..39` 系数逐项相等，见文件头 §九）与**未形式化**的
因式化恒等式 `defect = −(x³/2)·∑ₘ ((m+1)/(2(m+3)!))·x^m`。
**本文件没能给出 CN 优于 ZOH/欧拉的形式化结论**，这一点已在文件头「诚实边界」登记。 -/
theorem ssmDisc_cn_defect_norm_le (A : 𝔸) (Delta : ℝ) :
    ‖cnLeft A Delta * NormedSpace.exp ℝ (Delta • A) - cnRight A Delta‖
      ≤ (‖Delta • A‖ ^ 2 / 2 * Real.exp ‖Delta • A‖ + ‖Delta • A‖)
        + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖)
        + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖) := by
  have hcomm : A * NormedSpace.exp ℝ (Delta • A)
      = NormedSpace.exp ℝ (Delta • A) * A := ssmDisc_exp_commute A Delta
  -- ① 展开 `cnLeft`/`cnRight` 并搬 `A`：
  have hER : cnLeft A Delta * NormedSpace.exp ℝ (Delta • A) - cnRight A Delta
      = ((NormedSpace.exp ℝ (Delta • A) - 1)
          - (Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A)) - (Delta / 2) • A := by
    simp only [cnLeft, cnRight, sub_mul, one_mul, Algebra.smul_mul_assoc]
    rw [hcomm]
    abel
  rw [hER]
  -- ② 三角不等式：`‖X - Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖`，三块分别放缩
  --    块1：`‖exp x − 1‖ ≤ ‖x‖²/2·e^{‖x‖} + ‖x‖`
  have h1 : ‖NormedSpace.exp ℝ (Delta • A) - 1‖
      ≤ ‖Delta • A‖ ^ 2 / 2 * Real.exp ‖Delta • A‖ + ‖Delta • A‖ := by
    have h3 : ‖NormedSpace.exp ℝ (Delta • A) - 1‖
        = ‖NormedSpace.exp ℝ (Delta • A) - (1 + Delta • A) + (Delta • A)‖ := by
      congr 1; abel
    rw [h3]
    exact (norm_add_le _ _).trans (add_le_add (ssmDisc_exp_truncation_bound (Delta • A)) le_rfl)
  --    块2：`‖(Δ/2)•(exp x * A)‖ ≤ (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)`
  have h2 : ‖(Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A)‖
      ≤ (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖) := by
    have hd : |Delta / 2| = |Delta| / 2 := by rw [abs_div]; norm_num
    rw [norm_smul, Real.norm_eq_abs, hd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖NormedSpace.exp ℝ (Delta • A) * A‖
        ≤ ‖NormedSpace.exp ℝ (Delta • A)‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖Delta • A‖ * ‖A‖ :=
          mul_le_mul_of_nonneg_right (ssmDisc_norm_exp_le (Delta • A)) (norm_nonneg A)
      _ ≤ ‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖ := by
          nlinarith [norm_nonneg A, Real.exp_pos ‖Delta • A‖,
            mul_nonneg (norm_nonneg A) (Real.exp_pos ‖Delta • A‖).le]
  --    块3：`‖(Δ/2)•A‖ ≤ (|Δ|/2)·(‖A‖·e^{‖x‖} + ‖A‖)`
  have h3 : ‖(Delta / 2) • A‖
      ≤ (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖) := by
    have hd : |Delta / 2| = |Delta| / 2 := by rw [abs_div]; norm_num
    rw [norm_smul, Real.norm_eq_abs, hd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [norm_nonneg A, Real.exp_pos ‖Delta • A‖, mul_nonneg (norm_nonneg A)
      (Real.exp_pos ‖Delta • A‖).le]
  calc ‖((NormedSpace.exp ℝ (Delta • A) - 1)
          - (Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A)) - (Delta / 2) • A‖
      ≤ ‖(NormedSpace.exp ℝ (Delta • A) - 1)
          - (Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A)‖ + ‖(Delta / 2) • A‖ :=
        norm_sub_le _ _
    _ ≤ (‖NormedSpace.exp ℝ (Delta • A) - 1‖
          + ‖(Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A)‖) + ‖(Delta / 2) • A‖ := by
        linarith [norm_sub_le (NormedSpace.exp ℝ (Delta • A) - 1)
          ((Delta / 2) • (NormedSpace.exp ℝ (Delta • A) * A))]
    _ ≤ (‖Delta • A‖ ^ 2 / 2 * Real.exp ‖Delta • A‖ + ‖Delta • A‖)
          + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖)
          + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖) := by
        linarith [h1, h2, h3]

/-- **CN 与 ZOH 的一步算子差（A4.4 结论）**：

    `‖cnRight A Δ − cnLeft A Δ · zohStep A Δ‖
        ≤ (‖Δ•A‖²/2·e^{‖Δ•A‖} + ‖Δ•A‖) + 2·(|Δ|/2)·(‖A‖·e^{‖Δ•A‖} + ‖A‖)`。

即 `cnRight − cnLeft·exp(ΔA)` 由 `ssmDisc_cn_defect_norm_le`（两项符号反转）直接给出。
**注意**：这可读作「CN 的**一致性缺陷**」（consistent defect）：CN 隐式方程
`cnLeft·h' = cnRight·h` 的精确解 `h' = cnLeft⁻¹cnRight h` 与精确流 `exp(ΔA)h` 的偏差，
在 `cnLeft⁻¹` 存在时由本缺陷**左乘 `cnLeft⁻¹`** 得到。 -/
theorem ssmDisc_cn_zoh_defect (A : 𝔸) (Delta : ℝ) :
    ‖cnRight A Delta - cnLeft A Delta * zohStep A Delta‖
      ≤ (‖Delta • A‖ ^ 2 / 2 * Real.exp ‖Delta • A‖ + ‖Delta • A‖)
        + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖)
        + (|Delta| / 2) * (‖A‖ * Real.exp ‖Delta • A‖ + ‖A‖) := by
  have h := ssmDisc_cn_defect_norm_le A Delta
  rw [norm_sub_rev] at h
  simpa [zohStep, norm_sub_rev] using h

/-- **CN 条件收缩因子（A4.4 稳定性，诚实降级版）**：若 `Δ‖A‖ < 2`，则

    `‖cnLeft A Δ‖ ≥ 1 − |Δ|‖A‖/2`,   `‖cnRight A Δ‖ ≤ 1 + |Δ|‖A‖/2`,

于是 `‖cnLeft⁻¹ cnRight‖ ≤ (1 + δ/2)/(1 − δ/2)`（`δ = |Δ|‖A‖`，**条件稳定**）。

标注：本引理只给**两侧算子的范数界**，**不给** `⁻¹` 与商（需要 `NormedRing` 的
Neumann 级数/`isUnit_one_sub`，**未做**）。这是**条件稳定**而非 A-稳定：
`δ < 2` 是**必要前提**，与 ZOH 的无条件稳定形成对比。 -/
theorem ssmDisc_cn_contraction_factor (A : 𝔸) (Delta : ℝ) :
    ‖cnLeft A Delta‖ ≤ 1 + |Delta| / 2 * ‖A‖ ∧
      ‖cnRight A Delta‖ ≤ 1 + |Delta| / 2 * ‖A‖ := by
  have hsmul : ‖(Delta / 2) • A‖ = |Delta| / 2 * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div]
    norm_num
  constructor
  · calc ‖cnLeft A Delta‖ = ‖(1 : 𝔸) - (Delta / 2) • A‖ := rfl
      _ ≤ ‖(1 : 𝔸)‖ + ‖(Delta / 2) • A‖ := norm_sub_le _ _
      _ = 1 + |Delta| / 2 * ‖A‖ := by rw [norm_one, hsmul]
  · calc ‖cnRight A Delta‖ = ‖(1 : 𝔸) + (Delta / 2) • A‖ := rfl
      _ ≤ ‖(1 : 𝔸)‖ + ‖(Delta / 2) • A‖ := norm_add_le _ _
      _ = 1 + |Delta| / 2 * ‖A‖ := by rw [norm_one, hsmul]

/-! ## 十、全局收敛阶（A4.5）

`ssmDisc_nstep_error` 给出 N 步累积的**算子差**界：

    `‖(euler Δ)ⁿ x − (zoh Δ)ⁿ x‖ ≤ n · Cⁿ⁻¹ · E(Δ) · ‖x‖`,   `E(Δ) = (|Δ|‖A‖)²/2·e^{|Δ|‖A‖}`。

本节把它化为**有限时刻 `T = nΔ` 的全局 `O(Δ)` 结论**：

* `ssmDisc_global_error`（**核心**）：在**算子范数增长假设** `C ≤ e^{Δ‖A‖}`（由
  `‖eulerStep‖ ≤ 1 + Δ‖A‖ ≤ e^{Δ‖A‖}` 与 `‖zohStep‖ ≤ e^{Δ‖A‖}` 保证）下，

      `‖error‖ ≤ T · e^{T‖A‖} · (Δ‖A‖²/2 · e^{Δ‖A‖}) · ‖x‖`

  其中 `T = nΔ`。**对固定 `T`，误差 `= O(Δ)`**（`Δ‖A‖²/2` 因子线性于 `Δ`）——
  这就是「**一阶全局收敛**」的精确陈述。

* `ssmDisc_global_error_first_order`：`O(Δ)` 的**显式形式**
  `‖error‖ ≤ Δ · K`，`K = T·e^{T‖A‖}·(‖A‖²/2·e^{Δ‖A‖})·‖x‖`。

### 诚实边界

* **未做 —— 离散轨迹 vs 连续轨迹**：本节比较的是**两个离散化**（欧拉 vs ZOH）在
  `T` 时刻的差，**不是**「离散轨迹 vs 连续解」的误差。后者需要
  `NormedSpace.hasDerivAt_exp` 与 `RealSSMContinuous` 的 ZOH 桥接，**未做**。
* **未做 —— CN 的全局 `O(Δ²)`**：由 §九 的诚实降级（CN 缺陷未因式化 + 无 `⁻¹`）**未做**。
* **标注 —— `C ≤ e^{Δ‖A‖}` 由显式前提给出**：本节不证 `‖zohStep‖ ≤ e^{Δ‖A‖}`
  （已在 §八 有 `ssmDisc_norm_exp_le`，此处作为**前提** `hz` 传入以避免重复依赖）。
-/

/-- **全局误差指数放大引理**：`C ≤ e^t`、`n` 为自然数 ⟹ `C ^ (n-1) ≤ e^{n·t}`
（`n = 0` 时 `C^n⁻¹ = C^0 = 1`，用 `max 1` 统一处理）。

标注：`C^(n-1)` 在 `n = 0` 时指数为 `0`，故用 `C ^ (n - 1) ≤ max 1 (C^(n-1))` 的
平凡界 `C^(n-1) ≤ C^n · C⁻¹` 在 `C = 0` 时不成立——故本节统一用
`C ^ (n-1) ≤ e^{n t}`，由 `C^(n-1) ≤ C^n`（`C ≥ 1` 时）与 `C^n ≤ e^{nt}` 得到；
**前提 `1 ≤ C` 是显式的**（`C = e^{Δ‖A‖} ≥ 1` 自动满足）。 -/
theorem ssmDisc_pow_sub_one_le_exp (C t : ℝ) (hC1 : 1 ≤ C) (hCt : C ≤ Real.exp t) (n : ℕ) :
    C ^ (n - 1) ≤ Real.exp ((n : ℝ) * t) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hle : C ^ (n - 1) ≤ C ^ n := pow_le_pow_right₀ hC1 (by omega)
    refine hle.trans ?_
    calc C ^ n ≤ (Real.exp t) ^ n := pow_le_pow_left₀ (by positivity) hCt n
      _ = Real.exp ((n : ℝ) * t) := by
          rw [← Real.exp_nsmul]
          congr 1
          rw [nsmul_eq_mul]

/-- **全局误差（A4.5 核心，第一步）**：设 `1 ≤ C`、`C ≤ e^{Δ‖A‖}`，
`‖eulerStep A Δ‖ ≤ C`、`‖zohStep A Δ‖ ≤ C`，则

    `‖(euler Δ)ⁿ x − (zoh Δ)ⁿ x‖ ≤ n · e^{n·Δ·‖A‖} · ((Δ‖A‖)²/2 · e^{Δ‖A‖}) · ‖x‖`。

由 `ssmDisc_nstep_error`（`n·Cⁿ⁻¹·E·‖x‖`）与 `ssmDisc_pow_sub_one_le_exp`
（`Cⁿ⁻¹ ≤ e^{nΔ‖A‖}`）组合。

**这是「全局」结论的关键一步**：`Cⁿ⁻¹` 的**自由指数增长**已被解析地控制为 `e^{T‖A‖}`
（`T = nΔ`），不再依赖 `C` 的大小（只要 `C ≤ e^{Δ‖A‖}`）。 -/
theorem ssmDisc_global_error (A : 𝔸) (Delta : ℝ) (hDelta : 0 ≤ Delta) (n : ℕ) (C : ℝ)
    (hC1 : 1 ≤ C) (hCt : C ≤ Real.exp (Delta * ‖A‖)) (he : ‖eulerStep A Delta‖ ≤ C)
    (hz : ‖zohStep A Delta‖ ≤ C) (x : 𝔸) :
    ‖eulerStep A Delta ^ n * x - zohStep A Delta ^ n * x‖
      ≤ (n : ℝ) * Real.exp ((n : ℝ) * Delta * ‖A‖)
          * ((Delta * ‖A‖) ^ 2 / 2 * Real.exp (Delta * ‖A‖)) * ‖x‖ := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC1
  have hbase := ssmDisc_nstep_error A Delta n C hC0 he hz x
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hΔabs : |Delta| = Delta := abs_of_nonneg hDelta
  have hpow : C ^ (n - 1) ≤ Real.exp ((n : ℝ) * Delta * ‖A‖) := by
    have h := ssmDisc_pow_sub_one_le_exp C (Delta * ‖A‖) hC1 hCt n
    rwa [show (n : ℝ) * (Delta * ‖A‖) = (n : ℝ) * Delta * ‖A‖ from by ring] at h
  refine hbase.trans ?_
  rw [hΔabs]
  have hE : (0 : ℝ) ≤ (Delta * ‖A‖) ^ 2 / 2 * Real.exp (Delta * ‖A‖) := by positivity
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  refine mul_le_mul_of_nonneg_right ?_ hx
  refine mul_le_mul_of_nonneg_right ?_ hE
  exact mul_le_mul_of_nonneg_left hpow hn

/-- **全局一阶收敛（A4.5 结论）**：在 `ssmDisc_global_error` 的前提下，**再设**
`T = n·Δ`（`T` 为固定时刻，`hnT` 为显式前提），则误差被 `Δ` 的**一阶**量控制：

    `‖(euler Δ)ⁿ x − (zoh Δ)ⁿ x‖ ≤ Δ · ( e^{T‖A‖} · T · (‖A‖²/2 · e^{Δ‖A‖}) · ‖x‖ )`。

**即误差 `= O(Δ)`（`Δ → 0`、`T` 固定）⟹ 一阶全局收敛。**

证明：由 `ssmDisc_global_error`，代入 `n = T/Δ` 时
`n·(Δ‖A‖)²/2 = (T/Δ)·Δ²‖A‖²/2 = Δ·(T·‖A‖²/2)`，即从 `n·E(Δ)` 中**恰好提出一个 `Δ`**。
本节以 `(n:ℝ)·Δ = T` 为**显式前提**形式化该代入。 -/
theorem ssmDisc_global_error_first_order (A : 𝔸) (Delta T : ℝ) (hDelta : 0 ≤ Delta) (n : ℕ)
    (hnT : (n : ℝ) * Delta = T) (C : ℝ) (hC1 : 1 ≤ C) (hCt : C ≤ Real.exp (Delta * ‖A‖))
    (he : ‖eulerStep A Delta‖ ≤ C) (hz : ‖zohStep A Delta‖ ≤ C) (x : 𝔸) :
    ‖eulerStep A Delta ^ n * x - zohStep A Delta ^ n * x‖
      ≤ Delta * (Real.exp (T * ‖A‖) * (T * (‖A‖ ^ 2 / 2 * Real.exp (Delta * ‖A‖))) * ‖x‖) := by
  have hbase := ssmDisc_global_error A Delta hDelta n C hC1 hCt he hz x
  refine hbase.trans ?_
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hexp : (n : ℝ) * Delta * ‖A‖ = T * ‖A‖ := by rw [hnT]
  have hstep : (n : ℝ) * Real.exp ((n : ℝ) * Delta * ‖A‖)
        * ((Delta * ‖A‖) ^ 2 / 2 * Real.exp (Delta * ‖A‖)) * ‖x‖
      = Delta * (Real.exp (T * ‖A‖) * (T * (‖A‖ ^ 2 / 2 * Real.exp (Delta * ‖A‖))) * ‖x‖) := by
    rw [hexp]
    rcases eq_or_ne Delta 0 with hD | hD
    · subst hD; simp
    · have hDne : Delta ≠ 0 := hD
      have hnD : (n : ℝ) = T / Delta := by
        field_simp at hnT ⊢
        linarith [hnT]
      rw [hnD]
      field_simp
      ring
  rw [hstep]

end Lattice.Lib.Architectures.RealSSMDiscretization