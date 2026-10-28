import Mathlib

/-!
# LATTICE: 随机化验证 —— 采样验证的概率保证（自适应/随机化验证线）

验证器（采样/蒙特卡洛）的概率理论基础：
对非负损失 f（约束违背的指示/幅度），概率测度 μ 下：

  1. 马尔可夫界：μ{f ≥ ε} ≤ (1/ε)·∫f dμ（f ≥ 0 可积，
     mathlib mul_meas_ge_le_integral_of_nonneg 包装）；
  2. 切比雪夫界：μ{|X − c| ≥ δ} ≤ (1/δ²)·∫(X−c)² dμ
     （马尔可夫应用到 (X−c)²，集合等价 δ ≤ |X−c| ⟺ δ² ≤ (X−c)²）；
  3. 验证概率保证：训练收敛（∫f ≤ ε²）⟹ 违背概率 ≤ ε
     （验证器采样 pass 概率 ≥ 1−ε）——衔接 GD/收敛线。

意义（自适应/随机化验证）：验证器不再需要确定性全域检查——
马尔可夫/切比雪夫给「损失期望界 ⟹ 违背概率界」的概率保证；
训练收敛（RealGradDescent/RealConvergence 的 ε-终止）代入
hE 即得验证 pass 的置信保证。

模型无关：任意概率空间、任意非负损失。
-/

noncomputable section

namespace Lattice

open MeasureTheory

/-! ## 定理一：马尔可夫界
f ≥ 0 可积 ⟹ μ{f ≥ ε} ≤ (1/ε)·∫f（ε > 0）。-/

theorem markov_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    (μ { x | ε ≤ f x }).toReal ≤ (1 / ε) * ∫ x, f x ∂μ := by
  -- 马尔可夫：ε·μ{ε ≤ f} ≤ ∫f
  have hm := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε
  -- ε·μ ≤ ∫f ⟹ μ ≤ (1/ε)·∫f（ε > 0）
  have hm' : (μ { x | ε ≤ f x }).toReal ≤ (∫ x, f x ∂μ) / ε :=
    (le_div_iff₀ hε).mpr (by simpa [mul_comm] using hm)
  simpa [div_eq_mul_inv, one_div, mul_comm] using hm'

/-! ## 定理二：切比雪夫界
X 可积（二阶矩可积）⟹ μ{|X−c| ≥ δ} ≤ (1/δ²)·∫(X−c)²（δ > 0）。-/

theorem chebyshev_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} {X : α → ℝ} {c : ℝ}
    (hX_sq : Integrable (fun x => (X x - c) ^ 2) μ) {δ : ℝ} (hδ : 0 < δ) :
    (μ { x | δ ≤ |X x - c| }).toReal ≤ (1 / δ ^ 2) * ∫ x, (X x - c) ^ 2 ∂μ := by
  -- 集合等价：{δ ≤ |X−c|} = {δ² ≤ (X−c)²}（δ > 0，|·| ≥ 0）
  have hset : { x | δ ≤ |X x - c| } = { x | δ ^ 2 ≤ (X x - c) ^ 2 } := by
    apply Set.ext
    intro x
    constructor
    · intro h
      -- δ ≤ |a| ⟹ δ² ≤ |a|² = a²（δ ≥ 0）
      have habs : |δ| ≤ |X x - c| := by simpa [abs_of_pos hδ] using h
      have hsq : δ ^ 2 ≤ |X x - c| ^ 2 := by
        rw [sq_abs]
        exact sq_le_sq.mpr habs
      simpa [sq_abs] using hsq
    · intro h
      -- δ² ≤ a² = |a|² ⟹ |δ| ≤ |a|（sq_le_sq）⟹ δ ≤ |a|
      have habs : |δ| ≤ |X x - c| := (sq_le_sq.mp (by simpa [sq_abs] using h))
      simpa [abs_of_pos hδ, abs_of_nonneg (abs_nonneg _)] using habs
  rw [hset]
  -- 马尔可夫应用到 g = (X−c)²，阈值 δ²
  have hg_nonneg : 0 ≤ᵐ[μ] fun x => (X x - c) ^ 2 := by
    exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hm := mul_meas_ge_le_integral_of_nonneg hg_nonneg hX_sq (δ ^ 2)
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hm' : (μ { x | δ ^ 2 ≤ (X x - c) ^ 2 }).toReal ≤ (∫ x, (X x - c) ^ 2 ∂μ) / (δ ^ 2) :=
    (le_div_iff₀ hδ2).mpr (by simpa [mul_comm] using hm)
  simpa [div_eq_mul_inv, one_div, mul_comm] using hm'

/-! ## 定理三：验证概率保证
训练收敛（∫f ≤ ε²）⟹ 违背概率 μ{f ≥ ε} ≤ ε（验证 pass 概率 ≥ 1−ε）。-/

theorem verify_probability_guarantee {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : Integrable f μ) {ε : ℝ} (hε : 0 < ε)
    (hE : ∫ x, f x ∂μ ≤ ε ^ 2) :
    (μ { x | ε ≤ f x }).toReal ≤ ε := by
  -- 马尔可夫：μ ≤ (1/ε)∫f ≤ (1/ε)·ε² = ε
  calc
    (μ { x | ε ≤ f x }).toReal ≤ (1 / ε) * ∫ x, f x ∂μ := markov_bound hf_nonneg hf_int hε
    _ ≤ (1 / ε) * ε ^ 2 := mul_le_mul_of_nonneg_left hE (le_of_lt (one_div_pos.mpr hε))
    _ = ε := by
      field_simp [ne_of_gt hε]
      ring

/-! ## 注：自适应/随机化验证闭环
  马尔可夫（定理一）/切比雪夫（定理二）给「损失期望 ⟹ 违背概率」
  的概率保证；验证概率保证（定理三）连接训练收敛：GD/价值迭代
  的 ε-终止（RealConvergence/RealGradDescent）给出 ∫f ≤ ε² 型
  期望界 ⟹ 采样验证 pass 概率 ≥ 1−ε——验证器从确定性全域检查
  升级为概率保证（随机化验证线理论基础）。-/

end Lattice
