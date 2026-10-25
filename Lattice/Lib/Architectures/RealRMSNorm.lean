import Mathlib

/-!
# LATTICE: RMSNorm 缩放不变性（规范化族实例，模型无关）

transformer 调研的 RMSNorm（LLaMA 系，无均值中心化的 LayerNorm 变体）：
RMSNorm 对输入缩放不敏感（与 LayerNorm 同族性质）：

  RMSNorm(α·x) = RMSNorm(x)   （α > 0）

其中 RMS(x) = sqrt(Σ xᵢ² / n)（root mean square），
RMSNorm(x)ᵢ = xᵢ / RMS(x)。

证明：RMS 的 α 缩放（sqrt(α²·c) = α·sqrt(c)，α ≥ 0）→ 比值消去。

模型无关：任意维度、任意向量值。规范化族（LayerNorm/RMSNorm）统一缩放不变。
-/

noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## RMS（root mean square） -/

def rms (x : ι → ℝ) : ℝ :=
  Real.sqrt ((∑ i, x i ^ 2) / (Fintype.card ι : ℝ))

/-! ## RMSNorm -/

def rmsNorm (x : ι → ℝ) : ι → ℝ :=
  fun i => x i / rms x

/-! ## 引理：RMS 的 α 缩放
RMS(α·x) = α·RMS(x)（α ≥ 0）。-/

lemma rms_scale (x : ι → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    rms (fun i => α * x i) = α * rms x := by
  -- Σ(αxᵢ)² = α²·Σxᵢ²
  have hsum : ∑ i, (α * x i) ^ 2 = α ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold rms
  calc
    Real.sqrt ((∑ i, (α * x i) ^ 2) / (Fintype.card ι : ℝ))
        = Real.sqrt ((α ^ 2 * ∑ i, x i ^ 2) / (Fintype.card ι : ℝ)) := by rw [hsum]
    _ = α * Real.sqrt ((∑ i, x i ^ 2) / (Fintype.card ι : ℝ)) := by
      -- sqrt(α²·c) = α·sqrt(c)：c = (Σxᵢ²)/n ≥ 0
      have hc : 0 ≤ (∑ i, x i ^ 2) / (Fintype.card ι : ℝ) := by
        exact div_nonneg (Finset.sum_nonneg (fun i hi => sq_nonneg _)) (by positivity)
      have hαsq : 0 ≤ α ^ 2 := sq_nonneg α
      have hsqrt : Real.sqrt (α ^ 2) = α := by
        rw [Real.sqrt_sq_eq_abs α]
        exact abs_of_nonneg hα
      rw [mul_div_assoc]
      rw [Real.sqrt_mul hαsq ((∑ i, x i ^ 2) / (Fintype.card ι : ℝ))]
      rw [hsqrt]

/-! ## 定理：RMSNorm 缩放不变性（核心）
α > 0 ⟹ RMSNorm(α·x) = RMSNorm(x)。-/

theorem rmsNorm_scale_invariant (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    rmsNorm (fun i => α * x i) = rmsNorm x := by
  funext i
  unfold rmsNorm
  -- RMS(αx) = α·RMS(x)（α ≥ 0）
  have hrms : rms (fun j => α * x j) = α * rms x := rms_scale x α (le_of_lt hα)
  calc
    (α * x i) / rms (fun j => α * x j) = (α * x i) / (α * rms x) := by rw [hrms]
    _ = x i / rms x := by
      -- α·xᵢ / (α·RMS) = xᵢ / RMS（α ≠ 0）
      have hα0 : α ≠ 0 := ne_of_gt hα
      exact mul_div_mul_left (x i) (rms x) hα0

/-! ## 推论：RMS 正性（供分母非零用）
x 非零（存在非零分量）⟹ RMS(x) > 0。

注：`rmsNorm` 在 Lean 中是全函数（`fun i => x i / rms x`），ℝ 上除法对零分母取
junk 值 0，其「良定」是一条分式语义主张；本引理只保证分母 `rms x` 非零，
**不**声称 ℝ 除法语义上的良好定义。 -/

theorem rms_pos_of_nonzero (x : ι → ℝ) (i : ι) (h : x i ≠ 0) : 0 < rms x := by
  unfold rms
  -- RMS = sqrt(S/n)，S > 0（含正项）
  have hsq : 0 < (x i) ^ 2 := by
    have hn : (x i) ^ 2 ≠ 0 := by
      intro hz
      exact h (sq_eq_zero_iff.mp hz)
    exact lt_of_le_of_ne (sq_nonneg (x i)) (Ne.symm hn)
  have hS : 0 < ∑ j, x j ^ 2 := by
    -- 单项 < 总和
    have hle : (x i) ^ 2 ≤ ∑ j, x j ^ 2 := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j => x j ^ 2) (a := i)
        (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
    exact lt_of_lt_of_le hsq hle
  -- sqrt(S/n) > 0：S > 0 且 n > 0
  have hnpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hc : 0 < (∑ j, x j ^ 2) / (Fintype.card ι : ℝ) := div_pos hS hnpos
  exact Real.sqrt_pos.mpr hc

end Lattice
