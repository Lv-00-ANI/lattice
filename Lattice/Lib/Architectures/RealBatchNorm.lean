import Mathlib

/-!
# LATTICE: BatchNorm —— 批归一化缩放不变与推理仿射

规范化调研（research/real-world/norm-topk-family.md）：
BatchNorm 与 LayerNorm **数学同构**（中心化-方差归一化），仅统计量范围不同
（批内 vs token 内）——统一规律覆盖：

  1. 批统计量 1-齐次（bmean(αX)=α·bmean X、bvar(αX)=α²·bvar X）
     ⟹ 批归一化缩放不变：BN(α·X) = BN(X)（α > 0，全批联合）；
  2. 推理 BN 是仿射闭式：y = γ·(x−μ)/√(σ²+ε) + β = a·x + b
     （固定统计量时，衔接 RealIG 仿射/RealLinear）。

注意：批归一化是批耦合的（逐样本缩放不成立，只有全批联合缩放不变），
与 LN/GN 的对照在调研文档。

模型无关：任意批维度、任意特征。
-/

noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 批统计量 -/

def bmean (X : ι → ℝ) : ℝ :=
  (∑ i, X i) / (Fintype.card ι : ℝ)

def bcenter (X : ι → ℝ) : ι → ℝ :=
  fun i => X i - bmean X

def bvar (X : ι → ℝ) : ℝ :=
  ∑ i, (bcenter X i) ^ 2

/-! ## 批归一化 -/

def bnorm (X : ι → ℝ) : ι → ℝ :=
  fun i => bcenter X i / Real.sqrt (bvar X)

/-! ## 引理：批统计量 1-齐次 -/

lemma bmean_scale (X : ι → ℝ) (α : ℝ) :
    bmean (fun i => α * X i) = α * bmean X := by
  unfold bmean
  by_cases hc : (Fintype.card ι : ℝ) = 0
  · simp [hc]
  · calc
      (∑ i, α * X i) / (Fintype.card ι : ℝ) = (α * ∑ i, X i) / (Fintype.card ι : ℝ) := by
        rw [Finset.mul_sum]
      _ = α * ((∑ i, X i) / (Fintype.card ι : ℝ)) := by
        field_simp [hc]

lemma bcenter_scale (X : ι → ℝ) (α : ℝ) :
    bcenter (fun i => α * X i) = fun i => α * bcenter X i := by
  funext i
  unfold bcenter
  calc
    α * X i - bmean (fun j => α * X j) = α * X i - α * bmean X := by rw [bmean_scale X α]
    _ = α * (X i - bmean X) := by ring

lemma bvar_scale (X : ι → ℝ) (α : ℝ) :
    bvar (fun i => α * X i) = α ^ 2 * bvar X := by
  unfold bvar
  have hc : bcenter (fun j => α * X j) = fun i => α * bcenter X i := bcenter_scale X α
  calc
    (∑ i, (bcenter (fun j => α * X j) i) ^ 2) = ∑ i, (α * bcenter X i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc]
    _ = α ^ 2 * ∑ i, (bcenter X i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-! ## 定理一：批归一化缩放不变（统一规律实例化）
α > 0 ⟹ BN(α·X) = BN(X)（全批联合缩放不变）。-/

theorem bnorm_scale_invariant (X : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    bnorm (fun i => α * X i) = bnorm X := by
  funext i
  unfold bnorm
  -- 分子：α·cᵢ；分母：sqrt(α²·v) = α·sqrt(v)
  have hnum : bcenter (fun j => α * X j) i = α * bcenter X i := congrFun (bcenter_scale X α) i
  have hden : Real.sqrt (bvar (fun j => α * X j)) = α * Real.sqrt (bvar X) := by
    rw [bvar_scale X α]
    have hαsq : 0 ≤ α ^ 2 := sq_nonneg α
    have hv : 0 ≤ bvar X := by
      unfold bvar
      exact Finset.sum_nonneg (fun k hk => sq_nonneg _)
    have hsqrt : Real.sqrt (α ^ 2) = α := by
      rw [Real.sqrt_sq_eq_abs α]
      exact abs_of_nonneg (le_of_lt hα)
    calc
      Real.sqrt (α ^ 2 * bvar X) = Real.sqrt (α ^ 2) * Real.sqrt (bvar X) := by
        exact Real.sqrt_mul hαsq (bvar X)
      _ = α * Real.sqrt (bvar X) := by rw [hsqrt]
  calc
    bcenter (fun j => α * X j) i / Real.sqrt (bvar (fun j => α * X j))
        = (α * bcenter X i) / (α * Real.sqrt (bvar X)) := by rw [hnum, hden]
    _ = bcenter X i / Real.sqrt (bvar X) := by
      exact mul_div_mul_left (bcenter X i) (Real.sqrt (bvar X)) (ne_of_gt hα)

/-! ## 定理二：推理 BN 是仿射闭式
固定统计量（μ、σ、γ、β、ε）⟹ 推理 BN 是 x 的仿射函数（衔接 RealIG/RealLinear）。-/

theorem infer_bn_is_affine (μ σ γ β ε : ℝ) :
    (fun x : ℝ => γ * (x - μ) / Real.sqrt (σ ^ 2 + ε) + β) =
    fun x : ℝ => (γ / Real.sqrt (σ ^ 2 + ε)) * x + (β - γ * μ / Real.sqrt (σ ^ 2 + ε)) := by
  funext x
  -- γ(x-μ)/s + β = (γ/s)x + (β - γμ/s)；s = 0 时两侧都退化（ℝ 中 a/0 = 0），仍相等
  by_cases hs : Real.sqrt (σ ^ 2 + ε) = 0
  · simp [hs]
  · field_simp [hs]
    ring

/-! ## 推论：推理 BN 的斜率与截距
斜率 a = γ/√(σ²+ε)，截距 b = β − γμ/√(σ²+ε)——仿射参数可提取（衔接提取方向）。-/

theorem infer_bn_slope_intercept (μ σ γ β ε : ℝ) :
    (fun x : ℝ => γ * (x - μ) / Real.sqrt (σ ^ 2 + ε) + β) =
    fun x : ℝ => (γ / Real.sqrt (σ ^ 2 + ε)) * x + (β - γ * μ / Real.sqrt (σ ^ 2 + ε)) :=
  infer_bn_is_affine μ σ γ β ε

end Lattice
