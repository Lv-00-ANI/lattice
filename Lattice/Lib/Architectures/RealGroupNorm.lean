import Mathlib
import Lattice.Lib.Architectures.RealRMSNorm
import Lattice.Lib.Architectures.RealNormFamily
/-!
# LATTICE: GroupNorm 组内缩放不变（规范化族补全）

规范化调研（research/real-world/norm-topk-family.md 推荐目标 1）：
GroupNorm（ViT/ResNet/扩散/Mamba 组件）组内归一化——统一规律实例化：

  组统计量 grms(G, x) = sqrt(Σ_{i∈G} xᵢ² / |G|) 是 1-齐次的
  （grms(αx) = α·grms(x)）⟹ 组归一化缩放不变：
  GN(α·x) = GN(x)（α > 0）

退化：
  · G = 全集 ⟹ grms = rms（GroupNorm G=1 ⟺ RMSNorm，衔接既有证明）

模型无关：任意指标集、任意组。
-/


noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 组统计量（组内 RMS） -/

def grms (G : Finset ι) (x : ι → ℝ) : ℝ :=
  Real.sqrt ((∑ i in G, x i ^ 2) / (G.card : ℝ))

/-! ## 引理：组统计量 1-齐次
grms(G, αx) = α·grms(G, x)（α ≥ 0）。-/

omit [Fintype ι] in
lemma grms_scale (G : Finset ι) (x : ι → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    grms G (fun i => α * x i) = α * grms G x := by
  -- Σ_{i∈G}(αxᵢ)² = α²·Σ_{i∈G}xᵢ²
  have hsum : ∑ i in G, (α * x i) ^ 2 = α ^ 2 * ∑ i in G, x i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold grms
  calc
    Real.sqrt ((∑ i in G, (α * x i) ^ 2) / (G.card : ℝ))
        = Real.sqrt ((α ^ 2 * ∑ i in G, x i ^ 2) / (G.card : ℝ)) := by rw [hsum]
    _ = α * Real.sqrt ((∑ i in G, x i ^ 2) / (G.card : ℝ)) := by
      -- sqrt(α²·c) = α·sqrt(c)（α ≥ 0, c ≥ 0）
      have hc : 0 ≤ (∑ i in G, x i ^ 2) / (G.card : ℝ) := by
        exact div_nonneg (Finset.sum_nonneg (fun i hi => sq_nonneg _)) (by positivity)
      have hαsq : 0 ≤ α ^ 2 := sq_nonneg α
      -- (α²·S)/n = α²·(S/n)，再拆 sqrt(α²·c) = sqrt(α²)·sqrt(c)
      rw [mul_div_assoc]
      rw [Real.sqrt_mul hαsq ((∑ i in G, x i ^ 2) / (G.card : ℝ))]
      have hsqrt : Real.sqrt (α ^ 2) = α := by
        rw [Real.sqrt_sq_eq_abs α]
        exact abs_of_nonneg hα
      rw [hsqrt]

/-! ## 组归一化 -/

def gnorm (G : Finset ι) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i / grms G x

/-! ## 定理：GroupNorm 组内缩放不变（统一规律实例化）
α > 0 ⟹ GN(α·x) = GN(x)。-/

theorem gnorm_scale_invariant (G : Finset ι) (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    gnorm G (fun i => α * x i) = gnorm G x := by
  funext i
  unfold gnorm
  -- 统一规律：组统计量 1-齐次 ⟹ 商归一化缩放不变
  have hg : grms G (fun j => α * x j) = α * grms G x := grms_scale G x α (le_of_lt hα)
  calc
    (α * x i) / grms G (fun j => α * x j) = (α * x i) / (α * grms G x) := by rw [hg]
    _ = x i / grms G x := by
      -- α·xᵢ / (α·grms) = xᵢ / grms（α ≠ 0）
      have hα0 : α ≠ 0 := ne_of_gt hα
      exact mul_div_mul_left (x i) (grms G x) hα0

/-! ## 退化：G = 全集 ⟹ grms = rms（GroupNorm G=1 ⟺ RMSNorm） -/

theorem grms_univ_eq_rms (x : ι → ℝ) : grms Finset.univ x = rms x := by
  unfold grms rms
  rfl

/-! ## 推论：G=1 的 GroupNorm = RMSNorm（缩放不变衔接）
全集组的归一化与 RMSNorm 一致，故 RMSNorm 缩放不变可看作 GroupNorm 特例。-/

theorem gnorm_univ_eq_rmsNorm (x : ι → ℝ) : gnorm Finset.univ x = rmsNorm x := by
  funext i
  unfold gnorm rmsNorm
  rw [grms_univ_eq_rms x]

end Lattice
