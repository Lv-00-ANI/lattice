import Mathlib
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealSwiGLU
import Lattice.Lib.Architectures.RealActClass
/-!
# LATTICE: 一般门控机制 —— Gated(f = g·h)、乘积 Lipschitz、统一激活门控

激活族（RealActClass.SoftMasked: f(x) = s(x)·x，s ∈ [0,1]）只是门控的**特例**
（信号 h = id）。本文件建立模型无关的**一般门控**：

  Gated f g h := ∀ x, f x = g x · h x

  1. **软掩码是门控**：SoftMasked f s ⟹ Gated f s id（ReLU/GELU/SiLU/SwiGLU/
     hard-swish 全部自动纳入）；门控对复合、乘积封闭。
  2. **乘积 Lipschitz 界**（gated_lipschitz）：
       |g| ≤ 1、g 是 Lg-Lipschitz、h 是 Lh-Lipschitz、|h| ≤ M
       ⟹ f = g·h 是 (Lh + M·Lg)-Lipschitz
     （分解 g(x)h(x) − g(y)h(y) = g(x)(h(x)−h(y)) + (g(x)−g(y))h(y)）。
  3. **门控输出界**（gated_soft_mask_bound）：|g| ≤ 1 ⟹ ‖f(x)‖ ≤ ‖h(x)‖
     （标量版 gated_abs_le）。
  4. **门控 FFN 有效线性**（gated_ffn_effective）：
       Σ Wᵢ·f(hᵢ) = Σ (Wᵢ·g(hᵢ))·hᵢ
     回收 RealActClass.softMask_FFN_effective（h = id），并给出 SwiGLU 双投影形式
     swigluPair（门控支 a 经 σ、被支 b 相乘）与其余门控激活的统一陈述。

全部定理真实可证，无 sorry/axiom/admit。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice
/-! ## 一般门控定义 -/

/-- 一般门控：f(x) = g(x)·h(x)（g 为门、h 为信号）。 -/
def Gated (f g h : ℝ → ℝ) : Prop := ∀ x, f x = g x * h x

/-- 软掩码激活是门控（信号 h = id）。 -/
theorem softMasked_is_gated {f s : ℝ → ℝ} (h : SoftMasked f s) :
    Gated f s (fun x : ℝ => x) := by
  intro x
  exact h.1 x

/-- 门控对内层映射复合封闭：f = g·h ⟹ f∘k = (g∘k)·(h∘k)。 -/
theorem Gated.comp {f g h : ℝ → ℝ} (hf : Gated f g h) (k : ℝ → ℝ) :
    Gated (fun x => f (k x)) (fun x => g (k x)) (fun x => h (k x)) := by
  intro x
  exact hf (k x)

/-- 两个门控的逐点乘积仍是门控。 -/
theorem Gated.mul {f₁ g₁ h₁ f₂ g₂ h₂ : ℝ → ℝ}
    (hf₁ : Gated f₁ g₁ h₁) (hf₂ : Gated f₂ g₂ h₂) :
    Gated (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) (fun x => h₁ x * h₂ x) := by
  intro x
  change f₁ x * f₂ x = (g₁ x * g₂ x) * (h₁ x * h₂ x)
  rw [hf₁ x, hf₂ x]
  ring

/-! ## 把既有激活纳入门控框架 -/

theorem swiglu_is_gated : Gated swiglu sigmoid (fun x : ℝ => x) :=
  softMasked_is_gated swiglu_is_soft_masked

theorem silu_is_gated : Gated silu sigmoid (fun x : ℝ => x) :=
  softMasked_is_gated silu_is_soft_masked

theorem hardSwish_is_gated : Gated hardSwish hardSigmoid (fun x : ℝ => x) :=
  softMasked_is_gated hardSwish_is_soft_masked

theorem relu_is_gated : Gated relu reluSoftMask (fun x : ℝ => x) :=
  softMasked_is_gated relu_is_soft_masked

theorem gelu_is_gated : Gated geluTanh geluSoftMask (fun x : ℝ => x) :=
  softMasked_is_gated gelu_is_soft_masked

/-! ## 门控输出界 -/

/-- 标量门控输出界：|g| ≤ 1 ⟹ |f(x)| ≤ |h(x)|。 -/
theorem gated_abs_le {f g h : ℝ → ℝ} (hf : Gated f g h) (hg : ∀ x, |g x| ≤ 1) :
    ∀ x, |f x| ≤ |h x| := by
  intro x
  rw [hf x, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hg x)

/-- 向量门控输出界：f(x) = g(x) • h(x) 且 |g| ≤ 1 ⟹ ‖f(x)‖ ≤ ‖h(x)‖。 -/
theorem gated_soft_mask_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (g : E → ℝ) (h : E → E) (hgd : ∀ x, f x = g x • h x)
    (hg : ∀ x, |g x| ≤ 1) : ∀ x, ‖f x‖ ≤ ‖h x‖ := by
  intro x
  rw [hgd x, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hg x)

/-! ## 门控乘积的 Lipschitz 界 -/

/-- **乘积 Lipschitz 界**：|g| ≤ 1、g 是 Lg-Lipschitz、h 是 Lh-Lipschitz、|h| ≤ M
    ⟹ f = g·h 是 (Lh + M·Lg)-Lipschitz。 -/
theorem gated_lipschitz (f g h : ℝ → ℝ) (Lg Lh M : ℝ)
    (hgd : Gated f g h) (hg1 : ∀ x, |g x| ≤ 1)
    (hgL : ∀ x y, |g x - g y| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |h x - h y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |h x| ≤ M) (hLg : 0 ≤ Lg) :
    ∀ x y, |f x - f y| ≤ (Lh + M * Lg) * |x - y| := by
  intro x y
  have hdecomp : f x - f y = g x * (h x - h y) + (g x - g y) * h y := by
    rw [hgd x, hgd y]
    ring
  calc
    |f x - f y| = |g x * (h x - h y) + (g x - g y) * h y| := by rw [hdecomp]
    _ ≤ |g x * (h x - h y)| + |(g x - g y) * h y| := abs_add _ _
    _ = |g x| * |h x - h y| + |g x - g y| * |h y| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (Lh * |x - y|) + (Lg * |x - y|) * M := by
          apply add_le_add
          · exact mul_le_mul (hg1 x) (hhL x y) (abs_nonneg _) (by norm_num)
          · exact mul_le_mul (hgL x y) (hhM y) (abs_nonneg _)
              (mul_nonneg hLg (abs_nonneg _))
    _ = (Lh + M * Lg) * |x - y| := by ring

/-! ## 门控 FFN 的有效线性映射 -/

/-- **门控 FFN 有效线性**：Σ Wᵢ·f(hᵢ) = Σ (Wᵢ·g(hᵢ))·hᵢ。 -/
theorem gated_ffn_effective {ι : Type*} [Fintype ι] (f g h : ℝ → ℝ)
    (W H : ι → ℝ) (hgf : Gated f g h) :
    ∑ i, W i * f (H i) = ∑ i, (W i * g (H i)) * h (H i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hgf (H i)]
  ring

/-- 软掩码 FFN 定理（RealActClass.softMask_FFN_effective）由门控定理回收。 -/
theorem softMask_ffn_effective_via_gated {ι : Type*} [Fintype ι] (f s : ℝ → ℝ)
    (W H : ι → ℝ) (hsm : SoftMasked f s) :
    ∑ i, W i * f (H i) = ∑ i, (W i * s (H i)) * H i :=
  gated_ffn_effective f s (fun x : ℝ => x) W H (softMasked_is_gated hsm)

/-- 门控激活 FFN 实例：SwiGLU 的 swish 门控（信号 = 门控投影自身）。 -/
theorem swiglu_ffn_effective_via_gated {ι : Type*} [Fintype ι] (W H : ι → ℝ) :
    ∑ i, W i * swiglu (H i) = ∑ i, (W i * sigmoid (H i)) * H i :=
  gated_ffn_effective swiglu sigmoid (fun x : ℝ => x) W H swiglu_is_gated

/-! ## 双投影 SwiGLU（真实 SwiGLU：门控支 σ(a·) 乘被支 b·） -/

/-- 双投影 SwiGLU：swigluPair a b z = swish(a z) · b z。 -/
def swigluPair (a b : ℝ → ℝ) (z : ℝ) : ℝ := swiglu (a z) * b z

/-- SwiGLU 是门控：门 = σ∘a ∈ [0,1]，信号 = a·b。 -/
theorem swigluPair_is_gated (a b : ℝ → ℝ) :
    Gated (swigluPair a b) (fun z => sigmoid (a z)) (fun z => a z * b z) := by
  intro z
  unfold swigluPair swiglu
  ring

/-- SwiGLU 门控输出界：|swigluPair a b z| ≤ |a z · b z|。 -/
theorem swigluPair_bound (a b : ℝ → ℝ) (z : ℝ) :
    |swigluPair a b z| ≤ |a z * b z| :=
  gated_abs_le (swigluPair_is_gated a b)
    (fun w => by
      rw [abs_of_pos (sigmoid_bounds (a w)).1]
      exact le_of_lt (sigmoid_bounds (a w)).2) z

/-- 双投影 SwiGLU-FFN 有效线性：
    Σ Wᵢ·swigluPair a b (hᵢ) = Σ (Wᵢ·σ(a hᵢ))·(a hᵢ · b hᵢ)。 -/
theorem swigluPair_ffn_effective {ι : Type*} [Fintype ι] (a b : ℝ → ℝ) (W H : ι → ℝ) :
    ∑ i, W i * swigluPair a b (H i)
      = ∑ i, (W i * sigmoid (a (H i))) * (a (H i) * b (H i)) :=
  gated_ffn_effective (swigluPair a b) (fun z => sigmoid (a z)) (fun z => a z * b z)
    W H (swigluPair_is_gated a b)

/-! ## 硬门控与软门控的统一（ReLU / hard-swish / SiLU 的输出界） -/

/-- ReLU 的门控输出界：|relu x| ≤ |x|（门 ∈ {0,1}）。 -/
theorem relu_gated_bound (x : ℝ) : |relu x| ≤ |x| :=
  gated_abs_le relu_is_gated
    (fun w => by
      by_cases h : 0 < w
      · simp [reluSoftMask, h]
      · simp [reluSoftMask, h]) x

/-- SiLU 的门控输出界：|silu x| ≤ |x|（门 = σ ∈ [0,1]）。 -/
theorem silu_gated_bound (x : ℝ) : |silu x| ≤ |x| :=
  gated_abs_le silu_is_gated
    (fun w => by
      rw [abs_of_pos (sigmoid_bounds w).1]
      exact le_of_lt (sigmoid_bounds w).2) x

/-- hard-swish 的门控输出界：|hardSwish x| ≤ |x|（门 = hardSigmoid ∈ [0,1]）。 -/
theorem hardSwish_gated_bound (x : ℝ) : |hardSwish x| ≤ |x| :=
  gated_abs_le hardSwish_is_gated
    (fun w => by
      rw [abs_of_nonneg (hardSigmoid_bounds w).1]
      exact (hardSigmoid_bounds w).2) x

end Lattice
