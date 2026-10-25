import Lattice.Lib.Architectures.RealBlockLipschitz
import Mathlib

/-!
# LATTICE: 凸组合 Lipschitz —— attention 的组件常数（块界实例化）

RealBlockLipschitz（块界 Lf·(1+La+Lg)）的 La 组件常数：
注意力输出 = 权重凸组合 Σᵢ wᵢ·Vᵢx（权重 wᵢ 由 softmax 给出），
**权重固定时**凸组合是 Lipschitz 映射：

  1. 一般：‖Σ wᵢ·Vᵢx − Σ wᵢ·Vᵢy‖ ≤ (Σ |wᵢ|·‖Vᵢ‖)·‖x−y‖
     （线性 + norm_smul + 每层 Lipschitz）；
  2. 概率权重（wᵢ ≥ 0，Σwᵢ = 1）：界 ≤ M·‖x−y‖（M = max‖Vᵢ‖，
     凸组合不放大——衔接 convComb_norm_bound 的凸组合性质）。

实例化（RealBlockLipschitz 块界）：La = M（注意力层 Lipschitz 常数）；
softmax 权重随输入变化的完整 attention Lipschitz = 本定理 +
softmax 的 Lipschitz（连续可微推论，组件级假设）。

模型无关：任意范数空间 E/F、任意凸组合权重。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定理一：凸组合 Lipschitz（一般权重）
‖Σ wᵢ·Vᵢx − Σ wᵢ·Vᵢy‖ ≤ (Σ |wᵢ|·‖Vᵢ‖)·‖x−y‖。-/

theorem convComb_lipschitz {n : ℕ} (w : Fin n → ℝ) (V : Fin n → E →L[ℝ] F) :
    ∀ x y, ‖(∑ i : Fin n, w i • (V i x)) - (∑ i : Fin n, w i • (V i y))‖
      ≤ (∑ i : Fin n, |w i| * ‖V i‖) * ‖x - y‖ := by
  intro x y
  -- 差 = Σ wᵢ·(Vᵢx − Vᵢy)（线性）
  have hdiff : (∑ i : Fin n, w i • (V i x)) - (∑ i : Fin n, w i • (V i y))
      = ∑ i : Fin n, w i • (V i x - V i y) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_sub]
  -- 每项界：‖wᵢ·(Vᵢx − Vᵢy)‖ ≤ |wᵢ|·‖Vᵢ‖·‖x−y‖
  have hitem : ∀ i : Fin n, ‖w i • (V i x - V i y)‖ ≤ |w i| * ‖V i‖ * ‖x - y‖ := by
    intro i
    calc
      ‖w i • (V i x - V i y)‖ = |w i| * ‖V i x - V i y‖ := by
        -- 注：mathlib 4.14 中 norm_eq_abs 在 Real 命名空间
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |w i| * (‖V i‖ * ‖x - y‖) := by
        have hlin : ‖V i x - V i y‖ = ‖V i (x - y)‖ := by rw [← (V i).map_sub]
        rw [hlin]
        -- 注：mathlib 4.14 中 ContinuousLinearMap.norm_apply_le 已改名 le_opNorm
        exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm (V i) (x - y)) (abs_nonneg _)
      _ = |w i| * ‖V i‖ * ‖x - y‖ := by ring
  -- 三角不等式 + 逐项界（首步用 hdiff 把原差替换为 Σ wᵢ·(Vᵢx−Vᵢy)）
  calc
    ‖(∑ i : Fin n, w i • (V i x)) - (∑ i : Fin n, w i • (V i y))‖
        = ‖∑ i : Fin n, w i • (V i x - V i y)‖ := by rw [hdiff]
    _ ≤ ∑ i : Fin n, ‖w i • (V i x - V i y)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, |w i| * ‖V i‖ * ‖x - y‖ :=
          Finset.sum_le_sum (by intro i hi; exact hitem i)
    _ = (∑ i : Fin n, |w i| * ‖V i‖) * ‖x - y‖ := by rw [Finset.sum_mul]

/-! ## 定理二：概率权重凸组合 Lipschitz
wᵢ ≥ 0，Σwᵢ = 1，‖Vᵢ‖ ≤ M ⟹ 界 ≤ M·‖x−y‖（凸组合不放大）。-/

theorem convComb_lipschitz_prob {n : ℕ} (w : Fin n → ℝ) (V : Fin n → E →L[ℝ] F) (M : ℝ)
    (hw : ∀ i : Fin n, 0 ≤ w i) (hsum : (∑ i : Fin n, w i) = 1) (hM : ∀ i : Fin n, ‖V i‖ ≤ M) :
    ∀ x y, ‖(∑ i : Fin n, w i • (V i x)) - (∑ i : Fin n, w i • (V i y))‖ ≤ M * ‖x - y‖ := by
  intro x y
  have hmain := convComb_lipschitz w V x y
  -- Σ |wᵢ|·‖Vᵢ‖ = Σ wᵢ·‖Vᵢ‖ ≤ Σ wᵢ·M = M·Σwᵢ = M
  have hcoeff : (∑ i : Fin n, |w i| * ‖V i‖) ≤ M := by
    calc
      (∑ i : Fin n, |w i| * ‖V i‖) ≤ (∑ i : Fin n, w i * M) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          |w i| * ‖V i‖ = w i * ‖V i‖ := by rw [abs_of_nonneg (hw i)]
          _ ≤ w i * M := mul_le_mul_of_nonneg_left (hM i) (hw i)
      _ = M * (∑ i : Fin n, w i) := by
        rw [← Finset.sum_mul]
        rw [mul_comm]
      _ = M := by simp [hsum]
  calc
    ‖(∑ i : Fin n, w i • (V i x)) - (∑ i : Fin n, w i • (V i y))‖
        ≤ (∑ i : Fin n, |w i| * ‖V i‖) * ‖x - y‖ := hmain
    _ ≤ M * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)

/-! ## 注：块界实例化
  注意力层 Lipschitz 常数 La = M（max‖Vᵢ‖）——代入
  RealBlockLipschitz.block_lipschitz_bound（Lf·(1+La+Lg)）；
  完整 attention（softmax 权重随输入）的 Lipschitz = 本定理
  与 softmax 输入-Lipschitz 的组合（softmax 连续可微，组件级假设）。-/

end Lattice
