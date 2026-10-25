import Lattice.Lib.Architectures.RealNormalEquationScalar
import Mathlib

/-!
# LATTICE: n 约束加权驻点（泛化）—— 任意数量约束的加权法方程

RealWeightedConstraints（双约束）的 **n 约束泛化**：
任意有限个约束 {Aᵢx = bᵢ}ᵢ，加权损失

    L(x) = Σᵢ wᵢ·‖Aᵢx − bᵢ‖²

  1. 加权 fderiv（n 版）：fderiv L x v = Σᵢ 2wᵢ·re⟨Aᵢx−bᵢ, Aᵢv⟩
     （fderiv_sum 线性 + 单约束法方程逐项）；
  2. 各约束满足 ⟹ 加权驻点（任意权重，n 版）：
     ∀i ∀v，re⟨rᵢ,Aᵢv⟩ = 0 ⟹ fderiv L x = 0。

双约束（RealWeightedConstraints）是 n=2 特例；这是约束嵌入
（ConstraintEmbeddingSoundness）到任意多约束的完整泛化。

模型无关：任意 RCLike 𝕜 内积空间 + 实化假设、任意约束数 n。
-/

noncomputable section

namespace Lattice

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法（仅 ℝ/ℂ 有裸记法），
此处为任意 RCLike 𝕜 声明本地记法（与 RealNormalEquationScalar 一致）。-/
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ## n 约束加权损失 -/

def WeightedLossN {n : ℕ} (A : Fin n → E →L[𝕜] F) (b : Fin n → F) (w : Fin n → ℝ) (x : E) : ℝ :=
  ∑ i : Fin n, w i * NormSqLossScalar (A i) (b i) x

/-! ## 定理一：n 约束加权 fderiv（泛化）
fderiv L x v = Σᵢ 2wᵢ·re⟨Aᵢx−bᵢ, Aᵢv⟩。-/

theorem weightedN_fderiv {n : ℕ} (A : Fin n → E →L[𝕜] F) (b : Fin n → F) (w : Fin n → ℝ) (x v : E) :
    fderiv ℝ (WeightedLossN A b w) x v
      = ∑ i : Fin n, 2 * w i * RCLike.re ⟪A i x - b i, A i v⟫ := by
  unfold WeightedLossN
  -- 逐项可导（const_mul 复合）
  have hdiff : ∀ i : Fin n,
      DifferentiableAt ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x := by
    intro i
    exact (loss_differentiable_scalar (A i) (b i) x).const_mul (w i)
  -- fderiv 求和线性：fderiv Σ = Σ fderiv
  have hlin : fderiv ℝ (fun y => ∑ i : Fin n, w i * NormSqLossScalar (A i) (b i) y) x
      = ∑ i : Fin n, fderiv ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x := by
    exact fderiv_sum (u := Finset.univ) (A := fun i y => w i * NormSqLossScalar (A i) (b i) y)
      (fun i hi => hdiff i)
  -- 逐项：fderiv (wᵢLᵢ) x v = wᵢ·(2re⟨rᵢ,Aᵢv⟩)
  have hitem : ∀ i : Fin n, fderiv ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x v
      = 2 * w i * RCLike.re ⟪A i x - b i, A i v⟫ := by
    intro i
    calc
      fderiv ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x v
          = w i * fderiv ℝ (NormSqLossScalar (A i) (b i)) x v := by
            rw [fderiv_const_mul (loss_differentiable_scalar (A i) (b i) x) (w i)]
            simp
      _ = w i * (2 * RCLike.re ⟪A i x - b i, A i v⟫) := by
            rw [fderiv_loss_apply_scalar (A i) (b i) x v]
      _ = 2 * w i * RCLike.re ⟪A i x - b i, A i v⟫ := by ring
  calc
    fderiv ℝ (fun y => ∑ i : Fin n, w i * NormSqLossScalar (A i) (b i) y) x v
        = (∑ i : Fin n, fderiv ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x) v := by
          rw [hlin]
    _ = ∑ i : Fin n, fderiv ℝ (fun y => w i * NormSqLossScalar (A i) (b i) y) x v := by
          simp
    _ = ∑ i : Fin n, 2 * w i * RCLike.re ⟪A i x - b i, A i v⟫ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hitem i
    _ = (∑ i : Fin n, 2 * w i * RCLike.re ⟪A i x - b i, A i v⟫) := rfl

/-! ## 定理二：各约束满足 ⟹ n 约束加权驻点（泛化）
∀i ∀v，re⟨rᵢ,Aᵢv⟩ = 0 ⟹ fderiv L x = 0（任意权重）。-/

theorem weightedN_stationarity_of_components {n : ℕ} (A : Fin n → E →L[𝕜] F)
    (b : Fin n → F) (w : Fin n → ℝ) (x : E)
    (h : ∀ (i : Fin n) (v : E), RCLike.re ⟪A i x - b i, A i v⟫ = 0) :
    fderiv ℝ (WeightedLossN A b w) x = 0 := by
  ext v
  rw [weightedN_fderiv A b w x v]
  -- Σᵢ 2wᵢ·0 = 0
  apply Finset.sum_eq_zero
  intro i hi
  simp [h i v]

/-! ## 注：泛化闭环
  双约束（RealWeightedConstraints，n=2）⟹ n 约束（本文件，任意 n）；
  fderiv 线性（fderiv_sum）+ 单约束法方程逐项 ⟹ 加权法方程的完整
  求和形式；各约束满足 ⟹ 加权驻点对任意 n、任意权重成立——
  多约束约束嵌入（SFT/RLHF 多 term 损失）的完整泛化。-/

end Lattice
