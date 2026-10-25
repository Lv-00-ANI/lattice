import Lattice.Lib.Architectures.RealNormalEquationScalar
import Mathlib

/-!
# LATTICE: 多约束加权驻点 —— 加权损失的驻点刻画（P0 系列扩展）

把 P0 系列（单约束法方程）推广到**多约束加权损失**：

    L(x) = w₁·‖A₁x − b₁‖² + w₂·‖A₂x − b₂‖²

  1. 加权 fderiv：fderiv L x v = 2w₁·re⟨A₁x−b₁, A₁v⟩ + 2w₂·re⟨A₂x−b₂, A₂v⟩
     （fderiv 线性 + 单约束法方程，RealNormalEquationScalar 衔接）；
  2. 驻点刻画：fderiv = 0 ⟺ ∀v，w₁·re⟨r₁,A₁v⟩ + w₂·re⟨r₂,A₂v⟩ = 0
     （加权法方程——多约束的驻点条件，无需约束独立）；
  3. 充分性：各约束满足（残差正交）⟹ 加权驻点（任意权重）。

意义：约束嵌入（ConstraintEmbeddingSoundness）的多约束版——
多个硬约束的加权软损失，驻点条件 = 加权残差正交；
这是 SFT/RLHF 目标（多 term 损失）的驻点理论基础。

模型无关：任意 RCLike 𝕜 内积空间 + 实化假设。
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

/-! ## 加权损失（双约束） -/

def WeightedLoss2 (A₁ A₂ : E →L[𝕜] F) (b₁ b₂ : F) (w₁ w₂ : ℝ) (x : E) : ℝ :=
  w₁ * NormSqLossScalar A₁ b₁ x + w₂ * NormSqLossScalar A₂ b₂ x

/-! ## 定理一：加权 fderiv
fderiv L x v = 2w₁·re⟨A₁x−b₁, A₁v⟩ + 2w₂·re⟨A₂x−b₂, A₂v⟩。-/

theorem weighted2_fderiv (A₁ A₂ : E →L[𝕜] F) (b₁ b₂ : F) (w₁ w₂ : ℝ) (x v : E) :
    fderiv ℝ (WeightedLoss2 A₁ A₂ b₁ b₂ w₁ w₂) x v
      = 2 * w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + 2 * w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫ := by
  unfold WeightedLoss2
  have hd₁ : DifferentiableAt ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y) x :=
    (loss_differentiable_scalar A₁ b₁ x).const_mul w₁
  have hd₂ : DifferentiableAt ℝ (fun y => w₂ * NormSqLossScalar A₂ b₂ y) x :=
    (loss_differentiable_scalar A₂ b₂ x).const_mul w₂
  have hlin : fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y + w₂ * NormSqLossScalar A₂ b₂ y) x
      = fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y) x + fderiv ℝ (fun y => w₂ * NormSqLossScalar A₂ b₂ y) x :=
    fderiv_add hd₁ hd₂
  have hc₁ : fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y) x v
      = w₁ * fderiv ℝ (NormSqLossScalar A₁ b₁) x v := by
    rw [fderiv_const_mul (loss_differentiable_scalar A₁ b₁ x) w₁]
    simp
  have hc₂ : fderiv ℝ (fun y => w₂ * NormSqLossScalar A₂ b₂ y) x v
      = w₂ * fderiv ℝ (NormSqLossScalar A₂ b₂) x v := by
    rw [fderiv_const_mul (loss_differentiable_scalar A₂ b₂ x) w₂]
    simp
  calc
    fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y + w₂ * NormSqLossScalar A₂ b₂ y) x v
        = (fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y) x
            + fderiv ℝ (fun y => w₂ * NormSqLossScalar A₂ b₂ y) x) v := by
          rw [hlin]
    _ = fderiv ℝ (fun y => w₁ * NormSqLossScalar A₁ b₁ y) x v
        + fderiv ℝ (fun y => w₂ * NormSqLossScalar A₂ b₂ y) x v := by simp
    _ = w₁ * fderiv ℝ (NormSqLossScalar A₁ b₁) x v + w₂ * fderiv ℝ (NormSqLossScalar A₂ b₂) x v := by
          rw [hc₁, hc₂]
    _ = w₁ * (2 * RCLike.re ⟪A₁ x - b₁, A₁ v⟫) + w₂ * (2 * RCLike.re ⟪A₂ x - b₂, A₂ v⟫) := by
          rw [fderiv_loss_apply_scalar A₁ b₁ x v, fderiv_loss_apply_scalar A₂ b₂ x v]
    _ = 2 * w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + 2 * w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫ := by ring

/-! ## 定理二：加权驻点刻画
fderiv = 0 ⟺ ∀v，w₁·re⟨r₁,A₁v⟩ + w₂·re⟨r₂,A₂v⟩ = 0（加权法方程）。-/

theorem weighted2_stationarity_iff (A₁ A₂ : E →L[𝕜] F) (b₁ b₂ : F) (w₁ w₂ : ℝ) (x : E) :
    fderiv ℝ (WeightedLoss2 A₁ A₂ b₁ b₂ w₁ w₂) x = 0 ↔
      ∀ v : E, w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫ = 0 := by
  constructor
  · intro hfd v
    have hlin : fderiv ℝ (WeightedLoss2 A₁ A₂ b₁ b₂ w₁ w₂) x v = 0 := by
      rw [hfd]
      simp
    rw [weighted2_fderiv A₁ A₂ b₁ b₂ w₁ w₂ x v] at hlin
    nlinarith
  · intro h
    ext v
    rw [weighted2_fderiv A₁ A₂ b₁ b₂ w₁ w₂ x v]
    have hzero : w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫ = 0 := h v
    calc
      2 * w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + 2 * w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫
          = 2 * (w₁ * RCLike.re ⟪A₁ x - b₁, A₁ v⟫ + w₂ * RCLike.re ⟪A₂ x - b₂, A₂ v⟫) := by ring
      _ = 0 := by
            rw [hzero]
            ring

/-! ## 定理三：各约束满足 ⟹ 加权驻点
∀v，re⟨r₁,A₁v⟩ = 0 且 ∀v，re⟨r₂,A₂v⟩ = 0 ⟹ 加权损失驻点（任意权重）。-/

theorem weighted2_stationarity_of_components (A₁ A₂ : E →L[𝕜] F) (b₁ b₂ : F)
    (w₁ w₂ : ℝ) (x : E)
    (h₁ : ∀ v : E, RCLike.re ⟪A₁ x - b₁, A₁ v⟫ = 0)
    (h₂ : ∀ v : E, RCLike.re ⟪A₂ x - b₂, A₂ v⟫ = 0) :
    fderiv ℝ (WeightedLoss2 A₁ A₂ b₁ b₂ w₁ w₂) x = 0 := by
  ext v
  rw [weighted2_fderiv A₁ A₂ b₁ b₂ w₁ w₂ x v, h₁ v, h₂ v]
  simp

/-! ## 注：多约束嵌入闭环
  约束嵌入（ConstraintEmbeddingSoundness：单约束嵌入平方损失）⟹
  多约束加权嵌入（本文件：各约束满足 ⟹ 加权驻点，定理三）；
  驻点条件 = 加权法方程（定理二）——SFT/RLHF 多 term 损失的
  驻点理论基础；非负权重时驻点 ⟹ 加权残差权衡（Pareto 面）。-/

end Lattice
