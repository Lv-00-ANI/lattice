import Lattice.Lib.Architectures.RealNormalEquationScalar
import Mathlib

/-!
# LATTICE: 权重衰减/正则化 —— Ridge 损失的驻点与全局最优（任意 RCLike 域）

训练线的真实组件（AdamW 的 weight decay / Tikhonov 正则）：

    L_β(x) = ‖A·x − b‖² + β·‖x‖²

  1. 范数平方的 fderiv：fderiv (‖·‖²) x v = 2·re⟨x, v⟩
     （norm_sq_line_deriv_scalar 的 fderiv 形式）；
  2. Ridge fderiv：fderiv L_β x v = 2·re⟨Ax−b, Av⟩ + 2β·re⟨x, v⟩
     （fderiv 线性 + 法方程逐项）；
  3. 驻点刻画：fderiv = 0 ⟺ ∀v，re⟨Ax−b,Av⟩ + β·re⟨x,v⟩ = 0
     （正则法方程 (AᵀA + βI)x = Aᵀb 的弱形式）；
  4. 全局最优（β ≥ 0）：驻点 ⟹ 全局最小
     （‖A·v‖² + β‖v‖² ≥ 0 的交叉项消去，Ridge 损失凸）。

注：一致系统（Ax=b 可解）时正则驻点**不是**任意满足解——β‖x‖²
项要求 x 同时最小化范数；β → 0 极限是伪逆解（最小范数解）。
Ridge 驻点是「满足度与范数」的权衡（正则化偏差的量化）。

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

/-! ## 定理一：范数平方的 fderiv
fderiv (‖·‖²) x v = 2·re⟨x, v⟩（norm_sq_line_deriv_scalar 的 fderiv 版）。-/

theorem normSq_fderiv_scalar (x v : E) :
    fderiv ℝ (fun y : E => ‖y‖ ^ 2) x v = 2 * RCLike.re ⟪x, v⟫ := by
  have hdir : fderiv ℝ (fun y : E => ‖y‖ ^ 2) x v = deriv (fun t : ℝ => ‖x + t • v‖ ^ 2) 0 := by
    simpa using fderiv_apply_direction_scalar ((differentiableAt_id).norm_sq 𝕜)
  rw [hdir]
  exact norm_sq_line_deriv_scalar x v

/-! ## 定理二：Ridge fderiv
fderiv L_β x v = 2·re⟨Ax−b, Av⟩ + 2β·re⟨x, v⟩。-/

theorem ridge_fderiv (A : E →L[𝕜] F) (b : F) (β : ℝ) (x v : E) :
    fderiv ℝ (fun y => NormSqLossScalar A b y + β * ‖y‖ ^ 2) x v
      = 2 * RCLike.re ⟪A x - b, A v⟫ + 2 * β * RCLike.re ⟪x, v⟫ := by
  have hd1 : DifferentiableAt ℝ (NormSqLossScalar A b) x := loss_differentiable_scalar A b x
  have hd2 : DifferentiableAt ℝ (fun y => β * ‖y‖ ^ 2) x :=
    ((differentiableAt_id).norm_sq 𝕜).const_mul β
  have hlin : fderiv ℝ (fun y => NormSqLossScalar A b y + β * ‖y‖ ^ 2) x
      = fderiv ℝ (NormSqLossScalar A b) x + fderiv ℝ (fun y => β * ‖y‖ ^ 2) x :=
    fderiv_add hd1 hd2
  have hc : fderiv ℝ (fun y => β * ‖y‖ ^ 2) x v = β * (2 * RCLike.re ⟪x, v⟫) := by
    have hconst : fderiv ℝ (fun y => β * ‖y‖ ^ 2) x = β • fderiv ℝ (fun y => ‖y‖ ^ 2) x := by
      simpa using fderiv_const_mul ((differentiableAt_id).norm_sq 𝕜) β
    -- (β • fderiv (‖·‖²) x) v = β • (fderiv (‖·‖²) x v) = β * (2·re⟨x,v⟩)
    rw [hconst]
    rw [ContinuousLinearMap.smul_apply]
    rw [normSq_fderiv_scalar (𝕜 := 𝕜) x v]
    simp
  calc
    fderiv ℝ (fun y => NormSqLossScalar A b y + β * ‖y‖ ^ 2) x v
        = (fderiv ℝ (NormSqLossScalar A b) x + fderiv ℝ (fun y => β * ‖y‖ ^ 2) x) v := by
          rw [hlin]
    _ = fderiv ℝ (NormSqLossScalar A b) x v + fderiv ℝ (fun y => β * ‖y‖ ^ 2) x v := by simp
    _ = 2 * RCLike.re ⟪A x - b, A v⟫ + β * (2 * RCLike.re ⟪x, v⟫) := by
          rw [fderiv_loss_apply_scalar A b x v, hc]
    _ = 2 * RCLike.re ⟪A x - b, A v⟫ + 2 * β * RCLike.re ⟪x, v⟫ := by ring

/-! ## 定理三：Ridge 驻点刻画
fderiv = 0 ⟺ ∀v，re⟨Ax−b,Av⟩ + β·re⟨x,v⟩ = 0（正则法方程弱形式）。-/

theorem ridge_stationarity_iff (A : E →L[𝕜] F) (b : F) (β : ℝ) (x : E) :
    fderiv ℝ (fun y => NormSqLossScalar A b y + β * ‖y‖ ^ 2) x = 0 ↔
      ∀ v : E, RCLike.re ⟪A x - b, A v⟫ + β * RCLike.re ⟪x, v⟫ = 0 := by
  constructor
  · intro hfd v
    have hlin : fderiv ℝ (fun y => NormSqLossScalar A b y + β * ‖y‖ ^ 2) x v = 0 := by
      rw [hfd]
      simp
    rw [ridge_fderiv A b β x v] at hlin
    -- 2(re + βre) = 0 ⟹ re + βre = 0
    nlinarith
  · intro h
    ext v
    rw [ridge_fderiv A b β x v]
    have hzero : RCLike.re ⟪A x - b, A v⟫ + β * RCLike.re ⟪x, v⟫ = 0 := h v
    simp
    nlinarith

/-! ## 定理四：Ridge 全局最优（β ≥ 0）
驻点（正则法方程）⟹ 全局最小：Ridge 损失凸，驻点即最小值。-/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem ridge_global_min (A : E →L[𝕜] F) (b : F) (β : ℝ) (x : E) (hβ : 0 ≤ β)
    (hx : ∀ v : E, RCLike.re ⟪A x - b, A v⟫ + β * RCLike.re ⟪x, v⟫ = 0) :
    ∀ y : E, NormSqLossScalar A b x + β * ‖x‖ ^ 2 ≤ NormSqLossScalar A b y + β * ‖y‖ ^ 2 := by
  intro y
  unfold NormSqLossScalar
  -- 分解 y = x + (y−x)：
  -- ‖A y − b‖² + β‖y‖² − (‖Ax−b‖² + β‖x‖²)
  --   = 2(re⟨Ax−b,A(y−x)⟩ + β·re⟨x,y−x⟩) + ‖A(y−x)‖² + β‖y−x‖²
  --   = 0（驻点）+ 非负
  have hdecomp : A y - b = (A x - b) + A (y - x) := by
    calc
      A y - b = (A x - b) + (A y - A x) := by abel
      _ = (A x - b) + A (y - x) := by rw [← A.map_sub]
  have hdecomp2 : y = x + (y - x) := by abel
  -- ‖Ay−b‖² = ‖(Ax−b)+A(y−x)‖²；‖y‖² = ‖x+(y−x)‖²
  have h1 : ‖A y - b‖ ^ 2 = ‖(A x - b) + A (y - x)‖ ^ 2 := by rw [hdecomp]
  have h2 : ‖y‖ ^ 2 = ‖x + (y - x)‖ ^ 2 := by rw [← hdecomp2]
  -- 平方展开
  have hsq1 := norm_add_sq (𝕜 := 𝕜) (A x - b) (A (y - x))
  have hsq2 := norm_add_sq (𝕜 := 𝕜) x (y - x)
  -- 交叉项（驻点条件）
  have hcross : RCLike.re ⟪A x - b, A (y - x)⟫ + β * RCLike.re ⟪x, y - x⟫ = 0 := hx (y - x)
  nlinarith [h1, h2, hsq1, hsq2, hcross, hβ,
    sq_nonneg (‖A (y - x)‖), sq_nonneg (‖y - x‖)]

/-! ## 注：权重衰减语义
  Ridge 驻点 = 满足度（‖Ax−b‖²）与范数（‖x‖²）的权衡；
  β ≥ 0 保证凸性（全局最优，定理四）；β = 0 退化回最小二乘
  （RealLeastSquares）；β → ∞ 使解 → 0（收缩语义）。
  一致系统时正则驻点 = 最小范数满足解（β→0 伪逆极限），
  是权重衰减「宁可偏差也要小范数」的量化基础。-/

end Lattice
