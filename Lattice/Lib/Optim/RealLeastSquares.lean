import Lattice.Lib.Architectures.RealNormalEquationScalar
import Mathlib

/-!
# LATTICE: 最小二乘完整理论 —— 法方程解 ⟺ 全局最小（任意 RCLike 域）

补全法方程理论：RealNormalEquationScalar 给出「驻点 ⟺ 满足」（一致系统），
本文件给出最小二乘的**全局最优性**（任意系统，无需一致）：

  1. 残差正交 ⟹ 全局最小：若 ∀v，re⟨Ax−b, Av⟩ = 0（法方程条件），
     则 ∀y，‖Ax−b‖² ≤ ‖Ay−b‖²（norm_add_sq 分解，交叉项为零）；
  2. 全局最小 ⟹ 残差正交：变分论证——若 ‖Ax−b‖² 全局最小，则沿
     任意方向 v 的二次函数 2t·re⟨r,Av⟩ + t²·‖Av‖² ≥ 0（∀t），
     线性项必须为零（linear_term_forces_zero，无需 Fermat 定理）；
  3. 一致系统特例：满足 ⟺ 驻点 ⟺ 全局最小（P0_normal_equation_scalar
     衔接）。

闭环：驻点（法方程）→ 全局最小 → 最小二乘解的变分刻画——
「硬约束解嵌入软约束驻点」的全局性补全。

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

/-! ## 引理：线性项归零（变分核心）
若 ∀t，2t·c + t²·d ≥ 0（d ≥ 0），则 c = 0。
证明：取 t = −c/(d+1) 得负值矛盾（无需导数/极限）。-/

lemma linear_term_forces_zero (c d : ℝ) (hd : 0 ≤ d) (h : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * d) :
    c = 0 := by
  by_contra hc
  have ht : 0 ≤ 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d := h (-c / (d + 1))
  have hden : d + 1 ≠ 0 := by nlinarith
  have hneg : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d < 0 := by
    have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    have hnum : -d - 2 < 0 := by nlinarith
    have hdenpos : 0 < (d + 1) ^ 2 := sq_pos_of_ne_zero (by nlinarith : d + 1 ≠ 0)
    have heq : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = c ^ 2 * (-d - 2) / (d + 1) ^ 2 := by
      field_simp [hden]
      ring
    rw [heq]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc2 hnum) hdenpos
  exact (not_lt_of_ge ht) hneg

/-! ## 定理一：残差正交 ⟹ 全局最小
若 ∀v，re⟨Ax−b, Av⟩ = 0（法方程条件），则 x 是全局最小二乘解。-/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem normal_equation_global_min (A : E →L[𝕜] F) (b : F) (x : E)
    (hx : ∀ v : E, RCLike.re ⟪A x - b, A v⟫ = 0) :
    ∀ y : E, NormSqLossScalar A b x ≤ NormSqLossScalar A b y := by
  intro y
  unfold NormSqLossScalar
  -- Ay − b = (Ax−b) + A(y−x)
  have hdecomp : A y - b = (A x - b) + A (y - x) := by
    calc
      A y - b = (A x - b) + (A y - A x) := by abel
      _ = (A x - b) + A (y - x) := by rw [← A.map_sub]
  -- ‖(Ax−b) + A(y−x)‖² = ‖Ax−b‖² + 2re⟨Ax−b, A(y−x)⟩ + ‖A(y−x)‖²
  have hsq := norm_add_sq (𝕜 := 𝕜) (A x - b) (A (y - x))
  rw [hdecomp, hsq, hx (y - x)]
  nlinarith [sq_nonneg (‖A (y - x)‖)]

/-! ## 定理二：全局最小 ⟹ 残差正交
若 x 是全局最小二乘解，则 ∀v，re⟨Ax−b, Av⟩ = 0（变分）。-/

omit [CompleteSpace E] [CompleteSpace F] in
theorem residual_orthogonal_of_global_min (A : E →L[𝕜] F) (b : F) (x : E)
    (hx : ∀ y : E, NormSqLossScalar A b x ≤ NormSqLossScalar A b y) :
    ∀ v : E, RCLike.re ⟪A x - b, A v⟫ = 0 := by
  intro v
  -- 沿方向 v 的二次函数：∀t，0 ≤ 2t·c + t²·d（c = re⟨r,Av⟩，d = ‖Av‖²）
  have hgoal : ∀ t : ℝ, 0 ≤ 2 * t * RCLike.re ⟪A x - b, A v⟫ + t ^ 2 * ‖A v‖ ^ 2 := by
    intro t
    have hineq := hx (x + t • v)
    unfold NormSqLossScalar at hineq
    -- ‖A(x + t·v) − b‖² = ‖(Ax−b) + t·Av‖²
    have harg : ∀ t : ℝ, ‖A (x + t • v) - b‖ ^ 2 = ‖(A x - b) + t • (A v)‖ ^ 2 := by
      intro t
      have hArg : A (x + t • v) - b = (A x - b) + t • A v := by
        calc
          A (x + t • v) - b = (A x + A (t • v)) - b := by rw [A.map_add]
          _ = (A x + t • A v) - b := by
                have hsmul : A (t • v) = t • A v := by
                  calc
                    A (t • v) = A ((t : 𝕜) • v) := by rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
                    _ = (t : 𝕜) • A v := A.map_smul (t : 𝕜) v
                    _ = t • A v := by rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
                rw [hsmul]
          _ = (A x - b) + t • A v := by abel
      rw [hArg]
    rw [harg t] at hineq
    -- ‖(Ax−b) + t·Av‖² = ‖Ax−b‖² + 2re⟨Ax−b, t·Av⟩ + ‖t·Av‖²
    have hsq := norm_add_sq (𝕜 := 𝕜) (A x - b) (t • (A v))
    rw [hsq] at hineq
    -- re⟨r, t·Av⟩ = t·re⟨r,Av⟩（4.14 的 inner_smul_right 无共轭：⟨x, r·y⟩ = r·⟨x, y⟩）
    have hre : RCLike.re ⟪A x - b, t • A v⟫ = t * RCLike.re ⟪A x - b, A v⟫ := by
      calc
        RCLike.re ⟪A x - b, t • A v⟫ = RCLike.re ⟪A x - b, (t : 𝕜) • A v⟫ := by
          rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        _ = RCLike.re ((t : 𝕜) * ⟪A x - b, A v⟫) := by rw [inner_smul_right]
        _ = t * RCLike.re ⟪A x - b, A v⟫ := RCLike.re_ofReal_mul t _
    -- ‖t·Av‖² = t²·‖Av‖²
    have hnorm : ‖t • A v‖ ^ 2 = t ^ 2 * ‖A v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hre, hnorm] at hineq
    nlinarith [hineq]
  exact linear_term_forces_zero (RCLike.re ⟪A x - b, A v⟫) (‖A v‖ ^ 2) (sq_nonneg _) hgoal

/-! ## 定理三：一致系统特例
满足点 ⟹ 全局最小（‖Ax−b‖ = 0 是最小值）。-/

omit [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem satisfaction_global_min (A : E →L[𝕜] F) (b : F) (x : E) (hx : A x = b) :
    ∀ y : E, NormSqLossScalar A b x ≤ NormSqLossScalar A b y := by
  intro y
  unfold NormSqLossScalar
  rw [hx]
  simpa using sq_nonneg (‖A y - b‖)

/-! ## 定理四：法方程条件 ⟺ 全局最小
残差正交 ⟺ 全局最小（最小二乘解的变分刻画）。-/

theorem normal_equation_iff_global_min (A : E →L[𝕜] F) (b : F) (x : E) :
    (∀ v : E, RCLike.re ⟪A x - b, A v⟫ = 0) ↔ (∀ y : E, NormSqLossScalar A b x ≤ NormSqLossScalar A b y) := by
  constructor
  · exact normal_equation_global_min A b x
  · exact residual_orthogonal_of_global_min A b x

/-! ## 定理五：一致系统的完整刻画
驻点（fderiv = 0）⟺ 满足 ⟺ 全局最小。-/

theorem consistent_stationarity_iff_min (A : E →L[𝕜] F) (b : F) (x : E)
    (hb : b ∈ LinearMap.range (A : E →ₗ[𝕜] F)) :
    (fderiv ℝ (NormSqLossScalar A b) x = 0) ↔ (∀ y : E, NormSqLossScalar A b x ≤ NormSqLossScalar A b y) := by
  constructor
  · intro hfd
    -- fderiv = 0 ⟹ Ax = b（法方程，一致系统）⟹ 全局最小
    have hax : A x = b := (P0_normal_equation_scalar A b x hb).mp hfd
    exact satisfaction_global_min A b x hax
  · intro hmin
    -- 全局最小 ⟹ 残差正交 ⟹ Ax−b ∈ rangeᗮ ∩ range = ⊥ ⟹ Ax = b
    have hre : ∀ v : E, RCLike.re ⟪A x - b, A v⟫ = 0 := residual_orthogonal_of_global_min A b x hmin
    have horth : (A x - b) ∈ (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) :=
      mem_orthogonal_range_scalar hre
    have hax : A x ∈ LinearMap.range (A : E →ₗ[𝕜] F) :=
      LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hsub : (A x - b) ∈ LinearMap.range (A : E →ₗ[𝕜] F) :=
      Submodule.sub_mem (LinearMap.range (A : E →ₗ[𝕜] F)) hax hb
    have hbot : (A x - b) = 0 := by
      have hmem : (A x - b) ∈
          (LinearMap.range (A : E →ₗ[𝕜] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) := by
        exact Submodule.mem_inf.mpr ⟨hsub, horth⟩
      have hdisj : (LinearMap.range (A : E →ₗ[𝕜] F)) ⊓
          (Submodule.orthogonal (LinearMap.range (A : E →ₗ[𝕜] F))) = ⊥ := by
        exact Submodule.inf_orthogonal_eq_bot (LinearMap.range (A : E →ₗ[𝕜] F))
      have : (A x - b) ∈ (⊥ : Submodule 𝕜 F) := by simpa [hdisj] using hmem
      simpa using this
    -- Ax = b ⟹ 驻点（法方程，一致系统）
    have hAx : A x = b := sub_eq_zero.mp hbot
    exact (P0_normal_equation_scalar A b x hb).mpr hAx

/-! ## 注：理论闭环
  驻点 ⟺ 满足（RealNormalEquationScalar，一致系统）
  满足 ⟹ 全局最小（本文件定理三）
  全局最小 ⟹ 残差正交（本文件定理二，变分）
  残差正交 ⟺ 全局最小（本文件定理四，最小二乘刻画）
  ——「硬约束解嵌入软约束驻点」从局部（fderiv）补全到全局（最小值），
  最小二乘理论完整：一致系统时驻点=满足=全局最小（定理五）。-/

end Lattice
