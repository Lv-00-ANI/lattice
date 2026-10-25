import Mathlib
import Lattice.Lib.LinearAlgebra.RealInnerScalar
import Lattice.Lib.Chain.RealScalarField
import Lattice.Lib.Architectures.RealScalarResidual
import Lattice.Lib.Meta.RealScalarVerdict
import Lattice.Lib.Architectures.RealNormalEquationScalar
/-!
# LATTICE: 复数全链（§5 数域行）第一步 —— ℂ 上的实例化与 ℂ 特有恒等式

ℂ 是 mathlib 的 RCLike 实例（`RCLike ℂ`），既有任意域定理（RealInnerScalar /
RealScalarField / RealScalarResidual / RealScalarVerdict / RealNormalEquationScalar）
在 ℂ 上自动成立。本文件做两层落地：

  1. **ℂ 实例化**：把既有 `RCLike 𝕜` / `NontriviallyNormedField 𝕜` 定理在
     `𝕜 := ℂ` 上展开成实例定理（等距保范数、内积范数恒等式、编辑输出界、
     残差局部性、仿射编辑界、P0 法方程），并给具体空间
     `EuclideanSpace ℂ (Fin d)` 做实例；
  2. **ℂ 特有恒等式**：mathlib 已有 `Complex.normSq`（`normSq z = ‖z‖²`）与
     `Complex.mul_conj`（`z * conj z = ↑(normSq z)`），据此给出
     `‖z‖² = z·conj z`、`‖z‖² = RCLike.re (z * conj z)`、
     内积共轭对称 `⟨x,y⟩ = conj ⟨y,x⟩`（实数域没有此性质）等。

诚实性：所有定理只引用 mathlib 4.14 现成引理与既有文件定理，无 sorry/axiom/admit。
-/

noncomputable section

open scoped Topology ComplexConjugate

namespace Lattice

variable {E F : Type*}

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法；本文件在 ℂ 上使用
与 RealInnerScalar 一致的显式本地记法（固定 𝕜 := ℂ，避免类型类元变量卡死）。-/
local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-! ## 第一节：ℂ 复数代数基础（mathlib 现成 → 引用/重述） -/

/-! RCLike.re 在 ℂ 上就是 Complex.re（mathlib `RCLike.re_eq_complex_re`）。-/

theorem complex_re_eq_RCLike_re (z : ℂ) : RCLike.re z = z.re := by
  rfl

theorem complex_im_eq_RCLike_im (z : ℂ) : RCLike.im z = z.im := by
  rfl

/-! `Complex.normSq z = ‖z‖²`（mathlib `Complex.normSq_eq_norm_sq`）。-/

theorem complex_normSq_eq_norm_sq (z : ℂ) : Complex.normSq z = ‖z‖ ^ 2 :=
  Complex.normSq_eq_norm_sq z

/-! `z * conj z = ↑(normSq z)`（mathlib `Complex.mul_conj`）。-/

theorem complex_mul_conj_eq_normSq (z : ℂ) : z * conj z = (Complex.normSq z : ℂ) :=
  Complex.mul_conj z

/-! ‖z‖² = z · conj z（ℂ 上 |z|² = z·conj z；由上面两条桥接）。-/

theorem complex_norm_sq_eq_mul_conj (z : ℂ) : (‖z‖ ^ 2 : ℂ) = z * conj z := by
  simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj z).symm

/-! `normSq z` 非负（由 normSq = ‖z‖² 与平方非负给出）。-/

theorem complex_normSq_nonneg (z : ℂ) : 0 ≤ Complex.normSq z := by
  rw [Complex.normSq_eq_norm_sq]
  exact sq_nonneg ‖z‖

/-! ## 第二节：ℂ 实例化（既有任意域定理 → ℂ 实例） -/

/-! ‖z‖² = re⟨z, z⟩ 的 ℂ 自身一维实例：
ℂ 标准内积 `inner z z = conj z * z = z * conj z`，
故 `‖z‖² = RCLike.re (z * conj z)`（`inner_self_eq_norm_sq` + `Complex.mul_conj`）。-/

theorem complex_inner_self_norm_sq (z : ℂ) : ‖z‖ ^ 2 = RCLike.re (z * conj z) := by
  calc
    ‖z‖ ^ 2 = RCLike.re (inner z z) := (inner_self_eq_norm_sq (𝕜 := ℂ) z).symm
    _ = RCLike.re (z * conj z) := by
      have h : inner z z = z * conj z := by
        -- 用 RCLike.ext 证明两复数相等：re 与 im 分量分别相等
        apply RCLike.ext
        · -- re(inner z z) = re(z · conj z)：两边都是 ‖z‖²
          calc
            RCLike.re (inner z z) = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) z
            _ = (z * conj z).re := by
              -- (z·conj z).re = normSq z = ‖z‖²
              rw [Complex.mul_conj z, Complex.ofReal_re]
              exact (Complex.normSq_eq_norm_sq z).symm
            _ = RCLike.re (z * conj z) := (complex_re_eq_RCLike_re (z * conj z)).symm
        · -- im(inner z z) = 0 = im(z · conj z)（自内积虚部为 0，z·conj z 是实数）
          rw [inner_self_im (𝕜 := ℂ) z]
          rw [Complex.mul_conj z, complex_im_eq_RCLike_im]
          simp
      rw [h]

/-! 泛 E 上的内积范数恒等式（𝕜 := ℂ 实例，即 `inner_self_norm_sq_scalar` 的 ℂ 版）。-/

theorem complex_inner_self_norm_sq_instance [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : ‖x‖ ^ 2 = RCLike.re ⟪x, x⟫ :=
  inner_self_norm_sq_scalar (𝕜 := ℂ) x

/-! 等距保范数（𝕜 := ℂ 实例）：保 ℂ-内积的映射保范数。 -/

theorem complex_isometry_preserves_norm [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E → E) (hT : ∀ q k : E, ⟪T q, T k⟫ = ⟪q, k⟫) :
    ∀ x : E, ‖T x‖ = ‖x‖ :=
  isometry_preserves_norm_scalar (𝕜 := ℂ) T hT

/-! 等距复合闭合（𝕜 := ℂ 实例）。 -/

theorem complex_isometry_scalar_compose [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T S : E → E) (hT : ∀ q k : E, ⟪T q, T k⟫ = ⟪q, k⟫)
    (hS : ∀ q k : E, ⟪S q, S k⟫ = ⟪q, k⟫) :
    ∀ q k : E, ⟪T (S q), T (S k)⟫ = ⟪q, k⟫ :=
  isometry_scalar_compose (𝕜 := ℂ) T S hT hS

/-! 编辑输出变化界（𝕜 := ℂ 实例）：‖W'x − Wx‖ ≤ ‖W'−W‖·‖x‖。
这是 `edit_output_bound_scalar (𝕜 := ℂ)` 的一行实例化。 -/

theorem complex_edit_output_bound [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (W W' : E →L[ℂ] F) (x : E) :
    ‖W' x - W x‖ ≤ ‖W' - W‖ * ‖x‖ :=
  edit_output_bound_scalar (𝕜 := ℂ) W W' x

/-! 编辑后标量约束近似保持（𝕜 := ℂ 实例）。 -/

theorem complex_edit_preserves_constraint [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W W' : E →L[ℂ] ℂ) (x : E) (h : W x = 0) :
    ‖W' x‖ ≤ ‖W' - W‖ * ‖x‖ :=
  edit_preserves_constraint_scalar (𝕜 := ℂ) W W' x h

/-! 容差判定（𝕜 := ℂ 实例）。 -/

theorem complex_edit_verify_tolerance [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W W' : E →L[ℂ] ℂ) (x : E) (ε : ℝ) (h : W x = 0) (hε : ‖W' - W‖ * ‖x‖ ≤ ε) :
    ‖W' x‖ ≤ ε :=
  edit_verify_tolerance_scalar (𝕜 := ℂ) W W' x ε h hε

/-! 残差误差隔离（既有定理的 ℂ 域实例；其陈述不含 𝕜，域无关）：
‖(x+Fx)−(x+Gx)‖ = ‖Fx−Gx‖。 -/

theorem complex_residual_error_isolation [NormedAddCommGroup E]
    (x Fx Gx : E) : ‖(x + Fx) - (x + Gx)‖ = ‖Fx - Gx‖ :=
  residual_error_isolation_scalar x Fx Gx

/-! 残差编辑局部性（𝕜 := ℂ 实例）。 -/

theorem complex_residual_edit_local [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : E) (F F' : E →L[ℂ] E) :
    ‖ResidualS (𝕜 := ℂ) F' x - ResidualS (𝕜 := ℂ) F x‖ ≤ ‖F' - F‖ * ‖x‖ :=
  residual_edit_local_scalar (𝕜 := ℂ) x F F'

/-! 仿射（带偏置）编辑的输出变化界（𝕜 := ℂ 实例）。 -/

theorem complex_affine_edit_output_bound [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W W' : E →L[ℂ] ℂ) (b b' : ℂ) (x : E) :
    ‖(W' x + b') - (W x + b)‖ ≤ ‖W' - W‖ * ‖x‖ + ‖b' - b‖ :=
  affine_edit_output_bound_scalar (𝕜 := ℂ) W W' b b' x

/-! 仿射编辑容差判定（𝕜 := ℂ 实例）。 -/

theorem complex_edit_verify_tolerance_affine [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W W' : E →L[ℂ] ℂ) (b b' : ℂ) (x : E) (ε₁ ε₂ X : ℝ) (h : W x + b = 0)
    (hε₁ : ‖W' - W‖ ≤ ε₁) (hε₂ : ‖b' - b‖ ≤ ε₂) (hx : ‖x‖ ≤ X) :
    ‖W' x + b'‖ ≤ ε₁ * X + ε₂ :=
  edit_verify_tolerance_scalar_affine (𝕜 := ℂ) W W' b b' x ε₁ ε₂ X h hε₁ hε₂ hx

/-! P0 一般法方程（𝕜 := ℂ 实例）：实化驻点 ⟺ 满足（一致系统）。
L(x) = ‖A·x − b‖²，fderiv ℝ L x = 0 ⟺ A x = b。 -/

theorem complex_P0_normal_equation [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (A : E →L[ℂ] F) (b : F) (x : E) (hb : b ∈ LinearMap.range (A : E →ₗ[ℂ] F)) :
    fderiv ℝ (NormSqLossScalar A b) x = 0 ↔ A x = b :=
  P0_normal_equation_scalar (𝕜 := ℂ) A b x hb

/-! ## 第三节：ℂ 特有性质（实数域没有：ℝ 上 conj 是恒等，共轭对称退化为对称） -/

/-! 内积共轭对称性：⟨x, y⟩ = conj ⟨y, x⟩（mathlib `inner_conj_symm` 的 𝕜 := ℂ 实例）。-/

theorem complex_inner_conj_symm [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) : ⟪x, y⟫ = conj ⟪y, x⟫ := by
  simp

/-! 自内积的共轭不动性：conj ⟨x, x⟩ = ⟨x, x⟩（⟨x,x⟩ 是实数）。
ℝ 上平凡（conj = id）；ℂ 上由 im(⟨x,x⟩) = 0 与 re 分量相等给出。 -/

theorem complex_conj_inner_self [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : conj ⟪x, x⟫ = ⟪x, x⟫ := by
  apply RCLike.ext
  · -- re(conj ⟨x,x⟩) = re(⟨x,x⟩)
    calc
      RCLike.re (conj ⟪x, x⟫) = (conj ⟪x, x⟫).re := complex_re_eq_RCLike_re _
      _ = ⟪x, x⟫.re := Complex.conj_re _
      _ = RCLike.re ⟪x, x⟫ := (complex_re_eq_RCLike_re _).symm
  · -- im(conj ⟨x,x⟩) = -im(⟨x,x⟩) = 0 = im(⟨x,x⟩)
    calc
      RCLike.im (conj ⟪x, x⟫) = (conj ⟪x, x⟫).im := complex_im_eq_RCLike_im _
      _ = -⟪x, x⟫.im := Complex.conj_im _
      _ = 0 := by
        -- im(⟨x,x⟩) = 0（inner_self_im，经 complex_im_eq_RCLike_im 桥接）
        rw [← complex_im_eq_RCLike_im ⟪x, x⟫]
        rw [inner_self_im (𝕜 := ℂ) x]
        simp
      _ = RCLike.im ⟪x, x⟫ := (inner_self_im (𝕜 := ℂ) x).symm

/-! 自内积实部非负：0 ≤ re⟨x, x⟩（mathlib `inner_self_nonneg` 的 𝕜 := ℂ 实例）。-/

theorem complex_inner_self_re_nonneg [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : 0 ≤ RCLike.re ⟪x, x⟫ :=
  inner_self_nonneg (𝕜 := ℂ)

/-! ## 第四节：ℂ 值线性代数实例（具体空间：EuclideanSpace ℂ (Fin d)） -/

theorem complex_euclid_edit_output_bound (d : ℕ) (W W' : EuclideanSpace ℂ (Fin d) →L[ℂ] ℂ)
    (x : EuclideanSpace ℂ (Fin d)) : ‖W' x - W x‖ ≤ ‖W' - W‖ * ‖x‖ :=
  complex_edit_output_bound W W' x

theorem complex_euclid_inner_self_norm_sq (d : ℕ) (x : EuclideanSpace ℂ (Fin d)) :
    ‖x‖ ^ 2 = RCLike.re ⟪x, x⟫ :=
  complex_inner_self_norm_sq_instance x

theorem complex_euclid_isometry_preserves_norm (d : ℕ)
    (T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin d))
    (hT : ∀ q k : EuclideanSpace ℂ (Fin d), ⟪T q, T k⟫ = ⟪q, k⟫) :
    ∀ x : EuclideanSpace ℂ (Fin d), ‖T x‖ = ‖x‖ :=
  complex_isometry_preserves_norm T hT

theorem complex_euclid_inner_conj_symm (d : ℕ) (x y : EuclideanSpace ℂ (Fin d)) :
    ⟪x, y⟫ = conj ⟪y, x⟫ :=
  complex_inner_conj_symm x y

theorem complex_euclid_normal_equation (d : ℕ)
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (b x : EuclideanSpace ℂ (Fin d))
    (hb : b ∈ LinearMap.range (A : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))) :
    fderiv ℝ (NormSqLossScalar A b) x = 0 ↔ A x = b :=
  complex_P0_normal_equation A b x hb

/-! ## 注：复数全链后续
ℂ 特有链继续铺路：全纯/共轭导数（Wirtinger）、ℂ-伴随（ContinuousLinearMap.adjoint）、
幺正族（unitary）等可基于本节实例定理展开；实数版（Real* 系列）均为 𝕜 := ℝ 特例。 -/

end Lattice
