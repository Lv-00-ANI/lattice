import Mathlib

/-!
# LATTICE: 内积空间参数化基础 —— 𝕜-内积的范数恒等式与等距保范数

内积空间参数化（法方程 𝕜 版的铺路）：
mathlib 的 InnerProductSpace 已泛化到 RCLike 𝕜（ℝ/ℂ），
范数平方恒等式与等距保范数在任意 𝕜-内积空间成立：

  1. ‖x‖² = re⟨x, x⟩（𝕜-内积的范数恒等式，mathlib 泛化）；
  2. 保 𝕜-内积的等距保范数：⟨Tq,Tk⟩=⟨q,k⟩（∀q k）⟹ ‖Tx‖=‖x‖。

这是 RealNormalEquation（法方程）𝕜 版的基础：伴随/正交补的 𝕜 版本
在 mathlib 已存在（adjoint/orthogonal 对 RCLike 𝕜），本文件补齐范数层。

模型无关：任意 RCLike 域、任意内积空间。
-/

noncomputable section

namespace Lattice

variable {𝕜 E : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法（仅 ℝ/ℂ 有裸记法），
此处为任意 RCLike 𝕜 声明本地记法（与 mathlib 内部做法一致）。-/
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-! ## 定理一：𝕜-内积的范数平方恒等式
‖x‖² = re⟨x, x⟩（mathlib inner_self_eq_norm_sq 的 𝕜 泛化）。-/

theorem inner_self_norm_sq_scalar (x : E) :
    ‖x‖ ^ 2 = RCLike.re ⟪x, x⟫ := by
  exact (inner_self_eq_norm_sq x).symm

/-! ## 定义：保 𝕜-内积（等距） -/

def IsometryScalar (T : E → E) : Prop :=
  ∀ q k : E, ⟪T q, T k⟫ = ⟪q, k⟫

/-! ## 定理二：等距保范数（𝕜 版）
⟨Tq,Tk⟩=⟨q,k⟩（∀q k）⟹ ‖Tx‖ = ‖x‖。-/

theorem isometry_preserves_norm_scalar (T : E → E)
    (hT : ∀ q k : E, ⟪T q, T k⟫ = ⟪q, k⟫) :
    ∀ x : E, ‖T x‖ = ‖x‖ := by
  intro x
  -- ‖Tx‖² = re⟨Tx,Tx⟩ = re⟨x,x⟩ = ‖x‖²
  have hsq : ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [inner_self_norm_sq_scalar (𝕜 := 𝕜) (T x), inner_self_norm_sq_scalar (𝕜 := 𝕜) x]
    -- re 保等式：hT 给 ⟨Tx,Tx⟩ = ⟨x,x⟩，re 作用相同
    exact congrArg RCLike.re (hT x x)
  -- 非负数：sqrt(‖·‖²) = ‖·‖
  calc
    ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs (‖T x‖), abs_of_nonneg (norm_nonneg (T x))]
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := by
      rw [Real.sqrt_sq_eq_abs (‖x‖), abs_of_nonneg (norm_nonneg x)]

/-! ## 推论：𝕜-内积空间的等距复合闭合（正交族）
T、S 都保内积 ⟹ T∘S 保内积（正交变换族在 𝕜 下闭合）。-/

theorem isometry_scalar_compose (T S : E → E)
    (hT : ∀ q k : E, ⟪T q, T k⟫ = ⟪q, k⟫) (hS : ∀ q k : E, ⟪S q, S k⟫ = ⟪q, k⟫) :
    ∀ q k : E, ⟪T (S q), T (S k)⟫ = ⟪q, k⟫ := by
  intro q k
  calc
    ⟪T (S q), T (S k)⟫ = ⟪S q, S k⟫ := hT (S q) (S k)
    _ = ⟪q, k⟫ := hS q k

/-! ## 注：法方程 𝕜 版铺路
伴随（ContinuousLinearMap.adjoint，RCLike 𝕜）、正交补（Submodule.orthogonal）
与 fderiv 𝕜 在 mathlib 已存在；配合本文件的范数恒等式，
RealNormalEquation 的 𝕜 版仅需机械改写（ℝ 特化 → RCLike 𝕜）。 -/

end Lattice
