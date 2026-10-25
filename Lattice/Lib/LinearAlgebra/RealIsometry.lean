import Mathlib
import Lattice.Lib.Attention.RealRoPE
/-!
# LATTICE: 等距保范数 —— 正交变换族的统一性质（任意内积空间）

审计建议 ③（RoPE 维度分块参数化）的抽象核心：
任何**保内积的变换（等距）**在任意内积空间上保范数：

  ⟨T·q, T·k⟩ = ⟨q, k⟩（∀q k）⟹ ‖T·x‖ = ‖x‖（∀x）

这统一了 RoPE（2D 已证 rotate_preserves_dot）、任意维度旋转、
正交矩阵等一切正交变换族的保长度性质——比 Fin 分块簿记更通用。

模型无关：任意内积空间、任意保内积变换。
-/


noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 等距（保内积） -/

def Isometry (T : E → E) : Prop :=
  ∀ q k : E, (inner (T q) (T k) : ℝ) = (inner q k : ℝ)

/-! ## 定理：等距保范数
⟨Tq, Tk⟩ = ⟨q,k⟩（∀q k）⟹ ‖T·x‖ = ‖x‖。-/

theorem isometry_preserves_norm (T : E → E) (hT : Isometry T) :
    ∀ x : E, ‖T x‖ = ‖x‖ := by
  intro x
  -- ‖Tx‖² = ⟨Tx,Tx⟩ = ⟨x,x⟩ = ‖x‖²
  -- mathlib 4.14：inner_self_eq_norm_sq 带 re（RCLike.re ⟪x,x⟫ = ‖x‖²），
  -- 实内积空间用 real_inner_self_eq_norm_sq（无 re）
  have hsq : ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (T x), ← real_inner_self_eq_norm_sq x]
    exact hT x x
  -- 非负数：sqrt(‖·‖²) = ‖·‖（去绝对值）
  -- mathlib 4.14：Real.sqrt_sq_eq_abs 的参数是数值而非证明
  calc
    ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs (‖T x‖)]
      exact (abs_of_nonneg (norm_nonneg (T x))).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := by
      rw [Real.sqrt_sq_eq_abs (‖x‖)]
      exact abs_of_nonneg (norm_nonneg x)

/-! ## 推论一：等距保内积绝对值（分数稳定性）
|⟨Tq, Tk⟩| = |⟨q,k⟩|——正交变换保持相似度分数（注意力分数稳定性）。-/

theorem isometry_preserves_inner_abs (T : E → E) (hT : Isometry T) :
    ∀ q k : E, |(inner (T q) (T k) : ℝ)| = |(inner q k : ℝ)| := by
  intro q k
  rw [hT q k]

/-! ## 推论二：等距的复合仍是等距（正交族闭合）
T、S 都保内积 ⟹ T∘S 也保内积（正交变换族在复合下闭合）。-/

theorem isometry_compose (T S : E → E) (hT : Isometry T) (hS : Isometry S) :
    Isometry (fun x => T (S x)) := by
  intro q k
  calc
    inner (T (S q)) (T (S k)) = inner (S q) (S k) := hT (S q) (S k)
    _ = inner q k := hS q k

/-! ## 推论三：RoPE 2D 旋转保范数（实例化 rdot 版）
旋转保点积（rotate_preserves_dot，已证）⟹ 旋转保长度。
-/

theorem rotateR_preserves_norm_rdot (θ : ℝ) (p : Point2R) :
    rdot (rotateR θ p) (rotateR θ p) = rdot p p := by
  exact rotate_preserves_dot θ p p

/-! ## 注：任意维度实例化
对 Fin n 分块旋转：每块 2D 正交（rotate_preserves_dot），
由 isometry_compose（块组合闭合）+ isometry_preserves_norm 得整体保范数。
抽象定理已覆盖任意维度，无需 Fin 簿记。 -/

end Lattice
