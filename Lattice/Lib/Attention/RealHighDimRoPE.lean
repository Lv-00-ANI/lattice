import Mathlib
import Lattice.Lib.Attention.RealRoPE
/-!
# LATTICE: 高维分块 RoPE（Fin n 分块旋转）

RealRoPE 只在 2D 上陈述旋转位置编码（`rotateR` / `rope_relative_preserves_dot`）。
原始 RoPE 把 d 维向量按 2 维分块，**每一块用不同频率**旋转：

    BlockRotate(θ)(u)_i = R(θ_i) · u_i       （u_i ∈ ℝ² 是第 i 个 2D 块）

本文件把 2D 结果逐块提升到「n 个 2D 块」：

  1. `blockRotate`（def）：逐块用角度 θ_i 做 `rotateR`；
  2. `blockDot`（def）：分块内积 `Σ_i ⟨u_i, v_i⟩`；
  3. `block_rotate_preserves_dot`（核心）：分块旋转保内积（逐块 `rotate_preserves_dot` + 有限和）；
  4. `block_rotate_compose`：分块旋转的组合（逐块 `rotate_compose`）；
  5. `block_rope_relative_preserves_dot`（核心）：每块角度为 m·θ_i 时相对位置保点积；
  6. `block_rope_isometry` / `block_rotate_preserves_norm`（加分）：分块旋转保（平方）范数。

模型无关：维度 d、频率 θ : Fin d → ℝ、位置 m、p 全为任意参数；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 定义：分块旋转与分块内积 -/

/-- 分块旋转：对第 i 个 2D 块用角度 `θ i` 做 `rotateR`。 -/
def blockRotate {d : ℕ} (θ : Fin d → ℝ) (u : Fin d → Point2R) : Fin d → Point2R :=
  fun i => rotateR (θ i) (u i)

/-- 分块内积：各块 2D 内积之和 `Σ_i ⟨u_i, v_i⟩`（把 d 维向量的内积写成 2D 块内积之和）。 -/
def blockDot {d : ℕ} (u v : Fin d → Point2R) : ℝ :=
  ∑ i, rdot (u i) (v i)

/-- 分块平方范数 `‖u‖² = Σ_i ⟨u_i, u_i⟩`。 -/
def blockNormSq {d : ℕ} (u : Fin d → Point2R) : ℝ := blockDot u u

/-- 分块范数 `‖u‖ = sqrt(‖u‖²)`。 -/
def blockNorm {d : ℕ} (u : Fin d → Point2R) : ℝ := Real.sqrt (blockNormSq u)

/-! ## 定理一（核心）：分块旋转保内积
`Σ_i ⟨R(θ_i)u_i, R(θ_i)v_i⟩ = Σ_i ⟨u_i, v_i⟩`（逐块正交 + 有限和保持相等）。-/

theorem block_rotate_preserves_dot {d : ℕ} (θ : Fin d → ℝ) (u v : Fin d → Point2R) :
    blockDot (blockRotate θ u) (blockRotate θ v) = blockDot u v := by
  unfold blockDot
  refine Finset.sum_congr rfl ?_
  intro i _
  exact rotate_preserves_dot (θ i) (u i) (v i)

/-! ## 定理二：分块旋转的组合
`BlockRotate(a) ∘ BlockRotate(b) = BlockRotate(a + b)`（逐块 `rotate_compose`）。-/

theorem block_rotate_compose {d : ℕ} (a b : Fin d → ℝ) (u : Fin d → Point2R) :
    blockRotate a (blockRotate b u) = blockRotate (fun i => a i + b i) u := by
  funext i
  exact rotate_compose (a i) (b i) (u i)

/-! ## 定理三（核心）：分块 RoPE 相对位置保点积
查询在位置 `m`（每块角度 `m·θ_i`）、键在位置 `p`（每块角度 `p·θ_i`）时，
`⟨BlockRotate(mθ)q, BlockRotate(pθ)k⟩ = ⟨q, BlockRotate((p−m)θ)k⟩`。
逐块用 `rope_relative_preserves_dot`（相对角度只依赖 p − m），再取和。-/

theorem block_rope_relative_preserves_dot {d : ℕ} (m p : ℝ) (θ : Fin d → ℝ)
    (q k : Fin d → Point2R) :
    blockDot (blockRotate (fun i => m * θ i) q) (blockRotate (fun i => p * θ i) k) =
      blockDot q (blockRotate (fun i => (p - m) * θ i) k) := by
  unfold blockDot
  refine Finset.sum_congr rfl ?_
  intro i _
  exact rope_relative_preserves_dot m p (θ i) (q i) (k i)

/-! ## 定理四（加分）：分块旋转是等距（保平方范数） -/

theorem block_rotate_preserves_normSq {d : ℕ} (θ : Fin d → ℝ) (u : Fin d → Point2R) :
    blockNormSq (blockRotate θ u) = blockNormSq u :=
  block_rotate_preserves_dot θ u u

/-- 分块旋转保（平方范数的）范数 `‖BlockRotate(θ)u‖ = ‖u‖`。 -/
theorem block_rotate_preserves_norm {d : ℕ} (θ : Fin d → ℝ) (u : Fin d → Point2R) :
    blockNorm (blockRotate θ u) = blockNorm u := by
  unfold blockNorm
  rw [block_rotate_preserves_normSq]

/-! ## 推论：RoPE 分块变换的等距性
相对位置变换 `u ↦ BlockRotate((p−m)θ) u` 是等距（保平方范数），
故分块 RoPE 是 ℝ^{2d} 上的正交变换——注意力分数在位置编码下稳定。 -/

theorem block_rope_isometry {d : ℕ} (m p : ℝ) (θ : Fin d → ℝ) (u : Fin d → Point2R) :
    blockNormSq (blockRotate (fun i => (p - m) * θ i) u) = blockNormSq u :=
  block_rotate_preserves_normSq (fun i => (p - m) * θ i) u

end Lattice
