import Mathlib

/-!
# LATTICE: ROME 局部性 —— rank-one 编辑的精确"其余保持"

权重编辑调研（research/real-world/model-edit-math.md 目标 1）：
ROME 的 rank-one 编辑（对键 k₀ 写入值 v*，最小范数解）

  W'·x = W·x + ⟨k₀, x⟩ · (v* − W·k₀) / ‖k₀‖²

的三条精确性质：
  ① 事实写入：W'·k₀ = v*（编辑目标精确命中）；
  ② 正交补不变：⟨k₀, x⟩ = 0 ⟹ W'·x = W·x（"其余保持"的精确形式，ε = 0）；
  ③ 逐点编辑量：|W'·x − W·x| = |⟨k₀,x⟩|·|v*−W·k₀| / ‖k₀‖²。

"其余保持"的高维近似部分（经验）明确非定理，留给验证器；
本文件证明其可证内核（正交补精确保持）。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## ROME rank-one 编辑（标量行版：E →L[ℝ] ℝ） -/

def ROME (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (x : E) : ℝ :=
  W x + inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2)

/-! ## 引理：键向量的范数平方非零（k₀ ≠ 0 时） -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma key_norm_sq_ne_zero (k₀ : E) (hk : k₀ ≠ 0) : ‖k₀‖ ^ 2 ≠ 0 := by
  have hn : ‖k₀‖ ≠ 0 := by
    intro hz
    exact hk (norm_eq_zero.mp hz)
  exact pow_ne_zero 2 hn

/-! ## 定理一：事实精确写入
W'·k₀ = v*（编辑目标精确命中）。-/

theorem ROME_writes_fact (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (hk : k₀ ≠ 0) :
    ROME W k₀ v k₀ = v := by
  unfold ROME
  -- inner k₀ k₀ = ‖k₀‖²
  have hnorm : inner k₀ k₀ = ‖k₀‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℝ) k₀
  calc
    W k₀ + inner k₀ k₀ * ((v - W k₀) / ‖k₀‖ ^ 2)
        = W k₀ + ‖k₀‖ ^ 2 * ((v - W k₀) / ‖k₀‖ ^ 2) := by rw [hnorm]
    _ = W k₀ + (v - W k₀) := by
      -- ‖k₀‖² · (d/‖k₀‖²) = d（消去）
      have hk : ‖k₀‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₀ hk
      field_simp [hk]
    _ = v := by ring

/-! ## 定理二：正交补精确不变（其余保持，ε = 0）
⟨k₀, x⟩ = 0 ⟹ W'·x = W·x。-/

omit [CompleteSpace E] in
theorem ROME_preserves_orthogonal (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (x : E)
    (hx : inner k₀ x = (0 : ℝ)) :
    ROME W k₀ v x = W x := by
  unfold ROME
  calc
    W x + inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2)
        = W x + 0 * ((v - W k₀) / ‖k₀‖ ^ 2) := by rw [hx]
    _ = W x := by ring

/-! ## 定理三：逐点编辑量
|W'·x − W·x| = |⟨k₀,x⟩|·|v*−W·k₀| / ‖k₀‖²。-/

theorem ROME_pointwise_edit (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (x : E) (hk : k₀ ≠ 0) :
    |ROME W k₀ v x - W x| = |inner k₀ x| * |v - W k₀| / ‖k₀‖ ^ 2 := by
  unfold ROME
  -- ROME - Wx = inner k₀ x · (d/‖k₀‖²)
  have hdiff : W x + inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2) - W x =
      inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2) := by ring
  calc
    |W x + inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2) - W x|
        = |inner k₀ x * ((v - W k₀) / ‖k₀‖ ^ 2)| := by rw [hdiff]
    _ = |inner k₀ x| * |(v - W k₀) / ‖k₀‖ ^ 2| := abs_mul _ _
    _ = |inner k₀ x| * |v - W k₀| / ‖k₀‖ ^ 2 := by
      -- |d/‖k₀‖²| = |d|/‖k₀‖²（‖k₀‖² > 0）
      have hk : ‖k₀‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₀ hk
      have hpos : 0 ≤ ‖k₀‖ ^ 2 := sq_nonneg _
      have : |(v - W k₀) / ‖k₀‖ ^ 2| = |v - W k₀| / ‖k₀‖ ^ 2 := by
        rw [abs_div, abs_of_nonneg hpos]
      rw [this]
      ring

/-! ## 推论：逐神经元输出变化（行语义）
约束在某行上的输出变化恰为 u·⟨k₀,x⟩——衔接提取契约（编辑后约束多一项）。-/

theorem ROME_row_change (W : E →L[ℝ] ℝ) (k₀ : E) (v : ℝ) (x : E)
    (hx : inner k₀ x = (0 : ℝ)) (h : W x = 0) :
    ROME W k₀ v x = 0 := by
  rw [ROME_preserves_orthogonal W k₀ v x hx]
  exact h

end Lattice
