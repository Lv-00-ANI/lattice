import Mathlib

/-!
# LATTICE: MEMIT 加法界 —— 多层分布式编辑的总界

权重编辑调研（research/real-world/model-edit-math.md 备选三）：
MEMIT 在 L 层分布式编辑（每层编辑算子 Δ_l），总编辑效果是各层贡献之和：

  ‖Σ_l Δ_l·x‖ ≤ Σ_l ‖Δ_l·x‖ ≤ (Σ_l ‖Δ_l‖) · ‖x‖

（三角不等式 + 每层算子范数 Lipschitz）

推论：每层编辑有界（‖Δ_l‖ ≤ ε_l）⟹ 总编辑界 ≤ (Σε_l)·‖x‖——
MEMIT 的 ε 链归约到已有的 edit_tolerance_verdict（RealEditVerdict）。

模型无关：任意层指标、任意算子。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## MEMIT 层编辑总和 -/

def sumEdits {L : Type*} [Fintype L] (Δ : L → E →L[ℝ] F) (x : E) : F :=
  ∑ l, Δ l x

/-! ## 定理一：加法界（三角 + 算子范数）
‖Σ_l Δ_l·x‖ ≤ (Σ_l ‖Δ_l‖)·‖x‖。-/

theorem memit_additive_bound {L : Type*} [Fintype L] (Δ : L → E →L[ℝ] F) (x : E) :
    ‖sumEdits Δ x‖ ≤ (∑ l, ‖Δ l‖) * ‖x‖ := by
  unfold sumEdits
  calc
    ‖∑ l, Δ l x‖ ≤ ∑ l, ‖Δ l x‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖Δ l‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro l hl
      exact (Δ l).le_opNorm x
    _ = (∑ l, ‖Δ l‖) * ‖x‖ := by
      rw [Finset.sum_mul]

/-! ## 定理二：每层有界 ⟹ 总界
‖Δ_l‖ ≤ ε_l ⟹ ‖Σ_l Δ_l·x‖ ≤ (Σε_l)·‖x‖。-/

theorem memit_edit_bound {L : Type*} [Fintype L] (Δ : L → E →L[ℝ] F) (x : E)
    (ε : L → ℝ) (hε : ∀ l, ‖Δ l‖ ≤ ε l) :
    ‖sumEdits Δ x‖ ≤ (∑ l, ε l) * ‖x‖ := by
  calc
    ‖sumEdits Δ x‖ ≤ (∑ l, ‖Δ l‖) * ‖x‖ := memit_additive_bound Δ x
    _ ≤ (∑ l, ε l) * ‖x‖ := by
      have hsum : ∑ l, ‖Δ l‖ ≤ ∑ l, ε l :=
        Finset.sum_le_sum (fun l hl => hε l)
      exact mul_le_mul_of_nonneg_right hsum (norm_nonneg x)

/-! ## 推论：MEMIT 编辑后约束保持（衔接 edit_tolerance_verdict）
总编辑界 (Σε_l)·‖x‖ 代入 Verdict 判定：原约束满足 ⟹ 编辑后损失 ≤ ((Σε_l)X)²。 -/

theorem memit_edit_verdict {L : Type*} [Fintype L] (Δ : L → E →L[ℝ] E) (x : E)
    (ε : L → ℝ) (W : E →L[ℝ] ℝ) (b X : ℝ)
    (hε : ∀ l, ‖Δ l‖ ≤ ε l) (hx : ‖x‖ ≤ X)
    (h0 : W x + b = 0) :
    |W (sumEdits Δ x + x) + b| ≤ ‖W‖ * ((∑ l, ε l) * X) := by
  -- 编辑后输入 = x + ΣΔx（残差式编辑）；输出变化 = W(ΣΔx)
  have hW : |W (sumEdits Δ x + x) + b - (W x + b)| = |W (sumEdits Δ x)| := by
    -- W 线性：W(x + ΣΔx) - W x = W(ΣΔx)；b 抵消
    congr 1
    calc
      W (sumEdits Δ x + x) + b - (W x + b) = W (sumEdits Δ x + x) - W x := by ring
      _ = W (sumEdits Δ x) := by
        -- 线性映射：W(a + b) - W(a) = W(b)
        have : W (sumEdits Δ x + x) - W x = W (sumEdits Δ x + x - x) := by
          exact (W.map_sub (sumEdits Δ x + x) x).symm
        rw [this]
        congr 1
        abel
  calc
    |W (sumEdits Δ x + x) + b| = |W (sumEdits Δ x + x) + b - (W x + b)| := by
      rw [h0]
      simp
    _ = |W (sumEdits Δ x)| := hW
    _ ≤ ‖W‖ * ‖sumEdits Δ x‖ := W.le_opNorm _
    _ ≤ ‖W‖ * ((∑ l, ε l) * ‖x‖) := by
      have hb : ‖sumEdits Δ x‖ ≤ (∑ l, ε l) * ‖x‖ := memit_edit_bound Δ x ε hε
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg W)
    _ ≤ ‖W‖ * ((∑ l, ε l) * X) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (Finset.sum_nonneg (fun l _ => le_trans (norm_nonneg (Δ l)) (hε l)))) (norm_nonneg W)

end Lattice
