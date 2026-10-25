import Mathlib
import Lattice.Lib.Editing.RealEditSeq
/-!
# LATTICE: 非均匀顺序编辑 —— 每步不同界 δᵢ 的累积

P-Edit（RealEditSeq）的通用化：真实编辑序列每步编辑量不同，
均匀界（每步 ≤ δ）过于粗糙。非均匀版：

  ‖W_k·x − W_0·x‖ ≤ Σ_{i<k} δᵢ    （每步界 δᵢ 不同）

归纳同构，但累积是"逐项求和"而非"k·δ"。`δ i` 为任意实数序列，
既不要求单调也不要求非负，故每步编辑量各异的真实情况（大编辑后接小微调）
只是其中一个实例。

模型无关：任意算子、任意步界函数。
-/


noncomputable section

namespace Lattice

-- RealEditSeq 的声明都在 `Lattice` 命名空间下（本文件已 import RealEditSeq），无需 open。

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定理：非均匀顺序编辑误差累积
每步输出变化 ≤ δᵢ，k 步后 ‖W_k x − W_0 x‖ ≤ Σ_{i<k} δᵢ。-/

theorem edit_seq_nonuniform (W : Nat → E →L[ℝ] F) (x : E) (n : Nat) (δ : Nat → ℝ)
    (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ i) :
    ‖W n x - W 0 x‖ ≤ ∑ i in Finset.range n, δ i := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- 限制到 i < n（供归纳假设）
      have hstep' : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ i :=
        fun i hi => hstep i (by omega)
      -- 最后一步 ≤ δ n
      have hlast : ‖W (n + 1) x - W n x‖ ≤ δ n := hstep n (by omega)
      calc
        ‖W (n + 1) x - W 0 x‖ ≤ ‖W (n + 1) x - W n x‖ + ‖W n x - W 0 x‖ :=
          edit_two_step (W 0) (W n) (W (n + 1)) x
        _ ≤ δ n + ∑ i in Finset.range n, δ i := by
          exact add_le_add hlast (ih hstep')
        _ = ∑ i in Finset.range (n + 1), δ i := by
          rw [Finset.sum_range_succ]
          ring

/-! ## 推论：非均匀编辑后的约束近似保持
原约束满足（W_0 x = 0）⟹ 编辑后 ‖W_k x‖ ≤ Σ_{i<k} δᵢ。-/

theorem edit_seq_nonuniform_constraint (W : Nat → E →L[ℝ] ℝ) (x : E) (n : Nat) (δ : Nat → ℝ)
    (h0 : W 0 x = 0) (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ i) :
    ‖W n x‖ ≤ ∑ i in Finset.range n, δ i := by
  calc
    ‖W n x‖ = ‖W n x - W 0 x‖ := by
      rw [h0]
      simp
    _ ≤ ∑ i in Finset.range n, δ i := edit_seq_nonuniform W x n δ hstep

/-! ## 推论：均匀界是非均匀的特例
每步同界 δ（δᵢ = δ）⟹ 累积 = n·δ（衔接 RealEditSeq）。-/

theorem edit_seq_uniform_as_special (W : Nat → E →L[ℝ] F) (x : E) (n : Nat) (δ : ℝ)
    (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ) :
    ‖W n x - W 0 x‖ ≤ (n : ℝ) * δ := by
  -- 用非均匀版（δᵢ := δ）+ 求和 = n·δ
  have hnon : ‖W n x - W 0 x‖ ≤ ∑ i in Finset.range n, δ :=
    edit_seq_nonuniform W x n (fun _ => δ) (fun i hi => hstep i hi)
  calc
    ‖W n x - W 0 x‖ ≤ ∑ i in Finset.range n, δ := hnon
    _ = (n : ℝ) * δ := by
      -- Σ_{i<n} δ = n·δ
      rw [Finset.sum_const, Finset.card_range]
      simp

end Lattice