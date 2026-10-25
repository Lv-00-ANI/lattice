import Mathlib

/-!
# LATTICE: P-Edit —— 顺序编辑的误差累积与 ε-容差验证健全性

对齐约束注入调研（research/real-world/alignment-constraint-math.md §6 目标 A）：
真实模型经过 k 次顺序权重编辑（每次为保满足编辑，单步输出变化 ≤ δ），
累积输出变化被三角不等式界住：

  ‖W_k·x - W_0·x‖ ≤ k·δ   （k 步均匀界）

推论（容差验证健全性）：
  · 原约束满足（W_0·x = 0）⟹ 编辑后 ‖W_k·x‖ ≤ k·δ；
  · 容差 ε ≥ (k·δ)² 时验证器必接受（不误拒）；
  · 通过 ε-验证 ⟹ 无单输出违背超过 √ε（不误放的量化）。

原料：三角不等式 + Nat 归纳（不引入新数学，难度与 RealApprox 同级）。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 引理：两步编辑的误差累积（三角不等式）
‖W₂x - W₀x‖ ≤ ‖W₂x - W₁x‖ + ‖W₁x - W₀x‖。-/

lemma edit_two_step (W₀ W₁ W₂ : E →L[ℝ] F) (x : E) :
    ‖W₂ x - W₀ x‖ ≤ ‖W₂ x - W₁ x‖ + ‖W₁ x - W₀ x‖ := by
  have hdiff : W₂ x - W₀ x = (W₂ x - W₁ x) + (W₁ x - W₀ x) := by
    abel
  rw [hdiff]
  exact norm_add_le _ _

/-! ## 定理一：k 步均匀编辑的误差累积
每一步输出变化 ≤ δ，k 步后 ‖W_k x - W_0 x‖ ≤ k·δ。-/

theorem edit_seq_bound (W : Nat → E →L[ℝ] F) (x : E) (n : Nat) (δ : ℝ)
    (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ) :
    ‖W n x - W 0 x‖ ≤ (n : ℝ) * δ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- 限制 hstep 到 i < n（供归纳假设）
      have hstep' : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ :=
        fun i hi => hstep i (by omega)
      -- 最后一步 ≤ δ
      have hlast : ‖W (n + 1) x - W n x‖ ≤ δ := hstep n (by omega)
      calc
        ‖W (n + 1) x - W 0 x‖ ≤ ‖W (n + 1) x - W n x‖ + ‖W n x - W 0 x‖ :=
          edit_two_step (W 0) (W n) (W (n + 1)) x
        _ ≤ δ + (n : ℝ) * δ := by
          exact add_le_add hlast (ih hstep')
        _ = ((Nat.succ n : Nat) : ℝ) * δ := by
          rw [Nat.cast_succ]
          ring

/-! ## 定理二：编辑后约束近似保持（k 步）
原约束满足（W_0 x = 0）⟹ k 步编辑后 ‖W_k x‖ ≤ k·δ。-/

theorem edit_seq_preserves_constraint (W : Nat → E →L[ℝ] ℝ) (x : E) (n : Nat) (δ : ℝ)
    (h0 : W 0 x = 0) (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ) :
    ‖W n x‖ ≤ (n : ℝ) * δ := by
  calc
    ‖W n x‖ = ‖W n x - W 0 x‖ := by
      rw [h0]
      simp
    _ ≤ (n : ℝ) * δ := edit_seq_bound W x n δ hstep

/-! ## 定理三：ε-容差验证健全性（不误拒）
容差 ε ≥ (n·δ)² 时验证器接受编辑后的模型（原约束 ε-近似保持，
损失被 (n·δ)² 界住）。-/

theorem edit_seq_verify_no_false_reject (W : Nat → E →L[ℝ] ℝ) (x : E) (n : Nat) (δ ε : ℝ)
    (h0 : W 0 x = 0) (hstep : ∀ i : Nat, i < n → ‖W (i + 1) x - W i x‖ ≤ δ)
    (hε : ((n : ℝ) * δ) ^ 2 ≤ ε) :
    ‖W n x‖ ^ 2 ≤ ε := by
  have hb : ‖W n x‖ ≤ (n : ℝ) * δ := edit_seq_preserves_constraint W x n δ h0 hstep
  have hδ0 : 0 ≤ (n : ℝ) * δ := le_trans (norm_nonneg _) hb
  calc
    ‖W n x‖ ^ 2 ≤ ((n : ℝ) * δ) ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hδ0] using hb)
    _ ≤ ε := hε

/-! ## 定理四：ε-验证通过 ⟹ 违背量 ≤ √ε（不误放）
验证器接受（‖W_n x‖² ≤ ε，容差非负）⟹ 无单输出违背超过 √ε。 -/

theorem edit_seq_verify_no_false_accept (W : Nat → E →L[ℝ] ℝ) (x : E) (n : Nat) (ε : ℝ)
    (_hε0 : 0 ≤ ε) (h : ‖W n x‖ ^ 2 ≤ ε) : ‖W n x‖ ≤ Real.sqrt ε := by
  exact Real.le_sqrt_of_sq_le h

end Lattice
