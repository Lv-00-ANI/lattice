import Mathlib
import Lattice.Lift.RealLinear
import Lattice.Lib.Compiler.RealCombinators
import Lattice.Lift.RealNonlinear
/-!
# LATTICE: 蕴含与否定 —— 组合子层面的逻辑扩展

调研开放问题 2：组合子只证了 ∧/∨，¬ 与蕴含（→）未证。本文件补齐：

  1. 蕴含的权重对齐充分条件：
     out₂ = k·out₁ ⟹ (out₁ = 0 → out₂ = 0)——权重线性对齐时蕴含成立；
  2. 约束层面的蕴含：对齐 ⟹ c₁ 满足 → c₂ 满足（含 k≠0 等价、k=0 平凡）；
  3. De Morgan 在嵌入下的对应：
     ¬(real_andC a b = 0) ⟺ (a ≠ 0 ∨ b ≠ 0)
     ¬(real_orC a b = 0) ⟺ (a ≠ 0 ∧ b ≠ 0)；
  4. 蕴含的合取编码：c₁→c₂ 的可微惩罚 = relu(out₂²)·(1 - δ) 的代数基础——
     对齐时蕴含自动满足（零惩罚）。

纯 ℝ（Mathlib）。
-/


namespace Lattice

/-! ## 定理一：权重对齐 ⟹ 蕴含（输出层面）
out₂ = k·out₁ 且 out₁ = 0 ⟹ out₂ = 0。-/

theorem impl_via_alignment (out₁ out₂ k : ℝ) (h : out₂ = k * out₁) :
    out₁ = 0 → out₂ = 0 := by
  intro h₁
  rw [h, h₁]
  ring

/-! ## 定理二：对齐且系数非零 ⟹ 反向蕴含（等价）
out₂ = k·out₁ 且 k ≠ 0 ⟹ out₁ = 0 ⟺ out₂ = 0（双向）。-/

theorem impl_iff_via_alignment (out₁ out₂ k : ℝ) (hk : k ≠ 0) (h : out₂ = k * out₁) :
    out₁ = 0 ↔ out₂ = 0 := by
  constructor
  · exact impl_via_alignment out₁ out₂ k h
  · intro h₂
    -- out₂ = 0 = k·out₁ ⟹ out₁ = 0（k ≠ 0）
    have : k * out₁ = 0 := by rw [← h, h₂]
    exact (mul_eq_zero.mp this).resolve_left hk

/-! ## 定理三：约束层面的蕴含（对齐时）
约束 c₁、c₂ 的神经元输出对齐（out₂ = k·out₁）⟹ c₁ 满足 → c₂ 满足。-/

theorem constraint_implication_via_alignment (c₁ c₂ : RealConstraint) (k : ℝ)
    (h : ∀ x : ℝ, RealNeuronOut (convertReal c₂) x = k * RealNeuronOut (convertReal c₁) x) :
    ∀ x : ℝ, RealConstraintSat c₁ x → RealConstraintSat c₂ x := by
  intro x hsat
  -- c₁ 满足 ⟹ out₁ = 0 ⟹ out₂ = 0 ⟹ c₂ 满足
  have hout₁ : RealNeuronOut (convertReal c₁) x = 0 := (convertReal_preserves c₁ x).mp hsat
  have hout₂ : RealNeuronOut (convertReal c₂) x = 0 :=
    impl_via_alignment (RealNeuronOut (convertReal c₁) x) (RealNeuronOut (convertReal c₂) x) k
      (h x) hout₁
  exact (convertReal_preserves c₂ x).mpr hout₂

/-! ## 定理四：De Morgan —— ¬(AND) 在嵌入下的对应
¬(a²+b² = 0) ⟺ a ≠ 0 ∨ b ≠ 0。-/

theorem not_andC_zero_iff (a b : ℝ) : ¬(real_andC a b = 0) ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro h
    by_contra hnot
    -- a = 0 ∧ b = 0 → real_andC = 0，矛盾
    rw [not_or] at hnot
    have hz : real_andC a b = 0 :=
      (real_andC_eq_zero_iff a b).mpr ⟨(not_not.mp hnot.1), (not_not.mp hnot.2)⟩
    exact h hz
  · intro h hz
    -- a ≠ 0 ∨ b ≠ 0 且 real_andC = 0 ⟹ 矛盾（real_andC=0 ⟹ a=0 ∧ b=0）
    rcases h with h | h
    · exact h ((real_andC_eq_zero_iff a b).mp hz).1
    · exact h ((real_andC_eq_zero_iff a b).mp hz).2

/-! ## 定理五：De Morgan —— ¬(OR) 在嵌入下的对应
¬(a·b = 0) ⟺ a ≠ 0 ∧ b ≠ 0。-/

theorem not_orC_zero_iff (a b : ℝ) : ¬(real_orC a b = 0) ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro ha
      exact h ((real_orC_eq_zero_iff a b).mpr (Or.inl ha))
    · intro hb
      exact h ((real_orC_eq_zero_iff a b).mpr (Or.inr hb))
  · intro h hz
    -- a ≠ 0 ∧ b ≠ 0 且 a·b = 0 ⟹ 矛盾
    rcases (real_orC_eq_zero_iff a b).mp hz with ha | hb
    · exact h.1 ha
    · exact h.2 hb

/-! ## 定理六：蕴含的合取编码基础
c₁ → c₂ 的可微惩罚可用 relu 构造：当 out₁ = 0（c₁ 满足）时惩罚 = relu(out₂²)，
零化 ⟺ out₂ = 0（即 c₂ 满足）；当 out₁ ≠ 0 时无约束（前提不成立，不惩罚）。
-/

theorem implication_penalty (out₁ out₂ : ℝ) :
    out₁ = 0 → (relu (out₂ ^ 2) = 0 ↔ out₂ = 0) := by
  intro h₁
  -- relu(out₂²) = 0 ⟺ out₂² ≤ 0 ⟺ out₂² = 0 ⟺ out₂ = 0
  have hrelu : relu (out₂ ^ 2) = 0 ↔ out₂ ^ 2 ≤ 0 := relu_eq_zero_iff (out₂ ^ 2)
  have hsq : out₂ ^ 2 ≤ 0 ↔ out₂ = 0 := by
    constructor
    · intro hle
      have hnonneg : 0 ≤ out₂ ^ 2 := sq_nonneg out₂
      have hz : out₂ ^ 2 = 0 := le_antisymm hle hnonneg
      exact sq_eq_zero_iff.mp hz
    · intro h
      simp [h]
  rw [hrelu, hsq]

end Lattice
