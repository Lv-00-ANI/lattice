import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.LearningTheory.RealTopK
/-!
# LATTICE: 多头合并与头冗余 —— 合并输出的界、冗余误差与无损合并

多头注意力（MHA）的 `k` 个头输出被拼接/平均后进入下一层。本文件给出**头合并**的
定量理论（模型无关，任意范数空间 `F`）：

  1. `headOutput` / `mergeHeads` / `mergeHeadsOver`：单头输出（权重对 value 的凸组合）、
     多头合并（头级权重 `α` 对头输出 `h` 的凸组合）、以及限制在头集合 `S` 上的合并；
  2. `head_output_bound`：**单头输出界** `‖headOutput w V‖ ≤ max‖V‖`
     （复用 `RealAttention.convComb_norm_bound`）；
  3. `merge_output_bound`：合并输出界 `‖mergeHeads α h‖ ≤ M`
     （`α` 是概率分布、各头输出 ≤ `M`）；
  4. `merge_output_bound_subprob`：**次概率权重**（`Σ α ≤ 1`）的输出界仍为 `≤ M`
     ——剪枝/丢头只会减少质量、绝不放大输出；
  5. `head_redundancy_bound_subprob` / `head_redundancy_bound`（**核心**）：头间冗余
     ——若所有头都与参考头 `h0` 相差 ≤ ε（相似/冗余），则合并误差
     `‖mergeHeads α h − h0‖ ≤ ε`；一般（次概率）版本为 `≤ (Σα)·ε`；
  6. `head_pairwise_redundancy_bound`：两两相近（`∀ i, ‖h i − h j‖ ≤ ε`）⟹
     合并到任一头 `h j` 的误差 ≤ ε；
  7. `merge_exact_when_identical` / `merge_lossless_when_identical`（**无损合并**）：
     所有头恒等时 `mergeHeads α h = (Σα) • h0`，`Σα = 1` 时恰等于 `h0`；
  8. `mergeHeads_sub_drop` / `pruned_head_bound` / `pruned_head_mass_loss`
     （**剪头误差**）：丢掉第 `j` 头后输出差恰为 `−α_j • h_j`，其范数 ≤ `α_j · M`
     （误差被该头权重 × 输出上界控制）；质量损失恰为 `α_j`；
  9. `pruned_head_output_bound` / `mergeHeadsOver_eq_mergeHeads`：剪枝后（限制在头集合
     `S`）的输出界，直接复用 `RealTopK.topk_output_bound`——衔接 top-k 稀疏化。

**诚实假设与降级**（均显式标注）：
  · `F` 任意实赋范线性空间；头权重 `α`（或 `w`）非负、和为 1 时才是凸组合（概率性
    结论都显式假设）；
  · `merge_output_bound_subprob` 额外要求 `0 ≤ M`（由 `Σ α ≤ 1` 推出 `≤ M` 需要）；
  · `head_redundancy_bound` 中的「冗余度」用**范数意义**的 ε：`∀ i, ‖h i − h0‖ ≤ ε`。
    余弦相似度 `≥ 1 − ε` 的版本需要额外的尺度假设（`‖h i‖ = ‖h0‖ = 1` 与余弦–范数
    换算），本文件不声称该换算，只证明范数形式的冗余界——这是**陈述形式的选择**，
    不是证明困难；
  · `pruned_head_bound` 给出的是「丢头造成的输出差」的界，**不含**剪枝后重新归一化
    的误差（若剪枝后重新归一化权重，误差需另加一项；本文件只给未重归一化的原式差）；
  · 本文件不涉及多头之间的**相关性/协方差**结构（头冗余的经验度量），只给确定性界。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定义：单头输出与多头合并 -/

/-- 单头输出：权重 `w` 对 value `V` 的凸组合 `Σ_i w i • V i`。 -/
def headOutput {ι : Type*} [Fintype ι] (w : ι → ℝ) (V : ι → F) : F :=
  ∑ i, w i • V i

/-- 多头合并：把 `k` 个头的输出 `h` 按合并权重 `α` 组合成一个头。 -/
def mergeHeads {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) : F :=
  ∑ i, α i • h i

/-- 限制在头集合 `S` 上的合并（剪枝/稀疏合并）。 -/
def mergeHeadsOver {ι : Type*} [Fintype ι] (S : Finset ι) (α : ι → ℝ) (h : ι → F) : F :=
  ∑ i in S, α i • h i

/-- 剪头权重：把第 `j` 头的权重置 0。 -/
def dropHead {k : ℕ} (α : Fin k → ℝ) (j : Fin k) : Fin k → ℝ :=
  fun i => if i = j then 0 else α i

/-! ## 定理一：单头输出界（复用凸组合界） -/

theorem head_output_bound {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ) (V : ι → F)
    (M : ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖headOutput w V‖ ≤ M :=
  convComb_norm_bound w V M hw hsum hV

/-! ## 定理二：合并输出界 -/

theorem merge_output_bound {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (M : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) (hM : ∀ i, ‖h i‖ ≤ M) :
    ‖mergeHeads α h‖ ≤ M := by
  unfold mergeHeads
  calc
    ‖∑ i, α i • h i‖ ≤ ∑ i, ‖α i • h i‖ := norm_sum_le _ _
    _ = ∑ i, α i * ‖h i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i)]
    _ ≤ ∑ i, α i * M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hα i)
    _ = M * (∑ i, α i) := by rw [← Finset.sum_mul, mul_comm]
    _ = M := by rw [hsum, mul_one]

/-- 次概率权重（`Σ α ≤ 1`）的合并输出界：剪枝只减质量、不放大输出。 -/
theorem merge_output_bound_subprob {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (M : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hα1 : ∑ i, α i ≤ 1) (hM0 : 0 ≤ M) (hM : ∀ i, ‖h i‖ ≤ M) :
    ‖mergeHeads α h‖ ≤ M := by
  unfold mergeHeads
  calc
    ‖∑ i, α i • h i‖ ≤ ∑ i, ‖α i • h i‖ := norm_sum_le _ _
    _ = ∑ i, α i * ‖h i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i)]
    _ ≤ ∑ i, α i * M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hα i)
    _ = (∑ i, α i) * M := by rw [← Finset.sum_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hα1 hM0
    _ = M := one_mul M

/-! ## 定理三（核心）：头间冗余 ⟹ 合并误差有界 -/

/-- 合并减权的分解：`mergeHeads α h − (Σα) • h0 = Σ α i • (h i − h0)`。 -/
lemma mergeHeads_sub_smul_sum {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (h0 : F) :
    mergeHeads α h - (∑ i, α i) • h0 = ∑ i, α i • (h i - h0) := by
  unfold mergeHeads
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => (smul_sub (α i) (h i) h0).symm

/-- 次概率版冗余界：`‖mergeHeads α h − (Σα)•h0‖ ≤ (Σα)·ε`（`α ≥ 0`、
`∀i, ‖h i − h0‖ ≤ ε`）。 -/
theorem head_redundancy_bound_subprob {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (h0 : F)
    (ε : ℝ) (hα : ∀ i, 0 ≤ α i) (hε : ∀ i, ‖h i - h0‖ ≤ ε) :
    ‖mergeHeads α h - (∑ i, α i) • h0‖ ≤ (∑ i, α i) * ε := by
  rw [mergeHeads_sub_smul_sum]
  calc
    ‖∑ i, α i • (h i - h0)‖ ≤ ∑ i, ‖α i • (h i - h0)‖ := norm_sum_le _ _
    _ = ∑ i, α i * ‖h i - h0‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i)]
    _ ≤ ∑ i, α i * ε := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hε i) (hα i)
    _ = (∑ i, α i) * ε := by rw [Finset.sum_mul]

/-- **核心**：`α` 是概率分布（`Σα = 1`）且所有头与 `h0` 相差 ≤ ε ⟹
合并结果与 `h0` 的误差 ≤ ε（冗余头的合并不放大误差）。 -/
theorem head_redundancy_bound {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (h0 : F) (ε : ℝ)
    (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) (hε : ∀ i, ‖h i - h0‖ ≤ ε) :
    ‖mergeHeads α h - h0‖ ≤ ε := by
  have hmain := head_redundancy_bound_subprob α h h0 ε hα hε
  rwa [hsum, one_smul, one_mul] at hmain

/-- 两两相近（都以第 `j` 头为参考）⟹ 合并到 `h j` 的误差 ≤ ε。 -/
theorem head_pairwise_redundancy_bound {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (j : Fin k)
    (ε : ℝ) (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1) (hε : ∀ i, ‖h i - h j‖ ≤ ε) :
    ‖mergeHeads α h - h j‖ ≤ ε :=
  head_redundancy_bound α h (h j) ε hα hsum hε

/-! ## 定理四：相同头合并无损 -/

/-- 所有头恒等（都等于 `h0`）⟹ `mergeHeads α h = (Σα) • h0`。 -/
theorem merge_exact_when_identical {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (h0 : F)
    (hid : ∀ i, h i = h0) : mergeHeads α h = (∑ i, α i) • h0 := by
  calc
    mergeHeads α h = ∑ i, α i • h0 := by
      unfold mergeHeads
      exact Finset.sum_congr rfl fun i _ => by rw [hid i]
    _ = (∑ i, α i) • h0 := Finset.sum_smul.symm

/-- 所有头恒等且 `Σα = 1` ⟹ 合并**无损**：`mergeHeads α h = h0`。 -/
theorem merge_lossless_when_identical {k : ℕ} (α : Fin k → ℝ) (h : Fin k → F) (h0 : F)
    (hid : ∀ i, h i = h0) (hsum : ∑ i, α i = 1) : mergeHeads α h = h0 := by
  rw [merge_exact_when_identical α h h0 hid, hsum, one_smul]

/-! ## 定理五：剪头误差界 -/

/-- 丢头的权重和损失恰为 `α j`。 -/
theorem pruned_head_mass_loss {k : ℕ} (α : Fin k → ℝ) (j : Fin k) :
    ∑ i, dropHead α j i = (∑ i, α i) - α j := by
  have hpoint : ∀ i : Fin k, dropHead α j i = α i - (if i = j then α i else 0) := by
    intro i
    unfold dropHead
    by_cases h : i = j
    · simp [h]
    · simp [h]
  calc
    ∑ i, dropHead α j i = ∑ i, (α i - (if i = j then α i else 0)) :=
      Finset.sum_congr rfl fun i _ => hpoint i
    _ = (∑ i, α i) - ∑ i, (if i = j then α i else 0) := Finset.sum_sub_distrib
    _ = (∑ i, α i) - α j := by rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]

/-- 丢头后的合并与完整合并之差恰为 `−α_j • h_j`。 -/
lemma mergeHeads_sub_drop {k : ℕ} (α : Fin k → ℝ) (j : Fin k) (h : Fin k → F) :
    mergeHeads (dropHead α j) h - mergeHeads α h = -(α j) • h j := by
  unfold mergeHeads dropHead
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **剪头误差界**：丢掉第 `j` 头造成的输出差 ≤ `α_j · M`（该头权重 × 输出上界）。 -/
theorem pruned_head_bound {k : ℕ} (α : Fin k → ℝ) (j : Fin k) (h : Fin k → F) (M : ℝ)
    (hαj : 0 ≤ α j) (hM : ∀ i, ‖h i‖ ≤ M) :
    ‖mergeHeads (dropHead α j) h - mergeHeads α h‖ ≤ α j * M := by
  rw [mergeHeads_sub_drop, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hαj]
  exact mul_le_mul_of_nonneg_left (hM j) hαj

/-! ## 定理六：限制在头集合 `S` 上的合并（衔接 RealTopK） -/

theorem mergeHeadsOver_eq_mergeHeads {k : ℕ} (S : Finset (Fin k)) (α : Fin k → ℝ)
    (h : Fin k → F) : mergeHeadsOver S α h = ∑ i in S, α i • h i := rfl

/-- 头剪枝（只保留 `S` 内的头、权重在 `S` 上和为 1）的输出界：
直接复用 `RealTopK.topk_output_bound`。 -/
theorem pruned_head_output_bound {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (S : Finset ι) (α : ι → ℝ)
    (h : ι → F) (M : ℝ) (hα : ∀ i, i ∈ S → 0 ≤ α i) (hsum : ∑ i in S, α i = 1)
    (hM : ∀ i, ‖h i‖ ≤ M) : ‖mergeHeadsOver S α h‖ ≤ M :=
  topk_output_bound S α h M hα hsum hM

/-- 头剪枝的次概率版：`Σ_{i∈S} α i ≤ 1` 时输出仍 ≤ M（`M ≥ 0`）。 -/
theorem pruned_head_output_bound_subprob {ι : Type*} [Fintype ι] (S : Finset ι) (α : ι → ℝ)
    (h : ι → F) (M : ℝ) (hα : ∀ i, i ∈ S → 0 ≤ α i) (hα1 : ∑ i in S, α i ≤ 1)
    (hM0 : 0 ≤ M) (hM : ∀ i, ‖h i‖ ≤ M) : ‖mergeHeadsOver S α h‖ ≤ M := by
  unfold mergeHeadsOver
  calc
    ‖∑ i in S, α i • h i‖ ≤ ∑ i in S, ‖α i • h i‖ := norm_sum_le _ _
    _ = ∑ i in S, α i * ‖h i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i hi)]
    _ ≤ ∑ i in S, α i * M :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hM i) (hα i hi)
    _ = (∑ i in S, α i) * M := by rw [← Finset.sum_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hα1 hM0
    _ = M := one_mul M

end Lattice
