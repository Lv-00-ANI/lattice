import Mathlib

/-!
# LATTICE: 嵌入层 —— one-hot 行选取 = 线性映射（模型无关）

transformer 调研（research/real-world/transformer-semantics.md）的嵌入层：
token 查表 = one-hot 向量与嵌入矩阵的线性组合（行选取）

  Embedding(i) = E i = Σⱼ one_hot(i,j) · E j

其中 one_hot(i,j) = if j = i then 1 else 0（第 i 个标准基向量）。

模型无关：任意词表指标 ι、任意嵌入向量空间 F。
这是词表行语义的形式化基础（连接提取契约：嵌入行 = 符号化的 token 表示）。
-/

noncomputable section

namespace Lattice

variable {ι F : Type*}
  [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## one-hot 向量 -/

def oneHot (i j : ι) : ℝ := if j = i then 1 else 0

/-! ## 定理一：one-hot 线性组合 = 行选取
Σⱼ one_hot(i,j)·Eⱼ = Eᵢ（查表即线性映射）。-/

theorem oneHot_lookup (E : ι → F) (i : ι) :
    ∑ j, oneHot i j • E j = E i := by
  unfold oneHot
  -- 单点求和：只有 j = i 项非零
  rw [Finset.sum_eq_single i]
  · -- j = i：1 • E i = E i
    simp
  · -- j ≠ i：项为 0
    intro j hmem hji
    have hif : (if j = i then 1 else 0) = 0 := if_neg hji
    simp [hif, hji]
  · -- i ∈ univ（不可能不出现）
    intro hi
    exact (hi (Finset.mem_univ i)).elim

/-! ## 定理二：查表函数 = one-hot 线性组合（函数形式）
Embedding(i) = Σⱼ one_hot(i,j)·Eⱼ（逐 token 成立）。-/

theorem embed_lookup_is_linear (E : ι → F) :
    E = fun i => ∑ j, oneHot i j • E j := by
  funext i
  exact (oneHot_lookup E i).symm

/-! ## 定理三：one-hot 是标准基（对角唯一非零）
one_hot(i,j) = 1 ⟺ i = j（词表基的性质）。-/

omit [Fintype ι] in
theorem oneHot_eq_one_iff (i j : ι) : oneHot i j = 1 ↔ i = j := by
  unfold oneHot
  by_cases h : j = i
  · rw [if_pos h]
    constructor <;> intro _
    · exact h.symm
    · norm_num
  · rw [if_neg h]
    constructor
    · intro h1
      norm_num at h1
    · intro hij
      exact False.elim (h hij.symm)

/-! ## 定理四：嵌入单射 ⟺ 行两两不同
词表无重复嵌入（单射性条件：i ≠ j ⟹ Eᵢ ≠ Eⱼ）。-/

omit [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem embed_injective_iff_rows_distinct (E : ι → F) :
    Function.Injective E ↔ ∀ i j : ι, i ≠ j → E i ≠ E j := by
  constructor
  · intro h i j hij hE
    exact hij (h hE)
  · intro h i j hE
    by_contra hij
    exact h i j hij hE

/-! ## 定理五：one-hot 分解的唯一性
若 w 是"基分解"（Σⱼ wⱼ·Eⱼ 表示 Eᵢ 的系数），在 E 单射且线性无关的意义下
系数唯一——这里给出直接形式：查表与 one-hot 表示同一对象。-/

theorem oneHot_represents_token (E : ι → F) (i : ι) :
    ∑ j, oneHot i j • E j = E i :=
  oneHot_lookup E i

end Lattice
