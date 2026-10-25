import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealMaskFamily
import Lattice.Lib.Attention.RealCausalAttention
import Lattice.Lib.Attention.RealAttentionLipschitz
/-!
# LATTICE: 块稀疏注意力 —— 块级掩码、行随机与计数复杂度

块稀疏注意力（block-sparse attention，Longformer / BigBird / 分块 FlashAttention 的
共同骨架）把序列切成定长 `b` 的块，只在**允许的块对**内做注意力。本文件把它作为
`RealMaskFamily` 掩码族的一个实例处理：

  1. `blockOf` / `blockMask`：token `i` 属于块 `i / b`；`blockMask b allowed i j`
     表示「块对 `(blk i, blk j)` 被允许」——任意 `allowed : ℕ → ℕ → Prop`；
  2. `blockSparseSoftmax` / `blockSparseDenom`：只在允许块内做 softmax
     （定义上直接等于 `maskedSoftmax (blockMask b allowed)`，`if` 形式避免 −∞）；
  3. `block_sparse_denom_pos` / `block_sparse_pmf`：**行随机**——块行非空 ⟹
     权重是概率分布（复用 `RealMaskFamily.maskedSoftmax_sum_one`）；
  4. `block_sparse_output_bound`：**凸组合界** `‖输出‖ ≤ max‖V‖`（复用
     `masked_attention_output_bound`）；
  5. `block_mask_contains_causal`（衔接 `RealCausalAttention`）：块级因果掩码
     `allowed u v := v ≤ u` **包含** token 级因果掩码 `j ≤ i`；并给出分母比较
     `causalDenom_le_blockCausalDenom`（块掩码可见更多 ⟹ 分母更大 ⟹ 权重更「平」）；
  6. `block_sparse_block_count_le_total`（**计数复杂度**）：允许块数 ≤ 总块数；
     `block_sparse_all_blocks_count`：全允许时恰为 `nb²`（稠密退化）；
     `block_sparse_entries_le_dense`：块稀疏的分数条目数 ≤ 稠密的分数条目数；
  7. `block_sparse_all_blocks_eq_softmax`：全允许块掩码退化为 `RealAttention.softmax`；
  8. `block_sparse_lipschitz`：块稀疏注意力（固定权重）是 `M`-Lipschitz
     （复用 `RealAttentionLipschitz.convComb_lipschitz_prob`）——掩码族统一结果的复用。

**诚实假设与降级**（均显式标注）：
  · 行随机/输出界要求块行非空（`∃ j, blockMask b allowed i j`）——否则分母为 0；
  · `b = 0` 时 `blockOf` 恒为 `0`（Lean 中 `x / 0 = 0`），块掩码退化为「全允许或全
    禁止」的常掩码；本文件结论对 `b = 0` 仍成立（不需要 `b > 0`），但不声称它是
    有意义的稀疏性；
  · 计数复杂度是**允许块数**的组合计数，不是运行时定理：块稀疏只有在允许块数远小于
    `nb²` 时才真正省算力；本文件证明的是通用上界与稠密退化等式，**不证明**具体稀疏
    模式（如滑动窗口块、随机块）的精确块数——那需要额外的组合计数（本文件不涉及）；
  · `causalDenom_le_blockCausalDenom` 只给单侧比较（块掩码是因果掩码的**超集**，
    不是相等）；块大小 `b > 1` 时块掩码严格粗于 token 级因果掩码。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 块划分与块掩码 -/

/-- 块大小 `b` 下 token `i` 的块号：`i / b`（整除向下取整）。 -/
def blockOf {n : ℕ} (b : ℕ) (i : Fin n) : ℕ := (i : ℕ) / b

/-- 块级掩码：token `i` 可注意 token `j` ⟺ 块对 `(blk i, blk j)` 被 `allowed` 允许。
`allowed` 任意（全允许 / 块级因果 / 滑动窗口块 / 随机块…）。 -/
abbrev blockMask {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) (i j : Fin n) : Prop :=
  allowed (blockOf b i) (blockOf b j)

instance instDecidableRelBlockMask {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] : DecidableRel (blockMask b allowed (n := n)) :=
  fun i j => inferInstanceAs (Decidable (allowed (blockOf b i) (blockOf b j)))

/-- 块稀疏注意力分母：`Σ_k (if blockMask i k then exp(s_k) else 0)`。 -/
def blockSparseDenom {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  maskedDenom (blockMask b allowed) s i

/-- 块稀疏 softmax：只在允许的块内归一化。
定义上等于掩码族的通用形式 `maskedSoftmax (blockMask b allowed)`。 -/
def blockSparseSoftmax {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  maskedSoftmax (blockMask b allowed) s i

/-- 块级因果掩码：只允许 `blk j ≤ blk i`（块上三角被禁止）。 -/
abbrev blockCausalMask {n : ℕ} (b : ℕ) (i j : Fin n) : Prop :=
  blockMask b (fun u v => v ≤ u) i j

/-! ## 引理：块稀疏定义与掩码族一致，分母为正 -/

/-- 块稀疏 softmax 与掩码族通用形式定义相同（`rfl` 级一致性）。 -/
theorem blockSparseSoftmax_eq_masked {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (s : Fin n → ℝ) (i : Fin n) :
    blockSparseSoftmax b allowed s i = maskedSoftmax (blockMask b allowed) s i := rfl

/-- 块行非空 ⟹ 块稀疏分母为正。 -/
lemma block_sparse_denom_pos {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, blockMask b allowed i j) :
    0 < blockSparseDenom b allowed s i :=
  maskedDenom_pos (blockMask b allowed) s i hne

/-! ## 定理一（核心）：块稀疏权重非负 -/

theorem block_sparse_nonneg {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i j : Fin n) : 0 ≤ blockSparseSoftmax b allowed s i j :=
  maskedSoftmax_nonneg (blockMask b allowed) s i j

/-! ## 定理二（核心）：块稀疏权重行随机（行非空时） -/

theorem block_sparse_pmf {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, blockMask b allowed i j) :
    (∀ j, 0 ≤ blockSparseSoftmax b allowed s i j)
      ∧ (∑ j, blockSparseSoftmax b allowed s i j = 1) :=
  ⟨fun j => block_sparse_nonneg b allowed s i j,
   maskedSoftmax_sum_one (blockMask b allowed) s i hne⟩

/-! ## 定理三（核心）：块稀疏输出界（凸组合界） -/

theorem block_sparse_output_bound {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, blockMask b allowed i j)
    (V : Fin n → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (blockSparseSoftmax b allowed s i) V‖ ≤ M :=
  masked_attention_output_bound (blockMask b allowed) s i hne V M hV

/-- 块级因果掩码行非空：`blk i ≤ blk i`。 -/
theorem block_causal_row_nonempty {n : ℕ} (b : ℕ) (i : Fin n) :
    ∃ j, blockCausalMask b i j :=
  ⟨i, le_rfl⟩

/-- 块级因果掩码的注意力权重行随机（合法性）。 -/
theorem block_causal_row_random {n : ℕ} (b : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    ∑ j, blockSparseSoftmax b (fun u v => v ≤ u) s i j = 1 :=
  maskedSoftmax_sum_one (blockMask b (fun u v => v ≤ u)) s i (block_causal_row_nonempty b i)

/-- 块级因果掩码的注意力输出界。 -/
theorem block_causal_output_bound {n : ℕ} (b : ℕ) (s : Fin n → ℝ) (i : Fin n)
    (V : Fin n → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (blockSparseSoftmax b (fun u v => v ≤ u) s i) V‖ ≤ M :=
  block_sparse_output_bound b (fun u v => v ≤ u) s i (block_causal_row_nonempty b i) V M hV

/-! ## 定理四（核心，衔接 RealCausalAttention）：块因果掩码包含 token 因果掩码
`causalMask i j`（即 `j ≤ i`）⟹ `blk j ≤ blk i`（整除以 `b` 单调）。
注意方向：块掩码是因果掩码的**超集**（`b > 1` 时严格更大），不是相等。 -/

theorem block_mask_contains_causal {n : ℕ} (b : ℕ) (i j : Fin n) (h : causalMask i j) :
    blockCausalMask b i j := by
  unfold blockCausalMask blockMask blockOf
  exact Nat.div_le_div_right h

/-- 块因果掩码下的分母 ≥ token 级因果掩码下的分母（块掩码项更多、项非负）。
衔接 `RealCausalAttention.causalDenom`。 -/
theorem causalDenom_le_blockCausalDenom {n : ℕ} (b : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    causalDenom s i ≤ blockSparseDenom b (fun u v => v ≤ u) s i := by
  have hpt : ∀ j : Fin n,
      (if j ≤ i then Real.exp (s j) else 0)
        ≤ (if blockMask b (fun u v => v ≤ u) i j then Real.exp (s j) else 0) := by
    intro j
    by_cases h : j ≤ i
    · have hb : blockMask b (fun u v => v ≤ u) i j := block_mask_contains_causal b i j h
      simp [h, hb]
    · by_cases hb : blockMask b (fun u v => v ≤ u) i j
      · have hpos : (0 : ℝ) ≤ Real.exp (s j) := le_of_lt (Real.exp_pos (s j))
        simp [h, hb, hpos]
      · simp [h, hb]
  unfold causalDenom blockSparseDenom maskedDenom
  exact Finset.sum_le_sum fun j _ => hpt j

/-! ## 定理五（计数复杂度）：允许块数 ≤ 总块数 -/

/-- 允许块的个数（块级计数）：`Σ_u Σ_v [allowed u v]`。 -/
def allowedBlockCount (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] : ℕ :=
  ∑ u : Fin nb, ∑ v : Fin nb, (if allowed u v then 1 else 0)

/-- 任意块掩码的允许块数不超过 `nb²`（总块数）。 -/
theorem block_sparse_block_count_le_total (nb : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] : allowedBlockCount nb allowed ≤ nb * nb := by
  have hrow : ∀ u : Fin nb, (∑ v : Fin nb, (if allowed u v then 1 else 0)) ≤ nb := by
    intro u
    calc
      (∑ v : Fin nb, (if allowed u v then 1 else 0))
          ≤ ∑ _v : Fin nb, (1 : ℕ) := Finset.sum_le_sum fun v _ => by split <;> simp
      _ = nb := by simp
  unfold allowedBlockCount
  calc
    (∑ u : Fin nb, ∑ v : Fin nb, (if allowed u v then 1 else 0))
        ≤ ∑ _u : Fin nb, nb := Finset.sum_le_sum fun u _ => hrow u
    _ = nb * nb := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- 全允许块掩码的允许块数恰为 `nb²`（稠密退化）。 -/
theorem block_sparse_all_blocks_count (nb : ℕ) :
    allowedBlockCount nb (fun _ _ : ℕ => True) = nb * nb := by
  simp [allowedBlockCount, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- 块稀疏的分数条目数（允许块数 × 块内条目 `b²`）不超过同块划分下稠密的条目数。
（`nb² · b²` 是「按块稠密」的上界；真正省算力需要 `allowedBlockCount ≪ nb²`。） -/
theorem block_sparse_entries_le_dense {nb b : ℕ} (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] :
    allowedBlockCount nb allowed * (b * b) ≤ nb * nb * (b * b) :=
  Nat.mul_le_mul_right (b * b) (block_sparse_block_count_le_total nb allowed)

/-! ## 定理六（特例回收）：全允许块掩码退化回全注意力 softmax -/

theorem block_sparse_all_blocks_eq_softmax {n : ℕ} (b : ℕ) (s : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    blockSparseSoftmax b (fun _ _ : ℕ => True) s i = softmax s :=
  full_mask_eq_softmax s i

/-! ## 定理七：块稀疏注意力（固定权重）的 Lipschitz 性
复用 `RealAttentionLipschitz.convComb_lipschitz_prob`：凸组合概率权重不放大输入差。 -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem block_sparse_lipschitz {n : ℕ} (b : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, blockMask b allowed i j)
    (V : Fin n → E →L[ℝ] F) (M : ℝ) (hM : ∀ j, ‖V j‖ ≤ M) :
    ∀ x y : E,
      ‖(∑ j : Fin n, blockSparseSoftmax b allowed s i j • V j x)
        - (∑ j : Fin n, blockSparseSoftmax b allowed s i j • V j y)‖ ≤ M * ‖x - y‖ :=
  convComb_lipschitz_prob (blockSparseSoftmax b allowed s i) V M
    (fun j => block_sparse_nonneg b allowed s i j)
    (maskedSoftmax_sum_one (blockMask b allowed) s i hne) hM

/-- 块级因果掩码的 Lipschitz 性（上一条的因果实例，行非空自动满足）。 -/
theorem block_causal_lipschitz {n : ℕ} (b : ℕ) (s : Fin n → ℝ) (i : Fin n)
    (V : Fin n → E →L[ℝ] F) (M : ℝ) (hM : ∀ j, ‖V j‖ ≤ M) :
    ∀ x y : E,
      ‖(∑ j : Fin n, blockSparseSoftmax b (fun u v => v ≤ u) s i j • V j x)
        - (∑ j : Fin n, blockSparseSoftmax b (fun u v => v ≤ u) s i j • V j y)‖
        ≤ M * ‖x - y‖ :=
  block_sparse_lipschitz b (fun u v => v ≤ u) s i (block_causal_row_nonempty b i) V M hM

end Lattice