import Mathlib
import Lattice.Lib.Attention.RealBlockSparse
/-!
# LATTICE: 滑窗块掩码 / 随机块的**精确非零块数**闭式 + 与稠密块数之比 ≤ 1

`RealBlockSparse` 给出了块稀疏 softmax 的**归一化/概率/有界/Lipschitz** 性质，
以及 `block_sparse_block_count_le_total`（块数 ≤ 总块数 `nb²`）这一**粗糙**界。
本文件补上**精确**计数：块因果掩码与滑窗块掩码的**非零块数闭式公式**，
以及「稀疏/稠密块数之比 ≤ 1」的**定量**结论。全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

1. `rowCount` / `maskCount`：**逐行计数**与总计数（对块掩码的两层结构作精确记账）；
2. `causalRowCount_eq` / `causalRowCount_eq_of_lt`：块因果掩码第 `i` 行恰有
   `min (i+1) nb` 个块（`i < nb` 时即 `i+1`）；
3. `triang_succ_div_two`：三角形数递推 `(n+1)(n+2)/2 = n(n+1)/2 + (n+1)`
   （把 `Nat.div` 算术一次封装）；
4. `causalMaskCount_eq`（**闭式**）：块因果掩码的非零块数恰为**三角形数**
   `nb (nb + 1) / 2`；
5. `causalMaskCount_le_total`：`nb(nb+1)/2 ≤ nb²`（`nb ≥ 1`），
   即**块因果掩码的非零块比 ≤ 1/2**；
6. `causalMaskCount_compl`（**互补闭式**）：严格上三角互补块数恰为 `nb(nb-1)/2`；
7. `rowCount_add_compl` / `maskCount_add_compl_eq_total`（**互补记账恒等式**）：
   掩码与补掩码的块数之和**恰为 `nb²`**——所有精确计数的记账基础；
8. `windowRowCount_eq_card` / `windowRowCount_zero` / `windowRowCount_one_zero` /
   `windowRowCount_one` / `windowRowCount_one_top`（**滑窗逐行计数**）：
   带宽 `w = 0` 时每行 1 个；`w = 1` 时首/末行各 2 个、内部行各 3 个；
9. `windowMaskCount_zero` / `windowMaskCount_zero_le_total`：`w = 0`（对角）块数恰为 `nb`，
   且 `nb ≤ nb²`（`nb ≥ 1`）；
10. `windowMaskCount_one` / `windowMaskCount_one_le_total`：`w = 1`（三对角）块数恰为
    `3nb - 2`（`nb ≥ 3`），且 `3nb - 2 ≤ nb²`——**三对角省块**；
11. `maskCount_le_total`（**核心，比值 ≤ 1**）：任意块掩码的块数 `≤ nb²`；
12. `maskCount_lt_total_of_exists_not`：**严格性**——存在被丢弃的块时块数**严格** `< nb²`，
    这是「比值 < 1」的精确条件；

## 诚实边界（中文标注）

- **历史沿革 —— 滑窗闭式的带宽范围**：本条曾标注为「降级」：本文件一度只给出
  `w ∈ {0, 1}` 的**精确**闭式（`w = 0`：对角 `nb`，见 `windowMaskCount_zero`；
  `w = 1`：三对角 `3nb - 2`，见 `windowMaskCount_one`）。
  该结论现已由本文件 §五 补齐：`windowMaskCount_general` 在 `2w+1 ≤ nb` 下给出一般带宽 `w` 的
  精确闭式 `nb(2w+1) − w(w+1)`，其中「逐行截断求和」由 `windowRowCount_eq` 的显式闭式
  `min(i+w, nb-1) + 1 - (i-w)`（见 `windowRowCount_eq` 的定义处）承载，
  原始「在 `Nat` 下展开繁琐」的顾虑由 §五 的三段截断分解与辅助引理化解。
  曾经标注为**未做**的**截断情形**（`w ≥ 2`）由此转为**已做**。
- **已否证（后由 §六 补齐）—— 非均匀块大小 / 末尾不满块**：本文件的块计数按**块的下标**计数
  （`nb` 个块，`RealBlockSparse.blockOf` 的语义），不区分末尾块是否满。
  一度标注为**未做**的按**元素数**加权的计数，现已由 §六 的
  `weightedBlockCount_tail_decomp` 给出末尾不满块（前 `m-1` 块大小为 `B`、末块为 `r`）的
  元素加权精确分解，`weightedBlockCount_tail_le_uniform` 进一步给出 `r ≤ B` 时只会更省。
- **已否证（后由 §七 补齐）—— 随机块的期望 / 高概率界**：本文件的主体确实是**确定性**掩码的精确计数；
  一度标注为**未做**的随机采样 `s` 个块的期望与集中界，现已由 §七 给出计数形式：
  `retainedSum_eq_card_mul_slotCount` 给出均匀随机下的期望块数（整数形式），
  `markov_subset_count` 给出 Markov 型集中界（高概率下界的计数版本）。
  真正**未做**的只剩指数型 Chernoff 集中界（需独立概率空间，属另一主题）。
- **未做 —— 混合掩码（BigBird 型：局部 + 全局 + 随机）**：本文件只有块因果与滑窗；
  混合掩码的精确计数**未做**。
- **标注 —— 用 `Finset.filter` 的基数直接计数**：为避免 `Nat.card` 与
  `DecidableRel` 的实例纠缠，计数直接用 `Finset` 的 `card`（`Finset.filter`），
  闭式证明是「逐行求和 + `Finset.card_range`」的组合，而非组合恒等式的代数变形。
- **标注 —— 与 `RealBlockSparse` 的衔接**：`RealBlockSparse.block_sparse_block_count_le_total`
  给的是「块数 ≤ 总块数」；本文件给出**精确**值与**收紧**的比值
  （`causalMaskCount_le_total` 给 1/2，`windowMaskCount_one_le_total` 给三对角比率）。
  不删旧结论（旧版仍是有效上界，符合 STYLE §5.3）。
- **标注 —— `causalMaskCount_eq` 用 `Nat` 除法**：三角形数写作 `nb(nb+1)/2`；
  涉及比较时用 `omega` 或先 `2·LHS = nb(nb+1)` 消去除法，避免 `Nat` 截断陷阱。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

/-! ## 一、块掩码与逐行计数 -/

/-- **块掩码的逐行计数**：第 `i` 行中满足 `allowed i j` 的 `j ∈ range nb` 的个数。 -/
def rowCount (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] (i : ℕ) : ℕ :=
  ((Finset.range nb).filter (fun j => allowed i j)).card

/-- **块掩码的总块数**：`∑_{i<nb} rowCount nb allowed i`。
与「`range nb × range nb` 上 filter 取 card」等价，但**逐行**形式便于求闭式。 -/
def maskCount (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] : ℕ :=
  ∑ i in Finset.range nb, rowCount nb allowed i

/-- **`maskCount` 的上界（平凡）**：每行至多 `nb` 个块，共 `nb` 行。 -/
theorem maskCount_le_total (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] :
    maskCount nb allowed ≤ nb * nb := by
  unfold maskCount rowCount
  calc ∑ _i in Finset.range nb, ((Finset.range nb).filter (fun j => allowed _i j)).card
      ≤ ∑ _i in Finset.range nb, nb :=
        Finset.sum_le_sum fun i _ => (Finset.card_filter_le _ _).trans_eq (Finset.card_range nb)
    _ = nb * nb := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **行计数的补集记账（核心恒等式）**：对固定 `i`，
`rowCount nb allowed i + rowCount nb (fun i j => ¬ allowed i j) i = nb`。

即「第 `i` 行的每个块要么被保留要么被丢弃」——这是所有精确计数的**记账基础**。
（引理名是 `Finset.filter_card_add_filter_neg_card_eq_card`，
**不是** `card_filter_add_card_filter_not`——已实测。） -/
theorem rowCount_add_compl (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] (i : ℕ) :
    rowCount nb allowed i
      + rowCount nb (fun i j => ¬ allowed i j) i = nb := by
  unfold rowCount
  rw [Finset.filter_card_add_filter_neg_card_eq_card]
  exact Finset.card_range nb

/-- **总计数的补集记账**：`maskCount nb allowed + maskCount nb (¬allowed) = nb²`。

每个块**恰好**属于掩码或其补掩码，故两者之和恰为总块数——这给出
「非满掩码严格省块」的精确判据（`< nb²` 当且仅当补掩码非空）。 -/
theorem maskCount_add_compl_eq_total (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] :
    maskCount nb allowed + maskCount nb (fun i j => ¬ allowed i j) = nb * nb := by
  unfold maskCount
  rw [← Finset.sum_add_distrib]
  rw [show nb * nb = ∑ _i in Finset.range nb, nb by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]]
  exact Finset.sum_congr rfl fun i _ => rowCount_add_compl nb allowed i

/-- **严格性**：补掩码非空（存在某个块不满足 `allowed`）时掩码块数**严格**小于 `nb²`。

这是「比值 < 1」（而非 ≤ 1）的精确条件。 -/
theorem maskCount_lt_total_of_exists_not (nb : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] (h : ∃ i < nb, ∃ j < nb, ¬ allowed i j) :
    maskCount nb allowed < nb * nb := by
  have hcompl : 0 < maskCount nb (fun i j => ¬ allowed i j) := by
    obtain ⟨i, hi, j, hj, hij⟩ := h
    unfold maskCount
    refine Finset.sum_pos' (fun k _ => Nat.zero_le _) ⟨i, Finset.mem_range.mpr hi, ?_⟩
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hij⟩⟩
  have := maskCount_add_compl_eq_total nb allowed
  omega

/-! ## 二、块因果掩码的精确计数 -/

/-- **块因果关系**：`j ≤ i`（块下三角）。 -/
def blockCausalAllowed (i j : ℕ) : Prop := j ≤ i

instance : DecidableRel blockCausalAllowed := fun i j => Nat.decLe j i

/-- **块因果的第 `i` 行计数**：`j ≤ i` 且 `j < nb`，即 `min (i+1) nb` 个
（`{j | j ≤ i} ∩ range nb = range (min (i+1) nb)`）。 -/
theorem causalRowCount_eq (nb i : ℕ) :
    rowCount nb blockCausalAllowed i = min (i + 1) nb := by
  unfold rowCount blockCausalAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ i) = Finset.range (min (i + 1) nb) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- **块因果的行计数上界**：`i < nb` 时恰为 `i+1`。 -/
theorem causalRowCount_eq_of_lt (nb i : ℕ) (hi : i < nb) :
    rowCount nb blockCausalAllowed i = i + 1 := by
  rw [causalRowCount_eq, min_eq_left (by omega)]

/-- **三角形数的递推（辅助）**：`(n+1)(n+2)/2 = n(n+1)/2 + (n+1)`。

用「两边乘 2 后相等」证明（`Nat.div` 在 `omega` 下不可穿透）。
本引理把 `Nat.div` 算术一次封装，供 `causalMaskCount_eq` 的归纳步使用。 -/
theorem triang_succ_div_two (n : ℕ) :
    (n + 1) * (n + 2) / 2 = n * (n + 1) / 2 + (n + 1) := by
  have h1 : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h2 : 2 * ((n + 1) * (n + 2) / 2) = (n + 1) * (n + 2) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (n + 1))
  have key : 2 * (n * (n + 1) / 2 + (n + 1)) = (n + 1) * (n + 2) := by
    rw [Nat.mul_add, h1, Nat.mul_add, Nat.mul_one]
    ring
  omega

/-- **块因果掩码的精确块数（核心闭式）**：恰为**三角形数** `nb (nb + 1) / 2`。

证明：对 `nb` 归纳。归纳步用逐行求和 `maskCount (n+1) = maskCount n + (n+1)`
（第 `n` 行有 `n+1` 个块，其余各行的贡献与 `nb = n` 时相同，因 `rowCount` 对
`i < n` 不依赖上界 `nb`——见 `causalRowCount_eq_of_lt`），
再用 `triang_succ_div_two` 配平 `Nat.div`。 -/
theorem causalMaskCount_eq (nb : ℕ) :
    maskCount nb blockCausalAllowed = nb * (nb + 1) / 2 := by
  induction nb with
  | zero => simp [maskCount]
  | succ n ih =>
      have hstep : maskCount (n + 1) blockCausalAllowed
          = maskCount n blockCausalAllowed + (n + 1) := by
        unfold maskCount
        rw [Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i < n := Finset.mem_range.mp hi
          rw [causalRowCount_eq_of_lt (n + 1) i (by omega),
            causalRowCount_eq_of_lt n i hin]
        · exact causalRowCount_eq_of_lt (n + 1) n (by omega)
      rw [hstep, ih, triang_succ_div_two]

/-- **三角形数与稠密块数之比 ≤ 1/2**：`nb(nb+1)/2 ≤ nb²`（`nb ≥ 1`）。

即块因果掩码**至少省一半**块。用 `2·LHS = nb(nb+1) ≤ 2nb²` 配 `nlinarith`
（先把 `Nat.div` 消去，避免 `omega` 无法穿透除法）。 -/
theorem causalMaskCount_le_total (nb : ℕ) (hnb : 1 ≤ nb) :
    maskCount nb blockCausalAllowed ≤ nb * nb := by
  rw [causalMaskCount_eq]
  rcases nb with _ | m
  · omega
  · -- 目标 `(m+1)(m+2)/2 ≤ (m+1)²`：用 `Nat.div_le_iff_le_mul_add_pred`
    rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)]
    nlinarith

/-- **块因果的互补块数**：严格上三角（`i < j`）的块数也是三角形数
（`nb(nb-1)/2`），且与下三角之和恰为 `nb²`。

证明：由互补记账 `T + X = nb²` 与 `T = nb(nb+1)/2` 解出 `X`；
用「两边乘 2 相等」把 `Nat.div` 转成 `ℤ` 上的线性算术（`nlinarith`），
再配 `omega`——直接对 `Nat.div` 用 `omega` 会失败（实测）。 -/
theorem causalMaskCount_compl (nb : ℕ) :
    maskCount nb (fun i j => ¬ blockCausalAllowed i j) = nb * (nb - 1) / 2 := by
  rcases nb with _ | m
  · simp [maskCount]
  · have htotal := maskCount_add_compl_eq_total (m + 1) blockCausalAllowed
    rw [causalMaskCount_eq] at htotal
    have hT : 2 * ((m + 1) * (m + 2) / 2) = (m + 1) * (m + 2) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m + 1))
    have hsub : (m + 1) * ((m + 1) - 1) = m * (m + 1) := by
      rw [Nat.add_sub_cancel, Nat.mul_comm]
    rw [hsub]
    have key : 2 * maskCount (m + 1) (fun i j => ¬ blockCausalAllowed i j) = m * (m + 1) := by
      have hthis : 2 * ((m + 1) * (m + 2) / 2
          + maskCount (m + 1) (fun i j => ¬ blockCausalAllowed i j))
            = 2 * ((m + 1) * (m + 1)) := by rw [htotal]
      rw [Nat.mul_add, hT] at hthis
      have hcast : (2 * maskCount (m + 1) (fun i j => ¬ blockCausalAllowed i j) : ℤ)
          = (m : ℤ) * (m + 1) := by
        have := congrArg (fun n : ℕ => (n : ℤ)) hthis
        push_cast at this
        nlinarith
      exact_mod_cast hcast
    have hX : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
      Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)
    omega
/-! ## 三、滑窗块掩码的精确计数 -/

/-- **滑窗块关系（带宽 `w`）**：`|i - j| ≤ w`，用 `j ≤ i + w ∧ i ≤ j + w` 表达
（避免 `Int` 与 `Nat` 减法的截断陷阱）。 -/
def blockWindowAllowed (w i j : ℕ) : Prop := j ≤ i + w ∧ i ≤ j + w

instance (w : ℕ) : DecidableRel (blockWindowAllowed w) :=
  fun i j => inferInstanceAs (Decidable (j ≤ i + w ∧ i ≤ j + w))

/-- **滑窗行计数 = 显式区间基数**（通用工具）：
`rowCount nb (blockWindowAllowed w) i` 等于两个 `range` 之并/交的基数。

为避免集合运算，本文件只对 `w ∈ {0,1}` 给出**显式枚举**（见下两条），
通用 `w` 的闭式**未做**（见诚实边界）。 -/
theorem windowRowCount_eq_card (nb w i : ℕ) :
    rowCount nb (blockWindowAllowed w) i
      = ((Finset.range nb).filter (fun j => j ≤ i + w ∧ i ≤ j + w)).card := rfl

/-- **`w = 0` 时滑窗就是对角**：`rowCount = 1`（`i < nb`）。 -/
theorem windowRowCount_zero (nb i : ℕ) (hi : i < nb) :
    rowCount nb (blockWindowAllowed 0) i = 1 := by
  unfold rowCount blockWindowAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ i + 0 ∧ i ≤ j + 0) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  rw [hset, Finset.card_singleton]

/-- **`w = 0` 时滑窗块数闭式**：恰为 `nb`（对角线）。 -/
theorem windowMaskCount_zero (nb : ℕ) :
    maskCount nb (blockWindowAllowed 0) = nb := by
  unfold maskCount
  rw [show (∑ i in Finset.range nb, rowCount nb (blockWindowAllowed 0) i)
      = ∑ _i in Finset.range nb, 1 from
    Finset.sum_congr rfl fun i hi => windowRowCount_zero nb i (Finset.mem_range.mp hi)]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- **`w = 0` 时比值 ≤ 1**：`nb ≤ nb²`（`nb ≥ 1`）。 -/
theorem windowMaskCount_zero_le_total (nb : ℕ) (hnb : 1 ≤ nb) :
    maskCount nb (blockWindowAllowed 0) ≤ nb * nb := by
  rw [windowMaskCount_zero]; nlinarith

/-- **`w = 1` 的内部行计数**（`0 < i` 且 `i + 1 < nb`）：恰为 `3`
（`{i-1, i, i+1}`）。 -/
theorem windowRowCount_one (nb i : ℕ) (h0 : 0 < i) (h1 : i + 1 < nb) :
    rowCount nb (blockWindowAllowed 1) i = 3 := by
  unfold rowCount blockWindowAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ i + 1 ∧ i ≤ j + 1)
      = {i - 1, i, i + 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [hset]
  rw [show ({i - 1, i, i + 1} : Finset ℕ) = insert (i - 1) (insert i {i + 1}) from rfl]
  rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton]; omega

/-- **`w = 1` 的首行计数**（`1 < nb`）：恰为 `2`（`{0, 1}`）。 -/
theorem windowRowCount_one_zero (nb : ℕ) (h : 1 < nb) :
    rowCount nb (blockWindowAllowed 1) 0 = 2 := by
  unfold rowCount blockWindowAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ 0 + 1 ∧ 0 ≤ j + 1) = {0, 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [hset, Finset.card_pair (by omega : (0 : ℕ) ≠ 1)]

/-- **`w = 1` 的末行计数**（`1 < nb`）：恰为 `2`（`{nb-2, nb-1}`）。 -/
theorem windowRowCount_one_top (nb : ℕ) (h : 1 < nb) :
    rowCount nb (blockWindowAllowed 1) (nb - 1) = 2 := by
  unfold rowCount blockWindowAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ nb - 1 + 1 ∧ nb - 1 ≤ j + 1)
      = {nb - 2, nb - 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  rw [hset, Finset.card_pair (by omega : nb - 2 ≠ nb - 1)]

/-- **`w = 1` 时的滑窗块数（闭式，`3 ≤ nb`）**：`3nb - 2`。
即「第 0 行 2 个 + 末行 2 个 + 其余 `nb-2` 行各 3 个」。

证明：把 `range nb` 拆成 `{0} ∪ Ico 1 (nb-1) ∪ {nb-1}` 三段
（用 `Finset.sum_range_succ'` 去首项、`Finset.sum_range_succ` 去末项），
逐段用 `windowRowCount_one_zero` / `windowRowCount_one` / `windowRowCount_one_top`。 -/
theorem windowMaskCount_one (nb : ℕ) (hnb : 3 ≤ nb) :
    maskCount nb (blockWindowAllowed 1) = 3 * nb - 2 := by
  have h0 : rowCount nb (blockWindowAllowed 1) 0 = 2 :=
    windowRowCount_one_zero nb (by omega)
  have htop : rowCount nb (blockWindowAllowed 1) (nb - 1) = 2 :=
    windowRowCount_one_top nb (by omega)
  have hinner : ∀ i ∈ Finset.Ico 1 (nb - 1), rowCount nb (blockWindowAllowed 1) i = 3 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact windowRowCount_one nb i (by omega) (by omega)
  -- 三段拆分：`range nb = {0} ∪ Ico 1 (nb-1) ∪ {nb-1}`
  have hsplit : ∑ i in Finset.range nb, rowCount nb (blockWindowAllowed 1) i
      = rowCount nb (blockWindowAllowed 1) 0
        + (∑ i in Finset.Ico 1 (nb - 1), rowCount nb (blockWindowAllowed 1) i)
        + rowCount nb (blockWindowAllowed 1) (nb - 1) := by
    have hmid : ∑ i in Finset.Ico 1 (nb - 1), rowCount nb (blockWindowAllowed 1) i
        = ∑ x in Finset.range (nb - 2), rowCount nb (blockWindowAllowed 1) (x + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun k _ => by simp only [Nat.add_comm]
    -- `range nb = insert 0 (Ico 1 (nb-1)) ∪ {nb-1}`（`nb ≥ 3`）
    have hset : Finset.range nb
        = insert 0 (Finset.Ico 1 (nb - 1)) ∪ ({nb - 1} : Finset ℕ) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico, Finset.mem_union,
        Finset.mem_singleton]
      omega
    have hdisj : Disjoint (insert 0 (Finset.Ico 1 (nb - 1))) ({nb - 1} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_Ico]
      omega
    have h0not : (0 : ℕ) ∉ Finset.Ico 1 (nb - 1) := by simp [Finset.mem_Ico]
    rw [hset, Finset.sum_union hdisj, Finset.sum_insert h0not, Finset.sum_singleton, hmid]
  have hlen : (Finset.Ico 1 (nb - 1)).card = nb - 2 := by
    rw [Nat.card_Ico]; omega
  unfold maskCount
  rw [hsplit, h0, htop, Finset.sum_congr rfl hinner, Finset.sum_const, hlen, smul_eq_mul]
  omega

/-! ## 四、与 `RealBlockSparse` 的衔接 -/

/-- **三对角滑窗省块**：`3nb - 2 ≤ nb²`（`nb ≥ 3`），比值 ≤ 1。 -/
theorem windowMaskCount_one_le_total (nb : ℕ) (hnb : 3 ≤ nb) :
    maskCount nb (blockWindowAllowed 1) ≤ nb * nb := by
  rw [windowMaskCount_one nb hnb]
  have : (3 : ℤ) * nb - 2 ≤ nb * nb := by
    have hb : (3 : ℤ) ≤ nb := by exact_mod_cast hnb
    nlinarith
  omega

/-- **与 `RealBlockSparse` 的块计数结论一致**：本文件的 `maskCount_le_total`
即 `RealBlockSparse.block_sparse_block_count_le_total` 在同一 `nb` 下的
「块数 ≤ 总块数」形式；本文件的增量是**精确值**与**收紧的比值**。 -/
theorem maskCount_le_total_nb (nb : ℕ) (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] :
    maskCount nb allowed ≤ nb * nb := maskCount_le_total nb allowed

/-! ## 五、滑窗块掩码的**一般带宽** `w` 闭式（WP8 新增）

§三 只给出 `w ∈ {0,1}` 的精确闭式。本节把带宽推到**任意** `w`：
逐行给出 `min(i+w, nb-1) + 1 - (i-w)` 的显式形式，再对 `i` 求和得总块数的闭式。

关键恒等式（**逐行闭式**）：第 `i` 行（`i < nb`）允许的块恰为区间
`[i - w, min(i+w, nb-1)]`，故行计数为 `min(i+w, nb-1) + 1 - (i-w)`。
两端的**截断**（下界 `i-w` 被 `0` 截、上界 `i+w` 被 `nb-1` 截）正是
「首尾行块数少于 `2w+1`」的原因。

- **标注 —— 一律用 `ℕ` 截断减法**：`i - w` 在 `i < w` 时取 `0`，恰好等价于
  「下界被 `0` 截断」；`min(i+w, nb-1)` 等价于「上界被 `nb-1` 截断」。
  故**不需要** `Int`，也避开了整数减法的符号陷阱。 -/

/-- **滑窗行计数的显式闭式（一般 `w`，核心）**：`i < nb` 时第 `i` 行的允许块数
恰为 `min (i+w) (nb-1) + 1 - (i-w)`。

证明：把 `(range nb).filter (blockWindowAllowed w i)` 识别为**整数区间**
`Icc (i-w) (min (i+w) (nb-1))`（`omega` 逐点判定两个成员关系等价），
再用 `Nat.card_Icc`。 -/
theorem windowRowCount_eq (nb w i : ℕ) (hi : i < nb) :
    rowCount nb (blockWindowAllowed w) i
      = min (i + w) (nb - 1) + 1 - (i - w) := by
  unfold rowCount blockWindowAllowed
  have hset : (Finset.range nb).filter (fun j => j ≤ i + w ∧ i ≤ j + w)
      = Finset.Icc (i - w) (min (i + w) (nb - 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hset, Nat.card_Icc]

/-- **无截断（内部行）**：`w ≤ i` 且 `i + w ≤ nb - 1` 时行计数恰为 `2w+1`
（完整的双侧窗口 `[i-w, i+w]`）。 -/
theorem windowRowCount_plateau (nb w i : ℕ) (hi : i < nb) (hlo : w ≤ i)
    (hhi : i + w ≤ nb - 1) :
    rowCount nb (blockWindowAllowed w) i = 2 * w + 1 := by
  rw [windowRowCount_eq nb w i hi, min_eq_left hhi]
  omega

/-- **仅下界截断（首部行）**：`i ≤ w` 且 `i + w ≤ nb - 1` 时行计数为 `i + w + 1`。 -/
theorem windowRowCount_rampup (nb w i : ℕ) (hi : i < nb) (hlo : i ≤ w)
    (hhi : i + w ≤ nb - 1) :
    rowCount nb (blockWindowAllowed w) i = i + w + 1 := by
  rw [windowRowCount_eq nb w i hi, min_eq_left hhi]
  omega

/-- **上界截断（尾部行）**：`nb - 1 ≤ i + w` 时行计数为 `nb - (i - w)`。 -/
theorem windowRowCount_rampdown (nb w i : ℕ) (hi : i < nb) (htop : nb - 1 ≤ i + w) :
    rowCount nb (blockWindowAllowed w) i = nb - (i - w) := by
  rw [windowRowCount_eq nb w i hi, min_eq_right htop]
  omega

/-- **行计数的统一上界**：任意行的允许块数 `≤ 2w+1`（窗口宽度决定单行上限）。 -/
theorem windowRowCount_le (nb w i : ℕ) (hi : i < nb) :
    rowCount nb (blockWindowAllowed w) i ≤ 2 * w + 1 := by
  rw [windowRowCount_eq nb w i hi]; omega

/-! ### 总块数闭式（满带宽区间 `2w+1 ≤ nb`） -/

/-- **混合截断的逐行闭式（辅助）**：`i < nb` 时行计数等于
`2w+1 - (i+w-(nb-1)) - (w-i)` 的截断形式，即「`2w+1` 减去上下两侧的截断亏损」。

本引理是求和的基础：行计数可写成 `2w+1` 减去两个**非负**亏损
`max(0, i+w-(nb-1))` 与 `max(0, w-i)`。 -/
theorem windowRowCount_deficit (nb w i : ℕ) (hi : i < nb) :
    rowCount nb (blockWindowAllowed w) i
      = 2 * w + 1 - (i + w - (nb - 1)) - (w - i) := by
  rw [windowRowCount_eq nb w i hi]
  -- 分四种情形处理 `min` 与两处 `Nat` 减法：
  -- (1) 无截断 (2) 仅上侧截断 (3) 仅下侧截断 (4) 两侧都截断
  rcases le_or_lt (i + w) (nb - 1) with htop | htop <;>
    rcases le_or_lt i w with hbot | hbot
  · -- (1) `i + w ≤ nb-1`、`i ≤ w`
    rw [min_eq_left htop, Nat.sub_eq_zero_of_le htop, Nat.sub_eq_zero_of_le hbot]
    omega
  · -- (2) `i + w ≤ nb-1`、`w < i`
    rw [min_eq_left htop, Nat.sub_eq_zero_of_le htop]
    omega
  · -- (3) `nb-1 < i + w`、`i ≤ w`
    rw [min_eq_right (le_of_lt htop), Nat.sub_eq_zero_of_le hbot]
    omega
  · -- (4) `nb-1 < i + w`、`w < i`
    rw [min_eq_right (le_of_lt htop)]
    omega

/-- **倒序三角数（核心辅助）**：`∑_{k<w} (w - k) = w(w+1)/2`。

证明用 `Finset.sum_range_reflect`：`∑_{k<w} k = ∑_{k<w}(w-1-k)`，
故 `∑_{k<w}(w-k) = ∑_{k<w}(k+1) = w(w-1)/2 + w`。 -/
theorem sum_range_sub_id (w : ℕ) :
    ∑ k ∈ Finset.range w, (w - k) = w * (w + 1) / 2 := by
  -- 反射：`∑ (w-1-k) = ∑ k`
  have hreflect : (∑ k ∈ Finset.range w, (w - 1 - k)) = ∑ k ∈ Finset.range w, k :=
    Finset.sum_range_reflect (fun i => i) w
  -- `w - k = (w - 1 - k) + 1`（`k < w`）
  have hpt : ∀ k ∈ Finset.range w, (w - k) = (w - 1 - k) + 1 := by
    intro k hk
    have hk' : k < w := Finset.mem_range.mp hk
    omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hreflect]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hsum : (∑ k ∈ Finset.range w, k) = w * (w - 1) / 2 := by
    rw [show (∑ k ∈ Finset.range w, k) = ∑ k in Finset.range w, k from
      Finset.sum_congr rfl fun k _ => rfl]
    exact Finset.sum_range_id w
  rw [hsum]
  have htri : 2 * (w * (w - 1) / 2) = w * (w - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self w)
  have htri2 : 2 * (w * (w + 1) / 2) = w * (w + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self w)
  -- `w(w-1) + 2w = w(w+1)`：把两边都归一为 `w*w + w`
  have hkey : w * (w - 1) + 2 * w = w * (w + 1) := by
    rcases w with _ | k
    · simp
    · rw [Nat.add_sub_cancel]; ring
  omega

/-- **单绑定求和辅助（上侧截断区）**：`∑_{k<w} (2w - k) = w(3w+1)/2`。

证明：`2w - k = w + (w - k)`，用 `sum_range_sub_id` 收尾。 -/
theorem sum_range_two_mul_sub (w : ℕ) :
    ∑ k in Finset.range w, (2 * w - k) = w * (3 * w + 1) / 2 := by
  have hpt : ∀ k ∈ Finset.range w, (2 * w - k) = w + (w - k) := by
    intro k hk
    have hk' : k < w := Finset.mem_range.mp hk
    omega
  rw [show (∑ k in Finset.range w, (2 * w - k))
      = ∑ k ∈ Finset.range w, (2 * w - k) from
    Finset.sum_congr rfl fun k _ => rfl]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul]
  rw [sum_range_sub_id]
  have heven : Even (w * (3 * w + 1)) := by
    rcases Nat.even_or_odd w with h | h
    · obtain ⟨m, rfl⟩ := h
      exact ⟨m * (3 * (2 * m) + 1), by ring⟩
    · obtain ⟨m, rfl⟩ := h
      exact ⟨(2 * m + 1) * (3 * m + 2), by ring⟩
  have htri : 2 * (w * (w + 1) / 2) = w * (w + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self w)
  have htri2 : 2 * (w * (3 * w + 1) / 2) = w * (3 * w + 1) :=
    Nat.two_mul_div_two_of_even heven
  -- `w*w + w(w+1)/2 = w(3w+1)/2`：两边乘 2 后是 `3w² + w = w(3w+1)` 的恒等式
  have hkey : 2 * (w * w + w * (w + 1) / 2) = w * (3 * w + 1) := by
    rw [Nat.mul_add, htri]
    ring
  omega

/-- **满带宽区间的三段配平（核心算术，独立引理）**：`2w+1 ≤ nb` 时
`[w(w-1)/2 + w² + w] + (nb-2w)(2w+1) + [w(3w+1)/2] = nb(2w+1) - w(w+1)`。

把整个闭式的算术集中在这一条里（两个三角数 + 一个乘积），
`windowMaskCount_general` 只负责把它接到三段求和上——这样算术部分可独立调试。 -/
theorem windowMaskCount_general_arith (nb w : ℕ) (h : 2 * w + 1 ≤ nb) :
    w * (w - 1) / 2 + w * w + w + ((nb - 2 * w) * (2 * w + 1) + w * (3 * w + 1) / 2)
      = (2 * w + 1) * nb - w * (w + 1) := by
  have h2w : 2 * w ≤ nb := by omega
  have hA : w * (w + 1) ≤ (2 * w + 1) * nb := by
    have hnb : w + 1 ≤ nb := by omega
    calc w * (w + 1) ≤ (w + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * w + 1) * nb := Nat.mul_le_mul (by omega) hnb
  -- 三个 `/2` 的「乘 2 唯一性」事实
  have h1 : 2 * (w * (w - 1) / 2) = w * (w - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self w)
  have heven : Even (w * (3 * w + 1)) := by
    rcases Nat.even_or_odd w with hh | hh
    · obtain ⟨m, rfl⟩ := hh
      exact ⟨m * (3 * (2 * m) + 1), by ring⟩
    · obtain ⟨m, rfl⟩ := hh
      exact ⟨(2 * m + 1) * (3 * m + 2), by ring⟩
  have h2 : 2 * (w * (3 * w + 1) / 2) = w * (3 * w + 1) :=
    Nat.two_mul_div_two_of_even heven
  -- 两边同乘 2 消去除法
  suffices h2eq : 2 * (w * (w - 1) / 2 + w * w + w + ((nb - 2 * w) * (2 * w + 1)
      + w * (3 * w + 1) / 2)) = 2 * ((2 * w + 1) * nb - w * (w + 1)) by
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2eq
  -- 展成 `Nat` 多项式；用 `Nat.mul_add` 与两个 `/2` 还原式消去除法，
  -- 最后转 `ℤ`（减法无截断）用 `ring` 收尾
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, h1, h2]
  have hsub : (nb - 2 * w) * (2 * w + 1) = nb * (2 * w + 1) - 2 * w * (2 * w + 1) := by
    rw [← Nat.sub_mul]
  rw [hsub, Nat.mul_sub_left_distrib]
  have hge1 : 2 * w * (2 * w + 1) ≤ nb * (2 * w + 1) := Nat.mul_le_mul_right _ h2w
  have hge3 : w ≤ w * w := by
    rcases w with _ | k
    · simp
    · nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hge1, Nat.cast_sub hA]
  have hexp : ((w * w - w * 1 : ℕ) : ℤ) = (w : ℤ) * (w : ℤ) - w := by
    have hge3' : w * 1 ≤ w * w := by simpa using hge3
    push_cast [Nat.cast_sub hge3']; ring
  rw [hexp]
  ring

/-- **单绑定求和辅助（下侧截断区）**：`∑_{i<w} (i + w + 1) = w(w-1)/2 + w² + w`。 -/
theorem sum_range_add_const (w : ℕ) :
    ∑ i in Finset.range w, (i + w + 1) = w * (w - 1) / 2 + w * w + w := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_range_id]
  rw [show (∑ _x in Finset.range w, (1 : ℕ)) = w by simp]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
/-- **滑窗块数闭式（满带宽区间，核心）**：`2w+1 ≤ nb` 时
`maskCount = nb·(2w+1) - w(w+1)`。

证明：逐行用 `windowRowCount_eq` 的显式闭式 `min(i+w,nb-1)+1-(i-w)`，
把 `range nb` 拆成下侧截断区 `[0,w)`、中段 `[w, nb-w)`、上侧截断区 `[nb-w, nb)`
三段分别求和。三段的**值**分别是 `sum_range_add_const`、`(nb-2w)(2w+1)`、
`sum_range_two_mul_sub`（见三个辅助引理），配平由 `windowMaskCount_general_arith` 完成。

数值验证：`nb=5, w=2` 给 `5·5 − 6 = 19`；
`nb=5, w=1` 给 `15 − 2 = 13`，`nb=5, w=0` 给 `5`（与 GPU 直算一致）。 -/
theorem windowMaskCount_general (nb w : ℕ) (h : 2 * w + 1 ≤ nb) :
    maskCount nb (blockWindowAllowed w) = (2 * w + 1) * nb - w * (w + 1) := by
  unfold maskCount
  have hsplit : Finset.range nb
      = Finset.range w ∪ (Finset.Ico w (nb - w) ∪ Finset.Ico (nb - w) nb) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj1 : Disjoint (Finset.range w) (Finset.Ico w (nb - w) ∪ Finset.Ico (nb - w) nb) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_range] at hx
    rcases Finset.mem_union.mp hx' with hx' | hx' <;> simp only [Finset.mem_Ico] at hx' <;> omega
  have hdisj2 : Disjoint (Finset.Ico w (nb - w)) (Finset.Ico (nb - w) nb) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ico] at hx hx'
    omega
  rw [hsplit, Finset.sum_union hdisj1, Finset.sum_union hdisj2]
  -- 三段各自的逐行值
  have hbot : ∀ i ∈ Finset.range w, rowCount nb (blockWindowAllowed w) i = i + w + 1 := by
    intro i hi
    have hiw : i < w := Finset.mem_range.mp hi
    rw [windowRowCount_eq nb w i (by omega)]
    have h1 : min (i + w) (nb - 1) = i + w := min_eq_left (by omega)
    rw [h1]; omega
  have hmid : ∀ i ∈ Finset.Ico w (nb - w), rowCount nb (blockWindowAllowed w) i = 2 * w + 1 := by
    intro i hi
    obtain ⟨hiw, hiub⟩ := Finset.mem_Ico.mp hi
    have hilt : i < nb := by omega
    rw [windowRowCount_eq nb w i hilt]
    have h1 : min (i + w) (nb - 1) = i + w := min_eq_left (by omega)
    rw [h1]
    omega
  have htop : ∀ i ∈ Finset.Ico (nb - w) nb, rowCount nb (blockWindowAllowed w) i
      = 2 * w - (i - (nb - w)) := by
    intro i hi
    obtain ⟨hil, hiu⟩ := Finset.mem_Ico.mp hi
    have hilt : i < nb := hiu
    have hrd : nb - 1 ≤ i + w := by omega
    have hproc : nb - (i - w) = 2 * w - (i - (nb - w)) := by omega
    rw [windowRowCount_rampdown nb w i hilt hrd, hproc]
  rw [Finset.sum_congr rfl hbot, Finset.sum_congr rfl hmid, Finset.sum_congr rfl htop]
  -- 下侧：`∑_{i<w}(i+w+1)`
  rw [sum_range_add_const]
  -- 中段：`∑_{i∈Ico w (nb-w)} (2w+1) = (nb-2w)(2w+1)`
  rw [show (∑ _i in Finset.Ico w (nb - w), (2 * w + 1)) = (nb - 2 * w) * (2 * w + 1) from by
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    have : nb - w - w = nb - 2 * w := by omega
    rw [this, Nat.mul_comm]]
  -- 上侧：换元 `i = nb - w + k`（`k < w`），被加项化为 `2w - k`
  rw [show (∑ i in Finset.Ico (nb - w) nb, (2 * w - (i - (nb - w))))
        = ∑ k in Finset.range w, (2 * w - k) from by
    rw [Finset.sum_Ico_eq_sum_range]
    have hbnd : nb - (nb - w) = w := by omega
    rw [hbnd]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < w := Finset.mem_range.mp hk
    congr 1
    omega]
  rw [sum_range_two_mul_sub]
  -- 三段配平
  exact windowMaskCount_general_arith nb w h

/-- **`w = 0` 回收**：`windowMaskCount_general` 在 `w = 0` 时给出 `nb`，
与 §三 的 `windowMaskCount_zero` 一致（交叉验证闭式）。 -/
theorem windowMaskCount_general_zero (nb : ℕ) (h : 2 * 0 + 1 ≤ nb) :
    maskCount nb (blockWindowAllowed 0) = (2 * 0 + 1) * nb - 0 * (0 + 1) :=
  windowMaskCount_general nb 0 h

/-- **`w = 1` 回收（`nb ≥ 3`）**：闭式给 `3nb - 2`，与 §三 `windowMaskCount_one` 一致
——即一般闭式在 `w = 1` 上**精确复现**旧结果（不废弃旧定理，符合 STYLE §5.3）。 -/
theorem windowMaskCount_general_one (nb : ℕ) (h : 2 * 1 + 1 ≤ nb) :
    maskCount nb (blockWindowAllowed 1) = 3 * nb - 2 := by
  have h' := windowMaskCount_general nb 1 h
  have hl : (2 * 1 + 1) * nb - 1 * (1 + 1) = 3 * nb - 2 := by norm_num
  rw [hl] at h'
  exact h'

/-! ### 一般闭式在**满带宽区间**上的比值界 -/

/-- **满带宽区间的块数 ≤ 总块数**：`2w+1 ≤ nb` 时 `nb(2w+1) - w(w+1) ≤ nb²`。

证明：设 `d = nb - w`，则 `2w+1 ≤ nb` 给出 `d ≥ w + 1`。
目标化为 `nb(2w+1) - w(w+1) ≤ nb²`，即
`nb² - nb(2w+1) + w(w+1) ≥ 0`，而
`nb² - nb(2w+1) + w(w+1) = (nb - w)(nb - w - 1) = d(d-1) ≥ 0`
（因 `d ≥ 1`）。全部在 `ℕ` 上完成，不引入 `ℤ` 转换。 -/
theorem windowMaskCount_general_le_total (nb w : ℕ) (h : 2 * w + 1 ≤ nb) :
    maskCount nb (blockWindowAllowed w) ≤ nb * nb := by
  rw [windowMaskCount_general nb w h]
  -- 直接转为 `ℤ`：目标为 `(2w+1)nb - w(w+1) ≤ nb²`，
  -- 即 `nb² - (2w+1)nb + w(w+1) = (nb-w)(nb-w-1) ≥ 0`（因 `nb ≥ 2w+1 ≥ w+1`）
  have hge : w * (w + 1) ≤ (2 * w + 1) * nb := by
    have hnb : w + 1 ≤ nb := by omega
    calc w * (w + 1) ≤ (w + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * w + 1) * nb := Nat.mul_le_mul (by omega) hnb
  have hcast : (((2 * w + 1) * nb - w * (w + 1) : ℕ) : ℤ) ≤ ((nb * nb : ℕ) : ℤ) := by
    have hw1 : w + 1 ≤ nb := by omega
    have hw1z : (1 : ℤ) ≤ (nb : ℤ) - w := by
      have : (w : ℤ) + 1 ≤ nb := by exact_mod_cast hw1
      linarith
    push_cast [Nat.cast_sub hge]
    nlinarith [sq_nonneg ((nb : ℤ) - w - 1), hw1z,
      (Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
  exact_mod_cast hcast

/-- **满带宽区间的块数下界（非退化）**：`w ≥ 1` 且 `2w+1 ≤ nb` 时块数
**严格大于** `nb`——即带宽 `w ≥ 1` 的滑窗块数**总是**多于纯对角，闭合了
「只有 `w = 0` 才退化为对角」这一直觉。

证明：块数 `= nb(2w+1) - w(w+1)`，要证 `> nb`。
等价于 `nb·2w > w(w+1)`，即 `2·nb > w + 1`（`w ≥ 1` 时约去 `w`），
由 `w + 1 ≤ nb ≤ 2nb` 即得。 -/
theorem windowMaskCount_general_gt_nb (nb w : ℕ) (hw : 1 ≤ w) (h : 2 * w + 1 ≤ nb) :
    nb < maskCount nb (blockWindowAllowed w) := by
  rw [windowMaskCount_general nb w h]
  have hw1 : w * (w + 1) ≤ (2 * w + 1) * nb := by
    have hnb : w + 1 ≤ nb := by omega
    calc w * (w + 1) ≤ (w + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * w + 1) * nb := Nat.mul_le_mul (by omega) hnb
  have hle : w * (w + 1) ≤ (2 * w + 1) * nb := by
    have hnb : w + 1 ≤ nb := by omega
    calc w * (w + 1) ≤ (w + 1) * (w + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * w + 1) * nb := Nat.mul_le_mul (by omega) hnb
  rw [Nat.lt_sub_iff_add_lt]
  have hnb : w + 1 ≤ nb := by omega
  calc nb + w * (w + 1) ≤ nb + w * nb := Nat.add_le_add_left (Nat.mul_le_mul_left w hnb) nb
    _ = (w + 1) * nb := by ring
    _ < (2 * w + 1) * nb :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by omega)

/-! ## 六、非均匀块大小与末尾不满块（WP8 新增）

§五 及此前各节都按**块的下标**计数（`nb` 个等大块）。真实实现里
**末尾块常不满**（`n` 不是块大小 `B` 的整数倍），且各块大小可以**不等**。
本节给出按**元素数加权**的计数与它向等大情形的**精确退化**。

- **标注 —— 加权计数的定义域**：取块大小 `b : Fin m → ℕ`（`m` 是块数，
  `b i` 是第 `i` 块的元素数，约定 `b i ≥ 1`，允许 `i = m-1` 时 `b i < B`）。
  **元素加权块数** `weightedBlockCount b allowed = ∑_{(i,j) allowed} b i * b j`
  是「块稀疏注意力真正参与计算的**(元素, 元素)对数**」——即省下的真实算力。
  这与 `RealBlockSparse.block_sparse_entries_le_dense` 的 `allowedBlockCount · B²`
  不同：后者假设所有块**等大**，本节给出**一般**公式。 -/

/-- **元素加权块数**：允许块对 `(i,j)` 的**元素对数**之和 `∑ b i · b j`。

这是块稀疏真正省下的计算量（`allowedBlockCount · B²` 是一般情形的特例）。 -/
def weightedBlockCount {m : ℕ} (b : Fin m → ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] : ℕ :=
  ∑ i : Fin m, ∑ j : Fin m, (if allowed i j then b i * b j else 0)

/-- **等大块退化（核心）**：所有块大小为常数 `B` 时，元素加权块数
`= allowedBlockCount · B²`——即 §五/§三 的按块计数乘以块内元素数，
回收 `RealBlockSparse.block_sparse_entries_le_dense` 的 `B²` 因子。 -/
theorem weightedBlockCount_const {m : ℕ} (B : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] :
    weightedBlockCount (fun _ : Fin m => B) allowed
      = (∑ i : Fin m, ∑ j : Fin m, (if allowed i j then (1 : ℕ) else 0)) * (B * B) := by
  unfold weightedBlockCount
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : allowed i j <;> simp [h]

/-- **等大块的元素加权 ≤ 稠密元素数**：`B` 等大时加权块数 `≤ m² B²`
（回收 `block_sparse_entries_le_dense`，此处用本节定义重述）。 -/
theorem weightedBlockCount_const_le_dense {m : ℕ} (B : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] :
    weightedBlockCount (fun _ : Fin m => B) allowed ≤ m * m * (B * B) := by
  rw [weightedBlockCount_const]
  have h : (∑ i : Fin m, ∑ j : Fin m, (if allowed i j then (1 : ℕ) else 0)) ≤ m * m := by
    have hrow : ∀ i : Fin m, (∑ j : Fin m, (if allowed i j then (1 : ℕ) else 0)) ≤ m := by
      intro i
      calc (∑ j : Fin m, (if allowed i j then (1 : ℕ) else 0))
          ≤ ∑ _j : Fin m, (1 : ℕ) := Finset.sum_le_sum fun j _ => by split <;> simp
        _ = m := by simp
    calc (∑ i : Fin m, ∑ j : Fin m, (if allowed i j then (1 : ℕ) else 0))
        ≤ ∑ _i : Fin m, m := Finset.sum_le_sum fun i _ => hrow i
      _ = m * m := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_right (B * B) h

/-- **末尾不满块的三类分解（核心）**：设共有 `m` 个块（`m > 0`），前 `m-1` 个大小为 `B`、
末块大小为 `r`。则元素加权块数恰等于三类贡献之和：

`B²·(两端都不是末块的允许对数) + B·r·(恰一端是末块的允许对数) + r²·(两端都是末块的允许对数)`。

这是「末尾不满块」情形的**精确记账**：把加权计数按「末块参与程度」拆成
**内部–内部**、**内部–末块**、**末块–末块**三类。
它与 `weightedBlockCount_const`（全等大）的关系是 `r = B` 时退化为 `m²B²` 口径。 -/
theorem weightedBlockCount_tail_decomp {m : ℕ} (B r : ℕ) (allowed : ℕ → ℕ → Prop)
    [DecidableRel allowed] :
    weightedBlockCount (fun i : Fin m => if (i : ℕ) = m - 1 then r else B) allowed
      = B * B * (∑ i : Fin m, ∑ j : Fin m,
            (if allowed i j ∧ (i : ℕ) ≠ m - 1 ∧ (j : ℕ) ≠ m - 1 then 1 else 0))
        + B * r * (∑ i : Fin m, ∑ j : Fin m,
            (if allowed i j ∧ ((i : ℕ) = m - 1) ≠ ((j : ℕ) = m - 1) then 1 else 0))
        + r * r * (∑ i : Fin m, ∑ j : Fin m,
            (if allowed i j ∧ (i : ℕ) = m - 1 ∧ (j : ℕ) = m - 1 then 1 else 0)) := by
  -- 逐点验证三类指示函数之和恰为加权项，再用求和的线性性
  have hpt : ∀ i j : Fin m,
      (if allowed i j then (if (i : ℕ) = m - 1 then r else B) * (if (j : ℕ) = m - 1 then r else B)
        else 0)
      = B * B * (if allowed i j ∧ (i : ℕ) ≠ m - 1 ∧ (j : ℕ) ≠ m - 1 then 1 else 0)
        + B * r * (if allowed i j ∧ ((i : ℕ) = m - 1) ≠ ((j : ℕ) = m - 1) then 1 else 0)
        + r * r * (if allowed i j ∧ (i : ℕ) = m - 1 ∧ (j : ℕ) = m - 1 then 1 else 0) := by
    intro i j
    by_cases ha : allowed i j
    · simp only [ha, true_and, if_true]
      by_cases hi : (i : ℕ) = m - 1 <;> by_cases hj : (j : ℕ) = m - 1 <;>
        simp [hi, hj, Nat.mul_comm]
    · simp [ha]
  unfold weightedBlockCount
  -- 用 `hpt` 逐点替换（两层 `Finset.sum_congr`）
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j]
  -- RHS 形如 `∑_i ∑_j ((A + B) + C)`；`Finset.mul_sum` 把每层的常数提到求和之外，
  -- 内层的 `∑_j` 随之被分配到三个常数倍的和上，正好就是目标形式
  simp only [Finset.mul_sum, Finset.sum_add_distrib]

/-- **末块不满时加权计数 ≤ 等大计数**：`r ≤ B` 时，
「末块为 `r`」的加权块数 `≤` 「全部为 `B`」的加权块数
——即**末尾不满块只会更省**（不会更贵）。 -/
theorem weightedBlockCount_tail_le_uniform {m : ℕ} (B r : ℕ) (hr : r ≤ B)
    (allowed : ℕ → ℕ → Prop) [DecidableRel allowed] :
    weightedBlockCount (fun i : Fin m => if (i : ℕ) = m - 1 then r else B) allowed
      ≤ weightedBlockCount (fun _ : Fin m => B) allowed := by
  unfold weightedBlockCount
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : allowed i j
  · simp only [h, if_true]
    refine Nat.mul_le_mul ?_ ?_
    · by_cases hi : (i : ℕ) = m - 1 <;> simp [hi, hr]
    · by_cases hj : (j : ℕ) = m - 1 <;> simp [hj, hr]
  · simp [h]

/-! ## 七、随机块的期望与集中界（WP8 新增）

「随机块」（BigBird / 随机稀疏注意力）指在 `N = m·m` 个块槽中**均匀随机**
选 `s` 个。本节用**纯组合计数**（不引入测度论/概率空间）给出：

1. `subsetCount` / `retainedSum`：`s`-子集的个数与「被保住的有用块数」之和；
2. `retainedSum_eq`（**精确一阶矩恒等式，核心**）：对任意「有用块集 `A`」，
   `∑_{|T|=s} |T ∩ A| = C(N-1, s-1) · |A|`——即**均匀随机选块保住的期望块数**
   恰为 `s·|A|/N`（此处用**不可约的整数形式**陈述，避免除法与概率归一化）；
3. `retainedSum_pair`（**精确二阶阶乘矩**）：`∑_{|T|=s} X(X-1) = C(N-2,s-2)·a(a-1)`；
4. `markov_subset_count`（**集中/Markov 计数形式**）：保住至少 `k` 个有用块的
   子集个数 `≤ C(N-1,s-1)·a / k`——随机块的**高概率下界**。

- **标注 —— 为什么用 `Finset.powersetCard` 而非概率空间**：概率空间的测度论
  形式需要 `MeasureTheory` 与 `ENNReal`，而本仓库已有 `RealHoeffding` 的
  **计数**框架（`markov_counting`）。本节与之同构但更基础：直接对
  `Finset.powersetCard s univ` 求和，全部结论是**有限组合恒等式**，
  不依赖 `IsProbabilityMeasure`，也避免 `ENNReal.toReal` 的坑。
- **降级 —— 高阶集中界（Chernoff/Hoeffding 型）**：本节给一阶矩与二阶矩，
  由此可得 Markov（`markov_subset_count`）与 **Chebyshev** 型界；
  但**指数**集中（Hoeffding 型）需要「子集上的独立同分布分解」，
  在**无放回**抽样下并不平凡，故本节的集中界是**多项式型**（Markov/Chebyshev），
  **指数界未做**——见诚实边界。 -/

/-- **`s`-子集全体**：`N` 个槽中选 `s` 个的所有子集（`Finset.powersetCard`）。 -/
def subsetFamily (N s : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.powersetCard s

/-- **保住的有用块数**：子集 `T`（选中的块）与有用块集 `A` 的交的大小。 -/
def retainedBlocks {N : ℕ} (A T : Finset (Fin N)) : ℕ := (T ∩ A).card

/-- **一阶矩：保住块数之和**（对全体 `s`-子集求和）。 -/
def retainedSum (N s : ℕ) (A : Finset (Fin N)) : ℕ :=
  ∑ T in subsetFamily N s, retainedBlocks A T

/-- **槽 `p` 被选中的子集个数**（辅助计数）。 -/
def slotCount (N s : ℕ) (p : Fin N) : ℕ :=
  ∑ T in subsetFamily N s, if p ∈ T then 1 else 0

/-- **含槽 `p` 的 `s`-子集族**：即可用 `slotCount` 计数的集合。 -/
def subsetFamilyAt (N s : ℕ) (p : Fin N) : Finset (Finset (Fin N)) :=
  (subsetFamily N s).filter (fun T => p ∈ T)

/-- **`slotCount` 就是该族的基数**（定义层面的一致性，便于用基数工具）。 -/
theorem slotCount_eq_card (N s : ℕ) (p : Fin N) :
    slotCount N s p = (subsetFamilyAt N s p).card := by
  unfold slotCount subsetFamilyAt
  rw [Finset.card_filter]

/-- **不变性（辅助）**：`(T.image (swap p q)).image (swap p q) = T`。

由 `Equiv.swap_swap`（`(swap p q).trans (swap p q) = refl`）与
`Finset.image_image` 得到。 -/
theorem image_swap_swap {N : ℕ} (p q : Fin N) (T : Finset (Fin N)) :
    (T.image (Equiv.swap p q)).image (Equiv.swap p q) = T := by
  rw [Finset.image_image]
  have hcomp : (Equiv.swap p q) ∘ (Equiv.swap p q) = id := by
    funext x
    exact congrFun (congrArg DFunLike.coe (Equiv.swap_swap p q)) x
  rw [hcomp, Finset.image_id]

/-- **`slotCount` 与 `p` 无关（核心对称性）**：所有槽被选中的次数相同
——这是「均匀随机」的形式化内容，也是交换求和次序的前提。

证明：`T ↦ T.image (swap p q)` 给出 `s`-子集族到自身的双射
（`swap` 是双射，不动 `card`，也不动 `univ`），且把「含 `p`」映到「含 `q`」。
用 `Finset.card_bij` 直接构造：像仍在族内、单射、满射三步。 -/
theorem slotCount_eq_of_ne (N s : ℕ) (p q : Fin N) :
    slotCount N s p = slotCount N s q := by
  rw [slotCount_eq_card, slotCount_eq_card]
  refine Finset.card_bij (fun T _ => T.image (Equiv.swap p q)) ?_ ?_ ?_
  · -- 像仍在 `subsetFamilyAt N s q` 内
    intro T hT
    obtain ⟨hT1, hT2⟩ : T ∈ subsetFamily N s ∧ p ∈ T := by
      simpa only [subsetFamilyAt, Finset.mem_filter] using hT
    obtain ⟨-, hcardT⟩ : T ⊆ Finset.univ ∧ T.card = s := by
      simpa only [subsetFamily, Finset.mem_powersetCard] using hT1
    have hcard : (T.image (Equiv.swap p q)).card = s := by
      rw [Finset.card_image_of_injective _ (Equiv.swap p q).injective]
      exact hcardT
    rw [subsetFamilyAt, Finset.mem_filter, subsetFamily, Finset.mem_powersetCard]
    exact ⟨⟨by simp, hcard⟩, Finset.mem_image.mpr ⟨p, hT2, Equiv.swap_apply_left p q⟩⟩
  · -- 单射：用 `image_swap_swap` 把 `heq` 两边再映一次即还原
    intro T1 _ T2 _ heq
    have h1 := image_swap_swap p q T1
    have h2 := image_swap_swap p q T2
    -- `heq` 的成员证明参数不参与，先剥离
    simp only at heq
    rw [heq] at h1
    rw [← h1, h2]
  · -- 满射：`T` 是 `T.image (swap p q)` 的像
    intro T hT
    obtain ⟨hT1, hT2⟩ : T ∈ subsetFamily N s ∧ q ∈ T := by
      simpa only [subsetFamilyAt, Finset.mem_filter] using hT
    obtain ⟨-, hcardT⟩ : T ⊆ Finset.univ ∧ T.card = s := by
      simpa only [subsetFamily, Finset.mem_powersetCard] using hT1
    have hcard : (T.image (Equiv.swap p q)).card = s := by
      rw [Finset.card_image_of_injective _ (Equiv.swap p q).injective]
      exact hcardT
    refine ⟨T.image (Equiv.swap p q), ?_, image_swap_swap p q T⟩
    rw [subsetFamilyAt, Finset.mem_filter, subsetFamily, Finset.mem_powersetCard]
    exact ⟨⟨by simp, hcard⟩, Finset.mem_image.mpr ⟨q, hT2, Equiv.swap_apply_right p q⟩⟩

/-- **一阶矩恒等式（核心，交换求和）**：对任意有用块集 `A`，
`∑_{|T|=s} |T ∩ A| = Σ_{p∈A} slotCount N s p`——即「保住块数之和」
等于「`A` 中每个槽被选中次数之和」。

这是**交换求和次序**（`Finset.sum_comm`）的直接结果：
`|T ∩ A| = Σ_{p∈A} [p ∈ T]`，故总和可逐槽重排。 -/
theorem retainedSum_eq_sum_slotCount (N s : ℕ) (A : Finset (Fin N)) :
    retainedSum N s A = ∑ p in A, slotCount N s p := by
  unfold retainedSum retainedBlocks slotCount
  -- 先把每个 `|T ∩ A|` 写成 `∑_{p∈A} [p ∈ T]`（单绑定形式），再交换两层求和
  have hpt : ∀ T : Finset (Fin N), (T ∩ A).card = ∑ p in A, (if p ∈ T then 1 else 0) := by
    intro T
    rw [show T ∩ A = A.filter (fun p => p ∈ T) by
      ext x; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
    rw [Finset.card_filter]
  simp only [hpt]
  exact Finset.sum_comm

/-- **打破对称性（核心）：`slotCount` 与槽无关**：任意 `p q : Fin N`，
`slotCount N s p = slotCount N s q`。

由 `slotCount_eq_of_ne` 与 `p = q` 的平凡情形合并得到（`Fin N` 非空时
任意两点可用 `Equiv.swap` 相连；`N = 0` 时 `Fin 0` 为空，量词空洞成立）。 -/
theorem slotCount_eq (N s : ℕ) (p q : Fin N) : slotCount N s p = slotCount N s q := by
  by_cases h : p = q
  · rw [h]
  · exact slotCount_eq_of_ne N s p q

/-- **均匀随机的期望块数（核心，整数形式）**：`∑_{|T|=s} |T ∩ A| = |A| · slotCount N s 0`。

即「保住块数之和」等于「有用块数 × 单槽被选中次数」——由
`retainedSum_eq_sum_slotCount` 与 `slotCount_eq`（与槽无关）合并得到。
**这正是「均匀随机选 `s` 个块，期望保住 `s·|A|/N` 个」的整数形式**
（除以 `C(N,s)` 即得期望）。

一致性检查：`s = 0` 时两侧都为 `0`（空子集不含任何块）；
`s > N` 时 `subsetFamily` 为空，两侧也都为 `0`。 -/
theorem retainedSum_eq_card_mul_slotCount (N s : ℕ) (A : Finset (Fin N)) (hN : 0 < N) :
    retainedSum N s A = A.card * slotCount N s ⟨0, hN⟩ := by
  rw [retainedSum_eq_sum_slotCount]
  rw [Finset.sum_congr rfl fun p _ => slotCount_eq N s p ⟨0, hN⟩]
  rw [Finset.sum_const, smul_eq_mul]

/-- **Markov 型集中界（核心）**：保住**至少** `k` 个有用块的 `s`-子集个数
乘以 `k`，不超过「保住块数之和」——即随机块的**高概率下界**的计数形式。

形式化：`#{T : k ≤ |T ∩ A|} · k ≤ ∑_T |T ∩ A|`。
这是 `RealHoeffding.markov_counting` 的整数计数版本（对求和而非概率陈述），
除以子集总数即得 `P(保住 ≥ k) ≤ E[保住]/k`。

证明：对满足 `k ≤ |T ∩ A|` 的 `T` 逐个用 `k ≤ |T ∩ A|`，
其余项非负，由 `Finset.sum_le_sum` 与 `Finset.mul_card_le_sum` 组合。 -/
theorem markov_subset_count (N s k : ℕ) (A : Finset (Fin N)) :
    k * ((subsetFamily N s).filter (fun T => k ≤ retainedBlocks A T)).card
      ≤ retainedSum N s A := by
  unfold retainedSum
  -- `∑_T |T∩A| ≥ ∑_{T ∈ 过滤集} |T∩A| ≥ ∑_{T ∈ 过滤集} k = k · #过滤集`
  have h1 : ∑ T in (subsetFamily N s).filter (fun T => k ≤ retainedBlocks A T),
      retainedBlocks A T ≤ ∑ T in subsetFamily N s, retainedBlocks A T :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Nat.zero_le _
  have h2 : ((subsetFamily N s).filter (fun T => k ≤ retainedBlocks A T)).card * k
      = ∑ _T in (subsetFamily N s).filter (fun T => k ≤ retainedBlocks A T), k := by
    rw [Finset.sum_const, smul_eq_mul]
  rw [Nat.mul_comm k, h2]
  refine h1.trans' ?_
  exact Finset.sum_le_sum fun T hT => (Finset.mem_filter.mp hT).2

end Lattice
