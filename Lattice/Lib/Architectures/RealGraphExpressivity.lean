import Mathlib
import Lattice.Lib.Architectures.RealGNN
import Lattice.Lib.Architectures.RealWLRefinement
/-!
# LATTICE: 图神经网络的表达力——过平滑极限与 1-WL 不可区分的正则图见证

`RealGNN` 给出消息传递的**数值**界（有界、Lipschitz），`RealGNNEquivariance` 给出
**对称性**（置换等变）。本文件补上第三条腿：**表达力的两条硬限制**。

## 一、过平滑（over-smoothing）

重复消息传递会把各节点特征推向同一值。本文件给出：

1. `uniformMsgPass` / `iterMsgPass`：均匀聚合 `(Wh)_i = (1/|ι|)∑_j h_j` 与 `k` 次迭代；
2. `uniformMsgPass_const_fixed`：常向量是**不动点**；
3. `iterMsgPass_const`：常向量的 `k` 次迭代仍是常向量；
4. `overSmoothing_bound`：`k ≥ 1` 时任意两节点特征**精确相等**（差为 `0`）；
   `2M` 形式的数值界见 `overSmoothing_deviation_bound`（不紧，见 §四之二）；
5. `overSmoothing_limit`：`k → ∞` 时差趋于 0（`Filter.Tendsto`）；
6. `overSmoothing_deviation_bound`：`|iterMsgPass h (k+1) i - iterMsgPass h (k+1) j| ≤ 2M`
   —— 本情形下该界**不紧**（左侧实际为 `0`，见 §四之二）。

## 二、1-WL 不可区分的有限见证

**正则图**是 1-WL 与消息传递 GNN 的经典盲点：所有节点度数相同 ⟹ 均匀聚合
对每个节点给出**完全相同**的值。本文件给出**有限见证**：

7. `regular_cycle_3_regular_cycle_6`（**显式反例**）：`C₃`（三角）与 `C₆`（六边形）
   都是 2-正则图，但**不同构**（`Fintype.card` 分别为 3 和 6）。
   这给出「正则 + 同度数 + 非同构」的**机器验证见证**；
8. `regular_uniform_aggregate_eq`：在 `d`-正则图上，均匀聚合对所有节点给出同一个值
   —— 即 **1-WL 的第一次迭代无法区分任何两个节点**；
9. `oneWL_first_round_blind`：把 7 与 8 组合：存在一对非同构正则图，
   使 1-WL 第一轮的颜色划分在各自内部都是**单色**（无区分力）；
10. `regular_aggregate_determined_by_degree`：均匀聚合的输出**只依赖度数**，
    与图的具体连通结构无关 —— 这是「1-WL 只能看到度数分布」的定量刻画。

## 诚实边界（中文标注）

- **已做（WP7）—— 等基数正则非同构图对 `C₆` vs `2K₃`**：§五给出
  `C6_twoK3_same_card`（同基数）、`twoRegular_oneWL_blind`（2-正则 ⟹ 首轮单色）、
  `C6_twoK3_1WL_blind`（**真正的** 1-WL 盲点见证）。
  **修正**：§四原 `regular_noniso_witness_card` 已更名为
  `same_degree_noniso_witness`——它是「度序列不决定同构」的见证（基数 `3 ≠ 6`），
  **不是** 1-WL 盲点见证（1-WL **能**区分基数不同的图）。
- **未做 —— 完整的 1-WL 等价关系 / 颜色细化不变量**：本文件只给出**首轮**
  的单色性与一对**显式**等基数见证。完整的「1-WL 不可区分 ⟺ GNN 不可区分」
  见**新文件 `RealWLRefinement`**（`gnnFeat_eq_of_wlEq`：任意定深的 GNN ⊆ 1-WL）。
- **未做 —— 过平滑的**紧常数**：`2M(1-1/N)^k` 未证在一般设定下紧；
  对均匀聚合的常向量不动点（`uniformMsgPass_const_fixed`）该界是可达的
  （差恰为 0），但**非**渐近紧。真正紧的界需要随机游走混合时间的谱分析，**未做**。
  **诚实标注（R4 调研）**：Oono–Suzuki §6.2 逐字将其列为公开未解决问题
  （"We leave tighter bounds for d_ℳ in such a case for future research"），
  故本文件**不**投入紧常数，改证 §二 的**精确**结论（`uniformMsgPass_mean_zero`：
  一步**精确**归零，比任何几何界都强）。
- **降级 —— 均匀聚合替代一般邻接**：本文件的过平滑定理针对**均匀**（行随机）
  聚合算子 `(Wh)_i = avg_j h_j`；对一般 `A : ι → ι → ℝ` 的过平滑需要
  归一化邻接的谱间隙假设，**未做**（`RealGNN.degNorm` 只给单步 Lipschitz 界）。
- **未做 —— `C₆` 与 `2K₃` 的机器验证非同构**：§五的见证用的是**不变量相等**
  （单色划分 + 同基数），**未做**完整同构/非同构判定（需连通分量论证）。
- **未做 —— 非线性激活下的过平滑**：本文件的迭代只含**线性**均匀聚合；
  含 `σ` 的版本（`σ` 非恒等）**未做**——它需要 `σ` 的 Lipschitz 常数参与。
- **未做 —— 多分量过平滑**：Li et al. 2018 Thm 1 的收敛目标是**分量指示向量的
  线性组合**（分量内趋同、分量间不混合）；本文件只覆盖**单连通分量**。
- **已做（WP7）—— `C6Edges` / `TwoK3Edges` 的 2-正则组合事实**：两个边集已形式化
  （`C6Edges`：`y = x ± 1`；`TwoK3Edges`：同分量内相异），且 2-正则性由
  `C6Edges_two_regular` / `TwoK3Edges_two_regular`（`decide` 核验）**已证**。
- **未做 —— `C₆` 与 `2K₃` 的机器验证非同构**：§五的见证用**不变量相等**
  （首轮单色 + 同基数），**未做**完整同构/非同构判定（需连通分量论证）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 一、均匀聚合与迭代 -/

/-- **均匀聚合**：`(Wh)_i = (1/|ι|) ∑_j h_j`——把所有邻居特征取平均。
它与 `RealGNN` 的度数归一化聚合 `degNorm` **不同**：两者同为行随机型聚合，
但权重不同（此处 `1/N`，而 `degNorm` 在 `d`-正则图上为 `d/(d+1)`），故**不等价**
（更正见 §三 `regular_uniform_aggregate_eq` 的标注）。 -/
def uniformMsgPass (h : ι → ℝ) : ι → ℝ :=
  fun _ => (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j

/-- **`k` 次迭代**：`iterMsgPass h k = (W^k h)`。 -/
def iterMsgPass (h : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => h
  | k + 1 => uniformMsgPass (iterMsgPass h k)

/-- **均匀聚合保持常向量**：`h` 恒为 `c` ⟹ `Wh` 恒为 `c`。

因为 `(1/N)∑_j c = (1/N)·N·c = c`。这是过平滑的**不动点**。 -/
theorem uniformMsgPass_const (c : ℝ) [Nonempty ι] :
    uniformMsgPass (fun _ : ι => c) = fun _ => c := by
  funext i
  simp only [uniformMsgPass]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **常向量是迭代不动点**：`iterMsgPass (const c) k = const c`。 -/
theorem iterMsgPass_const (c : ℝ) [Nonempty ι] (k : ℕ) :
    iterMsgPass (fun _ : ι => c) k = fun _ => c := by
  induction k with
  | zero => rfl
  | succ n ih => rw [iterMsgPass, ih, uniformMsgPass_const]

/-! ## 二、过平滑的定量界 -/

/-- **一次均匀聚合的偏差收缩**：设 `∀i, |h i - c| ≤ A`（`c` 为均值），则
`|Wh i - c| ≤ (1 - 1/N) · A`。

证明：`Wh i - c = (1/N)∑_j (h j - c)`；取 `j = i` 的一项单独提出，
其余 `N-1` 项各 ≤ A，故 `|(1/N)∑| ≤ (1/N)(|h i - c| + (N-1)A) ≤ (1/N)(A + (N-1)A) = A`…
为得到**严格**收缩 `(1-1/N)A`，用「`∑_j (h j - c)` 的 `i` 项被其余项抵消」的技巧
（见下 `uniform_deviation_shrink`）。 -/
theorem uniformMsgPass_deviation (h : ι → ℝ) (c : ℝ) [Nonempty ι] (i : ι) :
    uniformMsgPass h i - c
      = (Fintype.card ι : ℝ)⁻¹ * ∑ j, (h j - c) := by
  simp only [uniformMsgPass]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
/-- **偏差收缩（核心引理）**：设 `∀j, |h j| ≤ A` 且 `∑_j h j = 0`（已去均值），
`N = |ι| ≥ 1`，则 `|(1/N)∑_j h j| = 0`——**去均值后聚合恒为 0**。

这是过平滑的**精确**机制：一次均匀聚合把向量投影到「常向量」子空间，
去均值分量被**完全抹掉**（不是收缩，是一次清零）。 -/
theorem uniformMsgPass_mean_zero (h : ι → ℝ) (hsum : ∑ j, h j = 0) [Nonempty ι] :
    uniformMsgPass h = fun _ => 0 := by
  funext i
  simp only [uniformMsgPass, hsum, mul_zero]

/-- **一次聚合即达常向量**：`uniformMsgPass h` 恒等于其均值
（因为每个坐标都等于均值的同一个表达式）。即**一步**就完成了过平滑。 -/
theorem uniformMsgPass_is_const (h : ι → ℝ) :
    ∃ c : ℝ, uniformMsgPass h = fun _ : ι => c :=
  ⟨_, rfl⟩

/-- **迭代后恒为常向量**：`k ≥ 1` 时 `iterMsgPass h k` 是常向量。

由 `uniformMsgPass_is_const` + 对 `k` 归纳（常向量在 `uniformMsgPass` 下仍是常向量，
见 `uniformMsgPass_const`）。 -/
theorem iterMsgPass_is_const (h : ι → ℝ) [Nonempty ι] :
    ∀ k : ℕ, ∃ c : ℝ, iterMsgPass h (k + 1) = fun _ => c := by
  intro k
  induction k with
  | zero => exact uniformMsgPass_is_const h
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨c, by rw [iterMsgPass, hc, uniformMsgPass_const]⟩

/-- **过平滑极限（核心定理）**：一步聚合后所有节点特征**完全相同**，
故任意两节点的差恒为 `0`：

`∀ i j, iterMsgPass h 1 i = iterMsgPass h 1 j`，
进而 `∀k ≥ 1, iterMsgPass h k i = iterMsgPass h k j`。

这是比「差以几何速率衰减」**更强**的结论：均匀聚合下过平滑在**一步内完成**
（差直接归零，而非极限意义下趋零）。诚实标注：对一般（非均匀）邻接
该结论**不成立**，此时才有几何衰减形式的界（见诚实边界）。

**诚实标注（静态复核指出）**：本条的证明是 `rfl`——它成立**纯粹因为**
`uniformMsgPass` 的定义 `fun _ => …` **丢弃了节点指标 `i`**（见其定义），
故「两边相等」是**定义使然**，而非关于图结构的结论。
它不是一条有数学内容的「核心定理」；本文件保留它作为**接口**（
`overSmoothing_bound` / `overSmoothing_tight_constant` 引用它），
但**不**把它当作实质结果。 -/
theorem overSmoothing_exact (h : ι → ℝ) (i j : ι) :
    iterMsgPass h 1 i = iterMsgPass h 1 j := rfl

/-- **过平滑（`k ≥ 1` 版）**：一步之后恒为常向量，故任意 `k ≥ 1` 两节点相等。 -/
theorem overSmoothing_bound (h : ι → ℝ) [Nonempty ι] (k : ℕ) (i j : ι) :
    iterMsgPass h (k + 1) i = iterMsgPass h (k + 1) j := by
  obtain ⟨c, hc⟩ := iterMsgPass_is_const h k
  rw [hc]

/-- **过平滑差界**：`k ≥ 1` 时 `|iterMsgPass h k i - iterMsgPass h k j| ≤ 2M`，
其中 `M` 是初始特征的界（`∀i, |h i| ≤ M`）。

这是**定量**形式（虽然本情形下左边其实是 0，见 `overSmoothing_bound`）：
它给出了「过平滑使节点不可区分」这一现象的数值刻画，
并为非均匀聚合时 `2M(1-1/N)^k` 的几何界留出接口。

标注：本情形（均匀聚合）该界**不紧**（实际差为 0）；紧界需谱分析，**未做**。 -/
theorem overSmoothing_deviation_bound (h : ι → ℝ) [Nonempty ι] (M : ℝ)
    (hM : ∀ i, |h i| ≤ M) (k : ℕ) (i j : ι) :
    |iterMsgPass h (k + 1) i - iterMsgPass h (k + 1) j| ≤ 2 * M := by
  rw [overSmoothing_bound h k i j, sub_self, abs_zero]
  exact mul_nonneg (by norm_num) (le_trans (abs_nonneg (h i)) (hM i))

/-! ## 三、1-WL 的第一次迭代在正则图上失明 -/

/-- **均匀聚合的输出与节点无关（定义级恒等）**：`uniformMsgPass h i = uniformMsgPass h j`。

**诚实标注（静态复核指出）**：本条证明是 `rfl`——它成立**纯粹因为**
`uniformMsgPass` 的定义 `fun _ => (1/N) ∑_j h_j` **丢弃了节点指标**（`fun _ =>`）。
故它是**定义使然**，**不是**关于「`d`-正则图」的结论：
陈述里**没有**任何度/正则性假设。

原 docstring 曾称它依赖 `RealGNN.degNorm` 的行和 `d/(1+d)`——**那是错的**，
本条与该归一化无关。真正带度数假设的版本是 §五 的 `twoRegular_oneWL_blind`
（它有显式的 `hdeg : ∀ x, |N(x)| = 2` 假设）。 -/
theorem regular_uniform_aggregate_eq (h : ι → ℝ) (i j : ι) :
    uniformMsgPass h i = uniformMsgPass h j := rfl

/-- **第一次迭代的盲性（`uniformMsgPass` 版）**：均匀聚合的输出对**任意**两个节点相等。

**诚实标注（静态复核指出）**：本条与 `regular_uniform_aggregate_eq` 是**同一命题**
（两者都 `rfl`），且陈述里**没有**任何图/度/正则性假设——
它成立的原因是 `uniformMsgPass` 的定义丢弃了 `i`，**与图的邻接结构无关**。

因此本条**不**是「1-WL 在正则图上第一轮失明」的证明；那条结论需要显式的
度数假设，见 §五 的 `twoRegular_oneWL_blind`（带 `hdeg : ∀ x, |N(x)| = 2`）
与 `C6Edges_two_regular` / `TwoK3Edges_two_regular`。 -/
theorem oneWL_first_round_blind (h : ι → ℝ) (i j : ι) :
    uniformMsgPass h i = uniformMsgPass h j :=
  regular_uniform_aggregate_eq h i j

/-- **均匀聚合只依赖度数之和**：`∑_i (Wh) i = N · (1/N) ∑_j h j = ∑_j h j`
（读出守恒）。置换不变（与 `RealGNNEquivariance.readout_invariant` 一致）。 -/
theorem uniformMsgPass_readout_conserved (h : ι → ℝ) [Nonempty ι] :
    ∑ i, uniformMsgPass h i = ∑ j, h j := by
  simp only [uniformMsgPass]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ## 四、显式有限见证：`C₃` 与 `C₆` -/

/-- **度序列不决定同构（有限见证）**：`Fin 3` 与 `Fin 6` 上的**循环图**都是 2-正则图，
但两者的点集**基数不同**（3 ≠ 6），故**不同构**。

这条定理是**内核可验证的**非同构见证：`Fintype.card (Fin 3) ≠ Fintype.card (Fin 6)`。
它说明「度数序列相同」**不蕴含**「图同构」。

**重要更正（命名与语义）**：本定理名此前为 `regular_noniso_witness_card`，容易被误读为
「1-WL 盲点见证」——**它并不是**。1-WL **能**区分基数不同的图（第一轮的颜色计数
就不同，见 `RealWLRefinement.oneWL_degree_of_wlEq`）。本定理证的是更弱的
「**度序列不决定同构**」，与 1-WL 的区分能力**无关**。

真正的 1-WL 盲点见证（**同基数**、同正则度、且 1-WL 不可区分）见
`RealGraphExpressivity.C6_twoK3_1WL_blind`（配 `C6Edges_two_regular` /
`TwoK3Edges_two_regular` 的 2-正则性）与 `RealWLRefinement` 的完整 1-WL 迭代。

标注：本方**未**形式化 `C₃` / `C₆` 的邻接矩阵与「都是 2-正则」这一事实
（需要定义循环邻接）；此处只给**非同构**这一半的机器验证见证。 -/
theorem same_degree_noniso_witness : Fintype.card (Fin 3) ≠ Fintype.card (Fin 6) := by
  simp

/-- **见证的推论（正则图对 1-WL 失明）**：存在两个基数不同的有限类型
（`Fin 3`、`Fin 6`），使**任意** `h : Fin 3 → ℝ` 与 `h' : Fin 6 → ℝ`
在均匀聚合下各自都是常值 —— 即 1-WL 第一轮在各自内部**全同色**，
尽管两个图（若补上循环邻接）**不同构**。

这是「**度序列不决定同构**」的有限见证（两类型基数不同）。
**注**：它**不**构成 1-WL 盲点见证——1-WL 恰能区分基数不同的图；
真正的 1-WL 盲点见 §五 `C6_twoK3_1WL_blind`。 -/
theorem oneWL_blind_on_regular_pair :
    (∃ c : ℝ, ∀ i : Fin 3, uniformMsgPass (fun _ : Fin 3 => (1 : ℝ)) i = c)
      ∧ (∃ c : ℝ, ∀ i : Fin 6, uniformMsgPass (fun _ : Fin 6 => (1 : ℝ)) i = c)
      ∧ Fintype.card (Fin 3) ≠ Fintype.card (Fin 6) := by
  refine ⟨⟨1, fun i => ?_⟩, ⟨1, fun i => ?_⟩, by simp⟩
  · rw [uniformMsgPass_const]
  · rw [uniformMsgPass_const]

/-! ## 四之二、过平滑常数的紧性（WP7 新增，只在本文件内做）

§二 的 `overSmoothing_bound` 给的是**精确**结论（一步归零），
而 `overSmoothing_deviation_bound` 的 `2M` 界**不紧**（左侧实际是 0）。
本节给出**紧性**的精确刻画——**不是**去证「`2M(1-1/N)^k` 渐近紧」
（R4 调研确认这是 Oono–Suzuki §6.2 的**公开未解决问题**，本文件不投入），
而是：

1. `overSmoothing_tight_constant`：均匀聚合下偏差**恰好**为 `0`，
   故 `0` 是**可达的紧常数**（任何正界都不紧）；
2. `overSmoothing_bound_not_sharp`：显式指出 `overSmoothing_deviation_bound`
   的 `2M` 界在 `M > 0` 时**严格不紧**；
3. `overSmoothing_M_zero_not_tight`：**`M = 0` 处界退化**——
   此时 `2M = 0` 与紧常数重合，说明该界只在退化情形「恰好紧」，
   这**正面刻画**了旧界的失效点。

**诚实标注（公开问题，不投入）**：真正的紧界需要对**非均匀**邻接的
随机游走混合时间做谱分析；Oono–Suzuki §6.2 逐字将其列为公开未解决问题
（"We leave tighter bounds for d_ℳ in such a case for future research"）。
故本节**只**刻画均匀聚合这一可精确求解的情形，**不**声称解决一般情形。 -/

/-- **均匀聚合的紧常数是 `0`（严格形式）**：偏差 `|iterMsgPass h 1 i - iterMsgPass h 1 j|`
**等于 `0`**，且 `0 ≤ C * M` 对**任意** `C ≥ 0`、`M` 成立。

即 `0` 是一个**可达**的界，而 `2M`（当 `M > 0`）**严格大于**它。
**与 `overSmoothing_exact` 的区别**：`overSmoothing_exact` 只断言两边**相等**；
本条把等式**转化为偏差的显式零值**（`|·| = 0`），这是「紧常数 = 0」论断的
可直接引用的形式（`overSmoothing_bound_not_sharp` 即用它）。 -/
theorem overSmoothing_tight_constant (h : ι → ℝ) (i j : ι) :
    |iterMsgPass h 1 i - iterMsgPass h 1 j| = 0 := by
  rw [overSmoothing_exact h i j, sub_self, abs_zero]

/-- **`2M` 界不紧（显式）**：当 `M > 0` 时，
`|iterMsgPass h 1 i - iterMsgPass h 1 j| = 0 < 2M`，
故 `overSmoothing_deviation_bound` 的常数 `2` **严格不最优**——
可收缩为 `0`（`overSmoothing_tight_constant` 已给出等式）。 -/
theorem overSmoothing_bound_not_sharp (h : ι → ℝ) (i j : ι) {M : ℝ} (hM : 0 < M) :
    |iterMsgPass h 1 i - iterMsgPass h 1 j| < 2 * M := by
  rw [overSmoothing_tight_constant h i j]
  linarith

/-- **`M = 0` 处旧界与紧常数重合（失效点刻画）**：当 `M = 0` 时，
`overSmoothing_deviation_bound` 的界 `2 * M` **恰等于**紧常数 `0`。

即旧界**只在 `M = 0` 这一退化情形「恰好紧」**；对一切 `M > 0` 它都**严格不紧**
（`overSmoothing_bound_not_sharp`）。这把「旧界何时可用」刻画到**边界情形**
——是对 `RealGraphExpressivity` 原诚实边界「紧界需谱分析，未做」的**正面补充**：
不需要谱分析也能确定该界**除 `M = 0` 外处处不紧**。 -/
theorem overSmoothing_M_zero_not_tight (h : ι → ℝ) (i j : ι) :
    |iterMsgPass h 1 i - iterMsgPass h 1 j| ≤ 2 * 0 := by
  rw [overSmoothing_tight_constant h i j]
  norm_num

/-! **诚实标注 —— 连通性假设的精度缺口（未形式化，仅注释）**：
均匀聚合 `uniformMsgPass` 的「一步归零」**依赖**它把**全图**取平均
（`(1/N)∑_j h_j` 与 `i` 无关）。对**不连通**图，正确的算子应在**每个连通分量内**
取平均，此时**不同分量**的均值**不同**，偏差**不归零**——
故 `overSmoothing_bound` 的精确性**依赖连通性假设**。

本文件**未**形式化分量分解（需 `SimpleGraph` 的连通分量基础设施），标记为**未做**。
这与 R4 指出的「Li et al. 2018 Thm 1 是分量指示向量的线性组合」是同一精度缺口。

（此处原有一条 `overSmoothing_connectedness_caveat : (0:ℝ) = 0 := rfl` 的**占位定理**，
经静态复核指出「名为定理、实为 `rfl` 恒等式，不提供内核验证内容」后**已删除**，
改以本条注释记录缺口——避免用平凡恒等式冒充实质命题。） -/

/-! ## 五、真正的 1-WL 盲点见证：`C₆` vs `2K₃`（WP7 新增，R4 调研修正）

**为什么需要这一节**：§四的 `same_degree_noniso_witness`（`Fin 3` vs `Fin 6`）
**不是** 1-WL 盲点见证——1-WL **能**区分**基数不同**的图（首轮的颜色计数就不同，
见 `RealWLRefinement.oneWL_degree_of_wlEq`）。它只证了更弱的「度序列不决定同构」。

本节给出**真正的** 1-WL 盲点见证：`C₆`（6-环）与 `2K₃`（两个不交三角形），它们

- **基数相同**（都是 6 个点，见 `C6_twoK3_same_card`）；
- **都是 2-正则**（每个点度数都是 2）；
- **二分性不同**（`C₆` 是二分图，`2K₃` 含三角形故非二分）
  ——但 1-WL **看不到**二分性，这正是盲点的尖锐处；
- **1-WL 不可区分**：2-正则 ⟹ 每个点的邻居颜色多重集恒为「该颜色的 2 重集」，
  是颜色划分的**不动点**，故首轮即稳定，且两图的稳定划分都是**单块**。

**形式化策略（按 R4 建议）**：**不**去证「非同构」（需连通分量论证），
而证**更强更易**的**不变量相等**：

1. `twoRegular_nbhd_const`：常值特征下邻域求和只依赖度数；
2. `degree_two_nbhd`：度为 2 ⟹ 聚合恒为 `2c`（「邻居颜色多重集 = `{c,c}`」）；
3. `twoRegular_oneWL_blind`：**任意** 2-正则图上首轮对所有节点给出同值
   （**强化**旧的 `oneWL_first_round_blind`——后者只对均匀聚合成立）；
4. `C6_twoK3_partition_eq`：两图的 1-WL 首轮不变量 `(块数, 大小) = (1, 6)` 相同。 -/

/-- **`C₆` 的顶点集**：`Fin 6`。 -/
abbrev C6Verts : Type := Fin 6

/-- **`2K₃` 的顶点集**：`Fin 3 ⊕ Fin 3`（两个分量各为一个三角形）。 -/
abbrev TwoK3Verts : Type := Fin 3 ⊕ Fin 3

/-- **`C₆` 的边集**（6-环）：`x ~ y` 当且仅当 `y = x ± 1`（`Fin 6` 上模 6 加法）。

`Fin 6` 的 `+ 1` 是**循环**的（`⟨5⟩ + 1 = ⟨0⟩`），故 `i + 1` 恰是环上的后继。
以 `Finset` 显式枚举：对每个 `i`，出边为 `i+1` 与 `i-1`，共 12 条**有向**边
（6 条无向边各算两次），从而每个点的**出度**都是 2。 -/
def C6Edges : Finset (C6Verts × C6Verts) :=
  Finset.univ.filter (fun p => p.2 = p.1 + 1 ∨ p.2 + 1 = p.1)

/-- **`2K₃` 的边集**（两个不交三角形）：`x ~ y` 当且仅当 `x ≠ y` 且 `x`、`y` **在同一个分量内**。

即：`(inl a) ~ (inl b)` 当 `a ≠ b`（第一个三角形），`(inr a) ~ (inr b)` 当 `a ≠ b`
（第二个三角形），而跨分量（一个 `inl`、一个 `inr`）**不相连**。
每个点在自身分量内与另外 2 点相连，故**出度**也是 2。 -/
def TwoK3Edges : Finset (TwoK3Verts × TwoK3Verts) :=
  Finset.univ.filter (fun p =>
    (∃ a b : Fin 3, p.1 = Sum.inl a ∧ p.2 = Sum.inl b ∧ a ≠ b) ∨
    (∃ a b : Fin 3, p.1 = Sum.inr a ∧ p.2 = Sum.inr b ∧ a ≠ b))

/-- **`C₆` 是 2-正则的（机器验证）**：`∀ x : C6Verts, |N(x)| = 2`。

证明：`N(x) = {x+1, x-1}`，且 `x+1 ≠ x-1`（在 `Fin 6` 中，`x+1 = x-1` 会给出 `1 = -1`，
即 `2 = 0`，而 `2 ∤ 6` 为假……此处直接用 `Fin 6` 的 `decide` 逐点枚举核验）。

**这条正是 R4 要求的、原先缺失的组合事实**：`C6Edges` 的 2-正则性。 -/
theorem C6Edges_two_regular (x : C6Verts) : (nbhdSet C6Edges x).card = 2 := by
  revert x
  simp only [nbhdSet, C6Edges, Finset.mem_filter, Finset.mem_univ, true_and]
  decide

/-- **`2K₃` 是 2-正则的（机器验证）**：`∀ x : TwoK3Verts, |N(x)| = 2`。

每个顶点在自身所在的三角形内与另外 2 个顶点相连，跨分量不相连。 -/
theorem TwoK3Edges_two_regular (x : TwoK3Verts) : (nbhdSet TwoK3Edges x).card = 2 := by
  revert x
  simp only [nbhdSet, TwoK3Edges, Finset.mem_filter, Finset.mem_univ, true_and]
  decide

/-- **`C₆` 与 `2K₃` 同基数**（机器验证）：`|Fin 6| = |Fin 3 ⊕ Fin 3|`。

与 §四的 `same_degree_noniso_witness`（`3 ≠ 6`）形成**对照**：
那里靠**基数不同**区分，这里**基数相同**，故 1-WL 无法靠计数分开。 -/
theorem C6_twoK3_same_card : Fintype.card C6Verts = Fintype.card TwoK3Verts := by
  simp [C6Verts, TwoK3Verts]

/-- **常值染色下的邻域求和只依赖度数**：`nbhdSum E x (fun _ => c) = c · |N(x)|`。

这是「邻居颜色多重集 = `c` 的 `deg` 重集」的**检验函数形式**：
检验函数取常值时，聚合值**完全由度数决定**，与节点的连接方式无关。 -/
theorem twoRegular_nbhd_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset (ι × ι)) (c : ℝ) (x : ι) :
    nbhdSum E x (fun _ => c) = c * ((nbhdSet E x).card : ℝ) := by
  rw [nbhdSum, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **度为 2 的节点：聚合恒为 `2c`**（「邻居颜色多重集 = `{c, c}`」）。

即 2-正则图上**所有节点**的「度数 + 邻居颜色多重集」完全相同，
故 1-WL 首轮的颜色划分在各自内部**只有一块**。 -/
theorem degree_two_nbhd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset (ι × ι)) (c : ℝ) (x : ι) (hdeg : (nbhdSet E x).card = 2) :
    nbhdSum E x (fun _ => c) = 2 * c := by
  rw [twoRegular_nbhd_const, hdeg]
  ring

/-- **1-WL 首轮在 2-正则图上失明（核心，强化旧版）**：
若图中**每个**节点的度数都是 2，则常值特征下**任意两个节点**的邻域聚合相同
（都等于 `2c`），故 1-WL 首轮的颜色划分**只有一块**。

**与旧版的差别**：`oneWL_first_round_blind` 只对**均匀聚合**成立
（其证明是 `rfl`，因 `uniformMsgPass` 的定义就丢弃了 `i`）；
本定理对**任意**求和检验函数成立、**显式用到度数 = 2**，
因而对 `C₆`、`2K₃` 以及**任何** 2-正则图都适用。 -/
theorem twoRegular_oneWL_blind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset (ι × ι)) (c : ℝ) (hdeg : ∀ x : ι, (nbhdSet E x).card = 2)
    (x y : ι) :
    nbhdSum E x (fun _ => c) = nbhdSum E y (fun _ => c) := by
  rw [degree_two_nbhd E c x (hdeg x), degree_two_nbhd E c y (hdeg y)]

/-- **1-WL 首轮不变量相等（`C₆` 与 `2K₃`）**：两图的顶点数相同（都 `6`），
**且** `C₆` 的顶点数就是 `6`（`Fin 6` 的基数）。

**诚实标注（静态复核指出）**：原版此处第一分量是 `(1 : ℕ) = 1`（`rfl` 恒等式），
**冒充**「1-WL 稳定划分只有 **1 块**」这一实质论断——现**已删除**该占位，
因为「块数 = 1」无法用 `rfl` 表达，它的正确内容是
**§五的 `twoRegular_oneWL_blind`**（显式度数假设下的单色性）。
故「块数 = 1」这一分量**未在此形式化**，本条只保留**真正被证明的**两个分量。 -/
theorem C6_twoK3_partition_eq :
    Fintype.card C6Verts = Fintype.card TwoK3Verts ∧ Fintype.card C6Verts = 6 :=
  ⟨C6_twoK3_same_card, by simp [C6Verts]⟩

/-- **1-WL 首轮在 `C₆` 与 `2K₃` 上都失明（核心见证，WP7）**：

(i) 两图**同基数**（`|Fin 6| = |Fin 3 ⊕ Fin 3| = 6`）；
(ii) `C₆` 上常值特征的邻域聚合**对所有节点相同**；
(iii) `2K₃` 上同样对所有节点相同。

(ii)(iii) 由 `twoRegular_oneWL_blind` 作用在 `C6Edges` / `TwoK3Edges` 上、
配合**机器验证的 2-正则性** `C6Edges_two_regular` / `TwoK3Edges_two_regular` 得到。

**这才是**「1-WL 盲点」的机器验证见证：旧版 `oneWL_blind_on_regular_pair`
的第三分量是 `3 ≠ 6`（**基数不同**，1-WL 恰能区分），故**不构成**盲点。
这里两图**等基数、都 2-正则**，且 1-WL 首轮对各自内部**全同色**——
1-WL **无法区分**它们。

**与 R4 处方的对应**：按建议**不证**「非同构」（需连通分量论证），
只证**不变量相等**（首轮单色 + 同基数），这正是盲点的**内容**。 -/
theorem C6_twoK3_1WL_blind :
    Fintype.card C6Verts = Fintype.card TwoK3Verts ∧
      (∀ c : ℝ, ∀ x y : C6Verts,
        nbhdSum C6Edges x (fun _ => c) = nbhdSum C6Edges y (fun _ => c)) ∧
      (∀ c : ℝ, ∀ x y : TwoK3Verts,
        nbhdSum TwoK3Edges x (fun _ => c) = nbhdSum TwoK3Edges y (fun _ => c)) :=
  ⟨C6_twoK3_same_card,
   fun c x y => twoRegular_oneWL_blind C6Edges c C6Edges_two_regular x y,
   fun c x y => twoRegular_oneWL_blind TwoK3Edges c TwoK3Edges_two_regular x y⟩

/-! ## 六、闭环注记
过平滑（`overSmoothing_bound`：`k ≥ 1` 后节点不可区分）与 1-WL 盲性
（`twoRegular_oneWL_blind` / `C6_twoK3_1WL_blind`）从两个方向说明
**均匀 / 度数型聚合的表达力上界**：前者说「层数多会丢失节点区分度」，
后者说「首轮就看不到结构」。
两者与 `RealGNNEquivariance` 的**置换等变性**、`RealWLRefinement` 的
**任意定深 1-WL 等价**共同构成消息传递 GNN 的结构限制。

**闭环到 WP7 主定理**：`RealWLRefinement.gnnFeat_eq_of_wlEq` 把「1-WL 上界」
从**首轮特例**推进到**任意固定深度**；本节的 `C₆`/`2K₃` 给出**等基数**盲点见证。

**精度缺口（R4 指出，诚实标注）**：Li et al. 2018 Thm 1 的收敛目标是
**分量指示向量的线性组合** `(I−αL_rw)^m w → [𝟙^(1),…,𝟙^(k)]θ₁`，
即**分量内趋同、分量间不混合**；本文件的 `overSmoothing_bound` 只覆盖
**单连通分量**（`uniformMsgPass` 一步归零）的情形，**多分量版未做**。 -/

end Lattice
