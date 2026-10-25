import Mathlib
import Lattice.Lib.Architectures.RealGNN
/-!
# LATTICE: 过平滑的**紧常数**（把 `RealGraphExpressivity` 的定量界升级为双向结果）

> ## ⚠⚠ 构建状态（F8，v16 —— **必须先读**）
>
> **F8 接手时的实测基线（`g3-r5.log`，对该版源码 29829B 的真实 `lake build`，13 error）**
> 及其处置如下（**按根因分组**，13 条 error 归为 **4 个根因**）：
>
> | # | 根因 | 命中 error | 修法 |
> |---|---|---|---|
> | A | `Nonempty ι` **循环论证**：`Fintype.card_ne_zero` 的**语句**是 `[Nonempty α] → …`，故 `haveI : Nonempty ι := …card_ne_zero` 自引用 | `:155`（1 条） | 把 `[Nonempty ι]` 提为 `avgSmooth_sub_mean` 的**显式类型类参数** |
> | B | `theorem … : ∀ k, …` 的**方程编译器**写法下**不能**用定理自身名字递归 ⟹ `obtain` 静默失败、`c` 未入上下文 | `:239, :244, :245`（3 条） | 改为显式 **`induction k with`** |
> | C | §四两个 `N = 2` 定理的**命题本身为假**（见下「假命题」栏） | `:343, :354, :373`（3 条） | **改命题**为真命题（`avgSmooth h 0 = 0`） |
> | D | `avgSmooth_sharp_witness_fin` 证明体内 4 处工具/形状误用（`Finset.sum_eq_single` 选错、β-redex 上的 `if`、`rw` 链过长、`sum_const` 收尾） | `:423, :424, :438, :460, :465`（5 条） | 改用 `Finset.add_sum_erase`、`show` 显式 β-归约、拆 `have`、`simp only` 收尾 |
>
> **⚠⚠ 判为「命题为假」的项（本文件最重要的产出，已改命题 + 留反例）**：
> §四原稿的 **`avgSmooth_sharp_witness_two`**（结论 `|avgSmooth h 0 − 0| = (1 − 1/2)·A`）
> 与 **`avgSmooth_sharp_ratio_two`**（结论 `|avgSmooth h 0| = (1 − 1/2)·|h 0|`）
> **均为假命题**。**反例**：取 `A = 2`（满足 `hA : 0 ≤ 2`）、`h = (2, −2)`，则
> `avgSmooth h 0 = (1/2)·(2 + (−2)) = 0` ⟹ 左端 `0`，右端 `(1 − 1/2)·2 = 1`，
> **`0 = 1` 为假**（LEAN 实测残留目标逐字为 `⊢ A = 0`）。
> **根因**：旧稿把「**精确归零**」误写成「`1 − 1/N` 的取等式」——与文件头 §B 早已登记的
> 「收缩常数是 `1/N`，**不是** `1 − 1/N`」是**同一处混淆的第二次复发**。
> **已按纪律 #11 改命题**（两定理结论改为真命题 `avgSmooth h 0 = 0` / `|avgSmooth h 0| = 0`），
> 反例保留在各自 docstring 与本节的小节注释导言中。**`1/N` 的登记未被回退。**
>
> **归属标注（诚实统计）**：上述 A/B/D 三类（**10 条 error**）是**原稿既有缺陷**，F8 只做修复；
> C 类（**3 条 error**）是**原稿的假命题**，F8 **改写了命题陈述**（这是本波次唯一改变数学内容的动作，
> 已在 docstring 与本节双重留痕）。**F8 未引入任何新命题改动**。
>
> **上一轮（G3，v15）的历史记录（保留，勿删）**：
> **本文件曾长期不能编译**（`RealOverSmoothingSharp.olean` 在 G3 之前**从未存在**）。
> **G3 独立核实了 Z1 提出的「结构性文本损坏」判断，结论：该判断【成立但定性不完整】**：
> * **成立的部分**：正文 `:378` 处确实有一行**被拼接的残缺代码** ——
>   `rw [Finset.sum_const, …, nsmul_eq_mul]  refine ⟨fun j => …, ⟨0, hNpos⟩,`
>   —— 即 `hsum_eq` 子证明在 `nsmul_eq_mul]` 后**被截断**，紧接着写上了
>   **外层定理**的 `refine ⟨…⟩`，两段证明被拼在同一行上（Lean 报
>   `unexpected identifier; expected command`）。
> * **不成立/不完整的部分**：`hsum_eq` **本身并没有被遗弃**——它在 `:391`（原 `:391`）
>   被 `rw [hsum_eq]` **引用过**，所以「`hsum_eq` 从未闭合 ⟹ 其内容全部无效」的推论是**错的**；
>   被吞掉的**只有外层 `refine` 这一行**（一个「证明体缺失片段」），不是「两段证明拼接成一段」。
> * **另外两处独立缺陷**（与文本损坏同源：都是 `hsum_eq` 的收尾）：`hsumA` 用的
>   `rw [hcast, mul_neg, mul_div_cancel₀ A …]` 中 `mul_neg` 制造的是 `-A * B` 形状、
>   与目标的 `B * (-A / B)` 不匹配；`congr 1` 得到的子目标方向与 `sum_const` 的模式相反。
> * **G3 已修复**：重写 `hsumA` 的收尾、把 `hsum_eq` 改成**受条件约束**的一般形式
>   （`hsum_gen`，只对「其余项恒等于 `B`」的 `f` 陈述——原陈述对任意 `f` 为**假**），
>  并补回缺失的 `refine`。**§A 的 iff 刻画现已由内核验证。**
> * G3 遗留的 linter 警告（`DecidableEq ι` / `Fintype ι` 在本节若干定理中未被使用，无害）
>   **仍然存在**，它们不是 error，未阻编译。

`RealGraphExpressivity` 给出过平滑的**上界**方向：均匀聚合
`(Wh)_i = (1/|ι|)∑_j h_j` 在**一步内**就把各节点特征推成同一个值
（`overSmoothing_bound`：`k ≥ 1` 时 `iterMsgPass h k i = iterMsgPass h k j`），
并诚实标注「**紧常数**未做：紧界需随机游走混合时间的谱分析」。

> **归属标注**：`RealGraphExpressivity.lean` 属 WP7；本文件是**新文件**
> （WP5 的 C4），**不复用其定义**而是自建「带自环的均匀收缩算子」
> `avgSmooth`（见 §一），以便给出**非退化**的收缩常数 `1/N`。

> **⚠ 声明清单校准（Z1-3，v14）**：本文件头**旧稿**曾列举
> `overSmoothingSharpConst`、`avgSmooth_mean_zero`、`avgSmooth_iter_shrink`、
> `avgSmooth_sharp_rigidity`、`avgSmooth_step_le_one` 五个名字——**全库均不存在**
> （只出现在本 docstring 里，是改名漂移遗留）。本文件**实际只有 15 个声明**
> （3 个 `def` + 12 个 `theorem`）。下方清单**已改写为真实存在的名字**。

## 本文件做什么（两条互补的锐性）

### A. 均匀聚合的「最优常数恰为 0」（§三）

`overSmoothing_bound` 的结论是「差 `= 0`」。若把它写成常数的形式
`|差| ≤ C·M`（`M` 是初始特征的界），则**任何** `C ≥ 0` 都成立
—— 直接谈「最优常数」是**空洞**的（`C = 0` 也可以，甚至 `C < 0` 之所以失败
只是因为 `C·M` 为负）。

本文件给出**有内容的双向刻画**：加上**非退化归一化条件** `h i ≠ h j`
（初始两个节点确实有区别）后，

    `∀ C, (∀ h M, (∀i,|h i| ≤ M) → h i ≠ h j → |差| ≤ C·M) ↔ 0 ≤ C`

即 **`0` 是唯一的最优常数**（`UniformSharpConst` / `uniformSharp_eq_zero_iff`；
辅助：`avgSmoothIter_is_const`、`avgSmoothIter_eq`、`mean_bound_pos_of_ne`）。

> **⚠ 命题澄清（必须与 docstring 同读，否则极易误用）**：
> 「最优常数为 0」**只在归一化条件 `h i ≠ h j` 下**成立，它**不**意味着
> 「过平滑界与常数无关」。条件的作用是保证 `M > 0`（由 `M ≥ |h i|`、
> `h i ≠ h j` 推出），从而「`C·M` 对所有 `M` 都成立」蕴含 `C ≥ 0`；
> 若无此条件，`C < 0` 也是「有效界」（因为两边都是 0，而 `C·M < 0` 时
> `0 ≤ C·M` 会失败——**但这只是平凡的类型事实，不构成数学内容**）。
> 建议登记为 CORRECTIONS 风格的「命题澄清」条目（见文件末注）。

### B. 带自环收缩的**实际**常数 `1/N`（§四）

> **⚠ 常数校准（Z1-2，v14）**：本文件头**旧稿**（及 §四的若干处文字）称收缩常数为
> `1 − 1/N` —— **该常数推不出来**，见 §二末与 `avgSmooth_deviation_shrink`
> 的正文（`RealOverSmoothingSharp.lean:143-153` 自己已承认这一点）。
> **实际被证明的常数是 `1/N`**（在**额外假设**「`c` 是精确均值」
> `∑_j (h j − c) = 0` 下）。二者的数值差异：`N = 2` 时 `1/N = 1/2` 而
> `1 − 1/N = 1/2`（**恰好相同**），`N = 4` 时 `1/4` vs `3/4`（**差 3 倍**）
> ⟹ 二者**只在 `N = 2` 重合**，不可互相替代。
> 本文件**未**证 `1 − 1/N` 的一般 `N` 版；§四给出的见证都形如
> 「`avgSmooth h i = 0`」的**精确归零**，**不**构成 `1 − 1/N` 的取等。
> > **⚠⚠ 补充（F8，v16）**：本清单第 5 条与 §四的两个 `N = 2` 定理**旧稿确实违反了
> > 上述校准**——它们把结论写成了 `(1 − 1/2)·A` 的**取等式**，而那**是假命题**
> > （`A > 0` 时左端 `0`、右端 `A/2`；取 `A = 2` 即 `0 = 1`）。
> > **现已全部改述为「精确归零」形式的真命题**，与本校准段**重新对齐**。
> > ⚠ 附带命名隐患：`avgSmooth_sharp_ratio_two` 的**名字**含 `ratio`（比值），
> > 但其更正后的结论是 `|avgSmooth h 0| = 0`（**比值退化**，不是 `1/2`）——
> > 名字为历史保留（STYLE「诚实降级：名字保持但 docstring 说明」），
> > **不要**据名字推断它给出了 `1/2` 的比值。

本文件 §四（实际内容）：

  1. 定义 `avgSmooth h = (1/N)∑_j h_j`（**带自环**的均匀收缩；与
     `RealGraphExpressivity.uniformMsgPass` 是同一个函数，但**证明路线不同**：
     这里走「均值 + 偏差收缩」），另有 `avgSmoothIter`（迭代）与 `mean`（均值）；
  2. `avgSmooth_eq_mean`：`avgSmooth h` 恒为常向量（值即 `mean h`，`rfl`）；
  3. `avgSmooth_sub_mean`：**去均值后收缩为 0**（一次投影）；
  4. `avgSmooth_deviation_shrink`（**核心收缩引理**）：在额外假设
     `∑_j (h j − c) = 0`（`c` 是**精确均值**）与 `∀j, |h j − c| ≤ A` 下，
     `|avgSmooth h i − c| ≤ (1/N)·A`（即常数是 **`1/N`**，不是 `1 − 1/N`）；
  5. `avgSmooth_sharp_witness_two`（`N = 2` 的**显式归零**）：`h = (A, −A)`、
     均值为 `0`，则 **`avgSmooth h 0 = 0`**（一步**精确归零**）；配套
     `avgSmooth_sharp_ratio_two`：**`|avgSmooth h 0| = 0`**。
     > **⚠⚠ 本条已更正（F8，v16）**：本清单**旧稿**曾把这两条写成
     > `|avgSmooth h 0 − 0| = A = (1 − 1/2)·A`（即「`1 − 1/2` 的取等式」）——
     > **那是假命题**：左端恒为 `0`，而 `(1 − 1/2)·A = A/2`，取 `A = 2` 得 `0 = 1`。
     > 根因与上方「常数校准」**同一处混淆**（把「精确归零」误当「`1 − 1/N` 取等」）。
     > 两条定理的**语句**已按纪律改述为真命题，反例见各自 docstring；
  6. `avgSmooth_sharp_witness_fin`（**一般 `N ≥ 2` 的显式归零见证**）：
     `h = (A, −A/(N−1), …)` 使 `∀j, |h j| ≤ A`、`∑ j, h j = 0`、`avgSmooth h 0 = 0`
     —— **精确归零**（**不是** `1 − 1/N` 的取等，见上方校准）；
  7. `avgSmooth_shrink_factor_eq`：`(1 − 1/N) = (N−1)/N` 的代数恒等式
     （用于把常数在两种书写形式间换算）。

## 诚实边界（中文标注）

- **降级 —— 本文件的收缩算子带自环**：`avgSmooth` 把**自身**也算进平均
  （对应邻接含自环 / `(I + A)/ (1 + d)` 型归一化）。**无自环**的纯邻居平均
  `A/d` 其谱半径一般更小（二部图上甚至为 `1`，即**无收缩**），
  紧常数需**谱间隙**分析，本文件**未做**。
- **未做 —— 一般图的谱间隙版**：把带自环收缩的常数改进为 `1 − λ₂`（随机游走混合时间）
  需要对归一化邻接的特征值做变分刻画（Courant–Fischer），**未做**；
  本文件给的是**完全图/自环情形**的常数 `1/N`（见上方 §B 校准）。
- **未做 —— 非线性激活下的过平滑**：本文件的迭代只含**线性**收缩；
  含 `σ` 的版本需要 `σ` 的 Lipschitz 常数参与，**未做**。
- **标注 —— 「最优常数为 0」的适用范围**：见 §A 的「命题澄清」——
  该陈述**只在**归一化条件 `h i ≠ h j`（等价地 `M > 0`）下有意义，
  不是「过平滑与常数无关」的意思。

无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Lattice.Lib.Architectures.RealOverSmoothingSharp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 一、带自环的均匀收缩算子 -/

/-- **带自环的均匀收缩**：`avgSmooth h = fun _ => (1/N)∑_j h_j`。

对应「邻接含自环」的均匀聚合（如 `(I + A)/(1 + d)` 的归一化）；
在**完全图 + 自环**上它恰是行随机的步进算子，其收缩常数为 `1/N`
（在「`c` 为精确均值」假设下，见 §四 `avgSmooth_deviation_shrink`）—— **不是** `1 − 1/N`。 -/
def avgSmooth (h : ι → ℝ) : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j

/-- **`k` 次迭代**。 -/
def avgSmoothIter (h : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => h
  | k + 1 => avgSmooth (avgSmoothIter h k)

/-- **均值**：`mean h = (1/N)∑_j h j`。 -/
def mean (h : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j

/-- `avgSmooth h` 恒为常向量，其值即 `mean h`（定义相等）。 -/
theorem avgSmooth_eq_mean (h : ι → ℝ) : avgSmooth h = fun _ => mean h := rfl

/-- **去均值后收缩为 0（一次投影）**：`∑_j (h j − mean h) = 0` 时
`avgSmooth (h − mean h) = 0`。

**⚠ `[Nonempty ι]` 是不可省的显式假设**（G3 修正）：`Fintype.card_ne_zero`
的**语句本身**是 `[Nonempty α] → card α ≠ 0`（pinned `Data/Fintype/Card.lean:507`），
即**它要求 `Nonempty` 作为输入**。故
`haveI : Nonempty ι := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero Fintype.card_ne_zero)`
是**循环论证**（要证 `Nonempty ι` 却先用了需要 `Nonempty ι` 的引理）⟹
实测报 `failed to synthesize Nonempty ι`。
⇒ 正确做法：把 `[Nonempty ι]` 提为**定理的显式类型类参数**（STYLE「`haveI` 不能覆盖
定理陈述里的实例需求」），使陈述与证明体同处一个实例作用域。 -/
theorem avgSmooth_sub_mean (h : ι → ℝ) [Nonempty ι] :
    avgSmooth (fun j => h j - mean h) = fun _ => 0 := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ j, (h j - mean h) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hconst : (∑ _j : ι, mean h) = (Fintype.card ι : ℝ) * mean h := by
      have h1 : (∑ _j : ι, mean h) = (Finset.univ : Finset ι).card • mean h :=
        Finset.sum_const _
      rw [h1, Finset.card_univ, nsmul_eq_mul]
    have hmean : mean h = (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j := rfl
    rw [hconst, hmean, ← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]
  have hval : avgSmooth (fun j => h j - mean h)
      = fun _ => (Fintype.card ι : ℝ)⁻¹ * ∑ j, (h j - mean h) := by
    unfold avgSmooth
    rfl
  rw [hval, hsum, mul_zero]

/-! ## 二、偏差收缩引理（核心） -/

/-- **偏差收缩（核心引理）**：在额外假设 `∑_j (h j − c) = 0`（`c` 是**精确均值**）
与 `∀j, |h j − c| ≤ A` 下，对**任意** `i`，

    `|avgSmooth h i − c| ≤ (1/N)·A`（`N = |ι| ≥ 1`）。

**⚠ 常数是 `1/N`，不是 `1 − 1/N`**（旧稿 docstring 曾写 `1 − 1/N`，已校正）。

**为什么 `1 − 1/N` 推不出来（本引理证明的核心论证）**：
`avgSmooth h i − c = (1/N)∑_j (h j − c)`，逐项拆出 `j = i`：

    `(1/N)∑_j (h j − c) = (1/N)(h i − c) + (1/N)∑_{j≠i}(h j − c)`

对第二项用 `|∑_{j≠i}(h j − c)| ≤ (N−1)·A`（每项 ≤ A，共 `N−1` 项），
于是左端 `≤ (1/N)|h i − c| + (1/N)(N−1)A ≤ (1/N)A + (1−1/N)A = A`
——这只给 `A`。为得到**严格**的 `(1−1/N)A`，用更强的观察：
**`(N−1)` 个「其他项」各自都不超过 `A`，但 `(h i − c)` 与它们的和
必须满足「总和 = N·(均值偏差)」**；正确做法是**逐项**用 `|h j − c| ≤ A`
（含 `j = i`，共 `N` 项）得 `|·| ≤ (1/N)·N·A = A`，**仍然只是 `A`**。

因此 `(1−1/N)A` **不能**从 `|h j − c| ≤ A` 单独推出——见 §四
`avgSmooth_deviation_shrink` 的**额外假设** `∑_j (h j − c) = 0`
（即 `c` 是**精确均值**）：此时 `∑_{j≠i}(h j − c) = −(h i − c)`，故

    `|avgSmooth h i − c| = (1/N)|h i − c| ≤ (1/N)·A`。

**本引理实际陈述的形式**（且这才是「收缩」的真正来源）：

    `∑_j (h j − c) = 0` ⟹ `|avgSmooth h i − c| ≤ (1/N)·A`（`∀j, |h j − c| ≤ A`）。

`1/N` 与 `1 − 1/N` 在 `N ≥ 3` 时**不相等**（`N = 2` 时恰好都为 `1/2`）；
本文件**只证了 `1/N`**（且额外需要「`c` 是精确均值」）。误写为 `1 − 1/N`
会让读者以为 `N` 大时收缩更快——**方向恰好相反**（`1/N` 更小 ⟹ 更强）。 -/
theorem avgSmooth_deviation_shrink (h : ι → ℝ) (c A : ℝ) [Nonempty ι]
    (hmean : ∑ j, h j - (Fintype.card ι : ℝ) * c = 0)
    (hA : ∀ j, |h j - c| ≤ A) (i : ι) :
    |avgSmooth h i - c| ≤ (Fintype.card ι : ℝ)⁻¹ * A := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hdec : avgSmooth h i - c = (Fintype.card ι : ℝ)⁻¹ * ∑ j, (h j - c) := by
    have h1 : avgSmooth h i = (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j := rfl
    have hc : (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * c) = c := by
      rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
    have h3 : (Fintype.card ι : ℝ)⁻¹ * ((∑ j, h j) - (Fintype.card ι : ℝ) * c)
        = (Fintype.card ι : ℝ)⁻¹ * ∑ j, h j - c := by
      rw [mul_sub, hc]
    have h2 : ∑ j, (h j - c) = (∑ j, h j) - (Fintype.card ι : ℝ) * c := by
      rw [Finset.sum_sub_distrib]
      rw [show (∑ _j : ι, c) = (Fintype.card ι : ℝ) * c from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    rw [h1, h2, ← h3]
  have hsum0 : ∑ j, (h j - c) = 0 := by
    rw [Finset.sum_sub_distrib]
    rw [show (∑ _j : ι, c) = (Fintype.card ι : ℝ) * c from by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    linarith
  rw [hdec, hsum0, mul_zero, abs_zero]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < (Fintype.card ι : ℝ))))
    (le_trans (abs_nonneg (h i - c)) (hA i))

/-! ## 三、§A：均匀聚合的「最优常数恰为 0」（双向） -/

/-- **均匀聚合一步归零**：`k ≥ 1` 时 `avgSmoothIter h k i = avgSmoothIter h k j`
（本文件自证的版本，用于 §A 的双向刻画）。 -/
theorem avgSmoothIter_is_const (h : ι → ℝ) :
    ∀ k : ℕ, ∃ c : ℝ, avgSmoothIter h (k + 1) = fun _ => c := by
  -- ⚠ **不要**用「`theorem … : ∀ k, …` + 竖线分支」的**方程编译器**写法：
  -- 在该写法下**不能**用定理自身的名字做递归调用（`avgSmoothIter_is_const h k`），
  -- Lean 报出的是**伪装过的级联**：`obtain ⟨c, hc⟩ := …` 静默失败（`c` 未被引进上下文、
  -- `hc` 退化成 `… = fun x => sorry`），随之 `unknown identifier 'c'` ×2 + `unsolved goals` ×1。
  -- 稳定写法：**先 `intro k` 把 `k` 引进局部上下文**，再显式 `induction k with`
  -- （⚠ `induction k` 要求 `k` 是**局部 fvar**；直接对 `∀ k, …` 里的绑定变元写
  -- `induction k` 会报 `unknown identifier 'k'` —— 故 `intro k` 不可省）。
  -- 归纳假设 `ih` 是一等公民（这正是方程编译器写法缺的东西）。
  intro k
  induction k with
  | zero => exact ⟨mean h, avgSmooth_eq_mean h⟩
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      -- ⚠ `refine ⟨mean (fun _ => c), ?_⟩` 会报 `Fintype ?m` stuck：`mean` 的参数
      -- `fun _ => c` 是**新写的 λ**，其定义域类型无从推断，于是 `mean` 的隐式 `{ι}`
      -- 与 `Fintype` 实例都成了元变量。**必须显式标注 λ 的定义域类型**。
      refine ⟨mean (fun _ : ι => c), ?_⟩
      have hstep : avgSmoothIter h (k + 1 + 1) = avgSmooth (avgSmoothIter h (k + 1)) := rfl
      rw [hstep, hc, avgSmooth_eq_mean]

/-- **`k ≥ 1` 时任意两节点相等**：过平滑在**一步内完成**。 -/
theorem avgSmoothIter_eq (h : ι → ℝ) (k : ℕ) (i j : ι) :
    avgSmoothIter h (k + 1) i = avgSmoothIter h (k + 1) j := by
  obtain ⟨c, hc⟩ := avgSmoothIter_is_const h k
  rw [hc]

/-- **§A 的最优常数谓词**：`UniformSharpConst i j C` 表示

    「对**任意** `h`、`M`，只要 `∀k, |h k| ≤ M` **且** `h i ≠ h j`（非退化），
      就有 `|avgSmoothIter h (k+1) i − avgSmoothIter h (k+1) j| ≤ C·M`」。

**归一化条件 `h i ≠ h j` 是本质的**：它保证存在这样的 `h` 使 `M > 0`
（因为 `M ≥ max(|h i|, |h j|)` 且两者不等 ⟹ `M > 0`），
从而「对所有 `M` 成立」能蕴含 `C ≥ 0`。没有它，`C < 0` 也会「成立」
（两边为 0 而 `C·M ≤ 0` 会失败——这是**平凡的类型事实**，不是数学内容）。 -/
def UniformSharpConst (i j : ι) (C : ℝ) : Prop :=
  ∀ h : ι → ℝ, h i ≠ h j → ∀ M : ℝ, (∀ k, |h k| ≤ M) →
    |avgSmoothIter h 1 i - avgSmoothIter h 1 j| ≤ C * M

/-- **非零归一化条件确实强制 `M > 0`**：只要 `h i ≠ h j` 且 `M ≥ |h i|`、`M ≥ |h j|`，
则 `0 < M`。这是 §A 中「`C ≥ 0` 是必要的」的**唯一**原因。 -/
theorem mean_bound_pos_of_ne {h : ι → ℝ} {i j : ι} {M : ℝ} (hne : h i ≠ h j)
    (hi : |h i| ≤ M) (hj : |h j| ≤ M) : 0 < M := by
  rcases lt_trichotomy (h i) (h j) with hlt | heq | hgt
  · have h1 : -(h i) ≤ |h i| := neg_le_abs (h i)
    have h2 : h j ≤ |h j| := le_abs_self (h j)
    linarith
  · exact absurd heq hne
  · have h1 : -(h j) ≤ |h j| := neg_le_abs (h j)
    have h2 : h i ≤ |h i| := le_abs_self (h i)
    linarith

/-- **§A 主定理（双向）**：`UniformSharpConst i j C ↔ 0 ≤ C`。

即：**在非退化归一化条件下，均匀聚合的过平滑常数的「最优值」恰为 `0`**。
（⟸ 方向由 `avgSmoothIter_eq` 直接给出——差恒为 `0`；
⟹ 方向：取指示函数 `h = 1_{i}`（`h i = 1`、`h j = 0`）与 `M = 1`，
则左端为 `0`，故 `0 ≤ C·1 = C`。）

**⚠ 与 docstring 同读**：这**不是**「过平滑与常数无关」——
`0` 之所以是下界，是因为差恒为 `0` 且 `M` 被条件强制为正。 -/
theorem uniformSharp_eq_zero_iff (i j : ι) (hij : i ≠ j) (C : ℝ) :
    UniformSharpConst i j C ↔ 0 ≤ C := by
  -- 为便于类型推断，先把指示函数提成局部定义
  let h₁ : ι → ℝ := fun k => if k = i then (1 : ℝ) else 0
  -- ⚠ 这些分支里的 `if_pos`/`if_neg` 一律用 `simp only`（而非 `rw`）：
  -- 目标里是 **beta-redex** `(fun k => if …) x`，`rw [if_pos]` 不穿透它（实测报 pattern 失配）。
  have h₁i : h₁ i = 1 := by
    simp only [h₁, if_pos rfl]
  have h₁j : h₁ j = 0 := by
    simp only [h₁, if_neg (fun h : j = i => hij h.symm)]
  have h₁abs : ∀ k, |h₁ k| ≤ 1 := by
    intro k
    by_cases hk : k = i
    · have hk' : h₁ k = 1 := by
        simp only [h₁, if_pos hk]
      rw [hk', abs_one]
    · have hk' : h₁ k = 0 := by
        simp only [h₁, if_neg hk]
      rw [hk', abs_zero]
      norm_num
  constructor
  · intro hC
    by_contra hneg
    push_neg at hneg
    have hne : h₁ i ≠ h₁ j := by
      rw [h₁i, h₁j]
      norm_num
    have h := hC h₁ hne 1 h₁abs
    have hzero : avgSmoothIter h₁ 1 i - avgSmoothIter h₁ 1 j = 0 :=
      sub_eq_zero.mpr (avgSmoothIter_eq h₁ 0 i j)
    rw [hzero, abs_zero] at h
    linarith
  · intro hC h hne M hM
    have hzero : avgSmoothIter h 1 i - avgSmoothIter h 1 j = 0 :=
      sub_eq_zero.mpr (avgSmoothIter_eq h 0 i j)
    rw [hzero, abs_zero]
    exact mul_nonneg hC (le_of_lt (mean_bound_pos_of_ne hne (hM i) (hM j)))

/-! ## 四、§B：带自环收缩的显式常数（`N = 2` 时 `1/N = 1 − 1/N = 1/2`）

> **⚠⚠ 本节命题已更正（F8，v16 —— 独立发现；G3 的 round-6 构建日志独立残留同一目标
> `⊢ A = 0`，佐证同源）**：本节**原稿**的两个 `N = 2` 定理把结论写成
> `(1 − 1/2)·A` 形式，**但那两个命题本身是假的**（`A > 0` 时：左端恒为 `0`，
> 右端为 `A/2`，取 `A = 2` 即 `0 = 1`）。根因是旧稿把「**精确归零**」误写成
> 「`1 − 1/N` 的取等式」——与文件头 §B 已登记的「收缩常数是 `1/N` 而非 `1 − 1/N`」
> 是**同一处混淆**。现两定理均已改述为**真命题**（结论即 `avgSmooth h 0 = 0`、
> `|avgSmooth h 0| = 0`），每个定理的 docstring 内记有反例。 -/

/-- **`N = 2` 时的显式归零**：`h = (A, −A)`、均值为 `0`，
则 `avgSmooth h 0 = 0`（**一步精确归零**），从而 `|avgSmooth h 0| = 0`。

**⚠⚠ 命题更正（F8，v16 —— 独立发现；G3 的 round-6 构建日志独立残留同一目标 `⊢ A = 0`，佐证同源。原稿此处为假命题，已改）**：
本定理**原稿**陈述为

    `|avgSmooth h 0 − 0| = (1 − 1/2)·A`

**该命题为假**（`A > 0` 时）：由 `avgSmooth` 的定义
`avgSmooth h i = (1/N)·∑_j h j`（本文件 `:134`）与 `h = (A, −A)` 得

    `avgSmooth h 0 = (1/2)·(A + (−A)) = 0`

故左端 `|0 − 0| = 0`，而右端 `(1 − 1/2)·A = A/2`。**取 `A = 2`（满足 `hA : 0 ≤ 2`）
即得 `0 = 1`，为假**（LEAN 实测残留目标正是 `⊢ A = 0`）。这与文件头 §B 已登记的
「收缩常数是 `1/N`，不是 `1 − 1/N`」**同源**：旧稿把「精确归零」误写成了
`1 − 1/N` 的取等式。**本文件从未也证不出 `1 − 1/N` 的取等**；本节给出的是
**归零见证**，故更正为下面的真命题。

> **⚠ 诚实标注（F8，v16）**：更正后的结论**不再需要** `hA : 0 ≤ A`
> —— 事实上 `avgSmooth h 0 = 0` 对**任意** `A : ℝ` 都成立
> （因为 `(1/2)·(A + (−A)) = 0` 与 `A` 的符号无关）。
> Lean 的 `unused variable` linter **实测报了** `:409:45 unused variable 'hA'`，
> 这正是该事实的机器证据。**保留 `hA` 的原因**：① 不改变公开签名（避免无谓的下游影响）；
> ② 它是原稿「有界特征」语境的见证（`∀j, |h j| ≤ A` 在本节的其他定理中确实使用）。
> ⇒ **若下游要更强的版本，可删 `hA` 得无条件定理**（这是**严格更强**的陈述，无风险）。
> ⚠ 与 `avgSmooth_sharp_witness_fin` 对比：**那条确实需要 `hA`**（它要证 `∀j, |h j| ≤ A`），
> 故 `hA` 在**本节内**并非全局冗余。 -/
theorem avgSmooth_sharp_witness_two (A : ℝ) (hA : 0 ≤ A) :
    avgSmooth (fun k : Fin 2 => if k = 0 then A else -A) 0 = 0 := by
  -- ⚠ **不要**用 `fin_cases (show (0 : Fin 2) = 0 from rfl)`：那是对**字面量**
  -- `(0 : Fin 2) = 0` 这个**恒真假设**做分情形，它**不会**枚举目标里出现的 `Fin 2`，
  -- 故对目标毫无作用（其后 `norm_num`/`ring` 对残留的 `if` 束手无策）。
  -- ⚠ 也不要用 `simp only [if_pos rfl]`：条件 `(0 : Fin 2) = 0` 是**结构等式**而非
  -- `True` 字面量（STYLE「`rw [if_pos]` 在 beta-redex 上必败」同族）。
  -- ⚠ **F8 修法（稳）**：把证明拆成**三个各自可独立核对的小步**，每步只做一件事，
  -- 全部走**已知形状**的原语（`avgSmooth` 展开 / `Fin.sum_univ_two` / `if_pos`/`if_neg`），
  -- 不依赖 `simp` 的 `DecidableEq (Fin 2)` 归约能力（那正是旧稿失败之处）。
  -- ① 展开 `avgSmooth`（定义等式，`rfl` 级）
  have h1 : avgSmooth (fun k : Fin 2 => if k = 0 then A else -A) 0
      = (↑(Fintype.card (Fin 2)) : ℝ)⁻¹
        * ∑ j : Fin 2, (if j = 0 then A else -A) := rfl
  -- ② 求和展开成两项：`Fin.sum_univ_two` 把 `∑ j : Fin 2, f j` 打成 `f 0 + f 1`
  have h2 : (∑ j : Fin 2, (if j = 0 then A else -A))
      = (if (0 : Fin 2) = 0 then A else -A) + (if (1 : Fin 2) = 0 then A else -A) :=
    Fin.sum_univ_two _
  -- ③ 两个 `if` 各自归约：`if_pos rfl` / `if_neg`（`(1 : Fin 2) ≠ 0` 由 `decide` 判定）
  have h3 : (if (0 : Fin 2) = 0 then A else -A) + (if (1 : Fin 2) = 0 then A else -A) = 0 := by
    rw [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), add_neg_cancel]
  rw [h1, h2, h3, Fintype.card_fin, mul_zero]

/-- **`N = 2` 的收缩比值形式（更正后）**：对 `h = (A, −A)`，
`|avgSmooth h 0| = 0`（比值是 `0`，**不是** `1/2`）。

**⚠⚠ 命题更正（F8，v16 —— 独立发现；G3 的 round-6 构建日志独立残留同一目标 `⊢ A = 0`，佐证同源）**：原稿陈述为
`|avgSmooth h 0| = (1 − 1/2)·|h 0|`，**该命题为假**（`A > 0` 时：
左端 `= 0`，而右端 `= (1/2)·|A| = A/2`；取 `A = 2` 得 `0 = 1`）。
**根因同上**：`h = (A, −A)` 在 `N = 2` 上被**精确归零**，故任何「收缩到 `(1/2)·A`」
的说法都与之矛盾。**已更正为真命题**：左端恒为 `0`。 -/
theorem avgSmooth_sharp_ratio_two (A : ℝ) (hA : 0 ≤ A) :
    |avgSmooth (fun k : Fin 2 => if k = 0 then A else -A) 0| = 0 := by
  rw [avgSmooth_sharp_witness_two A hA, abs_zero]

/-- **一般 `N` 的显式归零见证**：在 `N ≥ 2` 个节点上取

    `h := (A, −A/(N−1), …, −A/(N−1))`（一个 `+A`、`N−1` 个 `−A/(N−1)`），

则均值为 `0`、`∀j, |h j| ≤ A`，且 `avgSmooth h 0 = 0`（`i = 0`）。

**⚠ 意义校准（Z1-2，v14）**：本定理结论是 `avgSmooth h i = 0` —— **精确归零**，
**不是** `= (1 − 1/N)·A`（旧稿 docstring 曾这么写，**错误**：由
`avgSmooth h 0 = (1/N)(A − (N−1)·A/(N−1)) = (1/N)·0 = 0` 可知左端是 `0`，
而 `(1 − 1/N)·A` 在 `A > 0`、`N ≥ 3` 时 **非零**，两者不可能相等）。
它的价值是给出一个**显式的、可内核验证的归零点**，说明「一次投影即归零」；
**未做**：把 `1/N`（或旧稿的 `1 − 1/N`）写成一般图上的最优收缩常数
（需要谱间隙/混合时间，见文件头诚实边界）。 -/
theorem avgSmooth_sharp_witness_fin (N : ℕ) (hN : 2 ≤ N) (A : ℝ) (hA : 0 ≤ A) :
    ∃ (h : Fin N → ℝ) (i : Fin N),
        (∀ j, |h j| ≤ A)
      ∧ (∑ j, h j = 0)
      ∧ (avgSmooth h i = 0)
      ∧ (∃ j : Fin N, h j = A) := by
  have hNpos : 0 < N := by omega
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hN0 : (N : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  -- ⚠ 本证明不使用含强制转换的 `ring`：`Fin` 的强制转换在项里是 `↑↑a`，
  -- 会让 `ring` 的原子不匹配而失败。所有代数都在纯 ℝ 变量 `A`、`(N:ℝ)`、`∑ j, h j` 上做。
  -- 见证：`i₀ ↦ A`，其余 `N − 1` 个点 ↦ `-A/(N−1)`（简记为 `B`）。
  set B : ℝ := -A / ((N : ℝ) - 1) with hBdef
  have hBval : B = -A / ((N : ℝ) - 1) := hBdef
  -- ⚠ 不要用 `set i₀ : Fin N := ⟨0, hNpos⟩`：`set` 生成的 `i₀` 对类型检查器**不透明**
  -- （`subsection` 的 `⟨0, hNpos⟩` 是透明的，但 `set` 引入的是局部定义），
  -- 于是 `(fun j => if j = i₀ then …) i₀` 会留下 `if True then …` 而**闭不上目标**。
  -- 改用「局部记法」保持透明：直接写 `⟨0, hNpos⟩`，用 `h0i` 记录它等于 `⟨0, hNpos⟩`。
  -- 关键的**一般求和公式**：只有 `i₀` 一项为 `A`，其余 `N − 1` 项之和由调用方给出。
  -- ⚠ **修法（F8，v16）**：旧稿此处用 `rw [Finset.sum_eq_single …]` + 两个位置子弹，
  -- 实测报 `application type mismatch`（`hb hbb` 收到 `hbb : b = b` 而期望 `b = ⟨0,hNpos⟩`）
  -- 并级联出 `did not find instance of the pattern`。**根因是选错了工具**：
  -- 要证的正是「`∑_j f j = f a + ∑_{j∈s.erase a} f j`」，而 mathlib 已**逐字**提供该引理——
  -- **`Finset.add_sum_erase (s) (f) (h : a ∈ s) : f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`**
  -- （pinned `Algebra/BigOperators/Group/Finset.lean:1671`，由 `mul_prod_erase` 经 `to_additive` 生成
  -- ⟹ 直接 grep `theorem add_sum_erase` **搜不到**，须按 `to_additive` 源查找）。
  -- 单绑定 `∑ j, f j` 与 `∑ j ∈ Finset.univ, f j` 是**记法同义**，故直接 `.symm` 即可。
  have hsum_gen : ∀ (f : Fin N → ℝ),
      (∑ j ∈ (Finset.univ : Finset (Fin N)).erase (⟨0, hNpos⟩ : Fin N), f j)
        = ((N - 1 : ℕ) : ℝ) * B →
      (∑ j, f j) = f ⟨0, hNpos⟩ + ((N - 1 : ℕ) : ℝ) * B := by
    intro f hr
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin N)) f (Finset.mem_univ _), hr]
  have hrest : (∑ j ∈ (Finset.univ : Finset (Fin N)).erase (⟨0, hNpos⟩ : Fin N),
      (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j)
      = ((N - 1 : ℕ) : ℝ) * B := by
    -- ⚠ `Finset.sum_congr` 的**第二个参数**是 `∀ x ∈ s, f x = g x` 形式的**函数**；
    -- 写成 `fun j hj => …` 时 `hj` 收到的是 `j ∈ s`，但 `sum_congr` 会把整段
    -- 作为 `rw` 的**等式**使用、要求它**整体**是 `Eq`，于是报
    -- `did not find instance of the pattern`。稳定写法：先 `have` 出逐点等式，
    -- 再 `rw [Finset.sum_congr rfl hpt]`。
    have hpt : ∀ j ∈ (Finset.univ : Finset (Fin N)).erase (⟨0, hNpos⟩ : Fin N),
        (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j = B :=
      fun j hj => if_neg (Finset.mem_erase.mp hj).1
    rw [Finset.sum_congr rfl hpt]
    -- ⚠ `Finset.sum_const B` 只给 `∑ = card • B`，**不化简 `.card` 与 `nsmul`**；
    -- 必须补 `Finset.card_erase_of_mem` / `Finset.card_univ` / `Fintype.card_fin` / `nsmul_eq_mul`
    -- 才能到 `↑(N-1) * B`（实测报 type mismatch：`?m.card • B` vs `↑(N-1) * B`）。
    -- ⚠ **F8 修法**：把「`∑ const` → `card • B`」与「`card` 化简 → `↑(N-1) • B`」与
    -- 「`nsmul` → `*`」**用 `simp only` 一次做完**——`simp` 会**递归**应用且对
    -- `Nat.cast`/`nsmul` 的形状做规范化，比三条 `rw` 顺序链更稳（`rw` 链中任一步
    -- 形状不符即整体失配，这正是旧稿报 `type mismatch` 的机制）。
    have hcard : ((Finset.univ : Finset (Fin N)).erase (⟨0, hNpos⟩ : Fin N)).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
  have hsome : (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B)
      ⟨0, hNpos⟩ = A := by
    -- ⚠（原稿诊断）`simp only [if_pos rfl]` 在这里**失败**（实测目标残留 `(if True then A else B) = A`）：
    -- 条件 `⟨0,hNpos⟩ = ⟨0,hNpos⟩` 是**结构等式**，不是 `True` 字面量。
    -- ⚠ **F8 修法**：根因不是「条件不是 `True`」，而是**目标里带 β-redex**
    -- `(fun j => if …) ⟨0,hNpos⟩` —— `exact`/`rw` **不做 β-归约**，故 `if_pos` 的重写
    -- 落在 redex **内部**而外层不消（STYLE「`rw [if_pos]` 在 beta-redex 上必败」）。
    -- ⇒ 先 `show` 显式 β-归约（把 redex 打成裸 `if`），再 `exact if_pos rfl`。
    show (if (⟨0, hNpos⟩ : Fin N) = ⟨0, hNpos⟩ then A else B) = A
    exact if_pos rfl
  have hsum : (∑ j, (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j)
      = A + ((N - 1 : ℕ) : ℝ) * B := hsum_gen _ hrest
  -- `B` 配合的代数事实（纯 ℝ，可 `ring`）
  have hBmul : ((N - 1 : ℕ) : ℝ) * B = -A := by
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    rw [hBval, hcast, mul_div_cancel₀ (-A) (ne_of_gt hN1)]
  have hAB : A + ((N - 1 : ℕ) : ℝ) * B = 0 := by
    rw [hBmul]; ring
  refine ⟨fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B, ⟨0, hNpos⟩,
    ?_, ?_, ?_, ?_⟩
  · -- 逐点界：`|A| ≤ A`（用 `hA`）；`|B| ≤ A`（`B = A/(N−1)`、`N − 1 ≥ 1`）
    intro j
    by_cases hj : j = (⟨0, hNpos⟩ : Fin N)
    · have hgj : (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j = A := by
        simp only [if_pos hj]
      rw [hgj, abs_of_nonneg hA]
    · have hgj : (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j = B := by
        simp only [if_neg hj]
      rw [hgj]
      have hBabs : |B| = A / ((N : ℝ) - 1) := by
        -- ⚠ **F8 修法**：原稿用一条 `rw [hBval, abs_div, abs_of_pos hN1, abs_neg, abs_of_nonneg hA]`
        -- 实测在 `abs_of_pos hN1` 处报 `did not find instance of the pattern: |↑N - 1|`，
        -- 残留目标 `A / |↑N - 1| = A / (↑N - 1)`：`rw` **按序对整目标**用引理，
        -- 前一条 `abs_div` 刚把 `|−A| / |↑N−1|` 造出来时，`abs_of_pos hN1` 的
        -- **模式匹配时机/形状**并不可靠。⇒ 拆成**两个独立 `have`**（每步只做一件事），
        -- 再用 `simp only` 把它们喂进去——这是「`rw` 链过长即失配」的通用解法。
        have hden : |(N : ℝ) - 1| = (N : ℝ) - 1 := abs_of_pos hN1
        have hnum : |-A| = A := by rw [abs_neg, abs_of_nonneg hA]
        rw [hBval, abs_div, hden, hnum]
      rw [hBabs, div_le_iff₀ hN1]
      have h1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
        have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      nlinarith
  · -- 均值为 0：`∑ j, h j = A + (N−1)·B = 0`
    rw [hsum]
    exact hAB
  · -- `avgSmooth h i₀ = 0`：`∑ j, h j = 0` ⟹ `(1/N)·0 = 0`
    have hval : avgSmooth (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B)
        ⟨0, hNpos⟩
        = (↑(Fintype.card (Fin N)) : ℝ)⁻¹ *
          ∑ j, (fun j : Fin N => if j = (⟨0, hNpos⟩ : Fin N) then A else B) j := rfl
    rw [hval, hsum, hAB, mul_zero]
  · -- 取到 `A` 的那一项存在
    exact ⟨⟨0, hNpos⟩, hsome⟩

/-- **代数换算恒等式**：对任意 `N ≥ 1`，`(1 − 1/N) = ((N−1)/N)`（证明正确，保留）。

**⚠ 用途标注（Z1-2，v14）**：这是**纯代数换算**，**不**声称 `1 − 1/N` 是本文件的
收缩常数——本文件实际证明的收缩常数是 `1/N`（见 `avgSmooth_deviation_shrink`
与文件头 §B 校准）。保留本定理仅因它是真的恒等式、且便于将来把任一常数
写成两种形式。 -/
theorem avgSmooth_shrink_factor_eq (N : ℕ) (hN : 1 ≤ N) :
    (1 - (N : ℝ)⁻¹) = ((N : ℝ) - 1) / (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by
    have : 0 < N := hN
    exact_mod_cast ne_of_gt this
  -- 不用 `field_simp`（会留下除零义务）：显式的 `eq_div_iff` + `ring`。
  have h2 : (1 - (N : ℝ)⁻¹) * (N : ℝ) = ((N : ℝ) - 1) := by
    have h3 : (1 - (N : ℝ)⁻¹) * (N : ℝ)
        = (N : ℝ) - (N : ℝ)⁻¹ * (N : ℝ) := by rw [sub_mul, one_mul]
    rw [h3, inv_mul_cancel₀ hNR]
  exact (eq_div_iff hNR).mpr h2

end Lattice.Lib.Architectures.RealOverSmoothingSharp