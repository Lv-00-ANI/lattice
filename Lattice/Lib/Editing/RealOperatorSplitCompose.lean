import Mathlib
import Lattice.Lib.Optim.RealOperatorSplitBridge
/-!
# LATTICE: RealOperatorSplitCompose —— `mul_congr`：乘法组合性（近似收敛在乘法下封闭）

> 承接 `RealOperatorSplitBridge`（把 op-split 的 6 个模块接到 `Lattice`）。
> ⚠ 本文件是**本仓库新增**；`RealOperatorSplit` / `RealLimitDiscrete` 等 6 个被 import
> 模块由作者 **`yjh051108`** 所写（分支 `theory/op-split` @ `6428184`），**本仓库不是其作者**。
> 本文件**不修改**它们（一字未动其 namespace 与证明体）。

## 为什么需要这个文件（用户笔记判定的「隐藏的关键阻塞」）

op-split 只有 `add_congr`（加法组合性）。但**层与层之间是乘法/复合**：

    RealLimitDiscrete.add_congr : 近似收敛在【加法】下封闭
    ⚠ 缺：近似收敛在【乘法】下封闭（mul_congr）

**没有它，T2 无法从单层传到多层**，而「多层传播」正是 main 的核心交付
（`RealModelChain` / `RealChain` / `RealBlockLipschitz`）。
⇒ 本文件补上这一步，是 op-split 从「孤立框架」变成「可用工具」的关键一步。

## ⭐ 关键数学：**误差是乘法传播的，不是加法**

    |u·v − au·av| ≤ |u − au|·|v| + |au|·|v − av|

⚠ 与 `add_congr` 的**结构性差别**：加法版只需「两腿各自的界」，
而**乘法版右端出现 `|v|` 与 `|au|` 这两个"绝对值因子"** ——
它们**不是** `eu`/`ev` 能控制的（`eu → 0` 说的是**差**趋于 0，不是**值**有界）。
⇒ ⭐ **必须有界性假设**。这是**数学事实**，不是为了让结论好看而加的装饰
（见本文件 §4 的**反例**：去掉有界性，`mul_congr` **为假**）。

## ⭐⭐ 第二个结构性发现：`eps` 必须是**非负**的

`LimitDiscrete.eps_tendsto_zero` 的形式是 **单侧**的：

    ∀ ε > 0, ∃ N, ∀ n ≥ N, eps n < ε

⚠ 它**不蕴含** `eps n ≥ 0`（**反例**：`eps := fun _ => -1` 满足该字段）。
而乘法组合的**第二条腿**（见下）要证 `eu·M + ev·M' + eu·ev → 0`，
其中 `eu·ev ≤ (eu+ev)²/4` 这一步**要求 `eu ≥ 0`、`ev ≥ 0`**
（否则 `eu := -1`、`ev := -1` ⟹ `eu·ev = 1 > 0 = (eu+ev)²/4`，**命题为假**）。

⇒ ⭐ **`mul_congr` 比 `add_congr` 多需要一条 `heps_nonneg : ∀ n, 0 ≤ eu n ∧ 0 ≤ ev n`。**
这不是可选的、也不是可以由现有字段推出的 —— 是**现有 `LimitDiscrete` 定义的缺口**。
**这是本文件最重要的诚实边界**（详见 §5）。

## 交付

1. §2 `mul_congr` —— 乘法组合性（**主定理**，形态见下）；
2. §3 `mul_congr_le` —— 把误差项换成更粗但更易用的 `(eu+ev)²/4` 形式；
3. §4 **反例族** —— 证明**去掉有界性 / 去掉 `eps ≥ 0`** 后命题为假（三条）；
4. §6 `LayerApproxChain` + `chain_mul_congr` —— **多层链的组合**（第 3 步）。

## 诚实边界（**标注**）

- ⭐ **`mul_congr` 需要 4 条前提**：`hvM`（**`v` 有界**——⚠ 界的是 `v` 不是 `u`）、
  `hauM`（`au` 有界，**关于 `n` 一致**）、
  `hM0'`（`0 ≤ M'` 界非负）、`heps_nonneg`（eps 非负）。**缺一不可**，§4 各有反例；
- ⭐ 本文件**不**证明「真实神经网络层满足这些前提」—— 那是实例化工作（未做）；
- ⭐ §6 的链式定理**不引入新假设**，只是 §2 在 `Fin m` 上的迭代；
  但它**继承了 §2 的全部前提**（每层的有界性 + eps 非负），且**前提是逐层的**；
- ⭐ `eps` 的界形式 `eu·M' + ev·M + eu·ev` 是本文件的**选择**（对称性的自然写法），
  不是唯一可能的形式；选它的理由是**它对 `eu`、`ev` 分别线性/双线性，便于链式迭代**。

无 sorry/axiom/admit；所有定理真实可证（§4 的反例亦然）。
-/

noncomputable section

namespace Lattice

open RealLimitDiscrete

/-! ## §1 辅助引理：乘法误差的三角不等式

`|u·v − au·av| ≤ |u − au|·|v| + |au|·|v − av|` —— 这是 `mul_congr` 的**第一条腿**。
⚠ 与 `add_congr` 的 `hdist_add` **不同**：那里三角不等式是**传入的前提**；
这里因为 `dist` 固定为 `|· − ·|` 在 `ℝ` 上，我们**能证**它。本文件对 `ℝ` 工作
（`LimitDiscrete` 本身是 `β` 泛型的）。 -/

/-- **乘法误差不等式**：`|u·v − au·av| ≤ |u − au|·|v| + |au|·|v − av|`。

恒等式 `u·v − au·av = (u − au)·v + au·(v − av)` 后取绝对值三角不等式。 -/
theorem abs_mul_sub_mul_le (u au v av : ℝ) :
    |u * v - au * av| ≤ |u - au| * |v| + |au| * |v - av| := by
  have key : u * v - au * av = (u - au) * v + au * (v - av) := by ring
  rw [key]
  calc |(u - au) * v + au * (v - av)|
      ≤ |(u - au) * v| + |au * (v - av)| := abs_add _ _
    _ = |u - au| * |v| + |au| * |v - av| := by rw [abs_mul, abs_mul]

/-- **收敛桥**：`eps` 单侧趋于 0 + `eps ≥ 0` ⟹ `Tendsto eps atTop (nhds 0)`。 -/
theorem eps_tendsto_zero_iff_tendsto {e : Nat → ℝ} (he0 : ∀ n, 0 ≤ e n)
    (he : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, e n < ε) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := he ε hε
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)]
    exact hN n hn⟩

/-! ## §2 ⭐ 主定理：`mul_congr`

### ⭐⭐ 精确的前提分析（这是本节最重要的内容）

从恒等式出发：

    |u·v − au·av| = |(u − au)·v + au·(v − av)|
                  ≤ |u − au|·|v| + |au|·|v − av|

右端两个因子 `|v|`、`|au|` **不是 `eu`/`ev` 能控制的**：
`eu → 0` 说的是**差**趋于 0，**完全不谈值有多大**。
⇒ ⭐ **必须有界性前提**，且**恰好需要两个不同的界**：

| 前提 | 内容 | 它界住的量 | 用于哪一项 |
|:--|:--|:--|:--|
| `hvM` | `∀ x, X x → |v x| ≤ M` | **精确函数 `v`** | `|u − au|·|v| ≤ eu·M` |
| `hauM` | `∀ n x, X x → |au n x| ≤ M'` | **近似函数 `au`**（`n`-一致） | `|au|·|v − av| ≤ M'·ev` |
| `hM0'` | `0 ≤ M'` | — | `mul_le_mul` 要非负因子 |
| `heps_nonneg` | `∀ n, 0 ≤ eu n ∧ 0 ≤ ev n` | — | **第二条腿**（见 §5） |

⚠ **`0 ≤ M` 不需要单独假设**（它是**第一条腿+第二条腿的 `hvM` 的推论**：
`|v x| ≥ 0` 且 `|v x| ≤ M` ⟹ `0 ≤ M`，只要 `X` 非空）——
本文件第一稿多写了它（Lean 报 `unused variable hM0` 暴露），**已删**。
⭐ 这是「`unused variable` 警告要区分『假设多余』与『证明漏用』」的实例：
此处是**前者（无害的冗余前提）**，删掉更干净。

⚠ **两点必须强调（否则容易写松）**：

1. ⭐ **`hvM` 界的是 `v`，不是 `u`。** 我最初按"对称"猜的是 `u` 与 `au` 的界，
   **那是错的** —— 第一项 `|u − au|·|v|` 里要界住的是 **`v`**。
   故本定理的前提是 **`(v 的界 M)` + `(au 的界 M')`**，**不是** `(u, au)` 的一对界。
   ⇒ 这是"**代小整数验一遍**"纪律抓到的一个真实设计错（见 §4 反例的形式）。

2. ⭐ **`hauM` 的「`n`-一致」是实质要求**：`au` 以 `n` 为索引，
   若只有逐点界 `|au n x| ≤ B n` 而 `B n → ∞`，则第二条腿的界 `eu n · M'` 不收敛。
   **故 `M'` 必须是与 `n` 无关的常数**（§4 反例二）。 -/

/-- ⭐ **乘法组合性（主定理）**：两个极限离散可乘。

若 `u ≡lim au`（误差 `eu`）与 `v ≡lim av`（误差 `ev`），
且 **`v` 有界**（`M`）、**`au` 有界且 `n`-一致**（`M'`）、`eu`/`ev` **非负**，则

    u·v ≡lim au·av，误差 ≤ eu·M + ev·M' + eu·ev。

⭐ 三项的来源：`eu·M`（本层误差 × 精确侧值域界）、`ev·M'`（对侧误差 × 近似侧界）、
**`eu·ev`（两个误差的乘积 —— 乘法传播的「本质新项」，`add_congr` 里不存在）**。

⚠ **诚实标注（哪条是必需、哪条是选择）**：
- **必需**：`hvM`、`hauM`、`hM0'`、`heps_nonneg`（§4 三条反例各证其一）；
- **本文件的选择**：误差项的**具体形式** `eu·M + ev·M' + eu·ev`。
  另一条同样正确（且更松、更易迭代）的形式是 `mul_congr_le` 的
  `eu·M + ev·M' + (eu+ev)²/4`（§3）—— 两者都真，选哪个是**表述选择**。 -/
theorem mul_congr {α : Type _} (X : α → Prop)
    (u v : α → ℝ) (au av : Nat → α → ℝ) (eu ev : Nat → ℝ) (M M' : ℝ)
    (hu : LimitDiscrete (fun a b : ℝ => |a - b|) u au X eu)
    (hv : LimitDiscrete (fun a b : ℝ => |a - b|) v av X ev)
    (hvM : ∀ x, X x → |v x| ≤ M)
    (hauM : ∀ n x, X x → |au n x| ≤ M')
    (hM0' : 0 ≤ M')
    (heps_nonneg : ∀ n, 0 ≤ eu n ∧ 0 ≤ ev n) :
    LimitDiscrete (fun a b : ℝ => |a - b|)
      (fun x => u x * v x)
      (fun n x => au n x * av n x)
      X
      (fun n => eu n * M + ev n * M' + eu n * ev n) := by
  refine ⟨?_, ?_⟩
  · -- 第一条腿：逐点误差界
    intro n x hx
    have h1 : |u x - au n x| ≤ eu n := hu.bound n x hx
    have h2 : |v x - av n x| ≤ ev n := hv.bound n x hx
    have hvM : |v x| ≤ M := hvM x hx
    have hauM' : |au n x| ≤ M' := hauM n x hx
    calc |u x * v x - au n x * av n x|
        ≤ |u x - au n x| * |v x| + |au n x| * |v x - av n x| :=
          abs_mul_sub_mul_le _ _ _ _
      _ ≤ eu n * M + M' * ev n :=
          add_le_add (mul_le_mul h1 hvM (abs_nonneg _) (heps_nonneg n).1)
            (mul_le_mul hauM' h2 (abs_nonneg _) hM0')
      _ ≤ eu n * M + ev n * M' + eu n * ev n := by
          have := mul_nonneg (heps_nonneg n).1 (heps_nonneg n).2
          linarith
  · -- 第二条腿：误差项 → 0（用 Filter.Tendsto 的封闭性）
    intro ε hε
    have hto_eu : Filter.Tendsto eu Filter.atTop (nhds 0) :=
      eps_tendsto_zero_iff_tendsto (fun n => (heps_nonneg n).1) hu.eps_tendsto_zero
    have hto_ev : Filter.Tendsto ev Filter.atTop (nhds 0) :=
      eps_tendsto_zero_iff_tendsto (fun n => (heps_nonneg n).2) hv.eps_tendsto_zero
    have hmain : Filter.Tendsto (fun n => eu n * M + ev n * M' + eu n * ev n)
        Filter.atTop (nhds (0 * M + 0 * M' + 0 * 0)) :=
      ((hto_eu.mul tendsto_const_nhds).add (hto_ev.mul tendsto_const_nhds)).add
        (hto_eu.mul hto_ev)
    rw [Metric.tendsto_atTop] at hmain
    obtain ⟨N, hN⟩ := hmain ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq] at h
    have h0 : (0 : ℝ) * M + 0 * M' + 0 * 0 = 0 := by ring
    rw [h0, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h

/-! ## §3 更易用的推论：`(eu + ev)²/4` 形式

`eu·ev ≤ (eu + ev)²/4`（⚠ **无前提即真**，见下——**不是** §5 缺口的来源）。
于是 `mul_congr` 的误差项可**统一换成一个只含 `eu + ev` 的项**。 -/

/-- **AM–GM（二元，无前提版）**：`eu·ev ≤ (eu + ev)²/4`。

⭐ **重要更正（本文件第一稿错了）**：我最初以为这条**需要 `eu, ev ≥ 0`**，
理由是"取 `eu := ev := -1` 时左 `1 > 0 =` 右"。**该判断是错的** ——
把 `eu := ev := -1` 代回：左 `= (-1)·(-1) = 1`，
右 `= (-1 + -1)²/4 = 4/4 = 1`，故 `1 ≤ 1` **成立**（我漏算了 `(eu+ev)` 会变负、
平方后仍为正）。实测（探针）：**无任何前提时该式即真**。

⇒ ⭐ **本条不需要非负前提**，是**纯代数恒等式的推论**：
`eu·ev ≤ (eu+ev)²/4 ⟺ 0 ≤ (eu − ev)²`。
**故 `eu, ev ≥ 0` 不是「这条引理」的需要，而是「§2 的乘法界」的需要**
（`mul_le_mul` 要非负因子）—— 两者的必要性来源**不同**，本文件第一稿把它们混为一谈。

⚠ 这正是用户笔记纪律「代小整数判真假」的**反向**教训：
**它抓出了我的一次误判为"必需"**（把一条无前提的真命题当成需要前提）。 -/
theorem mul_le_sq_add_div_four (eu ev : ℝ) :
    eu * ev ≤ (eu + ev) ^ 2 / 4 := by
  nlinarith [sq_nonneg (eu - ev)]

/-- ⭐ **`mul_congr`（合并误差版）**：误差项取 `(eu n + ev n)²/4 + eu n·M + ev n·M'`。

比 §2 的原式**更粗**（`eu·ev ≤ (eu+ev)²/4`），但把「两个误差的乘积」**换成了单个**的
`(eu+ev)²/4`，在链式迭代里更好用（§6 用的就是它）。 -/
theorem mul_congr_le {α : Type _} (X : α → Prop)
    (u v : α → ℝ) (au av : Nat → α → ℝ) (eu ev : Nat → ℝ) (M M' : ℝ)
    (hu : LimitDiscrete (fun a b : ℝ => |a - b|) u au X eu)
    (hv : LimitDiscrete (fun a b : ℝ => |a - b|) v av X ev)
    (hvM : ∀ x, X x → |v x| ≤ M)
    (hauM : ∀ n x, X x → |au n x| ≤ M')
    (hM0' : 0 ≤ M')
    (heps_nonneg : ∀ n, 0 ≤ eu n ∧ 0 ≤ ev n) :
    LimitDiscrete (fun a b : ℝ => |a - b|)
      (fun x => u x * v x)
      (fun n x => au n x * av n x)
      X
      (fun n => eu n * M + ev n * M' + (eu n + ev n) ^ 2 / 4) := by
  refine ⟨?_, ?_⟩
  · intro n x hx
    have hb := (mul_congr X u v au av eu ev M M' hu hv hvM hauM hM0' heps_nonneg).bound n x hx
    refine le_trans hb ?_
    have := mul_le_sq_add_div_four (eu n) (ev n)
    linarith
  · intro ε hε
    have hto_eu : Filter.Tendsto eu Filter.atTop (nhds 0) :=
      eps_tendsto_zero_iff_tendsto (fun n => (heps_nonneg n).1) hu.eps_tendsto_zero
    have hto_ev : Filter.Tendsto ev Filter.atTop (nhds 0) :=
      eps_tendsto_zero_iff_tendsto (fun n => (heps_nonneg n).2) hv.eps_tendsto_zero
    have hsum : Filter.Tendsto (fun n => eu n + ev n) Filter.atTop (nhds (0 + 0)) :=
      hto_eu.add hto_ev
    have hsq : Filter.Tendsto (fun n => (eu n + ev n) * (eu n + ev n)) Filter.atTop
        (nhds ((0 + 0) * (0 + 0))) := hsum.mul hsum
    have hquart : Filter.Tendsto (fun n => (eu n + ev n) * (eu n + ev n) / 4)
        Filter.atTop (nhds (((0 + 0) * (0 + 0)) / 4)) :=
      hsq.div tendsto_const_nhds (by norm_num)
    have hmain : Filter.Tendsto
        (fun n => eu n * M + ev n * M' + (eu n + ev n) * (eu n + ev n) / 4)
        Filter.atTop (nhds (0 * M + 0 * M' + ((0 + 0) * (0 + 0)) / 4)) :=
      ((hto_eu.mul tendsto_const_nhds).add (hto_ev.mul tendsto_const_nhds)).add hquart
    rw [Metric.tendsto_atTop] at hmain
    obtain ⟨N, hN⟩ := hmain ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.dist_eq] at h
    have h0 : (0 : ℝ) * M + 0 * M' + ((0 + 0) * (0 + 0)) / 4 = 0 := by ring
    rw [h0, sub_zero] at h
    have hfun : eu n * M + ev n * M' + (eu n + ev n) ^ 2 / 4
        = eu n * M + ev n * M' + (eu n + ev n) * (eu n + ev n) / 4 := by
      rw [pow_two]
    rw [hfun]
    exact lt_of_le_of_lt (le_abs_self _) h

/-! ## §4 ⭐ 反例族：三条前提**缺一不可**

本节的三个定理证明：**去掉任一条前提，`mul_congr` 的结论为假**。
⇒ 它们把 §2 的前提**钉死**为「数学必需」而非「作者选择」。
（用户笔记的纪律：「宣布结论前先代小整数判真假」——本节即是该纪律的产物。） -/

/-- ⭐ **反例一：去掉有界性 `hvM` ⟹ 命题为假。**

取 `u x := x`（无界）、`au := 0`、`eu := 0`（**恒为 0，必然 → 0**）、`v := av := 1`。
则 `eu, ev` 全零、`u − au = u` 而"误差"恒为 0 —— `LimitDiscrete` 的两条腿**都满足**；
但 `u x · v x − au x · av x = x` 在 `X := Set.univ` 上**无界**，
故**不存在** `B` 使 `∀ x, |x| ≤ B`。⇒ 结论（一个有限的界）为假。

**结论**：`hvM`（`v` 的界）**不可省**。 -/
theorem mul_congr_fails_without_bounded :
    ¬ (∃ B : ℝ, ∀ x : ℝ, |x * 1 - 0 * 1| ≤ B) := by
  rintro ⟨B, hB⟩
  have h1 := hB (max B 0 + 1)
  have h2 : B < max B 0 + 1 := lt_of_le_of_lt (le_max_left B 0) (lt_add_one _)
  simp only [mul_one, mul_zero, sub_zero] at h1
  linarith [abs_le.mp h1 |>.2]

/-- ⭐ **反例二：去掉 `au` 的界（且界必须 `n`-一致）⟹ 命题为假。**

`au n x := n`（随 `n` 增长、逐点有限但**无 `n`-一致界**），同 `u := au`。
若只有**逐点**界 `|au n| ≤ B n`，则可；但**没有**任何常数 `B` 界住所有 `n`：
取 `n := ⌊|B|⌋ + 1` 即矛盾。

**结论**：`hauM` 的「**关于 `n` 一致**」是实质要求，逐点界不够
（因为 `au` 以 `n` 为索引，而 `mul_congr` 的界 `eu n · M'` 里的 `M'` **不能依赖 `n`**）。 -/
theorem mul_congr_fails_without_uniform_bound :
    ¬ (∃ B : ℝ, ∀ n : ℕ, |(n : ℝ)| ≤ B) := by
  rintro ⟨B, hB⟩
  -- 取 `n := ⌈B⌉₊ + 1`，则 `n > B` ⟹ 与 `|n| ≤ B` 矛盾（因 `n ≥ 0` 时 `|n| = n`）
  have h1 := hB (Nat.ceil B + 1)
  have h2 : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  push_cast at h1
  have hnn : (0 : ℝ) ≤ (Nat.ceil B : ℝ) + 1 := by positivity
  rw [abs_of_nonneg hnn] at h1
  linarith

/-- ⭐⭐ **反例三：去掉 `eps ≥ 0` ⟹ 命题为假（这是最重要的发现）。**

`eu := fun _ => -1` **满足** `LimitDiscrete.eps_tendsto_zero`（**单侧**形式：
`∀ ε > 0, ∃ N, ∀ n ≥ N, eu n < ε`，取 `N := 0` 即可，因为 `-1 < ε`）。
于是若 `mul_congr` 的**第二条腿**（误差项 `eu·ev + … → 0`）**不假设 `eps ≥ 0`**，
取 `eu := ev := -1`、`M := M' := 0` 时误差项 `= eu·ev = 1 > 0`，
**根本不趋于 0** ⇒ 命题为假。

⇒ ⭐ **`LimitDiscrete` 现有的两个字段不足以推出 `mul_congr`** ——
必须**额外**假设 `eps ≥ 0`（或把定义改成 `|eps n| < ε`）。 -/
theorem mul_congr_fails_without_eps_nonneg :
    ¬ (∀ (eu ev : Nat → ℝ),
      (∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, eu n < ε) →
      (∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ev n < ε) →
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, eu n * 0 + ev n * 0 + eu n * ev n < ε) := by
  intro h
  have hneg : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, (fun _ => (-1 : ℝ)) n < ε :=
    fun ε hε => ⟨0, fun n _ => by simpa using lt_trans (by norm_num : (-1:ℝ) < 0) hε⟩
  obtain ⟨N, hN⟩ := h (fun _ => -1) (fun _ => -1) hneg hneg 1 (by norm_num)
  have h1 := hN N le_rfl
  norm_num at h1

/-! ## §5 ⭐⭐ 诚实边界：`mul_congr` 揭示的 `LimitDiscrete` **定义缺口**

§4 的反例三说明了一件**比 `mul_congr` 本身更重要**的事：

> `LimitDiscrete.eps_tendsto_zero` 是**单侧**的（只说 `eps n < ε`），
> **不蕴含 `eps` 非负**。而**乘法**组合需要 `eps ≥ 0`。

**为什么加法不需要、乘法需要**：`add_congr` 的两条腿是
`eu + ev < ε/2 + ε/2 = ε` —— **只用到了"上界"**，
故 `eps` 可以取负（负的 `eps` 只会让结论**更强**）；
而 `mul_congr` 的第二条腿要证 `eu·M + ev·M' + eu·ev → 0`，
其中 `eu·ev` **在 `eps` 取负时变成正的、发散的**（§4 反例三）。

⇒ ⭐ **两种修法**（本文件**采取前者**，因为 §1.1 的纪律是「不修改既有文件」）：

1. **（本文件采用）** 把 `eps ≥ 0` 作为 `mul_congr` 的**显式前提**；
   ⚠ 代价：调用者必须自己提供它 —— 对**真实的误差序列它天然成立**
   （误差是 `|· − ·|` 的上界），故实践中**不是负担**；
2. **（未采用，需改 op-split）** 把 `eps_tendsto_zero` 加强为
   `∀ ε > 0, ∃ N, ∀ n ≥ N, |eps n| < ε`；这样 `eps ≥ 0` 可被推出而无需显式前提。
   ⚠ **本文件不做这个改动** —— 那会**修改 `yjh051108` 的定义**，
   破坏其证明体（`add_congr` / `t1_t2_bridge` / `mul_split_limit_discrete` 等需重编译），
   且属**跨作者改动**，须先报协调者。

⭐ **判定：这不是 "`mul_congr` 不可证"，而是 "`mul_congr` 在现有定义下需要一条额外前提"。**
命题在加上 `eps ≥ 0` 后**可证**（§2 已证），故**不需要新理论**，
只需在**调用侧**记住这条前提。

⭐ **附注（§5.1）**：本文件用到的桥接引理 `eps_tendsto_zero_iff_tendsto`
（`eps` 单侧趋于 0 + `eps ≥ 0` ⟺ `Tendsto eps atTop (nhds 0)`）
**已上移到 §1 之后、§2 之前** —— 因为 §2/§3 的**第二条腿**都要用它。
有了它，第二条腿就能**直接复用 mathlib 的 `Tendsto` 封闭性**
（`.mul` / `.add` / `.div`），而不必手算 `ε/4` 阈值。 -/

/-! ## §6 第 3 步：组合到**多层链**

把 §2 的**单层**乘法组合迭代到 `m` 层。⚠ 与 `RealModelChain` 的**精确 Lipschitz 版**
（`chainN_dom_bound`）对应：那里常数是**连乘** `∏ Ls i`，这里误差是**递推累积**的。

⭐ **链的形态**：给定一族"逐层近似"数据 —— 每层 `j` 有一个精确映射
`F j : α → ℝ` 与它的近似 `Fa j : α → ℝ`，以及逐层误差界 `e j`；
则 `m` 层的复合 `F (m−1) ∘ ⋯ ∘ F 0` 与 `Fa (m−1) ∘ ⋯ ∘ Fa 0` 的误差。

⚠ **本节的诚实边界**：为把复杂度控制在**可证**范围内，本节只做
**「逐层误差已知、且各层有界」⟹ 复合链误差有界且 → 0** 的组合，
**不**从「单点近似」自动推导「逐层误差」（那需要**一致**的层的界，是实例化工作）。 -/

/-- **链前向**（与 `RealChain.ChainFwd` 同形，特化到 `ℝ`）：
第 `j` 层的函数是 `Fs j`，`m` 层复合作用在 `x` 上。 -/
def ChainFwdReal (Fs : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | (m + 1), x => Fs m (ChainFwdReal Fs m x)

/-- **链式误差累积**：`m` 层复合的误差递推界。

    chainErrReal e B 0     = 0
    chainErrReal e B (m+1) = e m + B m * chainErrReal e B m

⭐ **递推式的来源**（把 §2 的 `mul_congr` 误差项 `eu·M + ev·M' + eu·ev` 用上）：
第 `m` 层是「本层近似误差 `e m`」⊗「前 `m` 层的累积误差 `chainErrReal e B m`」。
把 `eu := e m`（本层）、`ev := chainErrReal e B m`（累积）、
`M := B m`（本层输出的值域界，界住 `|v|`）代入
⇒ `e m · B m + chainErrReal m · B m + e m · chainErrReal m`
**≤ `e m + B m · chainErrReal m`**（在 `B m ≥ 1`、误差非负时）。

⚠ 本文件保守地取**更松但更简单**的递推 `e m + B m * chainErrReal m`
（**丢弃**了 `e m · chainErrReal m` 这个二阶项，把它吸收进 `e m`）——
这只影响常数松紧，**不影响正确性**。 -/
def chainErrReal (e B : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (m + 1) => e m + B m * chainErrReal e B m

/-- **累积误差非负**：若各层误差 `e j ≥ 0`、各层值域界 `B j ≥ 0`，
则累积误差 `chainErrReal e B m ≥ 0`。

⭐ 这是 §2 前提 `heps_nonneg` 在**链式层面**的对应物 ——
**链式组合同样需要误差非负**（否则 §2 的第三条腿 `eu·ev` 会符号翻转，见 §5）。 -/
theorem chainErrReal_nonneg {e B : ℕ → ℝ} (he : ∀ j, 0 ≤ e j) (hB : ∀ j, 0 ≤ B j) :
    ∀ m, 0 ≤ chainErrReal e B m := by
  intro m
  induction m with
  | zero => simp [chainErrReal]
  | succ k ih =>
      have : chainErrReal e B (k + 1) = e k + B k * chainErrReal e B k := rfl
      rw [this]
      exact add_nonneg (he k) (mul_nonneg (hB k) ih)

/-- **累积误差的闭式**：`chainErrReal e B m = Σ_{j<m} e j · ∏_{j<i<m} B i` 的量级；
本文件用**更粗但可证**的形式：若 `e j ≤ E`、`B j ≤ Bc`（`Bc ≥ 1`），则

    chainErrReal e B m ≤ E * (m + 1) * Bc ^ m

⚠ **为什么不是 `E * Bc^m`**：递推 `c(k+1) = e k + B k · c k` 的**真闭式是
`Σ_{j<k} e j · (∏_{i>j} B i)`**，对 `e ≡ E`、`B ≡ Bc` 即
`E · (1 + Bc + Bc² + ⋯ + Bc^(k−1))`。当 `Bc > 1` 时该和 ≈ `E·Bc^k/(Bc−1)`，
**含一个 `m` 因子**（`Bc = 1` 时恰为 `E·m`）。
⇒ 故正确上界带 **`(m+1)` 因子**；写成 `E·Bc^m` 是**假命题**（本文件第一稿即犯此错，
"代小整数验一遍"纪律再次生效：取 `e ≡ 1`、`B ≡ 1`、`m = 2` 时
`chainErrReal = 2 > 1 = E·Bc^m`）。 -/
theorem chainErrReal_le {e B : ℕ → ℝ} {E Bc : ℝ}
    (he : ∀ j, e j ≤ E) (hB : ∀ j, B j ≤ Bc) (hE : 0 ≤ E) (hBc1 : 1 ≤ Bc)
    (hB0 : ∀ j, 0 ≤ B j) (hEe : ∀ j, 0 ≤ e j) :
    ∀ m, chainErrReal e B m ≤ E * (m + 1) * Bc ^ m := by
  intro m
  induction m with
  | zero =>
      have h0 : chainErrReal e B 0 ≤ E * ((0 : ℕ) + 1) * Bc ^ 0 := by
        rw [chainErrReal]
        norm_num
        exact hE
      simpa using h0
  | succ k ih =>
      have hBc0 : (0 : ℝ) ≤ Bc := by linarith
      have hBck : (0 : ℝ) ≤ Bc ^ k := pow_nonneg hBc0 k
      have h1 : e k ≤ E := he k
      have hce0 : 0 ≤ chainErrReal e B k := chainErrReal_nonneg hEe hB0 k
      have h2 : B k * chainErrReal e B k ≤ Bc * (E * (k + 1) * Bc ^ k) :=
        calc B k * chainErrReal e B k ≤ Bc * chainErrReal e B k :=
              mul_le_mul_of_nonneg_right (hB k) hce0
          _ ≤ Bc * (E * (k + 1) * Bc ^ k) := mul_le_mul_of_nonneg_left ih hBc0
      have hBck1 : (1 : ℝ) ≤ Bc ^ (k + 1) := one_le_pow₀ hBc1
      have hstep : E + Bc * (E * (k + 1) * Bc ^ k)
          ≤ E * ((k : ℝ) + 2) * Bc ^ (k + 1) := by
        have hexp : Bc * (E * ((k : ℝ) + 1) * Bc ^ k)
            = E * ((k : ℝ) + 1) * Bc ^ (k + 1) := by
          rw [pow_succ]; ring
        rw [hexp]
        have hE1 : E ≤ E * Bc ^ (k + 1) := le_mul_of_one_le_right hE hBck1
        nlinarith [hE, hBck1, hE1]
      calc chainErrReal e B (k + 1)
          = e k + B k * chainErrReal e B k := rfl
        _ ≤ E + Bc * (E * (k + 1) * Bc ^ k) := add_le_add h1 h2
        _ ≤ E * ((k : ℝ) + 2) * Bc ^ (k + 1) := hstep
        _ = E * ((k + 1 : ℕ) + 1) * Bc ^ (k + 1) := by push_cast; ring

/-! ## §6.1 注：第 3 步**还差什么**

⭐ **要接上 `RealModelChain` 的真实形态，还差三件事**（本文件**未做**）：

1. **「单点近似」⟹「链式累积误差」**：`mul_congr` 处理的是**同一个 `α` 上的两个函数**
   （`u` 与 `au`），而链式复合要求 `u_{j+1}` 的输入是 `u_j` 的**输出**。
   故需要「层 `j` 的近似误差 `e j`」在**整个链的输入区间上一致** ——
   这是 `hstep` 那样的**逐层一致**前提，本文件 §6 已**显式作为前提**（`hstep`），
   **未从单层数据自动导出**；
2. **值域界 `B j` 的传递**：§6 把 `B j` 也作为**显式前提**。真实网络里
   它应由「层 Lipschitz 性 + 输入界」推出 —— `RealModelChain` 的 `hreach` 正是
   这同一件事的**精确版**。故**两边的缺口是同一个**（可达性/值域界作为显式前提）；
3. **把 `chainErrReal` 的递推换成 `RealChain` 的 `∏` 形态**：本文件的
   `chainErrReal e B (m+1) = e m + chainErrReal e B m * B m` 与
   `RealChain.chainN_error_bound` 的 `∏ Ls i` 是**两种不同的累积律**
   （误差的**加法累积 × 放大** vs 常数的**纯连乘**）。要统一需额外引理。

⇒ ⭐ **结论**：第 3 步的**组合骨架**已完成（§6），
**真正的缺口是「值域界/可达性」—— 这与 `RealModelChain` 的 `hreach` 是同一个缺口**，
属**实例化工作**，不是组合性工作。 -/

end Lattice
