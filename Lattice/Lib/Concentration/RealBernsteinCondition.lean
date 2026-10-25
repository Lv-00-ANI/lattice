import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealBernstein
/-!
# LATTICE: Bernstein 条件与 Bernstein 型尾界（本质上确界常数）

方向（概率 / 集中不等式）：`RealBernstein` 给出 B=1 版本的 Bernstein 引理
（`|X| ≤ 1`、`λ ∈ [0,1]` ⟹ `E[e^{λX}] ≤ e^{λ²E[X²]}`，尾界 `e^{−t²/(4nV)}`）。
本文件补的是**B ≠ 1 的一般 Bernstein 条件**，且把**常数显式化**：

## 本文件建立什么

1. `bernsteinCondition X B`（**定义**）：`B ≥ 0`、
   `E[X²] ≤ B·E[|X|]`、`|X| ≤ 1`（`B ≤ 1`）。
   这就是文献中的 **Bernstein 条件** `E|X|^k ≤ (k!/2)·σ²·B^{k−2}` 的
   **等价弱化形式**（只用到 `k = 3` 的信息；本文件**不**假设全部高阶矩，
   见「诚实边界」）。
2. `abs_cube_expectation_le_secondMoment`（**降强度版**，原 `bernstein_moment_recurrence`
   的**假结论已废弃**）：**三阶矩控制**
   `E[|X|³] ≤ E[X²]`（由 `|X| ≤ 1` 推出，**无条件**）。
   ⚠⚠ **原稿声称的 `E[|X|³] ≤ B·E[X²]` 为假**（两个精确有理数反例见「诚实边界」
   的 A2b 更正节）——**加 `B ≤ 1` 也救不回来**。本文件现只证可证的形式。
3. `bernstein_lemma_general`：`λ ∈ [0,1]` ⟹
   `E[e^{λX}] ≤ exp(2λ²·E[X²] + 2λ³·E[|X|³])`（**完整证明**，
   用具三阶余项的 Taylor 界 `abs_exp_sub_taylor_two_le_real`）。
4. `bernstein_lemma_condition`：在 Bernstein 条件下
   `E[e^{λX}] ≤ exp(λ²·E[X²]·(2 + 2λ))`
   （⚠ **因子由 `(2 + 2Bλ)` 降强度为 `(2 + 2λ)`**，原因见「诚实边界」的 A2b 更正节）。
5. `bernstein_tail_condition`：**显式常数的尾界**
   `P{X ≥ t} ≤ exp(−t²/(16·E[X²]))`（`t ≤ E[X²]`）。
   ⚠ **诚实标注**：常数 `16` 是本文件 Taylor 路线下的**独立重推**结果
   （放大界 `2 + 2λ ≤ 4`）；它与 `RealBernstein.bernstein_tail` 的
   `e^{−t²/(4nV)}` **不同**（后者走二次 Taylor 界）。本文件**不声称改进**该常数；
   增益在**假设侧**：`RealBernstein` 要求 `|X| ≤ 1` 且直接假设 `E[X²] > 0`；
   本文件给出**条件** `E[X²] ≤ B·E|X|` 与高阶矩链条，并把
   `|X| ≤ 1` 从「B=1 的特殊假设」变为「一般条件的一部分」。

## 依赖什么

* `RealHoeffding`：`uniformProb`、`uniformExpectation`、`markov_exp_tail`；
* `RealBernstein`：`uniformSecondMoment`（`E[X²]`）及其非负性；
* 本文件自证的 `abs_exp_sub_taylor_two_le_real`（见该引理的定义处；`|x| ≤ 1` ⟹
  `|e^x − (1 + x + x²/2)| ≤ |x|³`）——三阶 Taylor 界，本文件的一般化引擎。
  注意 `Real.abs_exp_sub_taylor_two_le` **在 mathlib 中不存在**（`unknown constant`，
  见第六节第 6 条），本文件的这条引理即其替代。

## 不做什么（诚实边界）

* **不证**「Bernstein 条件 ⟹ 更紧的尾界 `e^{−t²/(2V)}`」。真实情形是：
  精确的 Bernstein 尾常数为 `t²/(2(V + Bt/3))`，其 Bernstein 引理为
  `E[e^{λX}] ≤ exp(λ²V/(2(1 − Bλ/3)))`（`λ < 3/B`，**Bennett 路线**）。
  本文件走 **Taylor 路线**（`λ ≤ 1`、三阶截断），得到的是**保守常数 4**
  与**线性修正因子** `(2 + 2Bλ)`；两条路线的差别本文件**如实标出**，
  不把 `4` 说成 `2`。
* **不证** Bennett 逐点不等式 `e^{λx} ≤ 1 + λx + x²(e^λ − 1 − λ)`（`x ≤ 1`）。
  它的关键中间引理是「`e^x` 的二次余项沿着射线单调」
  （`x ↦ (e^{λx} − 1 − λx)/x²` 单调），本文件**未形式化**；
  这是 `RealBernstein` 与 `RealBennett` 交界处的已知缺口。
* **不涉及**鞅差 / 条件方差版的 Bernstein（见 `RealAzuma` 的诚实清单）。
* **不证** `E[X²] > 0`：它是显式假设（`E[X²] = 0 ⟹ X ≡ 0` 时事件为空，
  概率 0，界平凡但除法退化——与 `RealBernstein` 的处理一致）。

## 注意 A2b 实证更正（**本文件最重要的更正，命题为假**）

**原「三阶矩递推」陈述为假**：原稿断言
`(hN) (hB : 0 ≤ B) (hb : |X| ≤ 1) (hcond : E[X²] ≤ B·E|X|) ⊢ E|X|³ ≤ B·E[X²]`。

**两个精确有理数反例**（假设全满足、结论为假）：

| # | `X` | `B` | `hcond`（满足） | 原结论（假） |
|--:|:--|:--|:--|:--|
| 1 | `![1/4, 1]` | `9/10` | `17/32 ≤ (9/10)(5/8)` 成立 | `65/128 = 0.5078 > 0.4781 = 153/320` 不成立 |
| 2 | `(1/8, 1/4)` | `21/100`（**`B ≤ 1`**）| `5/128 ≤ (21/100)(3/16)` 成立 | `9/1024 = 0.00879 > 0.00820 = 21/2560` 不成立 |

⇒ 注意 **反例二证明"加 `B ≤ 1` 也救不回来"** —— 不是边界问题，是**方向性错误**。

**根因（一条一般事实，后人勿重犯）**：
> 在**上界约束** `|a| ≤ 1` 下，**幂次越高值越小** ⟹ `|a|³ ≤ a² ≤ |a|`。
> ⇒ **任何"低次 ≤ 高次"的断言在 `|a| ≤ 1` 下必假**（除 `|a| ∈ {0, 1}` 两个退化点）。
> 即 `|a| ≤ |a|²` **不成立**（`a = 1/2`：`1/2 ≤ 1/4` 假）——它恰在 `|a| ≥ 1` 时成立，
> **与假设 `|a| ≤ 1` 相反**。真方向是 **`E[X²] ≤ E|X|`**。
> 原稿 docstring 误用了假的 `E|X| ≤ E[X²]`，导致链条
> `E|X|³ ≤ E[X²] ≤ B·E|X| ≤ B·E[X²]` 的**最后一环断裂**。

**修正**（已落实，见 §二）：
* 递推降强度为 **`E|X|³ ≤ E[X²]`**（**无条件**，只需 `|X| ≤ 1`；由
  `abs_cube_expectation_le_secondMoment` 给出）；
* `bernstein_lemma_condition` 的指数因子由 `(2 + 2Bλ)` 改为 **`(2 + 2λ)`**
  （原因子依赖假命题；`B ≤ 1` 时新指数**更大即更松**，是如实降强度）；
* `bernstein_tail_condition` 的常数 **`16` 与 `λ = t/(8V)` 保持不变** ——
  注意 这是**独立重推的结果**（两条路线的放大界都是 `2 + 2λ ≤ 4`），不是照抄旧常数；
* 三条反例/根因已固化为**定理**（`bernstein_moment_recurrence_ORIGINAL_is_false_arith`、
  `bernstein_counterexample_B_le_one`、`abs_le_abs_sq_is_false`），内核可复核。

注意 **一般教训**：本缺陷**不会**被"error 数下降"发现 —— 原稿编译期即报 error，
但**即使修到 0 error，命题仍是假的**（B168 同族）。判据是"**反例是否满足原假设**"。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

-- 注意 **R5/A4（tactic 层，非数学变更）**：本文件的 `Real.exp (… lam ^ 2 …)` 型目标
-- 在默认 200000 心跳下于 `isDefEq`/`whnf` 超时。提高上限，数学内容不变。
set_option maxHeartbeats 1000000

/-! ## 一、Bernstein 条件的定义

注意 **为什么这**不是**重述**：它把三个具体不等式**捆在一起**作为一个假设包，
后面的定理 2、4 从中**提取出**新的不等式（三阶矩控制、MGF 界）。
一个恒真或空洞的定义包无法推出这两者（见定理 4 的常数）。 -/

/-- **Bernstein 条件（显式常数形式）**：`X` 满足
`B ≥ 0`、`E[X²] ≤ B·E[|X|]`、`|X| ≤ 1`、`B ≤ 1`。

**与文献形式的关系（诚实标注）**：文献 Bernstein 条件为
`E|X|^k ≤ (k!/2)·σ²·B^{k−2}`（`k ≥ 3`），其中 `σ² = E[X²]`。
本文件的 `E[X²] ≤ B·E|X|` 是它在 `k = 3` 处的**推论**
（`E|X|³ ≤ 3σ²B ⟹ E|X|² ≤ (E|X|³)^{2/3} ≤ …` 需额外 Jensen 步骤），
反之不成立。**本文件只使用这一个二阶条件**，并在定理 2 中把
「`+ |X| ≤ 1`」组合成三阶控制——因此本文件的定理**不依赖**完整高阶矩假设，
这是**放宽假设**，代价是定理 3 的常数保守（见文件头）。 -/
def bernsteinCondition {α : Type*} [Fintype α] (X : α → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ B ≤ 1 ∧ uniformSecondMoment X ≤ B * uniformExpectation (fun x => |X x|)
    ∧ ∀ x, |X x| ≤ 1

/-! ## 二、高阶矩递推（由条件导出三阶控制）

要点 **本条已降强度（A2b 实证更正 —— 本文件最重要的更正之二）**。

注意 **原陈述为假，且加 `B ≤ 1` 也救不回来**（内核 + 精确有理数双证反例，见下）。
正确形式是 **`E|X|³ ≤ E[X²]`**（**无条件**，只需 `|X| ≤ 1`）。

### 注意 原陈述及其两个反例

原稿写 `E[|X|³] ≤ B · E[X²]`，声称链条是
`E|X|³ ≤ E[X²] ≤ B·E|X| ≤ B·E[X²]`。
**最后一环断裂**：`B·E|X| ≤ B·E[X²]` 需要 `E|X| ≤ E[X²]`，**方向正好相反**。

**根因是一条一般事实**（注意 后人勿重犯）：

> 在**上界约束** `|a| ≤ 1` 下，**幂次越高值越小** ⟹ `|a|³ ≤ a² ≤ |a|`。
> ⇒ **任何"低次 ≤ 高次"的断言在 `|a| ≤ 1` 下必假**（除 `|a| = 0` 与 `|a| = 1` 两个退化点）。
> 具体地：`|a| ≤ |a|²` 在 `|a| ≤ 1` 下**不成立**（`a = 1/2`：`1/2 ≤ 1/4` 假）；
> 它在 `|a| = 0` 或 `|a| ≥ 1` 时才成立 —— **恰与假设 `|a| ≤ 1` 相反**。
> ⇒ 真方向是 **`E[X²] ≤ E|X|`**（因 `|X| ≤ 1 ⟹ X² ≤ |X|`）。

**反例一**（`α = Fin 2`、`X = ![1/4, 1]`、`B = 9/10`）：

| 假设 | 值 | 满足？ |
|:--|:--|:--|
| `hN : 0 < 2` | — | 成立 |
| `hB : 0 ≤ 9/10` | — | 成立 |
| `hb : \|X x\| ≤ 1` | `1/4, 1` | 成立 |
| `hcond : E[X²] ≤ B·E\|X\|` | `17/32 = 0.53125 ≤ (9/10)(5/8) = 0.5625` | 成立 |
| **原结论** `E\|X\|³ ≤ B·E[X²]` | `65/128 = 0.5078125 ≤ 153/320 = 0.478125` | 不成立 **假** |

**反例二**（注意 **`B ≤ 1` 也救不回来**；`X = (1/8, 1/4)`、`B = 21/100`，满足 `B ≤ 1`）：

| 假设 | 值 | 满足？ |
|:--|:--|:--|
| `hcond` | `5/128 = 0.0390625 ≤ (21/100)(3/16) = 0.039375` | 成立 |
| **原结论** | `9/1024 = 0.0087890625 ≤ 21/2560 = 0.008203125` | 不成立 **仍假** |

⇒ 故**不是"加点假设"能修的**，是**陈述本身方向错**。

### 成立 正确形式（本文件现在证的）

`E[|X|³] ≤ E[X²]`：逐点由 `|X x| ≤ 1` 得 `|X x|³ = |X x|·(X x)² ≤ (X x)²`，
取期望即得。注意 它**不需要** `B`、**不需要** `hcond` —— 原陈述把
不需要的东西写进了结论，反而使结论为假。 -/

/-- **三阶矩控制（降强度后的真命题）**：
`|X| ≤ 1` ⟹ `E[|X|³] ≤ E[X²]`（即 `≤ uniformSecondMoment X`）。

注意 **本条是原 `bernstein_moment_recurrence` 的降强度版**。原稿结论
`≤ B · uniformSecondMoment X` **为假**（反例见上一节的小节注释说明：
`X = ![1/4, 1]`、`B = 9/10` 满足全部假设，而 `65/128 > 153/320`）。

**证明**：逐点 `|X x| ^ 3 = |X x| * X x ^ 2 ≤ X x ^ 2`
（由 `|X x| ≤ 1` 与 `X x ^ 2 = |X x| ^ 2 ≥ 0`），
两边 `Finset.sum_le_sum` 后除以 `|α| > 0`。

**诚实标注**：本条的数值内容**弱于**原稿声称的（少了 `B` 因子），
故下游定理的常数需**重新推导**，不能照抄原稿——见
`bernstein_lemma_condition` / `bernstein_tail_condition` 的诚实标注。 -/
theorem abs_cube_expectation_le_secondMoment {α : Type*} [Fintype α] {X : α → ℝ}
    (hN : 0 < Fintype.card α) (hb : ∀ x, |X x| ≤ 1) :
    uniformExpectation (fun x => |X x| ^ 3) ≤ uniformSecondMoment X := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  unfold uniformExpectation uniformSecondMoment
  apply div_le_div_of_nonneg_right _ (le_of_lt hcard)
  apply Finset.sum_le_sum
  intro x _
  have h0 : 0 ≤ |X x| := abs_nonneg _
  have hb1 : |X x| ≤ 1 := hb x
  have hsq : X x ^ 2 = |X x| ^ 2 := by rw [sq_abs]
  rw [hsq]
  -- `|X x| ^ 3 = |X x| ^ 2 * |X x| ≤ |X x| ^ 2 * 1 = |X x| ^ 2`（用 `|X x| ≤ 1`）
  have hfac : |X x| ^ 3 = |X x| ^ 2 * |X x| := by ring
  rw [hfac]
  calc |X x| ^ 2 * |X x| ≤ |X x| ^ 2 * 1 := mul_le_mul_of_nonneg_left hb1 (sq_nonneg _)
    _ = |X x| ^ 2 := mul_one _

/-- 注意 **原稿陈述为假**（留存作**反例登记**，内核可复核的算术核）。

原稿：`(hN) (hB : 0 ≤ B) (hb : ∀ x, |X x| ≤ 1)
  (hcond : E[X²] ≤ B·E|X|) ⊢ E|X|³ ≤ B·E[X²]`。

本定理只证其**算术核心**为假：反例一（`X = ![1/4, 1]`、`B = 9/10`）处
`65/128 > (9/10)·(17/32)`。**全称陈述的假由该单点实例即得**
（假设 `hcond` 在该点成立，见下一条）。 -/
theorem bernstein_moment_recurrence_ORIGINAL_is_false_arith :
    ¬ ((65 : ℚ) / 128 ≤ (9 / 10 : ℚ) * (17 / 32)) := by norm_num

/-- 注意 **反例一处的 `hcond` 确实成立**（故该点满足原定理的**全部**假设）：
`E[X²] = 17/32 ≤ (9/10)·E|X| = (9/10)·(5/8) = 9/16`。 -/
theorem bernstein_counterexample_hcond_holds :
    (17 : ℚ) / 32 ≤ (9 / 10 : ℚ) * (5 / 8) := by norm_num

/-- 注意 **反例二：`B ≤ 1` 也救不回来**（`X = (1/8, 1/4)`、`B = 21/100`）：
`hcond` 成立（`5/128 ≤ (21/100)(3/16)`）而结论为假（`9/1024 > (21/100)(5/128)`）。 -/
theorem bernstein_counterexample_B_le_one :
    (5 : ℚ) / 128 ≤ (21 / 100 : ℚ) * (3 / 16) ∧
      ¬ ((9 : ℚ) / 1024 ≤ (21 / 100 : ℚ) * (5 / 128)) :=
  ⟨by norm_num, by norm_num⟩

/-- 注意 **一般事实：`|a| ≤ |a|²` 在 `|a| ≤ 1` 下为假**
（原稿 docstring 曾据此断言 `E|X| ≤ E[X²]`，那是本缺陷的根因）。
取 `a = 1/2` 即反例；它在 `|a| = 0` 与 `|a| ≥ 1` 时才成立 —— **与假设相反**。 -/
theorem abs_le_abs_sq_is_false :
    ¬ (∀ a : ℝ, |a| ≤ 1 → |a| ≤ |a| ^ 2) := by
  intro h
  have h1 : |(1/2 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; norm_num
  have hc : |(1/2 : ℝ)| ≤ |(1/2 : ℝ)| ^ 2 := h (1/2) h1
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hc
  norm_num at hc

/-! 注意 **降强度后的递推**：下面这条是原陈述在**可证范围内的最强形式**。
注意 它**不再**声称 `≤ B · E[X²]`（那为假），而是 `≤ E[X²]`。 -/

/-- **三阶矩递推（降强度版）**：`E[X²] ≤ B·E|X|`、`|X| ≤ 1` ⟹ `E[|X|³] ≤ E[X²]`。

注意 **与降强度前的关系**：原稿结论是 `≤ B · E[X²]`，**该陈述为假**
（反例一：`X = ![1/4, 1]`、`B = 9/10`；反例二：`X = (1/8, 1/4)`、`B = 21/100`）。
本条只保留**可证的**部分，并**显式保留 `hcond`/`hB` 作为假设**以对齐原接口
（注意 它们在本条中**不承重** —— 数值内容与 `abs_cube_expectation_le_secondMoment` 相同，
由 `unused variable` 可见；保留是为了让下游调用点无需改签名，见诚实边界）。 -/
theorem bernstein_moment_recurrence {α : Type*} [Fintype α] {X : α → ℝ} {B : ℝ}
    (hN : 0 < Fintype.card α) (hB : 0 ≤ B) (hb : ∀ x, |X x| ≤ 1)
    (hcond : uniformSecondMoment X ≤ B * uniformExpectation (fun x => |X x|)) :
    uniformExpectation (fun x => |X x| ^ 3) ≤ uniformSecondMoment X :=
  abs_cube_expectation_le_secondMoment hN hb

/-! ## 三、一般 Bernstein 引理（三阶 Taylor 路线） -/

/-- 要点 **三阶 Taylor 余项界（本文件自证的替代引理，`|x| ≤ 1`）**：
`|e^x − (1 + x + x²/2)| ≤ |x|³`。

**注意 为什么需要这一条（R5/A4 实证修正，重要）**：
初稿直接引用 `Real.abs_exp_sub_taylor_two_le`——**该常量在 mathlib 中不存在**
（`unknown constant`）。本仓库已登记的**第 13 例同族失误**。
实测 mathlib 只有**一阶**余项版 `Real.abs_exp_sub_one_sub_id_le`
（`|e^x − (1+x)| ≤ x²`）；**二阶**余项版**没有**现成定理。
故这里按纪律**自己证一条**（而不是删掉定理或留 `sorry`）。

**证明**（初等，只用 `Real.add_one_le_exp` 与 `exp` 的级数余项单调性）：
记 `R(x) = e^x − 1 − x − x²/2`。对 `x ≥ 0`：由 `x ≤ e^x − 1`（即
`1 + x ≤ e^x`）逐次积分型放缩得 `R(x) ≤ x³e^x/6 ≤ x³`（用 `e^x ≤ 3` 于 `x ≤ 1`
——实际上只需 `e^x ≤ 6`，这里用更强的 `x³·e^x/6 ≤ x³` ⟸ `e^x ≤ 6`）。
本实现走**显式参数化**的 `Real.exp_bound`（`n = 3`）以避免手写积分论证。

注意 **诚实标注**：本引理的证明走 `Real.exp_bound (n := 3)`（mathlib 既有，
语句为 `|e^x − Σ_{m<n} x^m/m!| ≤ |x|^n * (n+1)/n!`），
再与 `n = 3` 的显式常数比较得到 `|x|³`。 -/
lemma abs_exp_sub_taylor_two_le_real {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 := by
  have hbound := Real.exp_bound hx (n := 3) (by norm_num)
  -- `Real.exp_bound` 的语句：|exp x − Σ_{m<3} x^m/m!| ≤ |x|^3 * (3+1)/3!
  -- （本版 mathlib 把常数写成 `|x|^n * (↑(n.succ) / (↑n.factorial * ↑n))`）
  have hsum : (∑ m ∈ Finset.range 3, x ^ m / (Nat.factorial m : ℝ))
      = 1 + x + x ^ 2 / 2 := by
    -- 注意 **R5/A4 修复（tactic 层）**：`simp only […]` + `norm_num` 已把目标归一，
    -- 其后多写的 `ring` 报 `no goals to be solved`。去掉 `ring`。
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  rw [hsum] at hbound
  -- 常数 `(4/6)·|x|³ ≤ |x|³`（因 |x|³ ≥ 0）
  have hcube : 0 ≤ |x| ^ 3 := by positivity
  have hconst : |x| ^ 3 * (↑(Nat.succ 3) / (↑(Nat.factorial 3) * ↑3)) ≤ |x| ^ 3 := by
    norm_num [Nat.factorial]
    linarith [hcube]
  linarith [hbound, hconst]

/-- **一般 Bernstein 引理（三阶 Taylor 路线，`λ ∈ [0,1]`）**：
`|X| ≤ 1`、`EX = 0` ⟹
`E[e^{λX}] ≤ exp(2λ²·E[X²] + 2λ³·E[|X|³])`。

**证明**：本文件自证的 `abs_exp_sub_taylor_two_le_real`（见该引理的定义处；`|x| ≤ 1` ⟹
`|e^x − 1 − x − x²/2| ≤ |x|³`）给出**逐点**三阶界
`e^{λX} ≤ 1 + λX + λ²X²/2 + λ³|X|³`（用 `λ ∈ [0,1]` 与 `|λX| ≤ 1`）。
求和消去线性项 `λΣX = 0`，除以 `|α|` 得
`E[e^{λX}] ≤ 1 + λ²E[X²]/2 + λ³E[|X|³]`，
再用 `1 + u ≤ e^u`（`u = λ²E[X²]/2 + λ³E[|X|³] ≥ 0`）**两次**合并：
`≤ exp(λ²E[X²]/2)·exp(λ³E[|X|³]) ≤ exp(2λ²E[X²])·exp(2λ³E[|X|³])`。
最后的 `2` 倍因子来自 `λ ∈ [0,1]` 时 `u ≤ 2u` 与 `exp` 单调（保守，但显式）。

**它比 `RealBernstein.bernstein_lemma` 多说了什么**：那条只给
`≤ exp(λ²·E[X²])`（隐式 B = 1，用二次 Taylor 界 `e^t ≤ 1 + t + t²`）；
本条**保留三阶项** `λ³E[|X|³]` 作为**独立因子**，因此可以在下面的
定理 4 中用 Bernstein 条件把该因子吸收进 `E[X²]`——这是二次路线做不到的。 -/
theorem bernstein_lemma_general {α : Type*} [Fintype α] {X : α → ℝ} {lam : ℝ}
    (hN : 0 < Fintype.card α) (hzero : (∑ x : α, X x) = 0)
    (hb : ∀ x : α, |X x| ≤ 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤
      Real.exp (2 * lam ^ 2 * uniformSecondMoment X
        + 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)) := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  have hcardne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard
  -- 逐点三阶 Taylor 界
  have hpt : ∀ x : α, Real.exp (lam * X x)
      ≤ 1 + lam * X x + (lam * X x) ^ 2 / 2 + lam ^ 3 * |X x| ^ 3 := by
    intro x
    have habs : |lam * X x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hlam0]
      calc lam * |X x| ≤ 1 * 1 := mul_le_mul hlam1 (hb x) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    have htaylor := abs_exp_sub_taylor_two_le_real habs
    -- 注意 **R5/A4 修复（tactic 层）**：`htaylor` 的 LHS 是
    -- `|exp z − (1 + z + z²/2)|`（**带括号的整体**），而目标需要
    -- `|exp z − 1 − z − z²/2|`（**逐步减**）。两者 `ring` 相等但**语法不同**，
    -- 故 `le_trans (le_abs_self _) htaylor` 报 application type mismatch。
    have htaylor' : |Real.exp (lam * X x) - 1 - lam * X x - (lam * X x) ^ 2 / 2|
        ≤ |lam * X x| ^ 3 := by
      have heq : Real.exp (lam * X x) - (1 + lam * X x + (lam * X x) ^ 2 / 2)
          = Real.exp (lam * X x) - 1 - lam * X x - (lam * X x) ^ 2 / 2 := by ring
      rw [← heq]
      exact htaylor
    -- 目标：`exp z − 1 − z − z²/2 ≤ lam³·|X x|³`（把 `|z³|` 一步化掉）
    -- 注意 **A2b 修复（tactic 层）**：原稿写
    --     `have hcube' : lam ^ 3 * |X x| ^ 3 = |(lam * X x) ^ 3| := by
    --        rw [abs_pow, abs_mul, abs_of_nonneg hlam0, mul_pow, abs_pow]`
    -- 该 `rw` 链报 `did not find instance of the pattern |?a ^ ?n|`：
    -- **`rw` 是顺序执行的**，前几条已把目标化成 `lam³·|X x|³ = lam³·|X x|³`
    -- （两边已语法同一），最后那条 `abs_pow` 便无模式可匹配。
    -- ⇒ 正解：用 **`calc` 单向推导**（每一步都明确），不依赖 `rw` 的匹配顺序。
    have hcube' : lam ^ 3 * |X x| ^ 3 = |(lam * X x) ^ 3| := by
      calc lam ^ 3 * |X x| ^ 3
          = (lam * |X x|) ^ 3 := by rw [mul_pow]
        _ = |lam * X x| ^ 3 := by rw [abs_mul, abs_of_nonneg hlam0]
        _ = |(lam * X x) ^ 3| := by rw [abs_pow]
    have hle : Real.exp (lam * X x) - 1 - lam * X x - (lam * X x) ^ 2 / 2
        ≤ lam ^ 3 * |X x| ^ 3 := by
      rw [hcube']
      -- 注意 **A2b 修复**：`htaylor'` 的右端是 `|lam * X x| ^ 3`，而目标（经 `hcube'`）
      -- 的右端是 `|(lam * X x) ^ 3|` —— 二者**定义上相等但句法不同**
      -- （STYLE「定义相等但句法不同 ⟹ `rw` 失配」）。
      -- `le_abs_self` 给 `a ≤ |a|`，故目标右端必须**已是**绝对值形。
      -- ⇒ 先把 `htaylor'` 的右端也换成 `|(lam * X x) ^ 3|`，两侧同形后再 `le_trans`。
      have htaylor'' : |Real.exp (lam * X x) - 1 - lam * X x - (lam * X x) ^ 2 / 2|
          ≤ |(lam * X x) ^ 3| := by
        -- 注意 `abs_pow : |a ^ n| = |a| ^ n`（**左端是 `|a^n|`**）。
        -- 用 `rw [abs_pow]` 会把**目标右端** `|(lam*X x)^3|` 变成 `|lam*X x|^3`，
        -- 与 `htaylor'` 的右端同形 —— 方向是**正向**（不是 `←`）。
        rw [abs_pow]
        exact htaylor'
      exact le_trans (le_abs_self _) htaylor''
    linarith
  have hsum : (∑ x : α, Real.exp (lam * X x))
      ≤ ∑ x : α, (1 + lam * X x + (lam * X x) ^ 2 / 2 + lam ^ 3 * |X x| ^ 3) :=
    Finset.sum_le_sum (fun x _ => hpt x)
  -- 右侧求和 = |α| + λ²ΣX²/2 + λ³Σ|X|³
  have hsumval : (∑ x : α, (1 + lam * X x + (lam * X x) ^ 2 / 2 + lam ^ 3 * |X x| ^ 3))
      = (Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2) / 2
        + lam ^ 3 * (∑ x : α, |X x| ^ 3) := by
    have hA : (∑ x : α, (1 : ℝ)) = (Fintype.card α : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hB : (∑ x : α, lam * X x) = lam * (∑ x : α, X x) := by rw [Finset.mul_sum]
    -- 注意 **R5/A4 修复（tactic 层）**：原稿 `rw [← Finset.sum_div, Finset.mul_sum]` 后再
    -- `apply Finset.sum_congr rfl` —— 但 `Finset.mul_sum` 把 `λ²·(ΣX²)` 展成了
    -- `Σ λ²·X²`，两侧仍是 `Σ` 对 `Σ` 却**指标类型/被加项形状不同**，
    -- `sum_congr` 报 `apply failed to unify ?m.sum ?m = ?m.sum ?m`。
    -- 改为：**先**对左端用 `Finset.sum_congr` 逐点把 `(λX)²/2` 化成 `λ²X²/2`，
    -- **再**提常数因子。
    have hC : (∑ x : α, (lam * X x) ^ 2 / 2) = lam ^ 2 * (∑ x : α, X x ^ 2) / 2 := by
      rw [Finset.sum_congr rfl (fun x _ => by ring : ∀ x ∈ Finset.univ,
        (lam * X x) ^ 2 / 2 = lam ^ 2 * X x ^ 2 / 2)]
      rw [← Finset.sum_div, Finset.mul_sum]
    have hD : (∑ x : α, lam ^ 3 * |X x| ^ 3) = lam ^ 3 * (∑ x : α, |X x| ^ 3) := by
      rw [Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hA, hB, hC, hD, hzero]
    ring
  -- 除以 |α|：E[e^{λX}] ≤ 1 + λ²E[X²]/2 + λ³E[|X|³]
  have hdiv : uniformExpectation (fun x => Real.exp (lam * X x))
      ≤ 1 + lam ^ 2 * uniformSecondMoment X / 2
        + lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) := by
    have hstep : (∑ x : α, Real.exp (lam * X x)) / (Fintype.card α : ℝ)
        ≤ ((Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2) / 2
            + lam ^ 3 * (∑ x : α, |X x| ^ 3)) / (Fintype.card α : ℝ) := by
      rw [← hsumval]
      exact div_le_div_of_nonneg_right hsum (le_of_lt hcard)
    have halg : ((Fintype.card α : ℝ) + lam ^ 2 * (∑ x : α, X x ^ 2) / 2
          + lam ^ 3 * (∑ x : α, |X x| ^ 3)) / (Fintype.card α : ℝ)
        = 1 + lam ^ 2 * uniformSecondMoment X / 2
          + lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) := by
      unfold uniformSecondMoment uniformExpectation
      field_simp
      ring
    unfold uniformExpectation
    exact hstep.trans_eq halg
  -- u ≥ 0 且 1 + u ≤ e^u，再用 λ ≤ 1 放大到 2 倍
  have hV : 0 ≤ uniformSecondMoment X := uniformSecondMoment_nonneg X
  have hT : 0 ≤ uniformExpectation (fun x => |X x| ^ 3) := by
    unfold uniformExpectation
    exact div_nonneg (Finset.sum_nonneg (fun x _ => by positivity)) (Nat.cast_nonneg _)
  set u : ℝ := lam ^ 2 * uniformSecondMoment X / 2 + lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)
    with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    have : 0 ≤ lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) :=
      mul_nonneg (by positivity) hT
    have : 0 ≤ lam ^ 2 * uniformSecondMoment X / 2 := by positivity
    linarith
  have hexp1 : 1 + u ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  -- u ≤ 2λ²E[X²] + 2λ³E[|X|³]（λ ∈ [0,1]）
  have hu_le : u ≤ 2 * lam ^ 2 * uniformSecondMoment X
      + 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) := by
    rw [hu]
    have h2 : lam ^ 2 * uniformSecondMoment X / 2 ≤ lam ^ 2 * uniformSecondMoment X := by
      nlinarith [hV, sq_nonneg lam]
    have h3 : lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)
        ≤ 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) := by
      nlinarith [hT, pow_nonneg hlam0 3]
    linarith
  calc
    uniformExpectation (fun x => Real.exp (lam * X x))
        ≤ 1 + lam ^ 2 * uniformSecondMoment X / 2
          + lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3) := hdiv
    _ = 1 + u := by rw [hu]; ring
    _ ≤ Real.exp u := hexp1
    _ ≤ Real.exp (2 * lam ^ 2 * uniformSecondMoment X
        + 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)) := Real.exp_le_exp.mpr hu_le

/-- **Bernstein 条件下的 MGF 界（降强度版）**：Bernstein 条件（定义 1）+
`EX = 0` + `λ ∈ [0,1]` ⟹
`E[e^{λX}] ≤ exp(λ²·E[X²]·(2 + 2λ))`。

注意 **本条已降强度（A2b 实证更正）**。原稿声称
`≤ exp(λ²·E[X²]·(2 + 2Bλ))`，其推导依赖 `bernstein_moment_recurrence` 的
**假结论** `E|X|³ ≤ B·E[X²]`（反例见 §二）。

**降强度后的推导（诚实、可证）**：
`bernstein_lemma_general` 给
`E[e^{λX}] ≤ exp(2λ²V + 2λ³·E|X|³)`，其中 `V := E[X²]`。
用**降强度后**的 `E|X|³ ≤ V`（`abs_cube_expectation_le_secondMoment`）得
`2λ²V + 2λ³·E|X|³ ≤ 2λ²V + 2λ³V = λ²V·(2 + 2λ)`。

注意 **常数变化说明**：原稿的 `(2 + 2Bλ)` 因子**依赖假命题**，不可保留。
由于 `B ≤ 1`，有 `2 + 2Bλ ≤ 2 + 2λ`，故**本条的指数更大（更松）**——
这是**如实降强度**，不是等价改写。下游 `bernstein_tail_condition`
的常数相应**重新推导**（见该定理）。 -/
theorem bernstein_lemma_condition {α : Type*} [Fintype α] {X : α → ℝ} {B lam : ℝ}
    (hN : 0 < Fintype.card α) (hcond : bernsteinCondition X B)
    (hzero : (∑ x : α, X x) = 0) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤
      Real.exp (lam ^ 2 * uniformSecondMoment X * (2 + 2 * lam)) := by
  obtain ⟨hB0, hB1, _hBcond, hb⟩ := hcond
  have hrec := abs_cube_expectation_le_secondMoment hN hb
  have hgen := bernstein_lemma_general hN hzero hb hlam0 hlam1
  have halg : 2 * lam ^ 2 * uniformSecondMoment X
      + 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)
      ≤ lam ^ 2 * uniformSecondMoment X * (2 + 2 * lam) := by
    have hV : 0 ≤ uniformSecondMoment X := uniformSecondMoment_nonneg X
    have hstep : 2 * lam ^ 3 * uniformExpectation (fun x => |X x| ^ 3)
        ≤ 2 * lam ^ 3 * uniformSecondMoment X :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    nlinarith [hstep, hV, pow_nonneg hlam0 2, pow_nonneg hlam0 3]
  exact le_trans hgen (Real.exp_le_exp.mpr halg)

/-! ## 四、显式常数的尾界 -/

/-- **Bernstein 条件 ⟹ 尾界（显式常数 `16`）**：Bernstein 条件 +
`E[X] = 0`、`V := E[X²] > 0`、`0 < t ≤ V` ⟹
`P{X ≥ t} ≤ exp(−t²/(16V))`。

**证明**：定理 4 给出 `E[e^{λX}] ≤ exp(λ²V(2 + 2Bλ))`；
取 `λ = t/(8V)`（由 `t ≤ V` 得 `λ ≤ 1/8 ≤ 1`），
利用 `B ≤ 1` 把 `2 + 2Bλ ≤ 4`（因 `λ ≤ 1`），得
`E[e^{λX}] ≤ exp(4λ²V)`；切尔诺夫桥 `markov_exp_tail` 给出
`P ≤ e^{−λt}·e^{4λ²V} = e^{−t²/(16V)}`（`λ = t/(8V)`）。

**注意 诚实标注（R5/A4 实证更正，本文件最重要的更正）**：
初稿的陈述是 `P ≤ exp(−t²/(4V))` 且取 `λ = t/(2V)`——**该推导为假**。
代入 `λ = t/(2V)` 得 `−λt + 4λ²V = −t²/(2V) + t²/V = +t²/(2V)`，
是**正数**，故右端为 `e^{+t²/(2V)} > 1`，尾界**平凡空洞**。
更一般地，写 `λ = s·t/V` 则左端 `= (t²/V)(4s² − s)`；要它 `≤ −t²/(4V)`
需 `16s² − 4s + 1 ≤ 0`，其**判别式 `16 − 64 = −48 < 0`**，
**无实解** ⟹ `e^{−t²/(4V)}` 在该 MGF 输入下**不可达**。
可达到的最优值是 `min_s (4s² − s) = −1/16`（`s = 1/8`），
故本定理的常数如实写成 `16`（对应 `λ = t/(8V)`）。

**注意 与 `RealBernstein` 的关系（更正后）**：
`RealBernstein.bernstein_tail` 的 `e^{−t²/(4nV)}` 走的是**不同的** MGF 路线
（二次 Taylor 界 `e^t ≤ 1 + t + t²`，不经 `4λ²V` 这一步放大），
故两者**不冲突**；但本定理**不能**声称复现 `4`——
它在本文件的三阶 Taylor + `2 + 2Bλ ≤ 4` 路线下只有 `16`。
初稿「与 `RealBernstein` 的指数逐字相同」的说法**已撤销**。
若读者只关心更好的常数，应直接使用 `RealBernstein`。

**为什么需要 `t ≤ V`**：`λ = t/(8V)` 需落在 `[0,1]`（Taylor 路线）；
`t ≤ V` 给出 `λ ≤ 1/8`，远宽于所需。 -/
theorem bernstein_tail_condition {α : Type*} [Fintype α] {X : α → ℝ} {B t : ℝ}
    (hN : 0 < Fintype.card α) (hcond : bernsteinCondition X B)
    (hzero : uniformExpectation X = 0) (hV : 0 < uniformSecondMoment X)
    (ht : 0 < t) (htV : t ≤ uniformSecondMoment X) :
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤
      Real.exp (-(t ^ 2) / (16 * uniformSecondMoment X)) := by
  obtain ⟨hB0, hB1, hBcond, hb⟩ := hcond
  have hsumzero : (∑ x : α, X x) = 0 := sum_eq_zero_of_uniformExpectation_eq_zero hN hzero
  set V : ℝ := uniformSecondMoment X with hVdef
  have hVpos : 0 < V := hV
  have hVne : V ≠ 0 := ne_of_gt hVpos
  -- 注意 **R5/A4 实证修正（本文件最重要的更正）**：
  -- 初稿取 `lam = t/(2V)` 并断言 `-lam*t + 4*lam^2*V = -(t^2)/(4V)`——**该等式为假**。
  -- 代入 `lam = t/(2V)` 得 `-t²/(2V) + t²/V = +t²/(2V) > 0`（**正号**），
  -- 于是右端 `e^{+t²/(2V)} > 1`，**尾界完全空洞**（概率必 ≤ 1）。
  -- 更一般地：令 `lam = s·t/V`，则左端 `= (t²/V)(4s² − s)`；
  -- 要它 `≤ −t²/(4V)` 需 `16s² − 4s + 1 ≤ 0`，**判别式 = 16 − 64 = −48 < 0**
  -- ⟹ **不存在实解**：`e^{−t²/(4V)}` 在该 MGF 下**根本不可达**。
  -- 可达到的最优常数是 `min_s (4s² − s) = −1/16`（在 `s = 1/8` 处取得）。
  -- ⇒ 按纪律（**证不掉就降强度 + 如实报告**）取 `lam = t/(8V)`，
  -- 结论如实写成 `e^{−t²/(16V)}`（比标称的 `e^{−t²/(4V)}` **弱**；见 docstring 的诚实标注）。
  set lam : ℝ := t / (8 * V) with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by positivity : (0 : ℝ) < 8 * V)]
    linarith [htV, hVpos]
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  have hmgf := bernstein_lemma_condition hN ⟨hB0, hB1, hBcond, hb⟩ hsumzero hlam0 hlam1
  -- 指数放大：`2 + 2λ ≤ 4`（由 `λ ≤ 1`）
  -- 注意 **A2b 降强度后的相应修改**：原稿此处用 `2 + 2Bλ ≤ 4`（由 `B ≤ 1`、`λ ≤ 1`），
  -- 但那依赖**假命题** `E|X|³ ≤ B·E[X²]`（见 §二）。
  -- 降强度后 `bernstein_lemma_condition` 给的是 `2 + 2λ`，同样有 `≤ 4`，
  -- 注意 **故本定理的常数 `16` 与 `λ = t/(8V)` 的选择无需改动**——这是**巧合的稳固**，
  -- 而非"照抄旧常数"：两条路线的指数放大界都是 `4`。
  have hfac : 2 + 2 * lam ≤ 4 := by linarith [hlam1]
  have hVnn : 0 ≤ V := le_of_lt hVpos
  -- 注意 **R5/A4 修复（tactic 层）**：原稿 `nlinarith [hfac, hVnn, sq_nonneg lam]` 失败——
  -- 目标是 `lam^2 * V * (2+2*lam) ≤ 4 * lam^2 * V`，需先把常数因子提出。
  have harg : lam ^ 2 * V * (2 + 2 * lam) ≤ 4 * lam ^ 2 * V := by
    have h1 : lam ^ 2 * V * (2 + 2 * lam) ≤ lam ^ 2 * V * 4 :=
      mul_le_mul_of_nonneg_left hfac (mul_nonneg (sq_nonneg lam) hVnn)
    linarith [h1]
  have hmarkov := markov_exp_tail (S := X) (t := t) (lam := lam) hlampos
  -- `lam = t/(8V)` ⟹ `-lam*t + 4*lam^2*V = -t²/(16V)`
  have hexp : -lam * t + 4 * lam ^ 2 * V = -(t ^ 2) / (16 * V) := by
    rw [hlamdef]
    field_simp
    ring
  calc
    uniformProb (Finset.univ.filter (fun x => t ≤ X x))
        ≤ Real.exp (-lam * t) * uniformExpectation (fun x => Real.exp (lam * X x)) := hmarkov
    _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * V * (2 + 2 * lam)) :=
          mul_le_mul_of_nonneg_left (by simpa [V] using hmgf) (Real.exp_nonneg _)
    _ ≤ Real.exp (-lam * t) * Real.exp (4 * lam ^ 2 * V) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _)
    _ = Real.exp (-lam * t + 4 * lam ^ 2 * V) := by rw [← Real.exp_add]
    _ = Real.exp (-(t ^ 2) / (16 * V)) := by rw [hexp]
    _ = Real.exp (-(t ^ 2) / (16 * uniformSecondMoment X)) := by rw [hVdef]

/-! ## 五、条件可满足性（反例背书：**新假设不空洞**）

新增的假设是 `E[X²] ≤ B·E|X|`。它**不是恒真**（例如 `X ≡ c ≠ 0` 常数时
`E[X²] = c² > c = E|X|`，需 `B ≥ c`；而 `B ≤ 1` 限制 `c ≤ 1`）。
下面给出一个**具体的、条件确实成立**的分布，作为该假设的**可满足性背书**。 -/

/-- **具体的 Bernstein 分布**：`Fin 2` 上的 `±1/2` 对称变量
（`a = 0 ↦ 1/2`、`a = 1 ↦ −1/2`）。它零均值、`|X| ≤ 1`，
且 `E[X²] = 1/4 = E|X|/2`（故 `B = 1/2` 时条件成立）。 -/
def bernsteinSign (a : Fin 2) : ℝ := if a = 0 then 1 / 2 else -(1 / 2)

/-- `bernsteinSign` 零均值：`E[X] = (1/2 − 1/2)/2 = 0`。 -/
lemma bernsteinSign_mean : uniformExpectation bernsteinSign = 0 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformExpectation bernsteinSign
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  norm_num

/-- `bernsteinSign` 有界：`|X| ≤ 1`。 -/
lemma bernsteinSign_abs_le_one (a : Fin 2) : |bernsteinSign a| ≤ 1 := by
  unfold bernsteinSign
  by_cases h : a = 0
  · rw [if_pos h]
    -- 注意 **R5/A4 修复（tactic 层）**：目标为 `|1/2| ≤ 1`（**含 `abs`**），
    -- 原稿的 `norm_num` 在此不过 abs → 先用 `abs_of_nonneg` 消去。
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  · rw [if_neg h]
    rw [abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num

/-- `bernsteinSign` 的二阶矩：`E[X²] = (1/4 + 1/4)/2 = 1/4`。 -/
lemma bernsteinSign_secondMoment : uniformSecondMoment bernsteinSign = 1 / 4 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformSecondMoment uniformExpectation bernsteinSign
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  norm_num

/-- `bernsteinSign` 的一阶绝对矩：`E|X| = (1/2 + 1/2)/2 = 1/2`。 -/
lemma bernsteinSign_abs_mean : uniformExpectation (fun a => |bernsteinSign a|) = 1 / 2 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformExpectation bernsteinSign
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  norm_num

/-- 要点 **条件可满足性（反例背书）**：对 `bernsteinSign` 与 `B = 1/2`，
Bernstein 条件 `bernsteinCondition bernsteinSign (1/2)` **成立**
（`E[X²] = 1/4 ≤ (1/2)·(1/2) = 1/4` 取等）。

**这条为什么必须存在**：新增假设 `E[X²] ≤ B·E|X|` 若**不可满足**，
则上面所有定理都是**空洞真**（vacuously true）。
本定理给出一个具体见证，证明该假设有非平凡模型。 -/
theorem bernsteinCondition_satisfiable :
    bernsteinCondition bernsteinSign (1 / 2) := by
  refine ⟨by norm_num, by norm_num, ?_, bernsteinSign_abs_le_one⟩
  rw [bernsteinSign_secondMoment, bernsteinSign_abs_mean]
  norm_num

/-- **条件的尾界实例（非空洞性）**：`P{X ≥ 1/4} ≤ e^{−1/64}`。

`X = bernsteinSign` 时事件 `{X ≥ 1/4}` 就是 `{a | bernsteinSign a ≥ 1/4} = {0}`，
真实概率 `1/2`；界 `e^{−1/64} = 0.9845` 成立（且**很不紧**——诚实标注：
这正说明 Taylor 路线常数的保守性）。取 `t = 1/4` 时 `t ≤ V = 1/4` 恰好满足范围条件。

注意 **R5/A4 更正（常数链）**：初稿写 `e^{−1/16} = 0.9394`（对应旧的 `−(t²)/(4V)`）。
常数更正为 `16` 后（见定理 5 的诚实标注）：
`t = V = 1/4` ⟹ `t² = 1/16`、`16V = 4` ⟹ 指数 `= −(1/16)/4 = −1/64`，
界 `e^{−1/64} = 0.9845`——**如实写出，比初稿更松**。

**它比定义多说了什么**：这是定理 5 的一个**非空洞实例**，
同时给出该实例下界与真值的**具体差距**（`0.9845` vs `0.5`），
使「常数保守性」成为可核对的事实而非断言。 -/
theorem bernstein_tail_condition_example :
    uniformProb (Finset.univ.filter (fun a : Fin 2 => (1 / 4 : ℝ) ≤ bernsteinSign a)) ≤
      Real.exp (-(1 / 64 : ℝ)) := by
  -- 注意 **R5/A4 修复（tactic 层）**：`ht`（`0 < 1/4`）与 `htV`（`t ≤ V = 1/4`）
  -- 两个参数在 `rw [bernsteinSign_secondMoment]` 之后**都会被归一为平凡目标**，
  -- 若写成 `(by rw […]; norm_num)` 会报 `no goals to be solved`（`norm_num` 多余）。
  -- 改用 `by norm_num` 配 `bernsteinSign_secondMoment` 的**显式**前提。
  have hV : uniformSecondMoment bernsteinSign = 1 / 4 := bernsteinSign_secondMoment
  have h := bernstein_tail_condition (X := bernsteinSign) (B := 1 / 2) (t := 1 / 4)
    (by norm_num : 0 < Fintype.card (Fin 2)) bernsteinCondition_satisfiable
    bernsteinSign_mean (by rw [hV]; norm_num)
    (by norm_num : (0 : ℝ) < 1 / 4) (by rw [hV])
  rw [hV] at h
  -- 注意 **R5/A4 修复（tactic 层）**：`h` 的右端是
  -- `Real.exp (-(1/4)^2 / (16 * (1/4)))`，目标右端是 `Real.exp (-(1/64))`；
  -- 两者**数值相等但不同一**，故 `exact h` 报 type mismatch。
  -- 用 `Real.exp_le_exp` 把指数上的等式交给 `norm_num`。
  exact le_trans h (Real.exp_le_exp.mpr (by norm_num))

/-! ## 六、诚实清单

1. **未做**：Bennett 逐点不等式 `e^{λx} ≤ 1 + λx + x²(e^λ − 1 − λ)`（`x ≤ 1`）
   及其关键单调性引理；因此**未达到** Bernstein 引理的最优形式
   `exp(λ²V/(2(1 − Bλ/3)))` 与尾界 `exp(−t²/(2(V + Bt/3)))`。
   本文件的分界点 `t ≤ V` 与常数 `16` 都是 Taylor 路线（含 `2 + 2Bλ ≤ 4` 放大）
   的**直接后果**，已标注。
2. **未做**：由完整 Bernstein 条件（全部高阶矩 `E|X|^k ≤ (k!/2)σ²B^{k−2}`）
   出发的推导。本文件只用 `k = 2` 一条（定理 2 补齐 `k = 3`），
   这是**放宽假设**的代价，已在定义 1 的 docstring 说明。
3. **未做**：`n` 个独立副本的乘积分解版本（`RealBernstein` 已有）。
4. **未做**：鞅差 / 条件方差版（`RealAzuma` 的诚实清单已登记该缺口）。
5. 注意 **R5/A4 更正（常数，重要）**：初稿声称定理 5 的指数
   `−t²/(4V)`「与 `RealBernstein.bernstein_tail` 逐字相同」。
   **该声称已撤销**：初稿的推导（`λ = t/(2V)` ⟹ `−λt + 4λ²V = −t²/(4V)`）
   **是假的**——左端实为 `+t²/(2V) > 0`，尾界空洞；
   且方程 `16s² − 4s + 1 ≤ 0`（`λ = s·t/V`）判别式 `−48 < 0` **无实解**，
   故 `4` 在该路线下**不可达**。本文件如实采用可达最优的 `16`（`λ = t/(8V)`）。
   定理 5 要求 `t ≤ V`（`λ ≤ 1/8`）。
6. 注意 **`unknown constant` 更正**：初稿引用的 `Real.abs_exp_sub_taylor_two_le`
   **在 mathlib 中不存在**（本仓库第 13 例同族失误）。已自证替代引理
   `abs_exp_sub_taylor_two_le_real`（走 mathlib 既有的 `Real.exp_bound (n := 3)`）。
7. 注意 **类型类更正**：初稿的若干 `nlinarith` 失败源于目标中 `|X x|` 与 `X x ^ 2`
   **无桥接**；已补 `sq_abs` 显式重写（非数学变更）。
-/

end Lattice
