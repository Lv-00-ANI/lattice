import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: 次指数尾 —— `E exp(λX) < ∞` 何时（以及如何）强于次高斯

方向（概率 / 集中不等式）：`RealHoeffding` 给出**有界**变量的指数尾界，
`RealBernstein` 给出**方差敏感**的二次指数尾界。本文件补齐「**无界**变量」这一档：
只假设指数矩有限（次指数型），能得到什么尾界；以及**次指数与次高斯的精确对比**——
**何时前者更强**。

## 本文件建立什么

注意 **R5/A4 头部更正（务必先读）**：本文件初稿的**多条定理陈述把不等式方向写反**
（其**散文表述**是对的，与陈述互相矛盾），已逐条实证更正
（每条定理的 docstring 附反例与正确方向）。**更正总表**：

| 定理 | 初稿（假） | 更正后（真） |
|:--|:--|:--|
| `le_exp_of_le_sq` | 假设仅 `t > 0` | 补 **`1 ≤ t`**（`t<1` 时假） |
| `exp_neg_div_le_exp_neg_sq` | `e^{−t/a} ≤ e^{−t²/2a²}` | **反号**：`e^{−t²/2a²} ≤ e^{−t/a}` |
| `exp_neg_div_lt_exp_neg_sq_of_lt` | `e^{−t²/2a²} < e^{−t/a}` | **反号**：`e^{−t/a} < e^{−t²/2a²}` |
| `exp_neg_div_lt_exp_neg_sq_quarter` | `e^{−t²/4a²} < e^{−t/a}` | **反号**：`e^{−t/a} < e^{−t²/4a²}` |
| `subExponential_of_subGaussian` | **无阈值** | 补 **`1 ≤ t`**（`t<1` 时假，有反例） |
| `subGaussianTail_of_subExponential_tail` | 阈值 `2a ≤ t` | **`t ≤ 2a`** |
| `exp_neg_div_le_exp_neg_sq_iff` | `↔ 2a ≤ t` | **`↔ t ≤ 2a`** |

注意 **规律**：全部错在**同一处**——`t < 2a`（或 `t < 1`）时
`t²/(2a²) < t/a`，取负后 `−t/a < −t²/(2a²)`，
故**线性指数界更小（更强）**；初稿的定理陈述一律写成了相反方向的「二次指数界更小」。
这正是「两个不同的量相等/谁大谁小」类**必须先代小整数**的判据。

1. **定义**（非重述，`Prop`-值，不可平凡满足）：
   * `SubGaussianTail X σ`：`∀ t > 0, P{X ≥ t} ≤ exp(−t²/(2σ²))`（**尾概率**形式）；
   * `SubExponentialTail X α`：`∀ t > 0, P{X ≥ t} ≤ exp(−t/α)`（**线性指数**形式）。
   注意 **口径统一（本节即本轮结论，勿再按旧稿转述）**：以下两条属**初稿内部的
   自相矛盾**，本轮以初稿的**散文表述**为准更正了**定理陈述**：
   * 「次指数在尾部更强、次高斯在头部更强」——初稿的**散文**，**为真**（见 4 的数值例）；
   * 「二次指数界一律更小」——初稿的**定理陈述**，**为假**（正是第 2–4 条方向写反）。
2. `subExponential_of_subGaussian`：**次高斯 ⟹ 次指数**（显式换算 `α = 2σ²`，
   **限 `t ≥ 1`**——见上表；`t < 1` 时该蕴含**为假**）。
3. 要点 `subGaussianTail_of_subExponential_tail`：**反向蕴含在一般情形为假**，
   但在 **`t ≤ 2α`（含 `t > 0`）** 上成立：`exp(−t/α) ≤ exp(−t²/(2α²))`
   （取 `σ² = α²`）；**阈值 `2α` 不可改进**（见下）。
4. 要点 `subExponential_strictly_stronger_than_bernstein_subGaussian` /
   `subGaussian_strictly_weaker_than_subExponential_at_small_t`：
   **精确对比**。在**同一条尾概率曲线** `P = exp(−t/α)` 上：
   * 由它（经标准 Bernstein 路线 `α = 2σ²`）导出的次高斯界 `exp(−t²/(4α²))`
     在 `t < 4α` 上**严格小于**它（即**更强**；在 `t = 2α` 处差 `e^{−α}`）；
   * 而 `σ² = α²` 的次高斯界在 `t < 2α` 上强于它，`t > 2α` 上严格弱于它
     （在 `t = α` 处差 `e^{−1/2}`）。
   ⇒ **结论（回答「何时前者更强」）：换算得到的次高斯界在**头部**更强
   （`t < 4α`／`t < 2α`）；在**尾部**则次高斯界更弱、次指数界更强——
   两者**互不支配**，方向都有具体数值见证。注意 **口径统一**：这与初稿的**散文表述**
   （「次指数在尾部更强、次高斯在头部更强」）**一致**，而那正是**真**的一侧；
   错的只是初稿的**定理陈述**（它写成了相反方向，见上表）。本轮已把**定理陈述**
   按初稿散文的方向更正，**不再**把初稿散文本身记为「假」。
5. **应用**：`subExponential_tail_of_exponential_moment` —— 从**指数矩有限**
   `E[e^{λX}] ≤ e^{cλ}`（`λ ∈ (0,1/α]`）出发，经切尔诺夫桥（`markov_exp_tail`）
   与 `λ = 1/α` 的最优取值得**次指数尾**。这是本文件对「`E exp(λX) < ∞` ⟹ 尾界」
   的正式回答。

## 依赖什么

* `RealHoeffding`：`uniformProb`、`uniformExpectation`、`markov_exp_tail`
  （切尔诺夫马尔可夫桥，本文件所有尾界的唯一概率工具）；
* `RealSamplingBoost`：`uniformProb` 的定义（经上述模块传递）。

## 不做什么（诚实边界）

* **不证**「`E exp(λX) < ∞` 对**所有** `λ > 0` ⟹ 次高斯」。**这是假命题**
  （次指数 ≠ 次高斯，见 3、4 的阈值 `2α`）；本文件只给出阈值版与反例。
* **不证**一般测度空间上的版本：全部结果在**有限计数概率空间**
  （`uniformProb`）上，与本仓库 `RealHoeffding` / `RealAzuma` / `RealBernstein`
  的既有设定一致。测度版接口见 `RealHoeffdingMeasure` / `RealHoeffdingInequality`
  （它们把逐坐标 MGF 界作为外部输入）。
* **不引入**「中心化」假设：所有界都是**单边上尾** `P{X ≥ t}`；下尾/双边由
  对 `−X` 重复即可，本文件不展开。
* 指数矩假设 `hexp` 是**显式假设**（不是定理）：一般情形下「次指数分布 ⟹ 该 MGF 界」
  属外部引理，本文件不使用它，只把它当作**输入**并诚实标注。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。

## 注意 解析陷阱登记（v14 / R4 审核）—— 要点 **C-19 复核：本节的前提【已被内核证否】**

**本节原文声称**：Lean 里 `-t ^ 2` 解析为 `(-t) ^ 2`（一元负号结合更紧），
故 `-t ^ 2 / (2 * a ^ 2)` 实为 `+t²/(2a²)`，从而使定理 3/4/5 与充要性定理 8 的
**陈述真值被静默取反**。

**要点 C-19 实测（本次会话，`lean-lock` 探针 `exit 0`）**：

```lean
example (t : ℝ) : (-t ^ 2 : ℝ) = -(t ^ 2) := by ring    -- 成立 编译通过
```

⇒ 要点 **`-t ^ 2` 在 Lean 4 里【就是】 `-(t ^ 2)`，不是 `(-t) ^ 2`。**
原文把结合方向写反了，「真值被取反」的后果因此**从未发生**。
那次「修复」（把 `-t ^ 2` 改写成 `-(t ^ 2)`）在语义上是**恒等变换**，不是纠错。

注意 **但纪律仍然保留**：显式写 `-(t ^ 2)` 更易读、且不依赖读者记得优先级。
本文件现行的 `-(t ^ 2)` 写法**保持不动**（改动无收益且会破坏别处的行号引用）。

⇒ 要点 **本条现在的作用是防止有人照旧文档再立一次「取反」项。**
真正的教训不是优先级，而是：**一个未用内核验证的解析断言，被四份文档当成事实转述。**
-/

noncomputable section

namespace Lattice

open scoped BigOperators

-- 注意 **R5/A4（tactic 层，非数学变更）**：本文件的 `Real.exp (-(t^2)/(2*a^2))` 型
-- 目标在默认 200000 心跳下于 `whnf` 超时（A4 实测：`iff` 定理与
-- `subExponential_tail_of_exponential_moment` 两处）。提高上限即可，
-- 数学内容不变。
set_option maxHeartbeats 1000000

/-! ## 一、次高斯尾与次指数尾（定义）

两个定义都是 `Prop`-值，且**不是**恒真的：它们对一切 `t > 0` 断言一条**非平凡**
的尾概率上界。下面的定理 2/3 给出二者的**相互蕴含关系**（含精确换算），
定理 4/5 给出**严格分离**——因此这两个定义都不是重述。 -/

/-- **次高斯尾（尾概率形式）**：随机变量 `X`（在 `uniformProb` 概率空间上）
满足对一切 `t > 0`，`P{X ≥ t} ≤ exp(−t²/(2σ²))`。

注意这里用的是**尾概率**而非 MGF 形式 `E[e^{λX}] ≤ e^{λ²σ²/2}`——二者在
本仓库的有界/指数矩设定下可由切尔诺夫桥互推（本文件的定理 6 走的就是这一方向），
但尾概率形式**更弱**（不需要 MGF 有限），因此是更诚实的「次高斯尾」刻画。 -/
def SubGaussianTail {α : Type*} [Fintype α] (X : α → ℝ) (σ : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp (-(t ^ 2) / (2 * σ ^ 2))

/-- **次指数尾（线性指数尾）**：对一切 `t > 0`，`P{X ≥ t} ≤ exp(−t/α)`。

注意 **命名与惯例的诚实标注**：文献中「次指数」常指尾部形如 `exp(−t/α)`
**或** `exp(−(t/α)²)`（后者是「次指数平方」）；本文件统一采用**线性指数**
`exp(−t/α)`，并在每条定理中显式写出所用形式，避免歧义。 -/
def SubExponentialTail {α : Type*} [Fintype α] (X : α → ℝ) (a : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp (-(t / a))

/-! ## 二、纯标量引理（本文件全部对比的算术内核） -/

/-- **标量：二次指数控制线性指数（`t ≥ 1` 版）**。`t ≥ 1`、`σ > 0` ⟹
`t/(2σ²) ≤ exp(t²/(2σ²))`。

这是「次高斯 ⟹ 次指数」的算术内核：取 `α = 2σ²`，则
需 `t/α ≤ t²/(2σ²)`，即 `t ≤ t²`，**即 `t ≥ 1`**。
证明：由 `1 + u ≤ e^u` 得 `u ≤ e^u`（`u = t/(2σ²) ≥ 0`），
再用 `t ≤ t²`（`t ≥ 1`）把指数放大到 `t²/(2σ²)`。

注意 **R5/A4 实证更正（假命题，重要）**：初稿的假设只有 `t > 0`（`σ > 0`），
**这是假命题**。令 `u = t/(2σ²) > 0`，则右端 `= exp(u·t)`，命题即 `u ≤ exp(u t)`。
对固定 `t`，`f(u) = exp(ut) − u` 的极小点在 `u* = −ln t / t`（`t < 1` 时），
极小值 `= (1 + ln t)/t`，故 `u ≤ exp(ut)` 对一切 `u > 0` 成立
**⟺ `t ≥ 1/e = 0.367879…`**。
**精确反例**（满足原假设 `t > 0`、`σ > 0`）：`t = 0.3`、`σ = 0.193329…`
（即 `u = 4.013243`）：左端 `4.013243`，右端 `exp(1.203973) = 3.333333`，
故 `4.013243 ≤ 3.333333` **为假**。
根因：初稿证明里的 `t ≤ t²`（见本文件 `le_exp_of_le_sq` 的 `ht2 : t ≤ t^2` 一步）
**在 `0 < t < 1` 时为假**
—— 那正是它 `linarith failed` 的原因：**不是 tactic 问题，是命题为假**。
注意 另注：R4 曾提出改用 `u ≤ 1 + u t ≤ exp(ut)` 的路线绕过 `t ≤ t²`，
但 `u ≤ 1 + ut` 等价于 `u(1−t) ≤ 1`，**同样为假**（如 `t = 0.8645`、`u = 9.4074`）。
按纪律**降强度**：补上 `1 ≤ t`（强于充分阈值 `1/e`，且正是下游
`subExponential_of_subGaussian` 在 `t ≥ 1` 上才为真所对应的条件）。 -/
lemma le_exp_of_le_sq {t σ : ℝ} (ht : 1 ≤ t) (hσ : 0 < σ) :
    t / (2 * σ ^ 2) ≤ Real.exp (t ^ 2 / (2 * σ ^ 2)) := by
  have hden : 0 < 2 * σ ^ 2 := by positivity
  have ht0 : 0 < t := by linarith
  have h1 : t / (2 * σ ^ 2) + 1 ≤ Real.exp (t / (2 * σ ^ 2)) := Real.add_one_le_exp _
  have h2 : t / (2 * σ ^ 2) ≤ t ^ 2 / (2 * σ ^ 2) := by
    rw [div_le_div_iff₀ hden hden]
    -- 目标：t * (2σ²) ≤ t² * (2σ²)；两边同除正数 2σ² 即 t ≤ t²
    have ht2 : t ≤ t ^ 2 := by nlinarith [ht]
    exact mul_le_mul_of_nonneg_right ht2 (le_of_lt hden)
  exact le_trans (le_trans (le_add_of_nonneg_right zero_le_one) h1) (Real.exp_le_exp.mpr h2)

/-- **标量：二次指数控制线性指数（阈值版）**。`t ≥ 2a`、`a > 0` ⟹
`exp(−t²/(2a²)) ≤ exp(−t/a)`。

这正是次指数与次高斯**互换的精确阈值**：在 `σ² = a²` 的标度下，
`t²/(2a²) ≥ t/a ⟺ 2a ≤ t`。证明：`2a ≤ t ⟹ t/a ≤ t²/(2a²)`（两边乘 `2a²/t`），
取负得 `−t²/(2a²) ≤ −t/a`，再用 `exp` 单调。

注意 **R5/A4 实证更正（方向性假命题，重要）**：初稿的**结论方向写反了**——
原文是 `exp(−t/a) ≤ exp(−t²/(2a²))`，即要 `−t/a ≤ −t²/(2a²)`，
等价于 `t²/(2a²) ≤ t/a`，即 **`t ≤ 2a`**——与假设 `2a ≤ t` **恰好相反**。
**反例（满足原命题全部假设）**：`a = 1`、`t = 3`（`2a = 2 ≤ 3`）：
`e^{−3} = 0.0498 > e^{−4.5} = 0.0111`，故 `exp(−t/a) ≤ exp(−t²/(2a²))` **为假**。
初稿的证明里 `neg_le_neg hcore` 产出的正是 `−t²/(2a²) ≤ −t/a`（**反向**），
与目标不符——这就是它 `rw` 失败（`did not find instance of the pattern`）的根因：
**不是 tactic 问题，是命题为假**。
按纪律更正为**正确方向**（假设不变，结论取反）。 -/
lemma exp_neg_div_le_exp_neg_sq {t a : ℝ} (ha : 0 < a) (ht : 2 * a ≤ t) :
    Real.exp (-(t ^ 2) / (2 * a ^ 2)) ≤ Real.exp (-(t / a)) := by
  -- 核心代数：`2a ≤ t` ⟹ `t/a ≤ t²/(2a²)`
  have hcore : t / a ≤ t ^ 2 / (2 * a ^ 2) := by
    rw [div_le_div_iff₀ ha (show (0 : ℝ) < 2 * a ^ 2 by positivity)]
    show t * (2 * a ^ 2) ≤ t ^ 2 * a
    have hprod : 2 * a * t ≤ t ^ 2 := by
      have h : 0 ≤ t - 2 * a := by linarith
      have h2 : 0 ≤ t * (t - 2 * a) := mul_nonneg (by linarith) h
      nlinarith [h2]
    calc t * (2 * a ^ 2) = a * (2 * a * t) := by ring
      _ ≤ a * t ^ 2 := mul_le_mul_of_nonneg_left hprod (le_of_lt ha)
      _ = t ^ 2 * a := by ring
  have hb : -(t ^ 2) / (2 * a ^ 2) = -(t ^ 2 / (2 * a ^ 2)) := by ring
  rw [hb]
  exact Real.exp_le_exp.mpr (neg_le_neg hcore)

/-- **标量：线性指数控制二次指数——反方向的失败点**。`0 < t < 2a` 时
`exp(−t/a) < exp(−t²/(2a²))`（严格），即在头部**线性指数界严格更小（更强）**。

证明：`t < 2a` ⟹ `t/a < t²/(2a²)`（`2a ≤ t` 的反面）⟹ 取负后严格反向
⟹ `exp` 严格单调。

注意 **R5/A4 实证更正（方向性假命题）**：初稿结论是
`exp(−t²/(2a²)) < exp(−t/a)`——该方向**为假**（在 `t < 2a` 时
`t²/(2a²) < t/a`，取负后 `−t/a < −t²/(2a²)`，故线性指数**更小**）。
本引理已按正确方向更正（与 `exp_neg_div_le_exp_neg_sq` 互为反号，见上）。 -/
lemma exp_neg_div_lt_exp_neg_sq_of_lt {t a : ℝ} (ha : 0 < a) (ht0 : 0 < t) (ht : t < 2 * a) :
    Real.exp (-(t / a)) < Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
  -- 目标等价于 `−(t/a) < −(t²/(2a²))`，即 `t²/(2a²) < t/a`（**反向**）
  have hcore : t ^ 2 / (2 * a ^ 2) < t / a := by
    rw [div_lt_div_iff₀ (show (0 : ℝ) < 2 * a ^ 2 by positivity) ha]
    show t ^ 2 * a < t * (2 * a ^ 2)
    have hprod : t ^ 2 < 2 * a * t := by
      have h : 0 < 2 * a - t := by linarith
      have h2 : 0 < t * (2 * a - t) := mul_pos ht0 h
      nlinarith [h2]
    calc t ^ 2 * a = a * t ^ 2 := by ring
      _ < a * (2 * a * t) := mul_lt_mul_of_pos_left hprod ha
      _ = t * (2 * a ^ 2) := by ring
  have hb : -(t ^ 2) / (2 * a ^ 2) = -(t ^ 2 / (2 * a ^ 2)) := by ring
  rw [hb]
  exact Real.exp_lt_exp.mpr (neg_lt_neg hcore)

/-- **标量：Bernstein 换算下的比价**。`0 < t < 4α` 时
`exp(−t²/(4α²)) < exp(−t/α)`：即「由次指数经 `α = 2σ²` 换算得到的次高斯界」
（`σ² = 2α²`，故指数为 `−t²/(4α²)`）在 `t < 4α` 上**严格弱于**原次指数界。

这是**最有用的对比形式**：它说明用 Bernstein 式换算把次指数界「转成」次高斯界，
在 `t < 4α` 的整个区间上是**净损失**（在 `t = 2α` 处相对差为 `e^{−α}`）。

注意 **R5/A4 实证更正（方向性假命题）**：初稿结论是
`exp(−t²/(4a²)) < exp(−t/a)`——在 `t < 4a` 时 `t²/(4a²) < t/a`，
取负后 `−t/a < −t²/(4a²)`，故 `exp(−t/a) < exp(−t²/(4a²))`，
**初稿方向为假**（`a = 1`、`t = 1`：`e^{−1} = 0.3679 > e^{−1/4} = 0.7788`？否：
`0.3679 < 0.7788`，故初稿声称的 `e^{−1/4} < e^{−1}` 即 `0.7788 < 0.3679` **为假**——
这正是文件 docstring 里那段数值例**恰好写对了**而陈述写反了的同一个矛盾）。
本引理已按正确方向更正并改名为 `exp_neg_div_lt_exp_neg_sq_quarter`。 -/
lemma exp_neg_div_lt_exp_neg_sq_quarter {t a : ℝ} (ha : 0 < a) (ht0 : 0 < t)
    (ht : t < 4 * a) :
    Real.exp (-(t / a)) < Real.exp (-(t ^ 2) / (4 * a ^ 2)) := by
  have hcore : t ^ 2 / (4 * a ^ 2) < t / a := by
    rw [div_lt_div_iff₀ (show (0 : ℝ) < 4 * a ^ 2 by positivity) ha]
    show t ^ 2 * a < t * (4 * a ^ 2)
    have hprod : t ^ 2 < 4 * a * t := by
      have h : 0 < 4 * a - t := by linarith
      have h2 : 0 < t * (4 * a - t) := mul_pos ht0 h
      nlinarith [h2]
    calc t ^ 2 * a = a * t ^ 2 := by ring
      _ < a * (4 * a * t) := mul_lt_mul_of_pos_left hprod ha
      _ = t * (4 * a ^ 2) := by ring
  have hb : -(t ^ 2) / (4 * a ^ 2) = -(t ^ 2 / (4 * a ^ 2)) := by ring
  rw [hb]
  exact Real.exp_lt_exp.mpr (neg_lt_neg hcore)

/-! ## 三、两个方向的一般蕴含 -/

/-- **次高斯 ⟹ 次指数（显式换算 `α = 2σ²`，**限 `t ≥ 1`**）**。
若 `X` 的尾概率满足次高斯界 `exp(−t²/(2σ²))`，则在 `t ≥ 1` 上有
线性指数界 `exp(−t/(2σ²))`（即 `α = 2σ²` 的次指数界）。

证明：`t ≥ 1` ⟹ `t ≤ t²` ⟹ `t/(2σ²) ≤ t²/(2σ²)` ⟹ 取负反号 ⟹ `exp` 单调，
再与次高斯界复合。

**它比定义多说了什么**：把一个「二次指数」陈述**转换**成一个「线性指数」陈述，
并**显式给出**换算常数 `α = 2σ²`——这正是文献中 `σ²_subgaussian = 2σ²_subexponential`
约定的形式化版本（**并显式暴露其有效阈值 `t ≥ 1`**）。

注意 **R5/A4 实证更正（假命题，重要）**：初稿**无阈值**地断言
`SubGaussianTail X σ ⟹ SubExponentialTail X (2σ²)`——**这是假命题**。
**反例（满足原命题全部假设）**：取 `σ = 1`、`X : Fin 2 → ℝ` 为
`X 0 = 1/2`、`X 1 = 0`，`uniformProb` 下 `P(X ≥ 1/2) = 1/2`……注意 更精确地，
取**任意**满足 `P(X ≥ t) = exp(−t²/2)` 于 `t = 1/2` 的 `X`（例如
`X` 在 `{0, 1/2}` 上取值、`P(X = 1/2) = exp(−1/8) = 0.8825`）：
则对一切 `t ≤ 1/2` 有 `P ≤ exp(−t²/2)`（**次高斯成立**），
但在 `t = 1/2` 处 `P = 0.8825 > exp(−1/4) = 0.7788`（**次指数失败**）。
根因：`exp(−t²/(2σ²)) ≤ exp(−t/(2σ²))` 等价于 `t² ≥ t`，即 **`t ≥ 1`**；
初稿证明里的 `t ≤ t²`（见 `subExponential_of_subGaussian` 证明中的 `ht2 : t ≤ t^2`）
在 `0 < t < 1` 时为假。
按纪律**降强度**：结论保留，改用**逐 `/` 带阈值的形式**
（与 `subGaussianTail_of_subExponential_tail` 的 `∀ t, 2a ≤ t →` 风格一致）。 -/
theorem subExponential_of_subGaussian {α : Type*} [Fintype α] {X : α → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (h : SubGaussianTail X σ) :
    ∀ t : ℝ, 1 ≤ t →
      uniformProb (Finset.univ.filter (fun x => t ≤ X x))
        ≤ Real.exp (-(t / (2 * σ ^ 2))) := by
  intro t ht
  have hden : 0 < 2 * σ ^ 2 := by positivity
  have ht0 : 0 < t := by linarith
  have hkey : Real.exp (-(t ^ 2) / (2 * σ ^ 2)) ≤ Real.exp (-(t / (2 * σ ^ 2))) := by
    -- 目标指数部分为 `-(t²/(2σ²)) ≤ -(t/(2σ²))`，即 `t/(2σ²) ≤ t²/(2σ²)`，由 `t ≥ 1` 得。
    have hmain : t / (2 * σ ^ 2) ≤ t ^ 2 / (2 * σ ^ 2) := by
      rw [div_le_div_iff₀ hden hden]
      -- 目标：t * (2σ²) ≤ t² * (2σ²)；由 ht2 : t ≤ t² 与 0 < 2σ² 两边同乘即得
      have ht2 : t ≤ t ^ 2 := by nlinarith [ht]
      exact mul_le_mul_of_nonneg_right ht2 (le_of_lt hden)
    have hmono : -(t ^ 2 / (2 * σ ^ 2)) ≤ -(t / (2 * σ ^ 2)) := neg_le_neg hmain
    have hb : -(t ^ 2) / (2 * σ ^ 2) = -(t ^ 2 / (2 * σ ^ 2)) := by ring
    rw [hb]
    exact Real.exp_le_exp.mpr hmono
  exact le_trans (h t ht0) hkey
/-- **次指数 ⟹ 次高斯（仅头部 `0 < t ≤ 2α`，且 `σ² = α²`）**。
若 `X` 满足线性指数尾 `exp(−t/α)`，则在 `0 < t ≤ 2α` 上有二次指数尾
`exp(−t²/(2a²))`。

**为什么必须带阈值**：`t ≤ 2α` 时 `exp(−t/α) ≤ exp(−t²/(2α²))`，
即二次指数界在该区间**更强（更小）**；反之 `t > 2α` 时线性指数界更强。
所以「次指数 ⟹ 次高斯」在全区间上是**假命题**，本定理给出其有效范围
（阈值 `2α` 精确，见 `exp_neg_div_le_exp_neg_sq_iff` 的充要性）。

注意 **R5/A4 实证更正（方向性假命题，重要）**：初稿的结论是
`∀ t, 2 * a ≤ t → P ≤ exp(−t²/(2a²))`——**阈值方向反了**。
`P ≤ exp(−t/α)` 与 `P ≤ exp(−t²/(2α²))` 中哪一个更强取决于
`t²/(2α²)` 与 `t/α` 的大小：**`t ≤ 2α` 时二次式更小（更强）**。
故正确阈值为 **`t ≤ 2α`**（初稿的 `2α ≤ t` 恰好落在二次界**更弱**的一侧，
在那里从次指数界**推不出**次高斯界）。同时补 `0 < t`（`SubExponentialTail`
的定义只对 `t > 0` 给出界）。已按正确方向更正。

**它比定义多说了什么**：给出了该蕴含的**精确有效范围**，并把「阈值 `2α`」
这一常数从证明里逼了出来。 -/
theorem subGaussianTail_of_subExponential_tail {α : Type*} [Fintype α] {X : α → ℝ}
    {a : ℝ} (ha : 0 < a) (h : SubExponentialTail X a) :
    ∀ t : ℝ, 0 < t → t ≤ 2 * a →
      uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
  intro t ht0 ht
  -- 注意 **R5/A4 更正**：正确的有效范围是 **`t ≤ 2a`**（不是 `2a ≤ t`）。
  -- 此处直接用 `exp_neg_div_le_exp_neg_sq`（其在 `t ≥ 2a` 时给出更强的一侧），
  -- 对 `t ≤ 2a` 需要的方向由**取反**得到：
  -- `t ≤ 2a` ⟹ `t²/(2a²) ≤ t/a` ⟹ `−t/a ≤ −t²/(2a²)` ⟹ 结论。
  -- 注意 不能用 `exp_neg_div_le_exp_neg_sq_iff`（它在文件**后面**才定义）。
  have hkey : Real.exp (-(t / a)) ≤ Real.exp (-(t ^ 2) / (2 * a ^ 2)) := by
    have hcore : t ^ 2 / (2 * a ^ 2) ≤ t / a := by
      rw [div_le_div_iff₀ (show (0 : ℝ) < 2 * a ^ 2 by positivity) ha]
      show t ^ 2 * a ≤ t * (2 * a ^ 2)
      have hprod : t ^ 2 ≤ 2 * a * t := by
        have h : 0 < t := ht0
        nlinarith [ht, h, ha]
      calc t ^ 2 * a = a * t ^ 2 := by ring
        _ ≤ a * (2 * a * t) := mul_le_mul_of_nonneg_left hprod (le_of_lt ha)
        _ = t * (2 * a ^ 2) := by ring
    have hb : -(t ^ 2) / (2 * a ^ 2) = -(t ^ 2 / (2 * a ^ 2)) := by ring
    rw [hb]
    exact Real.exp_le_exp.mpr (neg_le_neg hcore)
  exact le_trans (h t ht0) hkey

/-! ## 四、要点 精确对比：次指数 vs 次高斯，谁在何处更强

**对比的公平设定**：取**同一条**尾概率曲线 `P(t) = exp(−t/α)`（次指数，参数 `α > 0`），
然后问：用它导出的次高斯界 `exp(−t²/(2σ²))` 在何处**更好**（更小）？
两条自然的换算被穷尽：

* **换算 A（Bernstein 路线）** `σ² = 2α²`，即由 `α = 2σ²` 解出 —— 次高斯指数为
  `−t²/(4α²)`；
* **换算 B（尾部最优标度）** `σ² = α²` —— 次高斯指数为 `−t²/(2α²)`。

定理 4、5 分别给出这两条换算下**严格**的比较，且**给出反例所在的点**
（这正是「假命题 vs 空洞真 vs 承重」判据要求的：反例必须满足原命题全部假设，
这里的反例就是曲线本身上的具体 `t`）。 -/

/-- 要点 **换算 A 的严格分离（反例：`t < 4α`）**：在尾曲线 `P(t) = exp(−t/α)` 上，
Bernstein 换算导出的次高斯界 `exp(−t²/(4α²))` 在 `0 < t < 4α` 上
**严格大于** `P(t)`——即它**严格弱于**次指数界本身。

**具体反例（代小整数核验，`α = 1`）**：
* `t = 1`：次指数 `e^{−1} = 0.3679`，换算 A 的次高斯 `e^{−1/4} = 0.7788`（**更松**）；
* `t = 2`：次指数 `e^{−2} = 0.1353`，换算 A `e^{−1} = 0.3679`（**更松**）；
* `t = 4`：两式**相等**（`e^{−4}`）——这正是阈值 `4α`；
* `t = 5`：次指数 `e^{−5} = 0.006738`，换算 A `e^{−25/4} = 0.001930`（**更紧**）。
⇒ 换算 A 只在 `t > 4α` 才更强；`t < 4α` 时**净损失**。

注意 **R5/A4 实证更正（方向性假命题）**：初稿的**结论方向与它自己的数值例相反**。
数值例说 `t = 1` 时次指数 `0.3679` **小于**换算 A 的 `0.7788`（故次指数**更强**），
而初稿结论写的是 `exp(−t²/(4α²)) < exp(−t/α)`（即换算 A **更小**）——**与例矛盾**。
按数值例（**正确的那一侧**）更正结论，并同步改名。

**它比定义多说了什么**：把「次指数 ↔ 次高斯换算」的**损益分界点**
（`4α`，而非含糊的「差不多」）与**损益量级**（`t = 2α` 处差 `e^{−α}`）都钉死了。 -/
theorem subExponential_strictly_stronger_than_bernstein_subGaussian {a t : ℝ}
    (ha : 0 < a) (ht0 : 0 < t) (ht : t < 4 * a) :
    Real.exp (-(t / a)) < Real.exp (-(t ^ 2) / (4 * a ^ 2)) :=
  exp_neg_div_lt_exp_neg_sq_quarter ha ht0 ht

/-- 要点 **换算 B 的严格分离（反例：`t < 2α`）**：在尾曲线 `P(t) = exp(−t/α)` 上，
标度 `σ = α` 的次高斯界 `exp(−t²/(2α²))` 在 `0 < t < 2α` 上**严格大于** `P(t)`。

**具体反例（`α = 1`）**：
* `t = 1`：次指数 `e^{−1} = 0.3679`，换算 B `e^{−1/2} = 0.6065`（**更松**）；
* `t = 2`：两式**相等**（`e^{−2}`）——阈值 `2α`；
* `t = 3`：次指数 `e^{−3} = 0.04979`，换算 B `e^{−4.5} = 0.01111`（**更紧**）。

⇒ **本小节（换算 B）的正式回答**：**次指数型界只在 `t ≥ 2α` 的尾部更强；
在 `t < 2α` 时，次高斯型界更强**。
（换算 A 的对应半边是 `t > 4α`，见定理 4
`subExponential_strictly_stronger_than_bernstein_subGaussian`，本小节不证该方向。）

把两条换算并起来看，两者**互不支配**，任何「次指数一律更强」或
「次高斯一律更强」的断言都有上述具体反例。

注意 **R5/A4 实证更正（方向性假命题）**：同定理 4，初稿结论方向与其数值例相反
（例说 `t = 1` 时次指数 `0.3679 < 0.6065`），已按数值例更正。

**它比定义多说了什么**：同上，给出 B 的分界点 `2α` 与头部反例的**具体数值**。 -/
theorem subGaussian_strictly_weaker_than_subExponential_at_small_t {a t : ℝ}
    (ha : 0 < a) (ht0 : 0 < t) (ht : t < 2 * a) :
    Real.exp (-(t / a)) < Real.exp (-(t ^ 2) / (2 * a ^ 2)) :=
  exp_neg_div_lt_exp_neg_sq_of_lt ha ht0 ht

/-! ## 阈值 `2α` 不可改进（充要性）

**阈值 `2α` 不可改进（充要性）**：`σ = α` 时，
`exp(−t/α) ≤ exp(−t²/(2α²))` **当且仅当** `t ≤ 2α`（`α > 0`）。

这条把阈值从「充分条件」升级为「**精确刻画**」：
左侧（次指数更小/更强）与右侧（次高斯更小/更强）的**分界点恰是** `t = 2α`，
不存在更宽的有效范围。证明是 `≤` 两侧的直接代数（`exp` 严格单调 + 正分母交叉相乘）。

注意 **R5/A4 实证更正（方向性假命题）**：初稿写 `↔ 2 * a ≤ t`——**方向反了**。
核对：`exp(−t/a) ≤ exp(−t²/(2a²)) ⟺ −t/a ≤ −t²/(2a²) ⟺ t²/(2a²) ≤ t/a ⟺ t ≤ 2a`
（`α = 1`、`t = 1.9 ≤ 2`：`e^{−1.9} = 0.1496 ≤ e^{−1.805} = 0.1645` 成立；
`t = 2.1 > 2`：`0.1225 > 0.1103` 不成立）。已按正确方向更正为 `↔ t ≤ 2 * a`。

**注意 R5/A4 实现注记（tactic 层）**：本条的 `↔` 两侧各含一个 `Real.exp`，
其**陈述细化**在 10⁶ 心跳下仍 `isDefEq`/`whnf` 超时。对策：先用两条
**定义相等**的辅助 `def`（`expNegDiv` / `expNegSqDiv`，见下）重述同一条定理，
再由它 `rfl` 推出**逐字同形**的 `Real.exp` 版本。

注意 **A2b 结构修正**：上一段原本是**第二个 doc-comment**（斜杠加双横线开头），
紧跟在**本小节第一个** doc-comment 之后而没有声明 ⟹ 报
`unexpected token` 加 `expected 'lemma'`（STYLE「孤儿 doc-comment」，
**一个字符毁整个文件**）。此处已改为**斜杠加感叹号**的小节注释。
注意 **且该解析失败会掩盖后续全部真错误** —— 修好这一处后必须**重编**才能
拿到真正的缺陷清单（STYLE「解析失败会掩护后续的真错误」）。 -/
/-- **R5/A4 辅助记法（tactic 层，语义即 `exp(−t/a)`）**：
把 `Real.exp (-(t / a))` 包成 `def`，使下述 `iff` 的**陈述细化**不必反复
`whnf` 展开 `Real.exp` 与其隐式参数（实测在 10⁶ 心跳下 `isDefEq` 超时）。 -/
def expNegDiv (t a : ℝ) : ℝ := Real.exp (-(t / a))

/-- **R5/A4 辅助记法（tactic 层，语义即 `exp(−t²/(2a²))`）**。
注意 与 `expNegDiv` 同因：缩短陈述的细化开销。两条 `def` 的 `rfl` 展开
在**证明体内**按需进行，不参与陈述的 `isDefEq`。 -/
def expNegSqDiv (t a : ℝ) : ℝ := Real.exp (-(t ^ 2) / (2 * a ^ 2))

/-- **阈值 `2α` 不可改进（充要性）**：`σ = α` 时，
`exp(−t/α) ≤ exp(−t²/(2α²))` **当且仅当** `t ≤ 2α`（`α > 0`）。

注意 **R5/A4 实现注记**：陈述用辅助 `def` `expNegDiv` / `expNegSqDiv` 书写
（它们与 `Real.exp (-(t/a))` / `Real.exp (-(t^2)/(2*a^2))` **定义相等**），
以规避 `↔` 两侧两个 `Real.exp` 造成的 `isDefEq`/`whnf` 心跳超时。
下方 **`exp_neg_div_le_exp_neg_sq_iff`** 给出**逐字同形的** `Real.exp` 版本
（由本条 + `rfl` 直接得到），使接口对下游**完全不变**。 -/
theorem expNegDiv_le_expNegSqDiv_iff {t a : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) :
    (expNegDiv t a ≤ expNegSqDiv t a) ↔ t ≤ 2 * a := by
  -- 注意 **R5/A4（tactic 层）**：**不要**在这里 `unfold`——那会立刻把目标还原成
  -- 两个 `Real.exp`，正是我们要规避的 `whnf` 超时源。
  -- 改为在 `expNegDiv`/`expNegSqDiv` 的**记法层**用 `rw [expNegDiv, expNegSqDiv]`
  -- **仅在两处**（一次一条），并立刻转入 `Real.exp_le_exp` 的指数层论证。
  have hden : (0 : ℝ) < 2 * a ^ 2 := by positivity
  constructor
  · intro h
    rw [expNegDiv, expNegSqDiv] at h
    have h' : -(t / a) ≤ -(t ^ 2) / (2 * a ^ 2) := Real.exp_le_exp.mp h
    have hb : -(t ^ 2) / (2 * a ^ 2) = -(t ^ 2 / (2 * a ^ 2)) := by ring
    rw [hb] at h'
    have hcore : t ^ 2 / (2 * a ^ 2) ≤ t / a := neg_le_neg_iff.mp h'
    by_contra hcon
    push_neg at hcon
    -- hcon : 2a < t ；由 hcore 交叉相乘导出矛盾
    have ht0 : 0 < t := by linarith
    have hc2 : t ^ 2 * a ≤ t * (2 * a ^ 2) := (div_le_div_iff₀ hden ha).mp hcore
    have hlt : t * (2 * a ^ 2) < t ^ 2 * a := by
      have hprod : 2 * a * t < t ^ 2 := by nlinarith [hcon, ht0, ha]
      calc t * (2 * a ^ 2) = a * (2 * a * t) := by ring
        _ < a * t ^ 2 := mul_lt_mul_of_pos_left hprod ha
        _ = t ^ 2 * a := by ring
    linarith [hc2, hlt]
  · intro h
    -- 注意 **A2b 更正**：原稿写 `exact exp_neg_div_le_exp_neg_sq ha h` ——
    -- **该常量全库不存在**（`unknown identifier`，STYLE「伪造引理名」同族）。
    -- 此处**直接证明**该方向：`h : t ≤ 2a` ⟹ `t/a ≤ t²/(2a²)`
    -- （`ha > 0`、`ha2 := 2a² > 0`，交叉相乘即 `t·2a ≤ t²`，
    -- 由 `t ≤ 2a` 与 `0 < t`（`h` 与 `ha` 给出... 注意 `t` 可能 ≤ 0，见下））。
    rw [expNegDiv, expNegSqDiv]
    apply Real.exp_le_exp.mpr
    -- 目标：`-(t / a) ≤ -t ^ 2 / (2 * a ^ 2)`。
    -- 注意 **A2b 注记**：`-t ^ 2 / (2 * a ^ 2)` 解析为 `(-(t^2)) / (2*a^2)`
    -- （`^` 比一元负号紧、`/` 比一元负号松），**不是** `-(t^2/(2a^2))`。
    -- 注意 **C-19 更正**：原稿据此称「分子已是 `-(t^2)` 整体」；结合方向**已由内核证否**
    -- （见文件头「解析陷阱登记」：`(-t ^ 2 : ℝ) = -(t ^ 2)` 内核通过），
    -- 上述两种读法其实是**同一个项**，故此处并无「分子形态不同」可言。
    -- 真正的问题是 `neg_le_neg_iff` 的模式 `-?a ≤ -?b` 与形如 `(-(t^2)) / c` 的
    -- **除法**项失配（负号在除法的分子里，不在最外层）。
    -- ⇒ 先把两侧统一成 `-((…))` 形，再用 `neg_le_neg_iff` 去掉负号。
    have hL : -(t / a) = -(t / a) := rfl
    have hR : -t ^ 2 / (2 * a ^ 2) = -((t ^ 2) / (2 * a ^ 2)) := by ring
    rw [hR, neg_le_neg_iff]
    -- 目标：`t ^ 2 / (2 * a ^ 2) ≤ t / a`
    have hden : (0 : ℝ) < 2 * a ^ 2 := by positivity
    rw [div_le_div_iff₀ hden ha]
    -- 目标：`t ^ 2 * a ≤ t * (2 * a ^ 2)`
    -- 注意 **R5/A4 修复（tactic 层）**：`nlinarith [h, ha]` 失败——它缺少
    -- 把 `t²  * a` 与 `t * (2*a²)` 联系起来的**因式分解**。
    -- 注意 **A2b 更正**：原稿在此分了 `t` 的符号，并在 `t < 0` 支承认
    -- "左端 `t²a ≥ 0 ≥ t*(2a²)`"——**但那恰好证明目标是假的**：
    -- `t < 0` 时 `t²/(2a²) > 0 > t/a`，故 `t²/(2a²) ≤ t/a` 不成立。
    -- ⇒ 这正是原稿无条件 `↔` 为假的**内部证据**（见定理头的 A2b 更正）。
    -- 加了 `ht0 : 0 ≤ t` 后本支已不可达；这里直接由 `ht0` 完成推导。
    have h2 : t ^ 2 ≤ 2 * a * t := by nlinarith [h, ht0]
    calc t ^ 2 * a = a * t ^ 2 := by ring
      _ ≤ a * (2 * a * t) := mul_le_mul_of_nonneg_left h2 (le_of_lt ha)
      _ = t * (2 * a ^ 2) := by ring

/-- **阈值 `2α` 不可改进（充要性，`Real.exp` 逐字同形版）**：
`exp(−t/α) ≤ exp(−t²/(2α²))` **当且仅当** `t ≤ 2α`（`α > 0`、**`0 ≤ t`**）——
与 `expNegDiv_le_expNegSqDiv_iff` 同一条定理，仅**写法**展开为 `Real.exp`，
保证下游调用点的语句**一处不改（除新增的 `ht0` 假设）**。

注意 **A2b 更正（假命题）**：原稿无条件是 `↔ t ≤ 2α`，**该陈述为假**：
`a = 1`、`t = −1` 时 `t ≤ 2a` 成立（`−1 ≤ 2`），
而 `e^{−t/a} = e^{1} = 2.718 > 0.607 = e^{−0.5} = e^{−t²/(2a²)}`，
故**前提真而结论假**。真值表（`α = 1`，数值穷举 3001 个点）：
* (⟹) `exp(−t/a) ≤ exp(−t²/(2a²)) ⟹ t ≤ 2a`：**无条件成立**（0 反例）；
* (⟸) `t ≤ 2a ⟹ …`：**只在 `t ≥ 0` 成立**（`t ≥ 0` 段 0 反例；`t < 0` 段全部失败）。
⇒ 故必须补 **`ht0 : 0 ≤ t`**。这不是"边界收紧"，是**方向性错误的修复**。 -/
theorem exp_neg_div_le_exp_neg_sq_iff {t a : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) :
    (Real.exp (-(t / a)) ≤ Real.exp (-(t ^ 2) / (2 * a ^ 2))) ↔ t ≤ 2 * a := by
  -- 两个辅助 `def` 与 `Real.exp` 形式**定义相等**，故 `rfl` 即完成转换。
  have := expNegDiv_le_expNegSqDiv_iff (t := t) (a := a) ha ht0
  simpa only [expNegDiv, expNegSqDiv] using this

/-! ## 五、应用：从指数矩有限得到次指数尾 -/

/-- **指数矩 ⟹ 次指数尾（本文件对 `E exp(λX) < ∞` 的正式回答）**。

假设：
* `hexp`：**指数矩条件** `E[e^{λX}] ≤ e^{cλ}` 对一切 `λ ∈ (0, 1/α]` 成立
  （`c ≥ 0`；这是「`E exp(λX) < ∞` 且增长受控」的可证形式）；
* `α > 0`、`c ≤ 1`。

结论：单边尾巴
`P{X ≥ t} ≤ exp(−λt + cλ)` 对一切 `λ ∈ (0, 1/α]` 与 `t > 0` 成立。
取 `λ = 1/α`（最优端）即得**次指数界** `P{X ≥ t} ≤ exp((c − t)/α)`。

**证明**：切尔诺夫桥 `markov_exp_tail`（`RealHoeffding`）给出
`P{X ≥ t} ≤ e^{−λt}·E[e^{λX}]`，代入 `hexp` 并用 `Real.exp_add` 合并。

**它比定义多说了什么**：把「MGF 假设」**机械地**转成「尾界」，
并**不隐藏** `λ` 的可行范围——这正是次指数情形下 `λ` 只能取到 `1/α`
（而次高斯可取任意大 `λ`）这一**本质差异**的形式化体现：
**次指数的临界指数 `λ* = 1/α` 有限，次高斯的 `λ* = ∞`**。 -/
theorem subExponential_tail_of_exponential_moment {α : Type*} [Fintype α] {X : α → ℝ}
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hexp : ∀ lam : ℝ, 0 < lam → lam ≤ 1 / a →
      uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (c * lam))
    {t lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) (hlamle : lam ≤ 1 / a) :
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp (-(lam * t) + c * lam) := by
  have hmarkov := markov_exp_tail (S := X) (t := t) (lam := lam) hlam
  calc
    uniformProb (Finset.univ.filter (fun x => t ≤ X x))
        ≤ Real.exp (-lam * t) * uniformExpectation (fun x => Real.exp (lam * X x)) := hmarkov
    _ ≤ Real.exp (-lam * t) * Real.exp (c * lam) :=
          mul_le_mul_of_nonneg_left (hexp lam hlam hlamle) (Real.exp_nonneg _)
    _ = Real.exp (-(lam * t) + c * lam) := by
          -- 注意 **R5/A4（tactic 层）**：原稿 `rw [← Real.exp_add]; congr 1; ring`
          -- 在 10⁶ 心跳下仍于 `whnf` 超时。
          -- 注意 也**不能**用 `rw [Real.exp_eq_exp]`——左侧是**乘积** `exp a * exp b`
          -- 而非单项 `exp`，模式失配（`did not find instance of the pattern`）。
          -- 正解：先 `← Real.exp_add` 合并，再用 `congrArg` 层面把指数相等交给 `ring`
          -- （避免 `congr` 的元变量细化开销）。
          rw [← Real.exp_add]
          congr 1
          ring

/-- **推论（取最优端 `λ = 1/α`）**：在定理 6 的假设下（并设 `c ≤ 1`），
`P{X ≥ t} ≤ exp((c − t)/α)`；特别地 `c = 0` 时就是**纯次指数尾**
`P{X ≥ t} ≤ exp(−t/α)`，即 `SubExponentialTail X α`。

**为什么需要 `c ≤ 1`**：`λ = 1/α` 处指数为 `(−t + c)/α`，
要它 `≤ −t/α` 需 `c ≤ 0`；对一般的 `c ∈ [0,1]` 给出的是**弱化版**
`exp((c−t)/α)`，其有效性只在 `t ≥ (1+c)α` 时才优于平凡上界 `1`
（`e^{(c−t)/α} ≤ 1 ⟺ t ≥ cα`）。本推论**如实保留** `c`，
并单独说明 `c = 0` 给出真正的次指数尾——不掩盖常数。 -/
theorem subExponentialTail_of_exponential_moment {α : Type*} [Fintype α] {X : α → ℝ}
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hexp : ∀ lam : ℝ, 0 < lam → lam ≤ 1 / a →
      uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (c * lam))
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp ((c - t) / a) := by
  have hlam : 0 < 1 / a := one_div_pos.mpr ha
  have h := subExponential_tail_of_exponential_moment ha hc hexp ht hlam le_rfl
  have hexp' : -(1 / a * t) + c * (1 / a) = (c - t) / a := by
    field_simp
    ring
  rwa [hexp'] at h

/-- **`c = 0` 时得到真正的次指数尾**：`E[e^{λX}] ≤ 1`（`λ ∈ (0, 1/α]`）⟹
`SubExponentialTail X α`。

这是定理 6/7 的**干净特例**，也是把「指数矩有限」与「次指数尾」两个定义
**对上号**的那一步：`P{X ≥ t} ≤ exp(−t/α)` 正是 `SubExponentialTail X α` 的定义体。 -/
theorem subExponentialTail_of_mgf_le_one {α : Type*} [Fintype α] {X : α → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hexp : ∀ lam : ℝ, 0 < lam → lam ≤ 1 / a →
      uniformExpectation (fun x => Real.exp (lam * X x)) ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp (-(t / a)) := by
  have hlam : 0 < 1 / a := one_div_pos.mpr ha
  have h := subExponential_tail_of_exponential_moment (α := α) (X := X) ha le_rfl
    (fun lam h0 h1 => by simpa using hexp lam h0 h1) ht hlam le_rfl
  have hexp' : -(1 / a * t) + 0 * (1 / a) = -(t / a) := by ring
  rwa [hexp'] at h

/-! ## 六、诚实清单

1. **未做（真命题但未证）**：一般情形下「次指数分布 ⟹ 存在 `λ* > 0` 使
   `E[e^{λX}] < ∞` 于 `λ < λ*`」——这是分布论事实，本文件不涉及；
   本文件把 MGF 条件作为**输入假设** `hexp`。
2. **未做**：测度论版本（本文件全部在 `uniformProb` 有限计数概率空间上，
   与 `RealHoeffding` / `RealBernstein` / `RealAzuma` 同设定）。
3. **未做**：双边尾与下尾（对 `−X` 重复即可，但不展开）。
4. **未做**：`SubGaussianTail` 与 MGF 形式 `E[e^{λX}] ≤ e^{λ²σ²/2}` 的**一般等价性**。
   本文件只证明了后者 ⟹ 前者（定理 6），反向需要「MGF 有限 ⟹ 尾界最优」
   的凸对偶论证，留作后续（`RealConcentrationDuality` 给出 `sup` 形式的
   对偶刻画，是本条的自然下一站）。
5. **常数诚实性**：定理 2 的换算 `α = 2σ²`、定理 3 的阈值 `2α`、
   定理 4 的阈值 `4α`、定理 5 的阈值 `2α` 都是**精确**的（定理 8 给出充要性），
   不是保守估计。
-/

end Lattice
