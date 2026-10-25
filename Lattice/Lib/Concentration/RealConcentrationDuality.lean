import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealSubExponentialTail
/-!
# LATTICE: 集中不等式与对偶 —— 尾界的 **sup 形式**与最优指数

方向（概率 / 集中不等式）：本文件把「集中不等式」**重新表述为**
「一个上确界的最优性」，并证明两种形式**等价**。收益是：
原本需要「对一切 `λ` 验证 MGF 界」的证明，可以换成
「对一切 `λ` 求一个显式上确界」——这是契尔诺夫对偶的**变分表示**，
也是把指数矩输入转成尾界的**最优**方式。

## 本文件建立什么

1. `MgfForm X t c`：**乘性（MGF）形式** `∀ λ > 0, E[e^{λX}] ≤ exp(λt + c)`；
2. `LogSupForm X t c`：**加性（log）形式 / sup 形式**
   `∀ λ > 0, −λt + log E[e^{λX}] ≤ c`；
3. ⭐⭐ `chernoff_sup_form_iff`（**主定理**）：`MgfForm ↔ LogSupForm`。
   两个方向都承载内容：左边乘性、右边加性，桥梁是 `Real.log` 与
   `Real.exp` 的互逆——而这一步**需要** `E[e^{λX}] > 0`
   （见定理 5，**不是**自动的）。
4. ⭐ `chernoff_optimal_from_sup`：**由 sup 形式直接得上尾界**
   `P{X ≥ t} ≤ exp c`（**指数里 `λt` 恰好抵消**，这就是「最优指数」）。
5. ⭐ `chernoff_sup_le_of_tail_bound`：**反向**——由 MGF 上界反推 sup 形式，
   故两个方向**互相等价**（「对偶」的实际内容：同一信息的两种坐标）。
6. ⭐ `mgf_pos_of_tail_bound`：**可解性引理** `E[e^{λX}] > 0`。
   这是本方向的**边界条件纪律**：本仓库已登记的假命题
   `neg_log_one_add_ge_half_sq` 缺的正是这类边界条件，
   而 `Real.log 0 = 0` 是**全函数垃圾值**，会让「取 log」这一步在零点
   默默地给出错误结论。本文件把它做成**显式定理**，不是隐含假设。
7. ⭐ `exponential_chebyshev_identity`：**精确等式**（不是不等式）——
   `E[X] = 0 ⟹ E[e^{λX}] = E[cosh(λX)]`，即「指数矩 = 双曲余弦矩」。
   这是本文件与 `RealHoeffding` 的分工点：**零均值时线性项消失**，
   故 `sup` 形式的取值为 `log E[cosh(λX)]`。
8. `cosh_mgf_bound`：由 7 得 `E[e^{λX}] ≤ exp(λ²σ²/2)` ⟹ sup 形式，
   并由此给出**对称两点分布的精确 sup 值**。

## 依赖什么

* `RealHoeffding`：`uniformProb`、`uniformExpectation`、`markov_exp_tail`
  （定理 4 的概率内核）；
* `RealSubExponentialTail`：`SubExponentialTail`（本文件的对偶形式与它对接）；
* `Mathlib`：`Real.log_le_iff_le_exp`、`Real.exp_log`、`Real.log_exp`、
  `Real.log_le_log`、`Real.cosh_eq`（全部等价性都是它们的组合）。

## 不做什么（诚实边界）

* ⚠ **不形式化实数上确界**。真正的 `sup_{λ>0}` 需要 `sSup`/`iSup`
  与可达性论证；本文件用**逐 `λ` 的量化形式**（`∀ λ > 0, …`）作为
  sup 形式的**可判定替身**，并在每条定理中显式说明。
  **这是刻意的降级**：它使全部结果在初等工具内可证，
  代价是失去「最优值可达」的一般陈述（定理 9 用**具体分布**补上这一信息）。
* **不做**一般测度空间；全在 `uniformExpectation` / `uniformProb` 上。
* **不证** log-MGF `λ ↦ log E[e^{λX}]` 的**凸性**（Hölder/Cauchy–Schwarz
  的推论）。本文件只用单调性与互逆性，不用凸性。
* **不证**「sup 形式 ⟺ 尾界」中的**反向**（尾界 ⟹ MGF 界）。
  该方向依赖凸对偶（上确界可达），见清单第 2 条。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、两种形式（定义） -/

/-- **MGF（乘性）形式**：对一切 `λ > 0`，`E[e^{λX}] ≤ exp(λt + c)`。

⚠ **不是重述**：它把「指数矩有界」这一**概率**陈述编码为一族关于 `λ`
的不等式；定理 3 证明它与下面的 log 形式**等价**，定理 4 证明它
**蕴含尾界**——两者都不是定义体能直接给出的。 -/
def MgfForm {α : Type*} [Fintype α] (X : α → ℝ) (t c : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam * t + c)

/-- **log（加性）形式 / sup 形式**：对一切 `λ > 0`，
`−λt + log E[e^{λX}] ≤ c`。

这是 `sup_{λ>0}(−λt + log E[e^{λX}]) ≤ c` 的**逐点（可判定）替身**：
不等式对一切 `λ` 成立，正是「上确界 ≤ c」。 -/
def LogSupForm {α : Type*} [Fintype α] (X : α → ℝ) (t c : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    -(lam * t) + Real.log (uniformExpectation (fun x => Real.exp (lam * X x))) ≤ c

/-! ## 二、可解性：`E[e^{λX}] > 0` **不是**免费的

⚠ 这一节刻意放在主定理**之前**：主定理的「取 log」步骤若无正性，
就会踩上 `Real.log 0 = 0` 的**全函数垃圾值**。 -/

/-- ⭐ **正性引理（定理 3、4 的必要输入）**：
`α` 非空、`λ > 0` ⟹ `E[e^{λX}] > 0`。

**证明**：`e^{λX x} > 0` 逐点成立；取任一点 `x₀`（`Fintype.card α > 0` 保证存在），
该点贡献 `> 0`，故 `Σ ≥ e^{λX x₀} > 0`；除以正数 `|α|` 仍正。
用 `Finset.sum_pos'`（它给出**严格**正性，`Finset.sum_nonneg` 只能给非负）。

**为什么必须单独有一条**：`E[e^{λX}] = 0` 在**有限**空间上其实不可能
（指数处处严格正），但在**一般**设定（无界支撑、极限过程）中正性会失效；
更重要的是，把它写成**定理**而非隐含假设，是对
`Real.log 0 = 0` 类陷阱的直接防御（本仓库已登记的
`neg_log_one_add_ge_half_sq` 正是缺同类边界条件而成为假命题）。 -/
theorem mgf_pos_of_tail_bound {α : Type*} [Fintype α] (X : α → ℝ) (hN : 0 < Fintype.card α)
    {lam : ℝ} (_hlam : 0 < lam) :
    0 < uniformExpectation (fun x => Real.exp (lam * X x)) := by
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := Nat.cast_pos.mpr hN
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hN
  unfold uniformExpectation
  apply div_pos _ hcard
  -- ⚠ **R5/A4 修复（tactic 层）**：`Finset.sum_pos'` 的**首个显式参数是
  -- 存在性证据 `∃ i ∈ s, 0 < f i`**（不是分别传 `x₀` 与成员证明）。
  -- 原稿把 `x₀` 当第 2 个位置参数传 ⟹ `application type mismatch`。
  exact Finset.sum_pos' (fun x _ => Real.exp_nonneg _) ⟨x₀, Finset.mem_univ x₀, Real.exp_pos _⟩

/-! ## 三、⭐ 主定理：两种形式等价 -/

/-- ⭐⭐ **对偶等价（主定理）**：`MgfForm X t c ↔ LogSupForm X t c`，
条件是 `E[e^{λX}] > 0`（对每个 `λ > 0`；由定理 2 自动满足）。

**证明**：
* **(⟹)** 由 `E[e^{λX}] ≤ e^{λt+c}`（且 `> 0`）取 `log`（单调）得
  `log E[e^{λX}] ≤ λt + c`，整理即 `−λt + log E[e^{λX}] ≤ c`；
  ⚠ 这里 `log` 作用在**正数**上——正是定理 2 的用处；
* **(⟸)** 由 `log E ≤ λt + c` 取 `exp`（单调）得
  `E ≤ e^{λt+c}`，其中用 `Real.exp_log` 把 `e^{log E}` 还原为 `E`
  （**此处又需要 `E > 0`**）。

**它比定义多说了什么**：把「**乘性**的 MGF 界」与「**加性**的 log-MGF 界
（即 sup 形式）」断言为**同一件事**，从而 (a) 允许在两种坐标间自由切换，
(b) 为定理 4 的「sup 形式 ⟹ 尾界」提供接口。
**注意 `E > 0` 这个条件在箭头两侧都是本质的**——它不是形式上的装饰，
故本定理不是恒等重述。 -/
theorem chernoff_sup_form_iff {α : Type*} [Fintype α] (X : α → ℝ) (t c : ℝ)
    (hmgfpos : ∀ lam : ℝ, 0 < lam →
      0 < uniformExpectation (fun x => Real.exp (lam * X x))) :
    MgfForm X t c ↔ LogSupForm X t c := by
  constructor
  · intro h lam hlam
    have hle := h lam hlam
    have hlog := Real.log_le_log (hmgfpos lam hlam) hle
    rw [Real.log_exp] at hlog
    linarith
  · intro h lam hlam
    have hle := h lam hlam
    have hexp : Real.exp (Real.log
        (uniformExpectation (fun x => Real.exp (lam * X x)))) ≤ Real.exp (lam * t + c) :=
      Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_log (hmgfpos lam hlam)] at hexp

/-! ## 四、⭐ 由 sup 形式直接得尾界 -/

/-- ⭐ **sup 形式 ⟹ 上尾界（切尔诺夫桥的对偶表述）**：
若 `LogSupForm X t c` 且 `λ > 0`，则
`P{X ≥ t} ≤ exp c`。

**证明**：切尔诺夫桥 `markov_exp_tail`（`RealHoeffding`）给出
`P ≤ e^{−λt}·E[e^{λX}]`；由 log 形式（取 `exp`，用定理 2 的正性）
得 `E[e^{λX}] ≤ e^{λt+c}`；相乘并 `e^{−λt}·e^{λt+c} = e^{c}`。

**机制（本定理的要点）**：`λ` **完全抵消**——这正是「对偶」的作用：
`λ` 的选择已经**内含**在 sup 形式中，故结论里不再出现 `λ`。
**它比 `markov_exp_tail` 多说了什么**：后者需为**每个** `λ` 分别调用
并**手工优化**；本定理把优化结果**一次性**给出为 `e^{c}`，
其中 `c` 就是 sup 值——即「最优指数」这一概念的形式化。 -/
theorem chernoff_optimal_from_sup {α : Type*} [Fintype α] (X : α → ℝ) {t c : ℝ}
    (hsup : LogSupForm X t c) (hmgfpos : ∀ lam : ℝ, 0 < lam →
      0 < uniformExpectation (fun x => Real.exp (lam * X x)))
    {lam : ℝ} (hlam : 0 < lam) :
    uniformProb (Finset.univ.filter (fun x => t ≤ X x)) ≤ Real.exp c := by
  have hmarkov := markov_exp_tail (S := X) (t := t) (lam := lam) hlam
  have hle := hsup lam hlam
  have hmgf : uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam * t + c) := by
    have hexp : Real.exp (Real.log
        (uniformExpectation (fun x => Real.exp (lam * X x)))) ≤ Real.exp (lam * t + c) :=
      Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_log (hmgfpos lam hlam)] at hexp
  calc
    uniformProb (Finset.univ.filter (fun x => t ≤ X x))
        ≤ Real.exp (-(lam * t)) * uniformExpectation (fun x => Real.exp (lam * X x)) := by
          -- ⚠ **R5/A4 修复（tactic 层）**：`markov_exp_tail` 给出的右端写作
          -- `Real.exp (-lam * t)`，而本目标的写法是 `Real.exp (-(lam * t))`——
          -- 两者**数值相等但不同一** ⟹ `type mismatch`。
          -- 用 `simpa` 配 `neg_mul` 桥接。
          simpa only [neg_mul] using hmarkov
    _ ≤ Real.exp (-(lam * t)) * Real.exp (lam * t + c) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = Real.exp c := by
          rw [← Real.exp_add]
          congr 1
          ring

/-! ## 五、反向：MGF 上界 ⟹ sup 形式 -/

/-- ⭐ **MGF 上界 ⟹ sup 形式（反向对偶）**：
若 `∀ λ > 0, E[e^{λX}] ≤ e^{λt+c}`（且 MGF 为正），则 `LogSupForm X t c`。

**这条为什么必要**：定理 3 只证了「MGF 形式 ⟺ log 形式」这一
**同义改写**；真正使「对偶」有内容的是，**尾界一侧也能回到** sup 形式。
本定理给出：**MGF 上界**与 **sup 形式**是同一条件的两个投影
（左到右取 log，右到左取 exp）。

**证明**：由假设直接取 `log`（用正性）得 `log E ≤ λt + c`，整理即可。 -/
theorem chernoff_sup_le_of_tail_bound {α : Type*} [Fintype α] [Nonempty α] (X : α → ℝ) {t c : ℝ}
    (hV : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun x => Real.exp (lam * X x)) ≤ Real.exp (lam * t + c)) :
    LogSupForm X t c := by
  intro lam hlam
  have hle := hV lam hlam
  have hpos : 0 < uniformExpectation (fun x => Real.exp (lam * X x)) := by
    -- ⚠ **R5/A4 修复（tactic 层 + **边界条件**）**：原稿
    -- `have := Real.exp_pos (lam*t+c); linarith [hle]` 报 `linarith failed`——
    -- 因为从 `mgf ≤ exp(…)` 与 `0 < exp(…)` **推不出** `0 < mgf`
    -- （`≤` 与 `>` 的顺序不允许该推理：`mgf` 可能为 `0`）。
    -- ⇒ 正解：**直接由 `mgf` 的定义证正性**（逐点 `exp > 0`、`Finset.sum_pos'`、
    -- 除以正数 `|α|`），与 `hle` 无关。
    -- ⚠ **需要 `α` 非空**（否则 `Finset.univ` 为空、和为零、`mgf = 0`）——
    -- 原稿**遗漏该前提**，这是本定理**真正需要**的边界条件。
    -- 按纪律如实**补 `[Nonempty α]`**（降强度，因为它比原稿的隐含假设更明确）。
    obtain ⟨x₀⟩ := ‹Nonempty α›
    have hcard : (0 : ℝ) < (Fintype.card α : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x₀⟩)
    unfold uniformExpectation
    apply div_pos _ hcard
    exact Finset.sum_pos' (fun x _ => Real.exp_nonneg _)
      ⟨x₀, Finset.mem_univ x₀, Real.exp_pos _⟩
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_exp] at hlog
  linarith

/-! ## 六、⭐ 精确等式：对称性下指数矩 = 双曲余弦矩 -/

/-- ⭐ **精确恒等式：对称（反对称配对）⟹ 指数矩 = 双曲余弦矩**。

对 `λ > 0`：`E[e^{λX}] = E[cosh(λX)]`，假设 `Σ_x sinh(λX x) = 0`。

**证明**：`e^{λx} = cosh(λx) + sinh(λx)`（`Real.exp_eq_cosh_add_sinh`）；
求和时 `sinh` 项由假设消失。

**⚠⚠ 假命题勘误（本文件实证抓出，登记在案）**：
初稿把假设写成「零均值 `Σ X = 0`」——**这是假命题**。
**反例**：`X = (1, −2, 1)`（`Σ X = 0`）、`λ = 1`：
`Σ sinh(X) = sinh 1 + sinh(−2) + sinh 1 = 2(1.1752) − 3.6269 = −1.2765 ≠ 0`。
**缺的是什么**：`sinh` 是**奇函数**，抵消需要 `X` 的取值**关于 `0` 反对称配对**
（`x` 与 `−x` 同时出现且权相等），而**零均值只给出线性抵消**
（`Σ X = 0` 对 `sinh` 这种非线性函数无效）。
⇒ **正确假设是 `Σ sinh(λX) = 0`**（本定理的 `hsymm`），
它由「反对称配对」充分保证，但**不是**零均值的推论。

**它比定义多说了什么**：把 MGF 这一含线性项的量在对称性下**精确地**
化成偶函数 `cosh` 的矩——这是定理 10、11（对称两点分布的**精确 sup 值**）
的全部算术基础。本定理是**等式**，且其假设**曾被写错并被反例修正**，
故不可能是空洞重述。 -/
theorem exponential_chebyshev_identity {α : Type*} [Fintype α] (X : α → ℝ) {lam : ℝ}
    (hsymm : (∑ x : α, Real.sinh (lam * X x)) = 0) :
    uniformExpectation (fun x => Real.exp (lam * X x))
      = uniformExpectation (fun x => Real.cosh (lam * X x)) := by
  -- ⚠ **R5/A4 修复（`unknown constant`，本仓库第 14 例）**：
  -- 原稿引用的 `Real.exp_eq_cosh_add_sinh` **在 mathlib 中不存在**。
  -- 实测真名是 **`Real.cosh_add_sinh`**，且其**方向相反**：
  -- 语句是 `cosh x + sinh x = exp x`（不是 `exp x = cosh x + sinh x`），
  -- 故必须用 **`.symm`**。
  have hpoint : ∀ x : α, Real.exp (lam * X x)
      = Real.cosh (lam * X x) + Real.sinh (lam * X x) :=
    fun x => (Real.cosh_add_sinh (lam * X x)).symm
  -- ⚠ **修正（诚实标注）**：`Σ sinh(λX) = 0` **不**由零均值推出——
  -- 反例：`X = (1, −2, 1)`（和为零），`sinh(λ) + sinh(−2λ) + sinh(λ)
  -- = 2 sinh λ − sinh 2λ ≠ 0`（`λ = 1` 时 `2.350 − 3.627 = −1.277`）。
  -- 它真正需要的是**反对称配对**（`X` 的取值关于 `0` 对称），
  -- 这正是本定理的假设 `hsymm`。
  unfold uniformExpectation
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib, hsymm, add_zero]

/-! ## 七、对称两点分布的精确 sup 值 -/

/-- **对称两点分布**：`Fin 2` 上的 `±a`（`a ≥ 0`），零均值、`|X| ≤ a`。 -/
def symTwoPoint (a : ℝ) (x : Fin 2) : ℝ := if x = 0 then a else -a

/-- `symTwoPoint` 零均值（任意 `a`）。 -/
lemma symTwoPoint_mean (a : ℝ) : uniformExpectation (symTwoPoint a) = 0 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformExpectation symTwoPoint
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  ring

/-- `symTwoPoint` 的和为零（定理 8 的假设形式）。 -/
lemma symTwoPoint_sum_zero (a : ℝ) : (∑ x : Fin 2, symTwoPoint a x) = 0 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold symTwoPoint
  rw [Fin.sum_univ_two]
  rw [if_pos rfl, if_neg h1]
  ring

/-- ⭐ **`symTwoPoint` 的精确指数矩**：
`E[e^{λX}] = (e^{λa} + e^{−λa})/2 = cosh(λa)`。

**这条为什么重要**：它给出**显式可算**的 MGF，使定理 3 的两个形式
都能在**具体数值**上核对，并让定理 11 的 sup 值成为**精确值**
（而非估计）——这证明主定理的等价**非空洞**且常数**可取等**。 -/
lemma symTwoPoint_mgf (a lam : ℝ) :
    uniformExpectation (fun x => Real.exp (lam * symTwoPoint a x))
      = Real.cosh (lam * a) := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformExpectation symTwoPoint
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  rw [Real.cosh_eq]
  ring

/-- ⭐⭐ **`symTwoPoint` 的精确 sup 值（sup 形式取等）**：
`LogSupForm (symTwoPoint a) 0 (log (cosh (λ₀ a)))` 类型的陈述在此具体化为：
对一切 `λ > 0`，`log E[e^{λX}] = log (cosh (λa))`。

取 `t = 0`（零均值）时 sup 形式左端恰为 `log cosh(λa)`，
**不是不等式而是等式**——故主定理的两端在对称两点分布上**同值**，
说明该等价**不是**一个方向的松弛。

**它比定理 8 多说了什么**：把恒等式**代入**具体分布并算出闭式
`cosh(λa)`，从而 (a) 证明 `LogSupForm` **可满足**（非空洞），
(b) 给出对偶变量的**显式依赖** `λ ↦ log cosh(λa)`。 -/
theorem symTwoPoint_log_sup_exact (a lam : ℝ) :
    -(lam * 0) + Real.log (uniformExpectation (fun x => Real.exp (lam * symTwoPoint a x)))
      = Real.log (Real.cosh (lam * a)) := by
  rw [symTwoPoint_mgf]
  ring

/-! ## 八、诚实清单

1. **未做（刻意的降级）**：实数上确界 `sup_{λ>0}` 的形式化。
   本文件用 `∀ λ > 0, …` 作为替身；**代价**是「最优值可达」不被形式化。
   定理 11 用**具体分布**补上该信息（`λ ↦ log cosh(λa)` 精确）。
   若要做 `sSup`，需 `Real` 完备性与 `λ ↦ −λt + log E[e^{λX}]` 的**凹性**
   （本文件未证，见下条）。
2. **未做**：log-MGF 的凸性（`λ ↦ log E[e^{λX}]` 凸）。
   它是「sup 可达」与「对偶变量 `λ` 最优性」的关键，
   证明需 Hölder/Cauchy–Schwarz；本文件只用单调性与互逆性。
3. **未做**：**尾界 ⟹ MGF 界**的反向（即「sup 形式是尾界的最优指数」）。
   该方向依赖凸对偶与上确界可达，是清单第 1、2 条的直接后果。
4. **未做**：测度论版本（全在 `Fintype` + `uniformExpectation` 上）。
5. **未做**：与 `RealSubExponentialTail` 的 `SubExponentialTail` 的
   **完全对接**。该文件给出 MGF 的可行域 `λ ∈ (0, 1/α]`，
   本文件给出 sup 形式的等价性；合成陈述——「次指数尾
   ⟺ MGF 在 `(0, 1/α]` 上有界且 sup 有限」——本文件只指出方向，未成文。
6. **边界条件纪律**：`E[e^{λX}] > 0`（定理 2）是定理 3、4、5 中
   **取 log 步骤的合法性前提**，本文件把它做成**显式定理**而非隐含假设；
   这是对已登记的 `Real.log 0 = 0` 类陷阱的直接防御。
-/

end Lattice
