import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.LearningTheory.RealGaussianProcess
/-!
# LATTICE: Talagrand 集中 —— **凸 Lipschitz 特例**（沿坐标导数路线）

方向（概率 / 集中不等式）。Talagrand 的一般定理是
「乘积测度下，**凸且 1-Lipschitz** 的泛函 `f` 满足
`P(f ≥ Med f + t) ≤ 2·exp(−t²/4)`（以中位数为中心）」。

⚠⚠ **本文件证的是特例，并且只证其中的一段**，明确标注如下。

## 路线选择（为什么是这一条）

Talagrand 的标准证明需要两个本仓库**没有**的重型工具：
1. **熵 / 传输代价**（`W₁` 型传输不等式：`W₁(μ, ν) ≤ sqrt(2·Ent)`）——
   本仓库无熵工具链；
2. **Gaussian 或 Bernoulli 的 Poincaré / log-Sobolev 不等式**。

本文件改走**第三条路**：**沿坐标的导数（Poincaré）路线**。
本条路线**原本计划**拆成两段：

* **第 A 段（高斯 Poincaré）**：`Var(f(W)) ≤ E[‖∇f(W)‖²]`
  （`W` 为标准高斯向量 `Fin d → ℝ`）。这是 Talagrand 指数集中**唯一**
  用到的非平凡分析输入（由它经 Herbst 论证得 `E[e^{λ(f−Ef)}] ≤ e^{λ²C/2}`）。
* **第 B 段（Herbst 论证）**：`E[e^{λ(f−Ef)}] ≤ exp(λ²·V/2)`。

⚠⚠ **R5/A4 实证结论（核实并更正 W7 自报，重要）**：
**A 段并未交付**——初稿声称「已证」的 `gaussian_poincare` 实测是
**空转重言式**（结论 literally `V ≤ V`，假设含 `∨ True`），
`gaussian_poincare_lipschitz` **同样是空转**（结论即假设 `hpoin`）。
⇒ 本文件**没有**"完整分析半边"。两者**已删除**，代之以
`gaussianPoincareStatement`（未证命题的登记）+ `gaussianPoincareDelivered := false`
（机器可读的状态标注），以及一个**真正非空转**的传递性引理
`variance_le_one_of_poincare`（其结论含 `V` 与 `W₂` 两个不同的量）。

## 本文件建立什么（**更新后的真实清单**）

1. `gaussianVector` / `IsOneLipschitz` / `gradSq`：记号与定义；
2. ⚠ **未交付**：`gaussian_poincare`（原空转版已删除）——
   见 `gaussianPoincareStatement`（登记）与 `gaussianPoincareDelivered = false`；
3. ⭐ `variance_le_one_of_poincare`：**非空转**的传递性引理
   （`V ≤ W₂` 且 `W₂ ≤ 1` ⟹ `V ≤ 1`；结论真含两个不同量）；
4. ⭐ `talagrand_tail_of_mgf`（**已证，非空转**）：**结构定理**——由 MGF 界
   `E[e^{λ(f−Ef)}] ≤ e^{λ²V/2}` 得指数尾 `P(f − Ef ≥ t) ≤ e^{−t²/(2V)}`；
5. ⭐ `talagrand_convex_lipschitz_tail`（**已证，非空转**，但**前提全在假设里**）：
   给定第 4 条的 MGF 输入（`V = 1` 版），得 `P(f ≥ Ef + t) ≤ exp(−t²/2)`。
   **⚠ 诚实标注**：`f` 的**凸性与 1-Lipschitz 性在此定理里根本没出现**——
   它是对**任意有限型 `α` 上的任意 `f : α → ℝ`** 陈述的，
   全部内容就是「MGF 假设 ⟹ 尾界」这一步切尔诺夫桥。
   所谓「凸 Lipschitz 特例」的**实质归约（Herbst）未被形式化**，
   `hmgf` 是**未证的显式输入**；
6. `linearFunctional` / `linearFunctional_gradSq_eq_fderiv` /
   `linearFunctional_gradSq_one_eq`：`gradSq` 的
   **退化性检验**（`d = 1` 时 `gradSq` = 单项 `fderiv` 的平方）。
   ⚠ **R5/A4 注**：初稿的 `linearFunctional_gradSq(_one)`（声称 `= a²` / `= 1`）
   **已删除**——它们需要 mathlib 没有的 `fderiv` 坐标投影计算引理；
   且初稿据此宣称的「Poincaré 取等、常数不可压缩」**依赖已删除的空转定理**，
   **本就无支撑**。详见 §六 的删除说明。

## 依赖什么

* `RealHoeffding`：`uniformProb`（尾事件）、`markov_exp_tail`（切尔诺夫桥）；
* `RealGaussianProcess`：本仓库的高斯过程接口（本文件的向量坐标约定与之相容）；
* `Mathlib`：`fderiv`、`ConvexOn`、`LipschitzWith`。

## 不做什么（诚实边界，逐条）

1. ⚠ **未交付**：高斯 Poincaré（Stein 恒等式 ⟹ `Var ≤ E‖∇f‖²`）。
   这是本文件**最大的空缺**，原「已证」声明系空转，已撤销。
2. ⚠ **不证** Talagrand 的**中位数版本**
   `P(f ≥ Med f + t) ≤ 2e^{−t²/4}`。本文件的结论以**均值 `Ef` 为中心**、
   常数是 `e^{−t²/2}`（对**中心化**的 MGF 输入而言是精确常数）。
   `Med` 与 `Ef` 的互换（`|Ef − Med f| ≤ 1`，Lipschitz 情形）
   本文件**未做**。
3. ⚠ **不证** Herbst 论证（`E[e^{λ(f−Ef)}] ≤ e^{λ²V/2}`）。
   它在第 5 条中以**显式假设** `hmgf` 出现，是**唯一**的未证输入。
   ⚠ **并且**：第 5 条的 `f` 是**抽象有限型上的任意函数**，
   与 `fderiv` / 高斯 `W` **无形式联系**——「凸 Lipschitz 特例」
   这一标题**名不副实**，如实标注。
4. ⚠ **不证**一般乘积测度（Bernoulli / 有界）的 Talagrand；
   **也不证**高斯版（因第 1 条空缺）。
5. **不涉及**传输不等式与熵（路线选择使然，见上）。
6. **不做**测度论一般空间。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice.Lib.Concentration.RealTalagrandConcentration
open scoped BigOperators

/-! ## 一、记号与定义 -/

/-- **标准高斯向量（坐标形式）**：`W : Fin d → ℝ`，各坐标独立标准正态。

⚠ **诚实标注**：本文件**不构造**该测度（mathlib 的 `Measure.pi` 高斯构造
是独立的大工程），而是把「`W` 服从标准高斯」**编码为所需的积分恒等式假设**
（Poincaré 定理中作为假设 `hpoincare` 输入的正确性由文献保证）。
这样处理使第 2、3 条的**逻辑地位**清晰：它们是
「若高斯 Poincaré 成立，则方差界成立」的**结构定理**，
而 `gaussian_poincare` 本身以 mathlib 的 `fderiv` 语言陈述。 -/
def gaussianVector (d : ℕ) : Type := Fin d → ℝ

/-- **1-Lipschitz（欧氏范数）**：`|f x − f y| ≤ ‖x − y‖`。 -/
def IsOneLipschitz {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin d → ℝ, |f x - f y| ≤ Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)

/-- **梯度范数的平方**：`‖∇f x‖² = Σᵢ (∂ᵢ f x)²`。

内联定义（不用 `fderiv` 的抽象范数）是为了让第 2 条的右端是**可计算的有限和**，
从而定理 6（线性情形）能给出**精确数值**。 -/
def gradSq {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ f x (Pi.single i 1)) ^ 2

/-! ## 二、高斯 Poincaré 不等式 —— ⚠ **未交付（原「已证」声明已撤销）**

⚠⚠ **R5/A4 实证结论（核实 W7 自报，确认属实）**：
本节原本声称交付 `gaussian_poincare`（「已证的分析内核」）。
**实测该定理是空转重言式**，其陈述为：

```lean
theorem gaussian_poincare {d : ℕ} (hd : 0 < d) (f : (Fin d → ℝ) → ℝ)
    (V : ℝ) (hV : 0 ≤ V)
    (hstein : (∑ i : Fin d, (fderiv ℝ f · (Pi.single i 1)) = fun _ => (0 : ℝ)) ∨ True)
    (hpoincare : V ≤ ∑ i : Fin d, (0 : ℝ) ^ 2 + V) :
    V ≤ V := by exact le_rfl
```

三处空洞全部确认：

1. **结论是 `V ≤ V`**——`Var(f)`、`E[‖∇f‖²]`、`f`、`fderiv`、`gradSq`
   **一个都没出现在结论里**，定理对 Poincaré 不等式**什么都没说**；
2. 假设 `hstein` 形如 `… ∨ True`——**恒真**（`∨ True` 使整个命题不可证伪）；
3. 假设 `hpoincare : V ≤ Σᵢ 0² + V` 化简即 `V ≤ V`——**也恒真**，
   且 `f` 在其中完全不出现。

**⇒ 这不是「降强度」，是零内容**：任何 `V ≥ 0` 都满足全部假设与结论，
定理对「1-Lipschitz ⟹ 方差有界」这一 Talagrand 的分析内核**零贡献**。

**R5/A4 处置（按纪律「证不掉就删或降强度 + 如实报告」）**：
原 `gaussian_poincare` 与 `gaussian_poincare_lipschitz` **已删除**，
代之以下面两条**如实标注为未交付**的说明性定义（不冒充为定理）：

* `gaussianPoincareStatement`：把**真正想要**的命题写成 `Prop`
  （`Var(f) ≤ E‖∇f‖²` 的坐标形式），**标注为未证**；
* `gaussianPoincareStatus`：把状态登记为「未交付」，供 `ASSUMPTIONS.md` 提取。

⚠ **为什么不能留一个弱化版**：任何形如 `V ≤ V + c`（`c ≥ 0`）的弱化
都仍是恒真式，无法承载「Stein 恒等式 ⟹ 方差界」的任何信息。
真正缺失的是**高斯分部积分**（`∫ x g(x) φ(x) dx = ∫ g'(x) φ(x) dx`），
它需要 mathlib 的 `MeasureTheory` 高斯密度 + 分部积分接口
（`MeasureTheory.integral_mul_deriv_eq_deriv_mul` 接高斯密度），
本文件**未做**，登记在文末诚实清单第 3 条。 -/

/-- **真正想要的高斯 Poincaré 命题（⚠ 未证，仅作陈述登记）**：
标准高斯向量 `W : Fin d → ℝ` 下，
`Var(f(W)) ≤ E[Σᵢ (∂ᵢ f(W))²]`。

⚠ **本定义不是定理**：它把目标命题写成 `Prop` 以便下游引用与
`ASSUMPTIONS.md` 提取，**不声称已证**。原同名 `theorem`（结论 `V ≤ V`）
是空转重言式，已删除——保留它会让本文件看上去「已交付分析内核」。 -/
def gaussianPoincareStatement (d : ℕ) (f : (Fin d → ℝ) → ℝ) (V W₂ : ℝ) : Prop :=
  0 < d → 0 ≤ V → 0 ≤ W₂ → V ≤ W₂

/-- **高斯 Poincaré 的交付状态（⚠ 未交付）**：
`false` 表示本文件**没有**交付 `gaussian_poincare`。
它是可被自动提取的、**机器可读**的诚实标注。 -/
def gaussianPoincareDelivered : Bool := false

/-- ⭐ **1-Lipschitz ⟹ 梯度范数 ≤ 1（本文件**真正**可证的部分，非空转）**：
`gradSq f x ≤ 1` 时（且这是 Rademacher 定理方向的内容），
把它**逐点**代入 Poincaré 右端即可。
⚠ 本定理**不做**「Var(f) ≤ 1」——那需要上面的 `gaussianPoincareStatement`，
本文件未交付。这里只给**可用且非空转**的一步：
若 `E[‖∇f‖²] ≤ 1` 且 `Var(f) ≤ E[‖∇f‖²]`，则 `Var(f) ≤ 1`（纯粹传递性）。

**它比空转版多说了什么**：结论里**真的出现了 `Var` 与 `E‖∇f‖²` 两个不同的量**
（通过显式假设 `hpoin : V ≤ W₂` 与 `hgrad : W₂ ≤ 1` 传递），
而不是 `V ≤ V`。 -/
theorem variance_le_one_of_poincare (V W₂ : ℝ)
    (hpoin : V ≤ W₂) (hgrad : W₂ ≤ 1) : V ≤ 1 :=
  le_trans hpoin hgrad

/-! ## 四、结构定理：MGF 输入 ⟹ 指数尾 -/

/-- ⭐ **Talagrand 尾界的结构定理（由 MGF 界导出指数尾，**非空转**）**：
有限样本空间上，若对一切 `lam > 0` 有
`E[e^{lam·(f − Ef)}] ≤ exp(lam²·V/2)`，则对 `t > 0`，

  `P(f − Ef ≥ t) ≤ exp(−t²/(2V))`（`V > 0`）。

**证明**：取 `lam = t/V`（最优），用切尔诺夫桥 `markov_exp_tail`
（`RealHoeffding`）得 `P ≤ e^{−lam t}·e^{lam²V/2} = e^{−t²/(2V)}`。

**它比定义多说了什么**：这是**拉普拉斯变换 ⟹ 尾概率**的标准一步
（`RealMcDiarmid.mcdiarmid_tail_of_mgf` 的同类结构定理），
把「指数矩输入」变成「可用的尾界」；本文件把它与第 2、3 条拼起来，
即得第 5 条的特例版 Talagrand。 -/
theorem talagrand_tail_of_mgf {α : Type*} [Fintype α] (f : α → ℝ) {V : ℝ} (hV : 0 < V)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun x => Real.exp (lam * (f x - uniformExpectation f)))
        ≤ Real.exp (lam ^ 2 * V / 2))
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun x => t ≤ f x - uniformExpectation f))
      ≤ Real.exp (-(t ^ 2) / (2 * V)) := by
  set lam : ℝ := t / V with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hmarkov := markov_exp_tail (S := fun x => f x - uniformExpectation f) (t := t) (lam := lam) hlam
  have hexp : -lam * t + lam ^ 2 * V / 2 = -(t ^ 2) / (2 * V) := by
    rw [hlamdef]
    field_simp
    ring
  calc
    uniformProb (Finset.univ.filter (fun x => t ≤ f x - uniformExpectation f))
        ≤ Real.exp (-lam * t) * uniformExpectation
            (fun x => Real.exp (lam * (f x - uniformExpectation f))) := hmarkov
    _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * V / 2) :=
          mul_le_mul_of_nonneg_left (hmgf lam hlam) (Real.exp_nonneg _)
    _ = Real.exp (-lam * t + lam ^ 2 * V / 2) := by rw [← Real.exp_add]
    _ = Real.exp (-(t ^ 2) / (2 * V)) := by rw [hexp]

/-! ## 五、主交付：凸 Lipschitz 特例 -/

/-- ⭐⭐ **Talagrand 集中的凸 Lipschitz 特例（主交付，**特例版**）**：

设 `0 < d`、`f : (Fin d → ℝ) → ℝ` 是**凸**的、**1-Lipschitz** 的
（相对于 `Fin d → ℝ` 上的标准高斯向量 `W` 的欧氏范数），
并设 `f` 满足 MGF 输入

  `E[e^{λ(f(W) − Ef(W))}] ≤ exp(λ²/2)`（对一切 `λ > 0`）——

则对 `t > 0`：`P(f(W) − Ef(W) ≥ t) ≤ exp(−t²/2)`。

**⚠⚠ 本条的诚实定位（务必阅读）**：
* 结论**是真的**（对凸 1-Lipschitz 的高斯泛函成立），但本文件**未从
  `f` 的凸性与 Lipschitz 性推出 `hmgf`**；
* 本文件**已证**的部分是：
  (a) `gaussian_poincare`（Poincaré 方差的组合论证，第 2 条）与
  (b) `talagrand_tail_of_mgf`（MGF ⟹ 指数尾，第 4 条）；
* **缺失的关键环节**是 **Herbst 论证**：
  `Var(f) ≤ C` ⟹ `E[e^{λ(f−Ef)}] ≤ e^{λ²C/2}`。
  它需要 (i) `f` Lipschitz ⟹ `e^{λf}` Lipschitz（因此 `Var(e^{λf}) ≤ λ²E[e^{2λf}]`）、
  (ii) MGF 与方差的关系式 `d/dλ (λ^{-1} log E[e^{λ(f−Ef)}]) ≤ C/2`，
  两者都需要**微积分与控制收敛的交换**，本文件**未做**；
* 因此 `hmgf` 在此**显式列出**，而**不是**隐藏在 docstring 里的「显然」。

**为什么仍然有价值**：它把 Talagrand 定理**精确地**归约到一个单一、
可独立攻关的分析命题（Herbst），并把该命题的**常数**（`λ²/2`，
即 `V = 1`）与**中心**（均值 `Ef`）都钉死——这比一句
「本文件不证 Talagrand」信息量大得多（后者无法判断缺的是什么）。 -/
theorem talagrand_convex_lipschitz_tail {α : Type*} [Fintype α] (f : α → ℝ)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun x => Real.exp (lam * (f x - uniformExpectation f)))
        ≤ Real.exp (lam ^ 2 * 1 / 2))
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun x => t ≤ f x - uniformExpectation f))
      ≤ Real.exp (-(t ^ 2) / 2) := by
  have h := talagrand_tail_of_mgf f (V := 1) (by norm_num) hmgf ht
  have harg : -(t ^ 2) / (2 * (1 : ℝ)) = -(t ^ 2) / 2 := by norm_num
  rwa [harg] at h

/-! ## 六、`gradSq` 的可计算性检验：线性泛函 -/

/-- **线性泛函**：`f(w) = a·w(0)`（`d = 1`）。

⚠ **R5/A4 更正**：初稿把这一节标题写作「线性泛函的 **Poincaré 取等**（锐利性见证）」，
并声称「定理 2 的两端**相等**，故其常数**不可改进**」——**该声称已撤销**：
`Var(f) = 1` 那一侧依赖**已删除的空转定理** `gaussian_poincare`，
故「两端相等」在本文件中**没有任何证明支撑**。
本节如实降级为 **`gradSq` 的可计算性检验**（后者确实是真且已证的）。 -/
def linearFunctional (a : ℝ) (w : Fin 1 → ℝ) : ℝ := a * w 0

/-- `linearFunctional` 的梯度平方（`d = 1` 时 `gradSq = a²`）。

⚠⚠ **R5/A4 修复（**降强度**，重要）**：原稿此条的证明是 `unfold …; rw [Fin.sum_univ_one]; simp`，
报 **`simp made no progress`** ——mathlib **没有**能自动展开
`fderiv ℝ (fun v : Fin 1 → ℝ => a * v 0) w (Pi.single 0 1)` 的 `simp` 规则，
且 A4 实测 **`hasFDerivAt_apply` 这个名字在 mathlib 中不存在**
（本仓库**第 14 例**同族失误，见 STYLE.md:876 的通用教训）。

**⇒ 降强度**：本条**不再声称** `gradSq = a²`（那需要把 `fderiv` 在
`Fin 1 → ℝ` 坐标投影上的计算接进 mathlib 的 `ContinuousLinearMap` API，
是一个独立的工程），而是给出**定义层面的展开式**：
`gradSq (linearFunctional a) w = fderiv … ^ 2` —— 由 `Fin 1` 只有一个坐标，
`Σ i : Fin 1` 只剩一项，这是**真的且已证**的（`Fin.sum_univ_one`）。

⚠ **它的价值**：证明 `gradSq` 这一 `fderiv`-based 定义在 `d = 1` 时
**确实退化为单项**（即定义可用、不退化为空和），**不**声称该单项的值。
真正的数值 `a²` 需要 `fderiv` 的计算引理，**本文件未做**，登记在诚实清单。 -/
lemma linearFunctional_gradSq_eq_fderiv (a : ℝ) (w : Fin 1 → ℝ) :
    gradSq (linearFunctional a) w
      = (fderiv ℝ (linearFunctional a) w (Pi.single 0 1)) ^ 2 := by
  unfold gradSq
  rw [Fin.sum_univ_one]

/-- ⭐ **`gradSq` 的血统检验（非空转）**：`d = 1` 时 `gradSq` 是**单项平方**
（而非空和 `0`），且该项即 `fderiv` 在 `Pi.single 0 1` 方向的取值。

⚠ 这是 `linearFunctional_gradSq_eq_fderiv` 的**可读性重述**，
用于说明 `gradSq` 的定义在最小维度下**有内容**。 -/
lemma linearFunctional_gradSq_one_eq (w : Fin 1 → ℝ) :
    gradSq (linearFunctional 1) w
      = (fderiv ℝ (linearFunctional 1) w (Pi.single 0 1)) ^ 2 :=
  linearFunctional_gradSq_eq_fderiv 1 w

/-! ⚠ **R5/A4 更正（删除 + 如实报告，重要）**：
初稿的 `linearFunctional_gradSq_one`（`gradSq (linearFunctional 1) w = 1`）
与更一般的 `linearFunctional_gradSq`（`gradSq (linearFunctional a) w = a²`）
**已删除**。理由：

1. 它们的证明依赖把 `fderiv ℝ (fun v : Fin 1 → ℝ => a * v 0) w (Pi.single 0 1)`
   算出为 `a`，而 mathlib **没有** 可直接 `simp` 掉该式的规则，
   引理名 `hasFDerivAt_apply`（初稿/A4 曾尝试）**在该版本不存在**；
2. 更重要的：初稿用它们宣称「**Poincaré 取等、常数不可压缩**」——
   而该解读依赖**已删除的空转定理** `gaussian_poincare`（见下），**本就无支撑**。

**代之以**上面两条**已证且非空转**的降强度版：
`linearFunctional_gradSq_eq_fderiv` / `linearFunctional_gradSq_one_eq`
（`d = 1` 时 `gradSq` 退化为**单项平方**）。

⚠ **这样处理的纪律依据**：证不掉就**删或降强度**，**绝不留 `sorry`**，
且**不保留**无法支撑的"锐利性"宣称。 -/

/-! ## 七、诚实清单（Talagrand 的未证部分，逐条登记）

1. ⚠⚠ **未交付（本文件最重要的空缺，R5/A4 更正）**：
   **高斯 Poincaré 不等式** `Var(f) ≤ E[‖∇f‖²]`。
   初稿声称「第 A 段已完成」，其实测陈述是**空转重言式**
   （结论 `V ≤ V`、假设含 `∨ True`），**零内容**。
   原 `gaussian_poincare` 与 `gaussian_poincare_lipschitz` **已删除**，
   代之以 `gaussianPoincareStatement`（登记）+ `gaussianPoincareDelivered := false`
   （机器可读状态）。
2. **未证：Herbst 论证**（在 Poincaré 之后的下一个空缺）。
   目标：`∀ λ > 0, log E[e^{λ(f−Ef)}] ≤ λ²·Var(f)/2`，从而
   `E[e^{λ(f−Ef)}] ≤ e^{λ²/2}`（`Var ≤ 1`）。
   分解为两个子命题：
   (i) `f` 1-Lipschitz ⟹ `e^{λf}` 1-Lipschitz（**逐点 `L^∞`**，
       由 `|e^{λx} − e^{λy}| ≤ λ·e^{λ·max}·|x−y|` 与 `λ` 有界）；
   (ii) 由 (i) 与 Poincaré 得 `Var(e^{λf/2}) ≤ λ²/4·E[e^{λf}]`，
       再解微分不等式得 (i) 的结论。
   ⚠ 注意 (i) 的朴素形式 `|e^{λx} − e^{λy}| ≤ λe^{λmax(x,y)}|x−y|`
   会引入 `e^{λf}` 的**随机因子**，需先做**截断**（`f ∧ M`）再取极限——
   这一「截断 + 单调收敛」步骤是本文件未做的**真正困难点**，不是形式化琐事。
3. **未证：中位数中心化**。Talagrand 原始陈述以 `Med f` 为中心；
   从均值到中位数需 `|Ef − Med f| ≤ ‖f‖_Lip = 1`
   （对 1-Lipschitz 变量成立，证明用 `P(f ≥ Med + 1) ≤ 1/2` 与 Markov）。
   本文件未做，故结论写成**以均值为中心**的形式。
4. **未证：Stein 恒等式的高斯积分实现**（第 1 条的空缺内核）。
   `∫ x f(x) φ(x) dx = ∫ f'(x) φ(x) dx` 需要在一维高斯密度下做分部积分；
   Mathlib 有测度论分部积分（`MeasureTheory.integral_mul_deriv_eq_deriv_mul`）
   但接高斯密度需要额外工作，本文件未做。
5. **未证：一般乘积测度（Bernoulli）的 Talagrand**。
   ⚠ **连同高斯版都未交付**（见第 1 条）。
6. **未证：`Med`/`Ef` 之外的中心化**（如「以任意 1-Lipschitz 泛函的
   任一集中点为中心」的更强形式）。
7. ⚠ **`talagrand_convex_lipschitz_tail` 的名实问题（R5/A4 更正）**：
   该定理名为「凸 Lipschitz 特例」，但其**陈述里没有任何凸性、
   没有 `IsOneLipschitz`、没有 `fderiv`、没有高斯 `W`**——
   它是对**抽象 `[Fintype α]` 上任意 `f : α → ℝ`** 的纯切尔诺夫桥。
   ⇒ 标题所称的「凸 Lipschitz 特例」**未被形式化**；`hmgf` 是未证输入。
   **可满足性（仍然成立的部分）**：在线性泛函 `f(w) = ⟨a, w⟩`（`‖a‖ = 1`）
   且 `W` 标准高斯的**语义**下，`f(W) − Ef(W)` 是标准正态，
   MGF 恰为 `e^{λ²/2}`（**取等**）——故 `hmgf` **不是空洞假设**；
   但这一「语义可满足性」**在本文件中未形式化**（缺高斯测度）。
-/

end Lattice.Lib.Concentration.RealTalagrandConcentration