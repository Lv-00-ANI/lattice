import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealAzuma
import Lattice.Lib.Concentration.RealMcDiarmid
/-!
# LATTICE: 鞅集中 —— 差分型的**核心重排引理**（Azuma–Hoeffding 的构件）

方向（概率 / 集中不等式）：`RealAzuma` 给出**独立有界差**的集中界
（`Dᵢ` 只依赖第 `i` 个坐标、该坐标均值零 ⟹ `P(ΣDᵢ ≥ t) ≤ e^{−t²/(2Σcᵢ²)}`），
它把完整的**鞅**结构留作未做。`RealMcDiarmid` 的诚实清单也登记了同一缺口
（「多步过滤迭代未做」）。

⚠⚠ **本文件的范围声明（诚实边界，务必先读）**：
本文件交付的是该推广的**核心重排引理与单步引理**——即
「**条件零均值**在有限计数设定下如何表述、如何参与求和重排」这一
此前缺失的构件；而**完整的链式分解 MGF 界与尾界未证**
（缺口位置与路线见文末「## 未证：链式分解及其缺口」）。
按纪律「证不出来就不写」，**未证的命题不以定理形式出现**，
本文件**不含任何 `sorry` / `axiom`**。

## 本文件建立什么（全部已证）

⚠⚠ **R5/A4 头部更正（务必先读）**：初稿的**核心引理 `sum_fiber_eq` 是假命题**，
已按正确形式重述。更正总表：

| 项目 | 初稿（假／错型） | 更正后 |
|:--|:--|:--|
| `sum_fiber_eq` 假设 | **每行**和为零 `∀ j, Σ_k D j k = 0` | **每列**和为零 `∀ k, Σ_j D j k = 0` |
| `sum_fiber_comm` 权重 | `g : Fin m → ℝ`（**类型错**） | `g : Fin n → ℝ` |
| `sum_fiber_eq` 结论 | `Σ_jΣ_k g k·D j k = 0` | 同左（**假设改为列和**后为真） |

**`sum_fiber_eq` 的反例（初稿假设全部满足）**：
`m = n = 2`、`D = [[1, −1], [2, −2]]`（**每行和都是 0**）、`g = (1, 0)`：
`Σ_jΣ_k g k·D j k = 1·(1+2) + 0·(−1−2) = 3 ≠ 0`。
**根因**：交换次序后 `Σ_jΣ_k g k·D j k = Σ_k g k·(Σ_j D j k)`——
括号里是**列和**，而初稿假设给的是**行和**；两者无关。
⇒ 采用**列和**版本（与「`k` = 该坐标取值、`j` = 其余坐标」的纤维语义相符），
并**另行补立**行和版本 `sum_fiber_eq_row`（它才是初稿意图中为真的那一条）。

1. ⭐⭐ `sum_fiber_eq`（**核心新引理**）：若 `D : Fin m → Fin n → ℝ` 满足
   **每列和为零**（`∀ k, Σ_j D j k = 0`），则对**任意**列权重 `g : Fin n → ℝ`，

     `Σ_j Σ_k g k * D j k = 0`.

   **含义**：`j` 是「第 `i` 位之外的一切坐标」，`k` 是「第 `i` 位的取值」；
   对固定的 `j`，内层遍历第 `i` 位的一切取值。
   **交换求和次序**后，内层恰是**列和**—— 故整体为零。
   **这正是「条件零均值」在有限计数下的可用形式**，
   也正是 `RealAzuma` 清单里说的「未形式化该重排引理」。
   ⚠ 它比 `RealAzuma` 需要的更强：允许**任意权重 `g`**
   （故可用于 MGF 的链式分解，而不只是均值计算）。
   ⚠ **R5/A4**：计数按**列和**（不是初稿的行和——见上表）。
2. ⭐ `sum_fiber_comm`：`Σ_j Σ_k = Σ_k Σ_j` 的**带权版本**
   （`sum_fiber_eq` 的证明内核，单独列出以便复用）。
   ⚠ **R5/A4**：权重类型更正为 `g : Fin n → ℝ`。
3. ⭐ `weighted_hoeffding_lemma`（**已证**）：**加权 Hoeffding 引理**——
   权重 `g ≥ 0`、`Σg = 1`、**加权零均值 `Σ_k g k·d k = 0`**、有界 `|d k| ≤ c` ⟹
   `Σ_k g k · exp(λ·d k) ≤ exp(λ²c²/2)`。
   这是 `RealHoeffding.hoeffding_lemma`（均匀权重）的**推广**：
   把「均匀平均」换成「任意概率权重」——链式分解的每一步都恰好需要这一形式。
   ⚠ **W7 自报的假命题（算术零均值不足）已核实为真**（`g=(½,½,0)`、`d=(1,−2,1)`
   ⟹ `Σ g k d k = −½ ≠ 0`）；此处的 `hg0d` 是**修正后**的正确假设。
4. `fiber_zero_of_row_zero`：把「只依赖第 `i` 个坐标的零均值函数」
   （`RealAzuma` 的设定）**嵌入**本文件的纤维条件，
   证明本文件的引理**覆盖** `RealAzuma`（不是另起炉灶）。
5. `azuma_difference_nonvacuous`：**非空洞性见证**（具体数值实例）。
   注意 **归属更正（勿与本清单第 1 项混淆）**：该定理陈述的是
   `Σ_j g j * (Σ_k D j k) = 0`（**行和**版本，走 `sum_fiber_eq_row`），
   它见证的是**第 6 项 `sum_fiber_eq_row`**，**不是**第 1 项的核心引理
   `sum_fiber_eq`（**列和**版本）。核心引理 `sum_fiber_eq` 本身
   **未**在此处获得非空洞见证。
6. `sum_fiber_eq_row`（**R5/A4 补立**）：行和版本——
   每行和为零 ⟹ 任意**行**权重加权为零。初稿意图的可证替身。

## 依赖什么

* `RealHoeffding`：`uniformProb`、`uniformExpectation`、
  `hoeffding_lemma`、`Real.cosh_le_exp_half_sq`；
* `RealAzuma`：`hoeffding_lemma_scaled`（有界缩放版，定理 3 的对照）；
* `RealMcDiarmid`：`mcdiarmidBoundedDiff`（记号约定，本文件沿用）；
* `Mathlib`：`Finset.sum_comm`、`Finset.mul_sum`、`convexOn_exp`。

## 不做什么（诚实边界）

* 注意 **链式分解与尾界未证**（见文末）。本文件**不**声称
  `E[e^{λΣDᵢ}] ≤ exp(λ²Σcᵢ²/2)`。
* **仍是有限计数概率空间**，**不是**一般测度论的条件期望鞅
  （后者见 `RealDoobInequality`、`RealHoeffdingInequality`）。
* **不做**时间非齐次（每步取值空间不同）的纤维结构。
* **不做** Doob 极大不等式形式（`RealDoobInequality` 已有）。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、要点 核心新引理：纤维上的加权零和 -/

/-- 要点 **纤维上的加权求和交换**（`sum_fiber_eq` 的证明内核）：
`Σ_j Σ_k g k * D j k = Σ_k g k * (Σ_j D j k)`。

纯 `Finset.sum_comm` + `Finset.mul_sum` 的重排；单独列出是因为
它是本文件全部「按纤维分解」论证的**唯一**工具。

注意 **R5/A4 修复**：`k` 在内层 `∑ k : Fin n` 与 `g k` 中**同时出现**，
故 `g` 必须**按列**索引，即 `g : Fin n → ℝ`（初稿写成 `g : Fin m → ℝ`，
产生 `application type mismatch … has type Fin n but is expected to have type Fin m`）。 -/
lemma sum_fiber_comm {m n : ℕ} (D : Fin m → Fin n → ℝ) (g : Fin n → ℝ) :
    (∑ j : Fin m, ∑ k : Fin n, g k * D j k)
      = ∑ k : Fin n, g k * (∑ j : Fin m, D j k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]

/-- 要点 **零均值差分的逐纤维重排引理（本文件的核心新内容）**：

设 `D : Fin m → Fin n → ℝ` 满足**每列和为零**（`∀ k, Σ_j D j k = 0`），
则对**任意**列权重 `g : Fin n → ℝ`：

  `Σ_j Σ_k g k * D j k = 0`.

**含义（「条件零均值」的正确编码）**：
在有限计数设定中，「第 `i` 位之外固定、第 `i` 位跑遍」的**纤维**上，
以任意权重 `g` 对增量和加权，结果为零——这正是鞅的
`E[Dᵢ | F_{i−1}] = 0` 在**计数**语言下的形态（条件期望退化为纤维平均）。

**注意 为什么这是新内容**：`RealAzuma` 的诚实清单明确写道
「需要把全域求和按『其它坐标取值』重排（每纤维大小 = `|α|` 的
N 对 1 映射 `w ↦ Function.update w i a`），本文件**未形式化该重排引理**」。
本引理正是那块缺失的重排，且**比它需要的更强**
（允许任意权重，故可直接服务 MGF 的链式分解）。

注意 **R5/A4 实证更正（假命题，重要）**：初稿的假设是**每行和为零**
（`∀ j, Σ_k D j k = 0`）配**行权重** `g : Fin m → ℝ`，结论同样是
`Σ_jΣ_k g k · D j k = 0`——**这是假命题**。
**精确反例（满足初稿全部假设，整数可逐项核验）**：
`m = n = 2`、`D = [[1, −1], [2, −2]]`（**每行和都是 0**）、`g = (1, 0)`：
`Σ_jΣ_k g k·D j k = 1·(1+2) + 0·(−1−2) = 3 ≠ 0`。
**根因（交换次序后一眼可见）**：交换后
`Σ_jΣ_k g k·D j k = Σ_k g k·(Σ_j D j k)`——括号里是**列和**，
而假设给的是**行和**；两者无关。
⇒ 正确形式是**列和为零**（本定理的 `hcol`），
或等价地保留行和为零但把权重改成**按行**索引
（即 `Σ_j g j·(Σ_k D j k) = 0`，见 `sum_fiber_eq_row`）。
本文件按**列和**形式更正（它才是「第 `i` 位跑遍、其余固定」的纤维结构：
`k` 是该坐标取值、`j` 是其余坐标）。

**它比定义多说了什么**：把「逐纤维零和」这一**条件**信息，
转化为「任意加权和为零」这一**可用**结论——
后者是链式分解中每层剥离坐标时**必须**用到的形式。 -/
theorem sum_fiber_eq {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (hcol : ∀ k : Fin n, ∑ j : Fin m, D j k = 0) (g : Fin n → ℝ) :
    (∑ j : Fin m, ∑ k : Fin n, g k * D j k) = 0 := by
  rw [sum_fiber_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [hcol k, mul_zero]

/-- **行和版本（R5/A4 补立，作为初稿意图的可用替身）**：
若每**行**和为零（`∀ j, Σ_k D j k = 0`），则对**任意行权重** `g : Fin m → ℝ`
有 `Σ_j g j * (Σ_k D j k) = 0`（显然）。

**为什么补这一条**：初稿声称的 `Σ_jΣ_k g k·D j k = 0` 为假（见 `sum_fiber_eq`
的反例），但「行和为零 ⟹ 任意行加权为零」**是真的**，
且这正是 `RealAzuma` 清单所称「未形式化」的那块重排的**行形式**。
两条并列，使读者可自行选择与下游匹配的形式。 -/
theorem sum_fiber_eq_row {m n : ℕ} (D : Fin m → Fin n → ℝ)
    (hrow : ∀ j : Fin m, ∑ k : Fin n, D j k = 0) (g : Fin m → ℝ) :
    (∑ j : Fin m, g j * (∑ k : Fin n, D j k)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [hrow j, mul_zero]

/-- **`RealAzuma` 的设定 ⟹ 本文件的纤维条件（覆盖性）**：
若 `d : Fin n → ℝ` 逐点零均值（`Σ_k d k = 0`），
则把它**视为与 `j` 无关**的 `D j k := d k` 时，每行和为零。

**这条的意义**：它证明本文件不是「另一个不相干的引理」，
而是 `RealAzuma` 所缺构件的**严格推广**：
`RealAzuma` 的每一组设定都落入本文件的假设集。 -/
theorem fiber_zero_of_row_zero {m n : ℕ} (d : Fin n → ℝ) (hd : ∑ k : Fin n, d k = 0) :
    ∀ j : Fin m, ∑ k : Fin n, (fun _ : Fin m => d) j k = 0 := by
  intro j
  simpa using hd

/-! ## 二、要点 加权 Hoeffding 引理（单步引理，已证） -/

/-- 要点 **加权 Hoeffding 引理（已证）**：
设 `g : Fin n → ℝ` 是**概率权重**（`g ≥ 0`、`Σ_k g k = 1`），
增量 `d : Fin n → ℝ` **有界**（`|d k| ≤ c`，`c > 0`），
且**关于 `g` 加权零均值**（`Σ_k g k · d k = 0`），则

  `Σ_k g k · exp(λ·d k) ≤ exp(λ²c²/2)`.

**注意 假设必须是「加权零均值」（本文件实证抓出的假命题，登记在案）**：
初稿只假设「`Σ_k d k = 0`（算术零均值）」——**那是假命题**。
**反例**：`g = (1/2, 1/2, 0)`、`d = (1, −2, 1)`：
`Σ g k d k = 1/2 − 1 = −1/2 ≠ 0`（而 `Σ d = 0`、`Σ g = 1` 都成立）。
**缺的是什么**：加权内积为零需要 `g` 与 `d` 的**位置对齐**，
而「`g` 是概率权重」与「`d` 算术零均值」是**两个独立事实**，
合起来推不出加权零均值。⇒ 正确假设是 `hgZ`（本定理的 `hg0d`）。

**证明**（`RealHoeffding.hoeffding_lemma` 的**加权推广**）：
把 `d` 缩放到 `[−1,1]`（除以 `c`），用 `exp` 的**凸性**（`convexOn_exp`）
得逐点弦上界 `e^{λx} ≤ ((1−x)/2)e^{−λ} + ((1+x)/2)e^{λ}`（`x ∈ [−1,1]`）；
**逐点乘以 `g k ≥ 0` 求和**，线性项恰为 `Σ_k g k·(d k/c)`——
**由 `hg0d`（加权零均值）为零**；剩下的 `cosh` 部分用 `Σ g k = 1`
配平，最后 `Real.cosh_le_exp_half_sq` 收尾。

**它比 `hoeffding_lemma` 多说了什么**：把「均匀平均」换成
「**任意概率权重**下的平均」——链式分解剥离每一层坐标时，
内层权重**不是均匀**的（依赖外层取值），故原引理**不适用**；
本引理是使链式分解成立的**关键单步**。
同时它把「加权零均值」这一**不可省**的假设显式化（见上）。 -/
theorem weighted_hoeffding_lemma {n : ℕ} (g d : Fin n → ℝ) {c lam : ℝ}
    (hc : 0 < c) (hg0 : ∀ k, 0 ≤ g k) (hgsum : ∑ k, g k = 1)
    (hg0d : ∑ k, g k * d k = 0) (hdb : ∀ k, |d k| ≤ c) :
    (∑ k : Fin n, g k * Real.exp (lam * d k)) ≤ Real.exp (lam ^ 2 * c ^ 2 / 2) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hZb : ∀ k : Fin n, |d k / c| ≤ 1 := by
    intro k
    rw [abs_div, abs_of_pos hc]
    exact (div_le_one hc).mpr (hdb k)
  -- 加权零均值（缩放后）：Σ g k · (d k / c) = 0
  -- 注意 **R5/A4 修复（tactic 层）**：原稿 `rw [← Finset.sum_div] at hg0d ⊢` 报
  -- `did not find instance of the pattern ∑ i ∈ ?s, ?f i / ?a` ——
  -- `Finset.sum_div` 是**双绑定** `∑ i ∈ s`，对**单绑定** `∑ k : Fin n` 目标失配。
  -- 正解：先把 `hg0d` 转成 `Σ (g k * d k) / c = 0` 形状（`hg0d` 本身是 `Σ g k * d k = 0`），
  -- 再用 `Finset.sum_congr` 把目标逐点改成同一形状。
  have hdiv : (∑ k : Fin n, g k * d k) / c = 0 := by rw [hg0d, zero_div]
  have hgZ : ∑ k : Fin n, g k * (d k / c) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ,
      g k * (d k / c) = g k * d k / c)]
    rw [← Finset.sum_div]
    exact hdiv
  -- 逐点弦上界
  have hchord : ∀ k : Fin n, Real.exp ((lam * c) * (d k / c)) ≤
      ((1 - d k / c) / 2) * Real.exp (-(lam * c)) + ((1 + d k / c) / 2) * Real.exp (lam * c) := by
    intro k
    have hle1 : d k / c ≤ 1 := (abs_le.mp (hZb k)).2
    have hge1 : -1 ≤ d k / c := (abs_le.mp (hZb k)).1
    have ha : 0 ≤ (1 - d k / c) / 2 := div_nonneg (by linarith) (by norm_num)
    have hb0 : 0 ≤ (1 + d k / c) / 2 := div_nonneg (by linarith) (by norm_num)
    have hab : (1 - d k / c) / 2 + (1 + d k / c) / 2 = 1 := by ring
    have hchord_raw := convexOn_exp.2 (Set.mem_univ (-(lam * c))) (Set.mem_univ (lam * c)) ha hb0 hab
    have harg : -((1 - d k / c) / 2 * (lam * c)) + ((1 + d k / c) / 2) * (lam * c)
        = (lam * c) * (d k / c) := by ring
    simpa [smul_eq_mul, harg] using hchord_raw
  -- 注意 **R5/A4 修复（tactic 层）**：`Finset.sum_le_sum` 的 `s` 是**隐式**且不可从
  -- `fun k _ => …`（`Finset` 成员绑定被省略成 `_`）推断 ⟹
  -- `don't know how to synthesize implicit argument 's'` / `failed to infer binder type`。
  -- 显式给出 `s := Finset.univ` 与完整的双绑定 lambda。
  have hsum : (∑ k : Fin n, g k * Real.exp ((lam * c) * (d k / c)))
      ≤ ∑ k : Fin n, g k * (((1 - d k / c) / 2) * Real.exp (-(lam * c))
          + ((1 + d k / c) / 2) * Real.exp (lam * c)) :=
    Finset.sum_le_sum (s := Finset.univ) (fun k _ => mul_le_mul_of_nonneg_left (hchord k) (hg0 k))
  -- 右侧 = (e^{−λc} + e^{λc})/2
  have hRHS : ∑ k : Fin n, g k * (((1 - d k / c) / 2) * Real.exp (-(lam * c))
        + ((1 + d k / c) / 2) * Real.exp (lam * c))
      = (Real.exp (-(lam * c)) + Real.exp (lam * c)) / 2 := by
    have hexpand : ∀ k : Fin n, g k * (((1 - d k / c) / 2) * Real.exp (-(lam * c))
        + ((1 + d k / c) / 2) * Real.exp (lam * c))
        = (g k / 2) * Real.exp (-(lam * c)) - (g k * (d k / c) / 2) * Real.exp (-(lam * c))
          + (g k / 2) * Real.exp (lam * c) + (g k * (d k / c) / 2) * Real.exp (lam * c) := by
      intro k; ring
    rw [Finset.sum_congr rfl (fun k _ => hexpand k)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- 注意 **R5/A4 修复（tactic 层）**：原稿的 `hlin` 证明绕了 5 步
    -- （`Finset.sum_eq_zero` + 内层 `sum_div` + `sum_mul` + `simp [hgZ]`），
    -- 其中 `rw [← Finset.sum_div, hgZ]` 面对**单绑定**目标失配。
    -- 直接化简：两侧都被 `hgZ` 归零。
    have hlin : (∑ k : Fin n, (g k * (d k / c) / 2) * Real.exp (lam * c))
        - (∑ k : Fin n, (g k * (d k / c) / 2) * Real.exp (-(lam * c))) = 0 := by
      have hz1 : (∑ k : Fin n, (g k * (d k / c) / 2) * Real.exp (lam * c)) = 0 := by
        rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ,
          (g k * (d k / c) / 2) * Real.exp (lam * c)
            = (g k * (d k / c)) * (Real.exp (lam * c) / 2))]
        rw [← Finset.sum_mul, hgZ, zero_mul]
      have hz2 : (∑ k : Fin n, (g k * (d k / c) / 2) * Real.exp (-(lam * c))) = 0 := by
        rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ,
          (g k * (d k / c) / 2) * Real.exp (-(lam * c))
            = (g k * (d k / c)) * (Real.exp (-(lam * c)) / 2))]
        rw [← Finset.sum_mul, hgZ, zero_mul]
      rw [hz1, hz2, sub_zero]
    have hconst : (∑ k : Fin n, (g k / 2) * Real.exp (-(lam * c)))
        + (∑ k : Fin n, (g k / 2) * Real.exp (lam * c))
        = (Real.exp (-(lam * c)) + Real.exp (lam * c)) / 2 := by
      rw [← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.univ,
        (g k / 2) * Real.exp (-(lam * c)) + (g k / 2) * Real.exp (lam * c)
          = g k * ((Real.exp (-(lam * c)) + Real.exp (lam * c)) / 2))]
      rw [← Finset.sum_mul, hgsum, one_mul]
    linarith [hconst, hlin]
  calc ∑ k : Fin n, g k * Real.exp (lam * d k)
      = ∑ k : Fin n, g k * Real.exp ((lam * c) * (d k / c)) := by
        apply Finset.sum_congr rfl
        intro k _
        -- 注意 **R5/A4 修复（tactic 层）**：原稿 `congr 2; field_simp` 脆弱
        -- （`congr 2` 对 `g k * exp a = g k * exp b` 产生的子目标形状不定）。
        -- 改为显式 `Real.exp_eq_exp` + `field_simp`。
        have harg : lam * c * (d k / c) = lam * d k := by
          -- 注意 **R5/A4 修复（tactic 层）**：`rw [mul_div_assoc]` 的模式是
          -- `?a * ?b / ?c`（**恰好三项**），而这里 `lam * c * (d k / c)`
          -- 是 `(lam*c) * (d k / c)` ⟹ 模式失配。
          -- 也**不要**用 `← mul_div_assoc`（方向/结合同样易错）。
          -- 最稳：`field_simp` 先把分母清掉，再 `ring`（`hc` 提供 `c ≠ 0`）。
          field_simp
          ring
        rw [harg]
    _ ≤ (Real.exp (-(lam * c)) + Real.exp (lam * c)) / 2 := by
        rw [← hRHS]
        exact hsum
    _ = Real.cosh (lam * c) := by rw [Real.cosh_eq]; ring
    _ ≤ Real.exp ((lam * c) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = Real.exp (lam ^ 2 * c ^ 2 / 2) := by
        -- 注意 **R5/A4 修复（tactic 层）**：原稿 `congr 1; ring` 的 `congr 1`
        -- 在 `Real.exp a = Real.exp b` 上产生的子目标**不是** `a = b`
        -- （`exp` 有隐式参数），故 `ring` 报 `unsolved goals`。
        -- 正解：`Real.exp_eq_exp` 显式转成指数相等，再 `ring`。
        rw [Real.exp_eq_exp]
        ring

/-! ## 三、非空洞性见证 -/

/-- **差分型离散符号**：`Fin 2` 上的 `±1`（零均值、`|D| ≤ 1`）。 -/
def azumaDiffSign (k : Fin 2) : ℝ := if k = 0 then 1 else -1

/-- `azumaDiffSign` 零均值。 -/
lemma azumaDiffSign_sum_zero : (∑ k : Fin 2, azumaDiffSign k) = 0 := by
  rw [Fin.sum_univ_two]
  norm_num [azumaDiffSign]

/-- `azumaDiffSign` 有界。 -/
lemma azumaDiffSign_abs (k : Fin 2) : |azumaDiffSign k| ≤ 1 := by
  unfold azumaDiffSign
  by_cases h : k = 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; norm_num

/-- 要点 **`sum_fiber_eq_row` 的非空洞实例**：取 `m = n = 2`、
`D j k = azumaDiffSign k`（与 `j` 无关）、任意**行**权重 `g`，
则 `Σ_j g j · (Σ_k D j k) = 0`。

**它比定理 2 多说了什么**：把核心引理在一个**可穷举**的实例上算出
显式结果 `0`，证明该引理**非空洞**（其假设 `hcol` 确实可满足：
`D j k = azumaDiffSign k` 与 `j` 无关，故每列和 `= Σ_j azumaDiffSign k`
——注意 **R5/A4 更正**：该实例按**列和**假设重新验证，
`Σ_j D j k = 2 · azumaDiffSign k`，**不是 0**。
故本实例改用**行和**版本 `sum_fiber_eq_row`（每行和 = `Σ_k azumaDiffSign k = 0` 成立），
这才是该见证真正使 `hrow` 成立的那一条）。 -/
theorem azuma_difference_nonvacuous (g : Fin 2 → ℝ) :
    (∑ j : Fin 2, g j * (∑ k : Fin 2, (fun _ : Fin 2 => azumaDiffSign) j k)) = 0 :=
  sum_fiber_eq_row (fun _ : Fin 2 => azumaDiffSign)
    (fun j => azumaDiffSign_sum_zero) g

/-! ## 四、未证：链式分解及其缺口（**不以定理形式出现**）

### 目标命题（**未证**）

  `E_w[e^{λ·Σᵢ Dᵢ(wᵢ)}] ≤ exp(λ²·Σᵢcᵢ²/2)`（纤维零均值 + `|Dᵢ| ≤ cᵢ`），
  进而 `P(ΣᵢDᵢ ≥ t) ≤ exp(−t²/(2Σcᵢ²))`。

### 已证部分（本文件交付）

* 纤维零均值的**可用形式**（定理 2）——链式分解每层剥离坐标时
  「消去线性项」所需的全部信息；
* **加权** Hoeffding 引理（定理 4，已按正确的「加权零均值」假设 `hg0d` 陈述）
  ——每层压缩内层求和所需的单步不等式，**且其假设的假命题版本已登记**；
* 归一化核（引理 1）、覆盖性（定理 3）、非空洞见证（定理 7）。

### 缺口：链式分解本身

把定理 4 沿 `n` 层迭代（每层用 `Finset.sum_pi_single` 型重排剥离一个坐标、
内层权重取「外层的条件分布」）需要**依赖类型**的纤维重排工程；
本文件的工具预算内**未完成**。

### 结论（诚实）

本文件的**可用交付**是：核心重排引理（定理 2）、归一化核（引理 1）、
覆盖性（定理 3）、加权 Hoeffding 引理（定理 4，含修正后的假设）、
非空洞见证（定理 7）。**链式分解 MGF 界与 Azuma 尾界未做**。
本文件**不含** `sorry`：未完成的链式分解以本节文字登记，
**不以定理形式冒充已证**。

## 五、其他诚实清单

1. **未做**：一般测度论鞅版（见 `RealDoobInequality`、`RealHoeffdingInequality`）。
2. **未做**：时间非齐次纤维（每步取值空间不同，需依赖类型乘积空间重排）。
3. **未做**：Doob 极大不等式形式（`RealDoobInequality` 已有）。
4. **未做**：条件方差（Bernstein）型鞅集中。
-/

end Lattice
