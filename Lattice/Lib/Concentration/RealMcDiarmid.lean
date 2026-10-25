import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: 有界差分（McDiarmid）不等式 —— 有限计数版本

方向（§5 验证行「McDiarmid」）：`RealHoeffding` 只处理 **同分布独立** 的变量和
（n 个独立副本 X(Xᵢ)），而实际的学习/验证损失往往是 **有界差分函数**
f(x₁,…,xₙ)（改变任意一个坐标对 f 的影响不超过常数 cᵢ）。本文件在
`RealHoeffding` 的有限计数概率空间上建立 McDiarmid（有界差分）不等式：

* **定义** `mcdiarmidBoundedDiff`：`|f z − f(z 的第 i 位改为 z')| ≤ cᵢ`。
* **拆项** `mcdiarmid_telescope`：只改动坐标集合 `s` 时
  `|f z − f z'| ≤ ∑_{i∈s} cᵢ`（Finset 归纳 + 三角不等式）。
* **极差界** `mcdiarmid_range_le`：`|f z − f z'| ≤ ∑ᵢ cᵢ`。
* **核心结构定理** `mcdiarmid_tail_of_mgf`：把 MGF 界
  `E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}` 作为 **显式假设**，导出尾界
  `P(f−Ef ≥ t) ≤ e^{−2t²/Σcᵢ²}`；并给出双边版本
  `mcdiarmid_two_sided_of_mgf`。

> **⚠ 常数约定的显式说明（Z1-1，v14；结论：`/8` 正确，无需改动）**
>
> **本条为「经复核确认」而非「修复」**：跨文件扫描曾报「`/8` 与增量式定义冲突、
> 应为 `/2`」——**该报告不成立**。经复核，**`/8` 与 `:68-70` 的增量式定义
> 完全协调**（二者**等价**，见下），故**代码未作任何改动**；
> 下方说明是**新增的约定澄清文档**，不是对既有 bug 的修补。
>
> 本项目存在**两种**并存的 Hoeffding/MGF 常数写法，二者**不是矛盾而是同一界**，
> 区别只在 `c` 的**约定**：
>
> | 约定 | `c` 的含义 | Hoeffding 引理 | 单坐标因子 | 尾界常数 |
> |:--|:--|:--|:--|:--|
> | **极差/区间长** | `φᵢ` 的**值域长度** `≤ cᵢ` | `e^{λ²(b−a)²/8}` | `e^{λ²cᵢ²/8}` | `e^{−2t²/Σcᵢ²}` |
> | **绝对界** | `\|X\| ≤ cᵢ`（值域长 `≤ 2cᵢ`） | 同上，代入 `b−a = 2cᵢ` | `e^{λ²cᵢ²/2}` | `e^{−t²/(2Σcᵢ²)}` |
>
> **换算**：`c_极差 = 2·c_绝对`，故 `Σc_极差²/8 = Σ(2c_绝对)²/8 = Σc_绝对²/2`
> —— **两式恒等**。
>
> **本文件用的是「极差」约定**（`:68-70` 的 `mcdiarmidBoundedDiff` 逐字给出
> `|f z − f (update z i z')| ≤ cᵢ`）。该定义与「`φᵢ` 值域长 `≤ cᵢ`」
> **等价**（两个方向都成立）：
> * (⟹) 取 `z := z₀`、`z' := u` 与 `z := z₀`、`z' := v`，三角不等式给出
>   逐对界；更强地，取 `z := update z₀ i u`、`z' := v` 并由
>   `update (update z₀ i u) i v = update z₀ i v` 得
>   `|f(update z₀ i u) − f(update z₀ i v)| ≤ cᵢ`；
> * (⟸) 值域长 `≤ cᵢ` 直接给出定义中每一条不等式（`update z i z'` 与 `z`
>   只差第 `i` 位）。
> ⟹ **`/8` 是本约定的正确常数**（`RealAzuma.lean:127` 的 `/2` 与
> `RealFiltrationIteration.lean:41,43,47` 的 `/2` 是**绝对界约定**下的同一界，
> 见 `RealFiltrationIteration.lean:63-74` 的既有如实标注）。
>
> **数值交叉验证（决定性）**：本文件 `:311` **已证**
> `mcdiarmid_additive_mgf : E[e^{λ·Σgᵢ}] ≤ e^{nλ²/2}`（加性实例、`cᵢ = 2`）。
> 若把 `:165` 的 `/8` 改成 `/2`，则 `hmgf` 变成 `e^{λ²·Σcᵢ²/2} = e^{2nλ²}`
> —— 与已证的 `e^{nλ²/2}` **相差因子 8（指数差 4 倍）**，**会把定理变成假命题**。
> 反之 `/8` 给出 `e^{λ²·4n/8} = e^{nλ²/2}`，**逐字吻合**。故 `/8` 保持不动。

* **完全证明的加性实例**（异构 Hoeffding）：`f w = ∑ᵢ gᵢ(wᵢ)`，每个 gᵢ
  零均值、`|gᵢ| ≤ 1`，此时有界差分常数 cᵢ = 2，得到
  `P(∑gᵢ ≥ t) ≤ e^{−t²/(2n)}` 及其双边版本 —— 这就是 McDiarmid 界在该
  实例下的精确取值。

**复用记号（全部来自已构建的模块，本文件不重新定义）**：
* `uniformProb`（`RealSamplingBoost`）：有限集上的均匀概率 `s.card / |α|`。
* `uniformExpectation`（`RealHoeffding`）：有限集上的均匀期望 `(∑ X)/|α|`。
* `sum_eq_zero_of_uniformExpectation_eq_zero`（`RealHoeffding`）：期望为 0
  （|α| > 0）⟹ 总和为 0，用于把零均值转成 `hoeffding_lemma` 的 `hzero`。
* `hoeffding_lemma`（`RealHoeffding`）：`|X| ≤ 1`、`EX = 0` ⟹
  `E[e^{λX}] ≤ e^{λ²/2}`；加性实例的每个坐标因子都用它。
* `markov_exp_tail`（`RealHoeffding`）：切尔诺夫马尔可夫桥
  `P(S ≥ t) ≤ e^{−λt} E[e^{λS}]`（λ > 0）；所有尾界都由它导出。
* `Real.exp_sum`、`Finset.prod_univ_sum`、`Fintype.card_pi_const`
  （Mathlib）：乘积空间上的指数/求和分解，是加性实例 MGF 乘积化的工具。

**诚实说明**：本文件不使用 `sorry` / `axiom` / `admit`。真正的 McDiarmid MGF
界（对 n 步鞅/过滤迭代证明 `E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}`）**未证**，
在 `mcdiarmid_tail_of_mgf` 中作为显式假设 `hmgf` 标注出来；详见文件末尾
「## 注」。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 复用记号（注释，无新声明）

`uniformProb`（`RealSamplingBoost`）= `s.card / Fintype.card α`；本文件所有
概率事件都形如 `Finset.univ.filter (fun w => …)`。
`uniformExpectation`（`RealHoeffding`）= `(∑ x, X x) / Fintype.card α`。
`markov_exp_tail`（`RealHoeffding`）提供指数马尔可夫桥。
`hoeffding_lemma`（`RealHoeffding`）提供单坐标因子的 `e^{λ²/2}` 上界。
`sum_eq_zero_of_uniformExpectation_eq_zero`（`RealHoeffding`）把零均值化为零和。 -/

/-! ## 定义：有界差分 -/

/-- **有界差分定义**。`mcdiarmidBoundedDiff n f c` 表示：函数
`f : (Fin n → Z) → ℝ` 在任意坐标 `i` 上、把取值改成任意 `z' : Z` 时，
函数值的变化量被 `c i` 控制，即
`|f z − f (Function.update z i z')| ≤ c i`。

这里 `Function.update z i z'` 是 Mathlib 的坐标替换（需要 `[DecidableEq Z]`），
它把 `z : Fin n → Z` 的第 `i` 位替换为 `z'`。这是 McDiarmid 不等式的核心
「有界差分」假设。

**⚠ 约定标注（Z1-1，v14）**：本定义刻画的是**单坐标增量**，它与
「固定其余坐标后 `z' ↦ f(update z i z')` 的**值域长度（极差）** `≤ c i`」
**等价**（⟸ 显然；⟹ 取 `z := update z₀ i u`、`z' := v` 并用
`update (update z₀ i u) i v = update z₀ i v`）。⟹ `c i` 是**极差**，
故 `hmgf` 的正确常数是 `/8`（**不是** `/2`；`/2` 对应的是「`|d| ≤ c`」
即值域长 `≤ 2c` 的**绝对界**约定，见文件头 §「常数约定的显式说明」）。 -/
def mcdiarmidBoundedDiff {Z : Type*} [DecidableEq Z] (n : ℕ) (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (z : Fin n → Z) (z' : Z), |f z - f (Function.update z i z')| ≤ c i

/-! ## 拆项引理（telescope） -/

/-- **坐标拆项引理（telescope）**。若 `z` 与 `z'` 只在有限坐标集合 `s` 上
可能不同（`∀ i ∉ s, z i = z' i`），且有界差分假设 `hbd` 成立，则
`|f z − f z'| ≤ ∑_{i∈s} cᵢ`。

证明：对 `s` 作 `Finset.induction_on`。空集时由 `∀ i, z i = z' i` 得
`z = z'`（`funext`），两边为 0。归纳步取 `a ∈ insert a s`，令
`z'' := Function.update z a (z' a)`，用三角不等式 `abs_sub_le` 拆分为
`|f z − f z''| + |f z'' − f z'|`：第一项由 `hbd a z (z' a)` 得 `≤ c a`；
第二项对 `z'' / z'` 用归纳假设（`∀ i ∉ s, z'' i = z' i`，由 `Function.update`
的 `update_noteq` 与前提给出）。 -/
theorem mcdiarmid_telescope {Z : Type*} [DecidableEq Z] (n : ℕ) (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) (hbd : mcdiarmidBoundedDiff n f c)
    (s : Finset (Fin n)) (z z' : Fin n → Z) (h : ∀ i ∉ s, z i = z' i) :
    |f z - f z'| ≤ ∑ i in s, c i := by
  classical
  revert z z' h
  refine Finset.induction_on s ?base ?step
  · intro z z' h
    have hzz : z = z' := by
      funext i
      exact h i (Finset.not_mem_empty i)
    rw [hzz]
    simp
  · intro a s ha ih z z' h
    let z'' : Fin n → Z := Function.update z a (z' a)
    have h1 : |f z - f z''| ≤ c a := by
      dsimp [z'']
      exact hbd a z (z' a)
    have h2 : |f z'' - f z'| ≤ ∑ i in s, c i := by
      apply ih
      intro i hi
      show z'' i = z' i
      by_cases hia : i = a
      · simpa [z'', hia] using Function.update_same a (z' a) z
      · dsimp [z'']
        rw [Function.update_noteq hia (z' a) z]
        exact h i (by
          intro hmem
          rw [Finset.mem_insert] at hmem
          rcases hmem with hmem | hmem
          · exact absurd hmem hia
          · exact hi hmem)
    calc
      |f z - f z'| ≤ |f z - f z''| + |f z'' - f z'| := abs_sub_le _ _ _
      _ ≤ c a + ∑ i in s, c i := add_le_add h1 h2
      _ = ∑ i in insert a s, c i := by rw [Finset.sum_insert ha]

/-! ## 极差界 -/

/-- **极差界（corollary）**。若 `c` 逐点非负（`hc`）且有界差分 `hbd` 成立，
则任意两样本的函数值之差被 `∑ᵢ cᵢ` 控制：`|f z − f z'| ≤ ∑ᵢ cᵢ`。
由 `mcdiarmid_telescope` 取 `s = Finset.univ`（此时前提 `∀ i ∉ univ, …`
空洞成立）得到；`hc` 作为假设列出以便与实际使用一致。 -/
theorem mcdiarmid_range_le {Z : Type*} [DecidableEq Z] (n : ℕ) (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) (hbd : mcdiarmidBoundedDiff n f c) (hc : ∀ i : Fin n, 0 ≤ c i)
    (z z' : Fin n → Z) : |f z - f z'| ≤ ∑ i : Fin n, c i := by
  have h := mcdiarmid_telescope n f c hbd (Finset.univ : Finset (Fin n)) z z'
    (fun i hi => absurd (Finset.mem_univ i) hi)
  simpa using h

/-! ## 期望取负的小引理（供双边版本使用） -/

/-- **期望的取负法则**：`E[−X] = −E[X]`。用于把「下尾事件」化为「对 `−f`
的上尾事件」，从而在双边界中复用单边上尾定理。 -/
lemma mcdiarmid_uniformExpectation_neg {α : Type*} [Fintype α] (X : α → ℝ) :
    uniformExpectation (fun x => -X x) = - uniformExpectation X := by
  unfold uniformExpectation
  rw [Finset.sum_neg_distrib, neg_div]

/-! ## 核心结构定理：由 MGF 界导出 McDiarmid 尾界 -/

/-- **由 MGF 界导出单边 McDiarmid 尾界（核心结构定理，含 `未证` 假设）**。

假设 `hmgf`：对一切 `lam > 0`，
`E[e^{lam·(f − Ef)}] ≤ e^{lam²·(∑ᵢ cᵢ²)/8}`。
则 `P(f − Ef ≥ t) ≤ e^{−2t²/(∑ᵢ cᵢ²)}`（`t > 0`）。

证明：取 `lam := 4t / ∑ᵢ cᵢ²`（由 `hpos` 知分母为正），用
`markov_exp_tail`（切尔诺夫马尔可夫桥）得
`P ≤ e^{−lam·t} · E[e^{lam(f−Ef)}] ≤ e^{−lam·t} · e^{lam²·Σc²/8}`，
再用 `Real.exp_add` 合并指数并由 `field_simp`/`ring` 化简恒等式
`−lam·t + lam²·Σc²/8 = −2t²/Σc²`。

**诚实标注（`未证`）**：`hmgf` 本身（真正需要 n 步过滤/鞅迭代证明的
McDiarmid MGF 界）在本文件中 **未证**，它作为定理的显式假设出现；本定理
只证明「由该 MGF 界可推出尾界」这一结构性的推导。 -/
theorem mcdiarmid_tail_of_mgf {Z : Type*} [Fintype Z] (n : ℕ) (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (hpos : 0 < ∑ i : Fin n, c i ^ 2) {t : ℝ} (ht : 0 < t)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun w : Fin n → Z => Real.exp (lam * (f w - uniformExpectation f)))
        ≤ Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 8)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ f w - uniformExpectation f))
      ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  classical
  let S : ℝ := ∑ i : Fin n, c i ^ 2
  have hS : 0 < S := hpos
  have hSne : S ≠ 0 := ne_of_gt hS
  let lam : ℝ := 4 * t / S
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (by linarith) hS
  have hmarkov := markov_exp_tail
    (S := fun w : Fin n → Z => f w - uniformExpectation f) (t := t) (lam := lam) hlam
  have hmgf' : uniformExpectation
      (fun w : Fin n → Z => Real.exp (lam * (f w - uniformExpectation f)))
      ≤ Real.exp (lam ^ 2 * S / 8) := by
    simpa [S] using hmgf lam hlam
  have hmain : uniformProb
      (Finset.univ.filter (fun w : Fin n → Z => t ≤ f w - uniformExpectation f))
      ≤ Real.exp (-2 * t ^ 2 / S) := by
    calc
      uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ f w - uniformExpectation f))
          ≤ Real.exp (-lam * t) * uniformExpectation
              (fun w : Fin n → Z => Real.exp (lam * (f w - uniformExpectation f))) := hmarkov
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * S / 8) :=
            mul_le_mul_of_nonneg_left hmgf' (Real.exp_nonneg _)
      _ = Real.exp (-2 * t ^ 2 / S) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [lam]
            field_simp [hSne]
            ring
  simpa [S] using hmain

/-- **由 MGF 界导出双边 McDiarmid 尾界（含 `未证` 假设）**。

除 `f` 的 MGF 界 `hmgf` 外，再假设 `−f` 的 MGF 界 `hmgf_neg`（同样是 `未证`
的 MGF 型假设），则
`P(|f − Ef| ≥ t) ≤ 2 · e^{−2t²/Σcᵢ²}`。

证明：事件 `{t ≤ |a|}`（`a := f w − Ef`）含于
`{t ≤ a} ∪ {t ≤ −a}`（`|a| ≥ t` 时若 `a ≥ 0` 则 `a ≥ t`，否则 `−a = |a| ≥ t`）；
上界分别由 `mcdiarmid_tail_of_mgf` 作用于 `f` 与 `−f` 得到（`−f` 的中心化量
`(−f) − E(−f) = −(f − Ef)`，用 `mcdiarmid_uniformExpectation_neg` 转化），
最后用并集界 `Finset.card_union_le` 相加，并用 `ring` 合并为 `2 ·`。

**诚实标注（`未证`）**：`hmgf` 与 `hmgf_neg` 均为 MGF 型显式假设，未在本文件
中证明。 -/
theorem mcdiarmid_two_sided_of_mgf {Z : Type*} [Fintype Z] (n : ℕ) (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (hpos : 0 < ∑ i : Fin n, c i ^ 2) {t : ℝ} (ht : 0 < t)
    (hmgf : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun w : Fin n → Z => Real.exp (lam * (f w - uniformExpectation f)))
        ≤ Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 8))
    (hmgf_neg : ∀ lam : ℝ, 0 < lam →
      uniformExpectation (fun w : Fin n → Z => Real.exp (lam * ((-f) w - uniformExpectation (-f))))
        ≤ Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 8)) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ |f w - uniformExpectation f|))
      ≤ 2 * Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
  classical
  let B := Finset.univ.filter (fun w : Fin n → Z => t ≤ f w - uniformExpectation f)
  let C := Finset.univ.filter (fun w : Fin n → Z => t ≤ -(f w - uniformExpectation f))
  have hsub : Finset.univ.filter (fun w : Fin n → Z => t ≤ |f w - uniformExpectation f|)
      ⊆ B ∪ C := by
    intro w hw
    have hA : t ≤ |f w - uniformExpectation f| := (Finset.mem_filter.mp hw).2
    have hcases : t ≤ f w - uniformExpectation f ∨ t ≤ -(f w - uniformExpectation f) := by
      by_cases h1 : t ≤ f w - uniformExpectation f
      · exact Or.inl h1
      · right
        have hneg : f w - uniformExpectation f < 0 := by
          by_contra h
          have h0 : 0 ≤ f w - uniformExpectation f := le_of_not_gt h
          rw [abs_of_nonneg h0] at hA
          exact h1 hA
        rw [abs_of_neg hneg] at hA
        exact hA
    rcases hcases with hl | hr
    · rw [Finset.mem_union]
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
    · rw [Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  have hmono : uniformProb
      (Finset.univ.filter (fun w : Fin n → Z => t ≤ |f w - uniformExpectation f|))
      ≤ uniformProb (B ∪ C) := by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg _)
  have hsubadd : uniformProb (B ∪ C) ≤ uniformProb B + uniformProb C := by
    unfold uniformProb
    calc
      (B ∪ C).card / (Fintype.card (Fin n → Z) : ℝ)
          ≤ (B.card + C.card) / (Fintype.card (Fin n → Z) : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_union_le B C))
              (Nat.cast_nonneg _)
      _ = B.card / (Fintype.card (Fin n → Z) : ℝ)
            + C.card / (Fintype.card (Fin n → Z) : ℝ) := by ring
  have hB : uniformProb B ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) :=
    mcdiarmid_tail_of_mgf n f c hN hn hpos ht hmgf
  have hC : uniformProb C ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by
    have hCeq : C = Finset.univ.filter
        (fun w : Fin n → Z => t ≤ (-f) w - uniformExpectation (-f)) := by
      dsimp only [C]
      apply Finset.filter_congr
      intro w _
      have hE : uniformExpectation (-f) = - uniformExpectation f := by
        simpa using mcdiarmid_uniformExpectation_neg (f : (Fin n → Z) → ℝ)
      simp only [Pi.neg_apply, hE]
      constructor <;> intro hh <;> linarith
    rw [hCeq]
    exact mcdiarmid_tail_of_mgf n (-f) c hN hn hpos ht hmgf_neg
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ |f w - uniformExpectation f|))
        ≤ uniformProb (B ∪ C) := hmono
    _ ≤ uniformProb B + uniformProb C := hsubadd
    _ ≤ Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2)
          + Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := add_le_add hB hC
    _ = 2 * Real.exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by ring

/-! ## 完全证明的实例：有界差分的加性情形（异构 Hoeffding）

设 `g : Fin n → Z → ℝ` 的每个坐标函数 `gᵢ` 满足 `E[gᵢ] = 0`、`|gᵢ| ≤ 1`，
取 `f w := ∑ᵢ gᵢ(wᵢ)`。此时 `f` 的有界差分常数 `cᵢ = 2`
（改变第 i 位只影响一个 `gᵢ`，而 `gᵢ` 的值域是 `[−1,1]`，**极差恰为 2**——
注意这是**极差约定**下的 `cᵢ`，与 `:68-70` 的定义一致，**不是「偷偷换约定」**），
且 MGF 界 `E[e^{λ(f−Ef)}] ≤ e^{nλ²/2}` 可以 **完全证明**
（乘积分解 + `hoeffding_lemma`），
于是 McDiarmid 尾界 `P(f−Ef ≥ t) ≤ e^{−t²/(2n)}` 也完全证明。

**常数自洽性核验**：`Σcᵢ² = 4n`，故 `/8` 形式的 MGF 指数是
`λ²·4n/8 = nλ²/2`（与 `mcdiarmid_additive_mgf` 逐字相同）；
尾界指数 `−2t²/Σcᵢ² = −2t²/(4n) = −t²/(2n)`（与 `mcdiarmid_additive_tail`
逐字相同）。⟹ **`/8` + `−2t²/Σcᵢ²` + `cᵢ = 2` 三者一致**。 -/

/-- **加性实例的 MGF 界（完全证明）**。对 `g : Fin n → Z → ℝ`，若每个坐标
`gᵢ` 零均值（`hg0`）、逐点 `|gᵢ| ≤ 1`（`hgb`），则
`E[e^{λ·∑ᵢ gᵢ(wᵢ)}] ≤ e^{n·λ²/2}`（对一切实数 `lam`）。

证明：先由 `unfold uniformExpectation` 写出定义，再用 `Real.exp_sum` 把
`e^{λ∑ᵢ gᵢ}` 写成 `∏ᵢ e^{λ gᵢ}`；用 `Finset.prod_univ_sum` 把乘积空间上的
求和拆成 `∏ᵢ ∑_z`；用 `Fintype.card_pi_const`、`Nat.cast_pow`、
`Finset.prod_div_distrib` 把 `(∏ᵢ∑_z)/(N^n)` 化为 `∏ᵢ uniformExpectation`；
每个因子 ≤ `e^{λ²/2}`（`hoeffding_lemma`，零均值由
`sum_eq_zero_of_uniformExpectation_eq_zero` 转成零和）；最后
`Finset.prod_const`、`Fintype.card_fin`、`Real.exp_nat_mul` 合并为
`e^{n·λ²/2}`。 -/
theorem mcdiarmid_additive_mgf {Z : Type*} [Fintype Z] (n : ℕ) (g : Fin n → Z → ℝ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (hg0 : ∀ i : Fin n, uniformExpectation (g i) = 0)
    (hgb : ∀ (i : Fin n) (z : Z), |g i z| ≤ 1) (lam : ℝ) :
    uniformExpectation (fun w : Fin n → Z => Real.exp (lam * ∑ i : Fin n, g i (w i)))
      ≤ Real.exp ((n : ℝ) * lam ^ 2 / 2) := by
  have hzsum : ∀ i : Fin n, (∑ z : Z, g i z) = 0 := fun i =>
    sum_eq_zero_of_uniformExpectation_eq_zero hN (hg0 i)
  have hfunc : (fun w : Fin n → Z => Real.exp (lam * ∑ i : Fin n, g i (w i)))
      = fun w : Fin n → Z => ∏ i : Fin n, Real.exp (lam * g i (w i)) := by
    funext w
    calc
      Real.exp (lam * ∑ i : Fin n, g i (w i))
          = Real.exp (∑ i : Fin n, lam * g i (w i)) := by rw [Finset.mul_sum]
      _ = ∏ i : Fin n, Real.exp (lam * g i (w i)) := Real.exp_sum _ _
  calc
    uniformExpectation (fun w : Fin n → Z => Real.exp (lam * ∑ i : Fin n, g i (w i)))
        = (∑ w : Fin n → Z, ∏ i : Fin n, Real.exp (lam * g i (w i)))
            / (Fintype.card (Fin n → Z) : ℝ) := by
          unfold uniformExpectation
          rw [hfunc]
    _ = (∏ i : Fin n, ∑ z : Z, Real.exp (lam * g i z))
          / ((Fintype.card Z : ℝ) ^ n) := by
          rw [Fintype.card_pi_const, Nat.cast_pow]
          congr 1
          rw [Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset Z))
            (f := fun i z => Real.exp (lam * g i z))]
          simp
    _ = ∏ i : Fin n, uniformExpectation (fun z : Z => Real.exp (lam * g i z)) := by
          unfold uniformExpectation
          calc
            (∏ i : Fin n, ∑ z : Z, Real.exp (lam * g i z))
                / ((Fintype.card Z : ℝ) ^ n)
                = (∏ i : Fin n, ∑ z : Z, Real.exp (lam * g i z))
                    / (∏ _i : Fin n, (Fintype.card Z : ℝ)) := by
                  congr 1
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = ∏ i : Fin n,
                  ((∑ z : Z, Real.exp (lam * g i z)) / (Fintype.card Z : ℝ)) := by
                  rw [Finset.prod_div_distrib]
    _ ≤ ∏ _i : Fin n, Real.exp (lam ^ 2 / 2) := by
          apply Finset.prod_le_prod
          · intro i _
            unfold uniformExpectation
            exact div_nonneg (Finset.sum_nonneg (fun z _ => Real.exp_nonneg _))
              (Nat.cast_nonneg _)
          · intro i _
            exact hoeffding_lemma (X := g i) (lam := lam) hN (hzsum i) (hgb i)
    _ = Real.exp ((n : ℝ) * lam ^ 2 / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← Real.exp_nat_mul]
          congr 1
          ring

/-- **加性实例的单边尾界（完全证明）**。同 `mcdiarmid_additive_mgf` 的假设，
`t > 0`，则 `P(∑ᵢ gᵢ(wᵢ) ≥ t) ≤ e^{−t²/(2n)}`。

证明：取 `lam := t/n`，用 `markov_exp_tail` 加 MGF 界得
`P ≤ e^{−lam·t} · e^{n·lam²/2} = e^{−t²/(2n)}`（`field_simp`/`ring` 化简）。

**这正是 McDiarmid 界在该实例下的精确取值**：对 `f w = ∑ᵢ gᵢ(wᵢ)` 有界差分
常数 `cᵢ = 2`，故 `Σcᵢ² = 4n`，McDiarmid 单边界给出
`e^{−2t²/Σcᵢ²} = e^{−2t²/(4n)} = e^{−t²/(2n)}`，与本定理一致（双边常数 2 亦同）。 -/
theorem mcdiarmid_additive_tail {Z : Type*} [Fintype Z] (n : ℕ) (g : Fin n → Z → ℝ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (hg0 : ∀ i : Fin n, uniformExpectation (g i) = 0)
    (hgb : ∀ (i : Fin n) (z : Z), |g i z| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ ∑ i : Fin n, g i (w i)))
      ≤ Real.exp (-t ^ 2 / (2 * n)) := by
  classical
  let S : (Fin n → Z) → ℝ := fun w => ∑ i : Fin n, g i (w i)
  let lam : ℝ := t / n
  have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos ht hnℝ
  have hmf : uniformExpectation (fun w : Fin n → Z => Real.exp (lam * S w))
      ≤ Real.exp ((n : ℝ) * lam ^ 2 / 2) := by
    simpa [S] using mcdiarmid_additive_mgf n g hN hn hg0 hgb lam
  have hmarkov := markov_exp_tail (S := S) (t := t) (lam := lam) hlam
  have hmain : uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ S w))
      ≤ Real.exp (-t ^ 2 / (2 * n)) := by
    calc
      uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ S w))
          ≤ Real.exp (-lam * t) * uniformExpectation (fun w => Real.exp (lam * S w)) := hmarkov
      _ ≤ Real.exp (-lam * t) * Real.exp ((n : ℝ) * lam ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hmf (Real.exp_nonneg _)
      _ = Real.exp (-t ^ 2 / (2 * n)) := by
            rw [← Real.exp_add]
            congr 1
            dsimp [lam]
            field_simp [hnne]
            ring
  simpa [S] using hmain

/-- **加性实例的双边尾界（完全证明）**。同假设、`t > 0`，则
`P(|∑ᵢ gᵢ(wᵢ)| ≥ t) ≤ 2 · e^{−t²/(2n)}`。

证明：事件 `{t ≤ |S w|}` 含于 `{t ≤ S w} ∪ {t ≤ −S w}`；第一个事件用
`mcdiarmid_additive_tail`（作用于 `g`），第二个作用于逐点取负的
`fun i z => -g i z`（零均值由 `mcdiarmid_uniformExpectation_neg` 保持，
`∑ᵢ (−gᵢ) = −∑ᵢ gᵢ` 由 `Finset.sum_neg_distrib`）；用并集界相加。 -/
theorem mcdiarmid_additive_two_sided {Z : Type*} [Fintype Z] (n : ℕ) (g : Fin n → Z → ℝ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (hg0 : ∀ i : Fin n, uniformExpectation (g i) = 0)
    (hgb : ∀ (i : Fin n) (z : Z), |g i z| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ |∑ i : Fin n, g i (w i)|))
      ≤ 2 * Real.exp (-t ^ 2 / (2 * n)) := by
  classical
  let S : (Fin n → Z) → ℝ := fun w => ∑ i : Fin n, g i (w i)
  let B := Finset.univ.filter (fun w : Fin n → Z => t ≤ S w)
  let C := Finset.univ.filter (fun w : Fin n → Z => t ≤ -(S w))
  have hg0' : ∀ i : Fin n, uniformExpectation (fun z : Z => -g i z) = 0 := by
    intro i
    rw [mcdiarmid_uniformExpectation_neg (g i), hg0 i, neg_zero]
  have hgb' : ∀ (i : Fin n) (z : Z), |(fun i z => -g i z) i z| ≤ 1 := by
    intro i z
    simpa using hgb i z
  have hsub : Finset.univ.filter (fun w : Fin n → Z => t ≤ |S w|) ⊆ B ∪ C := by
    intro w hw
    have hA : t ≤ |S w| := (Finset.mem_filter.mp hw).2
    rw [Finset.mem_union]
    by_cases h0 : 0 ≤ S w
    · left
      rw [abs_of_nonneg h0] at hA
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩
    · right
      rw [abs_of_neg (lt_of_not_ge h0)] at hA
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩
  have hmono : uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ |S w|))
      ≤ uniformProb (B ∪ C) := by
    unfold uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
      (Nat.cast_nonneg _)
  have hsubadd : uniformProb (B ∪ C) ≤ uniformProb B + uniformProb C := by
    unfold uniformProb
    calc
      (B ∪ C).card / (Fintype.card (Fin n → Z) : ℝ)
          ≤ (B.card + C.card) / (Fintype.card (Fin n → Z) : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast (Finset.card_union_le B C))
              (Nat.cast_nonneg _)
      _ = B.card / (Fintype.card (Fin n → Z) : ℝ)
            + C.card / (Fintype.card (Fin n → Z) : ℝ) := by ring
  have hB : uniformProb B ≤ Real.exp (-t ^ 2 / (2 * n)) := by
    have := mcdiarmid_additive_tail n g hN hn hg0 hgb ht
    simpa [B, S] using this
  have hC : uniformProb C ≤ Real.exp (-t ^ 2 / (2 * n)) := by
    have hneg := mcdiarmid_additive_tail n (fun i z => -g i z) hN hn hg0' hgb' ht
    have hCeq : C = Finset.univ.filter
        (fun w : Fin n → Z => t ≤ ∑ i : Fin n, -g i (w i)) := by
      dsimp only [C, S]
      apply Finset.filter_congr
      intro w _
      rw [Finset.sum_neg_distrib]
    rw [hCeq]
    exact hneg
  calc
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ |S w|))
        ≤ uniformProb (B ∪ C) := hmono
    _ ≤ uniformProb B + uniformProb C := hsubadd
    _ ≤ Real.exp (-t ^ 2 / (2 * n)) + Real.exp (-t ^ 2 / (2 * n)) := add_le_add hB hC
    _ = 2 * Real.exp (-t ^ 2 / (2 * n)) := by ring

/-! ## 具体数值实例（完全证明） -/

/-- **符号函数实例**：`Z = Fin 2` 上的 `z ↦ if z = 0 then 1 else −1`，
即取值 `{+1, −1}` 各半。用于给出一个完全证明的非平凡数值实例。 -/
def mcdiarmidSign (z : Fin 2) : ℝ := if z = 0 then 1 else -1

/-- **符号函数零均值（完全证明）**：`E[mcdiarmidSign] = (1 + (−1))/2 = 0`。 -/
lemma mcdiarmidSign_mean : uniformExpectation mcdiarmidSign = 0 := by
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  unfold uniformExpectation mcdiarmidSign
  rw [Fin.sum_univ_two, Fintype.card_fin]
  rw [if_pos rfl, if_neg h1]
  norm_num

/-- **符号函数有界（完全证明）**：`|mcdiarmidSign z| ≤ 1`。 -/
lemma mcdiarmidSign_abs (z : Fin 2) : |mcdiarmidSign z| ≤ 1 := by
  unfold mcdiarmidSign
  by_cases h : z = 0
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-- **McDiarmid 数值实例（完全证明）**：取 `Z = Fin 2`、`gᵢ = mcdiarmidSign`
（与 `i` 无关），则对任意 `n > 0`、`t > 0`，
`P(|∑ᵢ mcdiarmidSign(wᵢ)| ≥ t) ≤ 2 · e^{−t²/(2n)}`。
这是 `mcdiarmid_additive_two_sided` 的直接实例，所有假设均由
`mcdiarmidSign_mean`、`mcdiarmidSign_abs` 与 `Fintype.card_pos_iff` 提供。 -/
theorem mcdiarmid_example (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Fin 2 =>
        t ≤ |∑ i : Fin n, mcdiarmidSign (w i)|))
      ≤ 2 * Real.exp (-t ^ 2 / (2 * n)) := by
  exact mcdiarmid_additive_two_sided n (fun (_ : Fin n) (z : Fin 2) => mcdiarmidSign z)
    (Fintype.card_pos_iff.mpr ⟨(0 : Fin 2)⟩) hn
    (fun _ => mcdiarmidSign_mean) (fun _ z => mcdiarmidSign_abs z) ht

/-! ## 注：诚实清单与衔接

本文件不含 `sorry` / `axiom` / `admit`；以下是所有 **降级 / 未证 / 未做 /
标注** 的显式清单：

1. **`未证`（`mcdiarmid_tail_of_mgf` 的假设 `hmgf`）**：真正的 McDiarmid MGF
   界 `E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}` 需要沿 n 步过滤/鞅逐坐标迭代（每步用
   单坐标条件期望的有界差分引理），本文件 **未证**，而以显式假设形式标注。
   该定理本身只证明「MGF 界 ⟹ 尾界」的结构性推导（马尔可夫桥 + 指数最小化）。
2. **`未证`（`mcdiarmid_two_sided_of_mgf` 的假设 `hmgf_neg`）**：对 `−f` 的
   MGF 界同样是未证的显式假设；双边界的其余部分（并集界、`E[−f] = −Ef`）已证。
3. **`未做`（多步过滤迭代）**：把上述 `hmgf` 真正证明出来所需的 n 步过滤迭代
   **未做**。`RealAzumaMartingale` 明确把该迭代留作未来工作（它只建立了单步
   条件期望的 Hoeffding 型引理 `condExpFiber_hoeffding` 与鞅条件零均值
   `RealStochasticProcess.CondZeroMean` 等构件）。沿此路线补齐后即可去掉假设
   `hmgf`，得到真正的 McDiarmid 定理。
4. **`未做`（测度论版本）**：本文件全部是 **有限/计数** 概率空间
   （`Fintype` + `uniformProb` / `uniformExpectation`）上的版本；一般概率空间
   （测度、条件期望、鞅收敛）上的 McDiarmid 不等式 **未做**（可参考
   `RealHoeffdingMeasure` 的测度论 Hoeffding 路线扩展）。
5. **`降级`（常数与形式）**：核心结构定理以 `Σcᵢ²/8` 的 MGF 假设为输入；加性
   实例中 `cᵢ = 2`（**极差**约定），故 `Σcᵢ² = 4n`、MGF 指数为
   `λ²·4n/8 = nλ²/2`（即 `e^{nλ²/2}`，见 `mcdiarmid_additive_mgf`），
   尾界常数为 `e^{−2t²/(4n)} = e^{−t²/(2n)}`。
   **⚠ 旧稿勘误（Z1-1，v14）**：本条曾误写「MGF 指数为 `e^{2nλ²}`」——
   **错误**（`e^{2nλ²}` 是**绝对界约定**下把 `/8` 换成 `/2` 才会得到的值，
   与本文件已证的 `e^{nλ²/2}` 相差 8 倍），已按上式更正。
   这与 `RealHoeffding` 中因保守常数而出现的 `e^{−nt²/8}` 一脉相承（见
   `RealHoeffding` 的 `hoeffding_lemma_shifted` 标注）；本文件的加性实例是在
   其自身假设下 **完全证明** 的。

**与既有模块的衔接**：
* `RealHoeffding`：提供 `uniformExpectation`、`hoeffding_lemma`、
  `markov_exp_tail`、`sum_eq_zero_of_uniformExpectation_eq_zero`，是本文件
  全部推导的基础；加性实例本质上是其乘积分解技术对坐标依赖函数 `gᵢ` 的推广。
* `RealSamplingBoost`：提供 `uniformProb`（本文件所有事件概率的定义）。
* `RealAzumaMartingale`：提供 `RealStochasticProcess.condExpFiber`、
  `RealStochasticProcess.CondZeroMean`、`condExpFiber_hoeffding` 等单步构件，
  是把假设 `hmgf` 补成真证明的下一站（多步过滤迭代，`未做`）。
* `RealStochasticProcess`：提供条件期望纤维/零均值条件的一般框架。
-/

end Lattice
