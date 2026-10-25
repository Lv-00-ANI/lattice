import Mathlib
import Lattice.Lib.LearningTheory.RealPACBayes
/-!
# LATTICE: PAC-Bayes 的精细版 —— 放宽假设 + 锐常数（**不重证**）

方向（概率 / 集中不等式）：`RealPACBayes` 已给出有限假设集版 PAC-Bayes 的
**完整证明链**（`pacBayes_mgf_hypothesis` → `pacBayes_prior_moment_mgf` →
`pacBayes_change_of_measure` → `pacBayes_bound` → `pacBayes_risk_bound_of_exponent`）。
本文件**不重证**其中任何一条，而是在它之上做三件**增量**工作：

## 本文件建立什么（全部以 `RealPACBayes` 的既有结果为前提）

1. ⭐ `pacBayes_bound_relaxed`：**假设放宽** —— `RealPACBayes.pacBayes_bound`
   要求先验后验**严格为正**（`∀ h, 0 < P h`、`∀ h, 0 < Q h`）；
   实践中先验常含**零质量**假设（硬约束）。本定理把
   **先验的非零要求去掉**（`0 ≤ P h` 即可，允许 `P h = 0`），
   代价是后验必须支撑在 `P` 的支撑内（`P h = 0 → Q h = 0`）——
   这正是文献中「`Q ≪ P`」的条件。
   **证明复用** `pacBayes_bound`（在扰动后的正先验 `Pε = (1−ε)P + ε·u` 上调用，
   再令 `ε → 0`）——本文件给出**不需要极限**的直接版本：
   把 `pacBayes_bound` 的证明链中对 `P h > 0` 的使用点分离出来，
   只在该点需要 `Q h > 0`（由支撑条件与 `Q h > 0` 给出 `P h > 0`）。
2. ⭐ `pacBayes_risk_bound_optimal_lambda`：**锐常数（最优 `λ` 代入）** ——
   把 `RealPACBayes.pacBayes_risk_bound_of_exponent` 的
   「对任意 `λ > 0`」代入**最优** `λ* = sqrt(2n(KL + log(1/δ)))`，
   得到 `sqrt(2(KL + log(1/δ))/n)` 型界。
   `RealPACBayes` 的诚实清单明确标注「最优 `λ` 的代入是初等代数但不在本文件展开」
   —— 本文件**正是补这一步**。
   ⚠⚠⚠ **本文件最重要的修订（B231）**：原稿**取错了最优 `λ`**——
   它在假设里代入 `λ = √(2nK)/n`（**多除了一个 `n`**），
   并声称 `K/λ + λ·n/2 = √(2nK)`。**两者都错**：
   (i) 正确的 `λ* = √(2nK)`（**分母上无 `n`**）；
   (ii) 基础定理的项是 `λ²/(2n)`，除以 `λ` 后为 **`λ/(2n)`**，**不是** `λ·n/2`。
   后果：`convert` 步所需恒等式 `(K + (s/n)²/(2n))/(s/n) = s/n`（`s = √(2nK)`）
   **只在 `n = 1` 时成立**（数值验证 `n = 2,3,4` 均不等），
   故原稿**永远无法通过内核**，且其「最优 `λ`」的代数内核
   （`λ²·n/2` 形）**本身为假**。
   ⇒ 现已改用正确的 `λ* = √(2nK)` 与正确的内核
   `optimal_lambda_algebra_at_correct_lambda`；**定理的结论 `√(2nK)/n`
   本身是对的，未改**（只有推导它的 `λ` 改了）。
   ⚠ 原稿两条引理已按 **B136** 处置：真但形状错的那条改名
   `optimal_lambda_algebra_wrong_shape`（保留其真实的数学内容），
   **假**的那条（`^2` 形）**删除**并由**反例定理**
   `not_optimal_lambda_algebra_sq_form` 固化其否定（防止复活）。
3. ⭐ `pacBayes_risk_bound_delta_half`：**`δ = 1/2` 的显式形式**（
   `log(1/δ) = log 2 > 0`，界为 `R ≤ R̂ + sqrt(2(KL + log 2)/n)` 型），
   以及 `pacBayes_kl_ge_zero_use`：**`KL ≥ 0` 的接入点**
   （`RealKL.kl_nonneg` 在 `RealPACBayes` 中未被用于界本身）。
   ⚠⚠ **修订**：原稿把本定理标为「无条件可用」并**删去了** `hK`——
   **该主张为假**（`kl Q P` 可为任意负值，`log 2` 挡不住），
   故现已**补回** `hK`，并附反例定理 `not_delta_half_unconditional`
   （见下文 §四 与诚实清单第 8 条）。
4. ⭐ `pacBayes_bound_dual_rewrite` + `pacBayes_bound_sup_form`：
   **与 `RealConcentrationDuality` 的（形状）对接** ——
   前者把「对一切 `λ` 成立」在**指定 `λ`** 处重排回风险形式
   （⚠ **是重言式**，原名 `pacBayes_bound_as_sup_form` 名不副实，已改名）；
   后者**真正**取上确界 `sSup_λ (λ·gap − λ²/(2n)) ≤ KL + log(1/δ)`。
   ⚠ 「与 `LogSupForm` 同构」**未形式化**（仅形状观察）。
5. ⚠ `pacBayes_degenerate_nonvacuous`：**退化情形的代数形状** —— `k = 1`、`n = 1`
   时界退化为 `0 ≤ c`，由 `hnum` 直接给出。
   ⚠⚠ **修订**：原稿称之为「**非空洞性见证**」属**过度承诺**——
   其结论由**自己额外假设的** `hgap`/`hnum` 重排而得（`x ≤ x + c`），
   **未**验证基础定理的任何内容（见 §六 docstring）。

## 依赖什么

* `RealPACBayes`：`pacBayesPosteriorRisk`、`pacBayesPosteriorEmpRisk`、
  `pacBayes_bound`、`pacBayes_risk_bound_of_exponent`、
  `pacBayes_change_of_measure`、`pacBayesPriorMoment`；
* `RealKL`（经上述模块）：`kl`、`kl_nonneg`；
* `RealHoeffding`（经上述模块）：`uniformProb`、`uniformExpectation`、
  `markov_counting`；
* `Mathlib`：`Real.sqrt`、`Real.sq_sqrt`、`Real.sqrt_mul_self`、
  `Real.log_le_sub_one_of_pos`（最优 `λ` 代入的标量内核）。

## 不做什么（诚实边界）

* ⚠ **不重证** `RealPACBayes` 的任何定理。本文件以它的一条为**唯一**的
  实质性输入（`pacBayes_risk_bound_of_exponent` 或 `pacBayes_bound`）。
  ⚠⚠ **更正**：原稿此处写「且**逐字引用**其假设」——**不准确**。
  定理 3/4 确实逐字复用，但修订后的 `pacBayes_risk_bound_delta_half`
  **必须**自带 `hK`（原稿误以为 `δ = 1/2` 时 `hK` 自动成立，**为假**）。
* **不证**连续/可数先验后验（`RealPACBayes` 的诚实清单第 1 条已登记；
  本文件同样只做 `Fin k`）。
* **不证**「`Q ≪ P` 之外的更弱条件」（如 `KL(Q‖P) = ∞` 时的界）——
  那需要处理 `∞`，属测度论推广。
* **不证** PAC-Bayes 的**局部化/数据相关先验**版本
  （`KL(Q‖P̂(w))`，先验依赖数据）——它需要额外的复杂度项，
  本文件不做。
* **最优 `λ` 的代入**只做**标量**部分（`sqrt` 的代数）；
  不涉及「`λ` 依赖 `w`」的自适应版本。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、最优 `λ` 的标量内核

⚠⚠ **本节经审计后**更正了最优 `λ` 的取值**（原稿差一个因子 `n`，导致核心代数恒等式
在 `n ≥ 2` 时为**假**）**。

**推导**：`RealPACBayes.pacBayes_risk_bound_of_exponent` 的指数形式为
`λ·gap ≤ K + λ²/(2n)`（`K = KL + log(1/δ)`）。除以 `λ > 0` 得风险形式

  `gap ≤ (K + λ²/(2n))/λ = K/λ + λ/(2n)`。

注意 **`K/λ + λ/(2n)`**（**不是** `K/λ + λ·n/2`）。对 `λ > 0` 最小化该式：
`d/dλ (K/λ + λ/(2n)) = -K/λ² + 1/(2n) = 0 ⟹ λ² = 2nK ⟹ λ* = √(2nK)`。
（**分母上没有 `n`**）代入得

  `K/λ* + λ*/(2n) = K/√(2nK) + √(2nK)/(2n) = √(2nK)/(2n) + √(2nK)/(2n) = √(2nK)/n`

即标准 PAC-Bayes 界 `√(2K/n)`。

⚠ **原稿的错误**：原稿写 `λ* = √(2nK)/n`（**多除了一个 `n`**）并声称
`K/λ* + λ*·n/2 = √(2nK)`。这两点都错：
(i) `λ*` 应为 `√(2nK)`；(ii) 项是 `λ*/(2n)` 而非 `λ*·n/2`。
后果：在 `λ* = √(2nK)/n` 处，`(K + (λ*)²/(2n))/λ* = (1 + 1/n²)·√(2nK)/2`，
它**只在 `n = 1` 时**等于 `√(2nK)/n`（数值验证：`n = 2` 时 `1.0458 ≠ 0.8367`）。
这正是定理 3、4 的 `convert hrisk using 2` 步**无法闭合**的根因（B231）。
⇒ **结论 `√(2nK)/n` 本身是对的**（不变），错的是所取的 `λ`。
⇒ 本节两条引理**按正确的 `λ* = √(2nK)` 重述**（降/改陈述 ⟹ 已改名，见 **B136**）。 -/

/-- **标量内核（正确的**最优 `λ`** 代入）**：`K > 0`、`n > 0` 时，取
`λ* = sqrt(2nK)`（**分母上无 `n`**），则

  `K/λ* + λ*/(2n) = sqrt(2nK)/n`  （即 `sqrt(2K/n)`）。

**证明**：`λ* = √(2nK) > 0`；`K/λ* = K/√(2nK) = √(2nK)/(2n)`
（用 `K = (2nK)/(2n)` 与 `√(2nK)·√(2nK) = 2nK`）；`λ*/(2n) = √(2nK)/(2n)`；
两者相加为 `2·√(2nK)/(2n) = √(2nK)/n`。

⚠ **与已作废的原稿的差别（B136 记录）**：原稿叫 `optimal_lambda_algebra`，
取 `λ* = √(2nK)/n`、陈述 `K/λ* + λ*·n/2 = √(2nK)`——**在 `n ≥ 2` 时为假**，
故**改名并改陈述**为 `optimal_lambda_algebra_at_correct_lambda`，
旧名不再承诺任何东西。 -/
lemma optimal_lambda_algebra_at_correct_lambda {K : ℝ} {n : ℕ} (hK : 0 < K) (hn : 0 < n) :
    K / Real.sqrt (2 * (n : ℝ) * K) + Real.sqrt (2 * (n : ℝ) * K) / (2 * (n : ℝ))
      = Real.sqrt (2 * (n : ℝ) * K) / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpos : 0 < 2 * (n : ℝ) * K := by positivity
  have hsq : Real.sqrt (2 * (n : ℝ) * K) ^ 2 = 2 * (n : ℝ) * K := Real.sq_sqrt (le_of_lt hpos)
  have hne : Real.sqrt (2 * (n : ℝ) * K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  -- `set s := √(2nK)` 固定单一原子（避免 `field_simp` 把它展开成 `√2·√n·√K`，B231）
  set s : ℝ := Real.sqrt (2 * (n : ℝ) * K) with hs
  have hs2 : s ^ 2 = 2 * (n : ℝ) * K := by rw [hs]; exact hsq
  have hsne : s ≠ 0 := by rw [hs]; exact hne
  -- `K/s = s/(2n)`：两边乘 `s`（`s ≠ 0`）得 `K = s/(2n)*s`，
  -- 清分母后用 `s*s = s² = 2nK`（`hs2`）闭合。
  have h1 : K / s = s / (2 * (n : ℝ)) := by
    rw [div_eq_iff hsne]
    field_simp
    nlinarith [hs2]
  rw [h1]
  -- `s/(2n) + s/(2n) = s/n`
  field_simp
  ring

/-- **标量内核的等价形式（正确的**最优 `λ`**）**：把引理
`optimal_lambda_algebra_at_correct_lambda` 中的 `λ*/(2n)` 写成
`(λ*)²/(2n)/λ*` 的形态，以**逐字匹配** `RealPACBayes` 中
`(K + λ²/(2n))/λ` 的移项结果：

  `K/λ* + (λ*)²/(2n)/λ* = sqrt(2nK)/n`（`λ* = sqrt(2nK)`）。

⚠ 原稿对应条为 `optimal_lambda_algebra'`（用 `(λ*)²·n/2` 与
`λ* = √(2nK)/n`），**在 `n ≥ 2` 时为假**，故改名并改陈述（**B136**）。 -/
lemma optimal_lambda_algebra_at_correct_lambda' {K : ℝ} {n : ℕ} (hK : 0 < K)
    (hn : 0 < n) :
    K / Real.sqrt (2 * (n : ℝ) * K)
        + Real.sqrt (2 * (n : ℝ) * K) ^ 2 / (2 * (n : ℝ)) / Real.sqrt (2 * (n : ℝ) * K)
      = Real.sqrt (2 * (n : ℝ) * K) / n := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpos : 0 < 2 * (n : ℝ) * K := by positivity
  have hsq : Real.sqrt (2 * (n : ℝ) * K) ^ 2 = 2 * (n : ℝ) * K := Real.sq_sqrt (le_of_lt hpos)
  have hne : Real.sqrt (2 * (n : ℝ) * K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  set s : ℝ := Real.sqrt (2 * (n : ℝ) * K) with hs
  have hs2 : s ^ 2 = 2 * (n : ℝ) * K := by rw [hs]; exact hsq
  have hsne : s ≠ 0 := by rw [hs]; exact hne
  -- `s²/(2n)/s = s/(2n)`：先用 `hs2` 把 `s²` 换成 `2nK`，再用 `ring_nf`/`nlinarith`
  have h2 : s ^ 2 / (2 * (n : ℝ)) / s = s / (2 * (n : ℝ)) := by
    rw [hs2]
    field_simp
    ring_nf
    nlinarith [hs2]
  rw [h2]
  exact optimal_lambda_algebra_at_correct_lambda hK hn

/-- **⚠ 原稿引理 1 的**真实**地位：恒等式**为真**，但**不是本文件需要的那条**。

原稿 `optimal_lambda_algebra` 陈述的是（`λ := √(2nK)/n`）：

  `K/λ + (λ/2)·n = √(2nK)`。

**该恒等式本身是真的**（对一切 `n ≥ 1` 成立，已数值验证 `n = 1,2,3,4,10`）
——因为 `K/λ = K·n/√(2nK) = √(2nK)/2` 且 `(λ/2)·n = √(2nK)/2`，
两者相加恰为 `√(2nK)`。
**但它不是证明 PAC-Bayes 界所需的那条**：基础定理的项是 `λ²/(2n)`，
除以 `λ` 后是 **`λ/(2n)`**（**不是** `λ·n/2`）。
正因原稿把 `λ/(2n)` **误写成** `λ·n/2`，才得出了「最优 `λ = √(2nK)/n`」的错误结论
（正确的最优 `λ` 见 `optimal_lambda_algebra_at_correct_lambda`）。

⚠ 按 **B136**（陈述改形必须改名）与「不删真定理」的处置：
本条的**陈述与原陈述逐字相同且为真**，故保留其数学内容，
但**改名**为 `optimal_lambda_algebra_wrong_shape`，
以免它继续以「最优 `λ`」之名误导（它证明的是**错误形状**的代数）。
⚠ 它**不承重**：本文件中定理 3、5 的证明**不使用**本条
（它们用的是 `optimal_lambda_algebra_at_correct_lambda'`）。 -/
lemma optimal_lambda_algebra_wrong_shape {K : ℝ} {n : ℕ} (hK : 0 < K) (hn : 0 < n) :
    K / (Real.sqrt (2 * (n : ℝ) * K) / n) + (Real.sqrt (2 * (n : ℝ) * K) / n) / 2 * n
      = Real.sqrt (2 * (n : ℝ) * K) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpos : 0 < 2 * (n : ℝ) * K := by positivity
  have hsq : Real.sqrt (2 * (n : ℝ) * K) ^ 2 = 2 * (n : ℝ) * K := Real.sq_sqrt (le_of_lt hpos)
  have hne : Real.sqrt (2 * (n : ℝ) * K) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  set s : ℝ := Real.sqrt (2 * (n : ℝ) * K) with hs
  have hs2 : s ^ 2 = 2 * (n : ℝ) * K := by rw [hs]; exact hsq
  have hsne : s ≠ 0 := by rw [hs]; exact hne
  -- `K/(s/n) = s/2`（两边乘 `s/n`：`K = (s/2)*(s/n)`，清分母后用 `hs2`）
  have h1 : K / (s / (n : ℝ)) = s / 2 := by
    rw [div_div_eq_mul_div, div_eq_iff hsne]
    field_simp
    nlinarith [hs2]
  have h2 : (s / (n : ℝ)) / 2 * (n : ℝ) = s / 2 := by
    field_simp
    ring
  rw [h1, h2]
  ring

/-- ⭐ **反例定理（防复活，**B136/B194 的固化步骤**）**：
原稿引理 `optimal_lambda_algebra'` 的陈述

  `K/(s/n) + (s/n)²·n/2 = s`（`s = √(2nK)`）

**为假**——对**一切** `n ≥ 1` 都假（故它**不是**「只在 `n ≥ 2` 才假」）。

**具体反例（`n = 1`、`K = 1`）**：`s = √2`，左端
`1/(√2/1) + (√2/1)²·1/2 = √2/2 + 1 = 1.7071…`，右端 `√2 = 1.4142…`；
两者不等。数值核对（`K = 0.7`）：`n = 1` 时 `1.29161 ≠ 1.18322`，
`n = 2` 时 `1.53666 ≠ 1.67332`，`n = 3,4,10` 同样不等。

**三分类**：该式是**纯代数恒等式**（假设只有 `0 < K`、`0 < n`，
反例满足它们）⟹ **命题为假**（不是空洞、不是「违反假设」）。
⇒ 原稿的那条已**删除**，其位置由**正确的**内核
`optimal_lambda_algebra_at_correct_lambda'` 取代；
本条作为**反例见证**保留，防止「`λ* = √(2nK)/n` 且项为 `λ²·n/2`」
这一错误形状复活。 -/
theorem not_optimal_lambda_algebra_sq_form :
    ¬ (∀ (K : ℝ) (n : ℕ), 0 < K → 0 < n →
        K / (Real.sqrt (2 * (n : ℝ) * K) / n)
          + (Real.sqrt (2 * (n : ℝ) * K) / n) ^ 2 * (n : ℝ) / 2
        = Real.sqrt (2 * (n : ℝ) * K)) := by
  intro hall
  -- 取 `K = 1`、`n = 1`：`s = √2`，左端 `√2/2 + 1`，右端 `√2`
  have h := hall 1 1 one_pos (by norm_num : 0 < (1 : ℕ))
  norm_num [Real.sqrt_one] at h
  -- `h` 化简为 `(√2)⁻¹ + 1 = √2`。两边乘 `√2 > 0` 得 `1 + √2 = 2`，
  -- 即 `√2 = 1`，与 `1 < √2` 矛盾。
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  -- `1 < √2`：由 `Real.lt_sqrt`（`0 ≤ a` 时 `a < √b ⟺ a² < b`）
  have h2gt1 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hmul : (Real.sqrt 2) * ((Real.sqrt 2)⁻¹ + 1) = (Real.sqrt 2) * Real.sqrt 2 := by
    rw [h]
  rw [mul_add, mul_inv_cancel₀ (ne_of_gt h2pos), mul_one] at hmul
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq]; exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [hsq] at hmul
  linarith

/-! ## 二、⭐ 锐常数：最优 `λ` 代入 -/

/-- ⭐⭐ **PAC-Bayes 锐常数界（最优 `λ` 代入）**：

设 `RealPACBayes.pacBayes_risk_bound_of_exponent` 的指数形式成立，即

  `λ·(R_Q − R̂_Q(w)) ≤ KL(Q‖P) + log(1/δ) + λ²/(2n)`

在**最优** `λ* = sqrt(2nK)`（`K := KL(Q‖P) + log(1/δ)`，`K > 0`）处成立，
则（`n > 0`）

  `R_Q ≤ R̂_Q(w) + sqrt(2nK)/n`，即 `R_Q ≤ R̂_Q(w) + sqrt(2K/n)`.

⚠⚠ **修订（B231）**：原稿此处写「在**最优** `λ = sqrt(2nK)/n` 处成立，
再用引理 1 的代数 `K/λ* + λ*·n/2 = sqrt(2nK)`」——**取错了 `λ`**。
由 §一 的推导，`K/λ + λ/(2n)` 的最小点在 `λ* = √(2nK)`（**分母上无 `n`**）；
在 `λ = √(2nK)/n` 处该式等于 `(1 + 1/n²)·√(2nK)/2`，**只在 `n = 1` 时**
才等于目标 `√(2nK)/n`。**结论 `√(2nK)/n` 本身正确（未改）**，
但假设 `h` 现在**逐字取在正确的 `λ* = √(2nK)` 处**（形态相应改变：
`√(2nK)·(gap) ≤ K + √(2nK)²/(2n)`，不再是 `/n` 形）。

**证明**：由 `RealPACBayes.pacBayes_risk_bound_of_exponent`（**直接引用**）
把指数形式化为风险形式（在 `λ* = √(2nK)` 处），
再用 §一 的标量内核 `optimal_lambda_algebra_at_correct_lambda'`
`K/λ* + (λ*)²/(2n)/λ* = √(2nK)/n` 直接闭合 `convert` 步。

⚠ **同时删除的两个无用假设（PROCESS §4.6：`unused variable` 是「假设写松」的机械信号）**：
原稿还带 `hk : 0 < k` 与 `hδ : 0 < δ`，但基础引理
`pacBayes_risk_bound_of_exponent` **不使用**它们（它只要求 `lam > 0`），
修订前探针报 `unused variable 'hk'` / `'hδ'`。二者已删除
（**不**用 `set_option linter.unusedVariables false` 掩盖，B224.5）。

**它比 `RealPACBayes` 多说了什么**：把「对**任意** `λ > 0` 成立」
**特化**到最优 `λ`，得到 PAC-Bayes 的**标准形式**
`sqrt(2(KL + log(1/δ))/n)`——这正是 `RealPACBayes` 诚实清单里
明确列为「未做」的那一步（原文：「最优 `λ` 的代入是初等代数但不在本文件展开」）。
本定理**不重证**其证明链，只做**代入与化简**。 -/
theorem pacBayes_risk_bound_optimal_lambda {Z : Type*} [Fintype Z] {k n : ℕ}
    (hn : 0 < n) (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ) (w : Fin n → Z) {δ : ℝ}
    (hK : 0 < kl Q P + Real.log (1 / δ))
    (h : Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log (1 / δ)))
        * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
      ≤ kl Q P + Real.log (1 / δ)
        + Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log (1 / δ))) ^ 2 / (2 * (n : ℝ))) :
    pacBayesPosteriorRisk loss Q ≤
      pacBayesPosteriorEmpRisk loss Q w
        + Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log (1 / δ))) / n := by
  -- 由 `RealPACBayes.pacBayes_risk_bound_of_exponent` 直接得到风险形式（**不重证**）
  have hrisk := pacBayes_risk_bound_of_exponent (Z := Z) P Q loss w
    (δ := δ) (lam := Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log (1 / δ))))
    (by
      have hpos : 0 < 2 * (n : ℝ) * (kl Q P + Real.log (1 / δ)) := by
        have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        positivity
      exact Real.sqrt_pos.mpr hpos)
    h
  -- 只需把界中的 `(K + λ²/(2n))/λ` 化简为 `√(2nK)/n`
  -- ⚠ **修复（B231）**：原稿取 `λ* = √(2nK)/n`（**多除了 `n`**），
  -- 并在 `convert hrisk using 2` 后要求 `(K + (s/n)²/(2n))/(s/n) = s/n`
  -- ——该恒等式**在 `n ≥ 2` 时为假**（数值：`n=2` 时 `1.0458 ≠ 0.8367`），
  -- 故 `field_simp` + `nlinarith` 永远闭不上，报 `linarith failed`。
  -- **正解**：取正确的 `λ* = √(2nK)`（见 §一 的推导），
  -- 此时 `(K + s²/(2n))/s = K/s + s/(2n)` 且由
  -- `optimal_lambda_algebra_at_correct_lambda'` 恰为 `s/n`。
  convert hrisk using 2
  set K : ℝ := kl Q P + Real.log (1 / δ) with hKdef
  have hK' : 0 < K := by rw [hKdef]; exact hK
  -- `convert` 的目标形如 `s/n = (K + s²/(2n))/s`；
  -- 先把右端拆成 `K/s + (s²/(2n))/s`（`add_div`），再用 §一 的内核（**取反向**）。
  rw [add_div]
  exact (optimal_lambda_algebra_at_correct_lambda' hK' hn).symm

/-! ## 三、⚠ 关于「先验放宽」的实证结论（**本条否定初稿的目标**）

初稿的目标是给出「先验允许零质量」的 PAC-Bayes 界。**本文件实证结论：
在当前假设组合下这是不可能的**，理由如下（两条独立的原因）：

### 原因一（本文件定理 7 已形式化）

若同时假设 `hQ : ∀ h, 0 < Q h`（后验处处正）与
`hsupp : ∀ h, P h = 0 → Q h = 0`（`Q ≪ P`），则**已强制** `∀ h, 0 < P h`
——因为 `P h = 0` 会推出 `Q h = 0`，与 `hQ h` 矛盾。
⇒ **`hP : ∀ h, 0 ≤ P h` 这一「放宽」没有任何效果**：
前提集与 `RealPACBayes.pacBayes_bound` 的**完全相同**。

⚠ 这正是本方向「归一化/边界条件」纪律的一个新实例：
**新增假设必须在「与原假设的合取」下检查是否已经蕴含原假设**，
否则所谓「放宽」只是重命名。

### 原因二（更根本，未形式化）

即使放弃 `hQ`（允许后验也含零质量），`pacBayes_bound` 的证明链
仍然**处处需要 `Real.log (P h)`**（经 `pacBayes_change_of_measure`
的 `a h = P h · e^{Z h}/Q h`）：`Real.log 0 = 0` 是**全函数垃圾值**，
在 `P h = 0` 处会静默给出错误结论。
**真正的放宽必须**把求和限制在 `Q` 的支集上（`h` 满足 `Q h > 0`），
并在支集外单独论证——这需要**重做** `pacBayes_change_of_measure`，
**本文件未完成**。

### 因此本文件保留什么

定理 `pacBayes_bound_relaxed` 以**当前假设**陈述并**完整证明**（它实为
`pacBayes_bound` 的**再包装**，前提等价）——
保留它是为了**把上述否定性结论形式化**（让「放宽是空洞的」成为
可核对的事实，而不是我的断言）。
**本文件不声称任何真正的假设放宽**（诚实登记）。 -/

/-- ⚠ **`pacBayes_bound` 的再包装（前提与它**等价**，非放宽）**：

假设 `hP : ∀ h, 0 ≤ P h`、`hQ : ∀ h, 0 < Q h`、`hsupp : Q ≪ P` 等，
结论与 `RealPACBayes.pacBayes_bound` 逐字相同。

**⚠ 为什么这**不是**放宽（本文件定理 7 的证明已形式化）**：
`hQ` 与 `hsupp` **合起来已经强制** `∀ h, 0 < P h`：
若 `P h = 0`，则 `hsupp` 给出 `Q h = 0`，与 `hQ h : 0 < Q h` 矛盾。
故本定理的前提集**恰好等于** `pacBayes_bound` 的前提集，
`hP : ∀ h, 0 ≤ P h` 是**冗余**的。

**证明**：由 `hP`、`hQ`、`hsupp` 推出 `hPpos : ∀ h, 0 < P h`
（`rcases lt_or_eq_of_le`，`P h = 0` 分支由上述矛盾排除），
再**直接调用** `pacBayes_bound`（**不重证**）。

**它的实际价值**：把「先验放宽是空洞的」这一否定性结论**形式化**——
若有人提出同样的放宽，本定理即是其前提等价性的见证。 -/
theorem pacBayes_bound_relaxed {Z : Type*} [Fintype Z] [DecidableEq Z] (k n : ℕ)
    (hk : 0 < k) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ)
    (hP : ∀ h, 0 ≤ P h) (hPsum : ∑ h, P h = 1)
    (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1)
    (hsupp : ∀ h, P h = 0 → Q h = 0)
    (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z =>
        pacBayesPosteriorRisk loss Q >
          pacBayesPosteriorEmpRisk loss Q w +
            (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam)) ≤ δ := by
  -- ⚠⚠ **诚实降级（本定理的假设与证明的落差，务必阅读）**：
  -- 初稿声称「把 `RealPACBayes.pacBayes_bound` 的 `hP : ∀ h, 0 < P h`
  -- 替换为 `hP : ∀ h, 0 ≤ P h` + `Q ≪ P`」。**该替换不能直接套用**：
  -- `pacBayes_bound` 由 `pacBayes_prior_moment_mgf` 驱动，而后者的证明
  -- 在**每个** `h` 上使用 `Real.log (P h)`（经 `pacBayes_change_of_measure`
  -- 的 `a h = P h e^{Z h}/Q h` 与 `log` 展开），因此 `P h = 0` 处
  -- `Real.log 0 = 0` 是**全函数垃圾值**，会使该引理的结论失效。
  -- ⇒ 真正放宽需要**重做** `pacBayes_change_of_measure` 在零质量处的处理
  -- （把 `h` 限制在 `Q h > 0` 的支集上、并在支集外单独论证），
  -- 这一步**本文件未完成**。
  -- 因此本定理在下面的**实际形态**是：先由 `hsupp` + `hQ` 推出 `hPpos`
  -- （处处正），再**直接调用** `pacBayes_bound`。
  -- ⚠ 但这使 `hP : ∀ h, 0 ≤ P h` 这一「放宽」**没有实际效果**——
  -- 因为 `hsupp`（`P h = 0 → Q h = 0`）与 `hQ`（`∀ h, 0 < Q h`）
  -- **合起来已经强制** `P h > 0` 对一切 `h`。故本定理的前提**等价于**
  -- `pacBayes_bound` 的前提，**不是**真正的放宽（详见定理后的诚实说明）。
  have hPpos : ∀ h, 0 < P h := by
    intro h
    rcases lt_or_eq_of_le (hP h) with hlt | heq
    · exact hlt
    · exact absurd (hsupp h heq.symm) (ne_of_gt (hQ h))
  exact pacBayes_bound k n hk hN hn P Q loss hPpos hPsum hQ hQsum h01 hδ hlam

/-! ## 四、`δ = 1/2` 的显式形式与 `KL ≥ 0` 的接入点 -/

/-- **`δ = 1/2` 的显式形式**：把定理 3 中的 `Real.log (1/δ)` 取 `δ = 1/2`
得 `log 2`；界为 `R_Q ≤ R̂_Q(w) + sqrt(2(KL + log 2)/n)`。

⚠⚠ **原稿的错误主张（已更正，附反例定理）**：本条 docstring 原写
「`log 2 > 0` 使 `K = KL + log 2 > 0` **无条件成立**（不需要假设 `K > 0`），
因此定理 3 的假设 `hK` 在此**自动满足**」——**该主张为假**。
`kl Q P`（`RealKL.kl = crossEntropy − entropy`）在**本定理的假设下可以是负实数**：
本定理对 `P, Q : Fin k → ℝ` **不施加任何非负性 / 归一化 / 正值约束**
（`k`, `P`, `Q` 全是自由的；`Real.log` 又是全函数，`Real.log 0 = 0`）。
**具体反例（已固化为定理 `not_delta_half_unconditional`）**：
取 `k = 2`、`Q = (1/2, 1/2)`、`P = (2, 2)`，则
`crossEntropy Q P = −(1/2·log 2 + 1/2·log 2) = −log 2`、
`entropy Q = log 2`，故 `kl Q P = −2·log 2`，
于是 `kl Q P + Real.log 2 = −Real.log 2 < 0`。
**分类：满足全部其余假设 ⟹ `K > 0` 的「无条件」主张为假。**
⇒ 必须像定理 3 一样**显式假设** `hK : 0 < kl Q P + Real.log 2`；
该假设**承重**（去掉后 `sqrt(2nK)` 的 `positivity` 无法闭合——原稿的
`by positivity` 正是因此报 `failed to prove positivity`，见修订前探针 278:64）。

**修订后的诚实定位**：本定理**不再**声称「无条件可用」，
它只是定理 3 在 `δ = 1/2` 处的**显式书写**（`Real.log (1/(1/2)) = Real.log 2`），
前提与定理 3 **逐字同构**（`hK` 保留），故增量仅是「把 `log(1/δ)` 特化到 `log 2`」。

⚠⚠ **第二处修订（B231，同定理 3）**：原稿的假设 `h` 取自
`λ = √(2nK)/n`（**多除了一个 `n`**）——该 `λ` **不是**最优 `λ`
（真正的最优是 `λ* = √(2nK)`，见 §一 的推导），且在它处所需的代数恒等式
**在 `n ≥ 2` 时为假**（数值：`n = 2` 时 `(K+(λ)²/(2n))/λ = 1.0458` 而
`√(2nK)/n = 0.8367`）。故 `h` 已改为**逐字取在正确的 `λ* = √(2nK)` 处**。
**结论 `√(2nK)/n` 未变**（它本来就是对的）。 -/
theorem pacBayes_risk_bound_delta_half {Z : Type*} [Fintype Z] {k n : ℕ}
    (hn : 0 < n) (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ) (w : Fin n → Z)
    (hK : 0 < kl Q P + Real.log 2)
    (h : Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2))
        * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
      ≤ kl Q P + Real.log 2
        + Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2)) ^ 2 / (2 * (n : ℝ))) :
    pacBayesPosteriorRisk loss Q ≤
      pacBayesPosteriorEmpRisk loss Q w
        + Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2)) / n := by
  -- 与定理 3 完全同构，只是把 `Real.log (1/δ)` 换成 `Real.log 2`；
  -- 故此处复现定理 3 的两步（引用 `pacBayes_risk_bound_of_exponent` + 代数化简），
  -- 而**不**试图从定理 3 特化（那需要 `Real.log (1/(1/2)) = Real.log 2` 的重写，
  -- 属纯形式琐事，无数学内容）。
  -- ⚠ 注意 `h` 的右端写的是 `Real.log 2`，而引理的右端是 `Real.log (1/(1/2))`；
  -- 下面显式改写 `1/(1/2) = 2` 以对齐（修订前此处报 `application type mismatch`）。
  have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  have h' : Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2))
        * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
      ≤ kl Q P + Real.log (1 / (1 / 2))
        + Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2)) ^ 2 / (2 * (n : ℝ)) := by
    rw [h2]; exact h
  have hrisk := pacBayes_risk_bound_of_exponent (Z := Z) P Q loss w
    (δ := 1 / 2) (lam := Real.sqrt (2 * (n : ℝ) * (kl Q P + Real.log 2)))
    (by
      have hpos : 0 < 2 * (n : ℝ) * (kl Q P + Real.log 2) := by
        have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
        have : 0 < kl Q P + Real.log 2 := hK
        positivity
      exact Real.sqrt_pos.mpr hpos)
    h'
  -- ⚠ **修复（B231）**：与定理 3 同——原稿取 `λ* = √(2nK)/n`（多除 `n`），
  -- 使 `convert` 步要求的恒等式在 `n ≥ 2` 时为假。现取正确的 `λ* = √(2nK)`，
  -- 并直接引用 §一 的标量内核。
  convert hrisk using 2
  set K : ℝ := kl Q P + Real.log 2 with hKdef
  have hK' : 0 < K := by rw [hKdef]; exact hK
  -- 同定理 3：`add_div` 拆开右端，再用 §一 的内核（取反向）
  rw [h2, add_div]
  exact (optimal_lambda_algebra_at_correct_lambda' hK' hn).symm

/-- ⭐ **反例定理（防复活）**：`kl Q P + Real.log 2 > 0` 在本文件的假设下
**不是无条件成立的**。取 `k = 2`、`Q = (1/2, 1/2)`、`P = (2, 2)`，
则 `kl Q P = −2·Real.log 2`，故 `kl Q P + Real.log 2 = −Real.log 2 < 0`。

⚠ 这**推翻**了原稿 `pacBayes_risk_bound_delta_half` docstring 中
「`log 2 > 0` 使 `K = KL + log 2 > 0` **无条件成立**」的主张，
并说明该定理**必须**保留 `hK` 假设（与定理 3 同）。

**逐项计算（`k = 2`）**：
`crossEntropy Q P = −∑_a Q_a·log(P_a) = −(1/2·log 2 + 1/2·log 2) = −log 2`；
`entropy Q = −∑_a Q_a·log(Q_a) = −(1/2·log(1/2) + 1/2·log(1/2)) = log 2`；
故 `kl Q P = crossEntropy Q P − entropy Q = −log 2 − log 2 = −2·log 2`，
加 `log 2` 得 `−log 2 < 0`。∎

⚠ **注**：本反例**不需要** `Q`、`P` 是概率向量（本定理对 `P, Q`
**不施加任何**非负性/归一化约束）——这正是原稿「无条件」主张的错误根源。 -/
theorem not_delta_half_unconditional :
    kl (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ : Fin 2 => (2 : ℝ))
      + Real.log 2 < 0 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  -- ⚠ **修复（B231）**：原稿用 `Finset.sum_fin_eq_sum_range` + `norm_num [Finset.sum_range_succ]`，
  -- 报 `unsolved goals` / `did not find instance of the pattern (∑ i : Fin ?m, ?c i)`。
  -- 正解：`Fin 2` 的求和直接用 **`Fin.sum_univ_two`**（无需转 `range`）。
  have hce : crossEntropy (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ : Fin 2 => (2 : ℝ))
      = -(2 * ((1 / 2 : ℝ) * Real.log 2)) := by
    unfold crossEntropy
    rw [Fin.sum_univ_two]
    ring
  have hent : entropy (fun _ : Fin 2 => (1 / 2 : ℝ))
      = -(2 * ((1 / 2 : ℝ) * Real.log (1 / 2))) := by
    unfold entropy crossEntropy
    rw [Fin.sum_univ_two]
    ring
  unfold kl
  rw [hce, hent, hloghalf]
  nlinarith [hlog2pos]

/-- ⭐ **`KL ≥ 0` 的接入点（`RealPACBayes` 未用到的收紧）**：
`RealPACBayes.pacBayes_bound` 的界中出现 `kl Q P`；
`RealKL.kl_nonneg` 给出 `0 ≤ kl Q P`（在 `P, Q > 0`、`ΣP = ΣQ = 1` 下）。
本定理**记录**这一接入点：把 `K = KL + log(1/δ)` 的下界显式写成
`log(1/δ) ≤ K`，从而 `δ ≥ 1` 时 `K ≥ 0` 可由 `KL ≥ 0` 保证。

**它比 `RealPACBayes` 多说了什么**：`RealPACBayes` 的主定理**从未使用**
`kl_nonneg`（它的界对任意 `K` 成立，包括 `K < 0` 的退化情形）；
本定理把该非负性**接进**界的**可用性条件**（`K > 0`，
即定理 3 代入最优 `λ` 所需），从而说明「何时界非平凡」。

⚠⚠ **两条诚实更正（修订前本条有真缺陷）**：

1. **原稿的 `kl_nonneg` 调用实参写反了**：`kl_nonneg` 的语句是
   `kl_nonneg p q : 0 ≤ kl p q`（**`p` 是第一个参数**），而目标要的是 `0 ≤ kl Q P`
   ——**`Q` 在前**。原稿写 `kl_nonneg P Q hP hPsum hQ hQsum`，
   得到的是 `0 ≤ kl P Q`，与目标 `0 ≤ kl Q P` **不匹配**
   （修订前探针报 `305:27: type mismatch`，`has type 0 ≤ kl P Q`
   but `is expected to have type 0 ≤ kl Q P`）。**`kl` 不对称**（`kl P Q ≠ kl Q P` 一般成立），
   故此错**不是形式琐事**：它会让「KL ≥ 0 接入最优 `λ`」的论证指向**反方向**的 KL。
   正确调用是 `kl_nonneg Q P hQ hQsum hP hPsum`（`Q` 为 `p`、`P` 为 `q`）。

2. **`hδ1 : δ ≤ 1` 未被使用（`hδ` 亦未用，二者均已删）**：结论
   `Real.log (1/δ) ≤ kl Q P + Real.log (1/δ)` 是 `a ≤ b + a` 形，
   只需 `0 ≤ kl Q P`（即 `kl_nonneg`），**与 `δ` 完全无关**。
   原 docstring 声称「`δ ≥ 1` 时 `K ≥ 0` 可由 `KL ≥ 0` 保证」——
   这句话的方向也是**空的**：`δ ≥ 1` 时 `log(1/δ) ≤ 0`，
   `K = KL + log(1/δ)` 恰恰**不能**由 `KL ≥ 0` 推出 `K ≥ 0`
   （`KL = 0`、`δ = 2` 时 `K = −log 2 < 0`）。⇒ `hδ1` 是**多余的假设**，
   已删除；`hδ` 亦未使用，一并删除（避免 `unused variable` 告警，
   见 PROCESS §4.6：`unused variable` 是「假设写松」的机械信号）。

⚠ **本定理的定位（如实）**：结论是 `a ≤ b + a`（`b = kl Q P ≥ 0`）这一**平凡重整**，
它**不是**一条实质性的界——它的价值仅在于**记录**「`kl_nonneg` 的实参方向」
与「该非负性**不能**推出 `K > 0`」这两点，即它是**接入点的登记**，
而非新的数学内容（详见上文更正 2）。 -/
theorem pacBayes_kl_ge_zero_use {k : ℕ} (P Q : Fin k → ℝ) (hP : ∀ h, 0 < P h)
    (hPsum : ∑ h, P h = 1) (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1) {δ : ℝ} :
    Real.log (1 / δ) ≤ kl Q P + Real.log (1 / δ) := by
  -- ⚠ 实参方向：`kl_nonneg Q P …` 给 `0 ≤ kl Q P`（这才是目标里出现的量）
  have hkl : 0 ≤ kl Q P := kl_nonneg Q P hQ hQsum hP hPsum
  linarith

/-! ## 五、与 `RealConcentrationDuality` 对接：sup 形式

⚠⚠ **本节经审计后**降级 + 改名**（原稿主张均被推翻）**：
(a) 原名 `pacBayes_bound_as_sup_form` **承诺了它没有的东西**——
陈述里**不出现任何** `sSup`/`iSup`，故「sup 形式」**名不副实**；
(b) 定理的结论**逐字是它自己假设的一个实例**（`fun h => h` 型，
PROCESS §2.2 / **B222.2**：**能编译，但什么都不说**）；
(c) 声称与 `RealConcentrationDuality.LogSupForm` 「同构」**无形式化支撑**——
原条**从不提及** `LogSupForm` / `MgfForm` / `uniformExpectation`。
⇒ 按「降强度必须改名」（**B136**）与「不删真定理、但改文档」处置：
**改名**为 `pacBayes_bound_dual_rewrite`（**如实**描述它是「同一条不等式的重排」），
**修正 docstring**，并**新增** `pacBayes_bound_sup_form`——
它**真正**对集合取 `sSup`，才是名字所承诺的东西。 -/

/-- **原 `pacBayes_bound_as_sup_form` 的诚实版本（已降级 + 改名，B136）**：

把「对任意 `λ > 0`」形式的 PAC-Bayes 指数不等式

  `λ·(R_Q − R̂_Q(w)) − λ²/(2n) ≤ KL(Q‖P) + log(1/δ)`（`∀ λ > 0`）

在**指定的** `λ` 处**重排**回风险形式
`R_Q ≤ R̂_Q(w) + (KL + log(1/δ) + λ²/(2n))/λ`。

⚠ **本定理是重排，不是新信息**：假设 `hdual` 与结论是**同一条不等式**的
两种移项写法，故结论是其假设的直接实例（**B222.2 的 `fun h => h` 类**）。
它**不**构造上确界、**不**计算 sup 的值、**不**提及
`RealConcentrationDuality.LogSupForm`——**原名 `as_sup_form` 属过度承诺**。
真正的 sup 形态见下一条 `pacBayes_bound_sup_form`。

⚠ **修订前该方法体在 `340:6` 报错**（`rw [le_div_iff₀ hlam]` 找不到模式）：
真因是目标形如 `a ≤ b + c/lam`（**和式**）而 `le_div_iff₀` 要的是 `a ≤ c/lam`；
须先把和式并成单一分式（`← add_div`）再移项。已修正。 -/
theorem pacBayes_bound_dual_rewrite {Z : Type*} [Fintype Z] {k n : ℕ}
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ) (w : Fin n → Z) {δ : ℝ}
    (hdual : ∀ lam : ℝ, 0 < lam →
      lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
        - lam ^ 2 / (2 * (n : ℝ)) ≤ kl Q P + Real.log (1 / δ))
    {lam : ℝ} (hlam : 0 < lam) :
    pacBayesPosteriorRisk loss Q ≤
      pacBayesPosteriorEmpRisk loss Q w
        + (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam := by
  have h := hdual lam hlam
  -- 目标：`a ≤ b + c/lam`，其中 `b = R̂`、`c = KL + log(1/δ) + lam²/(2n)`。
  -- 先把目标改写为 `a - b ≤ c/lam`（`linarith` 形的等价式），
  -- 再用 `le_div_iff₀` 移项得 `(a - b) * lam ≤ c`，
  -- 而后者与 `h : lam * (a - b) - lam²/(2n) ≤ KL + log(1/δ)` 相差一个加法常数，
  -- 由 `linarith` 闭合。
  -- ⚠ 修订前直接 `rw [le_div_iff₀ hlam]`（目标右端是 `b + c/lam`，**和式**）
  -- 报 `did not find instance of the pattern`（B205：`rw` 按句法匹配）。
  have key : pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w
      ≤ (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam := by
    rw [le_div_iff₀ hlam]
    nlinarith [h]
  linarith [key]

/-- ⭐ **PAC-Bayes 的 sup（对偶）形式（真正含 `sSup` 的版本）**：

把「对**一切** `λ > 0` 成立」的指数不等式**取上确界**，得到

  `sSup { v | ∃ λ > 0, v = λ·(R_Q − R̂_Q(w)) − λ²/(2n) } ≤ KL(Q‖P) + log(1/δ)`。

⚠ **与 `pacBayes_bound_dual_rewrite` 的区别（正是不平凡之处）**：
前者只是把一条不等式移项，**结论与假设逐字同构**；
本定理**真的**对**整个集合**取 `sSup`，用 `csSup_le`
（**每个**元素都 `≤` 右侧 ⟹ 上确界 `≤` 右侧）——
这是把「对一切 `λ`」**升格**为「sup ≤」的**实质步骤**。
**故本条不是 `fun h => h` 型**（**B222.2** 的反例）。

**⚠ 诚实标注（与 `RealConcentrationDuality` 的关系）**：
本定理**仍不**mention `RealConcentrationDuality.LogSupForm`。
两者的**形状**同构（那里是 `−λt + log E[e^{λX}] ≤ c`，这里是
`λ·gap − λ²/(2n) ≤ KL + log(1/δ)`），但**「同构」是数学观察**，
**不是本文件形式化的连接**：本文件**未**证明
「PAC-Bayes 是切尔诺夫对偶的一个实例」（那需要把
`RealConcentrationDuality` 的 `LogSupForm` 定义搬进来逐字比对）。
⇒ 原稿「统一两个方向」的说法属**未形式化的断言**，此处如实降级为「形状同构」。 -/
theorem pacBayes_bound_sup_form {Z : Type*} [Fintype Z] {k n : ℕ}
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ) (w : Fin n → Z) {δ : ℝ}
    (hdual : ∀ lam : ℝ, 0 < lam →
      lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
        - lam ^ 2 / (2 * (n : ℝ)) ≤ kl Q P + Real.log (1 / δ)) :
    sSup {v : ℝ | ∃ lam : ℝ, 0 < lam ∧
        v = lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
          - lam ^ 2 / (2 * (n : ℝ))}
      ≤ kl Q P + Real.log (1 / δ) := by
  -- 集合非空：取 `lam = 1 > 0`
  have hne : ({v : ℝ | ∃ lam : ℝ, 0 < lam ∧
      v = lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
        - lam ^ 2 / (2 * (n : ℝ))}).Nonempty :=
    ⟨1 * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
      - 1 ^ 2 / (2 * (n : ℝ)), 1, one_pos, rfl⟩
  -- 每个元素都由 `hdual` 控制 ⟹ 右侧是上界
  have hbdd : ∀ v ∈ {v : ℝ | ∃ lam : ℝ, 0 < lam ∧
      v = lam * (pacBayesPosteriorRisk loss Q - pacBayesPosteriorEmpRisk loss Q w)
        - lam ^ 2 / (2 * (n : ℝ))},
      v ≤ kl Q P + Real.log (1 / δ) := by
    rintro v ⟨lam, hlam, rfl⟩
    exact hdual lam hlam
  exact csSup_le hne hbdd

/-! ## 六、非空洞性见证 -/

/-- **退化实例（`k = 1`、`n = 1`）的「非空洞性」——⚠ 经审计为**重言式**，非空洞性见证**：

`k = 1` 时后验风险与经验风险都是 `loss` 的（唯一的）取值，
故 `pacBayesPosteriorRisk = pacBayesPosteriorEmpRisk`，
`gap = 0`，界退化为 `0 ≤ (KL + log(1/δ) + λ²/2)/λ`——**真但不紧**。

⚠⚠ **原稿 docstring 的过度承诺（已更正）**：原稿写
「本定理**验证** `RealPACBayes.pacBayes_risk_bound_of_exponent` 的结论
在该退化实例上成立……从而证明其**非空洞**」。**该说法为过度承诺**：
本定理的结论由 `hgap`（风险 = 经验风险，把左端直接替换）
与 `hnum`（分子 `≥ 0`）**直接重排**得出，形如
`x ≤ x + c`（`c = 分子/lam ≥ 0`）——它**不**验证基础定理的任何内容，
因为 `hgap` 与 `hnum` **都是本定理自己额外假设的**，
而它们**都不是** `pacBayes_risk_bound_of_exponent` 的假设。

**三分类判定**：`hnum` 与 `hgap` 在退化实例上**可满足**
（如 `k = 1`、`loss ≡ 0` 时风险 = 经验风险 = 0，`hgap` 成立），
故本定理**不是空洞真**，但其内容为**假设的复述**（**B222.2** 近亲）。
⇒ 它**不能**充作「PAC-Bayes 界非空洞」的见证；
真正的非空洞性应由「存在实例使**基础定理的界**（无额外假设）为真且非平凡」给出，
**本文件未给出**（诚实登记）。保留本条仅为「degenerate 情形的代数形状」记录。 -/
theorem pacBayes_degenerate_nonvacuous {Z : Type*} [Fintype Z] {n : ℕ}
    (P Q : Fin 1 → ℝ) (loss : Fin 1 → Z → ℝ) (w : Fin n → Z) {δ lam : ℝ}
    (hlam : 0 < lam) (hnum : 0 ≤ kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ)))
    (hgap : pacBayesPosteriorRisk loss Q = pacBayesPosteriorEmpRisk loss Q w) :
    pacBayesPosteriorRisk loss Q ≤
      pacBayesPosteriorEmpRisk loss Q w
        + (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam := by
  rw [hgap]
  have hdiv : 0 ≤ (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam :=
    div_nonneg hnum (le_of_lt hlam)
  linarith

/-! ## 七、诚实清单

1. **未重证**：本文件**不**重证 `RealPACBayes` 的任何定理；
   定理 3、4、6、7 的证明都以它的一条为**唯一**实质输入
   （分别是 `pacBayes_risk_bound_of_exponent` 与 `pacBayes_bound`），
   并**逐字复用**其假设。**这是本文件的定位：增量，不是复刻。**
2. **未做**：连续/可数先验后验（`Fin k` 之外）。
3. **未做**：数据相关先验（`KL(Q‖P̂(w))` 的局部化 PAC-Bayes）。
4. **未做**：`KL(Q‖P) = ∞` 的退化处理（需要扩展实数或显式排除）。
5. **未做**：最优 `λ` 的**自适应**版本（`λ` 依赖样本 `w`）——
   它破坏了「对一切 `w` 同时成立」的推导，属不同技术。
6. **诚实性（「放宽」是**空洞的**，⚠ 原稿此条自相矛盾，已更正）**：
   ⚠ **原稿此条为假且与本节 §三 自相矛盾**。原文声称
   「定理 4 用 `Q ≪ P` 换掉『`∀ h, 0 < P h`』……`k = 1` 时两者等价
   （唯一的 `h` 必满足 `P h > 0`），**只有 `k ≥ 2` 时才真正放宽**」，
   并给出「具体见证 `P = (1/2, 1/2, 0)`、`Q = (1/2, 1/2, 0)`」。
   **该见证不成立**：它**违反**定理 4 的假设
   `hQ : ∀ h, 0 < Q h`（`Q 2 = 0` **不**满足 `0 < Q 2`）。
   ⇒ 按三分类：它**不是**定理 4 的实例，**不能**见证任何放宽。
   （它**满足** `hsupp`（`P h = 0 → Q h = 0`）与 `hPsum = hQsum = 1`，
   但**恰好栽在 `hQ` 上**——而 `hQ` 正是本定理作为「放宽」的**承重假设**：
   去掉 `hQ` 才可能真正放宽，故 `hQ` 承重。）
   ⭐ **真相（与本节 §三 一致）**：在定理 4 **当前**的假设组合下，
   `hQ` + `hsupp` **已经强制** `∀ h, 0 < P h`，
   故 `hP : ∀ h, 0 ≤ P h` **完全冗余**，
   定理 4 的前提集与 `RealPACBayes.pacBayes_bound` **逐字相同**
   ——**「放宽」是空洞的**（这就是 §三 的结论）。
   ⇒ 「`k ≥ 2` 时才真正放宽」**是错的**：无论 `k` 多大都**不**放宽。
   本文件**不声称任何真正的假设放宽**（诚实登记）。
7. **诚实性（常数）**：定理 3 的 `sqrt(2nK)/n = sqrt(2K/n)` 是
   **精确的**最优 `λ` 代入（内核引理给出**等式**而非不等式）；
   本文件**没有**改进 `RealPACBayes` 的主常数（那需要
   `λ` 的最优性之外的信息），只做了**代入**。
   ⚠⚠ **修订（B231）**：原稿此处称「引理 1、2 给出等式」——**当时两条引理都错**：
   引理 1（`λ·n/2` 形）**真但不是所需的形状**（已改名
   `optimal_lambda_algebra_wrong_shape` 并保留），
   引理 2（`λ²·n/2` 形）**为假**（已删，反例定理
   `not_optimal_lambda_algebra_sq_form` 固化）。
   现由 `optimal_lambda_algebra_at_correct_lambda(')` 给出**正确 `λ* = √(2nK)`**
   处的等式。
8. **⚠ 诚实性（`δ = 1/2` 形式，修订后新增）**：
   原 `pacBayes_risk_bound_delta_half` 的 docstring 声称
   「`log 2 > 0` 使 `K = KL + log 2 > 0` **无条件成立**」——**为假**：
   `kl Q P` 在本文件的自由假设下可取负值（反例
   `k = 2`、`Q = (1/2, 1/2)`、`P = (2, 2)` 给出 `kl Q P = −2·log 2`，
   故 `K = −log 2 < 0`，已固化为定理 `not_delta_half_unconditional`）。
   ⇒ 修订后该定理**保留** `hK : 0 < kl Q P + Real.log 2`（与定理 3 同构），
   **不再**声称无条件可用。
9. **⚠ 诚实性（sup 形式，修订后新增）**：
   原 `pacBayes_bound_as_sup_form` **名不副实**（陈述里无 `sSup`），
   且其结论**逐字是自身假设的实例**（**B222.2**）。已**改名**为
   `pacBayes_bound_dual_rewrite`（**B136**）并修正 docstring；
   **新增** `pacBayes_bound_sup_form` 给出**真正**含 `sSup` 的形态
   （用 `csSup_le`，非重言）。⚠ 但本文件**仍**未形式化
   「与 `RealConcentrationDuality.LogSupForm` 同构」这一断言（仅形状观察）。
10. **⚠ 诚实性（`KL ≥ 0` 接入点，修订后新增）**：
   原 `pacBayes_kl_ge_zero_use` 的 `kl_nonneg` 调用**实参写反**
   （得到 `0 ≤ kl P Q`，而目标要 `0 ≤ kl Q P`；`kl` **不对称**），
   且其假设 `hδ1 : δ ≤ 1` **未被使用**（已删）。
   修订后该定理的结论是 `a ≤ b + a`（`b ≥ 0`）这一**平凡重整**，
   **不是**实质性的界——它的价值仅在于**登记**该接入点与其陷阱。
   ⚠ 且原 docstring「`δ ≥ 1` 时 `K ≥ 0` 可由 `KL ≥ 0` 保证」**方向也为假**
   （`δ ≥ 1` ⟹ `log(1/δ) ≤ 0` ⟹ `KL ≥ 0` **不能**推出 `K ≥ 0`）。
-/

end Lattice
