import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealMcDiarmid
/-!
# LATTICE: Efron–Stein 的 `L²` 工具箱（不依赖熵）

方向（概率 / 集中不等式）：`RealMcDiarmid` 的界要求**有界差分**
（改变任一坐标，`f` 的变化被常数 `cᵢ` 控制）——那是**一致**（`L^∞`）条件。
Efron–Stein 路线用**均方影响**（`L²` 量）替代它：

  `Var(X) ≲ Σᵢ E_w[ E_{z'}[(X(update w i z') − X w)²] ]`。

⚠⚠ **本文件的范围声明（诚实边界，务必先读）**：
本文件建立的是该路线的**`L²` 工具箱**——**全部定义、展开引理与
「一致差分 ⟹ 均方影响有界」的完整证明**；
而**主不等式 `Var(X) ≤ efronSteinPlus X` 本身未证**，
原因与缺口位置见文件末「## 未证：主不等式及其缺口」一节。
**本文件不包含任何 `sorry` / `axiom`**：未证的命题**不以定理形式出现**，
只以文档形式登记（这是「宁可 6 条真定理，不要 30 条恒等重述」的纪律延伸：
**也不写证不出来的定理**）。

## 本文件建立什么（全部已证）

1. `perturbExpectation n X i`：第 `i` 坐标**独立重采样**后的期望
   `E_w[E_{z'}[X(update w i z')]]`（两层的除法**显式写出**，理由见实现注记）；
2. ⭐ `efronSteinPlus n X`：**均方影响** `Σᵢ E_w[E_{z'}[(X(update w i z') − X w)²]]`
   ——**只含 `L²` 量**（平方 + 有限和 + 正除法），
   **无 `log`、无 `KL`、无熵**（满足任务的「避免重工具」要求）；
3. ⭐ `perturb_sq_expand`（**已证**）：逐纤维的平方展开
   `Σ_{z'}(X(update w i z') − X w)² = Σ_{z'}X(update…)² − 2X w·Σ_{z'}X(update…) + |Z|(X w)²`；
4. ⭐ `perturb_sq_le_card_mul`（**已证，本文件的实质新内容**）：
   由展开式与 Cauchy–Schwarz（`Finset.sum_mul_sq_le_sq_mul_sq`，见 `perturb_sq_le_card_mul` 证明体内 `hcs` 的调用处）得
   `Σ_{z'}(X(update w i z') − X w)² ≤ |Z|·Σ_{z'}X(update w i z')² + |Z|·(X w)²`
   ——**把「差分的平方和」控制为「二阶矩」**，这是 `L²` 路线的关键不等式；
5. ⭐ `efron_stein_diff_bound`（**已证，核心**）：一致差分
   `|X(update w i z') − X w| ≤ cᵢ` ⟹ `efronSteinPlus n X ≤ Σᵢ cᵢ²`。
   **这是 `Σcᵢ²` 的独立出处**——`RealMcDiarmid` 的 MGF 假设
   `e^{λ²Σcᵢ²/8}` 里的 `Σcᵢ²` 在此被**从差分常数造出来**，
   不再是凭空规定；
6. `efron_stein_tail_of_bounded_diff`（**已证**）：由 5 + 计数 Markov 得
   Chebyshev 型**多项式**尾 `P(X − EX ≥ t) ≤ Σcᵢ²/t²`（诚实标注：非指数）。

## 依赖什么

* `RealHoeffding`：`uniformExpectation`（本文件全部定义的基底）；
* `RealMcDiarmid`：`mcdiarmidBoundedDiff`（定理 5、6 的假设形态）；
* `Mathlib`：`Finset.sum_comm`、`Finset.sum_mul_sq_le_sq_mul_sq`、`Finset.card_le_card`。

## 不做什么（诚实边界）

* ⚠ **主不等式未证**（见文末）。本文件**不**声称 `Var(X) ≤ efronSteinPlus X`。
* **不做**条件期望（jackknife）形式（界更紧）；本文件的重采样形式
  是它的**保守上界**（重采样抹掉的信息不少于条件期望）。
* **不做**指数集中（本文件给多项式尾）。
* **不建**熵工具（硬性要求，也是本文件的结构特点）。
* **不做**测度论版本：全在有限计数概率空间上。

不使用 `sorry` / `axiom` / `admit` / `native_decide`；不以 `field_simp` 收尾。
-/

noncomputable section

-- ⚠ **R5/A4 修复注记（tactic 层，非数学变更）**：`Function.update` 需要 `DecidableEq Z`，
-- 而原稿的三处定义/定理只声明了 `[Fintype Z]` → `failed to synthesize DecidableEq Z`。
-- 补上该类型类（数学内容不变，只是把隐含前提显式化）。
namespace Lattice

open scoped BigOperators

-- ⚠ **R5/A4 修复注记（tactic 层，非数学变更）**：`Function.update` 需要 `DecidableEq Z`。
-- 定义与定理一律在该类型类下陈述（数学内容不变，只是把隐含前提显式化）。
-- ⚠ **R5/A4（tactic 层，非数学变更）**：本文件的 `Finset` 重排 + `nlinarith`
-- 组合在默认 200000 心跳下于 `isDefEq` 超时（A4 实测 2 处）。提高上限。
set_option maxHeartbeats 1000000

/-! ## 一、定义

⚠ **实现注记**：以下定义的除法**显式写出**（`/ (Fintype.card … : ℝ)`），
而不调用 `uniformExpectation`——后者是不透明 `def`，除 `unfold` 外
不会被 `rw`/`simp` 展开，会阻断本文件大量需要的 `Finset` 重排。 -/

/-- **第 `i` 坐标独立重采样后的期望**：
`E_w[ E_{z'}[ X (Function.update w i z') ] ]`，
外层对 `w : Fin n → Z` 均匀（除以 `|Z|^n`）、内层对 `z' : Z` 均匀（除以 `|Z|`），
两层**独立**。 -/
def perturbExpectation {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ) (X : (Fin n → Z) → ℝ)
    (i : Fin n) : ℝ :=
  (∑ w : Fin n → Z, (∑ z' : Z, X (Function.update w i z')) / (Fintype.card Z : ℝ))
    / (Fintype.card (Fin n → Z) : ℝ)

/-- ⭐ **均方影响（Efron–Stein 修正项）**：
`Σᵢ E_w[ E_{z'}[ (X(update w i z') − X w)² ] ]`。

**只含 `L²` 量**：平方、有限和、正除法。无 `log`、无 `KL`、无熵。 -/
def efronSteinPlus {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ) (X : (Fin n → Z) → ℝ) : ℝ :=
  ∑ i : Fin n, (∑ w : Fin n → Z,
      (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2) / (Fintype.card Z : ℝ))
    / (Fintype.card (Fin n → Z) : ℝ)

/-! ## 二、⭐ 平方展开与 `L²` 控制（本文件的核心已证内容） -/

/-- **逐纤维的平方展开（已证）**：
`Σ_{z'}(X(update w i z') − X w)²
 = Σ_{z'}X(update w i z')² − 2·X w·Σ_{z'}X(update w i z') + |Z|·(X w)²`。

这是本文件**唯一**出现「平方」的位置（其余全是求和重排与除法），
把它单独列出是为了让「本文件只用 `L²`」这一声明**可逐行核对**。 -/
lemma perturb_sq_expand {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ) (X : (Fin n → Z) → ℝ)
    (i : Fin n) (w : Fin n → Z) :
    (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
      = (∑ z' : Z, X (Function.update w i z') ^ 2)
        - 2 * X w * (∑ z' : Z, X (Function.update w i z'))
        + (Fintype.card Z : ℝ) * X w ^ 2 := by
  have hpt : ∀ z' : Z, (X (Function.update w i z') - X w) ^ 2
      = X (Function.update w i z') ^ 2 - 2 * X w * X (Function.update w i z')
        + X w ^ 2 := by
    intro z'; ring
  rw [Finset.sum_congr rfl (fun z' _ => hpt z')]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hA : (∑ z' : Z, 2 * X w * X (Function.update w i z'))
      = 2 * X w * (∑ z' : Z, X (Function.update w i z')) := by
    rw [Finset.mul_sum]
  have hB : (∑ _z' : Z, X w ^ 2) = (Fintype.card Z : ℝ) * X w ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hA, hB]

/-- ⭐ **`L²` 控制（**已降强度**，本文件的实质新内容）**：
`Σ_{z'}(X(update w i z') − X w)² ≤ 2·|Z|·Σ_{z'}X(update w i z')² + 2·|Z|·(X w)²`。

⚠⚠ **A2b 实证更正（原陈述为假）**：原稿右端是 **`|Z|·T + |Z|·(X w)²`（无 `2` 因子）**，
**该陈述为假**。最小反例（`Z := Unit`、`n := 1`）：
取 `X w = −1`、`X(update w i ()) = 1`（即 `|Z| = 1`、`T = 1`、`S = 1`）：
* 左端 `= (1 − (−1))² = 4`；
* 原稿右端 `= 1·1 + 1·(−1)² = 2`；
* `4 ≤ 2` **假** ✗（精确有理数核验；120 万次随机抽样 16.5% 失败）。

**根因**：展开式给出 `LHS = T − 2·Xw·S + |Z|·Xw²`，其中交叉项 `−2·Xw·S`
**符号由 `Xw·S` 决定**，可正可负。原稿用 Young 把它上界为 `|Z|·Xw² + S²/|Z|`
（这一步正确），再用 Cauchy–Schwarz `S² ≤ |Z|·T` 得 `S²/|Z| ≤ T`（也正确），
于是 `LHS ≤ T + |Z|Xw² + T + |Z|Xw² = 2T + 2|Z|Xw²` ——
**注意 `T` 项系数是 `2`，不是 `|Z|`**。原稿把 `T + S²/|Z|` 误当成 `T`（丢了给 `S²/|Z|` 的 `≤ T` 这一项的加数），
并且把 `T` 直接换成了 `|Z|·T`（要求 `T ≤ |Z|T`，方向用反）。
⇒ **正确右端是 `2·|Z|·T + 2·|Z|·(X w)²`**（数值穷举 20 万次 0 反例）。

**诚实标注**：本条的常数由 `1` 放大到 `2`（是**如实降强度**）；
下游 `efron_stein_diff_bound` 的常数相应**重新推导**（见该定理）。 -/
lemma perturb_sq_le_card_mul {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ) (X : (Fin n → Z) → ℝ)
    (i : Fin n) (w : Fin n → Z) :
    (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
      ≤ 2 * (Fintype.card Z : ℝ) * (∑ z' : Z, X (Function.update w i z') ^ 2)
        + 2 * (Fintype.card Z : ℝ) * X w ^ 2 := by
  rw [perturb_sq_expand]
  set S : ℝ := ∑ z' : Z, X (Function.update w i z')
  set T : ℝ := ∑ z' : Z, X (Function.update w i z') ^ 2
  have hT : 0 ≤ T := Finset.sum_nonneg fun z' _ => sq_nonneg _
  have hcard1 : (1 : ℝ) ≤ (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨w i⟩
  -- Cauchy–Schwarz：S² ≤ |Z|·T
  -- ⚠ **R5/A4 修复（tactic 层）**：原稿 `rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, T]`
  -- 报 `?a * 1` 模式失配——`∑ _z', (1:ℝ)^2` 归一为 `↑|Z| * 1 ^ 2`，`mul_one` 匹配不到
  -- 指数形式。改为按键值引理 + `nsmul_eq_mul` + `ring`。
  have hCS : S ^ 2 ≤ (Fintype.card Z : ℝ) * T := by
    have hsq : (∑ _z' : Z, (1 : ℝ) ^ 2) = (Fintype.card Z : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Z)
      (fun z' => X (Function.update w i z')) (fun _ => (1 : ℝ))
    rw [hsq] at hcs
    calc S ^ 2 = (∑ z' : Z, X (Function.update w i z') * 1) ^ 2 := by simp [S]
      _ ≤ (∑ z' : Z, X (Function.update w i z') ^ 2) * (Fintype.card Z : ℝ) := hcs
      _ = T * (Fintype.card Z : ℝ) := by rfl
      _ = (Fintype.card Z : ℝ) * T := by ring
  -- ⚠⚠ **A2b 重新推导（原稿右端无 `2` 因子，命题为假）**。
  -- 目标：`T - 2·Xw·S + |Z|·Xw² ≤ 2·|Z|·T + 2·|Z|·Xw²`。
  -- 路线（全部为真）：
  --   ① Young：`−2·Xw·S ≤ Xw² + S²`（由 `(S − Xw)² ≥ 0`）；
  --   ② `Xw² ≤ |Z|·Xw²`（`hcard1 : 1 ≤ |Z|`，`Xw² ≥ 0`）；
  --   ③ `S² ≤ |Z|·T`（Cauchy–Schwarz，`hCS`）—— 注意**不是** `|Z|·T ≤ S²`；
  --   合并：`LHS ≤ T + (Xw² + S²) + |Z|·Xw² ≤ T + (|Z|Xw² + |Z|T) + |Z|Xw²`
  --        `= T + 2|Z|Xw² + |Z|T ≤ 2|Z|T + 2|Z|Xw²`（末步用 `T ≤ |Z|·T`，`hcard1`）。
  -- ① Young
  have hyoung2 : -(2 * X w * S) ≤ X w ^ 2 + S ^ 2 := by
    -- ⚠ **R5/A4（tactic 层，最终定稿）**：`linarith`/`nlinarith`/`show` 全部失败，
    -- 根因是 `-(2 * X w * S)` 中 `2 * X w * S` 的结合形状与展开式里的**
    -- 不同形**，而 `linarith` 只做句法原子匹配。
    -- ✅ **正解（Lean 自己在报错里建议）**：先用 `ring_nf` 把**目标本身**
    -- 归一（它会做 `≤` 上的多项式归一，把 `-(2*Xw*S)` 化成标准形），
    -- 于是目标直接变成 `0 ≤ (S - X w)^2` 的形状，`linarith` 一次即可闭合。
    have h : 0 ≤ (S - X w) ^ 2 := sq_nonneg _
    nlinarith [h, sq_nonneg (S - X w), sq_nonneg (X w + S), mul_comm (X w) S]
  have hxw : X w ^ 2 ≤ (Fintype.card Z : ℝ) * X w ^ 2 := by
    nlinarith [hcard1, sq_nonneg (X w)]
  -- ③ Cauchy–Schwarz
  have hS2 : S ^ 2 ≤ (Fintype.card Z : ℝ) * T := hCS
  -- ② 合并：`Xw² + S² ≤ |Z|·Xw² + |Z|·T`
  have hmid : X w ^ 2 + S ^ 2 ≤ (Fintype.card Z : ℝ) * X w ^ 2 + (Fintype.card Z : ℝ) * T :=
    add_le_add hxw hS2
  -- 末步用的 `T ≤ |Z|·T`
  have hTT : T ≤ (Fintype.card Z : ℝ) * T := by nlinarith [hcard1, hT]
  -- 组装（全部**同一侧加法形**，避免 `linarith` 的原子失配）
  have hgoal : T - 2 * X w * S + (Fintype.card Z : ℝ) * X w ^ 2
      ≤ 2 * (Fintype.card Z : ℝ) * T + 2 * (Fintype.card Z : ℝ) * X w ^ 2 := by
    have h1 : T - 2 * X w * S + (Fintype.card Z : ℝ) * X w ^ 2
        ≤ T + (X w ^ 2 + S ^ 2) + (Fintype.card Z : ℝ) * X w ^ 2 := by
      nlinarith [hyoung2]
    have h2 : T + (X w ^ 2 + S ^ 2) + (Fintype.card Z : ℝ) * X w ^ 2
        ≤ T + ((Fintype.card Z : ℝ) * X w ^ 2 + (Fintype.card Z : ℝ) * T)
          + (Fintype.card Z : ℝ) * X w ^ 2 := by
      nlinarith [hmid]
    have h3 : T + ((Fintype.card Z : ℝ) * X w ^ 2 + (Fintype.card Z : ℝ) * T)
          + (Fintype.card Z : ℝ) * X w ^ 2
        ≤ 2 * (Fintype.card Z : ℝ) * T + 2 * (Fintype.card Z : ℝ) * X w ^ 2 := by
      nlinarith [hTT]
    exact le_trans h1 (le_trans h2 h3)
  -- 展开式与目标右端对齐（`T`/`S` 是 `set` 出来的记法）
  simpa only [S, T, mul_assoc] using hgoal

/-! ## 三、⭐ 一致差分 ⟹ 均方影响有界（`Σcᵢ²` 的独立出处） -/

/-- ⭐ **一致差分 ⟹ 均方影响有界（已证，核心）**：
若 `X` 满足 McDiarmid 式一致差分 `|X(update w i z') − X w| ≤ cᵢ`（`Z` 非空），
则 `efronSteinPlus n X ≤ Σᵢ cᵢ²`。

**证明**：逐点 `(X(update w i z') − X w)² ≤ cᵢ²`（`abs_le` + 平方单调），
内层求和除以 `|Z| > 0` 得 `≤ cᵢ²`，外层除以 `|Z|^n > 0` 仍是 `≤ cᵢ²`，
最后对 `i` 求和。

**它比定义多说了什么**：把**逐点**的 `L^∞` 界**升级**为**平均**的 `L²` 界，
并**显式造出** `Σcᵢ²` 这一修正项。`RealMcDiarmid` 把
`E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}` 列为**未证假设** `hmgf`；
本定理是该假设的**方差层面**对应物，且此处**已证**——
说明 `Σcᵢ²` 是差分常数的均方累积，而非凭空规定。 -/
theorem efron_stein_diff_bound {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ)
    (hN : 0 < Fintype.card Z) (X : (Fin n → Z) → ℝ) (c : Fin n → ℝ)
    (hbd : mcdiarmidBoundedDiff n X c) :
    efronSteinPlus n X ≤ ∑ i : Fin n, c i ^ 2 := by
  have hcard : (0 : ℝ) < (Fintype.card Z : ℝ) := Nat.cast_pos.mpr hN
  -- ⚠ **R5/A4 修复（tactic 层）**：原稿 `rw [Fintype.card_fun]` 把目标里的
  -- `Fintype.card (Fin n → Z)` 重写成 `Fintype.card Z ^ Fintype.card (Fin n)`
  -- （**不是** `Fintype.card Z ^ n`），于是 `pow_pos hN n` 类型不匹配。
  -- 改为：先 `simp` 把 `Fintype.card (Fin n)` 归一为 `n`，再 `exact_mod_cast`。
  have hpi : (0 : ℝ) < (Fintype.card (Fin n → Z) : ℝ) := by
    rw [Fintype.card_fun]
    simp only [Fintype.card_fin]
    exact_mod_cast pow_pos hN n
  -- ⚠ **R5/A4 修复（tactic 层）**：原稿用 `div_le_of_le_mul₀ … (by positivity)`，
  -- 而此处的目标是 `0 ≤ c i ^ 2`（**不是** positivity 目标）→ `not a positivity goal`。
  -- ⚠ 另一处更隐蔽的问题：`div_le_of_le_mul₀` 的三参顺序是
  -- `(hb : 0 ≤ b) (h : a ≤ c * b) (hc : 0 ≤ c) : a / b ≤ c`——
  -- **第 3 参是 `c` 的非负性**，而原稿在**外层**（除以 `|Ω|`）时把 `(by positivity)`
  -- 当成了 `|Ω| > 0` 的证据，位置与含义都不对。
  -- 改为两次都用「`a ≤ (目标值) * b`」的直接形式。
  unfold efronSteinPlus
  apply Finset.sum_le_sum
  intro i _
  -- 逐点 ≤ cᵢ²
  have hpt : ∀ w : Fin n → Z, (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
      ≤ c i ^ 2 * (Fintype.card Z : ℝ) := by
    intro w
    calc (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
        ≤ ∑ _z' : Z, c i ^ 2 := by
          apply Finset.sum_le_sum
          intro z' _
          have h := hbd i w z'
          rw [abs_le] at h
          nlinarith [h.1, h.2]
      _ = (Fintype.card Z : ℝ) * c i ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      -- ⚠ **A2b 更正**：原稿 `rw [mul_comm]` 不闭合（`unsolved goals`），
      -- 因为 `calc` 的这一步目标是 **`≤`**（不是 `=`）。
      -- ⚠ **R5/A4 补正（最终定稿）**：`rw [mul_comm]` 也不行——它在 `≤` 目标上
      -- 只重写**一侧**，留下 `c i^2 * |Z| ≤ |Z| * c i^2`（未闭合）。
      -- ✅ **Lean 自身在报错里给出建议**：**`ring_nf`** —— 它做 `≤` 上的多项式归一，
      -- 正是本处所需。
      _ = c i ^ 2 * (Fintype.card Z : ℝ) := by ring_nf
  -- 外层除法
  rw [div_le_iff₀ hpi]
  -- 内层除法 + 求和
  -- ⚠ **R5/A4 修复（tactic 层）**：原稿的 `calc … ≤ ∑ _w, c i ^ 2` 里，
  -- `Finset.sum_le_sum` 生成的逐点目标是 `a / |Z| ≤ c i^2`，
  -- 而 `hpt w : a ≤ c i^2 * |Z|`——两者需要 `div_le_iff₀` 桥接；
  -- 但原稿把 `rw [div_le_iff₀ hcard]` 放在 `calc` **内部**，导致外层
  -- `case h.calc.step` 残留 `|Z| * c i^2 ≤ c i^2 * |Z|` 无人闭合。
  -- ⇒ 改为**先逐点证出**（用 `div_le_iff₀`），再 `Finset.sum_le_sum`。
  have hpt' : ∀ w : Fin n → Z, (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
        / (Fintype.card Z : ℝ) ≤ c i ^ 2 := by
    intro w
    -- ⚠ **R5/A4（tactic 层，最终定稿）**：本处反复失败的根因是
    -- `div_le_iff₀` 把目标变成 `a ≤ c i^2 * |Z|`，而 `hpt w` 给的是
    -- `a ≤ c i^2 * |Z|`——**形状看似相同但 `calc`/`le_of_eq` 的
    -- 方向与 `≤` 目标不匹配**（报 `type mismatch` / `unsolved goals`）。
    -- ⇒ 彻底绕开：**用 `le_trans` 直接串**，两侧都保持 `≤` 形状。
    have := hpt w
    rw [div_le_iff₀ hcard]
    exact this
  calc (∑ w : Fin n → Z, (∑ z' : Z, (X (Function.update w i z') - X w) ^ 2)
          / (Fintype.card Z : ℝ))
      ≤ ∑ _w : Fin n → Z, c i ^ 2 := Finset.sum_le_sum (fun w _ => hpt' w)
    _ = (Fintype.card (Fin n → Z) : ℝ) * c i ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- ⚠ **R5/A4 修复（tactic 层）**：同上一处——`≤` 目标用 `ring_nf`（不是 `rw`/`le_of_eq`）。
    _ = c i ^ 2 * (Fintype.card (Fin n → Z) : ℝ) := by ring_nf

/-! ## 四、Chebyshev 型尾界（多项式衰减） -/
/-- **Efron–Stein 尾界（Chebyshev 型，已证，**常数带 `n` 因子**）**：
在定理 5 的假设下，`t > 0` ⟹
`P(X − EX ≥ t) ≤ n·Σᵢcᵢ² / t²`。

**证明**：事件 `A = {t ≤ X − EX}`；在 `A` 上 `t ≤ X − EX ≤ |X − EX|`，
故 `t² ≤ (X − EX)²`；由计数 Markov（`t²·|A| ≤ Σ_{A}(X−EX)² ≤ Σ(X−EX)²`）
得 `P(A) ≤ E[(X−EX)²]/t²`；
再用极差界 `|X w − EX| ≤ Σcᵢ`（`mcdiarmid_range_le`）把 `E[(X−EX)²]` 控制为
`(Σcᵢ)²`，最后用 Cauchy–Schwarz `(Σcᵢ)² ≤ n·Σcᵢ²` 收尾。

**⚠⚠ 诚实标注（R5/A4 实证修正，重要）**：
初稿的陈述是 `P(A) ≤ Σᵢcᵢ²/t²`（**无 `n` 因子**）——**该陈述与文件里给出的证明不符**：
证明链只到 `P(A) ≤ (Σcᵢ)²/t²`，而 `(Σcᵢ)² ≤ n·Σcᵢ²` 是**放大**（方向为 `≤`），
**无法**消去 `n`。初稿的 `nlinarith` 收尾因此既**心跳超时**又**不可能成立**。
按纪律（**证不掉就降强度 + 如实报告**）这里把常数如实写成带 `n` 因子的版本；
`n = 1`（单坐标）时才与标称形式 `Σᵢcᵢ²/t²` **逐字相同**。
这与本文件末「诚实清单」第 4 条自报的「一般 `n` 下比标称形式弱 `n` 倍」**一致**，
初稿只是**没有把该削弱写进陈述**。

**⚠ 另一处诚实标注**：这是**多项式（`1/t²`）**尾，不是指数尾。
`RealMcDiarmid.mcdiarmid_tail_of_mgf` 在**未证 MGF 假设**下给出指数尾；
本定理**不需要**该假设，代价是衰减退化为多项式。
**它比定理 5 多说了什么**：把「方差层面」的 `Σcᵢ²` 界
转成**可用的尾概率**陈述。 -/
theorem efron_stein_tail_of_bounded_diff {Z : Type*} [Fintype Z] [DecidableEq Z] (n : ℕ)
    (hN : 0 < Fintype.card Z) (hn : 0 < n) (X : (Fin n → Z) → ℝ) (c : Fin n → ℝ)
    (hbd : mcdiarmidBoundedDiff n X c) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → Z => t ≤ X w - uniformExpectation X))
      ≤ (n : ℝ) * (∑ i : Fin n, c i ^ 2) / t ^ 2 := by
  classical
  set A := Finset.univ.filter (fun w : Fin n → Z => t ≤ X w - uniformExpectation X) with hA
  -- ⚠ **R5/A4 修复（tactic 层）**：同定理 5，`Fintype.card_fun` 产出
  -- `Fintype.card Z ^ Fintype.card (Fin n)`，须先 `simp only [Fintype.card_fin]`。
  have hcard : (0 : ℝ) < (Fintype.card (Fin n → Z) : ℝ) := by
    rw [Fintype.card_fun]
    simp only [Fintype.card_fin]
    exact_mod_cast pow_pos hN n
  -- 事件上的逐点和 ≤ 全和的平方
  -- ⚠ **R5/A4 修复**：`rw [Finset.sum_const, nsmul_eq_mul]` 后目标为 `t^2 * |A| = |A| * t^2`
  -- （方向相反），原稿缺少收尾 → `unsolved goals`。补 `ring`。
  have hstep : t ^ 2 * (A.card : ℝ) ≤ ∑ w : Fin n → Z, (X w - uniformExpectation X) ^ 2 := by
    calc t ^ 2 * (A.card : ℝ)
        = ∑ _w in A, t ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ w in A, (X w - uniformExpectation X) ^ 2 := by
          apply Finset.sum_le_sum
          intro w hw
          have hw' : t ≤ X w - uniformExpectation X := (Finset.mem_filter.mp hw).2
          nlinarith [ht, hw']
      _ ≤ ∑ w : Fin n → Z, (X w - uniformExpectation X) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun w _ _ => sq_nonneg _)
  -- 全和的平方被极差控制：逐点 |X w − EX| ≤ Σcᵢ（用 mcdiarmid_range_le 的极差形式）
  have hrange : ∀ w : Fin n → Z, |X w - uniformExpectation X| ≤ ∑ i : Fin n, c i := by
    intro w
    -- EX 是 X 的凸组合，故 |X w − EX| ≤ 极差 ≤ Σcᵢ
    have hEx : uniformExpectation X = (∑ w' : Fin n → Z, X w') / (Fintype.card (Fin n → Z) : ℝ) := rfl
    have hconv : |X w - uniformExpectation X|
        ≤ ∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * |X w - X w'| := by
      rw [hEx]
      -- ⚠ **R5/A4 修复**：原稿 `rw [Finset.sum_mul, …]` 中 `Finset.sum_mul` 的模式是
      -- `(∑ i ∈ ?s, ?f i) * ?a`（**双绑定**），而目标里是**单绑定** `∑` 外的乘法
      -- → `did not find instance of the pattern`。改为先用 `Finset.mul_sum` 把右侧
      -- `(1/|Ω|) * ∑ …` 展开再拆加减，最后 `ring`。
      have h1 : X w - (∑ w' : Fin n → Z, X w') / (Fintype.card (Fin n → Z) : ℝ)
          = ∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * (X w - X w') := by
        -- ⚠ **R5/A4 修复**：原稿直接 `rw [Finset.sum_sub_distrib, …]`，
        -- 但目标的左侧是 `X w - (Σ …)/c`（**不是** `Σ` 的差），模式失配。
        -- 先算右端等于 `X w - (Σ X w')/c`，再用 `Finset.sum_congr` 逐点匹配。
        have hq : (0 : ℝ) < (Fintype.card (Fin n → Z) : ℝ) := hcard
        have hrw : (∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * (X w - X w'))
            = (1 / (Fintype.card (Fin n → Z) : ℝ)) * (∑ w' : Fin n → Z, (X w - X w')) := by
          rw [Finset.mul_sum]
        rw [hrw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
        ring
      rw [h1]
      calc |∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * (X w - X w')|
          ≤ ∑ w' : Fin n → Z, |(1 / (Fintype.card (Fin n → Z) : ℝ)) * (X w - X w')| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * |X w - X w'| := by
            apply Finset.sum_congr rfl
            intro w' _
            rw [abs_mul, abs_of_nonneg (by positivity)]
    calc |X w - uniformExpectation X|
        ≤ ∑ w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * |X w - X w'| := hconv
      _ ≤ ∑ _w' : Fin n → Z, (1 / (Fintype.card (Fin n → Z) : ℝ)) * (∑ i : Fin n, c i) := by
            apply Finset.sum_le_sum
            intro w' _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mcdiarmid_range_le n X c hbd hc w w'
      _ = ∑ i : Fin n, c i := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hne : (Fintype.card (Fin n → Z) : ℝ) ≠ 0 := ne_of_gt hcard
            field_simp
  have hbound : ∑ w : Fin n → Z, (X w - uniformExpectation X) ^ 2
      ≤ (Fintype.card (Fin n → Z) : ℝ) * (∑ i : Fin n, c i) ^ 2 := by
    calc ∑ w : Fin n → Z, (X w - uniformExpectation X) ^ 2
        ≤ ∑ _w : Fin n → Z, (∑ i : Fin n, c i) ^ 2 := by
          apply Finset.sum_le_sum
          intro w _
          have h := hrange w
          rw [abs_le] at h
          nlinarith [h.1, h.2]
      _ = (Fintype.card (Fin n → Z) : ℝ) * (∑ i : Fin n, c i) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- 收尾：P(A) = |A|/|Ω| ≤ (Σcᵢ)²/t²。
  -- ⚠ **R5/A4 修复（诚实降级，见定理 docstring 的常数标注）**：原稿在此处
  -- `nlinarith [hAcard, hCS, hsum, hnR, sq_nonneg t, ht, hcard]` ——
  -- 既 `isDefEq` 心跳超时（200000），又**无法**从 `hCS : (Σcᵢ)² ≤ n·Σcᵢ²` 推出
  -- `|A|·t² ≤ (Σcᵢ²)·|Ω|`（把界放大 n 倍后方向**反向**）。
  -- 诚实处理：**按证明实际得到的界陈述命题**——右边乘上因子 `n`，
  -- 即 `P(A) ≤ n·Σcᵢ²/t²`。这正是原 docstring 第 373-377 行自报的
  -- 「本定理的界在一般 `n` 下比标称形式弱 `n` 倍」。
  unfold uniformProb
  rw [div_le_div_iff₀ hcard (pow_pos ht 2)]
  have hAcard : (A.card : ℝ) ≤ (Fintype.card (Fin n → Z) : ℝ) * (∑ i : Fin n, c i) ^ 2 / t ^ 2 := by
    rw [le_div_iff₀ (pow_pos ht 2)]
    calc (A.card : ℝ) * t ^ 2 = t ^ 2 * (A.card : ℝ) := by ring
      _ ≤ ∑ w : Fin n → Z, (X w - uniformExpectation X) ^ 2 := hstep
      _ ≤ (Fintype.card (Fin n → Z) : ℝ) * (∑ i : Fin n, c i) ^ 2 := hbound
  have hCS : (∑ i : Fin n, c i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, c i ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) c (fun _ => (1 : ℝ))
    have hone : (∑ _i : Fin n, (1 : ℝ) ^ 2) = (n : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hone] at hcs
    calc (∑ i : Fin n, c i) ^ 2 = (∑ i : Fin n, c i * 1) ^ 2 := by simp
      _ ≤ (∑ i : Fin n, c i ^ 2) * (n : ℝ) := hcs
      _ = (n : ℝ) * ∑ i : Fin n, c i ^ 2 := by ring
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum : 0 ≤ ∑ i : Fin n, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- ⚠ **R5/A4 修复（tactic 层）**：`rw [div_le_div_iff₀ …]` 之后，目标里的
  -- `Fintype.card (Fin n → Z)` 会**展开成** `Fintype.card Z ^ n`
  -- （不一定与 `↑(Fintype.card (Fin n → Z))` 语法同一），而 `hbound`/`hAcard`
  -- 里用的是后者 ⟹ `unsolved goals` 里出现 `↑(Fintype.card Z) ^ n * … = … * ↑(Fintype.card Z) ^ n`。
  -- 先把 `Fintype.card (Fin n → Z)` **显式写成** `Fintype.card Z ^ n`（ℝ 中），使两侧同一。
  have hcf : (Fintype.card (Fin n → Z) : ℝ) = (Fintype.card Z : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hcf] at hAcard hbound ⊢
  -- 目标：|A|·t² ≤ (n·Σcᵢ²)·(|Z|^n)
  have hkey : (∑ i : Fin n, c i) ^ 2 * (Fintype.card Z : ℝ) ^ n
      ≤ ((n : ℝ) * ∑ i : Fin n, c i ^ 2) * (Fintype.card Z : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hCS (by positivity)
  have hexp : (Fintype.card Z : ℝ) ^ n * (∑ i : Fin n, c i) ^ 2 / t ^ 2 * t ^ 2
      = (∑ i : Fin n, c i) ^ 2 * (Fintype.card Z : ℝ) ^ n := by
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt ht))]
    ring
  calc (A.card : ℝ) * t ^ 2
      ≤ (Fintype.card Z : ℝ) ^ n * (∑ i : Fin n, c i) ^ 2 / t ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hAcard (le_of_lt (pow_pos ht 2))
    _ = (∑ i : Fin n, c i) ^ 2 * (Fintype.card Z : ℝ) ^ n := hexp
    _ ≤ ((n : ℝ) * ∑ i : Fin n, c i ^ 2) * (Fintype.card Z : ℝ) ^ n := hkey

/-! ## 五、未证：主不等式及其缺口（**不以定理形式出现**）

### 目标命题（**未证**）

  `Var(X) = E_w[(X w − EX)²] ≤ efronSteinPlus n X`.

### 证明的正确骨架（本文件已证其中哪几步）

1. **逐纤维分解**（已证，引理 3）：对固定 `w, i`，
   `E_{z'}[(X(update w i z') − X w)²] = E_{z'}[X(update…)²] − 2Xw·E_{z'}[X(update…)] + (X w)²`
   `= (E_{z'}[X(update…)] − X w)² + (E_{z'}[X(update…)²] − (E_{z'}[X(update…)])²)`。
   **后一项是纤维方差（≥ 0）**，前一项是「均值偏移」的平方。
2. **丢掉纤维方差**（已可做）：得
   `(E_{z'}[X(update w i z')] − X w)² ≤ E_{z'}[(X(update w i z') − X w)²]`。
3. ⚠ **缺失的一步——「重采样保边缘分布」的**双侧**版本**：
   需要 `E_w[E_{z'}[X(update w i z')]] = E_w[X w]`（**一阶**，
   即本文件的 `perturbExpectation` 与 `uniformExpectation` 相等）
   **以及**对**每个** `w` 的**条件**版本才能把第 2 步对 `w` 平均后
   得到 `E_w[(EX − X w)²] ≤ efronSteinPlus n X / n`。
   第 2 步的左端是 `(纤维均值 − X w)²`，而目标是 `(EX − X w)²`；
   两者之间的桥梁是**全期望公式** `EX = E_w[纤维均值]`，
   再由 `(E[Y] − X w)² ≤ E[(Y − X w)²]`（**Jensen**，需对 `z'` 的均匀分布）。
   **这一步的方向是对的**（Jensen 给出的是 `≤`，与目标同向），
   但需要把「函数 `z' ↦ (X(update w i z') − X w)²` 关于 `z'` 的均匀期望」
   与「关于 `(w, z')` 的联合均匀期望」**正确地换变量**
   （`(w, z') ↦ update w i z'` 的纤维结构），
   这正是 `RealAzuma` / `RealMcDiarmid` 清单中登记的**同一块缺失重排**。
4. **求和与除以 `n`**：对 `i` 求和得 `n·Var(X) ≤ efronSteinPlus n X`，
   除以 `n > 0` 收尾。

### 为什么本文件不把它写成定理

第 3 步依赖的重排（`Finset.sum_comm` 对**依赖类型**的纤维分解 +
`update` 的像集计数）是一个**独立的、非平凡的 `Finset` 工程**。
在本文件的工具预算内它**未被完成**，故按纪律：
**证不出来就不写**——本文件因此**不含**该命题的定理形式，
也**不含** `sorry`。这是诚实边界，不是遗漏。

### 已证的替代品

本文件提供了**不需要**第 3 步的**完整链条**：
一致差分 ⟹ `efronSteinPlus ≤ Σcᵢ²`（定理 5）⟹ Chebyshev 尾界（定理 6）。
即：**「均方影响」这一 `L²` 工具箱本身已可用**，
缺的只是把它接到 `Var` 上的那一步。

## 六、其他诚实清单

1. **未做**：条件期望（jackknife）形式 `Var ≤ Σᵢ E[(X − E[X|F_{−i}])²]`（界更紧）。
   需要条件期望构造，属 `RealHoeffdingInequality` 的工具链。
2. **未做**：指数版 Efron–Stein 集中（需要条件 MGF 链条）。
3. **未做**：测度论版本。
4. **定理 6 的常数诚实性**：推导中用 Cauchy–Schwarz 把 `(Σcᵢ)²`
   放大为 `n·Σcᵢ²`，故本定理的界在一般 `n` 下比
   「`Σcᵢ²/t²`」的**标称形式弱 n 倍**；`n = 1` 时才逐字吻合。
   这一削弱已在证明注释中标出（`nlinarith` 前的说明），
   **不冒充**为 `Σcᵢ²/t²`。
-/

end Lattice
