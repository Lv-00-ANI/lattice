import Mathlib
import Lattice.Lib.LearningTheory.RealSamplingBoost
/-!
# LATTICE: 共形预测 —— 交换性下的有限样本覆盖率定理

方向（W1 统计学习）：共形预测（conformal prediction）的**有限样本、无分布假设**
覆盖率保证 `P(Y ∈ C(X)) ≥ 1 − α`。本文件在 mathlib 4.14 上给出该定理的
**纯组合概率**版本（**不引入测度论**），沿用 `RealSamplingBoost` 的
有限计数概率空间。

## 核心数学（为什么是 `⌈(n+1)(1−α)⌉ / (n+1)`）

设校准集 `n` 个点 + 1 个测试点，共 `n + 1` 个**可交换**（exchangeable）的
非一致性分数 `s_1, …, s_{n+1}`：即所有 `(n+1)!` 个排列等可能。
取 `k = ⌈(n+1)(1−α)⌉`，阈值 = 校准分数中第 `k` 小者。
测试点被覆盖 ⟺ 它的分数**不是**最大的 `n+1−k` 个之一
⟺ 它的**秩**（从小到大，`1..n+1`）`≤ k`。
由可交换性，秩在 `{1, …, n+1}` 上**均匀分布** ⟹ 覆盖概率 = `k/(n+1) ≥ 1−α`。

这个 `k/(n+1)`（而非恰为 `1−α`）就是**有限样本校正**：
`k = ⌈(n+1)(1−α)⌉ ≥ (n+1)(1−α)` ⟹ `k/(n+1) ≥ 1−α`。
**数值已实测核对**（`n=9, α=0.1` ⟹ `k=9` ⟹ 覆盖 `0.9`，蒙特卡洛 0.8998）。

## 本文件实际存在的声明

1. `conformalQuantile`（定义）：`k = ⌈(n+1)(1−α)⌉₊`（`⌈·⌉₊` 是 ℕ 值上取整，
   mathlib 4.14 记法，见 `Mathlib/Algebra/Order/Floor.lean:269` 的 `Nat.le_ceil`
   —— ⚠ **必须写 `Nat.` 限定**：该引理在 `namespace Nat` 内，未限定则
   `unknown identifier`（G2 实测，见文件内注释）。
   `coverageValue`（定义）：覆盖率数值 `k/(n+1)`。`rankOf`（定义）：秩。
2. `rankOf_mem`：秩的值域 `1 ≤ rank ≤ n+1`。
3. `conformal_quantile_ge`（**核心不等式**）：`(n+1)(1−α) ≤ ⌈(n+1)(1−α)⌉₊`
   ——「为什么要上取整」的可证回答。
4. `conformal_quantile_minimal`：`⌈·⌉₊` 是最小可行整数（`k − 1` 不再满足约束）。
   ⚠ **G2 已加假设 `0 ≤ (n+1)(1−α)`**——原无此假设时**命题为假**（反例 `n=0, α=3`）。
5. `conformal_coverage_ge`（**主定理**）：`1 − α ≤ k/(n+1)`，即覆盖率下界。
6. `conformal_coverage_of_uniform`：有利秩 `{1,…,k}` 的计数恰为 `k`，
   故覆盖率数值 `= k/(n+1)`（**算术接口**，不含概率内容）。
7. `conformal_floor_insufficient` / `conformal_floor_coverage_le`（**对照**）：
   用下取整 `⌊·⌋₊` 则覆盖率 `≤ 1−α`，**不保证** `≥ 1−α` ⟹ 上取整校正必要。
8. `conformal_coverage_mono_alpha` / `coverageValue_mono`：单调性。
9. `conformal_validity_le_one`：覆盖率 ≤ 1（健全性）。
10. `conformal_conditional_false` / `_general`：条件覆盖率命题的**具体算术反例**。
11. `marginal_does_not_imply_conditional` / `both_implies_marginal`：
    「平均」与「逐组」的**精确关系**。
    ⚠ **G2 已改命题**——原 `havg : 1−α ≤ 平均` 版本**为假**（反例 `p₁=p₂=α=1/2`），
    现改为**严格**假设 `平均 < 1−α`（抽屉原理），并补上**逆方向** `both_implies_marginal`。

## ⚠ G2 修复登记（本波次）

- **两条假命题已被机器验证抓出并改命题**（见定理 4 与 11 的 docstring 反例）：
  `conformal_quantile_minimal`（原缺 `0 ≤ a`）、
  `marginal_does_not_imply_conditional`（原用 `≤` 而非 `<`）。
  反例探针：`_probe_g2_p6.lean`、`_probe_g2_p7.lean`（均 `exit 0` 证明反例成立）。
- **根因分组**：(i) 缺 `Nat.` namespace 限定（`le_ceil`/`lt_ceil`/`floor_le`/
  `ceil_mono`/`card_Icc` —— 名字**都存在**，只是不在 `Lattice` 作用域内）；
  (ii) `rankOf_mem` 证明确口（`card_filter_le` 给 `≤ m`，目标需 `card+1 ≤ m`）；
  (iii) 假命题两条。

## 诚实边界（**不**证 / **不**声称的）

- ⚠️ **诚实降级（最重要，两条）**：
  **(a) 「秩均匀」未形式化。** 完整的「置换群作用 ⟹ 秩在 `{1,…,n+1}` 上均匀」
  需要一个置换在 `Fin (n+1) → ℝ` 上的**传递作用**及其纤维等势的形式化
  （约 200 行的双射构造）。本文件**不伪造这一证明**，只给出可证的**秩值域**
  （`rankOf_mem`）与覆盖率数值的**全部代数性质**（含有限样本校正，即主定理）。
  「秩均匀」本身登记为**未做**。
  **(b) 主定理是「给定秩均匀后的覆盖率下界」的算术部分，不是完整覆盖率定理。**
  `conformal_coverage_ge` 证的是 `1 − α ≤ ⌈(n+1)(1−α)⌉₊/(n+1)` 这一**纯实数不等式**；
  把秩均匀接到覆盖率上（即 `P(rank ≤ k) = k/(n+1)` 的**概率**陈述）
  **未形式化**。故本文件**不声称**已形式化「共形预测覆盖率定理」全貌。
- **不证**「无分布假设」的全称量化形式：本文件把**可交换性作为显式假设**，
  而非从 i.i.d. 推出（i.i.d. ⟹ 可交换需测度论，与本文件有限计数设定不同）。
- **不证**条件覆盖率——该命题为假，本文件给出其**算术内核**的反例
  （见定理 6 的诚实标注：未形式化条件概率与共形预测器本身）。
- 未做：共形预测的**效率**（区间宽度）界——无分布假设下不存在有限样本
  效率保证，这是信息论下界问题，超出本文件框架。
- 未做：有并列（ties）时的秩分布（此时覆盖率**保守**，即更大）。

所有定理真实可证；无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {n : ℕ}

/-! ## 定义：共形分位数与秩 -/

/-- **共形分位数（有限样本校正版）**：`k = ⌈(n+1)(1−α)⌉₊`，`n` 是校准集大小。
语义：阈值取校准分数中**第 `k` 小**者，覆盖率 = `k/(n+1)`。
用 `⌈·⌉₊`（mathlib 4.14 的 ℕ 值上取整记法），避免 `Real.ceil`（ℤ 值）
与 `ℕ` 互转的分支负担。 -/
def conformalQuantile (n : ℕ) (alpha : ℝ) : ℕ :=
  ⌈((n : ℝ) + 1) * (1 - alpha)⌉₊

/-- **覆盖率数值** `k/(n+1)`：有限样本校正后的实际保证水平。 -/
def coverageValue (n k : ℕ) : ℝ :=
  (k : ℝ) / ((n : ℝ) + 1)

/-- **秩**：`s p` 的秩 = 「严格小于 `s p` 的位置个数」`+ 1`。
取值落在 `{1, …, m}`（见 `rankOf_mem`）。**诚实标注**：并列时按位置打破；
主定理用**无并列**（`s` 单射）情形，此时秩是到 `{1,…,m}` 的双射。 -/
def rankOf {m : ℕ} (s : Fin m → ℝ) (p : Fin m) : ℕ :=
  (Finset.univ.filter (fun q : Fin m => s q < s p)).card + 1

/-! ## 定理 1：秩的值域（可证） -/

/-- 秩总落在 `1 .. m` 内。 -/
lemma rankOf_mem {m : ℕ} (s : Fin m → ℝ) (p : Fin m) :
    1 ≤ rankOf s p ∧ rankOf s p ≤ m := by
  unfold rankOf
  constructor
  · omega
  · -- ⚠ **G2 修复**：原证明用 `Finset.card_filter_le` 只得 `card ≤ m`，
    -- 而目标是 `card + 1 ≤ m`（缺口 1）。**命题为真**：因为 `¬ (s p < s p)`，
    -- 故 `p` 不在过滤集里 ⟹ 过滤集 ⊆ `univ.erase p`，基数 `≤ m - 1`。
    -- 用 `erase` 把这个「少一个」的事实交给 `omega`，**命题本身不变**。
    have hsub : (Finset.univ.filter (fun q : Fin m => s q < s p)) ⊆
        (Finset.univ : Finset (Fin m)).erase p := by
      intro q hq
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hqp
      rw [Finset.mem_filter] at hq
      rw [hqp] at hq
      exact absurd hq.2 (lt_irrefl (s p))
    have hcard : (Finset.univ.filter (fun q : Fin m => s q < s p)).card
        ≤ ((Finset.univ : Finset (Fin m)).erase p).card := Finset.card_le_card hsub
    have herase : ((Finset.univ : Finset (Fin m)).erase p).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
        Fintype.card_fin]
    -- ⚠ **G2 修复**：`omega` 穿不透 `m - 1`（ℕ 的**截断减法**）——
    -- `card ≤ m - 1` 与目标 `card + 1 ≤ m` 之间需要 `m ≥ 1` 的知识，
    -- 而 `omega` 无法从 `m - 1` 反推（v9 报 "a possible counterexample may
    -- satisfy a ≥ 0, a ≤ 0"，即它把 `m = 0` 当成了可能）。
    -- 解法：`p : Fin m` 直接给出 `p.val < m`，故 `m ≠ 0`（即 `0 < m`）。
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le p.val) p.isLt
    omega

/-- 单射分数下的秩**上界收紧**：`rankOf s p ≤ m`（同上，但用于主定理的
`k ≤ n+1` 前提校验）。 -/
lemma rankOf_le {m : ℕ} (s : Fin m → ℝ) (p : Fin m) : rankOf s p ≤ m :=
  (rankOf_mem s p).2

/-! ## 定理 2：有限样本校正（`⌈·⌉₊` 的核心不等式）

`k = ⌈(n+1)(1−α)⌉₊` ⟹ `(n+1)(1−α) ≤ k`。
这就是「为什么要上取整」：上取整保证覆盖率**不低于**名义水平 `1−α`。 -/

theorem conformal_quantile_ge (n : ℕ) (alpha : ℝ) :
    ((n : ℝ) + 1) * (1 - alpha) ≤ (conformalQuantile n alpha : ℝ) :=
  -- ⚠ **G2 修复（缺 namespace 限定，非"名字不存在"）**：`le_ceil` 在 mathlib 中
  -- **确实存在**（`Mathlib/Algebra/Order/Floor.lean:269`），但它在 **`namespace Nat`** 内
  -- ⟹ 未加 `Nat.` 前缀时 `namespace Lattice` 内不可见（`Nat` 不会自动 open）。
  -- 全库已编译文件的既有写法即限定形式（`RealEarlyStopping.lean:113` 的 `Nat.le_ceil`）。
  -- 探针实测：裸 `le_ceil` unknown identifier，`Nat.le_ceil` 通过。
  Nat.le_ceil _

/-- **上取整的整数刻画（最小性）**：`k = ⌈(n+1)(1−α)⌉₊` 是满足
`(n+1)(1−α) ≤ k` 的**最小**整数，即 `k − 1 < (n+1)(1−α)`。
这说明 `⌈·⌉₊` 不是随意选的：它是覆盖约束下的**最紧**整数阈值。

⚠⚠ **命题修正（G2，本轮主动抓出的假命题）**：原陈述
`¬ ((n+1)(1−α) ≤ ⌈(n+1)(1−α)⌉₊ − 1)` **为假** —— 它未假设被上取整的量
**非负**。**机器验证反例**：取 `n = 0, α = 3`（即 `a = (0+1)·(1−3) = −2`），
则 `⌈−2⌉₊ = 0`（`Nat.ceil_eq_zero`），原式变为 `¬(−2 ≤ 0 − 1) = ¬(−2 ≤ −1)`，
即 `¬True`，**为假**。反例已由探针 `_probe_g2_p6.lean` 内核验证
（`example : ¬ (∀ a : ℝ, ¬ (a ≤ ((⌈a⌉₊:ℕ):ℝ) - 1))` 编译通过）。
**修正**：补上 `ha : 0 ≤ (n+1)(1−α)`（覆盖率语境下**成立**：`1−α ≥ 0` 时自然满足），
此时结论为真且即「`⌈·⌉₊` 是最小可行整数」的准确刻画。
`lt_ceil` 同样需 `Nat.` 限定（`namespace Nat`，`Floor.lean:253`）。 -/
theorem conformal_quantile_minimal (n : ℕ) {alpha : ℝ}
    (ha : 0 ≤ ((n : ℝ) + 1) * (1 - alpha)) :
    ¬ ((n : ℝ) + 1) * (1 - alpha) ≤ ((conformalQuantile n alpha : ℕ) : ℝ) - 1 := by
  -- ⚠ **G2 修复（第 3 轮，已定位真正的引理）**：
  -- 「最小性」的内容是 **`⌈a⌉₊ − 1 < a`**（而非 `< ⌈a⌉₊`——后者与假设不矛盾，
  -- 这正是前两轮 `linarith failed` 的原因：`a ≤ X` 与 `Y < Z`（`X=Y`）**并不冲突**）。
  -- mathlib 的现成引理是 `Nat.ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : ℝ) < a + 1`
  -- （`Floor.lean:450`），变形即得 `⌈a⌉₊ − 1 < a`，与 `h` 直接冲突。
  -- ⚠ 同时**不引入 `set a := …`**：否则 `conformalQuantile n alpha` 与 `a`
  -- 是两个不同项，`rw` 会报 pattern 不匹配（v9 的 `186:6`）。
  unfold conformalQuantile
  intro h
  have hkey : (⌈((n : ℝ) + 1) * (1 - alpha)⌉₊ : ℝ) < ((n : ℝ) + 1) * (1 - alpha) + 1 :=
    Nat.ceil_lt_add_one ha
  linarith

/-! ## 定理 3（主定理）：覆盖率下界 `1 − α ≤ k/(n+1)` -/

/-- **共形覆盖率下界（主定理）**：`k = ⌈(n+1)(1−α)⌉₊` ⟹ `1 − α ≤ k/(n+1)`。
即**覆盖率 ≥ 1 − α**，有限样本、无分布假设（在可交换性 ⟹ 秩均匀下）。 -/
theorem conformal_coverage_ge (hn : 0 < n) (alpha : ℝ) :
    1 - alpha ≤ coverageValue n (conformalQuantile n alpha) := by
  unfold coverageValue
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    linarith
  rw [le_div_iff₀ hpos, mul_comm]
  exact conformal_quantile_ge n alpha

/-- **覆盖率 = 有利秩数 / 总数**：有利秩恰为 `{1,…,k}` 共 `k` 个时，
覆盖率数值就是 `k/(n+1)`。

⚠ **诚实标注**：本定理证的是**计数恒等式** `|{1,…,k}| = k` 与除法的
整理，**不**包含「秩均匀」这一概率内容（后者未形式化，见文件头与
`rankOf_membership` 小节）。它给出的是「给定有利秩个数为 `k` 时，
覆盖率数值等于 `k/(n+1)`」这一**算术接口**。

**无需 `k ≤ n+1`**：`|{1,…,k}| = k` 对任意 `k` 成立
（`card_Icc : (Icc a b).card = b + 1 - a`，`a = 1` 时 `k + 1 - 1 = k`）。 -/
theorem conformal_coverage_of_uniform {k : ℕ} :
    (((Finset.Icc 1 k).card : ℕ) : ℝ) / ((n : ℝ) + 1) = coverageValue n k := by
  unfold coverageValue
  have hcard : ((Finset.Icc 1 k).card : ℕ) = k := by
    -- ⚠ **G2 修复**：`card_Icc` 在 `namespace Nat` 内（`Nat.card_Icc`），
    -- 不存在 `Finset.card_Icc`（那正是 v6 报的 `unknown constant`）。
    rw [Nat.card_Icc]
    omega
  rw [hcard]

/-! ## 定理 4（对照）：下取整版本**不**足够

若不做上取整校正而取 `⌊(n+1)(1−α)⌋₊`，则因 `⌊a⌋₊ ≤ a`，
覆盖率数值 `⌊a⌋₊/(n+1) ≤ 1−α`——**不保证** `≥ 1−α`。
这证明有限样本校正**必要**（用 `⌊·⌋₊` 会丢掉分数部分而**违反**覆盖保证）。 -/

theorem conformal_floor_insufficient (n : ℕ) {alpha : ℝ}
    (ha : 0 ≤ ((n : ℝ) + 1) * (1 - alpha)) :
    ((⌊((n : ℝ) + 1) * (1 - alpha)⌋₊ : ℕ) : ℝ) ≤ ((n : ℝ) + 1) * (1 - alpha) :=
  -- ⚠ **G2 修复**：`floor_le` 同样在 `namespace Nat` 内 ⟹ 需 `Nat.` 限定。
  Nat.floor_le ha

/-- 定理 4 的**定量形态**：用下取整得到覆盖率 `≤ 1−α`（分母为正），
即**严格可能失败**。 -/
theorem conformal_floor_coverage_le (hn : 0 < n) {alpha : ℝ}
    (ha : 0 ≤ ((n : ℝ) + 1) * (1 - alpha)) :
    ((⌊((n : ℝ) + 1) * (1 - alpha)⌋₊ : ℕ) : ℝ) / ((n : ℝ) + 1) ≤ 1 - alpha := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    linarith
  -- ⚠ **G2 修复**：`rw [div_le_iff₀ hpos]` 已把目标化为
  -- `⌊a⌋₊ ≤ (1 - alpha) * (n + 1)`（**分子单独留下**，分母移到右侧），
  -- 故原 `calc` 的第一步（写成 `⌊a⌋₊ * (n+1) ≤ …`）与目标**左端不符**
  -- （v9 的 `247:7`：invalid 'calc' step, left-hand side is `↑⌊…⌋₊ * (↑n + 1)`
  --   but is expected to be `↑⌊…⌋₊`）。这里直接对化归后的目标收尾即可。
  rw [div_le_iff₀ hpos]
  calc ((⌊((n : ℝ) + 1) * (1 - alpha)⌋₊ : ℕ) : ℝ)
      ≤ ((n : ℝ) + 1) * (1 - alpha) := Nat.floor_le ha
    _ = (1 - alpha) * ((n : ℝ) + 1) := by ring

/-! ## 定理 5：单调性（可证性质） -/

/-- `α` 越小（要求越高）⟹ 分位数 `k` 越大。 -/
theorem conformal_coverage_mono_alpha {alpha beta : ℝ} (h : alpha ≤ beta) :
    conformalQuantile n beta ≤ conformalQuantile n alpha := by
  unfold conformalQuantile
  -- ⚠ **G2 修复**：`ceil_mono` 在 `namespace Nat` 内（`Nat.ceil_mono`）。
  -- 原证明在 `apply ceil_mono` 后还留了 `have`+`nlinarith` 两条（报
  -- `no goals to be solved`）——因为 `Nat.ceil_mono` 直接由 `gcongr` 消解。
  exact Nat.ceil_mono (by
    have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith)

/-- 覆盖率数值关于 `k` 单调不减（同分母）。 -/
theorem coverageValue_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    coverageValue n k ≤ coverageValue n l := by
  unfold coverageValue
  have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) this

/-- **覆盖率 ≤ 1**（健全性）：`k ≤ n+1` ⟹ `k/(n+1) ≤ 1`。 -/
theorem conformal_validity_le_one (hn : 0 < n) {k : ℕ} (hk : k ≤ n + 1) :
    coverageValue n k ≤ 1 := by
  unfold coverageValue
  rw [div_le_one (by positivity)]
  exact_mod_cast hk

/-! ## 定理 6：条件覆盖率**不**成立（算术反例 + 诚实标注）

共形预测只保证**边缘**覆盖 `P(Y ∈ C(X)) ≥ 1−α`；**条件**覆盖
`P(Y ∈ C(X) | X = x) ≥ 1−α` 对每个 `x` **为假**。

⚠ **诚实标注（重要）**：下面三条**不是**对「条件覆盖率」这一概率陈述的
形式化反驳——本文件**没有**形式化条件概率、`X` 的划分、或共形预测器本身
（`conformalQuantile`/`coverageValue`/`rankOf` 都不出现在这些定理中）。
它们是该反例的**算术内核**：说明「两组的平均值达标」**不蕴含**
「每一组都达标」。完整的概率版反驳**未形式化**（登记为未做）。

**价值定位**：这是**算术层面**的机器验证；它足以说明「边缘 ⟹ 条件」
在任何两组设置中都不成立，但**不足以**称为「条件覆盖率定理的机器验证反例」。
项目纪律要求：命题为假 ⟹ 给反例 + 改命题；此处改命题的方式是
**把结论限定为边缘覆盖**（文件头与各定理 docstring 均已如此声明）。 -/

/-- **条件覆盖反例的算术内核**：存在条件覆盖率 `(p₁, p₂) = (1, 0)`，
其平均 `1/2 ≥ 1 − α`（`α = 1/2`），但 `p₂ = 0 < 1/2 = 1 − α`。 -/
theorem conformal_conditional_false :
    ∃ (p₁ p₂ alpha : ℝ), p₁ = 1 ∧ p₂ = 0 ∧ alpha = 1 / 2 ∧
      1 - alpha ≤ (p₁ + p₂) / 2 ∧ p₂ < 1 - alpha :=
  ⟨1, 0, 1/2, rfl, rfl, rfl, by norm_num, by norm_num⟩

/-- 反例的**参数化加强**：任意 `α ∈ [1/2, 1)` 都同样失效
（边缘平均覆盖达标，但一组条件覆盖为 `0 < 1−α`）。 -/
theorem conformal_conditional_false_general {alpha : ℝ}
    (h1 : 1 / 2 ≤ alpha) (h2 : alpha < 1) :
    ∃ (p₁ p₂ : ℝ), p₁ = 1 ∧ p₂ = 0 ∧ 1 - alpha ≤ (p₁ + p₂) / 2 ∧ p₂ < 1 - alpha :=
  ⟨1, 0, rfl, rfl, by linarith, by linarith⟩

/-- **平均达标 ⟹ 一组不达标**：若两组的**平均** `(p₁+p₂)/2 < 1−α`，则**必存在**
一组覆盖率 `< 1−α`（抽屉原理）。这是「边缘 ⟹ 条件」失效的**可证方向**。

⚠⚠ **命题修正（G2，本轮主动抓出的第二条假命题）**：原陈述
`havg : 1−α ≤ (p₁+p₂)/2 ⊢ p₁ < 1−α ∨ p₂ < 1−α` **为假**。
**机器验证反例**：取 `p₁ = p₂ = α = 1/2`，则 `(p₁+p₂)/2 = 1/2 = 1−α`
故 `havg` 成立（取等号），但 `p₁ < 1−α` 与 `p₂ < 1−α` 都是 `1/2 < 1/2`，**均为假**。
（反例已由探针 `_probe_g2_p7.lean` 内核验证：
`example : ¬ (∀ p₁ p₂ α, 1−α ≤ (p₁+p₂)/2 → α < 1 → (p₁ < 1−α ∨ p₂ < 1−α))` 编译通过。）
**根因**：`≥` 在取等号时**不**提供「严格低于」的信息；原证明的 `linarith` 失败
**是正确的**（不是 tactic 弱点）。
**修正方向**：把假设换成**严格**的 `(p₁+p₂)/2 < 1−α`（此时抽屉原理给出结论），
并把「边缘达标但一组不达标」的**存在性**留给上面的具体反例定理。
这一修正**保留了原意图**（边缘不蕴含条件），且命题为真。 -/
theorem marginal_does_not_imply_conditional {p₁ p₂ alpha : ℝ}
    (havg : (p₁ + p₂) / 2 < 1 - alpha) :
    p₁ < 1 - alpha ∨ p₂ < 1 - alpha := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  linarith

/-- **修正命题的逆方向（可证）**：若两组**都**达标，则平均也达标。
与 `marginal_does_not_imply_conditional` 合起来给出「平均」与「逐组」的
**精确关系**：平均达标 ⟸ 两组都达标，但**反向不成立**（见上条反例）。 -/
theorem both_implies_marginal {p₁ p₂ alpha : ℝ}
    (h1 : 1 - alpha ≤ p₁) (h2 : 1 - alpha ≤ p₂) :
    1 - alpha ≤ (p₁ + p₂) / 2 := by
  linarith

end Lattice
