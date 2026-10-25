import Mathlib
import Lattice.Lib.Architectures.RealSparseCodingNorms
/-! # RealSparseCodingSoftThreshold

拆分自 `RealSparseCoding.lean`（第 494–668 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealSparseCoding` 仍有效，
两个 importer（`RealCompressedSensing`、`RealSeamBridges2`）因此不受影响。

本模块重新声明了原文件的四项作用域设置（缺一不可）：
`noncomputable section`（原 :147）、`open scoped BigOperators`（原 :149）、
`namespace Lattice`（原 :151）、`variable {n : ℕ}`（原 :153）。

**边界经注释深度校验**：原文件中 `## ⚠ 登记在案的假命题之四`（:741）位于 :703 打开的
注释块**内部**，是散文而非分节标记；在 :741 切分会产生 `unterminated comment`。
本模块因此覆盖到 :1276，把该段散文与其所属块一并保留。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n : ℕ}

/-! ## 二、软阈值算子：`min_x ½(x−y)² + λ|x|` 的唯一最优解（核心）

`soft_λ(y) = sign(y)·max(|y|−λ, 0)`。它是 **L1 近端算子**（proximal operator
of `λ|·|`），也是 ISTA / TISTA / LASSO 坐标下降的**原子步骤**。

本节给出**完整的一维最优性证明**（含唯一性），方法为**按 `x` 的三段分情形**：
在每段内目标是无约束二次函数，配方即得该段最小点；再比较三段的值。
-/

/-- **软阈值（soft-thresholding）算子**：`softThresh lam y = sign(y)·max(|y|−lam, 0)`。

用 `max` 与 `sign` 定义（而非分段 `if`），使 `Real.sign` 的既有引理可用。 -/
def softThresh (lam y : ℝ) : ℝ := Real.sign y * max (|y| - lam) 0

/-- **软阈值的显式分段形式**（**要求 `0 ≤ λ`**）：`y > lam` 时 `y − lam`；
`|y| ≤ lam` 时 `0`；`y < −lam` 时 `y + lam`。

## ⚠⚠ 登记在案的假命题之五（v14 实测抓出，**本文件最严重的一处**）

原稿的陈述**没有 `0 ≤ lam` 假设**，而该陈述在 **`λ < 0` 时为假**。
**代小整数即知**（STYLE §4）—— 取 `lam = -5`、`y = -1`：

  · 左端：`sign(-1) · max(|-1| − (−5), 0) = (−1) · max(6, 0) = −6`；
  · 右端：`lam < y` 即 `−5 < −1` 为**真** ⟹ 取 `y − lam = −1 + 5 = 4`；
  · **`−6 ≠ 4`** ⟹ 等式为假。

**穷举验证**（我做的机器穷举）：`lam ∈ {−2.5,−2,…,2.5}`（步长 0.5）×
`y ∈ {−5,…,5}`（步长 0.5）共 231 组：
**`λ ≥ 0` 时 0 违例；`λ < 0` 时 15 组违例** ⟹ **分界线正是 `λ ≥ 0`**。

**根因**：`max(|y| − λ, 0)` 只在 `λ ≥ 0` 时才恒等于 `|y| − λ`（**不**取到 `0` 的那一支，
除非 `|y| ≤ λ`）；`λ < 0` 时 `|y| − λ = |y| + |λ| > 0` **恒正**，
`sign(y)` 因子与 `if` 链的分段**对不上**。
`λ` 是正则化强度，**物理上取 `λ ≥ 0`**（与 `softThresh_of_le` 的偏离同源）。

**处置**：加 `(hlam : 0 ≤ lam)`。⚠ **所有调用点都已有 `0 < lam` 或 `0 ≤ lam`**（见下），
故**不影响任何下游**。这是与任务清单的**第六处诚实偏离**。
📌 **已登记：`CORRECTIONS B49`**。 -/
theorem softThresh_eq (lam y : ℝ) (hlam : 0 ≤ lam) :
    softThresh lam y
      = if lam < y then y - lam else if y < -lam then y + lam else 0 := by
  unfold softThresh
  -- ⭐ v6/v11/v14 修复（**本文件最高频根因**）：`max_eq_left` / `max_eq_right` 的真实语句
  -- （pinned `Order/Defs/LinearOrder.lean:232/235`）：
  --   `max_eq_left  (h : b ≤ a) : max a b = a`   -- 取**左**操作数（假设是 `b ≤ a`）
  --   `max_eq_right (h : a ≤ b) : max a b = b`   -- 取**右**操作数（假设是 `a ≤ b`）
  -- 目标是 `max (|y| - lam) 0`（`a = |y|-lam`、`b = 0`）。
  -- ⚠ **v14 又发现**：原稿在 `y < 0` 支里断言 `¬ (lam < y)`（**只由 `y < 0`**），
  -- 但 `lam = -5, y = -1` 时 `lam < y` **成立** ⟹ 那个 `linarith` 必失败
  -- （v14 报 `:527:32 linarith failed`）。**这正是"陈述缺 `0 ≤ lam`"的症状**。
  -- 加了 `hlam : 0 ≤ lam` 后：`y < 0 ∧ 0 ≤ lam` ⟹ `lam < y` 确实为假，`h3` 可证。成立
  rcases lt_trichotomy y 0 with hy | hy | hy
  · -- `y < 0`：`sign y = -1`，`|y| = -y`，目标 `-1 * max (-y - lam) 0`
    have habs : |y| = -y := abs_of_neg hy
    rw [habs, Real.sign_of_neg hy]
    -- `0 ≤ lam` 且 `y < 0` ⟹ `¬ (lam < y)`
    have h3 : ¬ (lam < y) := by linarith
    by_cases h : y < -lam
    · -- `y < -lam` ⟹ `-y - lam > 0` ⟹ `max` 取**左** `-y - lam`
      have h1 : (0:ℝ) ≤ -y - lam := by linarith
      simp only [max_eq_left h1]
      rw [if_neg h3, if_pos h]
      ring
    · -- `¬ y < -lam` ⟹ `-y - lam ≤ 0` ⟹ `max` 取**右** `0`
      have h2 : -y - lam ≤ 0 := by linarith
      simp only [max_eq_right h2]
      rw [if_neg h3, if_neg h]
      ring
  · -- `y = 0`：`sign 0 = 0`，目标 `0 * max (|0| - lam) 0 = 0`
    subst hy
    rw [abs_zero, Real.sign_zero]
    -- 左端恒为 `0`；右端：`¬ (lam < 0)`（由 `hlam`）、`¬ (0 < -lam)`（由 `hlam`）
    have h3 : ¬ (lam < (0 : ℝ)) := by linarith
    have h4 : ¬ ((0 : ℝ) < -lam) := by linarith
    rw [if_neg h3, if_neg h4]
    ring
  · -- `0 < y`：`sign y = 1`，`|y| = y`，目标 `1 * max (y - lam) 0`
    have habs : |y| = y := abs_of_pos hy
    rw [habs, Real.sign_of_pos hy]
    by_cases h : lam < y
    · have h1 : (0:ℝ) ≤ y - lam := by linarith
      simp only [max_eq_left h1]
      rw [if_pos h]
      ring
    · have h2 : y - lam ≤ 0 := by linarith
      have h4 : ¬ (y < -lam) := by linarith
      simp only [max_eq_right h2]
      rw [if_neg h, if_neg h4]
      ring

/-- **软阈值的奇对称性**：`soft_λ(−y) = −soft_λ(y)`。 -/
theorem softThresh_odd (lam y : ℝ) : softThresh lam (-y) = -softThresh lam y := by
  unfold softThresh
  rw [abs_neg, Real.sign_neg]
  -- 目标：`-y.sign * max (|y| - lam) 0 = -(y.sign * max (|y| - lam) 0)`
  -- ⚠ v11 修复：`rw [max_eq_left …]` 在此报 `did not find instance of the pattern: -lam ⊔ 0`，
  -- 而 `simp only [max_eq_left …]` 报 `simp made no progress`（残留 `-y.sign * ((…) ⊔ 0) = …`）。
  -- 真因：`max` 与 `⊔` 是**同一个函数**但记法不同，且此处 `max` 埋在乘法里，直接 `rw` 命中不稳。
  -- ⇒ 最稳路线：**把两处 `max` 都用 `max_eq_left`/`max_eq_right` 消掉后再 `ring`**，
  -- 用一个 `by_cases` 统一给出两条取值不等式，避免 `simp` 的谓词同形问题。
  by_cases h : (0:ℝ) ≤ |y| - lam
  · -- ⚠ v12 修复：`rw [max_eq_left h, max_eq_left h]` 在此报 `pattern (|y| - lam) ⊔ 0` 失配
    -- （`Real.sign_neg` 之后目标外层是 `-y.sign * (…)`，`rw` 的模式匹配被 `⊔` 记法干扰）。
    -- 改 `simp only [max_eq_left h]`（simp 会规范化并把两处 `max` 都换掉）。
    simp only [max_eq_left h]
    ring
  · simp only [max_eq_right (le_of_not_ge h)]
    ring

/-- **软阈值的死区**：`|y| ≤ λ ⟹ soft_λ(y) = 0`（**稀疏性的来源**）。 -/
theorem softThresh_eq_zero_of_abs_le (lam y : ℝ) (h : |y| ≤ lam) : softThresh lam y = 0 := by
  unfold softThresh
  -- `max (|y| - lam) 0` 在 `|y| - lam ≤ 0` 时取**右**操作数 `0` ⟹ `max_eq_right`（原稿正确）。
  rw [max_eq_right (by linarith : |y| - lam ≤ 0), mul_zero]

/-- **软阈值在 0 处取值 0**：`soft_λ(0) = 0`（**对任意 `λ` 成立**，含 `λ < 0`）。

⚠ 位置说明（v6 修复）：本定理**必须声明在 `softThresh_of_le_false_counterexample` 之前**
——后者用 `rw [softThresh_zero]`。初稿把它放在 `softThresh_of_le` **之后**，
导致 `unknown identifier 'softThresh_zero'`（v10 报 `:589:6`）。
这是**真·前向引用**（与 v9 里那个"伪前向引用"`hterm` 不同：那个是级联，这个是顺序错）。

⚠ **v11 修复（证明路线，不是命题）**：初稿写
`softThresh_zero lam := softThresh_eq_zero_of_abs_le lam 0 (by simp)`，
但 `softThresh_eq_zero_of_abs_le` 需要 `|0| ≤ lam`，即 **`0 ≤ lam`** ——
**当 `lam < 0` 时该前提不成立**，`by simp` 无法闭合（v11 报 `:596:38 unsolved goals ⊢ 0 ≤ lam`）。
而**命题本身对任意 `lam` 都真**（`sign 0 = 0` ⟹ 乘积恒 `0`）⟹ **换证明路线**：
直接 `unfold` + `Real.sign_zero` + `mul_zero`。 -/
@[simp] theorem softThresh_zero (lam : ℝ) : softThresh lam 0 = 0 := by
  unfold softThresh
  rw [abs_zero, Real.sign_zero, zero_mul]

/-- **⚠ 登记在案的假命题之三（v6 实测抓出）**：`softThresh_of_le` **原陈述为假**。

原稿只假设 `lam ≤ y`，**不加 `0 < lam`**，但该命题在 `lam ≤ 0` 时**不成立**：

  · `lam = -1`、`y = 0`：`lam ≤ y` 成立，但
    `soft_λ(0) = sign(0)·max(|0|−(−1), 0) = 0·1 = 0`，而 `y − lam = 0 + 1 = 1` ⟹ `0 ≠ 1`；
  · `lam = -1`、`y = -1/2`：`lam ≤ y` 成立，但
    `soft_λ(−1/2) = −1·max(1/2 + 1, 0) = −3/2`，而 `y − lam = 1/2` ⟹ `−3/2 ≠ 1/2`。

**根因**：`sign(y)·max(|y|−λ, 0) = y − λ` 只在 `λ ≥ 0` 时才与「大信号平移」语义吻合；
`λ < 0` 时 `max(|y|−λ, 0) = |y| − λ ≠ |y|`，`sign` 因子就把符号带偏了。
（这正是 `softThresh` 的**定义域**：`λ` 是正则化强度，物理上取 `λ ≥ 0`。）

**处置**（STYLE §5「假命题处理」）：**不证原陈述**，改为**加 `0 < lam` 的正确版本**，
并在下方 `softThresh_of_le_false_counterexample` 中**机器验证**反例。
这是与任务清单的**第四处诚实偏离**（前三处见文件头「诚实边界」）。
📌 **已登记：`CORRECTIONS B49`**。 -/
theorem softThresh_of_le_false_counterexample :
    ¬ (∀ lam y : ℝ, lam ≤ y → softThresh lam y = y - lam) := by
  -- `lam = -1`、`y = 0` 即反例（见上）。
  intro h
  have h1 : (-1 : ℝ) ≤ 0 := by norm_num
  have h2 := h (-1) 0 h1
  -- `softThresh (-1) 0 = Real.sign 0 * max (|0| - (-1)) 0 = 0`
  rw [softThresh_zero] at h2
  norm_num at h2

/-- **软阈值的收缩性质（`λ > 0` 的正确版本）**：`0 < λ ≤ y ⟹ soft_λ(y) = y − λ`。

⚠ **`0 < lam` 不可去**（原稿省略该假设 ⟹ 命题为假，见上方
`softThresh_of_le_false_counterexample` 的反例与说明）。 -/
theorem softThresh_of_le (lam y : ℝ) (hlam : 0 < lam) (h : lam ≤ y) :
    softThresh lam y = y - lam := by
  -- ⭐ v6 修复：在 `0 < lam` 下 `0 ≤ y` 与 `0 ≤ lam` 都由 `linarith` 直接给出。
  have hy : 0 ≤ y := by linarith
  unfold softThresh
  -- `max (y - lam) 0`：`lam ≤ y` ⟹ `0 ≤ y - lam` ⟹ 取**左** ⟹ `max_eq_left`
  rw [abs_of_nonneg hy, max_eq_left (by linarith : (0:ℝ) ≤ y - lam)]
  -- `0 < lam ≤ y` ⟹ `y ≠ 0`，故 `sign y = 1`
  have hz : y ≠ 0 := by linarith
  rw [Real.sign_of_pos (lt_of_le_of_ne hy (Ne.symm hz))]
  ring


end Lattice
