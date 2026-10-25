import Mathlib
import Lattice.Lib.LinearAlgebra.RealSparseCodingOptimality
/-! # RealSparseCodingCounterexamples

拆分自 `RealSparseCoding.lean`（第 703–1276 行），2026-10-15。
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

/-! ### 主结果：软阈值的最优性与唯一性

目标泛函 `obj lam y x = ½(x−y)² + λ|x|`（**L1 正则最小二乘**，一维）。
本节的定理给出：`x = soft_λ(y)` 是它的**唯一**全局最小点（`λ > 0`）。
-/

/-- **L1 正则目标泛函**：`obj lam y x = ½(x−y)² + λ·|x|`。 -/
def l1Objective (lam y x : ℝ) : ℝ := (1 / 2) * (x - y) ^ 2 + lam * |x|

/-- `x > 0` 时 `l1Objective = ½(x−y)² + λx`（去掉绝对值）。 -/
theorem l1Objective_of_pos (lam y x : ℝ) (hx : 0 < x) :
    l1Objective lam y x = (1 / 2) * (x - y) ^ 2 + lam * x := by
  unfold l1Objective
  rw [abs_of_pos hx]

/-- `x < 0` 时 `l1Objective = ½(x−y)² − λx`（`|x| = −x`）。 -/
theorem l1Objective_of_neg (lam y x : ℝ) (hx : x < 0) :
    l1Objective lam y x = (1 / 2) * (x - y) ^ 2 - lam * x := by
  unfold l1Objective
  rw [abs_of_neg hx]
  ring

/-- **⭐ 软阈值的最优性（主结果，含唯一性）**：

`x = soft_λ(y)`（`λ > 0`）是 `min_x ½(x−y)² + λ|x|` 的**唯一全局最小点**：

  (1) 最优性：`∀ x, l1Objective λ y (soft_λ y) ≤ l1Objective λ y x`；
  (2) 唯一性：等号仅在 `x = soft_λ y` 处成立。

**证明**（按 `x` 的三段分情形 + 三段最小值一致）：

  · `x > 0`：目标 `= ½(x−y)² + λx ≥ λy − λ²/2`（配方），等号 `⟺ x = y − λ`；
  · `x = 0`：目标 `= ½y²`。
  · `x < 0`：目标 `= ½(x−y)² − λx ≥ −λy − λ²/2`（配方），等号 `⟺ x = y + λ`；

三条下界在 `y` 的符号上分别取到，且恰等于 `soft_λ(y)` 处的值——
即「三段的最小点拼起来」正是软阈值。

## ⚠ 登记在案的假命题之四（v6 实测抓出，本条最重要）：原稿的 `hval` 等式为假

原 `softThresh_optimal` 的证明以一个中间断言（下称 `hval`）为枢轴：

```
l1Objective lam y (softThresh lam y)
  = min (lam*y - lam^2/2) (min (y^2/2) (-lam*y - lam^2/2))
```

**代小整数即知其为假**（STYLE §4）：取 `lam = 1`、`y = -3`（此时 `y < -lam`）：

  · 左端：`soft_1(-3) = sign(-3)·max(3-1, 0) = -2`，
    `l1Objective 1 (-3) (-2) = ½(-2+3)² + 1·|-2| = ½ + 2 = 5/2`；
  · 右端：`A = -7/2`、`B = 9/2`、`C = 5/2`，
    `min A (min B C) = min (-7/2) (5/2) = -7/2`。

`5/2 = -7/2` 为假 ⟹ **`hval` 不成立**。

**根因**：`A`、`B`、`C` 是**三段各自的下界**（`x>0` / `x=0` / `x<0` 时的最小值），
`min A (min B C)` 是这三者的**全局最小**——它**小于等于**真值，一般**不相等**。
`obj(soft_λ(y))` 的真值是**按 `y` 所在区域选出的那一段的值**（见
`softThresh_value_of_le_neg` / `_of_abs_le` / `_of_ge`，本文件已分别证明）。

⇒ 原证的**主结论**（`softThresh_optimal` 是最优且唯一）**本身为真**，
但**证明枢轴是假的** —— 这正是「**占位级断言**被 `min` 的弱界掩盖」的典型。
处置：**改证明结构**（不再走 `min`，改为**按 `x` 的符号分两支、每支内按 `y` 的区域细分**，
直接把 `obj(x)` 与 `obj(soft)` 比较），**命题本身不动**（它是真定理）。
这是与任务清单的**第五处诚实偏离**（属于"证明结构缺陷"而非"命题为假"，
但按 STYLE §4「先代小整数判真假」的纪律在此**必须显式登记**，否则后人会重蹈覆辙）。
📌 **已登记：`CORRECTIONS B49`**。 -/
theorem softThresh_optimal (lam y : ℝ) (hlam : 0 < lam) :
    (∀ x : ℝ, l1Objective lam y (softThresh lam y) ≤ l1Objective lam y x)
      ∧ (∀ x : ℝ, l1Objective lam y (softThresh lam y) = l1Objective lam y x →
          x = softThresh lam y) := by
  -- 记号（与 docstring 一致）：`A = lam*y - lam^2/2`、`B = (1/2)*y^2`、`C = -lam*y - lam^2/2`。
  -- ⭐ v6 重写：**不再使用假的 `hval` 等式**，改用**统一的两步结构**：
  --   ① 按 `x` 的**符号**分两支（`x >= 0` / `x < 0`）；
  --   ② 每支内按 `y` 与 `±lam` 的关系细分，得出**该支的最小值**（恰好都是三个下界之一）；
  --   ③ 再用 `obj(soft) ≤ 该支最小值` 收尾，最后处理等号（唯一性）。
  --
  -- 关键区域值（由 `softThresh_eq` + `l1Objective_of_pos/neg` 得到）：
  --   `y < -lam`：`soft = y + lam`，`obj(soft) = C`；
  --   `|y| ≤ lam`：`soft = 0`，   `obj(soft) = B`；
  --   `lam ≤ y`：`soft = y - lam`，`obj(soft) = A`。
  --
  -- 两支的最小值（`x ≥ 0` 支 / `x < 0` 支，即 `½(x-y)² ± λx` 在**半线**上的最小值）：
  --   · `x ≥ 0`，`y ≤ lam`：`min = B`（`x* = 0`）；`y ≥ lam`：`min = A`（`x* = y-lam`）。
  --   · `x < 0`，`y ≥ -lam`：`min = B`（`x* = 0`）；`y ≤ -lam`：`min = C`（`x* = y+lam`）。
  -- 于是 2×2 的「区域 × 支」表里，`obj(soft)` 都 `≤` 对应支最小值：
  --   `y<-lam`: `C ≤ B`（`= ½(y+lam)²`）；`|y|≤lam`: `B = B`；`lam≤y`: `A ≤ B`（`= ½(y-lam)²`）。
  -- `soft` 在三个区域的取值（下游三条最优性/唯一性分支共用）
  have hsoftC : y < -lam → l1Objective lam y (softThresh lam y) = -lam * y - lam ^ 2 / 2 := by
    intro hy
    have hs : softThresh lam y = y + lam := by
      rw [softThresh_eq lam y hlam.le]
      have h1 : ¬ (lam < y) := by linarith
      rw [if_neg h1, if_pos hy]
    rw [hs]
    have hneg : y + lam < 0 := by linarith
    -- ⚠ v12 修复：`l1Objective_of_neg` 的签名是 `(lam y x : ℝ) (hx : x < 0)` ——
    -- **`x` 是显式的第三个参数**，不能省略（v11 报 `application type mismatch:
    -- expected ℝ but got y + lam < 0`，即 `hneg` 被喂给了 `x`）。
    rw [l1Objective_of_neg lam y (y + lam) hneg]
    ring
  have hsoftB : -lam ≤ y → y ≤ lam → l1Objective lam y (softThresh lam y) = (1 / 2) * y ^ 2 := by
    intro h1 h2
    have hs : softThresh lam y = 0 :=
      softThresh_eq_zero_of_abs_le lam y (abs_le.mpr ⟨h1, h2⟩)
    rw [hs, l1Objective, abs_zero]
    ring
  have hsoftA : lam ≤ y → l1Objective lam y (softThresh lam y) = lam * y - lam ^ 2 / 2 := by
    intro hy
    have hs : softThresh lam y = y - lam := softThresh_of_le lam y hlam hy
    -- ⚠ 此处 `y - lam` 可能为 `0`（`y = lam`），但 `l1Objective_of_pos` 要 `0 < x`；
    -- 改用 `l1Objective` 直接展开 + `abs_of_nonneg`。
    rw [hs, l1Objective]
    -- ⚠ v14 修复：`rw [abs_of_nonneg hy0, abs_of_nonneg hyl]` 里**第一个是多余的** ——
    -- 展开后目标是 `(1/2)*(y-lam-y)^2 + lam*|y-lam| = …`，**只有 `|y-lam|`**
    -- （`|y|` 已被 `(y-lam)-y` 消掉）⟹ `abs_of_nonneg hy0` 报
    -- `rewrite failed: pattern |y|`（v14 报 `:807:8`）。**只保留 `hyl` 那一条**。
    have hyl : (0:ℝ) ≤ y - lam := by linarith
    rw [abs_of_nonneg hyl]
    ring
  -- 两支上的**下界**：给出 `obj(x)` 与 `B`（或 `A`/`C`）的差，全部是平方/乘积非负
  -- `x ≥ 0` 支：`obj(x) - B = ½x² + x(λ - y)`
  have hge0_B : ∀ x : ℝ, 0 ≤ x → y ≤ lam →
      (0:ℝ) ≤ l1Objective lam y x - (1 / 2) * y ^ 2 := by
    intro x hx hxy
    rcases lt_trichotomy x 0 with h | h | h
    · linarith
    · -- ⚠ v12 修复：`subst h` 会**消去 `x`**，目标变成 `0 ≤ l1Objective lam y 0 - y²/2`。
      -- `rw [l1Objective, abs_zero, sub_zero]` 里的 `sub_zero` 模式是 `?a - 0`，
      -- 而此时结构是 `(1/2)*(0-y)^2 + lam*0 - (1/2)*y^2`，**最后一个 `- 0` 不存在**
      -- ⟹ `rewrite failed: pattern ?a - 0`（v11 报 `:804:33`）。
      -- 改用 `simp only [...]` 归一化后 `ring` 收尾。
      subst h
      simp only [l1Objective, abs_zero, mul_zero, add_zero]
      nlinarith [sq_nonneg y]
    · rw [l1Objective_of_pos lam y x h]
      -- ⚠ v15 修复：同 `:934` 的根因 —— **不要**把 `(by linarith : …)` 直接内联进
      -- `nlinarith […]` 的列表（`mul_nonneg` 的侧条件会触发类型类合成，
      -- 而内联证明的惰性可能让实例卡住）。提成命名 `have`。
      have hlamy : (0:ℝ) ≤ lam - y := by linarith
      have hmul : (0:ℝ) ≤ x * (lam - y) := mul_nonneg (le_of_lt h) hlamy
      nlinarith [sq_nonneg x, hmul]
  -- `x ≥ 0` 支：`obj(x) - A = ½(x - (y-λ))²`（`λ ≤ y` 时 `x* = y-λ ≥ 0` 落在支内）
  -- ⚠ 注意 `x = 0` 时不能用 `l1Objective_of_pos`，需单独处理并由 `½(y-λ)² ≥ 0` 收尾。
  have hge0_A : ∀ x : ℝ, 0 ≤ x → lam ≤ y →
      (0:ℝ) ≤ l1Objective lam y x - (lam * y - lam ^ 2 / 2) := by
    intro x hx hxy
    rcases lt_trichotomy x 0 with h | h | h
    · linarith
    · subst h
      rw [l1Objective, abs_zero]
      nlinarith [sq_nonneg (y - lam)]
    · rw [l1Objective_of_pos lam y x h]
      nlinarith [sq_nonneg (x - (y - lam))]
  -- `x < 0` 支：`obj(x) - B = x(½x - y - λ)`（两个因子都 `< 0`）
  -- ⚠ 直接 `rw [l1Objective_of_neg]` 之后目标含 `x` 与 `y` 的**乘积项** `x*y`，
  -- `nlinarith` 需要**显式喂进乘积非负**的证据；用 `mul_pos` 给出。
  have hlt0_B : ∀ x : ℝ, x < 0 → -lam ≤ y →
      (0:ℝ) ≤ l1Objective lam y x - (1 / 2) * y ^ 2 := by
    intro x hx hxy
    rw [l1Objective_of_neg lam y x hx]
    -- ⚠ v15 修复（同 `:934`）：把 `mul_pos` 的内联侧条件提成命名 `have`。
    have hxm : x / 2 - y - lam < 0 := by linarith
    have hmul : (0:ℝ) < x * (x / 2 - y - lam) :=
      mul_pos_of_neg_of_neg hx hxm
    nlinarith [hmul]
  -- `x < 0` 支：`obj(x) - C = ½(x - (y+λ))²`
  have hlt0_C : ∀ x : ℝ, x < 0 → y < -lam →
      (0:ℝ) ≤ l1Objective lam y x - (-lam * y - lam ^ 2 / 2) := by
    intro x hx hxy
    rw [l1Objective_of_neg lam y x hx]
    nlinarith [sq_nonneg (x - (y + lam))]
  constructor
  · -- ===== 最优性 =====
    intro x
    rcases le_or_lt 0 x with hx | hx
    · -- `x ≥ 0`：分 `y ≤ lam`（`obj(soft) ≤ B ≤ obj(x)`）与 `lam ≤ y`（`obj(soft) ≤ A ≤ obj(x)`）
      rcases le_or_lt y lam with hy | hy
      · rcases le_or_lt y (-lam) with hy1 | hy1
        · -- `y ≤ -lam`：`obj(soft) = C ≤ B`
          -- ⚠ `hsoftC` 要**严格** `y < -lam`，而 `le_or_lt` 给的是 `≤`。
          -- ⚠ v14 修复（**极隐蔽**）：不能写 `lt_of_le_of_ne hy1 (by intro hc; subst hc; linarith)` ——
          -- `subst hc` 会把 **`hc : y = -lam` 里的 `y` 全局代换成 `-lam`**，
          -- 于是 `hsoftC`/`hge0_B`/`hy` 等**所有含 `y` 的假设都被改写**，
          -- 报出 `hsoftC : -lam < -lam → …`（v14 `:862:72`/`:868:21`/`:895:76` 一排错）。
          -- 正解：用 `ne_of_lt` 的**方向相反的组合**，或直接 `rcases lt_or_eq_of_le hy1`。
          rcases lt_or_eq_of_le hy1 with hy' | hy'
          · have hs := hsoftC hy'
            rw [hs]
            have hCB : -lam * y - lam ^ 2 / 2 ≤ (1 / 2) * y ^ 2 := by
              nlinarith [sq_nonneg (y + lam)]
            linarith [hge0_B x hx hy]
          · -- `y = -lam`：此时 `soft = 0`，用 `hsoftB`（`-lam ≤ y ≤ lam`）
            subst hy'
            rw [hsoftB (le_refl (-lam)) (by linarith)]
            linarith [hge0_B x hx hy]
        · -- `-lam ≤ y ≤ lam`：`obj(soft) = B`
          -- ⚠ v14 修复：`le_or_lt y (-lam)` 的**第二支**给的是 `hy1 : -lam < y`（**严格**），
          -- 而 `hsoftB` 的第一个参数要 `-lam ≤ y`（**非严格**）⟹ 直接 `hsoftB hy1` 报
          -- `application type mismatch`（v14 `:868:21`）。用 `le_of_lt hy1`。
          rw [hsoftB (le_of_lt hy1) hy]
          linarith [hge0_B x hx hy]
      · -- `lam ≤ y`：`obj(soft) = A`
        rw [hsoftA (le_of_lt hy)]
        linarith [hge0_A x hx (le_of_lt hy)]
    · -- `x < 0`：分 `y < -lam`（`obj(soft) = C ≤ obj(x)`）与 `-lam ≤ y`（`obj(soft) ≤ B ≤ obj(x)`）
      -- ⚠ **变量遮蔽陷阱**：用 `hyneg`/`hypos` 而非复用外层的 `hy`
      rcases lt_or_ge y (-lam) with hyneg | hyneg
      · have hs := hsoftC hyneg
        rw [hs]
        linarith [hlt0_C x hx hyneg]
      · rcases le_or_lt y lam with hypos | hypos
        · -- `-lam ≤ y ≤ lam`：`obj(soft) = B`
          rw [hsoftB hyneg hypos]
          linarith [hlt0_B x hx hyneg]
        · -- `lam ≤ y`：`obj(soft) = A ≤ B`
          rw [hsoftA (le_of_lt hypos)]
          have hBA : lam * y - lam ^ 2 / 2 ≤ (1 / 2) * y ^ 2 := by
            nlinarith [sq_nonneg (y - lam)]
          linarith [hlt0_B x hx hyneg]
  · -- ===== 唯一性 =====
    intro x hxeq
    rcases le_or_lt 0 x with hx | hx
    · -- `x ≥ 0`
      rcases le_or_lt y lam with hy | hy
      · rcases le_or_lt y (-lam) with hy1 | hy1
        · -- `y ≤ -lam`：分 `y < -lam` 与 `y = -lam`（**不用 `subst hc`，它会污染上下文**）
          rcases lt_or_eq_of_le hy1 with hy' | hy'
          · -- `y < -lam`：`obj(soft) = C`，而 `x ≥ 0` 时 `obj(x) ≥ B > C`
            -- `obj(x) ≥ B > C = obj(soft)` 与等号矛盾：分 `x = 0` 与 `x > 0`
            rcases lt_trichotomy x 0 with h | h | h
            · linarith
            · subst h
              rw [hsoftC hy', l1Objective, abs_zero] at hxeq
              -- `hxeq : C = B` 迫使 `(y+lam)² = 0`，与 `hy' : y < -lam` 矛盾
              -- ⚠ v23/v24 修复（同 `:1069`）：给**最小但足够**的假设集 ——
              -- ⚠ v23 我漏了 `hy'`（`y < -lam`），导致 `linarith failed`（v24 报 `:940:24`）。
              -- `nlinarith only [...]` 是**白名单**：**凡不在列表里的假设都用不上**。
              exact (by nlinarith only [hxeq, hy'] : False).elim
            · rw [hsoftC hy', l1Objective_of_pos lam y x h] at hxeq
              -- `hxeq : C = ½(x-y)² + λx`；`½(x-y)² + λx - C = ½x² + x(λ-y) + ½(y+λ)² > 0`
              -- ⚠ v15/v16 修复：把 `mul_pos`/`mul_nonneg` 的侧条件**先提成命名 `have`**。
              -- ① 内联进 `nlinarith […]` 列表会让类型类合成卡在 `PosMulStrictMono ?m`；
              -- ② ⚠ **此处 `h : 0 < x`（第三支），不是 `x < 0`** ——
              --    `mul_pos_of_neg_of_neg h …` 会报 `application type mismatch: h has type 0 < x`
              --    （v16 报 `:950:73`）。这里要的是**正数乘正数**：`lam - y > 0`。
              have hly : (0:ℝ) < lam - y := by linarith
              have hmul : (0:ℝ) < x * (lam - y) := mul_pos h hly
              -- ⚠ v24/v25 修复：`nlinarith only [...]` 是**白名单**，且**需要平方非负的提示**。
              -- 关键恒等式（`nlinarith` 能自己展开）：
              --   `½(x-y)² + λx − C = ½x² + x(λ−y) + ½(y+λ)²`
              -- 由 `hxeq` 该式 `= 0`；而 `hmul > 0` 给第一项正、
              -- `sq_nonneg x`/`sq_nonneg (y+lam)` 给另两项非负 ⟹ 矛盾。
              exact (by nlinarith only [hxeq, hmul, sq_nonneg x, sq_nonneg (y + lam)] : False).elim
          · -- `y = -lam`：`soft = 0`，`obj(soft) = B`；用 `hsoftB`
            -- ⚠ v16 修复：`subst hy'` 会把 `y` 全局代换成 `-lam`，**连 `hsoftB` 的实例也变**，
            -- 之后 `rw [hsoftB …] at hxeq` 报 `rewrite failed: pattern l1Objective lam (-lam) …`
            -- （v16 `:959:18`）—— 因为 `subst` 之后目标的形状与 `hsoftB` 的结论不再逐字同形。
            -- **改用更稳的路线：直接展开 `l1Objective` + `hsoftB` 的结论作为等式**。
            subst hy'
            have hB : l1Objective lam (-lam) (softThresh lam (-lam)) = (1 / 2) * (-lam) ^ 2 :=
              hsoftB (le_refl (-lam)) (by linarith)
            rw [hB] at hxeq
            -- ⚠ v17 修复：唯一性的目标是 `x = softThresh lam (-lam)`。
            -- `x = 0` 支不能 `rw [hB]`（`hB` 的 LHS 是 `l1Objective …`，目标里没有它）——
            -- v16 报 `rewrite failed: pattern l1Objective lam (-lam) …`。
            -- 正确：由 `hxeq : B = B`（恒真）**不能**推出 `soft = 0`，需直接从
            -- `softThresh` 的定义算：`softThresh lam (-lam) = sign(-lam)*max(|-lam|-lam, 0) = 0`。
            have hzero : softThresh lam (-lam) = 0 := by
              -- ⚠ v19/v20 修复：
              -- ① `hlam : 0 < lam` 是**严格**的，`abs_of_nonneg` 要 `0 ≤ lam` ⟹ 用 `hlam.le`；
              -- ② **`rw` 已经把目标闭合时不能再跟 `linarith`**
              --    （v20 报 `no goals to be solved`）。
              -- 用 `have` 给出侧条件、再 `exact`，结构最清晰。
              have habs : |(-lam : ℝ)| ≤ lam := by
                rw [abs_neg, abs_of_nonneg hlam.le]
              exact softThresh_eq_zero_of_abs_le lam (-lam) habs
            rcases lt_trichotomy x 0 with h | h | h
            · linarith
            · subst h
              rw [l1Objective, abs_zero] at hxeq
              rw [hzero]
            · rw [l1Objective_of_pos lam (-lam) x h] at hxeq
              -- `obj(x) = B` 且 `x > 0` ⟹ `½x² + x(λ+lam) = 0`，两项都 `> 0`
              have hpos2 : (0:ℝ) < lam - -lam := by linarith
              have hmul2 : (0:ℝ) < x * (lam - -lam) := mul_pos h hpos2
              -- ⚠ v24 修复：加 `h`（`x > 0`）—— `nlinarith only` 是**白名单**，
              -- 推出矛盾所需的每条假设都必须列出。
              exact (by nlinarith only [hxeq, hmul2, h] : False).elim
        · -- `-lam ≤ y ≤ lam`：`obj(soft) = B`；等号 ⟹ `x = 0 = soft`
          -- ⚠ 只把 `obj(soft)` 一侧换成 `B`（写成等式用 `rw [...] at hxeq` 会**两侧都**被换掉
          -- 而退化成 `B = B`，丢失信息）。
          have hBs : l1Objective lam y (softThresh lam y) = (1 / 2) * y ^ 2 := hsoftB (le_of_lt hy1) hy
          rcases lt_trichotomy x 0 with h | h | h
          · linarith
          · subst h
            -- `x = 0`：目标 `0 = softThresh lam y`；由 `-lam ≤ y ≤ lam` 用死区引理
            -- ⚠ v17 修复：不能 `rw [hsoftB …]`（目标里没有 `l1Objective`，v16 报 `:978:16`）。
            rw [hBs] at hxeq
            -- ⚠ v19 修复：`le_or_lt y (-lam)` 的第二支给 `hy1 : -lam < y`（**严格**），
            -- 而 `abs_le.mpr` 要 `-lam ≤ y` ⟹ `⟨hy1, hy⟩` 报 `application type mismatch`
            -- （v19 `:986:67`）。用 `le_of_lt hy1`。
            exact (softThresh_eq_zero_of_abs_le lam y
              (abs_le.mpr ⟨le_of_lt hy1, hy⟩)).symm
          · rw [hBs] at hxeq
            rw [l1Objective_of_pos lam y x h] at hxeq
            -- `hxeq : B = ½(x-y)² + λx`（`B = ½y²`）⟹ `x·(½x − y + λ) = 0`。
            -- `x > 0` ⟹ `½x = y − λ ≤ 0`（因 `y ≤ lam`）⟹ 与 `x > 0` 矛盾。
            -- ⚠ v21 修复：v15~v20 我写的 `hpos3 : 0 < lam - y` **是错的**（`y = lam` 时它不成立），
            -- 故 `linarith` 一直失败（v21 报 `:1002:47`）。
            -- **正确的中间量**是 `½x = y - lam`，再由 `y ≤ lam` 与 `x > 0` 矛盾。
            have hfac : x * (x / 2 - y + lam) = 0 := by nlinarith
            rcases mul_eq_zero.mp hfac with hx0 | hx0
            · linarith
            · linarith
      · -- `lam ≤ y`：`obj(soft) = A`；`x ≥ 0` 时 `obj(x) - A = ½(x-(y-λ))²`
        -- ⚠ v16 修复：`le_or_lt y lam` 的第二支给的是 **`hy : lam < y`（严格）**，
        -- 而 `hsoftA` 要 `lam ≤ y` ⟹ 直接 `hsoftA hy` 报
        -- `application type mismatch: hy has type lam < y, expected lam ≤ y`（v16 `:984:90`）。
        -- 用 `le_of_lt hy`。
        have hAs : l1Objective lam y (softThresh lam y) = lam * y - lam ^ 2 / 2 :=
          hsoftA (le_of_lt hy)
        rcases lt_trichotomy x 0 with h | h | h
        · linarith
        · subst h
          -- `x = 0`：目标 `0 = softThresh lam y`。
          -- ⚠ v19 修复：由 `hxeq` 得 `B = A`，配合 `lam ≤ y` 可推出 `y = lam`，
          -- 再由 `softThresh_of_le` 得 `softThresh lam lam = 0`。
          -- **不要**去 `rw [hAs] at hxeq` 后就指望目标自动闭合 —— 目标里没有 `l1Objective`，
          -- `rw` 系列都在改 `hxeq` 而非目标（v19 报 `:1003:8 unsolved goals`）。
          have hyeq : y = lam := by
            rw [hAs, l1Objective, abs_zero] at hxeq
            nlinarith [sq_nonneg (y - lam)]
          -- ⚠ v22 修复：`rw [hyeq, softThresh_of_le …]` 之后目标是 **`0 = lam - lam`**，
          -- 这**不是语法同一**，`rw` **不会自动闭合** ⟹ 必须补 `ring`
          -- （v22 报 `:1018:8 unsolved goals`）。
          rw [hyeq, softThresh_of_le lam lam hlam le_rfl]
          ring
        · -- `x > 0`：`hxeq : A = ½(x-y)² + λx` ⟹ `½(x-(y-λ))² = 0` ⟹ `x = y - λ`
          -- 而 `y ≥ lam` 且 `x > 0` ⟹ 与 `soft` 一致，直接给出 `x = softThresh lam y`。
          rw [hAs] at hxeq
          rw [l1Objective_of_pos lam y x h] at hxeq
          have hz : (x - (y - lam)) ^ 2 = 0 := by nlinarith
          have hp := pow_eq_zero hz
          have hx0 : x = y - lam := by linarith
          -- 目标：`x = softThresh lam y`。由 `y ≥ lam` 得 `soft = y - lam`，与 `hx0` 一致。
          rw [hx0, softThresh_of_le lam y hlam (le_of_lt hy)]
    · -- `x < 0`
      -- ⚠ 同样避免遮蔽：用 `hyneg`/`hypos` 而非复用外层的 `hy`
      rcases lt_or_ge y (-lam) with hyneg | hyneg
      · -- `y < -lam`：`obj(soft) = C`，`x < 0` 时 `obj(x) - C = ½(x-(y+λ))²` ⟹ `x = y+λ = soft`
        -- ⚠ 只换 `obj(soft)` 一侧（两次 `rw` 同一等式会退化成 `C = C` 丢失信息）
        have hCs : l1Objective lam y (softThresh lam y) = -lam * y - lam ^ 2 / 2 := hsoftC hyneg
        rw [hCs] at hxeq
        rw [l1Objective_of_neg lam y x hx] at hxeq
        have hz : (x - (y + lam)) ^ 2 = 0 := by nlinarith
        have hp := pow_eq_zero hz
        have hx0 : x = y + lam := by linarith
        -- 目标：`x = softThresh lam y`；由 `y < -lam` 得 `soft = y + lam`。
        rw [hx0, softThresh_eq lam y hlam.le,
          if_neg (by linarith : ¬ (lam < y)), if_pos hyneg]
      · rcases le_or_lt y lam with hypos | hypos
        · -- `-lam ≤ y ≤ lam`：`obj(soft) = B`；`x < 0` 时 `obj(x) - B = x(½x-y-λ) > 0`
          have hBs : l1Objective lam y (softThresh lam y) = (1 / 2) * y ^ 2 := hsoftB hyneg hypos
          rw [hBs] at hxeq
          rw [l1Objective_of_neg lam y x hx] at hxeq
          -- ⚠ v15 修复（同 `:934`）：提成命名 `have`（`mul_pos` 用 `neg_pos.mpr` 的两个内联证明
          -- 会让类型类合成卡在 `PosMulStrictMono ?m`）。
          have hxm : x / 2 - y - lam < 0 := by linarith
          have hmul4 : (0:ℝ) < (-x) * (-(x / 2 - y - lam)) :=
            mul_pos (neg_pos.mpr hx) (neg_pos.mpr hxm)
          -- ⚠ v23/v24 修复（**heartbeat 超时 → 2 条 linarith 失败**）：
          -- `by nlinarith : False` 全上下文搜索会心跳耗尽（v23）；改 `nlinarith only` 后
          -- 又因**漏列假设**而失败（v24，同 `:940`）⟹ 需要 `hx`（`x < 0`）。
          exact (by nlinarith only [hxeq, hmul4, hx] : False).elim
        · -- `lam < y`：`obj(soft) = A ≤ B`，而 `x < 0` 时 `obj(x) ≥ B` ⟹ 等号迫使 `B = A`
          have hAs : l1Objective lam y (softThresh lam y) = lam * y - lam ^ 2 / 2 :=
            hsoftA (le_of_lt hypos)
          -- ⚠ v22 修复：**先把 `hB` 展开成与 `hxeq` 同形的表达式**，再 `linarith`。
          -- 否则 `hB` 含 `l1Objective lam y x` 而 `hxeq` 已展开成 `½(x-y)² - λx`，
          -- **两者不同形**，`linarith` 无法连接（v22 报 `:1071:69 linarith failed`）。
          have hB : (0:ℝ) ≤ l1Objective lam y x - (1 / 2) * y ^ 2 := hlt0_B x hx hyneg
          rw [l1Objective_of_neg lam y x hx] at hB
          rw [hAs] at hxeq
          rw [l1Objective_of_neg lam y x hx] at hxeq
          have hBA : lam * y - lam ^ 2 / 2 ≤ (1 / 2) * y ^ 2 := by
            nlinarith [sq_nonneg (y - lam)]
          -- `obj(x) = A ≤ B ≤ obj(x)` ⟹ `B = A` ⟹ `y = lam`，与 `lam < y` 矛盾
          have hABeq : (1 / 2) * y ^ 2 = lam * y - lam ^ 2 / 2 := by linarith
          -- ⚠ v23 修复（**heartbeat 超时，不是逻辑错误**）：`nlinarith` 在**当前上下文**
          -- （含 `hsoftA`/`hge0_*`/`hlt0_*` 等一大堆大公式）里搜索，**心跳耗尽**
          -- （v23 报 `(deterministic) timeout at isDefEq / Linarith.SimplexAlgorithm.Gauss`）。
          -- ⇒ **把矛盾单独抽出来**：由 `hABeq` 直接得 `(y - lam)² = 0`（纯 `ring` 级），
          -- 再与 `hypos : lam < y` 矛盾 —— **不需要 `nlinarith` 全上下文搜索**。
          have hz : (y - lam) ^ 2 = 0 := by nlinarith only [hABeq]
          have hyeq : y = lam := by
            have hp := pow_eq_zero hz
            linarith
          linarith

/-- **软阈值最优性的简写（只取最优性，不含唯一性）**。 -/
theorem softThresh_is_min (lam y : ℝ) (hlam : 0 < lam) (x : ℝ) :
    l1Objective lam y (softThresh lam y) ≤ l1Objective lam y x :=
  (softThresh_optimal lam y hlam).1 x

/-- **软阈值的最优性（`≤` 形式；`x` 任意，无需假设）**。

⚠⚠ **v23 更正（审计代理 FALSESWEEP 报告，内核复核后裁定）** —— **改名 + 删假设**：

原声明为

```
theorem eq_softThresh_of_is_min (lam y x : ℝ) (hlam : 0 < lam)
    (h : l1Objective lam y x ≤ l1Objective lam y y) :
    l1Objective lam y (softThresh lam y) ≤ l1Objective lam y x
```

**两处缺陷（内核实测坐实）**：

1. ⚠ **`unused variable 'h'`**：结论 `l1Objective lam y (softThresh lam y) ≤ l1Objective lam y x`
   **直接由 `softThresh_is_min lam y hlam x` 得出，对任意 `x` 成立**，
   `h` 完全**未被使用**（证明体是 `softThresh_is_min lam y hlam x`，一字符未提 `h`）。
2. ⚠ **名实不符**：名字承诺「若 `x` 是最小点则 `x = soft_λ(y)`」（**等式**），
   而结论既**非等式**，也**与 `h` 无关**。

**为什么取「改名 + 删 `h`」而不是「把结论改成真等式」**（审计给的二选一，本代理裁定）：

⭐ **候选方案①（把结论改成 `x = softThresh lam y`）被内核证伪**，
**且证伪只需一行**：取 `x := y`，则 `h` 由 `≤` 的**自反性**恒成立，
而 `lam = 1, y = 3` 时 `softThresh 1 3 = 2 ≠ 3` ⟹ 结论为假。
（内核探针 `_probe_out/fs26.lean`：`exit=0`，其中
 `l1Objective lam y y ≤ l1Objective lam y y`（`le_refl`）与
 `softThresh (1:ℝ) 3 = 2` 均**机器验证**；`3 ≠ 2` 亦是。）

⇒ **名字承诺的那个真命题确实存在，但它的正确前提不是 `h`**：
需要 `x` 是**全局最小点**（`∀ z, obj z ≥ obj x`）或等价的**值等式**
`l1Objective lam y x = l1Objective lam y (softThresh lam y)` ——
而后者**本文件早已证明**，即 `softThresh_optimal lam y hlam |>.2`。
故此处**不重复**该内容，只把这条**弱化命题**如实命名为 `softThresh_le_of_is_min`
（其结论与「`x` 是最小点」无关，**只是 `softThresh` 的全局最优性**）。

📌 **建议 coordinator 登记为 `CORRECTIONS` 新条目**；
一般教训：**「`unused variable` ⟹ 名字承诺的假设从未参与证明」**，
处置时**先试着把结论加强到名字真正承诺的形态并代小整数判真假** ——
本例中该形态为**假**，故正确处置是**改名**而非加强。 -/
theorem softThresh_le_of_is_min (lam y : ℝ) (hlam : 0 < lam) (x : ℝ) :
    l1Objective lam y (softThresh lam y) ≤ l1Objective lam y x :=
  softThresh_is_min lam y hlam x

/-- **软阈值的单侧分段形式**（便于区域分情形；`0 ≤ λ` 时与 `softThresh_eq` 等价）：

`soft_λ(y) = if y ≤ -λ then y + λ else if y ≤ λ then 0 else y - λ`。

⚠ **`softThresh_eq` 的 if 链用 `<`，本引理用 `≤`** —— 两者在分界点 `y = ±λ` 处
**数值相同**（边界处 `y + λ = 0` / `y - λ = 0`），但**分支方向相反**。
因此本引理的证明**必须按 `≤` 分支**：若按 `y < -λ` 走，则 `¬ (y < -λ)` 时可能 `y = -λ`，
而 RHS 在 `y = -λ` 取**第一支**，此时 `¬ (y ≤ -λ)` **不可证**（这是 v14 实测到的一个真 bug）。 -/
theorem softThresh_piecewise (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ y : ℝ, softThresh lam y
      = if y ≤ -lam then y + lam else if y ≤ lam then (0:ℝ) else y - lam := by
  intro y
  rw [softThresh_eq lam y hlam]
  by_cases h1 : y ≤ -lam
  · -- `y ≤ -lam`：RHS 取 `y + lam`；LHS 按 `y < -lam` 或 `y = -lam` 分（两者同值 `y + lam`）
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · rw [if_neg (by linarith : ¬ (lam < y)), if_pos h1']
      rw [if_pos h1]
    · -- `y = -lam`（**边界点**）：两侧都应得 `0`，但**左边是 LHS 链的最后一个 `else 0`**、
      -- RHS 是 `(-lam) + lam` ⟹ 目标是 `0 = -lam + lam`，**不是语法同一**，
      -- 故 `rw` **不会自动闭合**，必须补 `ring`（这是 v15 只读审读抓到的遗漏）。
      rw [h1']
      rw [if_neg (by linarith : ¬ (lam < -lam))]
      rw [if_neg (by linarith : ¬ ((-lam : ℝ) < -lam))]
      rw [if_pos (le_refl (-lam))]
      ring
  · -- `¬ y ≤ -lam`：RHS 的第二个 if；LHS 按 `lam < y` 分
    rw [if_neg (by linarith : ¬ (y ≤ -lam))]
    by_cases h2 : lam < y
    · rw [if_pos h2]
      rw [if_neg (by linarith : ¬ (y ≤ lam))]
    · rw [if_neg h2, if_neg (by linarith : ¬ (y < -lam))]
      rw [if_pos (by linarith : y ≤ lam)]

/-- **软阈值的非扩张性（1-Lipschitz）**：
`|soft_λ(y₁) − soft_λ(y₂)| ≤ |y₁ − y₂|`（`λ ≥ 0`）。

这是 ISTA / TISTA / FISTA **收敛性分析**的核心假设（近端算子非扩张）。 -/
theorem softThresh_nonexpansive (lam : ℝ) (hlam : 0 ≤ lam) (y₁ y₂ : ℝ) :
    |softThresh lam y₁ - softThresh lam y₂| ≤ |y₁ - y₂| := by
  -- ⭐ v6/v11 修复（**原稿的证明结构本身证不出该命题**）：
  -- 原稿走 `soft_λ(y) = max(y−λ,0) + min(y+λ,0)`，再用
  -- `|f₁-f₂| + |g₁-g₂| ≤ |y₁-y₂| + |y₁-y₂|`，最后试图"收回"到 `|y₁-y₂|`。
  -- ⚠ **该收尾是反方向的**（`2|d| ≤ |d|` 为假）：
  --   · v9 把该步写成 `_ ≥ |y₁ - y₂|` ⟹ `calc` 的 `Trans` 要求方向一致 ⟹
  --     `invalid 'calc' step, failed to synthesize Trans LE.le GE.ge`；
  --   · v11 我一度把它改成 `≤` ⟹ **那是假命题** ⟹ `linarith failed`。
  -- **根因**：`max(·−λ,0)` 与 `min(·+λ,0)` **各自**只是 1-Lipschitz，
  -- 加法只能给 `≤ 2|d|`；而「两者取值区间相反（`f ≥ 0 ≥ g`）」这一关键事实
  -- 被三角不等式**丢掉了**。⇒ 该路线**本质上达不到紧的 `1|d|`**。
  --
  -- **正确路线（本处采用）**：按 `softThresh_eq` 的**分段形式**做区域分情形。
  -- 先把三段写成单侧的 `if` 链（`y ≤ -lam ↦ y+lam`；`y ≤ lam ↦ 0`；否则 `y-lam`），
  -- 再对 `(y₁, y₂)` 的 3×3 = 9 种区域组合逐一验证：
  -- 每支里 `soft` 要么是**常数**、要么是 `y ± lam`（平移）⟹ Lipschitz 平凡。
  have hreg := softThresh_piecewise lam hlam
  -- ⚠⚠ v16 修复（**我此前的路线是循环论证！**）：
  -- 我曾用 `abs_sub_le_iff` 拆成两个单侧 + `hmono`（单调性）关闭。
  -- **但第二个单侧需要的正是"Lipschitz 上界"本身**：要证 `soft₂ - soft₁ ≤ y₂ - y₁`，
  -- 而单调性只给下界 `soft₂ ≥ soft₁` ⟹ **循环论证**（v16 报 `:1141:6 linarith failed`）。
  --
  -- **正解（唯一非循环）**：把两处 `softThresh` 用 `hreg` 展开成 if 链，
  -- 再按 3×3 区域分情形；每支里 `soft` 是**常数**或 `y ± λ` 的**平移**，
  -- `|差| ≤ |y₁-y₂|` 由 `abs` 的符号拆分 + `linarith` 平凡闭合。
  --
  -- ⚠⚠ v18 修复（**最终路线**）：此前的两次尝试都失败，原因各不相同：
  -- · v16 用 `abs_sub_le_iff` + `hmono`（单调性）⟹ **循环论证**（第二个单侧要的正是上界）；
  -- · v17 用 3×3 区域 + `first | abs_of_nonneg … | abs_of_nonpos … | …` ⟹
  --   **`abs` 的符号在区域信息下未必可判**，`first` 的分支会逐个失败
  --   （v17 报 `:1131:18 linarith failed` **9 次**，即 9 个区域支都掉到最后一个兜底分支）。
  --
  -- **v18 的正解**：仍然按 3×3 区域分情形，但——
  -- ① 用 **`abs_sub_le_iff`** 把**外层** `|E₁ - E₂| ≤ d` 自动拆成两个单侧
  --    （**不需要人工判定符号**，这正是 `abs_sub_le_iff` 的价值）；
  -- ② 用 **`abs_le`/`abs_of_nonneg`/`abs_of_nonpos` 处理右侧的 `|y₁ - y₂|`**
  --    （它的符号由 `le_total y₁ y₂` 显式给出）；
  -- ③ 每个分支最后直接 `linarith`（此时所有 `abs` 都已消除，目标是**线性**的）。
  rw [hreg y₁, hreg y₂]
  by_cases hA : y₁ ≤ -lam <;> by_cases hC : y₁ ≤ lam <;>
    by_cases hB : y₂ ≤ -lam <;> by_cases hD : y₂ ≤ lam <;>
    simp only [hA, hC, hB, hD, if_true, if_false] <;>
    (rw [abs_sub_le_iff] <;>
      constructor <;>
      (rcases le_total y₁ y₂ with hle | hle <;>
        first
          | (rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y₁ - y₂)]; linarith)
          | (rw [abs_of_nonpos (by linarith : y₁ - y₂ ≤ 0)]; linarith)
          | (rw [abs_of_nonpos (by linarith : y₂ - y₁ ≤ 0)]; linarith)
          | (rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y₂ - y₁)]; linarith)
          | (rw [abs_of_nonneg (show (0:ℝ) ≤ 0 by norm_num)]; linarith)
          | (rw [abs_of_nonpos (show (0:ℝ) ≤ 0 by norm_num)]; linarith)
          | (ring_nf; linarith)))

/-- **软阈值的单调性**：`y₁ ≤ y₂ ⟹ soft_λ(y₁) ≤ soft_λ(y₂)`（`λ ≥ 0`）。

⚠ **v6 更正证明路线**：原稿声称"由非扩张性 + 奇对称得到"，但代码**只用了非扩张性**。
**该路线不成立**：非扩张性给出的是 `|soft y₁ - soft y₂| ≤ |y₁ - y₂|`，
它**不能**推出单调性（例如 `soft y₁ - soft y₂ ≤ y₂ - y₁` 在 `y₂ - y₁` 很大时毫无约束力；
`linarith` 会报 `failed to find a contradiction`，v9 正是 `:736:2` 这条）。
正确路线：**用 `softThresh_eq` 的显式分段形式直接做情形分析**（`y` 与 `±λ` 的关系），
这是「1-Lipschitz **不蕴含**单调」的一个具体教训。 -/
theorem softThresh_mono (lam : ℝ) (hlam : 0 ≤ lam) {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    softThresh lam y₁ ≤ softThresh lam y₂ := by
  have hreg := softThresh_piecewise lam hlam
  rw [hreg y₁, hreg y₂]
  -- 按 `y₁`、`y₂` 各处于三段中的哪一段，共 9 支；每支 `linarith` 闭合。
  -- ⚠ `hlam : 0 ≤ lam` **必须**在上下文里（`hreg` 的 `y ≤ -lam ⟹ y ≤ lam` 用到它）。
  by_cases hA : y₁ ≤ -lam <;> by_cases hC : y₁ ≤ lam <;>
    by_cases hB : y₂ ≤ -lam <;> by_cases hD : y₂ ≤ lam <;>
    simp only [hA, hC, hB, hD, if_true, if_false] <;> linarith

/-- **软阈值是 L1 近端算子（prox）的显式公式**：
`prox_{λ|·|}(y) := argmin_x ½‖x − y‖² + λ‖x‖₁` 在一维就是 `soft_λ(y)`。
本条把该命名固定为该文件的 `softThresh`，供下游引用。 -/
def proxL1 (lam y : ℝ) : ℝ := softThresh lam y

/-- `proxL1` 就是 `softThresh`（定义即证）。 -/
@[simp] theorem proxL1_eq_softThresh (lam y : ℝ) : proxL1 lam y = softThresh lam y := rfl

/-- **`proxL1` 的最优性**（`softThresh_optimal` 在 `proxL1` 语言下的重述）。 -/
theorem proxL1_optimal (lam y : ℝ) (hlam : 0 < lam) (x : ℝ) :
    l1Objective lam y (proxL1 lam y) ≤ l1Objective lam y x :=
  softThresh_is_min lam y hlam x


end Lattice
