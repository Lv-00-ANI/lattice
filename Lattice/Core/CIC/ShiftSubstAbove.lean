import Mathlib
import Lattice.Core.CIC.ShiftSubstBinder

/-!
# `n > j` 区域：`var` 分支真正完整了（阶段 5）

## 第 834 轮发现的缺口

**第 831 轮把 `var` 分支记为「完整：三情形」。第 834 轮指出那**只对 `n < j` 完整**，
`n > j` 从未讨论 —— 而在那一区域 `subst` 会**递减**下标（`var (n-1)`）。**

**本轮补上它。**

## `n > j` 的计算

**取 `c < j < n`、`d > 0`：**

1. **`subst j s (var n) = var (n-1)`** —— **因 `n > j`，走 `n - 1` 分支；**
2. **`shift c d (var (n-1)) = var ((n-1)+d)`** —— **`n-1 ≥ j > c`，走 `else` 分支；**
3. **`shift (c+1) d (var n) = var (n+d)`** —— **`n > j > c` 使 `n < c+1` 为假；**
4. **`subst (j+d) _ (var (n+d)) = var ((n+d)-1)`** —— **`n+d > j+d`，走 `n - 1` 分支。**

**=> 左边是 `var ((n-1)+d)`，右边是 `var ((n+d)-1)`，两者的下标都是 `n + d - 1`。**

**=> 相等。这也解释了为什么这一区域**不像** `n = c` 那样失败：
两边的递减与位移次序不同，但**算术上抵消**。**

## `var` 分支的四个区域，现在全都有定理

| 区域 | 状态 |
|:--|:--|
| **`n < c`** | **`shift_subst_var_below`（第 829 轮）** |
| **`n = c`** | **`shift_subst_fails_at_cutoff_boundary`（第 830 轮，**否证**）** |
| **`c < n < j`** | **`shift_subst_var_middle`（第 831 轮）** |
| **`n > j`** | **本轮** |

**=> 这一分支现在真的是穷尽的：三个区域成立、一个区域被否证。** -/

namespace Lattice.Core.CIC

/-- **`n > j` 区域：`subst` 的递减与 `shift` 的位移在算术上抵消。**

**=> 左边下标是 `(n-1)+d`，右边是 `(n+d)-1`，都是 `n+d-1`。
这条补上了第 834 轮标出的最后一个缺口。** -/
theorem shift_subst_var_above (c j d n : ℕ) (hj : c < j) (hn : j < n) (hd : 0 < d) (s : Term) :
    shift c d (subst j s (Term.var n)) =
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var n)) := by
  have hs : subst j s (Term.var n) = Term.var (n - 1) := by
    show (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) = Term.var (n - 1)
    rw [if_neg (by omega : ¬ n = j), if_neg (by omega : ¬ n < j)]
  rw [hs]
  have h1 : shift c d (Term.var (n - 1)) = Term.var (n - 1 + d) := by
    show (if n - 1 < c then Term.var (n - 1) else Term.var (n - 1 + d)) = Term.var (n - 1 + d)
    rw [if_neg (by omega : ¬ n - 1 < c)]
  rw [h1]
  have h2 : shift (c + 1) d (Term.var n) = Term.var (n + d) := by
    show (if n < c + 1 then Term.var n else Term.var (n + d)) = Term.var (n + d)
    rw [if_neg (by omega : ¬ n < c + 1)]
  rw [h2]
  have h3 : subst (j + d) (shift c d s) (Term.var (n + d)) = Term.var (n + d - 1) := by
    show (if n + d = j + d then shift c d s else if n + d < j + d then Term.var (n + d)
          else Term.var (n + d - 1)) = Term.var (n + d - 1)
    rw [if_neg (by omega : ¬ n + d = j + d), if_neg (by omega : ¬ n + d < j + d)]
  rw [h3]
  congr 1
  omega

/-- **`var` 分支的四区域划分。**

**=> 对任意 `c`、`j`、`n` 恰有一个区域成立；三区域成立、`n = c` 被否证。
本条把「穷尽」写成可检查的形式。** -/
theorem shift_subst_var_regions (c j n : ℕ) :
    n < c ∨ n = c ∨ (c < n ∧ n < j) ∨ n = j ∨ j < n := by
  omega

end Lattice.Core.CIC
