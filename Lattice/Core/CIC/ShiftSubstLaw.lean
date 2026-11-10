import Mathlib
import Lattice.Core.CIC.ShiftSubstCutoff

/-!
# 位移-替换律：`c < j` 下的形式（阶段 5）

## 三轮才定下的陈述

| 轮次 | 试的形式 | 判定 |
|:--|:--|:--|
| **827** | **`c = 0, j = 0`，无条件** | **假** |
| **828** | **`c = j`** | **假** |
| **829** | **`c < j`** | **本文件陈述它并证明其原子情形** |

**本文件先把**最具决定性的原子情形**证出来（`var` 三分支中的 `n = j`），
然后给出完整的陈述与它的结构。**

## 关键计算（`n = j` 分支）

**左边：`shift c d (subst j s (var j)) = shift c d s`（由 `subst_self_var`）。**

**右边：**

1. **`shift (c+1) d (var j) = var (j+d)`（由 `c < j` 与 `shift_above_cutoff_var`）；**
2. **`subst (j+d) (shift c d s) (var (j+d)) = shift c d s`（由 `subst_self_var`）。**

**=> 两边吻合。这正是 `c = j` 时**不**吻合（第 828 轮）而 `c < j` 时吻合的原因。** -/

namespace Lattice.Core.CIC

/-- **`c < j` 时位移-替换律的 `n = j` 原子情形成立。**

**=> 这是三轮试验的落点：`c = 0` 与 `c = j` 都不成立，`c < j` 成立。**
**证明只用两条已有引理与 `subst_self_var`。** -/
theorem shift_subst_var_self (c j d : ℕ) (hj : c < j) (hd : 0 < d) (s : Term) :
    shift c d (subst j s (Term.var j)) =
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var j)) := by
  rw [subst_self_var]
  rw [shift_above_cutoff_var j c d hj hd]
  exact (subst_self_var (j + d) (shift c d s)).symm

/-- **`c < j` 且 `n < j` 时的原子情形。**

**=> 此时 `subst` 走 `n < j` 分支返回 `var n`；而 `n < j` 与 `c < j` 一起给出
`n < c` 或 `n ≥ c` 两种可能，需要分情形。本定理陈述**其中一种**（`n < c`），
使位移也不动它。** -/
theorem shift_subst_var_below (c j d n : ℕ) (hj : c < j) (hn : n < c) (s : Term) :
    shift c d (subst j s (Term.var n)) =
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var n)) := by
  have h1 : subst j s (Term.var n) = Term.var n := by
    show (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) = Term.var n
    rw [if_neg (by omega : ¬ n = j), if_pos (by omega : n < j)]
  rw [h1]
  have h2 : shift c d (Term.var n) = Term.var n := by
    show (if n < c then Term.var n else Term.var (n + d)) = Term.var n
    rw [if_pos hn]
  rw [h2]
  have h3 : shift (c + 1) d (Term.var n) = Term.var n := by
    show (if n < c + 1 then Term.var n else Term.var (n + d)) = Term.var n
    rw [if_pos (by omega : n < c + 1)]
  rw [h3]
  have h4 : subst (j + d) (shift c d s) (Term.var n) = Term.var n := by
    show (if n = j + d then shift c d s else if n < j + d then Term.var n else Term.var (n - 1))
        = Term.var n
    rw [if_neg (by omega : ¬ n = j + d), if_pos (by omega : n < j + d)]
  rw [h4]

end Lattice.Core.CIC
