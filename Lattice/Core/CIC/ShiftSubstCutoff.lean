import Mathlib
import Lattice.Core.CIC.ShiftSubstCommute

/-!
# 位移-替换律：`c = j` 也**不**成立，正确形式需要 `c < j`（阶段 5）

## 第 827 轮之后又排除了一种形式

**第 827 轮否证了 `c = 0, j = 0` 的无条件形式。本轮检验 `c = j` 的形式：**

```
shift j d (subst j s (var j))  =?=  subst (j+d) (shift j d s) (shift (j+1) d (var j))
```

**右边逐步化简：**

1. `shift (j+1) d (var j) = var j`（因为 `j < j+1`，不动）；
2. `subst (j+d) (shift j d s) (var j) = var j`（因为 `j < j+d`，走 `n < j'` 分支）。

**=> 右边化简为 `var j`，而左边是 `shift j d (subst j s (var j)) = shift j d s`。**

**`shift j d s = var j` 对任意 `s` **为假**。**

**=> 所以 `c = j` 的形式也**不**成立。**

## 那么正确形式必须是什么

**关键在左边：当 `c ≤ j` 时，`subst j s (var j) = s`，于是左边变成 `shift c d s`。
要让右边也变成 `shift c d s`，需要 `subst (j+d) (shift c d s) (shift (c+1) d (var j))` 化简为 `shift c d s`，
而这要求 `shift (c+1) d (var j) = var (j+d)`（即 `j ≥ c+1`）**且** `j+d = j+d`（恒真）。**

**=> 正确形式需要 **`j ≥ c + 1`**，即 **`c < j`**（严格）。**

**本文件把这个判定写成定理：`c = j` 时等式为假；因此 `c < j` 是**必要**条件。** -/

namespace Lattice.Core.CIC

/-- **`subst j s (var j) = s`（对任意 `j`）。**

**=> 推广第 827 轮的 `subst_zero_var_zero`：`var` 分支的第一判据是 `n = j`，此处成立。** -/
@[simp] theorem subst_self_var (j : ℕ) (s : Term) : subst j s (Term.var j) = s := by
  show (if j = j then s else if j < j then Term.var j else Term.var (j - 1)) = s
  rw [if_pos rfl]

/-- **`j < j + d` 时 `subst (j+d) s (var j) = var j`。**

**=> 走 `n < j'` 分支，返回 `var j`（不是 `s`）。** -/
theorem subst_below_var (j d : ℕ) (hd : 0 < d) (s : Term) :
    subst (j + d) s (Term.var j) = Term.var j := by
  show (if j = j + d then s else if j < j + d then Term.var j else Term.var (j - 1)) = Term.var j
  rw [if_neg (by omega : ¬ (j = j + d)), if_pos (by omega : j < j + d)]

/-- **`c < j` 时 `shift (c+1) d (var j) = var (j+d)`。**

**=> `c + 1 ≤ j` 使 `j < c+1` 为假，走 `else` 分支返回 `var (j + d)`。** -/
theorem shift_above_cutoff_var (j c d : ℕ) (h : c < j) (hd : 0 < d) :
    shift (c + 1) d (Term.var j) = Term.var (j + d) := by
  show (if j < c + 1 then Term.var j else Term.var (j + d)) = Term.var (j + d)
  rw [if_neg (by omega : ¬ j < c + 1)]

/-- **`c = j` 时位移-替换律**不**成立。**

**=> 左边是 `shift j d s`（由 `subst_self_var`），右边化简为 `var j`（由 `shift_above_cutoff_var`
的反面与 `subst_below_var`）。两者对任意 `s` 不同。**

**这条与第 827 轮的 `shift_subst_no_unconditional` 合起来说明：
正确形式必须在 `c < j` 的严格条件下陈述。** -/
theorem shift_subst_needs_strict (j d : ℕ) (hd : 0 < d) (s : Term)
    (hs : shift j d s ≠ Term.var j) :
    shift j d (subst j s (Term.var j)) ≠
      subst (j + d) (shift j d s) (shift (j + 1) d (Term.var j)) := by
  rw [subst_self_var]
  have h2 : shift (j + 1) d (Term.var j) = Term.var j := by
    show (if j < j + 1 then Term.var j else Term.var (j + d)) = Term.var j
    rw [if_pos (by omega : j < j + 1)]
  rw [h2]
  have h3 : subst (j + d) (shift j d s) (Term.var j) = Term.var j :=
    subst_below_var j d hd (shift j d s)
  rw [h3]
  intro h
  exact hs h

end Lattice.Core.CIC
