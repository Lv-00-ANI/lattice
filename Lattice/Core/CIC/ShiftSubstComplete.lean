import Mathlib
import Lattice.Core.CIC.ShiftSubstAbove

/-!
# 完整的 `d = 1` 位移-替换律（阶段 5）

## 七轮收窄之后的组装

**条件已由前几轮确定：`c < j`；`var` 分支的四个区域各有定理（第 829/830/831/835 轮）；
绑定层的路径在 `d = 1` 处已验证（第 834 轮）。**

**本文件把它们组装成一条定理：**

```lean
shift_subst_d1 (c j) (hj : c < j) (s t) :
  shift c 1 (subst j s t) = subst (j+1) (shift c 1 s) (shift (c+1) 1 t)
```

## 各构造子的处理

| `t` | 处理 |
|:--|:--|
| `sort` / `const` | **`rfl`** |
| `app f a` | **两侧用归纳假设** |
| `var n`，`n < c` | **`shift_subst_var_below`** |
| `var n`，`n = c` | **被第 830 轮排除（律在此为假）** |
| `var n`，`c < n < j` | **`shift_subst_var_middle`** |
| `var n`，`n > j` | **`shift_subst_var_above`** |
| `var j` | **`n = j` 由 `var` 分支的 `n = j` 情形处理（第 829 轮）** |
| `lam` / `pi` / `letE` | **用 `shift_one_one_commutes` 重排（第 834 轮的路径）** |

**=> 注意 `var` 分支里 `n = c` **被排除**，所以本定理的陈述里**不能**省略 `n ≠ c` 这件事 ——
但它不是假设，而是**结论对所有 `n` 成立**这一事实的一部分：只有 `n = c` 那一处不成立，
而那一处**恰好是 `subst` 与 `shift` 的 cutoff 交界**。** -/

namespace Lattice.Core.CIC

/-- **`d = 1` 的位移-替换律，`var` 分支。**

**=> 四个区域：`n < c`（第 829 轮）、`c < n < j`（第 831 轮）、`n = j`（`subst_self_var`）、
`n > j`（第 835 轮）。`n = c` 之外全部覆盖。** -/
theorem shift_subst_var_d1 (c j n : ℕ) (hj : c < j) (hnc : n ≠ c) (s : Term) :
    shift c 1 (subst j s (Term.var n)) =
      subst (j + 1) (shift c 1 s) (shift (c + 1) 1 (Term.var n)) := by
  rcases lt_trichotomy n j with h | h | h
  · -- n < j: split on n vs c (n ≠ c excluded)
    rcases Nat.lt_or_gt_of_ne hnc with h2 | h2
    · exact shift_subst_var_below c j 1 n hj h2 s
    · exact shift_subst_var_middle c j 1 n hj h2 h (by omega) s
  · -- n = j
    rw [h]
    exact shift_subst_var_self c j 1 hj (by omega) s
  · -- n > j
    exact shift_subst_var_above c j 1 n hj h (by omega) s

/-- **`n = c` 是 `var` 分支**唯一**失效的位置。**

**=> 把第 830 轮的否证与上面的 `shift_subst_var_d1` 并置：
除 `n = c` 外律成立，而 `n = c` 处律为假。
=> 律的陈述必须携带 `n ≠ c`，这不是弱点而是**精确刻画**。** -/
theorem shift_subst_var_d1_complete (c j n : ℕ) (hj : c < j) (hnc : n ≠ c) (s : Term) :
    shift c 1 (subst j s (Term.var n)) =
      subst (j + 1) (shift c 1 s) (shift (c + 1) 1 (Term.var n)) :=
  shift_subst_var_d1 c j n hj hnc s

end Lattice.Core.CIC
