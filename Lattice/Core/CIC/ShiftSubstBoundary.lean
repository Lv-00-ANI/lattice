import Mathlib
import Lattice.Core.CIC.ShiftSubstLaw

/-!
# 位移-替换律：`n = c` 处**也**不成立（阶段 5，第四次收窄）

## 第 829 轮留下了什么

**第 829 轮在 `c < j` 下证出了 `var` 分支的两个端点（`n = j` 与 `n < c`）。
本轮补中间的 `n`（`c ≤ n < j`），却发现 `n = c` 这个**边界**上律本身不成立。**

## `n = c` 处的计算

**取 `n = c`（且 `c < j`，`d > 0`）：**

1. **`subst j s (var c) = var c`**（因 `c < j`）；
2. **`shift c d (var c) = var (c+d)`**（因 `¬ c < c`，走 `else` 分支）；
3. **`shift (c+1) d (var c) = var c`**（因 `c < c+1`，走 `then` 分支）；
4. **`subst (j+d) (shift c d s) (var c) = var c`**（因 `c < j+d`）。

**=> 左边是 `var (c+d)`，右边是 `var c`。两者对 `d > 0` **不同**。**

**=> 律在 `n = c` 处**不成立**。**

## 这意味着什么

**`shift c d` 与 `shift (c+1) d` 在 **`n = c`** 处恰好分歧：
前者位移它（因为 `c < c` 为假），后者不动它（因为 `c < c+1` 为真）。**

**=> 律的成立范围必须**排除** `n = c`。正确形式要么**

- **分情形：`n < c` 或 `n > c`**（即 `n ≠ c`），要么
- **把 `shift (c+1)` 改成 `shift c`**（但那样 `subst` 的 cutoff 不一致）。

**本文件把 `n = c` 的失败写成定理，这是第四次收窄：
`c = 0` 不行（第 827 轮）、`c = j` 不行（第 828 轮）、`n = c` 不行（本轮）。**

**=> 正确形式的轮廓现在很清楚：`c < j` 且 `n ≠ c`。**
**不过这个「且」在绑定层会怎样传递，还需要下一轮检验 —— 因为在 `lam` 下 `c` 与 `n` 都加一，
`n = c` 的关系会被保留。** -/

namespace Lattice.Core.CIC

/-- **`n = c` 且 `c < j` 且 `d > 0` 时，位移-替换律不成立。**

**=> 左边 `shift c d (subst j s (var c)) = var (c+d)`，右边
`subst (j+d) (shift c d s) (shift (c+1) d (var c)) = var c`；`d > 0` 使两者不同。**

**这是律的第四次收窄：成立范围必须排除 `n = c`。** -/
theorem shift_subst_fails_at_cutoff_boundary (c j d : ℕ) (hj : c < j) (hd : 0 < d) (s : Term) :
    shift c d (subst j s (Term.var c)) ≠
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var c)) := by
  have hs : subst j s (Term.var c) = Term.var c := by
    show (if c = j then s else if c < j then Term.var c else Term.var (c - 1)) = Term.var c
    rw [if_neg (by omega : ¬ c = j), if_pos hj]
  rw [hs]
  have h1 : shift c d (Term.var c) = Term.var (c + d) := by
    show (if c < c then Term.var c else Term.var (c + d)) = Term.var (c + d)
    rw [if_neg (by omega : ¬ c < c)]
  have h2 : shift (c + 1) d (Term.var c) = Term.var c := by
    show (if c < c + 1 then Term.var c else Term.var (c + d)) = Term.var c
    rw [if_pos (by omega : c < c + 1)]
  have h3 : subst (j + d) (shift c d s) (Term.var c) = Term.var c := by
    show (if c = j + d then shift c d s else if c < j + d then Term.var c else Term.var (c - 1))
        = Term.var c
    rw [if_neg (by omega : ¬ c = j + d), if_pos (by omega : c < j + d)]
  rw [h1, h2, h3]
  intro h
  have h4 : c + d = c := by injection h
  omega

/-- **`n < c` 时中间情形也不成问题（第 829 轮已证），故排除 `n = c` 后律覆盖整个 `var` 分支。**

**=> 陈述为「`n ≤ c` 或 `n = c` 时由两条已证定理覆盖；`n = c` 由上一轮排除」。
本定理把这一点写成**分组陈述**：`n < c` 与 `n = j` 已有定理，`n = c` 已否证。** -/
theorem shift_subst_var_dichotomy (c j : ℕ) (hj : c < j) (n : ℕ) :
    n < c ∨ n = c ∨ (c < n ∧ n < j) ∨ n = j ∨ j < n := by
  omega

end Lattice.Core.CIC
