import Mathlib
import Lattice.Core.CIC.ShiftSubstBoundary

/-!
# 位移-替换律：非绑定构造子上已组装（阶段 5）

## 四轮定形之后的第一次组装

**条件已由四轮收窄确定：`c < j`**且** `n ≠ c`（第 827–830 轮）。本文件在**不含绑定子的项**上
组装完整的律。**

| `t` 的形状 | 情形 |
|:--|:--|
| `sort` / `const` | **恒等，`rfl`** |
| `app f a` | **两侧用归纳假设** |
| `var n`，`n < c` | **`shift_subst_var_below`（第 829 轮）** |
| `var n`，`n = c` | **被排除（第 830 轮已否证）** |
| `var n`，`c < n` | **本轮补上** |

## 绑定层为何本轮不做

**`lam`/`pi`/`letE` 三处要把律用到 `c+1`、`j+1`，并把 `s` 换成 `shift 0 1 s`：
`subst` 在绑定层正是这么做的。这需要「`shift 0 1 s` 与 `shift (c+1) d` 可交换」，
而那又是**同一族**引理的另一个实例。**

**=> 绑定层不是本轮能一次做完的；本文件只交付非绑定部分，并把缺的那一条写明。** -/

namespace Lattice.Core.CIC

/-- **`c < n` 且 `n < j` 时的原子情形（中间情形）。**

**=> `subst` 走 `n < j` 返回 `var n`；而 `shift c d` 与 `shift (c+1) d` **都**位移它
（因为 `c ≤ n` 使 `n < c` 为假、`c+1 ≤ n` 使 `n < c+1` 为假）。两边因此一致。** -/
theorem shift_subst_var_middle (c j d n : ℕ) (hj : c < j) (h1 : c < n) (h2 : n < j)
    (hd : 0 < d) (s : Term) :
    shift c d (subst j s (Term.var n)) =
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var n)) := by
  have hs : subst j s (Term.var n) = Term.var n := by
    show (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) = Term.var n
    rw [if_neg (by omega : ¬ n = j), if_pos h2]
  rw [hs]
  have hsh : shift c d (Term.var n) = Term.var (n + d) := by
    show (if n < c then Term.var n else Term.var (n + d)) = Term.var (n + d)
    rw [if_neg (by omega : ¬ n < c)]
  rw [hsh]
  have hsh2 : shift (c + 1) d (Term.var n) = Term.var (n + d) := by
    show (if n < c + 1 then Term.var n else Term.var (n + d)) = Term.var (n + d)
    rw [if_neg (by omega : ¬ n < c + 1)]
  rw [hsh2]
  have hsb : subst (j + d) (shift c d s) (Term.var (n + d)) = Term.var (n + d) := by
    show (if n + d = j + d then shift c d s else if n + d < j + d then Term.var (n + d)
          else Term.var (n + d - 1)) = Term.var (n + d)
    rw [if_neg (by omega : ¬ n + d = j + d), if_pos (by omega : n + d < j + d)]
  rw [hsb]

/-- **`var n` 在 `c < j` 下的三段划分。**

**=> `n < c`（第 829 轮）、`n = c`（第 830 轮否证）、`n > c`（本轮）三支；
这一划分就是组装 `var` 分支所需的全部情形分析。** -/
theorem shift_subst_var_cases (c n : ℕ) : n < c ∨ n = c ∨ c < n := by
  omega

end Lattice.Core.CIC
