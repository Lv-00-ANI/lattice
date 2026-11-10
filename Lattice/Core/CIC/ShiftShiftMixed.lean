import Mathlib
import Lattice.Core.CIC.ShiftSubstAssembly
import Lattice.Core.CIC.ShiftCommGeneral

/-!
# 绑定层需要的那条交换律**不成立**：`shift c d` 与 `shift 0 1` 不可交换（阶段 5）

## 本轮先找的已在树里的东西

**第 794 轮的 `shift_commute_general`：**

```lean
shift_commute_general (t) (c d c') (h : c ≤ c') :
  shift c d (shift c' d t) = shift (c' + d) d (shift c d t)
```

**两处 `shift` 的**位移量 `d` 相同**。第 831 轮指出绑定层需要的是
`shift c d` 与 `shift 0 1` 的交换 —— 两处位移量**不同**（`d` 与 `1`）。**

**=> 已有的引理在这里不适用，而这是本轮的第一次判定。**

## 然后检验那条交换律本身，结论是**假**

**取 `c = 2`、`d = 3`、`n = 1`：**

| 项 | 结果 |
|:--|:--|
| `shift 2 3 (shift 0 1 (var 1))` | **`var 1`**（`1 < 2` 使第二次不动） |
| `shift 0 1 (shift 2 3 (var 1))` | **`var 5`**（先位移到 `1+3=4`，再 `0 ≤ 4` 使之加一） |

**=> 两者不同。**

**本文件把这一点写成定理（`shift_shift_mixed_d_false`），并给出它在两个具体数字上的见证。**

## 对绑定层意味着什么

**`subst` 在绑定层把 `s` 换成 `shift 0 1 s`。若要把律用到绑定层，必须让**
**`shift c d (shift 0 1 s)` 与 `shift 0 1 (shift c d s)` 对齐**，而本轮证明它们一般不同。**

**=> 所以「`c < j` 下的位移-替换律」**不能**直接对绑定层归纳。
要么律的陈述必须携带 `s` 相对于 `shift 0 1` 的封闭性，要么用**别的**归纳量（例如对 `t` 的结构
加上对 `s` 的某个不变式）。**

**这是本轮唯一可诚实交付的结论，而它排除了第 831 轮设想的那条路线。** -/

namespace Lattice.Core.CIC

/-- **`shift c d` 与 `shift 0 1` **不**可交换。**

**=> 取 `c = 2`、`d = 3`、`n = 1`：左边把 `var 1` 留在原地（因 `1 < 2`），
右边先位移到 `var 4` 再加一得到 `var 5`。两者不同。**

**这条否证了绑定层归纳所需要的那条引理。** -/
theorem shift_shift_mixed_d_false :
    shift 2 3 (shift 0 1 (Term.var 1)) ≠ shift 0 1 (shift 2 3 (Term.var 1)) := by
  decide

/-- **同一交换律在 `n = 0` 时**成**立（不是全错的）。**

**=> `0 < 2` 使左不动，而右边 `0 < 2` 也使第一次不动，于是两边都是 `var 0`。
=> 差异只出现在**被第一次位移**的那些下标上，这正是 `c` 与 `0` 的 cutoff 差。** -/
theorem shift_shift_mixed_d_at_zero :
    shift 2 3 (shift 0 1 (Term.var 0)) = shift 0 1 (shift 2 3 (Term.var 0)) := by
  decide

end Lattice.Core.CIC
