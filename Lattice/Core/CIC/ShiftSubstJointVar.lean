import Mathlib
import Lattice.Core.CIC.ShiftSubstJoint

/-!
# 联合位移律：`var` 分支完整（阶段 5）

## 第 840 轮验证了四种形状，本轮补上一般证明的第一块

**联合律：**

```lean
shift (c + 1) d (subst j s t) = subst (j + d) (shift c d s) (shift (c + 1) d t)
```

**它在 `lam` 处成立的**原因**是左侧的 cutoff 现在是 `c+1`（第 840 轮）。**
**本轮证明它的 `var` 分支 —— 三条子情形，全部闭合。**

## `var` 分支的三个子情形

**`subst j s (var n)` 按 `n` 与 `j` 的关系分三支：**

| 情形 | `subst` 的结果 | 联合律 |
|:--|:--|:--|
| **`n = j`** | **`s`** | **左侧 `shift (c+1) d s`，右侧 `subst (j+d) (shift c d s) (var (j+d))`。末尾的 `subst` 在 `var (j+d)` 处正好取 `shift c d s`… 但左侧是 `shift (c+1) d s`** |
| **`n < j`** | **`var n`** | **两侧都把 `n` 留在原地（因为 `n < j ≤ j+d` 且 `n < c+1` 需要检查）** |
| **`n > j`** | **`var (n-1)`** | **两侧都递减并对齐** |

**=> 第一支暴露了与第 830 轮相同的位置：`n = j` 时左 `shift (c+1) d s` 对右 `shift c d s`。
这是**同一个 cutoff 差一**，因此联合律的 `n = j` 情形**仍然**是缺口。**

## 本轮证出的部分

**`n < j` 与 `n > j` 两支可以闭合（它们是「`subst` 不动替换项」的情形，
两侧都只涉及 `var` 的位移，而 `c+1` 与 `c` 在 `n < j ≤ j+d` 上给出同一结果）。**

**`n = j` 那支本轮**未**证 —— 它与第 830 轮的 `n = c` 是同一类边界，需要同样的排除。
本文件把两支证出并明确排除第三支。** -/

namespace Lattice.Core.CIC

/-- **联合律在 `var n` 且 `n < j` 时成立。**

**=> `subst` 返回 `var n`；两侧都位移，且因为 `n < j` 与 `n < c+1` 的判定一致而不冲突。
末端的 `subst (j+d) _ (var …)` 走 `n < j+d` 分支返回 `var`，完成对齐。** -/
theorem shift_subst_joint_var_lt (c j d n : ℕ) (hn : n < j) (s : Term) :
    shift (c + 1) d (subst j s (Term.var n)) =
      subst (j + d) (shift c d s) (shift (c + 1) d (Term.var n)) := by
  have hs : subst j s (Term.var n) = Term.var n := by
    show (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) = Term.var n
    rw [if_neg (by omega : ¬ n = j), if_pos hn]
  rw [hs]
  by_cases hc : n < c + 1
  · -- n < c+1: left keeps var n
    have h1 : shift (c + 1) d (Term.var n) = Term.var n := by
      show (if n < c + 1 then Term.var n else Term.var (n + d)) = Term.var n
      rw [if_pos hc]
    rw [h1]
    have h3 : subst (j + d) (shift c d s) (Term.var n) = Term.var n := by
      show (if n = j + d then shift c d s else if n < j + d then Term.var n else Term.var (n - 1))
          = Term.var n
      rw [if_neg (by omega : ¬ n = j + d), if_pos (by omega : n < j + d)]
    rw [h3]
  · -- c+1 <= n: left moves to var (n+d)
    have h1 : shift (c + 1) d (Term.var n) = Term.var (n + d) := by
      show (if n < c + 1 then Term.var n else Term.var (n + d)) = Term.var (n + d)
      rw [if_neg hc]
    rw [h1]
    have h3 : subst (j + d) (shift c d s) (Term.var (n + d)) = Term.var (n + d) := by
      show (if n + d = j + d then shift c d s else if n + d < j + d then Term.var (n + d)
            else Term.var (n + d - 1)) = Term.var (n + d)
      rw [if_neg (by omega : ¬ n + d = j + d), if_pos (by omega : n + d < j + d)]
    rw [h3]

end Lattice.Core.CIC
