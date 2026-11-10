import Mathlib
import Lattice.Core.CIC.ParallelSubst
import Lattice.Core.CIC.ShiftAsInst

/-!
# `inst_lift_shift`：一般 `cutoff` 下六个构造子闭合，**第七个（`var`）为假**

## 这一轮重新检查了什么

**第 793 轮结论：`shift` 可以被一次 `inst` 模拟，但每进一层绑定就漂移一格。
本轮换一个归纳形式再试一次 —— 并发现一件事：`ParallelSubst.lean` 里**已经有**那条阶梯律**

```lean
shift_commutation_general (c : Nat) (b : Term) :
  shift (c + 1) 1 (shift c 1 b) = shift c 2 b
```

**它对**任意 `Term`** 成立。**这一点之前的几轮都没有用上：我在第 782、783、784 轮手推的正是它的特例。**

**=> 用它检查 `inst_lift_shift` 的一般 `cutoff` 形式，六个构造子立刻闭合。
只有 `var` 不闭合 —— 而它不是「差一步」，是**假的**。**

## 六个构造子（已在本轮的探测中逐条闭合）

**对 `inst (lift σ) (shift c 1 t) = shift c 1 (inst σ t)` 按 `t` 归纳、并对 `c` 与 `σ` 一般化：**

| 构造子 | 做法 |
|:--|:--|
| `sort`、`const` | `simp only [shift, inst]` |
| `app` | 两个归纳假设 |
| `lam`、`pi`、`letE` | `rw [ihA c σ]` → `congr 1` → **`exact ihb (c + 1) (lift σ)`** |

**`exact ihb (c + 1) (lift σ)` 这一行说明**指数学与替换深度都对了**：归纳假设恰好在 `(c+1, lift σ)` 处实例化。**

## 但 `var` 情形是**假**的

**取 `c = 1`、索引 `1`，目标化简为**

```
shift 0 1 (σ 1) = shift 1 1 (σ 1)
```

**而这两个算子**不同**：**

```lean
shift 0 1 (var 0) = var 1     -- decide
shift 1 1 (var 0) = var 0     -- decide
```

**`shift 0 1` 固定的是**没有**索引（`0 ≤ n` 全部位移），`shift 1 1` 固定的是索引 `0`。**

**=> 一般 `cutoff` 形式**不能**成立，而原因与第 792 轮完全相同：
`lift` 的不动集是 `{0}`，`shift c` 的不动集是 `[0, c)`。**

## 结论

**`inst_comp` 的绑定情形需要 `cutoff = 1` 而归纳基例只会给出 `cutoff = 0`；
把定理一般化到 `cutoff = 1` 会让 `var` 失败。这两件事不能同时满足。**

**本文件**不**声称 `inst_comp` 已证；它把「六个闭合、第七个为假」写成可检查的记录，
并指出 `shift_commutation_general` 这条既有工具此前未被使用。** -/

namespace Lattice.Core.CIC

/-- **`shift 0 1` 与 `shift 1 1` 在索引 `0` 处不同。**

**=> 这是「一般 `cutoff` 形式在 `var` 处失败」的原子见证。** -/
theorem shift_zero_one_vs_one_one :
    shift 0 1 (Term.var 0) = Term.var 1 ∧ shift 1 1 (Term.var 0) = Term.var 0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`shift_commutation_general` 的特例：`c = 0`。**

**`shift 1 1 (shift 0 1 b) = shift 0 2 b`。**

**=> 这条是 `ParallelSubst.lean` 已有的 `shift_one_one_zero_one`；
本文件把它与 `shift_commutation_general` 并置，说明两者的关系。** -/
theorem shift_one_one_zero_one_from_general (b : Term) :
    shift 1 1 (shift 0 1 b) = shift 0 2 b := shift_commutation_general 0 b

end Lattice.Core.CIC
