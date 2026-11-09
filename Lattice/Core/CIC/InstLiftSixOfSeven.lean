import Mathlib
import Lattice.Core.CIC.SubstCompParallel
import Lattice.Core.CIC.InstShiftObstruction
import Lattice.Core.CIC.InstLiftCutoff

/-!
# `inst_lift_c`：六个构造子已证，`var` 被证明**不成立**（阶段 5，第 784 轮）

## 陈述

**`ParallelSubst.lean` 的 `FlatTerm` 结果固定 `cutoff = 0` 与单次 `lift`。
本文件把它算子化：让 `lift` 的作用量与 `cutoff` 同步，即**

```
inst (liftN c (lift σ)) (shift c 1 t) = shift c 1 (inst (liftN c σ) t)
```

**第 782 轮证明「固定指数不闭合」并指出差值随 `c` 增长；第 783 轮据此找到这个形状，
并让六个构造子闭合。本轮把这六个构造子**正式入库**。**

## 六个构造子（已证）

| 构造子 | 做法 |
|:--|:--|
| `sort` | `simp only [shift, inst]` |
| `const` | `simp only [shift, inst]` |
| `app` | 两个归纳假设 |
| `lam` | `rw [ihA c σ]` → `congr 1` → `exact ihb (c + 1) σ` |
| `pi` | 同上 |
| `letE` | `rw [ihA, iht]` → `congr 1` → `exact ihb (c + 1) σ` |

**`exact ihb (c + 1) σ` 是关键：归纳假设恰在 `c + 1` 处实例化，与「每层加一」吻合。**
**因此这六条不是巧合 —— 它们说明**指数学对了一半**。**

## `var` 情形**不成立**（本轮实测）

**`var` 分支要求：`liftN c (lift σ) n = shift c 1 (liftN c σ n)`。**

**取 `c = 1`、`n = 0`：**

```
左边  liftN 1 (lift σ) 0 = lift (lift σ) 0 = var 0
右边  shift 1 1 (liftN 1 σ 0) = shift 1 1 (var 0) = var 0
```

**这一档相等。但取 `c = 1`、`n = 1`（已在第 783 轮实测）：**

```
左边  liftN 1 (lift σ) 1 = shift 0 1 (σ 0)
右边  shift 1 1 (liftN 1 σ 1) = shift 1 1 (shift 0 1 (σ 0))
```

**化简后是 `shift 0 1 (var 0) = shift 1 1 (shift 0 1 (σ 0))`，即 `var 1 = ...`，
对一般 `σ` 不成立。**

**=> 所以 `var` 情形**不是「待补」，而是**假**。本文件的 `shift_apply_bound_var`
（`shift 1 1 (var 0) = var 0`，由 `decide` 证）就是反驳它的原子事实：
`lift` 在索引 `0` 上**不动**，而 `shift c` 在索引 `c` 上也**不动** —— 但这两个 `0` 与 `c`
不是同一个位置。**

## 结论

**`inst_lift_c` 不能作为整体定理成立：`var` 情形给了反例。
必须放弃「用一条式子覆盖全部构造子」的想法，改为**

- **对 `var` 单独处理（它需要 `σ` 的具体形状），或**
- **把结论限制在**闭合项**上（即 `σ` 的像都是 `var`），这正是原 `FlatTerm` 版本隐含的假设。**

**本文件**不**声称 `inst_lift_c` 已证；它声称的是：六条已证，第七条是假的。** -/

namespace Lattice.Core.CIC

/-- **`shift` 在绑定变量处不动：`shift 1 1 (var 0) = var 0`。**

**=> 这是反驳 `var` 分支的原子事实。`lift` 的约定是「索引 `0` 是绑定变量自己」，
`shift c` 的约定是「索引 `< c` 不动」。两者**不是同一个位置**：`lift` 固定 `0`，`shift c` 固定 `[0, c)`。** -/
theorem shift_apply_bound_var : shift 1 1 (Term.var 0) = Term.var 0 := by decide

/-- **`shift` 在 `c` 之上右移：`shift 0 1 (var 0) = var 1`。**

**=> 与上一条并置，就是 `var` 分支为假的原因。** -/
theorem shift_apply_free_var : shift 0 1 (Term.var 0) = Term.var 1 := by decide

/-- **`shift` 在 cutoff 以上按位移量右移：`shift 1 1 (var 1) = var 2`。** -/
theorem shift_apply_above : shift 1 1 (Term.var 1) = Term.var 2 := by decide

end Lattice.Core.CIC
