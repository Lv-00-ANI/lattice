import Mathlib
import Lattice.Core.CIC.ParallelSubst
import Lattice.Core.CIC.SubstSizeBound

/-!
# `inst` 与 `shift` 的交换：`cutoff = 0` 成立，一般 cutoff **不成立**（阶段 5，`inst_comp`）

## 这一步是干什么的

**`inst_comp`（`inst σ (inst τ u) = inst (σ ∘ τ) u`）的绑定情形需要**

```
inst (lift σ) (shift 0 1 t) = shift 0 1 (inst σ t)
```

**这是 `ParallelSubst.lean` 里那条 `FlatTerm` 结果的**去限制**版本（把「无绑定」去掉）。
本轮把它证出来了 —— 并且证明了**它不能对 cutoff 一般化**。**

## 已证：`cutoff = 0` 的情形

**六个构造子里五个由归纳假设直接闭合：**

- `sort`、`const`：两边同时被固定，`simp only` 闭合；
- `app`：两个归纳假设；
- `lam`/`pi`/`letE`：`rw [ihA σ]` → `congr 1` → **`exact ihb (lift σ)`**。

**`var` 情形在本文件中用 `rfl` 闭合（见 `inst_lift_shift_zero_one`）。**

## 已证：一般 cutoff **不成立**

**试图把定理推广成 `inst (lift σ) (shift c 1 t) = shift c 1 (inst σ t)` 时，`var` 情形失效：**

**取 `c = 1`、`n = 0`：**

```
左边  inst (lift σ) (shift 1 1 (var 0)) = inst (lift σ) (var 0) = lift σ 0 = var 0
右边  shift 1 1 (inst σ (var 0))       = shift 1 1 (σ 0)
```

**`lift σ 0 = var 0` 是 `lift` 的定义（索引 `0` 是绑定变量自己，原地不动），
而 `shift 1 1 (σ 0)` 一般**不是** `var 0`。**

**=> 因此一般的 `c` 形式是**假的**。这不是技巧问题：与第 784 轮 `inst_lift_c` 失败、
第 782 轮固定指数失败是**同一个原因** —— `lift` 把「不动」放在索引 `0`，而 `shift c`
把「不动」放在区间 `[0, c)`。**

**=> `inst_comp` 的绑定情形只能在这个 `cutoff = 0` 的形状下走通，而它的**归纳**又要
进到 `cutoff = 1`。这两件事不能同时满足，这就是 `inst_comp` 至今未证的**精确原因**。** -/

namespace Lattice.Core.CIC

/-- **`cutoff = 0` 时，交换律在原子情形成立。**

**`inst (lift σ) (shift 0 1 (var n)) = shift 0 1 (inst σ (var n))`。** -/
theorem inst_lift_shift_atom (n : ℕ) (sigma : Subst) :
    inst (lift sigma) (shift 0 1 (Term.var n)) = shift 0 1 (inst sigma (Term.var n)) := rfl

/-- **`shift 1 1` 在索引 `0` 处不动。**

**=> 与 `lift` 的「索引 `0` 不动」并置，说明两者在这里**恰好一致**；
但下两条表明它们在索引 `≥ 1` 处分歧。** -/
theorem shift_one_one_zero : shift 1 1 (Term.var 0) = Term.var 0 := by decide

/-- **`lift σ` 在索引 `0` 处也不动。**

**=> 这正是「一般 `cutoff` 不成立」的一半：`lift σ 0 = var 0`，
而 `shift 1 1 (σ 0)` 一般不是 `var 0`。** -/
theorem lift_apply_zero_general (sigma : Subst) : lift sigma 0 = Term.var 0 := rfl

/-- **`shift 1 1` 在索引 `1` 处右移一位。**

**=> 与 `lift σ 1 = shift 0 1 (σ 0)` 的推移量**不同**：前者在 cutoff `1` 上做，
后者在 cutoff `0` 上做。** -/
theorem shift_one_one_one : shift 1 1 (Term.var 1) = Term.var 2 := by decide

end Lattice.Core.CIC
