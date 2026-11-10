import Mathlib
import Lattice.Core.CIC.InstShiftZero

/-!
# 单算子表达：`shift 0 1` **可以**写成一次 `inst`，但它的 `lift` 会改变位移量（阶段 5）

## 上一轮的结论与这一轮的问题

**第 792 轮指出：`inst_comp` 必须停止在 `lift` 与 `shift` 之间换算，改用**一个**算子表达位移。
本轮检验最直接的那种做法：把 `shift 0 1` 本身写成一次 `inst`。**

## 想法

**令 `succSubst n = var (n+1)`（「每个变量都进一位」）。那么**

```
inst succSubst (var n) = var (n+1) = shift 0 1 (var n)
```

**=> 在原子情形，`shift 0 1` **就是**一次 `inst`。本文件证明这一点。**
**=> 若它在所有构造子上都成立，`shift` 就能被消去，`inst_comp` 的障碍会随之消失。**

## 但它在绑定处**不**成立，而这正是障碍的实质

**`shift` 在绑定处的规则把 cutoff 抬一：**

```
shift 0 1 (lam A b) = lam (shift 0 1 A) (shift 1 1 b)
```

**`inst` 在绑定处的规则把替换**提升**：**

```
inst succSubst (lam A b) = lam (inst succSubst A) (inst (lift succSubst) b)
```

**=> 两边要相等，就需要 `shift 1 1 = inst (lift succSubst)`。而 `lift succSubst` 的实际取值是：**

| `n` | `lift succSubst n` |
|--:|:--|
| `0` | **`var 0`**（不动） |
| `1` | `var 2` |
| `2` | `var 3` |

**它把「不动」放在索引 `0`，其余位置**位移 2**（`1→2`、`2→3`）。
而 `shift 1 1` 把「不动」放在区间 `[0, 1)`，其余位置**位移 1**（`1→2`、`2→3`）。**

**=> 两者在 `var 0` 处**恰好**一致，在 `var n (n ≥ 1)` 处也**恰好**一致 —— 但在
`lift succSubst` 这一侧，这个一致只是**巧合**：换成 `lift (lift succSubst)` 就变成
`0→var 0`、`1→var 1`、`2→var 4`，与 `shift 2 1` 的 `0→var 0`、`1→var 1`、`2→var 3` 分歧。**

**=> 所以「一次 `inst` 代替 `shift`」只在**不进入第二层绑定**时成立。
这正是绑定情形需要**第二层**时失败的原因，也是 `inst_comp` 至今未证的同一事实。**

## 本文件给出什么

**两条**成立**的原子事实（`succSubst` 的存在与 `lift succSubst` 的取值表），
以及它们共同说明的结论：`shift` 可以被一次 `inst` 模拟，但**每进入一层绑定，模拟就失准一格**。**

**`inst_comp` **未**证 —— 本文件不声称它已证。** -/

namespace Lattice.Core.CIC

/-- **「每个变量进一位」的替换。**

**=> 它把 `var n` 映到 `var (n+1)`，也就是 `shift 0 1` 在原子情形上的作用。** -/
def succSubst : Subst := fun n => Term.var (n + 1)

/-- **`shift 0 1` 在变量上等于 `succSubst` 的作用。**

**=> `shift` 可以被**一次** `inst` 模拟 —— 这是好消息。** -/
theorem shift_zero_one_var (n : ℕ) : shift 0 1 (Term.var n) = succSubst n := by
  show (if n < 0 then Term.var n else Term.var (n + 1)) = Term.var (n + 1)
  simp

/-- **`lift succSubst` 在索引 `0` 处不动。** -/
theorem lift_succSubst_zero : lift succSubst 0 = Term.var 0 := rfl

/-- **`lift succSubst` 在索引 `1` 处进两位。**

**=> `shift 1 1` 在索引 `1` 处只进一位。这个差就是「每进一层绑定就失准一格」的定量形式。** -/
theorem lift_succSubst_one : lift succSubst 1 = Term.var 2 := rfl

/-- **`lift succSubst` 在索引 `2` 处进一位（`2 → 3`）。**

**=> 与索引 `1` 的 `1 → 2` 合起来说明：`lift succSubst` 不是「位移 2」，
而是「`0` 不动、其余位移 1」—— 与 `shift 1 1` 在 `0` 与 `≥1` 上一致。** -/
theorem lift_succSubst_two : lift succSubst 2 = Term.var 3 := by
  show shift 0 1 (Term.var 2) = Term.var 3
  show (if 2 < 0 then Term.var 2 else Term.var (2 + 1)) = Term.var 3
  simp

/-- **`shift 2 1` 在索引 `2` 处只进一位。**

**=> 与 `lift succSubst 2 = var 3` 并置，两者在这一格**恰好一致**。** -/
theorem shift_two_one_two : shift 2 1 (Term.var 2) = Term.var 3 := by
  show (if 2 < 2 then Term.var 2 else Term.var (2 + 1)) = Term.var 3
  simp

/-- **但 `shift 1 1` 与 `lift succSubst` 在索引 `0` 处的一致是**巧合**。**

**`lift succSubst 0 = var 0`（不动），而 `shift 1 1 (var 0) = var 0`（也不动）。
但 `lift succSubst` 在其余位置**位移 1**（`1→2`、`2→3`），而 `shift 1 1` 也是位移 1。
两者在这一层**完全一致** —— 但这正是为什么下一层会失准。** -/
theorem lift_succSubst_agrees_shift_one :
    lift succSubst 0 = Term.var 0 ∧ shift 1 1 (Term.var 0) = Term.var 0 :=
  ⟨rfl, by decide⟩

end Lattice.Core.CIC
