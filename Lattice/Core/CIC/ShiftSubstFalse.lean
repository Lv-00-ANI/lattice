import Mathlib
import Lattice.Core.CIC.ShiftSubstFull

/-!
# `d = 1` 的位移-替换律**在绑定层为假**（阶段 5，第八次否证）

## 第 838 轮把错配定位在标注上，本轮确认它不是标注约定的问题

**第 838 轮看到绑定分支留下：**

```
(subst (j+1) (shift c 1 s) (shift (c+1) 1 A)).lam  ...body...
=
(subst (j+1) (shift c 1 s) (shift c 1 A)).lam      ...body...
```

**并把它记成「`subst` 与 `shift` 对标注的处理不同」。**

**这个说法是对的，但由此得出的下一步（改陈述或改约定）**不成立，因为律本身是假的**。

## 具体反例

**取 `c = 0`、`j = 1`、`s = var 5`、`t = lam (var 0) (var 1)`：**

```lean
#eval (shift 0 1 (subst 1 (.var 5) (.lam (.var 0) (.var 1)))
       == subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.lam (.var 0) (.var 1))))
-- false
```

**=> 律在 `lam` 处**为假**。**

## 为什么它一定为假（不必依赖计算）

**`shift c d` 对 `lam A b` 的定义是：**

```lean
| c, d, .lam A b => .lam (shift c d A) (shift (c + 1) d b)
```

**而 `subst j s` 对 `lam A b` 是：**

```lean
| j, s, .lam A b => .lam (subst j s A) (subst (j + 1) (shift 0 1 s) b)
```

**左边 `shift c 1 (subst j s (lam A b))` 的标注是 `shift c 1 (subst j s A)`；
右边按定义得到 `subst (j+1) (shift c 1 s) (shift (c+1) 1 A)`。**

**两者的**标注位置**分别是「先替换再位移」与「先位移（在 `c+1` 处）再替换」。
一般情形下它们不同 —— 这正是反例所显示的东西。**

## 结论

**`d = 1` 的位移-替换律**不能**作为一个无条件等式陈述：它在 `lam` 处失败，与它在 `var c` 处失败
是**两个独立的原因**（第 830 轮 vs 本轮）。**

**=> `par-subst` 不能由这条律得到。需要的是另一条路线：
要么对 `ParRedV` 直接作归纳（把 `subst` 放在 `ParRedV` 的 `beta` 构造子内部处理），
要么引入**替换与位移的联合陈述**（`s` 与 `t` 同时换），使标注位置在两边一致。**

**本轮把反例写成本定理，并把这两条路线记下来。** -/

namespace Lattice.Core.CIC

/-- **`d = 1` 位移-替换律在 `lam` 处为假。**

**=> 具体见证：`c = 0`、`j = 1`、`s = var 5`、`t = lam (var 0) (var 1)`。
`decide` 判定两侧不等。**

**这与第 830 轮 `var c` 处的失败是**两个独立原因**：那里是 cutoff 交界，
这里 `subst` 与 `shift` 对标注的处理次序不同。** -/
theorem shift_subst_d1_fails_at_lam :
    shift 0 1 (subst 1 (.var 5) (.lam (.var 0) (.var 1))) ≠
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.lam (.var 0) (.var 1))) := by
  decide

/-- **同一反例的 `pi` 版本。** -/
theorem shift_subst_d1_fails_at_pi :
    shift 0 1 (subst 1 (.var 5) (.pi (.var 0) (.var 1))) ≠
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.pi (.var 0) (.var 1))) := by
  decide

end Lattice.Core.CIC
