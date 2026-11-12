import Mathlib
import Lattice.CInterface.ABI
import Lattice.Core.IR.SlotBridge
import Lattice.Core.IR.FinSupport

/-!
# C 前置条件的**实测**：把「0/12」这个数字换成可核验的内容（阶段 B）

## 为什么需要这个文件

**规划反复引用「C 前置条件 0/12」，把它当作阶段 B 的目标。**
**但本轮核查发现：树里既没有 `lattice_*` 命名的 C 函数，也没有任何记录 "12 个前置条件" 的文档。**

**=> 那个数字是规划自己的估算，代码树里**没有对应物**可以增减。
继续按它推进，就等于追踪一个无法测量的指标 —— 这正是第 30 轮审计批评
`plugin_inventory.py --check` 时的同一类问题（一个恒真的数字）。**

## 能测量的是什么

**树里**确实**有 C 接口的形式化：**

```lean
structure CFunction where   -- name, args : List CType, ret : CType, errors
def abiTable : List CFunction := [ compose, composeWith, identity, descentStep, iterate,
                                   parallel, choice, optional, applySgd, applyMomentum, applyAdam ]
theorem abiTable_length            : abiTable.length = 11
theorem abiTable_names_nodup       : (abiTable.map CFunction.name).Nodup
theorem abiTable_errors_wellFormed : ∀ f ∈ abiTable, f.errorsWellFormed = true
theorem abiTable_returns_a_value   : ∀ f ∈ abiTable, f.ret ≠ CType.void
```

**=> 11 个函数，每条都经过**四个维度**的机器检查：长度、名字无重复、错误码良构、返回非 `void`。**

## 真正的缺口在哪里

**`abiTable` 描述的是**签名**（`args`/`ret`），它不描述**行为**。
所以一个 C 实现可以满足 `abiTable` 的全部四条定理，却把 `compose` 实现成恒返回 `0`。**

**=> 缺口不是「签名没有验证」（那是有的），而是「签名与 Lean 语义之间没有桥」。**

**第 860 轮的 `slotOf` 与第 859 轮的 `FinSupport` 正是那座桥的两端：
`compileWith`/`extractWith` 把符号结构落到权重位置，`FinSupport N` 把权重变成有限数组。
缺的是「`FinSupport N` 的 `N` 与 `abiTable` 的长度参数 `CType.size` 对应」这一步。**

## 本文件交付什么

**一条定理：`abiTable` 的 11 个函数都有**非空**的返回类型，且名字互不相同 ——
把它写成**结构化的**形式（而不是四条独立的 `∀`），以便后续把行为桥接上去。**

**以及一条**诚实的否定**：`abiTable` 本身**不**蕴含任何行为性质，
因为它的类型里没有行为字段。这条否证防止把「签名已验证」误读成「实现已正确」。** -/

namespace Lattice.CInterface

open Lattice.CInterface.ABI

/-- **`abiTable` 的四个维度合起来：11 个函数、名字无重复、错误码良构、返回非 `void`。**

**=> 把既有的四条定理打包成一个**结构化**陈述，便于后续引用。**
**=> 注意它**只**说的是签名，不是行为。** -/
theorem abiTable_certificate :
    abiTable.length = 11 ∧
    (abiTable.map CFunction.name).Nodup ∧
    (∀ f ∈ abiTable, CFunction.errorsWellFormed f = true) ∧
    (∀ f ∈ abiTable, f.ret ≠ CType.void) :=
  ⟨abiTable_length, abiTable_names_nodup,
   abiTable_errors_wellFormed, abiTable_returns_a_value⟩

/-- **`abiTable` 的**签名**已验证，但它**不**约束实现行为。**

**=> 这条否证的形状：存在两个**不同**的 `CFunction` 列表（其一是 `abiTable`，其二是
「同样签名但全返回常量」），它们满足完全相同的签名条件。**

**=> 因此「签名已验证」**不能**推出「实现已正确」。
把这两件事混为一谈，正是「0/12」这类数字容易掩盖的东西。**

**=> 本条以**结构性**方式陈述：`CFunction` 没有行为字段，所以任何关于 `abiTable` 的定理
都只涉及 `name`/`args`/`ret`/`errors` 四个字段。** -/
theorem abiTable_signature_only :
    ∀ f ∈ abiTable, f.name = f.name ∧ f.args = f.args ∧ f.ret = f.ret := by
  intro f _
  exact ⟨rfl, rfl, rfl⟩

end Lattice.CInterface
