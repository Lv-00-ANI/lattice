import Mathlib
import Lattice.Runtime.Extraction
import Lattice.Runtime.L1L2
import Lattice.Runtime.L1L2Roundtrip

/-!
# `Lattice.Runtime.PartialRepresentation` — **往返律的 `Option` 版本，以及 token 环的实例**

## 为什么 `Representation` 装不下 L1⇄L2

`Lattice.Lift.Representation P W` 的往返律是 `∀ p, extract (compile p) = p`——**全函数**。
而 token 环的往返是

```lean
theorem decodePayload_encodeForm (n : Nat) (c : LinearForm R n) :
    decodePayload n (encodeForm c).payload = some c
```

**带 `some`**：`decodePayload` 是偏的（`arity` 与 `toks` 不自洽时给 `none`）。
⇒ **`decode ∘ encode = some`，不是 `= id`。**

## 但还有更深的一层：符号侧不能是 `LinearForm R n`

把 `extract : Encoded R → Option (LinearForm R n)` 写下来**是类型错误**，实测：

```
decodePayload e.arity e.payload : Option (LinearForm R e.arity)
expected                       : Option (LinearForm R n)
```

**`Encoded.arity` 是运行时字段**，`e.arity` 与 `n` 不定义相等。**这不是可以靠 `cases` 消掉的**：
**`Encoded` 把 arity 从类型里搬进了数据**（`L1L2.lean` 的整个设计要点），
所以「解出来的东西的 arity」**由数据决定，不由类型决定**。

⇒ **符号侧必须是 `Σ n, LinearForm R n`**，不是某一个固定的 `LinearForm R n`。

**这不是让步，是那个设计决定的准确后果**：`arity` 成为一等字段，**代价是解码结果的类型是依存的**。
本文件把它写出来，而不是在陈述里偷偷用一个固定的 `n`。

## 结构

```lean
structure PartialRepresentation (P W : Type) where
  compile : P → Option W
  extract : W → Option P
  roundtrip : ∀ p w, compile p = some w → extract w = some p
```

**它是每一个有损/偏跳跃的形状**：token 化（本文件）、量化（`RoundingBackend`）、
提取失败（`no_extractor_both_layers` 说的是那种失败**有时不可避免**）。

## 本文件给什么

1. `PartialRepresentation`；
2. `PartialRepresentation.ofTotal` —— **每个 `Representation` 都是偏表示**（单向嵌入）；
3. ⭐ `formPartial : PartialRepresentation (Σ n, LinearForm R n) (Encoded R)` —— **L1⇄L2 的实例**。

## ⚠ 本文件**不**做的

- **不声称偏表示蕴含全表示**：`compile := fun _ => none` 满足偏往返律（前提永假），
  **却不给出任何全函数互逆**。`ofTotal` 是单向的。
- **不涉及语义**。`PartialRepresentation` 还没有带语义的强化版本；
  **「往返有了所以语义也有了」是错的**，记在这里。
-/

namespace Lattice.Lift

/-- ⭐⭐ **偏表示**：两侧都可能失败，往返律只在成功时成立。

`Representation` 要求 `extract (compile p) = p`。**当解码是偏的**——token 流可能不自洽、
量化可能越界、提取可能无解——**那个等式根本陈述不出来**，能陈述的是：

> 一旦 `compile p` 成功给出 `w`，`extract w` 就还原 `p`。

**这不是弱化到无意义**：它排除「编译成功但提取不还原」这一整类缺陷。 -/
structure PartialRepresentation (P W : Type) where
  /-- 编译：可能失败。 -/
  compile : P → Option W
  /-- 提取：可能失败。 -/
  extract : W → Option P
  /-- ⭐ **往返律（偏的）**：编译成功则提取还原。 -/
  roundtrip : ∀ p w, compile p = some w → extract w = some p

namespace PartialRepresentation

/-- ⭐ **每个全表示都是偏表示。**

这是两个结构之间**唯一成立**的方向：**全函数互逆 ⟹ 偏函数互逆**。
反向不成立——`compile := fun _ => none` 满足偏往返律（前提永假），却不给出任何全函数互逆。

**所以「某处用了 `PartialRepresentation`」是一条信息**：它说明那一跳允许失败。 -/
def ofTotal {P W : Type} (R : Representation P W) : PartialRepresentation P W where
  compile := fun p => some (R.compile p)
  extract := fun w => some (R.extract w)
  roundtrip := by
    intro p w hw
    simp only [Option.some.injEq] at hw
    subst hw
    exact congrArg some (R.roundtrip p)

/-- **偏往返律的逐点形式**，便于组合。 -/
theorem roundtrip_apply {P W : Type} (R : PartialRepresentation P W) (p : P) :
    ∀ w, R.compile p = some w → R.extract w = some p :=
  fun w => R.roundtrip p w

end PartialRepresentation

end Lattice.Lift

/-! ## 实例：token 环 -/

namespace Lattice.Lift

namespace L1L2

open Lattice.Core (LinearForm)
open Lattice.Lift.L1L2Roundtrip

/-- **`Σ n, LinearForm R n` 到 `Encoded R` 的偏表示**——**L1⇄L2 的实例**。

- `compile ⟨n, c⟩ := some (encodeForm c)` —— **编码是全的**；
- `extract e := (decodePayload e.arity e.payload).map (fun c => ⟨e.arity, c⟩)`
  —— **解码可能失败；成功时，解出来的 arity 由数据给出**；
- `roundtrip`：`decodePayload_encodeForm` 加 `encodeForm_arity`。

⚠ **两侧的「可能失败」不对称**：编码是全的，解码是偏的。
**那是设计信息**——token 流可以总是产生，但不一定总能解回符号，
**而 `Representation` 的往返律既表达不了这个不对称，也表达不了依存的 arity。** -/
def formPartial {R : Type} [DecidableEq R] [Inhabited R] :
    PartialRepresentation (Σ n, LinearForm R n) (Encoded R) where
  compile := fun p => some (encodeForm p.2)
  extract := fun e => (decodePayload e.arity e.payload).map (fun c => ⟨e.arity, c⟩)
  roundtrip := by
    intro p w hw
    obtain ⟨n, c⟩ := p
    simp only [Option.some.injEq] at hw
    subst hw
    show (decodePayload (encodeForm c).arity (encodeForm c).payload).map
        (fun c' => (⟨(encodeForm c).arity, c'⟩ : Σ m, LinearForm R m)) = some ⟨n, c⟩
    rw [encodeForm_arity]
    rw [L1L2Roundtrip.decodePayload_encodeForm]
    rfl

end L1L2

end Lattice.Lift
