import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# **官方展品 M-4：L1 ⇄ L2 是一条 `compose` 链，且它闭合于恒等**（阶段 U）

## 这个展品展示什么

**`README.md` 的链路图把 M-4 画成 `decode ∘ L1Bridge` 方向的回程，而 M-1（`Showcase/FullChain.lean`）
只走到 `SymToken` 就停了。**

**本文件把**符号 → token**与**token → 符号**各做成一个具名 `Primitive`，用 `compose` 串起来，
并证明：**

```lean
l1l2Roundtrip.run cs = some cs
```

**⇒ 即**合成的链在 `ConstraintSet` 上是恒等**——这不是一个新造的等式，
而是库里既有的 `decode_encode` 在 `Compose` 语言里的**同一个事实**。**

## 为什么这两个阶段的前置条件都是 `True`

**`Primitive.sound` 要求 `run` 成功。**
**⇒ 只有当某一跳**可能失败**时，`pre` 才必须收窄到「该跳成功」。**

| 阶段 | `run` | `pre` |
|:--|:--|:--|
| `encode` | `some (encode cs)` —— 全函数 | `True` |
| `decode` | `decode ts`，而 `decode` 的**定义**就是 `some (…)` | `True` |

**⇒ 与 M-1 的 `tokenizePrim` 形成对照：那里 `tokenizeV` 返回 `Option` 且**可能为 `none`**，
所以它的 `pre` 必须是 `(tokenizeV V s).isSome`。**「前置条件恰好是这一跳的成功条件」是同一原则的两种形态。**

## 一个被这次展品**撞出来**的事实：`ConstraintSet` 有两份在真实代码里相遇

**第一次编译失败，错误是：**

```
argument
  cs
has type
  ConstraintSet : Type
but is expected to have type
  Lift.SymbolToWeightCorrectness.ConstraintSet : Type
```

**=> 我从 `Lib/Editing/RealExtractCanonical.lean` 引入的 `ConstraintSet` 与 `encode` 接受的那个
**不是同一个类型**。审计记过「`ConstraintSet` 有 4 份定义」（`ConvertVectorLinear`、`RealExtractCanonical` 等），
**而这里是其中两份第一次被放进同一个文件、并被编译器当面拒绝。**

**本文件的处理是**明确写出 `encode` 接受的那一份**（`Lift.SymbolToWeightCorrectness.ConstraintSet`），
而不是靠 `open` 让某一份胜出——**展品必须指向真实的那一个，否则它证明的是关于另一个类型的命题。**

**=> 这是一个**立即可见**的收敛点：若把 `ConstraintSet` 收到唯一权威，本文件的那三处限定词就可以删掉。**
**在那之前，写明具体是哪一份是唯一诚实的写法。** -/

namespace Lattice.Compose.Showcase.L1L2

open Lattice.Compose

/-- **⭐⭐ L2 → L1：把 `ConstraintSet` 编码成 `SymToken` 列表，做成 `Primitive`。**

**全函数，故 `pre := True`；`post` 说「结果就是 `encode cs`」。** -/
def encodePrim : Primitive Lift.SymbolToWeightCorrectness.ConstraintSet (List SymToken) where
  pre := fun _ => True
  post := fun cs ts => Lattice.encode cs = ts
  run := fun cs => some (Lattice.encode cs)
  sound := by
    intro cs _
    exact ⟨Lattice.encode cs, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐ L1 → L2：把 `SymToken` 列表解码回 `ConstraintSet`，做成 `Primitive`。**

**`decode` 的定义本身就是 `some (…)`，所以它也是全函数。** -/
def decodePrim : Primitive (List SymToken) Lift.SymbolToWeightCorrectness.ConstraintSet where
  pre := fun _ => True
  post := fun ts cs => Lattice.decode ts = some cs
  run := fun ts => Lattice.decode ts
  sound := by
    intro ts _
    exact ⟨_, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ 回程链：`encode` 之后 `decode`，用 `compose` 串起来。**

**合成条件是「编码的后置蕴含解码的前置」——解码的前置是 `True`，故平凡。** -/
def l1l2Roundtrip : Primitive Lift.SymbolToWeightCorrectness.ConstraintSet Lift.SymbolToWeightCorrectness.ConstraintSet :=
  compose encodePrim decodePrim (by
    intro cs ts _
    trivial)

/-- **⭐⭐⭐ 展品的核心：合成的链在 `ConstraintSet` 上是**恒等**。**

**=> 这正是既有的 `decode_encode`，在 `Compose` 语言里重述为一条 `run` 等式。**
**⇒ 没有它，展品只是一个新定义；有了它，`Compose` 层与 `Runtime` 层的桥是可引用的。** -/
theorem l1l2Roundtrip_run (cs : Lift.SymbolToWeightCorrectness.ConstraintSet) :
    l1l2Roundtrip.run cs = some cs := by
  show (some (Lattice.encode cs)).bind Lattice.decode = some cs
  exact Lattice.decode_encode cs

/-- **⭐⭐ 合成链的 `sound`：对任意 `ConstraintSet`，链产出且后置成立。**

**=> 因为回程闭合于恒等，这里的存在性见证就是 `cs` 本身。** -/
theorem l1l2Roundtrip_sound (cs : Lift.SymbolToWeightCorrectness.ConstraintSet) (hs : l1l2Roundtrip.pre cs) :
    ∃ z, l1l2Roundtrip.run cs = some z ∧ l1l2Roundtrip.post cs z :=
  l1l2Roundtrip.sound cs hs

end Lattice.Compose.Showcase.L1L2
