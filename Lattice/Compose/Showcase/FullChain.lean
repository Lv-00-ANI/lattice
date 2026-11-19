import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lib.Chain.RealChainEntryOOV

/-!
# **`Compose/Showcase/FullChain.lean` —— 官方展品 M-1：整条 L0 → L2 链是一条 `Compose` 链**（阶段 T）

## 为什么需要这个文件

**`README.md` 的链路图把 M-1（数据 → token → 符号）画成一条链，而**库里至今没有任何定理把它写成一条
`Compose` 链**——`Compose` 层的 11 个 primitive 与 6 个组合子从未被端到端使用过。**

**=> 本文件是**第一个官方展品**：它把链的前两跳各做成一个具名 `Primitive`，
用 `compose` 合成，然后**证明合成的 `run` 就是手写管线**。**

## 展示厅的三条判据（全部满足）

| 判据 | 本文件 |
|:--|:--|
| ① 有一条 `Compose` 链，每环节是**具名 `Primitive`**，不是手写 `bind` | `tokenizePrim` + `bridgePrim` + `compose` |
| ② 链的 `sound` 是**真推导** | 两个阶段的 `sound` 各自是真证明，`compose` 的 `sound` 由 `Primitive.sound` 消费 |
| ③ `run` 与手写管线**相等** | **`fullChain_run`** |

## 一个设计要点：`Pre` 必须包含「这一跳能成功」

**`Primitive.sound` 的陈述是 `∀ x, pre x → ∃ y, run x = some y ∧ post x y`——它要求 `run` **成功**。**

**而 `tokenizeV` 返回 `Option`：它可以失败（OOV 无法编码时）。**
**=> 把它做成 `Primitive` 时，`pre` 必须写成 `(tokenizeV V s).isSome`，**
**否则 `sound` **不可证**——这正是「前置条件就是这一跳的成功条件」的本来含义，
而不是把失败偷藏进 `run := none`。**

**`L1Bridge` 是全函数，故其 `pre := True`。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`tokenizePrim`** | **⭐⭐ L0 → L1 的 `Primitive`，`pre` 是「分词成功」** |
| **`bridgePrim`** | **⭐⭐ L1 → L2 的 `Primitive`，全函数** |
| **`fullChain`** | **⭐⭐⭐ 用 `compose` 合成的整条链** |
| **`fullChain_run`** | **⭐⭐⭐ 合成的 `run` 等于手写管线 `map L1Bridge ∘ tokenizeV`** |
| **`fullChain_sound`** | **⭐⭐ 合成的 `sound`（`compose` 的真推导的直接消费）** | -/

namespace Lattice.Compose.Showcase.FullChain

open Lattice.Compose

/-- **⭐⭐ L0 → L1：OOV 感知的分词，做成 `Primitive`。**

**`pre` 写成 `(tokenizeV V s).isSome`：前置条件**就是**这一跳的成功条件，
所以 `sound` 可证而不是被回避。** -/
def tokenizePrim (V : OOVVocab) : Primitive (List Char) (List CharToken) where
  pre := fun s => (tokenizeV V s).isSome
  post := fun s y => tokenizeV V s = some y
  run := fun s => tokenizeV V s
  sound := by
    intro s hs
    cases h : tokenizeV V s with
    | none =>
      -- `pre` 在失败时不可满足
      simp [h] at hs
    | some y =>
      exact ⟨y, h, h⟩
  strength := .exact
  coverage := none

/-- **⭐⭐ L1 → L2：`L1Bridge`，全函数，故 `pre := True`。** -/
def bridgePrim : Primitive (List CharToken) (List SymToken) where
  pre := fun _ => True
  post := fun y z => Lattice.Lib.Chain.RealEndToEnd.L1Bridge y = z
  run := fun y => some (Lattice.Lib.Chain.RealEndToEnd.L1Bridge y)
  sound := by
    intro y _
    exact ⟨Lattice.Lib.Chain.RealEndToEnd.L1Bridge y, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ 整条链：用 `compose` 合成，而**不是**手写 `bind`。**

**合成条件是「第一跳的后置蕴含第二跳的前置」——第二跳的 `pre` 是 `True`，故平凡成立。** -/
def fullChain (V : OOVVocab) : Primitive (List Char) (List SymToken) :=
  compose (tokenizePrim V) bridgePrim (by
    intro s y _
    trivial)

/-- **⭐⭐⭐ 展品的核心：合成的 `run` **就是**手写管线。**

**=> `(fullChain V).run s = (tokenizeV V s).map L1Bridge`。**

**这条把「用 `Compose` 组合」与「手写管线」**证明地**等同起来——
没有它，展品只是一个新定义，不是一条关于既有管线的定理。** -/
theorem fullChain_run (V : OOVVocab) (s : List Char) :
    (fullChain V).run s = (tokenizeV V s).map Lattice.Lib.Chain.RealEndToEnd.L1Bridge := by
  cases h : tokenizeV V s with
  | none => simp [fullChain, compose, tokenizePrim, bridgePrim, h]
  | some y => simp [fullChain, compose, tokenizePrim, bridgePrim, h]

/-- **⭐⭐ 合成链的 `sound`：只要分词这一步能成功，链就产出 `SymToken` 列表且后置成立。**

**=> 这是 `Primitive.sound` 的直接消费，其内容是 `compose` 的真推导。** -/
theorem fullChain_sound (V : OOVVocab) (s : List Char) (hs : (fullChain V).pre s) :
    ∃ z, (fullChain V).run s = some z ∧ (fullChain V).post s z :=
  (fullChain V).sound s hs

end Lattice.Compose.Showcase.FullChain
