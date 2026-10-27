/-
# 带激活的多层 `Ladder`：让「多层」有语义内容

## 0. 问题

`Lift/MultiLayerLadder.lean` 的多层是**重言**的（原因记在那一节：`compileNet` 只换包装，
`satSym` 与 `satW` 展开成同一个命题）。`Core/Activation` 又证明了另一件事：**纯仿射的多层会折叠**
（`actStackEval_of_no_activation`：全 `none` 的栈等于 `netAct`）。**所以「多层」在纯仿射下本来就没有内容。**

两层合起来才是要点：要让「多层」有语义，栈里必须有激活；要有 `Ladder` 的形式，`l2l3` 必须改变表示。

## 1. 设计：`l2l3` 把一条程序**切成两段**

| 侧 | 类型 | 谓词 |
|:--|:--|:--|
| 符号 | `List (StackLayer n)`（一条完整程序） | `satSym s := ∀ x, actStackEval s x = g x` |
| 权重 | `List (StackLayer n) × List (StackLayer n)`（切成两段） | `satW w := ∀ x, actStackEval w.2 (actStackEval w.1 x) = g x` |

`l2l3 s := (s.take (s.length / 2), s.drop (s.length / 2))`。

**`l2l3` 改变了表示**：一边是一条程序，另一边是一对（前段、后段）。
**`satSym` 与 `satW` 是不同的命题**：前者说「整条程序算出 `g`」，后者说「先跑前段再跑后段算出 `g`」。
桥梁需要两条引理：

1. `actStackEval_append`（本节新证）：先跑 `p` 再跑 `q` = 跑 `p ++ q`；
2. `List.take_append_drop`：`s.take k ++ s.drop k = s`。

**所以 `l2l3_sound` 不是 `exact h`。**

## 2. 为什么这真的让「多层」有内容

`StackLayer.act : Option (ℝ → ℝ)`。若所有层都是 `none`，`actStackEval_of_no_activation` 说整条栈
等于 `netAct`——**多层折叠成一层，「切成两段」就没有意义**。存在 `some relu` 的层时，`relu_not_affine`
说该函数不是仿射，**含激活的栈不能折叠成任何单层仿射**，于是「前段 + 后段」是一个真的分解。

`activationLadder_requires_activation` 把前一半写成了定理。

## 3. 边界

- **`g` 是实例参数**（与 `Geo/CodegenLadder.lean` 同一处理）：`Ladder.satW : W → Prop` 只接收权重，
  「算出了什么」必须有一个可比较的目标。
- **切点取 `s.length / 2`** 只是为了非平凡（长度 ≥ 2 时前段非空）；`l2l3_sound` 对**任意**切点都成立，
  证明没有用到 `/ 2`。
- **本节不证**任意含激活的栈都与某个仿射等价或不等价；只证拼接的求值分解，并引用既有的
  `relu_not_affine` 说明为何不可折叠。
- 本节**不改** `Core/Activation`、`Lift/MultiLayerLadder` 的任何既有定理。
-/
import Mathlib
import Lattice.Lift.EndToEnd
import Lattice.Core.Activation

namespace Lattice.Lift

open Lattice.Core Lattice.Core.Activation

variable {n : ℕ}

/-- **`actStackEval` 对拼接的分解**：先跑 `ls` 再跑 `ms`，等于跑 `ls ++ ms`。

`actStackEval` 是 `List.foldl`，所以这就是 `List.foldl_append`。
**这条是本节 `l2l3_sound` 的一半**——没有它，「先跑前段再跑后段」就与「跑整条」对不上。 -/
theorem actStackEval_append (ls ms : List (StackLayer n)) (x : Fin n → ℝ) :
    actStackEval (ls ++ ms) x = actStackEval ms (actStackEval ls x) := by
  unfold actStackEval
  rw [List.foldl_append]

/-- **带激活的多层 `Ladder`**：`l2l3` 把一条程序**切成前段与后段**。

`l2l3_sound` 用 `actStackEval_append` 与 `List.take_append_drop`，**不是 `exact h`**——
这就是它与 `MultiLayerLadder` 的区别。 -/
noncomputable def activationLadder (g : (Fin n → ℝ) → Fin n → ℝ) :
    Ladder (List (StackLayer n)) (StackLayer n) (List (StackLayer n))
      (List (StackLayer n) × List (StackLayer n)) where
  l0l1 := identityTokenizer (StackLayer n)
  l1l2 :=
    { encode := id
      decode := some
      roundtrip := fun _ => rfl }
  l2l3 := fun s => (s.take (s.length / 2), s.drop (s.length / 2))
  satSym := fun s => ∀ x : Fin n → ℝ, actStackEval s x = g x
  satW := fun w => ∀ x : Fin n → ℝ, actStackEval w.2 (actStackEval w.1 x) = g x
  l2l3_sound := by
    intro s hs x
    -- goal: `actStackEval s.drop (actStackEval s.take x) = g x`
    -- the append lemma, read right-to-left, turns the two runs into one
    rw [← actStackEval_append]
    -- and the split reassembles into the original program
    rw [List.take_append_drop]
    exact hs x

/-- **端到端**：整条程序处处算出 `g` ⟹ 切成两段后「先前段后后段」也处处算出 `g`。 -/
theorem activationLadder_forward (g : (Fin n → ℝ) → Fin n → ℝ) (s : List (StackLayer n))
    (hs : (activationLadder g).satSym s) :
    (activationLadder g).satW ((activationLadder g).l2l3 s) :=
  Ladder.ladder_forward (activationLadder g) s hs

/-- **两侧是不同的命题**（结构证据）：`satSym` 的量词跑在**一条**程序上，
`satW` 的量词跑在**一对**程序上，`l2l3` 是那个切分。 -/
theorem activationLadder_l2l3_is_a_split (g : (Fin n → ℝ) → Fin n → ℝ)
    (s : List (StackLayer n)) :
    (activationLadder g).l2l3 s
      = (s.take (s.length / 2), s.drop (s.length / 2)) :=
  rfl

/-- **为什么这个分解不是可有可无的**：纯仿射的栈会折叠成一层
（`actStackEval_of_no_activation`），那时「前段 + 后段」与「整条」说的是同一件事，
因为整条本来就等于 `netAct`。**只有存在激活层时，切分才是真把一件事拆成两件。** -/
theorem activationLadder_requires_activation (ps : List (AffineLayer (Fin n))) :
    actStackEval (ps.map fun p => (⟨p, none⟩ : StackLayer n)) = fun x => netAct ps x := by
  funext x
  exact actStackEval_of_no_activation ps x

end Lattice.Lift
