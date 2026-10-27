/-
# 一个 `l2l3_sound` **不是重言**的 `Ladder`：表达式树 → 指令列表

## 0. 为什么需要这一节

`Lift/MultiLayerLadder.lean` 的 `l2l3_sound := fun _ h => h` 是重言，原因是结构性的：
`compileNet = s.layers.map layerOfNet`，而 `layerOfNet` 只换包装，所以 `satSym` 与 `satW`
**展开成同一个命题**。两个谓词重合时，桥梁定理必然没有内容。

**要让它有内容，`l2l3` 必须改变表示。** 库里有现成的、已经证明过的例子：
`CExprCodegen.toStack`（第 157 轮）把**表达式树**编译成**扁平指令列表**，
`toStack_correct` 是真正的翻译正确性定理。

**本文件把那个例子装进 `Ladder`。**

## 1. 为什么 `l2l3_sound` 在这里不是重言

三个谓词各自的**主语不同**：

| 侧 | 谓词 | 谈的是什么 |
|:--|:--|:--|
| 符号 | `satSym e := ∀ pts, evalC e pts = g pts` | **表达式树**的求值 |
| 权重 | `satW w := ∀ pts seed, runProg (env pts) w [seed] = some (g pts :: [seed])` | **指令列表**在栈机上的运行 |

`evalC` 与 `runProg` 是两个不同的函数，`l2l3` 是 `e ↦ compileProg (toStack e)`。
**桥梁是 `toStack_correct`**：把树编译成指令，运行指令得到树的值。这正是「编译保持语义」。

**并且两侧都是 `∀`：符号侧对**所有**测试环境，权重侧对**所有**环境**与**所有**初始种子**。
不是单点。

## 2. 深度限制

`toStack_correct` 的前提是 `CExpr.depth e ≤ 1`（第 157 轮记录：代码生成器目前只覆盖浅树）。
所以符号侧取**子类型** `{ e : CExpr n // Lattice.Geo.CExprCodegen.CExpr.depth e ≤ 1 }`。

**这把限制放进类型，而不是加一个可能被忘记的前提。**

## 3. 边界

- **目标函数 `g` 是实例参数**：`Ladder.satW : W → Prop` 只接收权重，「它算出了什么」
  必须有一个可比较的目标。`g` 同时给出两侧的比较基准，而**两侧的计算方式不同**——
  这才是桥梁定理的内容。
- **不声称**代码生成覆盖任意深度的表达式。`depth ≤ 1` 是当前实现的边界，已登记。
- 本节**不改** `MultiLayerLadder`、`CExprCodegen`、`StackCodegen` 的任何既有定理。
-/
import Mathlib
import Lattice.Lift.EndToEnd
import Lattice.Geo.CExprCodegen

namespace Lattice.Lift

open Lattice.Geo.ComputableExpr

/-- **深度受限的符号表达式**：代码生成器当前覆盖的那一类。

用子类型而不是前提，是因为 `Ladder` 的字段是函数，没有地方放一个「请先证明这个前提」的
参数；把限制放进类型，误用就会在类型检查处失败。 -/
abbrev ShallowCExpr (n : ℕ) := { e : CExpr n // Lattice.Geo.CExprCodegen.CExpr.depth e ≤ 1 }

/-- **`l2l3_sound` 有内容的 `Ladder`**：`CExpr → List StackOp`。

`l2l3_sound` 的证明用 `toStack_correct`，不是 `exact h`：它把「树算出 `g`」翻译成
「指令列表在栈机上算出 `g`」。 -/
noncomputable def codegenLadder {n : ℕ} (g : (ℕ → Fin n → Float) → Float) :
    Ladder (List (ShallowCExpr n)) (ShallowCExpr n) (ShallowCExpr n)
      (List (StackCodegen.StackOp (ℕ × Fin n) Float)) where
  l0l1 := identityTokenizer (ShallowCExpr n)
  l1l2 :=
    { encode := fun s => [s]
      decode := fun ts => ts.head?
      roundtrip := fun _ => rfl }
  l2l3 := fun e => StackCodegen.compileProg (Lattice.Geo.CExprCodegen.toStack e.val)
  satSym := fun e => ∀ pts : ℕ → Fin n → Float, CExpr.evalC e.val pts = g pts
  satW := fun w => ∀ (pts : ℕ → Fin n → Float) (seed : Float),
    StackCodegen.runProg (fun pa : ℕ × Fin n => pts pa.1 pa.2) w [seed]
      = some (g pts :: [seed])
  l2l3_sound := by
    intro e he pts seed
    -- the bridge: run the compiled program, get the tree's value
    -- 	oStack_correct no longer takes a depth hypothesis: CExpr.depth_eq_one makes it vacuous
    rw [Lattice.Geo.CExprCodegen.toStack_correct e.val pts seed]
    -- and `satSym` says the tree's value is `g`
    rw [he pts]

/-- **端到端**：符号侧对所有环境算出 `g` ⟹ 编译出的指令列表对所有环境与种子算出 `g`。 -/
theorem codegenLadder_forward {n : ℕ} (g : (ℕ → Fin n → Float) → Float)
    (e : ShallowCExpr n) (he : (codegenLadder g).satSym e) :
    (codegenLadder g).satW ((codegenLadder g).l2l3 e) :=
  Ladder.ladder_forward (codegenLadder g) e he

/-- **显式形式**（供阅读）：`satW` 确实是「对**所有**环境与**所有**种子」，不是单点。 -/
theorem codegenLadder_satW_iff {n : ℕ} (g : (ℕ → Fin n → Float) → Float)
    (w : List (StackCodegen.StackOp (ℕ × Fin n) Float)) :
    (codegenLadder g).satW w ↔
      ∀ (pts : ℕ → Fin n → Float) (seed : Float),
        StackCodegen.runProg (fun pa : ℕ × Fin n => pts pa.1 pa.2) w [seed]
          = some (g pts :: [seed]) :=
  Iff.rfl

/-- **`l2l3` 确实改变了表示**：符号侧是树，权重侧是指令列表。

这条是「不是重言」的结构性证据：两侧的类型不同，所以 `satSym` 与 `satW` 不可能展开成
同一个命题（对比 `MultiLayerLadder`，那里两侧都是 `List AffineLayer`）。 -/
theorem codegenLadder_l2l3_changes_representation {n : ℕ}
    (g : (ℕ → Fin n → Float) → Float) (e : ShallowCExpr n) :
    (codegenLadder g).l2l3 e = StackCodegen.compileProg (Lattice.Geo.CExprCodegen.toStack e.val) :=
  rfl

end Lattice.Lift
