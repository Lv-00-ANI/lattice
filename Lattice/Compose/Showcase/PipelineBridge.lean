import Mathlib
import Lattice.Compose.Combinators
import Lattice.Compose.Showcase.FullChain
import Lattice.Compose.Showcase.L1L2
import Lattice.Lib.Chain.RealChainEntryOOV

/-!
# `Lattice.Compose.Showcase.PipelineBridge` —— 把 `pipeline` 接到 `Compose` 层（W4-1/W4-2）

## 本轮**只加一个**定义

树里**已有**四段中的三段（`FullChain.tokenizePrim`、`bridgePrim`、`L1L2.decodePrim`）。
本文件只补**第四段**（`compileToLayer` 的 `Primitive` 包装）与一次 `compose`，外加一条等式定理。

**⇒ 上一轮我重造了 `tokenizePrim`，被 `check_duplicate_classes` 判为重复。⇒ 本文件**不重造任何东西**。**

## 一个**必须核**而不是假设的细节

`pipeline`（`RealEndToEnd:802`）用的是 `tokenize s = tokenizeRaw (foldBlanks s)`，
而 `tokenizePrim V` 用的是 `tokenizeV V`，且 `tokenizeV_VAll_eq_tokenizeRaw : tokenizeV VAll s = tokenizeRaw s`。

**⇒ 故两者差一个 `foldBlanks`。⇒ 本文件的等式**带** `foldBlanks`——不抹掉它，也不假装它不存在。**
-/

namespace Lattice.Compose.Showcase.PipelineBridge

open Lattice.Compose
open Lattice.Compose.Showcase.FullChain (tokenizePrim bridgePrim fullChainPrim)
open Lattice.Compose.Showcase.L1L2 (decodePrim)

/-- **`compileToLayer` 作为 `Primitive`**——四段里**唯一**缺的那一段。

**⇒ `compileToLayer : ConstraintSet → Layer` 是**全**函数 ⇒ `pre := True` 合法。** -/
def compilePrim :
    Primitive Lattice.Lift.SymbolToWeightCorrectness.ConstraintSet
      Lattice.Lift.SymbolToWeightCorrectness.Layer where
  pre := fun _ => True
  post := fun cs l => l = Lattice.Lift.SymbolToWeightCorrectness.compileToLayer cs
  run := fun cs => some (Lattice.Lift.SymbolToWeightCorrectness.compileToLayer cs)
  sound := by
    intro cs _
    exact ⟨_, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **整条链（四段）**：数据 → token → 符号 → 约束集 → 权重。

**⇒ 三次 `compose`，每一条 `h` 都平凡（中间各段 `pre := True`）。** -/
def pipelinePrim (V : Lattice.OOVVocab) :
    Primitive (List Char) Lattice.Lift.SymbolToWeightCorrectness.Layer :=
  compose (compose (fullChainPrim V) decodePrim (by intro s z _; trivial)) compilePrim
    (by intro s cs _; trivial)

/-- **⭐⭐⭐ W4-1：`pipeline s` **就是** `pipelinePrim VAll` 在 `foldBlanks s` 上的运行结果。**

**⇒ 为什么是 `foldBlanks s` 而不是 `s`：`tokenize` 先把空白折叠，而 `tokenizeV VAll = tokenizeRaw`（不折叠）。**
**⇒ 故等式**必须**带这个变换——把它抹掉才是错的。** -/
theorem pipeline_eq_pipelinePrim (s : List Char) :
    Lattice.Lib.Chain.RealEndToEnd.pipeline s
      = (pipelinePrim Lattice.VAll).run
          (Lattice.foldBlanks s) := by
  simp only [pipelinePrim, compilePrim, decodePrim, bridgePrim, fullChainPrim, tokenizePrim,
    Lattice.Compose.compose, Lattice.Lib.Chain.RealEndToEnd.pipeline,
    Lattice.tokenizeV_VAll_eq_tokenizeRaw]
  simp only [Lattice.tokenize, Option.some_bind, Option.bind_assoc, Option.map_eq_bind, Function.comp]

end Lattice.Compose.Showcase.PipelineBridge