import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Core.IR.Chain

/-!
# **官方展品 M-3：符号捷径——知识 → L2 → 权重，**不经过 token**（阶段 V）

## 这个展品展示什么

**M-1 走的是数据 → token → 符号；M-4 走的是符号 → token → 符号的回程。**
**=> 两者都**必须经过 token**。**

**M-3 是**另一条路**：从符号知识（`Term`）直接 `parse` 到 L2（`IRSkeleton`），
再 `compileSkel` 到 L3（`IRWeights`）——**token 层完全不出现**。**
**这正是 `README.md` 链路图里那条「符号捷径」的第一次可引用实现。**

## 上轮预判的障碍**不存在**——而原因值得记录

**我在上一轮计划里写：「`parse` 不是 `Option`，所以要做成 `Primitive` 必须先定失败语义」。**

**⇒ 实测后发现：`parse : Term → IRSkeleton` **是全函数**（`Parse.lean:170`），它**不会失败**。**

**=> 所以「失败语义」这个设计决策根本不需要做：`pre := True` 就是**正确答案**，
而不是一个回避。**

**这与 M-1 的 `tokenizeV` 恰成对照：**

| 阶段 | 返回类型 | `pre` | 结论 |
|:--|:--|:--|:--|
| `tokenizeV`（M-1） | `Option` | `(tokenizeV V s).isSome` | **可能失败 ⇒ 前置条件收窄** |
| **`parse`（M-3）** | **`IRSkeleton`** | **`True`** | **全函数 ⇒ 前置条件不收窄** |

**=> 三张展品（M-1、M-3、M-4）合起来把同一条原则的三个可能答案都走了一遍：
可能失败、全函数（可计算）、全函数（不可计算）。**

## 一个必须明写的边界

**`compileSkel` 是 `noncomputable`（它把 `skeletonCode k : ℕ` 强制成 `ℝ`）。**
**=> 本文件的 `compileSkelPrim` 因此也是 `noncomputable`。**
**=> 这不影响它作为 `Primitive`：`Primitive.run` 只是一个字段，不要求可计算。**
**但这意味着 **M-3 和 M-4 的可执行性不同**：M-4 的两个阶段都是可计算的，M-3 的第二段不是。**

**⇒ 这是「可执行边界」（`STATE-FINAL §3.1`）在这里的一个具体落点，而不是一句抽象的话。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`parsePrim`** | **⭐⭐ 知识 → L2，全函数** |
| **`compileSkelPrim`** | **⭐⭐ L2 → 权重，全函数（不可计算）** |
| **`symbolShortcut`** | **⭐⭐⭐ 用 `compose` 合成的捷径：`Term → IRWeights`** |
| **`symbolShortcut_run`** | **⭐⭐⭐ 捷径的 `run` 等于 `some (compileSkel (parse t))`** |
| **`symbolShortcut_sound`** | **⭐⭐ 合成的 `sound`** | -/

namespace Lattice.Compose.Showcase.SymbolShortcut

open Lattice.Compose

/-- **⭐⭐ 知识 → L2：`parse` 做成 `Primitive`。**

**`parse` 是**全函数**（`Parse.lean:170`），故 `pre := True`——不是回避，是事实。** -/
def parsePrim : Primitive Lattice.Core.CIC.Term Lattice.Core.IR.IRSkeleton where
  pre := fun _ => True
  post := fun t k => Lattice.Core.IR.parse t = k
  run := fun t => some (Lattice.Core.IR.parse t)
  sound := by
    intro t _
    exact ⟨Lattice.Core.IR.parse t, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐ L2 → 权重：`compileSkel` 做成 `Primitive`。**

**⚠ `compileSkel` 是 `noncomputable`（把 `skeletonCode k : ℕ` 强制成 `ℝ`），
故本定义亦 `noncomputable`。这与 M-4 的两段都可计算形成对照。** -/
noncomputable def compileSkelPrim :
    Primitive Lattice.Core.IR.IRSkeleton Lattice.Core.IR.IRWeights where
  pre := fun _ => True
  post := fun k W => Lattice.Core.IR.compileSkel k = W
  run := fun k => some (Lattice.Core.IR.compileSkel k)
  sound := by
    intro k _
    exact ⟨Lattice.Core.IR.compileSkel k, rfl, rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ 符号捷径：`parse` 之后 `compileSkel`，**token 层不出现**。**

**合成条件是「解析的后置蕴含编译的前置」——编译的前置是 `True`，故平凡成立。** -/
noncomputable def symbolShortcut :
    Primitive Lattice.Core.CIC.Term Lattice.Core.IR.IRWeights :=
  compose parsePrim compileSkelPrim (by
    intro t k _
    trivial)

/-- **⭐⭐⭐ 展品的核心：捷径的 `run` 就是 `compileSkel ∘ parse`。**

**=> 这条把「用 `Compose` 组合出来的捷径」与「手写的 `compileSkel (parse t)`」**证明地**等同起来。** -/
theorem symbolShortcut_run (t : Lattice.Core.CIC.Term) :
    symbolShortcut.run t = some (Lattice.Core.IR.compileSkel (Lattice.Core.IR.parse t)) := by
  show (some (Lattice.Core.IR.parse t)).bind
      (fun k => some (Lattice.Core.IR.compileSkel k)) = _
  rfl

/-- **⭐⭐ 捷径的 `sound`：对任意知识，捷径产出且后置成立。** -/
theorem symbolShortcut_sound (t : Lattice.Core.CIC.Term) (hs : symbolShortcut.pre t) :
    ∃ z, symbolShortcut.run t = some z ∧ symbolShortcut.post t z :=
  symbolShortcut.sound t hs

end Lattice.Compose.Showcase.SymbolShortcut
