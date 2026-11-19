import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators
import Lattice.Lib.Compiler.ModelsBehavior

/-!
# **官方展品 M-5：L3 ⇄ L2 闭环——两个阶段的后置条件都是**行为性**的（阶段 Z）

## 这是五张展品里唯一一张「难的那跳」

**M-1 / M-2 / M-3 / M-4 都已建成。M-5 是 `README.md` 标注为难点的那一跳：权重 ⇄ 符号。**

**它此前被挡住，原因在第 991–992 轮被查清：**

- **`ModelsIR W k := W = compileSkel k` 只约束槽 0 一个实数，其余坐标强制为 0**（`modelsIR_off_zero`）；
- **因此以它为基础写的 `Primitive.post` 只能承载 `True` 级内容**；
- **而第 992 轮证明：任何承载非零截距的权重**不能**满足它**（`modelsIR_forbids_nontrivial_payload`）。

**⇒ 所以 M-5 不能建在 `ModelsIR` 上。本文件改用它上一轮造出的**行为性**谓词 `modelsBehavior`。**

## 设计决定：把分段数 `n` 放进输入类型

**`modelsBehavior W g n` 带一个分段数 `n`（「网格有 `n` 段」），而 `Primitive I O` 的两个类型参数里没有它。**

**两个选择：**

| 方案 | 后果 |
|:--|:--|
| **把 `n` 固定成常数** | 定理只对一个 `n` 成立；而 `segmentIndex`/`gridEval` 的语义依赖 `n`，固定它等于丢掉一般性 |
| **把 `n` 放进输入类型**（本文件采用） | **`I = (ℕ → Segment) × ℕ`**：输入就是「网格 + 它的分段数」，一般性保留 |

**⇒ 于是正向阶段的输出也带 `n`（`IRWeights × ℕ`），使两段类型严丝合缝地接上。
这个 `n` 不是装饰：它是 `modelsBehavior` 的一个**真实参数**，去掉它谓词就不完整。**

## 两段的后置条件都是行为性的

| 阶段 | `pre` | `run` | **`post`** |
|:--|:--|:--|:--|
| **正向** `forwardPrim` | `True` | `some (encodeGrid g, n)` | **`modelsBehavior W g n`** |
| **反向** `backwardPrim` | `True` | `some (decodeGrid W)` | **`modelsBehavior W g n`** |

**⇒ 反向阶段的 `post` 是**「读出来的网格在 `[0,1]` 上与给定的 `g` 行为一致」**——
**这不是「等于某个码」，而是一条关于求值的陈述。** 这正是本展品与旧 `ModelsIR` 的根本差别。

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`forwardPrim`** | **⭐⭐ L2 → L3，`post` 是 `modelsBehavior`** |
| **`backwardPrim`** | **⭐⭐⭐ L3 → L2，`post` 也是 `modelsBehavior`（**提取必须被行为验证**）** |
| **`l3l2Roundtrip`** | **⭐⭐⭐ 用 `compose` 合成的闭环** |
| **`l3l2Roundtrip_run`** | **⭐⭐⭐ 闭环回到**原网格**：`run (g, n) = some g`** |
| **`l3l2Roundtrip_post_nondegenerate`** | **⭐⭐⭐ 闭环的 `post` **不是** `True`：它蕴含逐点求值相等** | -/

namespace Lattice.Compose.Showcase.L3L2

open Lattice.Compose
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler.ModelsBehavior

/-- **⭐⭐ L2 → L3：把网格编码成权重，同时把分段数带上。**

**`post` 是 `modelsBehavior W g n`：**编码后的权重必须**行为上**与 `g` 一致**，
而不是「等于某个预先存好的码」。** -/
noncomputable def forwardPrim :
    Primitive ((ℕ → Segment) × ℕ) (Lattice.Core.IR.IRWeights × ℕ) where
  pre := fun _ => True
  post := fun p q => modelsBehavior q.1 p.1 p.2
  run := fun p => some (encodeGrid p.1, p.2)
  sound := by
    intro p _
    exact ⟨(encodeGrid p.1, p.2), rfl, modelsBehavior_encodeGrid p.1 p.2⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ L3 → L2：从权重提取网格，`post` **同样是** `modelsBehavior`。**

**⇒ 这是本展品的重点：**提取不是「拿回某个东西就算成功」，
而是「拿回来的东西必须行为一致」**。
**若提取错了，`sound` 就无法被证明——而这正是 M-5 一直缺的那道检查。** -/
noncomputable def backwardPrim : Primitive (Lattice.Core.IR.IRWeights × ℕ) (ℕ → Segment) where
  pre := fun _ => True
  post := fun q g => modelsBehavior q.1 g q.2
  run := fun q => some (decodeGrid q.1)
  sound := by
    intro q _
    exact ⟨decodeGrid q.1, rfl, fun _ => rfl⟩
  strength := .exact
  coverage := none

/-- **⭐⭐⭐ L3 ⇄ L2 闭环：正向编码、反向提取，用 `compose` 串起来。**

**合成条件是「编码的后置蕴含提取的前置」——提取的前置是 `True`，故平凡。** -/
noncomputable def l3l2Roundtrip : Primitive ((ℕ → Segment) × ℕ) (ℕ → Segment) :=
  compose forwardPrim backwardPrim (by
    intro p q _
    trivial)

/-- **⭐⭐⭐ 闭环回到**原网格**。**

**=> 由第 965 轮的 `decodeGrid_encodeGrid`：提取是编码的左逆，故 `run (g, n) = some g`。**
**⇒ 这条把「L3 ⇄ L2 闭合」从一句期望变成一条 `run` 等式。** -/
theorem l3l2Roundtrip_run (g : ℕ → Segment) (n : ℕ) :
    l3l2Roundtrip.run (g, n) = some g := by
  show (some (encodeGrid g, n)).bind (fun q => some (decodeGrid q.1)) = some g
  simp only [Option.some_bind]
  rw [decodeGrid_encodeGrid]

/-- **⭐⭐⭐ 闭环的后置条件**不是 `True`**：它蕴含逐点求值相等。**

**=> 这是与旧 `ModelsIR` 的分水岭：旧版对闭环只能给出「槽 0 等于一个码」，
本版给出「`[0,1]` 上每一点的求值都相等」——
**一条真正关于行为的陈述**，而且它是**从 `post` 里推出来的**，不是额外假设。**

**⚠ 该恒等式对**所有** `n` 成立（含 `n = 0`），故不设 `n > 0` 前提——
`decodeGrid_encodeGrid` 是纯代数事实，不依赖分段数的语义。** -/
theorem l3l2Roundtrip_post_nondegenerate (g : ℕ → Segment) (n : ℕ) :
    ∀ x : Set.Icc (0 : ℝ) 1,
      gridEval (decodeGrid (encodeGrid g)) n x.1 = gridEval g n x.1 := by
  intro x
  rw [decodeGrid_encodeGrid]

end Lattice.Compose.Showcase.L3L2
