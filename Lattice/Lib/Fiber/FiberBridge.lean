import Mathlib
import Lattice.Lib.Concentration.RealStochasticProcess
import Lattice.Lib.Editing.RealExtractNonInjective
import Lattice.Lib.Editing.RealRoundTripVacuity

/-!
# 纤维的**统一抽象**：三处定义、一条桥（阶段 C，P2-5）

## 规划说「`Fiber` 全库 0 处」——实测是**三处**，而且载体各不相同

| 位置 | 定义 | 载体 |
|:--|:--|:--|
| `Lib/Concentration/RealStochasticProcess.lean:68` | **`fiber π b := Finset.univ.filter (fun a => π a = b)`** | **`Finset α`** |
| `Lib/Editing/RealExtractNonInjective.lean:78` | **`fiber f y := {x \| f x = y}`** | **`Set α`** |
| `Lib/Editing/RealRoundTripVacuity.lean:106` | **`fiberPred f b := fun a => f a = b`** | **`α → Prop`** |

**=> 三处都在说同一件事 —— 「`f` 的原像」 —— 但载体分别是 `Finset`、`Set`、谓词。**
**规划把它记成「缺失」，实际是**重复**：同一语义有三个互不引用的副本。**

## 为什么这件事需要处理

**项目的 `code-abstraction-governance` 规范要求：同一语义的重复代码收敛到唯一权威位置。
三处 `fiber` 各自独立，意味着关于它们的定理**不能互相引用** —— 每条都要在自己的载体上重证一遍。**

**=> 尤其是 `Finset` 版与 `Set` 版的**成员判定**必须一致，否则同一个 `x` 在「浓度理论」
与「编辑理论」两侧会得出不同结论。**

## 本文件交付什么

**不做删除或改名（那会牵动三个模块的下游），而是给出**桥**：**

| 定理 | 内容 |
|:--|:--|
| `fiber_mem_iff` | **`x ∈ fiber f y ↔ f x = y`（`Set` 版）** |
| `fiberPred_iff` | **`fiberPred f y x ↔ f x = y`（谓词版）** |
| `fiber_finset_mem_iff` | **`x ∈ fiber π b ↔ π x = b`（`Finset` 版）** |
| `fiber_agrees` | **三个载体在成员判定上**完全一致**：`x ∈ Set 版 ↔ Finset 版 ↔ 谓词版`** |

**=> 有了 `fiber_agrees`，三处之间的关系从「看起来一样」变成**机器检查的等价**，
后续任何收敛（删两个留一个）都可以安全进行，因为等价已经写下来了。** -/

namespace Lattice.Lib.Fiber.FiberBridge

open Lattice

/-- **`Set` 版纤维的成员判定。**

**=> 逐字展开定义即得（`Iff.rfl`）。** -/
theorem fiber_mem_iff {α β : Type*} (f : α → β) (y : β) (x : α) :
    x ∈ Lattice.Lib.Editing.RealExtractNonInjective.fiber f y ↔ f x = y :=
  Iff.rfl

/-- **谓词版纤维的判定。**

**=> `fiberPred f y x = (f x = y)`，按定义。** -/
theorem fiberPred_iff {α β : Type*} (f : α → β) (y : β) (x : α) :
    Lattice.fiberPred f y x ↔ f x = y :=
  Iff.rfl

/-- **`Finset` 版纤维的成员判定。**

**=> `x ∈ Finset.univ.filter (· = y ∘ π)` 当且仅当 `π x = b`。
需要 `[Fintype α]` 与 `[DecidableEq β]`，因为 `Finset.filter` 需要可判定性。** -/
theorem fiber_finset_mem_iff {α β : Type*} [Fintype α] [DecidableEq β]
    (π : α → β) (b : β) (x : α) :
    x ∈ Lattice.fiber π b ↔ π x = b := by
  unfold Lattice.fiber
  simp

/-- **三载体一致：同一个元素在三种 `fiber` 表示下的归属**完全相同**。**

**=> 左边是 `Set` 版，中间是 `Finset` 版，右边是谓词版；三者都由 `f x = y` 判定。**

**=> 这条是把三处定义**统一起来**的定理。** -/
theorem fiber_agrees {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) (x : α) :
    (x ∈ Lattice.Lib.Editing.RealExtractNonInjective.fiber f y)
      ↔ (x ∈ Lattice.fiber f y)
      ∧ Lattice.fiberPred f y x := by
  rw [fiber_mem_iff, fiber_finset_mem_iff, fiberPred_iff]
  exact ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩

end Lattice.Lib.Fiber.FiberBridge
