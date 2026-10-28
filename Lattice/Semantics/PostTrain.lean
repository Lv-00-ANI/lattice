/-
# S10：`post_train_preserves` —— 后训练**不破坏**已经成立的东西

## 0. 这条义务到底该说什么

`SEMANTICS-MAINLINE.md` 的 S10 行写「后训练后约束保持/可修复」。
**「保持」与「可修复」是两件不同的事**，本条只做**保持**，并且要把它做成一条**有内容**的定理。

⚠ **容易写成空话的两种写法**：

1. 「后训练之后，目标约束仍可能成立」——那是存在性，等于没保证；
2. 「后训练之后约束可修复」——那要给出修复算子，而修复属于 `Repair` 层（已有），
   **不是后训练的性质**。

## 1. 本条的精确内容：**在解处，一步是恒等**

二次损失的梯度下降是**精确可解**的：`step η c β = β − η·2·(β + c)`。
于是

> **`β + c = 0`（约束已满足）⟹ `step η c β = β`（参数不动）**

**参数不动 ⟹ 整条配置不动 ⟹ 任何关于配置的命题都保持。**

所以本条的陈述**不是**关于某一条约束的，而是关于**任意谓词**的：

```lean
post_train_preserves : β + c = 0 → P (配置 β) → P (配置 (step η c β))
```

**这条比「某条约束仍成立」强得多**：它覆盖**所有**约束，包括**训练时根本没被优化**的那些。
那正是工程上要问的问题——**在 A 上训练会不会破坏 B**——答案是：**在解处不会，因为什么都没变。**

## 2. 为什么前提不能省：反面定理

若在**非解处**也声称「不破坏」，那是**假的**：此时 `step` 会移动参数。
本文件证 `step_changes_off_solution`：**`η ≠ 0` 且 `β + c ≠ 0` 时 `step η c β ≠ β`**。
所以「在解处」不是装饰性前提，**删掉它结论就是假**。

## 3. 边界

- **只在解处恒等**：`β + c = 0` 之外，一步**会**改变配置，所以可能破坏别的约束。
  **这是本条的真实范围，不是遗漏**——「训练不破坏任何东西」在一般情形下**不成立**。
- **只做一维线性约束**（`Fin 1` + `linearConstraint`），与 `ConstraintDescent` 同范围。
- **不做「可修复」**：修复算子属于 `Repair` 层。
- **`step` 的符号**：`netLoss = (β + c)²`，其导数是 `2(β + c)`，所以 `step η c β = β − η·2(β+c)`。 -/
import Mathlib
import Lattice.Core.Net
import Lattice.Domains.Geometry.ConstraintDescent
import Lattice.Domains.Constraints.ConstraintSet

namespace Lattice.Semantics.PostTrain

open Lattice.Core Lattice.Geo Lattice.Geo.ConstraintSet Lattice.Geo.ConstraintDescent

variable {η c β : ℝ} {pts : ℕ → Pt 1}

/-! ## 一、在解处一步是恒等 -/

/-- **约束已满足 ⟹ 一步不动参数。** 这正是「二次损失梯度下降精确可解」的直接后果：
`step η c β = β − η·2·(β + c)`，而 `β + c = 0`。 -/
theorem step_at_solution (h : β + c = 0) : step η c β = β := by
  unfold step
  rw [h]
  ring

/-- **在解处权重层不变**：`shiftLayer` 只读参数，参数不动则层不动。 -/
theorem shiftLayer_step_at_solution (h : β + c = 0) :
    shiftLayer (step η c β) = shiftLayer β := by
  rw [step_at_solution (η := η) h]

/-- **在解处整条配置不变。** -/
theorem config_step_at_solution (h : β + c = 0) :
    (fun k => netAct [shiftLayer (step η c β)] (pts k))
      = (fun k => netAct [shiftLayer β] (pts k)) := by
  rw [shiftLayer_step_at_solution (η := η) h]

/-! ## 二、S10：**任意**谓词都被保持 -/

/-- ⭐⭐ **S10 `post_train_preserves`**：在解处取一步，**任何关于配置的谓词**都保持。

**为什么是关于任意谓词而不是某条约束**：训练时我们只优化**一条**约束，
而工程问题恰恰是「优化 A 会不会破坏 B」。答案是：**在 A 已满足处不会，因为什么都没变。**
把这个事实陈述成「任意谓词都保持」，才是它的完整强度。 -/
theorem post_train_preserves (h : β + c = 0) (P : (ℕ → Pt 1) → Prop)
    (hP : P (fun k => netAct [shiftLayer β] (pts k))) :
    P (fun k => netAct [shiftLayer (step η c β)] (pts k)) := by
  rw [config_step_at_solution (η := η) (pts := pts) h]
  exact hP

/-- **推论：任意一条约束**（**包括训练时没被优化的那些**）在解处都被保持。 -/
theorem post_train_preserves_holds (h : β + c = 0) (c' : GeoConstraint 1)
    (hP : GeoConstraint.Holds c' (fun k => netAct [shiftLayer β] (pts k))) :
    GeoConstraint.Holds c' (fun k => netAct [shiftLayer (step η c β)] (pts k)) :=
  post_train_preserves (η := η) h _ hP

/-- **推论：整个约束集**在解处被保持。 -/
theorem post_train_preserves_set (h : β + c = 0) (G : List (GeoConstraint 1))
    (hG : HoldsSet G (fun k => netAct [shiftLayer β] (pts k))) :
    HoldsSet G (fun k => netAct [shiftLayer (step η c β)] (pts k)) :=
  post_train_preserves (η := η) h _ hG

/-! ## 三、前提是**必要的**：非解处一步会动参数 -/

/-- ⭐⭐ **反面定理：`η ≠ 0` 且约束未满足时，一步确实移动参数。**

**它证明 §二 的前提不是装饰**：删掉 `β + c = 0`，结论就是**假**——
在非解处一步会把配置改掉，所以「训练不破坏任何东西」**一般情形下不成立**。

**这也是本条的边界**：`post_train_preserves` 只在解处成立，而那正是它声称的范围。 -/
theorem step_changes_off_solution (hη : η ≠ 0) (h : β + c ≠ 0) : step η c β ≠ β := by
  intro heq
  have hzero : η * (2 * (β + c)) = 0 := by
    unfold step at heq
    linarith
  rcases mul_eq_zero.mp hzero with hη0 | h2
  · exact hη hη0
  · exact h (by linarith)

end Lattice.Semantics.PostTrain
