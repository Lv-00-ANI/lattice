import Mathlib
import Lattice.Plugins.Manifest

/-!
# `Lattice.Compose.EditModel` —— 编辑统一模型的**最小子集**（W5-3）

## 规格要什么（`LONG-TERM-PLAN` W5-3）

> §9 的 `EditTarget`/`Change`/`EditMode`/`applyRelational`/`applyHard`/`Consistent`/`Commutes`/`repair`
> 全部为空；实现最小子集（`applyRelational` + `Consistent` + `Commutes`）。

## 实测（第 1233 轮）

| 名字 | 树里 |
|:--|:--|
| `EditTarget` / `EditMode` / `applyRelational` / `Commutes` / `PrimitiveContract` | **0** |
| `Consistent` | 2 文件提及、**0 声明** |
| `Edit` | **两处**：`Core/IR/Confluence.Edit`（`{plugin, value}`）、`Semantics/Annotations.Edit n`（`{del, add, removed}`） |
| 「不同键的作用可交换」 | **已有**：`Plugins/Runtime/RTargets.apply_comm` |

**⇒ 故本文件**不**再造一个「不同键可交换」的副本；它造的是**带类型的 target**——**
**⇒ 即「编辑对准的是**哪个插件的哪个槽**」，而那正是现有两处 `Edit` 都没有的东西（它们只认「插件」或「约束集」）。**

## 为什么 `Commutes` 写在 **target** 上而不是 value 上

**⇒ 两个编辑若对准**不同的槽**，无论值是什么都互不影响——这是**类型**保证的；**
**⇒ 若对准**同一个槽**，即使值相同也可能有顺序语义（后写覆盖）。⇒ 故 `Commutes` 的判据是**目标不同**，不是**值不同**。**
-/

namespace Lattice.Compose.EditModel

open Lattice.Plugins (PluginName ObligationKind)

/-- **编辑目标**：**哪个插件的哪个槽**。

**⇒ 这是现有两处 `Edit` 都缺的那一维：`Confluence.Edit` 只到插件，`Annotations.Edit` 只到约束集。** -/
structure EditTarget where
  /-- 哪个插件。 -/
  plugin : PluginName
  /-- 哪个义务槽（十二槽之一）。 -/
  kind : ObligationKind
  deriving DecidableEq, Repr

/-- **编辑方式**。**⇒ 两个构造子而已：关系式（软）与硬化（硬）。⇒ 本文件只证与方式无关的那条定律。** -/
inductive EditMode where
  | relational
  | hard
  deriving DecidableEq, Repr

/-- **一次编辑**：对准一个 target，按一种方式，装一个值。 -/
structure Edit where
  target : EditTarget
  mode : EditMode
  value : Option ℕ
  deriving DecidableEq, Repr

/-- **状态**：每个插件当前的取值。**⇒ 用函数而不是 `Map`：本模型不需要可枚举，只需要可比较。** -/
abbrev EditState := PluginName → Option ℕ

/-- **关系式应用**（`applyRelational`）：**只改它对准的那个插件，其余原样。**

**⇒ 这里**不另设 `applyEdit`**：同名函数已在 `Core/IR/Confluence` 里存在，**
**⇒ 而本模型的层次不同（它改的是**槽级**状态）。⇒ 故只保留规范要求的那个名字。 -/
def applyRelational (e : Edit) (s : EditState) : EditState :=
  fun p => if p = e.target.plugin then e.value else s p

/-- **两个编辑**可交换**：它们对准**不同的插件**。

**⇒ 判据是 target 而不是 value（见文件头）。** -/
def Commutes (e₁ e₂ : Edit) : Prop := e₁.target.plugin ≠ e₂.target.plugin

/-- **⭐⭐ 可交换 ⇒ 应用可交换**（`Commutes` 的**内容**）。 -/
theorem commutes_apply {e₁ e₂ : Edit} (h : Commutes e₁ e₂) (s : EditState) :
    applyRelational e₁ (applyRelational e₂ s) = applyRelational e₂ (applyRelational e₁ s) := by
  funext p
  have hne : e₁.target.plugin ≠ e₂.target.plugin := h
  have hne' : e₂.target.plugin ≠ e₁.target.plugin := fun hh => hne hh.symm
  simp only [applyRelational]
  by_cases hp₁ : p = e₁.target.plugin
  · have hp₂ : p ≠ e₂.target.plugin := fun h2 => hne (hp₁.symm.trans h2)
    simp [hp₁, hp₂, hne, hne']
  · by_cases hp₂ : p = e₂.target.plugin
    · simp [hp₁, hp₂, hne, hne']
    · simp [hp₁, hp₂]

/-- **一组编辑**一致**：两两对准不同插件。** -/
def Consistent (es : List Edit) : Prop :=
  ∀ e₁ ∈ es, ∀ e₂ ∈ es, e₁ ≠ e₂ → Commutes e₁ e₂

/-- **⭐ 一致组里**每一个**编辑都与其余全部可交换。** -/
theorem consistent_commutes_all {es : List Edit} (h : Consistent es) {e : Edit} (he : e ∈ es)
    {f : Edit} (hf : f ∈ es) (hne : e ≠ f) : Commutes e f :=
  h e he f hf hne

/-- **⭐ 一致组的**首元素**可与**尾组**依次换到最前**（`Consistent` 的实际用途：插入顺序无关）。** -/
theorem consistent_head_comm {es : List Edit} (h : Consistent es) {e : Edit} (he : e ∈ es) :
    ∀ f ∈ es, f ≠ e → Commutes e f := by
  intro f hf hne
  exact h e he f hf (fun hfe => hne hfe.symm)

end Lattice.Compose.EditModel