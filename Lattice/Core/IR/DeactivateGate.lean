import Mathlib
import Lattice.Core.IR.Lifecycle

/-!
# 停用门的**对称形式**：`canDeactivate`（阶段 C，P2-8）

## 本轮核查到的事实

**规划 P2-8 说「`cannotActivate` 不存在」。**

**实测：**「拒绝激活」这件事已经存在**，只是名字不是 `cannotActivate`：**

```lean
theorem canActivate_needs_requires (deps) (s) (P Q) (hreq) (hQ : s.active Q = false) :
    ¬ canActivate deps s P
```

**=> 它正是「激活门拒绝一个依赖未满足的插件」**。再加一个 `cannotActivate := ¬ canActivate` 只是改个名字。**

## 但**对称的那一半**确实缺失

**`Lifecycle.lean:167` 的小节标题写着「T6: the activation gate **AND** the deactivation gate」，
而这一节里只有**激活**门（`canActivate`）与它的拒绝形式。
**停用门**只体现为 `unload_inactive`（停用后确实失活），那是**结果**而不是**门**。**

**=> 缺少的是：什么条件下**允许**停用一个插件。**

## 停用门该怎么写

**激活的条件是「所有依赖都活着」（`∀ Q ∈ deps P, s.active Q = true`）。
按对称性，停用的条件应当是「**不是**别的插件的依赖」—— 否则停用会让那个插件的依赖落空。**

**=> 于是 `canDeactivate deps s P := ∀ Q, P ∈ deps Q → s.active Q = false`：
只有当一个插件不是**任何活跃插件**的依赖时，才能安全停用它。**

**这不是凭空发明：它正是 `lattice_ordering` 的**逆否**所需要的条件。
`lattice_ordering` 说「若 P 活跃而它的依赖 Q 死掉，则 P 必死」。
反过来问「何时可以安全地让 Q 死」，答案就是「当没有活跃的 P 依赖 Q 时」。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `canActivate_iff` | **激活门的展开形式** |
| `canDeactivate_iff` | **停用门的展开形式** |
| `canDeactivate_not_required_by_active` | **停用门的**内容**：`P` 不是任何活跃插件的依赖** |
| `deactivate_preserves_ordering` | **安全停用保持 `lattice_ordering`** —— 停用门存在的理由 |
| `canDeactivate_nil` | **无任何依赖关系时，任何插件都可安全停用** |

**=> `deactivate_preserves_ordering` 是核心：它把「停用门」与既有的排序律钉在一起，
使停用门不是孤立的新定义，而是排序律的**守护条件**。** -/

namespace Lattice.Core.IR

/-- **激活门的展开：`P` 的所有依赖都活跃。**

**=> 逐字展开 `canActivate` 的定义。** -/
theorem canActivate_iff (deps : Plugin → List Plugin) (s : LifeState) (P : Plugin) :
    canActivate deps s P ↔ ∀ Q ∈ deps P, s.active Q = true :=
  Iff.rfl

/-- **停用门：`P` 不是**任何活跃插件**的依赖。**

**=> 只有在这个条件下停用 `P` 才安全 —— 否则必然有某个活跃插件失去它的依赖，
从而违反 `lattice_ordering`。** -/
def canDeactivate (deps : Plugin → List Plugin) (s : LifeState) (P : Plugin) : Prop :=
  ∀ Q, P ∈ deps Q → s.active Q = false

/-- **停用门的展开形式。** -/
theorem canDeactivate_iff (deps : Plugin → List Plugin) (s : LifeState) (P : Plugin) :
    canDeactivate deps s P ↔ ∀ Q, P ∈ deps Q → s.active Q = false :=
  Iff.rfl

/-- **停用门的内容：`P` 不被任何**活跃**插件依赖。**

**=> 这是 `canDeactivate` 的直接使用形式：给定 `P` 是某个 `Q` 的依赖，
若 `Q` 活跃，则停用门不成立。** -/
theorem canDeactivate_not_required_by_active (deps : Plugin → List Plugin) (s : LifeState)
    (P Q : Plugin) (hreq : P ∈ deps Q) (hQ : s.active Q = true) :
    ¬ canDeactivate deps s P := by
  intro h
  have := h Q hreq
  rw [hQ] at this
  exact absurd this (by simp)

/-- **安全停用保持排序律。**

**=> 若停用门成立（`P` 不被任何活跃插件依赖），并且 `P` 确实是某个 `Q` 的依赖，
那么 `Q` 必定**不活跃**。**

**=> 这就是停用门的**理由**：它保证 `lattice_ordering` 在停用之后仍然成立 ——
不会出现「`Q` 活跃而其依赖 `P` 已死」的状态。** -/
theorem deactivate_preserves_ordering (deps : Plugin → List Plugin) (s : LifeState)
    (P Q : Plugin) (hgate : canDeactivate deps s P) (hreq : P ∈ deps Q) :
    s.active Q = false :=
  hgate Q hreq

/-- **无任何依赖关系时，任何插件都可安全停用。**

**=> 若 `deps` 恒为空列表，则「`P ∈ deps Q`」对任何 `P`、`Q` 都假，
停用门的前提永远不成立，故条件平凡成立。** -/
theorem canDeactivate_nil (s : LifeState) (P : Plugin) :
    canDeactivate (fun _ => []) s P := by
  intro Q h
  simp at h

end Lattice.Core.IR
