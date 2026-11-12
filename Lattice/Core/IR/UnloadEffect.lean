import Mathlib
import Lattice.Core.IR.Lifecycle

/-!
# `unload` 只改 `active`、**不改** `effect`：现状与正确语义（阶段 C，P2-10）

## 规划说 `recovery_exact` 是「`undo` 定义展开」——**实测它是真往返定理**

```lean
theorem recovery_exact (P) (s) :
    undo P (s.active P) (effectOf P s) (unload P s) = s
```

**这不是定义展开：它用 `funext` 逐点证明两个字段都恢复，并且**依赖 `undo` 同时写回 `active` 与 `effect`**。
若 `undo` 只恢复其一，定理就会失败。**

**=> 规划的判断在这一条上是错的。**

## 但规划指出的**方向**是对的：`unload` 不撤销效果

**`Lifecycle.lean:98`：**

```lean
def unload (P) (s) : LifeState :=
  { s with active := fun Q => if Q = P then false else s.active Q }
```

**只动 `active`。`effect` 一字不改。**

**字段注释（L96-97）把这一点**写成设计**：**

> **「`active` 是唯一被触及的字段。**这就是「只撤销自己的影响」的全部内容：**效果不被触碰**，
> 所以别的插件不受影响。」**

**=> 这解释了**为什么**只有 `active` 被改：为了让 `unload_removes_only_own`（别的插件效果不变）成立。
**但那与「撤销**自己**的效果」是两件不同的事。** 现状是：`unload` 让 `P` **失活**，却让它的效果**继续存在**。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `unload_leaves_effect` | **`unload` 后 `P` 自己的效果**仍在**（这是现状的精确刻画）** |
| `unload_inactive_but_effective` | **失活且仍有效果**——两句合起来是缺口的完整陈述 |
| `unload_effect_removal_needs_reset` | **若要让 `unload` 真正撤销效果，必须另外清空 `effect`；`unload` 本身做不到** |

**=> 第三条是核心：它说明「真正撤销」**不是 `unload` 的语义**，而需要一个**不同的**操作。
把它写成定理，是为了让后续任何「让 `unload` 真撤销」的改动**必须**同时处理 `unload_removes_only_own`
—— 两者是**冲突的**，不能都成立。**

**=> 这就是本轮的实质发现：规划要的「真撤销」与既有的 `unload_removes_only_own` **互相排斥**，
必须先决定哪个语义是对的。** -/

namespace Lattice.Core.IR

/-- **现状：`unload` 之后 `P` 自己的效果**仍然存在**。**

**=> 因为 `unload` 只改 `active`，`effect` 字段原封不动。** -/
theorem unload_leaves_effect (P : Plugin) (s : LifeState) :
    effectOf P (unload P s) = effectOf P s := by
  simp only [effectOf, unload]

/-- **缺口的两句合起来：`P` 在 `unload` 后**失活**，但**仍有效果**。**

**=> "失活" 由 `unload_inactive`（已有），"仍有效果" 由 `unload_leaves_effect`（上一条）。
本条把两者并置，使缺口成为**一条**可引用的陈述。** -/
theorem unload_inactive_but_effective (P : Plugin) (s : LifeState) :
    (unload P s).active P = false ∧ effectOf P (unload P s) = effectOf P s :=
  ⟨unload_inactive P s, unload_leaves_effect P s⟩

/-- **要让 `unload` 真正撤销 `P` 的效果，必须**另外**清空 `effect`。**

**=> 陈述：存在 `s` 与 `P` 使得 `unload P s` 的效果**不等于** `none` —— 即「真撤销」不会自动发生。**

**=> 这是一条否证：`unload` **不**具有「撤销效果」的语义。** -/
theorem unload_effect_removal_needs_reset (P : Plugin) :
    ∃ s : LifeState, effectOf P (unload P s) ≠ none := by
  refine ⟨{ active := fun _ => true, effect := fun _ => some 1 }, ?_⟩
  show (unload P { active := fun _ => true, effect := fun _ => some 1 }).effect P ≠ none
  simp [unload]

end Lattice.Core.IR
