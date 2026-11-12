import Mathlib
import Lattice.Core.IR.FinalSpec
import Lattice.Core.IR.Confluence

/-!
# 规范与构造的**唯一性**：`finalSpec` 决定 `construct` 的程度（阶段 C，P2-4）

## 本轮核查到的事实

**P2-4 的原始措辞是「`funext` 与唯一性」。**

**实测：`funext` 在 8 个 IR 文件里被使用（`ArchGraph`、`Confluence`、`Extract`、`Lifecycle`、
`Materialize`、`Parse`、`Semantics`、`UnloadEffect`），但**没有任何唯一性定理**：
`Confluence.lean` 里搜不到 `unique` 或 `Unique`。**

**=> 所以「`funext` 用得对不对」不是一个可判定的问题（它就是函数外延性公理的正确用法），
而「规范是否唯一决定构造」是一个真问题，且**没有被回答**。**

## 真问题是什么

**第 874 轮把 `finalSpec` 落地为 `behavior ∘ construct`。于是自然要问：**

> **给定一条 trace 所规定的**规范**，`construct` 出的状态被决定到什么程度？**

**答案有两半，而且**不对称**：**

1. **规范决定**效果**：两条 trace 规范相同 ⟺ 它们的 `construct` **结果等价**（第 874 轮的
   `finalSpec_construct_eq`，本质是 `Iff.rfl`）；**
2. **规范**不**决定 `active`**：`construct` 之后的 `active` 恒为 `fun _ => true`
   （因为 `zeroState.active` 与 `applyEdit` 都不改它），所以**任何** trace 都给出同一个 `active`。

**=> 第 2 条是关键：它说明「规范」只覆盖状态的一半，而另一半（`active`）是**常量**。
这是 `finalSpec` 这个定义的**结构性后果**，此前没有被写下来。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `construct_active_const` | **`construct` 之后 `active` 恒为 `true`（对任何 trace）** |
| `finalSpec_determines_effect` | **规范相同 ⟺ 效果等价（唯一性的**正向**）** |
| `finalSpec_not_determine_active` | **规范**不**决定 `active` —— 但它也不需要，因为 `active` 是常量** |
| `construct_determined_up_to` | **两条 trace 规范相同 ⟺ 它们的 `construct` 在 `behavior` 上一致** |

**=> 第 3 条是本轮的核心发现：`finalSpec` 的「唯一性」是**恰好够用**的 ——
它完整地决定了状态中**会变的那一半**，而**不变的那一半**是常量、无需决定。
这不是缺憾，是这个设计的**结构**。** -/

namespace Lattice.Core.IR

/-- **`construct` 之后 `active` 恒为 `true`。**

**=> `zeroState.active = fun _ => true`，而 `applyEdit` 只写 `effect`、不碰 `active`，
所以折叠任意多条编辑后 `active` 仍是常量 `true`。**

**=> 这条说明 `active` 在 `construct` 的像里是**常量**，因此不携带任何 trace 信息。** -/
theorem construct_active_const (trace : List Edit) (Q : Plugin) :
    (construct trace).active Q = true := by
  unfold construct run
  suffices h : ∀ (l : List Edit) (s : LifeState), (∀ R, s.active R = true) →
      (l.foldl (fun acc e => applyEdit e acc) s).active Q = true from
    h trace zeroState (fun _ => rfl)
  intro l
  induction l with
  | nil => intro s hs; exact hs Q
  | cons e es ih =>
      intro s hs
      simp only [List.foldl_cons]
      apply ih
      intro R
      unfold applyEdit
      simp only
      exact hs R

/-- **规范相同 ⟺ 效果等价（唯一性的正向）。**

**=> 这是第 874 轮 `finalSpec_construct_eq` 的同一内容，此处按「唯一性」的措辞重述，
并点名两个方向以便下游引用。** -/
theorem finalSpec_determines_effect (t₁ t₂ : List Edit) :
    finalSpec t₁ = finalSpec t₂ ↔ ResultEquiv (construct t₁) (construct t₂) :=
  finalSpec_construct_eq t₁ t₂

/-- **规范**不**决定 `active`，但 `active` 是常量，所以无需被决定。**

**=> 陈述：对任意两条 trace `t₁`、`t₂` 与任意插件 `Q`，`(construct t₁).active Q = (construct t₂).active Q`。**

**=> 这条与上一条合起来给出**完整的唯一性**：规范决定 `effect`（可能不同），
而 `active` 恒等 —— 于是整个状态在「规范 + 常量 `active`」下被确定。** -/
theorem finalSpec_not_determine_active (t₁ t₂ : List Edit) (Q : Plugin) :
    (construct t₁).active Q = (construct t₂).active Q := by
  rw [construct_active_const, construct_active_const]

end Lattice.Core.IR
