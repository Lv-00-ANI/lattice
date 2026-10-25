/-
# LATTICE: RealOpContract — T3 未命名算子契约（包装入库）

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）
> 入库最低线：外延 + tag + 可选语义等式 + 可选展开 + 证书句柄。
> 打包不改外延；补名不破坏 T1 闭环。

## 诚实边界（**标注**）

1. ⭐ **本文件不提供实现对象** —— `semantic := none` 合法，故它**未做**「补上实现」这件事；
   它的价值是把「待实现」**形式化**为一个可入库的契约，而**不是**解决实现缺口。
2. ⭐ `cert : Option String` 是**证书句柄**，**未证**其内容；复验在外部流程（**留待**）。
3. ⭐ 「命名动作」**未做**形式化：`semantic` 以 Option 隐式表示了命名/未命名，
   但没有可投出/可撤回的目光状态（详见 `RealOperatorSplit` 文件头第 3 条）。
-/

import Lattice.Lib.Editing.RealOperatorSplit
import Lattice.Lib.Chain.RealLimitDiscrete
namespace RealOpContract

open RealOperatorSplit RealLimitDiscrete

/-- 语义等式义务（可选命名）。 -/
def DefEq {α β : Type _} (u : UnknownOp α β) : Option (α → β) → Prop
  | none => True
  | some s => ∀ x, s x = u.toFun x

/-- 算子契约：入库对象。 -/
structure OpContract (α β : Type _) where
  op : UnknownOp α β
  semantic : Option (α → β) := none
  defEq : DefEq op semantic
  approx : Option (Nat → α → β) := none
  cert : Option String := none

/-- 打包：只写元数据，不动外延。 -/
def package {α β : Type _} (u : UnknownOp α β)
    (sem : Option (α → β)) (h : DefEq u sem)
    (ap : Option (Nat → α → β)) (c : Option String) : OpContract α β where
  op := u
  semantic := sem
  defEq := h
  approx := ap
  cert := c

/-- **T3-1 外延不变** -/
theorem t3_package_ext {α β : Type _} (u : UnknownOp α β)
    (sem : Option (α → β)) (h : DefEq u sem)
    (ap : Option (Nat → α → β)) (c : Option String) :
    ∀ x, (package u sem h ap c).op.toFun x = u.toFun x :=
  fun _ => rfl

/-- **T3-2 补名不破坏 T1 闭环** -/
theorem t3_rename_keeps_t1 {α β : Type _} [AddCommGroup β]
    (f D : α → β) (n : Option String) (tg : Nat) :
    ∀ x, f x = D x + ({ toFun := (residualOp f D).toFun, tag := tg, name := n } :
      UnknownOp α β).toFun x :=
  t1_decompose f D

/-- **T3-3 命名成功则语义 = 外延** -/
theorem t3_sem_eq_op {α β : Type _} (K : OpContract α β)
    (s : α → β) (hsem : K.semantic = some s) :
    ∀ x, s x = K.op.toFun x := by
  intro x
  have h : DefEq K.op (some s) := by
    rw [← hsem]
    exact K.defEq
  exact h x

/-- 展开列（T2 用）。 -/
def expandOf {α β : Type _} (K : OpContract α β) : Option (Nat → α → β) :=
  K.approx

/-! 诚实边界：T3 **不自动**解释语义（**未做**）；`semantic = none` 合法；
证书复验在外部流程（**留待**）。本文件**未证**任何算子的可实现性。 -/

end RealOpContract
