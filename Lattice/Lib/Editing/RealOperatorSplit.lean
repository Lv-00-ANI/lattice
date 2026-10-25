/-
# LATTICE: RealOperatorSplit — T1 分解恒等式（记账约定）

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）
> 目标：不再声称逆向编译恒成功，而是给「未解释的部分」一个显式名字。
> `f = D + U` 是**恒等式**（记账约定）；T2（极限离散收敛）见 `RealLimitDiscrete`。

公理立场：确定性（一切计算皆有算子，未命名者入 `UnknownOp`）。
本文件不声称 U 已被解释，只证**分解恒等**。

## 诚实边界（**标注**）

1. ⭐ **T1 是恒等式，不是存在性结果** —— 证明体是 `add_sub_cancel` 一行，作用是给残差一个
   显式载体，**未做**任何新的数学内容。
2. ⭐ **适用范围限于光滑激活** —— T2 的 `Z^(n+1)/(n+1)!` 精度来自 Taylor 余项形式，
   该形式要求 σ 在区间上 `n+1` 阶可导；**对 ReLU 这类非光滑激活不成立**（**超出**本框架范围）。
   故本文件**不解决**「ReLU 类激活的精确闭环问题」。
3. ⭐ **命名动作尚未形式化** —— `name : Option String` 以 Option **隐式**表示了
   「命名/未命名」二元状态；「命名动作」本身（可投出/可撤回的目光）**未做**形式化。
   若将来引入显式目光状态（Gaze），本文件的 `name` 字段应成为其特例。
4. ⭐ 「一切非线性皆 T2」是**用户公理**，本文件**不证**普适性（另见 `RealLimitDiscrete`）。
-/

import Mathlib.Algebra.Group.Basic

namespace RealOperatorSplit

/-- 未命名算子：外延 + 稳定标识 + 待补名字。 -/
structure UnknownOp (α : Type _) (β : Type _) where
  toFun : α → β
  tag : Nat
  name : Option String := none

/-- 函数外延调用（显式，不依赖 CoeFun）。 -/
def UnknownOp.eval {α β : Type _} (u : UnknownOp α β) : α → β :=
  u.toFun

/-- 离散展开接口（T2 用）。 -/
structure DiscreteExpand (α : Type _) (β : Type _) where
  u : UnknownOp α β
  approx : Nat → α → β

/-- T1 余项算子：`U x = f x − D x`。 -/
def residualOp {α β : Type _} [AddGroup β] (f D : α → β) : UnknownOp α β where
  toFun := fun x => f x - D x
  tag := 0
  name := none

/-- **T1 分解恒等式（记账约定）**：任意 `f` 都能写成 `D + 残差`——这是恒等式而非存在性结果，
    其作用是给「未解释的部分」一个显式名字，**不声称** `U` 的语义。 -/
theorem t1_decompose {α β : Type _} [AddCommGroup β] (f D : α → β) :
    ∀ x, f x = D x + (residualOp f D).toFun x := by
  intro x
  show f x = D x + (f x - D x)
  exact (add_sub_cancel (D x) (f x)).symm

theorem t1_pointwise {α β : Type _} [AddCommGroup β] (f D : α → β) :
    ∀ x, f x = D x + (residualOp f D).toFun x :=
  t1_decompose f D

/-- 沿已知项列表剥余项（结构递归于列表）。 -/
def residualsOf {α β : Type _} [AddGroup β] (f : α → β) :
    List (α → β) → List (UnknownOp α β)
  | [] => [residualOp f (fun _ => 0)]
  | D :: Ds =>
      let u := residualOp f D
      u :: residualsOf u.toFun Ds

/-- 补名字不改变外延。 -/
theorem t3_name_irrelevant {α β : Type _} (u : UnknownOp α β) (n : Option String) :
    ({ toFun := u.toFun, tag := u.tag, name := n } : UnknownOp α β).toFun = u.toFun :=
  rfl

/-! 诚实边界：T1 只保证恒等，**不解释**语义；T2 极限离散**未做**于本文件（见 `RealLimitDiscrete`）；
有限域抽样不得当作 T2。`residualsOf` 的**标**签 `tag := 0` 为占位，**未证**其区分性。 -/

end RealOperatorSplit
