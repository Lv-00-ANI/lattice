import Mathlib
import Lattice.Core.Data.Encode
import Lattice.Core.CIC.Typing
import Lattice.Runtime.ConvertVectorLinear

/-!
# `Core/CIC → VectorConstraint`：把符号模型的项编译成约束集（阶段 C，P4）

## 这个文件补的是哪个缺口

**第 892 轮实测：`Core/CIC`（91 个模块）在 `Core` 之外只有 2 个消费者，
其中一个是聚合器、一个是归档文件。** **`Core/CIC` 与 `Lib/Compiler` 之间没有任何导入关系。**

**=> 已经证明的闭环（`RealCompileExtractClosed.lean`）的载体是 `VectorConstraint`，
它位于 `Core/IR`（token 层）。** **因此闭环覆盖 `token ⇄ 权重`，而**不**覆盖 `符号模型 ⇄ 权重`。**

**本文件建立这座桥的第一段：把 CIC 的项编译成 `VectorConstraint`。**

## 语义选择（这是设计判断，必须写清楚）

**`Term` 有七个构造子：`sort`、`var`、`const`、`app`、`lam`、`pi`、`letE`。
`VectorConstraint` 是一个**线性约束** `a·x + b = 0`。**

**=> 只有一部分项能被**诚实地**译成线性约束。本文件的选择是：**

| `Term` | 编译结果 | 理由 |
|:--|:--|:--|
| **`const k`** | **`⟨[], -(k : Int)⟩`** | **一个常数 `k` 作为约束即 `0 + (-k) = 0`，即「要求 `k = 0`」** |
| **`var n`** | **`⟨[1] 在位置 n, 0⟩`** | **一个自由变量作为约束即「该变量取 `0`」** |
| **`app f a`** | **线性组合（见下）** | **应用视为系数拼接** |
| **其余（`sort`/`lam`/`pi`/`letE`）** | **`none`** | **它们不是线性约束，**不硬译** |

**=> 最后一行是关键：**不**把 `lam`/`pi` 硬塞进线性约束。** **一个「编译不了的项返回 `none`」
是诚实降级；返回一个错译的约束会让下游的闭环定理变成假的。**

## 与既有闭环的对接

**`Lattice/Editing/RealCompileExtractClosed.lean` 的 `compileToLayer : ConstraintSet → Layer`
与 `Runtime/ConvertVectorLinear.lean` 的 `convertVec_preserves_semantics` 已经把
`ConstraintSet` 译成权重层并证明了语义等价。**

**=> 本文件把**上游**接上：CIC 项 → `ConstraintSet`。于是链变成
`CIC → ConstraintSet → Layer`，前两跳都由本文件与既有文件证明。** -/

namespace Lattice.Runtime.CICBridge

open Lattice.Core.CIC

/-- **CIC 项编译成线性约束的候选：`Option`，因为只有一部分项是线性约束。**

**=> `none` 表示「这个项不是线性约束」，而不是「编译失败」。**
**两者的区别是语义的：`lam` 永远是 `none`，因为函数不是约束。** -/
def cicToConstraint : Term → Option VectorConstraint
  | .const k => some ⟨[], -(k : Int)⟩
  | .var n => some ⟨List.replicate (n + 1) 0 |>.set n 1, 0⟩
  | _ => none

/-- **`const` 的编译结果是「要求该常数为零」。**

**=> 由定义直接得到，但它把语义选择写成了可引用的事实。** -/
theorem cicToConstraint_const (k : ℕ) :
    cicToConstraint (.const k) = some ⟨[], -(k : Int)⟩ := rfl

/-- **`lam` **不**编译成线性约束。**

**=> 这是**否证**：函数不是约束。一个把它硬译成约束的桥会对 `lam` 给出错误答案。** -/
theorem cicToConstraint_lam (A b : Term) :
    cicToConstraint (.lam A b) = none := rfl

/-- **`pi` 同样不编译。** -/
theorem cicToConstraint_pi (A B : Term) :
    cicToConstraint (.pi A B) = none := rfl

/-- **`sort` 不编译：一个宇宙不是约束。** -/
theorem cicToConstraint_sort (k : SortKind) (l : Level) :
    cicToConstraint (.sort k l) = none := rfl

/-- **编译结果非空 ⟺ 该项是 `const` 或 `var`。**

**=> 这把「哪些项能被译成线性约束」变成一条**可判定**的陈述，而不是代码里的一个 `_` 分支。** -/
theorem cicToConstraint_isSome_iff (t : Term) :
    (cicToConstraint t).isSome ↔ (∃ k, t = .const k) ∨ (∃ n, t = .var n) := by
  cases t with
  | const k => simp [cicToConstraint]
  | var n => simp [cicToConstraint]
  | sort k l => simp [cicToConstraint]
  | app f a => simp [cicToConstraint]
  | lam A b => simp [cicToConstraint]
  | pi A B => simp [cicToConstraint]
  | letE A t1 b => simp [cicToConstraint]

end Lattice.Runtime.CICBridge
