/-
# `CExpr` 的代码生成：可执行边界的字面闭合

## 0. 这一节交付什么

`CExpr` 是本项目的可执行轨道（第 87–88 轮）：与 `GeoExpr` 同构，但常量是 `Float`，
求值 `evalC` 是普通 `def`。

**本节把它接到第 157 轮泛化后的栈机上**，并证明**生成的代码算出 `evalC` 的值**。

## 1. 三段映射

| 段 | 内容 |
|:--|:--|
| `CExpr.depth` | 栈深度（叶子 1，二元 `max (d a) (d b - 1)`） |
| `toStack` | `CExpr n → Lattice.Lift.StackCodegen.StackExpr (ℕ × Fin n) Float`：`coord` ↦ `load`，`const` ↦ `lit` |
| **`stackDepth_toStack`** | **映射保持深度** |
| **`evalStack_toStack`** | **映射保持语义** |

## 2. 主定理

```lean
theorem toStack_correct (e : CExpr n) (pts : ℕ → Fin n → Float) (seed : Float)
    (h : CExpr.depth e ≤ 1) :
    Lattice.Lift.StackCodegen.runProg (fun pa : ℕ × Fin n => pts pa.1 pa.2) (Lattice.Lift.StackCodegen.compileProg (toStack e)) [seed] =
      some (evalC e pts :: [seed])
```

**一个符号表达式变成指令列表，运行该列表得到表达式的值。**

## 3. 边界（必须明说）

- **`h : CExpr.depth e ≤ 1` 是栈预算**，不是附加假设：叶子要 1 格，二元节点需要较深的分支。
  **深度 > 1 的表达式需要更深的初始栈**——`Lattice.Lift.StackCodegen.compileProg_correct` 允许任意初始栈，
  本节取最小的一格。
- **这是「生成器正确」，不是「浮点判定可靠」**：`toStack_correct` 说
  「运行生成的代码 ⟹ 得到 `evalC` 的值」，**而 `evalC` 本身是 `Float` 计算**，
  它与 `ℝ` 上 `evalPts` 的偏差是 `STATE-FINAL` §3.6.2 记录的**单向性**，本节不改变它。
- **本节不含 `Float` 的相等判定**：定理是等式陈述，不是在证明「浮点比较可靠」。
- 本节**不改** `CExpr` 与 `evalC` 的定义。
-/
import Mathlib
import Lattice.Runtime.StackCodegen
import Lattice.Domains.ComputableExpr

/-! ## Mapping `CExpr` onto the machine -/

open Lattice.Geo


namespace Lattice.Geo.CExprCodegen

open Lattice.Geo.ComputableExpr.CExpr

variable {n : ℕ}

/-- **Stack depth of a `CExpr`** — the same shape as `Lattice.Lift.StackCodegen.stackDepth`.

**It is constantly 1**, which `CExpr.depth_eq_one` below proves; the recursion is faithful to
`stackDepth` but the second argument's `- 1` never binds because a leaf already contributes 1. -/
def CExpr.depth : Lattice.Geo.ComputableExpr.CExpr n → ℕ
  | .coord _ _ => 1
  | .const _ => 1
  | .add a b => max (depth a) (depth b - 1)
  | .sub a b => max (depth a) (depth b - 1)
  | .mul a b => max (depth a) (depth b - 1)

/-- **The projection**: a `CExpr` becomes a stack program over `Float`, with the configuration
index `Nat × Fin n` (point, axis). -/
def toStack : Lattice.Geo.ComputableExpr.CExpr n → Lattice.Lift.StackCodegen.StackExpr (ℕ × Fin n) Float
  | .coord p axis => .load (p, axis)
  | .const c => .lit c
  | .add a b => .add (toStack a) (toStack b)
  | .sub a b => .sub (toStack a) (toStack b)
  | .mul a b => .mul (toStack a) (toStack b)

/-- **The projection preserves depth.** -/
theorem stackDepth_toStack (e : Lattice.Geo.ComputableExpr.CExpr n) :
    Lattice.Lift.StackCodegen.stackDepth (toStack e) = CExpr.depth e := by
  induction e with
  | coord p axis => rfl
  | const c => rfl
  | add a b iha ihb => simp only [toStack, Lattice.Lift.StackCodegen.stackDepth, CExpr.depth, iha, ihb]
  | sub a b iha ihb => simp only [toStack, Lattice.Lift.StackCodegen.stackDepth, CExpr.depth, iha, ihb]
  | mul a b iha ihb => simp only [toStack, Lattice.Lift.StackCodegen.stackDepth, CExpr.depth, iha, ihb]

/-- **`CExpr.depth` is constantly 1.**

The recursion `max (depth a) (depth b - 1)` looks like it tracks a stack height, but a leaf already
contributes 1, so the `- 1` never binds and the result is 1 for every expression. **This is why
`toStack_correct` needs no depth hypothesis.** -/
theorem CExpr.depth_eq_one {n : ℕ} (e : Lattice.Geo.ComputableExpr.CExpr n) : CExpr.depth e = 1 := by
  induction e with
  | coord p axis => rfl
  | const c => rfl
  | add a b iha ihb =>
      show max (CExpr.depth a) (CExpr.depth b - 1) = 1
      rw [iha, ihb]; decide
  | sub a b iha ihb =>
      show max (CExpr.depth a) (CExpr.depth b - 1) = 1
      rw [iha, ihb]; decide
  | mul a b iha ihb =>
      show max (CExpr.depth a) (CExpr.depth b - 1) = 1
      rw [iha, ihb]; decide

/-- **The projection preserves meaning.** -/
theorem evalStack_toStack (e : Lattice.Geo.ComputableExpr.CExpr n) (pts : ℕ → Fin n → Float) :
    Lattice.Lift.StackCodegen.evalStack (fun pa : ℕ × Fin n => pts pa.1 pa.2) (toStack e) =
      Lattice.Geo.ComputableExpr.CExpr.evalC e pts := by
  induction e with
  | coord p axis => rfl
  | const c => rfl
  | add a b iha ihb =>
      simp only [toStack, Lattice.Lift.StackCodegen.evalStack, Lattice.Geo.ComputableExpr.CExpr.evalC, iha, ihb]
  | sub a b iha ihb =>
      simp only [toStack, Lattice.Lift.StackCodegen.evalStack, Lattice.Geo.ComputableExpr.CExpr.evalC, iha, ihb]
  | mul a b iha ihb =>
      simp only [toStack, Lattice.Lift.StackCodegen.evalStack, Lattice.Geo.ComputableExpr.CExpr.evalC, iha, ihb]

/-- **`CExpr` compiles to executable code that computes `evalC`.**

This is the closure of the executable boundary for the `CExpr` track: a symbol expression becomes an
instruction list, and running that list on a one-element stack yields the expression's value.

**The `depth e ≤ 1` hypothesis was REMOVED in round 199** because `CExpr.depth_eq_one` shows it holds
for every expression: the old docstring called it "the stack budget", which was a *misreading* — it is not
a budget the caller must respect, it is a fact. A hypothesis that is always true is worse than no
hypothesis: it invites the reader to believe the compiler has a depth limit it does not have. -/
theorem toStack_correct (e : Lattice.Geo.ComputableExpr.CExpr n) (pts : ℕ → Fin n → Float) (seed : Float) :
    Lattice.Lift.StackCodegen.runProg (fun pa : ℕ × Fin n => pts pa.1 pa.2) (Lattice.Lift.StackCodegen.compileProg (toStack e)) [seed] =
      some (Lattice.Geo.ComputableExpr.CExpr.evalC e pts :: [seed]) := by
  rw [Lattice.Lift.StackCodegen.compileProg_correct (fun pa : ℕ × Fin n => pts pa.1 pa.2) (toStack e) seed]
  rw [evalStack_toStack]

end Lattice.Geo.CExprCodegen
