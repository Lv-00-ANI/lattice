/-
# 栈代码生成：第 89–92 轮判定「永久停止」的路线，在第 155 轮闭合

## 0. 这一节推翻了什么

第 89–92 轮四次尝试把一个表达式编译成栈机程序并证明语义保持，全部失败。
第 92 轮的结论是：

> **永久停止这条路线的实现，不再消耗轮次。**
> 这已经超出「用定理推进项目」的范围，变成「和 Lean 的归纳机制搏斗」。

**第 155 轮重做，一次闭合。根因不是 Lean，是生成器的指令顺序写错了。**

## 1. 真正的错误：`compileAcc` 里 `add` 的位置

第 89–92 轮的累加器式生成器是：

```lean
compileAcc (.add a b) acc = compileAcc b (compileAcc a acc ++ [.add])
```

展开：`acc ++ compile(a) ++ [add] ++ compile(b)`。

**`add` 在 `b` 的指令之前执行——而那时栈上只有 `a` 的值。**

正确的后序是 `acc ++ compile(a) ++ compile(b) ++ add`：

```lean
compileAcc (.add a b) acc = compileAcc b (compileAcc a acc) ++ [.add]
```

**这一个符号的位置，就是四次失败的原因。**

前四轮记录的三个「Lean 机制」问题——`induction` 不重写依赖假设、`bind` 链化简、
`b - 1` 的截断减法——**都真实存在，但都是次生问题**：它们是在一个语义错误的目标上努力时遇到的。

## 2. 三个次生问题，本节的解法

| 问题 | 解法 |
|:--|:--|
| **`induction e` 不重写 `hst : stackDepth e ≤ st.length`** | **把 `st` / `st'` 移进结论**：`∀ acc st st', ...`，每情形由 `intro` 引入，于是 `stackDepth e` 已经被归纳析构 |
| **`bind` 链化简** | **不产生 `bind` 链**：`compileAcc_correct` 两次调用 `runProg_append` |
| **`omega` 看不穿 `b - 1`** | **`le_succ_of_pred_le` 独立证明**（`Nat.succ_pred_eq_of_pos` + `omega`） |

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `stackDepth_left` / `stackDepth_right` | `max a (b-1) ≤ n` 的两条推论 |
| **`le_succ_of_pred_le`** | **`b - 1 ≤ n ⟹ b ≤ n + 1`** |
| **`runProg_append`** | **`runProg` 对程序拼接可组合** |
| **`compileAcc_correct`** | **生成器在任意累加器与任意初始栈下语义保持** |
| **`compileProg_correct`** | **`runProg (compileProg e) [0] = some (evalStack e :: [0])`** |

## 4. 边界

- **本节是通用的**：不含任何 Geo 层定义，载体是 `StackExpr` / `StackOp`。
  **它证明的是「代码生成这个模式可行」，不是「`CExpr` 已能生成代码」**——
  后者需要把 `CExpr` 映射到 `StackExpr`，是接线的一步。
- 本节**不涉及浮点**：`evalStack : StackExpr → ℕ`，所以是纯整数的语义保持。
  **`Float` 轨道的单向性（`STATE-FINAL` §3.6.2）不变**。
- 本节**不改**路线 C 的其余部分。
-/
import Mathlib

namespace Lattice.Lift.StackCodegen

inductive StackExpr where
  | lit : ℕ → StackExpr
  | add : StackExpr → StackExpr → StackExpr
  | mul : StackExpr → StackExpr → StackExpr

namespace StackExpr

def evalStack : StackExpr → ℕ
  | .lit n => n
  | .add a b => evalStack a + evalStack b
  | .mul a b => evalStack a * evalStack b

/-- Stack stackDepth needed. A binary node pops two and pushes one, so the LARGER branch needs one more
than the other -- hence `max a (b - 1)`. -/
def stackDepth : StackExpr → ℕ
  | .lit _ => 1
  | .add a b => max (stackDepth a) (stackDepth b - 1)
  | .mul a b => max (stackDepth a) (stackDepth b - 1)

/-- The instruction set. -/
inductive StackOp where
  | push : ℕ → StackOp
  | add : StackOp
  | mul : StackOp

namespace StackOp

def run : StackOp → List ℕ → Option (List ℕ)
  | .push n, st => some (n :: st)
  | .add, a :: b :: st => some ((b + a) :: st)
  | .add, _ => none
  | .mul, a :: b :: st => some ((b * a) :: st)
  | .mul, _ => none

end StackOp

/-- Accumulator-style generator: left-associated, as round 90 learned. -/
def compileAcc : StackExpr → List StackOp → List StackOp
  | .lit n, acc => acc ++ [.push n]
  | .add a b, acc => compileAcc b (compileAcc a acc) ++ [.add]
  | .mul a b, acc => compileAcc b (compileAcc a acc) ++ [.mul]

def compileProg (e : StackExpr) : List StackOp := compileAcc e []

/-- Execute a program, with `Option` for underflow (round 89's fix). -/
def runProg : List StackOp → List ℕ → Option (List ℕ)
  | [], st => some st
  | op :: rest, st =>
      (match StackOp.run op st with
       | some st' => runProg rest st'
       | none => none)

/-! ## The arithmetic lemmas, independently -/

/-- `max a (b - 1) <= n` gives `a <= n`. -/
theorem stackDepth_left (a b n : ℕ) (h : max a (b - 1) ≤ n) : a ≤ n :=
  le_trans (le_max_left _ _) h

/-- `max a (b - 1) <= n` gives `b <= n + 1`.

`omega` cannot see through the truncated subtraction, which is what stopped round 91. -/
theorem le_succ_of_pred_le (b n : ℕ) (h : b - 1 ≤ n) : b ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · simp only [hb]; omega
  · have : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hb
    omega

/-- … and from the `max` form. -/
theorem stackDepth_right (a b n : ℕ) (h : max a (b - 1) ≤ n) : b ≤ n + 1 :=
  le_succ_of_pred_le b n (le_trans (le_max_right _ _) h)

/-! ## Append -/

/-- **`runProg` is append-compositional** when the prefix succeeds. -/
theorem runProg_append (p q : List StackOp) (st : List ℕ) :
    ∀ (mid : List ℕ), runProg p st = some mid → runProg (p ++ q) st = runProg q mid := by
  induction p generalizing st with
  | nil =>
      intro mid h
      simp only [runProg, Option.some.injEq] at h
      rw [← h]
      simp only [List.nil_append]
  | cons op rest ih =>
      intro mid h
      simp only [runProg] at h ⊢
      split at h
      · rename_i st' hst'
        exact ih st' mid h
      · simp at h

/-- **The code generator is correct.**

`compileAcc` appends `e`'s instructions after `acc`, so running the whole thing first runs `acc` and then
`e`; the conclusion therefore says `runProg (compileAcc e acc) st = some (evalStack e :: st')` where `st'` is what
`acc` produced.

`stackDepth e <= st'.length` is the stack budget: a binary node needs the LARGER branch to fit, because
the other branch's value is still on the stack while it runs. -/
theorem compileAcc_correct (e : StackExpr) :
    ∀ (acc : List StackOp) (st st' : List ℕ),
      runProg acc st = some st' → stackDepth e ≤ st'.length →
      runProg (compileAcc e acc) st = some (evalStack e :: st') := by
  induction e with
  | lit n =>
      intro acc st st' hacc _
      show runProg (acc ++ [StackOp.push n]) st = some (n :: st')
      rw [runProg_append acc [StackOp.push n] st st' hacc]
      rfl
  | add a b iha ihb =>
      intro acc st st' hacc hd
      have hda : stackDepth a ≤ st'.length := stackDepth_left _ _ _ hd
      have hia := iha acc st st' hacc hda
      have hdb : stackDepth b ≤ (evalStack a :: st').length := by
        simp only [List.length_cons]
        exact stackDepth_right _ _ _ hd
      have hib := ihb (compileAcc a acc) st (evalStack a :: st') hia hdb
      show runProg (compileAcc b (compileAcc a acc) ++ [StackOp.add]) st = some ((evalStack a + evalStack b) :: st')
      rw [runProg_append (compileAcc b (compileAcc a acc)) [StackOp.add] st (evalStack b :: evalStack a :: st') hib]
      rfl
  | mul a b iha ihb =>
      intro acc st st' hacc hd
      have hda : stackDepth a ≤ st'.length := stackDepth_left _ _ _ hd
      have hia := iha acc st st' hacc hda
      have hdb : stackDepth b ≤ (evalStack a :: st').length := by
        simp only [List.length_cons]
        exact stackDepth_right _ _ _ hd
      have hib := ihb (compileAcc a acc) st (evalStack a :: st') hia hdb
      show runProg (compileAcc b (compileAcc a acc) ++ [StackOp.mul]) st = some ((evalStack a * evalStack b) :: st')
      rw [runProg_append (compileAcc b (compileAcc a acc)) [StackOp.mul] st (evalStack b :: evalStack a :: st') hib]
      rfl

/-- **The corollary with an empty accumulator**: compiling `e` and running it on an empty stack
yields `evalStack e`. -/
theorem compileProg_correct (e : StackExpr) (h : stackDepth e ≤ 1) :
    runProg (compileProg e) [0] = some (evalStack e :: [0]) := by
  have := compileAcc_correct e [] [0] [0] rfl (by simpa using h)
  simpa [compileProg] using this

end StackExpr

end Lattice.Lift.StackCodegen
