/-
# 栈代码生成：从 `ℕ` 泛化到任意载体

## 0. 两件事，别混为一谈

第 155 轮闭合了栈代码生成的**模式**，语义是 `evalStack : StackExpr → ℕ`。

**但本项目的可执行轨道是 `CExpr`（第 87–88 轮），它的常量是 `Float`。**
一个只认 `ℕ` 的机器装不下它。所以需要两件**独立**的事：

| # | 做什么 | 状态 |
|--:|:--|:--|
| **1** | **把机器泛化到任意 `α`（带 `Add`/`Mul`）** | **本节** |
| 2 | 把 `CExpr` 映射上来（需要 `sub` 与 `load`） | 下一步 |

## 1. 泛化为什么几乎不花代价

第 155 轮的证明**从未使用 `ℕ` 的任何性质**——`compileAcc_correct` 只用 `runProg_append` 和 `rfl`。
所以把 `ℕ` 换成 `α`（只要求 `Add`/`Mul`）后，**逐行不变**。

**这不是巧合**：栈机的语义保持与算术无关，它只关乎「指令序列 + 栈深度」。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `stackDepth_left` / `_right` | `max a (b-1) ≤ n` 的两条推论（**与 `α` 无关**） |
| `le_succ_of_pred_le` | **`b - 1 ≤ n ⟹ b ≤ n + 1`**（与 `α` 无关） |
| `runProg_append` | **`α` 任意**，程序拼接可组合 |
| **`compileAcc_correct`** | **`α` 任意、累加器任意、栈任意** |
| **`compileProg_correct`** | **`runProg (compileProg e) [seed] = some (evalStack e :: [seed])`**，`seed : α` 任意 |

## 3. 边界

- **`StackOp` 只有 `push` / `add` / `mul`**。接 `CExpr` 还需要 `sub`，
  以及一条从配置读值的 `load`——**那会让 `runProg` 多一个配置参数**，是下一步。
- **本节不含任何 Geo 定义**：`α` 是自由类型参数。
- **`Float` 的单向性（`STATE-FINAL` §3.6.2）不变**：本节只说「指令序列的语义保持」，
  **不说「浮点判定可靠」**。
- 第 155 轮的 `ℕ` 版本是本节的实例（`α := ℕ`）。**原文件已被本节替代**，
  历史记录见 `STATE-FINAL` §3.6.2c′。
-/
import Mathlib

namespace Lattice.Lift.StackCodegen

variable {α : Type}

inductive StackExpr (α : Type) where
  | lit : α → StackExpr α
  | add : StackExpr α → StackExpr α → StackExpr α
  | mul : StackExpr α → StackExpr α → StackExpr α

namespace StackExpr

def evalStack [Add α] [Mul α] : StackExpr α → α
  | .lit a => a
  | .add x y => evalStack x + evalStack y
  | .mul x y => evalStack x * evalStack y

/-- Stack depth: a binary node needs the larger branch, plus one if the larger is the second. -/
def stackDepth : StackExpr α → ℕ
  | .lit _ => 1
  | .add x y => max (stackDepth x) (stackDepth y - 1)
  | .mul x y => max (stackDepth x) (stackDepth y - 1)

end StackExpr

inductive StackOp (α : Type) where
  | push : α → StackOp α
  | add : StackOp α
  | mul : StackOp α

namespace StackOp

def run [Add α] [Mul α] : StackOp α → List α → Option (List α)
  | .push a, st => some (a :: st)
  | .add, x :: y :: st => some ((y + x) :: st)
  | .add, _ => none
  | .mul, x :: y :: st => some ((y * x) :: st)
  | .mul, _ => none

end StackOp

def compileAcc : StackExpr α → List (StackOp α) → List (StackOp α)
  | .lit a, acc => acc ++ [.push a]
  | .add x y, acc => compileAcc y (compileAcc x acc) ++ [.add]
  | .mul x y, acc => compileAcc y (compileAcc x acc) ++ [.mul]

def compileProg (e : StackExpr α) : List (StackOp α) := compileAcc e []

def runProg [Add α] [Mul α] : List (StackOp α) → List α → Option (List α)
  | [], st => some st
  | op :: rest, st =>
      (match StackOp.run op st with
       | some st' => runProg rest st'
       | none => none)

/-! ## The arithmetic, unchanged -/

theorem stackDepth_left (a b n : ℕ) (h : max a (b - 1) ≤ n) : a ≤ n :=
  le_trans (le_max_left _ _) h

theorem le_succ_of_pred_le (b n : ℕ) (h : b - 1 ≤ n) : b ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · simp only [hb]; omega
  · have : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hb
    omega

theorem stackDepth_right (a b n : ℕ) (h : max a (b - 1) ≤ n) : b ≤ n + 1 :=
  le_succ_of_pred_le b n (le_trans (le_max_right _ _) h)

/-! ## Correctness, unchanged -/

theorem runProg_append [Add α] [Mul α] (p q : List (StackOp α)) (st : List α) :
    ∀ (mid : List α), runProg p st = some mid → runProg (p ++ q) st = runProg q mid := by
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
      · rename_i st' _
        exact ih st' mid h
      · simp at h

theorem compileAcc_correct [Add α] [Mul α] (e : StackExpr α) :
    ∀ (acc : List (StackOp α)) (st st' : List α),
      runProg acc st = some st' → StackExpr.stackDepth e ≤ st'.length →
      runProg (compileAcc e acc) st = some (StackExpr.evalStack e :: st') := by
  induction e with
  | lit a =>
      intro acc st st' hacc _
      show runProg (acc ++ [StackOp.push a]) st = some (a :: st')
      rw [runProg_append acc [StackOp.push a] st st' hacc]
      rfl
  | add x y ihx ihy =>
      intro acc st st' hacc hd
      have hdx : StackExpr.stackDepth x ≤ st'.length := stackDepth_left _ _ _ hd
      have hix := ihx acc st st' hacc hdx
      have hdy : StackExpr.stackDepth y ≤ (StackExpr.evalStack x :: st').length := by
        simp only [List.length_cons]
        exact stackDepth_right _ _ _ hd
      have hiy := ihy (compileAcc x acc) st (StackExpr.evalStack x :: st') hix hdy
      show runProg (compileAcc y (compileAcc x acc) ++ [StackOp.add]) st =
        some ((StackExpr.evalStack x + StackExpr.evalStack y) :: st')
      rw [runProg_append (compileAcc y (compileAcc x acc)) [StackOp.add] st
            (StackExpr.evalStack y :: StackExpr.evalStack x :: st') hiy]
      rfl
  | mul x y ihx ihy =>
      intro acc st st' hacc hd
      have hdx : StackExpr.stackDepth x ≤ st'.length := stackDepth_left _ _ _ hd
      have hix := ihx acc st st' hacc hdx
      have hdy : StackExpr.stackDepth y ≤ (StackExpr.evalStack x :: st').length := by
        simp only [List.length_cons]
        exact stackDepth_right _ _ _ hd
      have hiy := ihy (compileAcc x acc) st (StackExpr.evalStack x :: st') hix hdy
      show runProg (compileAcc y (compileAcc x acc) ++ [StackOp.mul]) st =
        some ((StackExpr.evalStack x * StackExpr.evalStack y) :: st')
      rw [runProg_append (compileAcc y (compileAcc x acc)) [StackOp.mul] st
            (StackExpr.evalStack y :: StackExpr.evalStack x :: st') hiy]
      rfl

/-- The corollary on a one-element stack, with the seed arbitrary. -/
theorem compileProg_correct [Add α] [Mul α] (e : StackExpr α) (seed : α)
    (h : StackExpr.stackDepth e ≤ 1) :
    runProg (compileProg e) [seed] = some (StackExpr.evalStack e :: [seed]) := by
  have := compileAcc_correct e [] [seed] [seed] rfl (by simpa using h)
  simpa [compileProg] using this

/-! ## 4. 实例化：泛化的意义在于它真的能用 -/

/-- 具体程序：`(2 + 3) * 4`，在 `ℕ` 上。 -/
def exampleNat : StackExpr ℕ := .mul (.add (.lit 2) (.lit 3)) (.lit 4)

/-- **`ℕ` 实例真的算出 20。** 生成 5 条指令，运行得到 `[20, 0]`。 -/
theorem exampleNat_runs : runProg (compileProg exampleNat) [0] = some (20 :: [0]) := by
  decide

/-- **`ℤ` 实例**：`-3 + 5 = 2`。 -/
def exampleInt : StackExpr ℤ := .add (.lit (-3)) (.lit 5)

theorem exampleInt_runs : runProg (compileProg exampleInt) [0] = some (2 :: [0]) := by
  decide

/-- **`Float` 实例存在**——这正是 `CExpr` 轨道需要的载体。

`Float` 的相等不可判定（`NaN`），所以这里只检查**程序长度**，不检查求值结果。
**这正是 `STATE-FINAL` §3.6.2 记录的 `Float` 单向性的具体体现**：生成器可用，
而「运行结果等于什么」不能由 `decide` 判定。 -/
def exampleFloat : StackExpr Float := .mul (.add (.lit 2.0) (.lit 3.0)) (.lit 4.0)

theorem exampleFloat_compiles : (compileProg exampleFloat).length = 5 := by
  decide

/-- **泛化的最后一条证据**：`CExpr` 的常量类型是 `Float`，而 `StackExpr Float` 就是这个载体。

**这不是接线，是可行性**——真正的映射还需要 `sub` 与 `load`（见 §3）。 -/
theorem float_is_a_valid_carrier : Nonempty (StackExpr Float) := ⟨exampleFloat⟩

end Lattice.Lift.StackCodegen
