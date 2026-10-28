/-
# 栈代码生成：任意载体、带配置读取与减法

## 0. 三代演进

| 轮次 | 语义 | 载体 |
|:--|:--|:--|
| 155 | `Nat` | `push` / `add` / `mul` |
| 156 | **任意 `Add`/`Mul`** | 同上 |
| **157** | **任意 `Add`/`Sub`/`Mul`** | **加 `load`（读配置）与 `sub`** |

**第 157 轮加两件东西，都是为了能装下 `CExpr`**：它的常量是 `Float`（第 156 轮已解决），
而它还有 `coord p axis`（需要从配置读值）与 `sub`（需要减法）。

## 1. 配置索引

```lean
StackOp σ α  =  push a | load i | add | sub | mul
run cfg op st
```

`σ` 是「配置索引」类型，`cfg : σ → α` 提供 `load` 读到的值。
**对 `CExpr n` 取 `σ := ℕ × Fin n`、`cfg := fun (p, axis) => pts p axis`**——见 `Geo/CExprCodegen`。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `stackDepth_left` / `_right` | `max a (b-1) ≤ n` 的两条推论 |
| `le_succ_of_pred_le` | `b - 1 ≤ n ⟹ b ≤ n + 1` |
| **`runProg_append`** | **`cfg`、`α`、程序均任意** |
| **`compileAcc_correct`** | **任意累加器、任意栈、任意配置** |
| **`compileProg_correct`** | **`runProg cfg (compileProg e) [seed] = some (evalStack cfg e :: [seed])`** |

## 3. 边界

- **本节不含任何 Geo 定义**：`σ`、`α` 都是自由类型参数。
- **`Float` 的单向性（`STATE-FINAL` §3.6.2）不变**：本节只说指令序列的语义保持，
  **不说浮点判定可靠**。
- `CExpr` 的映射在 `Lattice/Geo/CExprCodegen.lean`（`Geo` 层 import `Lift` 是允许的）。
-/
import Mathlib

namespace Lattice.Lift.StackCodegen

variable {σ α : Type}

inductive StackExpr (σ : Type) (α : Type) where
  | lit : α → StackExpr σ α
  | load : σ → StackExpr σ α
  | add : StackExpr σ α → StackExpr σ α → StackExpr σ α
  | sub : StackExpr σ α → StackExpr σ α → StackExpr σ α
  | mul : StackExpr σ α → StackExpr σ α → StackExpr σ α


def evalStack [Add α] [Sub α] [Mul α] (cfg : σ → α) : StackExpr σ α → α
  | .lit a => a
  | .load i => cfg i
  | .add x y => evalStack cfg x + evalStack cfg y
  | .sub x y => evalStack cfg x - evalStack cfg y
  | .mul x y => evalStack cfg x * evalStack cfg y

/-- Stack depth. `lit` and `load` need one slot; a binary node needs the larger branch, plus one if
the larger is the second. -/
def stackDepth : StackExpr σ α → ℕ
  | .lit _ => 1
  | .load _ => 1
  | .add x y => max (stackDepth x) (stackDepth y - 1)
  | .sub x y => max (stackDepth x) (stackDepth y - 1)
  | .mul x y => max (stackDepth x) (stackDepth y - 1)


inductive StackOp (σ : Type) (α : Type) where
  | push : α → StackOp σ α
  | load : σ → StackOp σ α
  | add : StackOp σ α
  | sub : StackOp σ α
  | mul : StackOp σ α


def runOp [Add α] [Sub α] [Mul α] (cfg : σ → α) : StackOp σ α → List α → Option (List α)
  | .push a, st => some (a :: st)
  | .load i, st => some (cfg i :: st)
  | .add, x :: y :: st => some ((y + x) :: st)
  | .add, _ => none
  | .sub, x :: y :: st => some ((y - x) :: st)
  | .sub, _ => none
  | .mul, x :: y :: st => some ((y * x) :: st)
  | .mul, _ => none


def compileAcc : StackExpr σ α → List (StackOp σ α) → List (StackOp σ α)
  | .lit a, acc => acc ++ [.push a]
  | .load i, acc => acc ++ [.load i]
  | .add x y, acc => compileAcc y (compileAcc x acc) ++ [.add]
  | .sub x y, acc => compileAcc y (compileAcc x acc) ++ [.sub]
  | .mul x y, acc => compileAcc y (compileAcc x acc) ++ [.mul]

def compileProg (e : StackExpr σ α) : List (StackOp σ α) := compileAcc e []

def runProg [Add α] [Sub α] [Mul α] (cfg : σ → α) :
    List (StackOp σ α) → List α → Option (List α)
  | [], st => some st
  | op :: rest, st =>
      (match runOp cfg op st with
       | some st' => runProg cfg rest st'
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

/-! ## Correctness, now with a configuration -/

theorem runProg_append [Add α] [Sub α] [Mul α] (cfg : σ → α)
    (p q : List (StackOp σ α)) (st : List α) :
    ∀ (mid : List α), runProg cfg p st = some mid → runProg cfg (p ++ q) st = runProg cfg q mid := by
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

theorem compileAcc_correct [Add α] [Sub α] [Mul α] (cfg : σ → α) (e : StackExpr σ α) :
    ∀ (acc : List (StackOp σ α)) (st st' : List α),
      runProg cfg acc st = some st' → stackDepth e ≤ st'.length →
      runProg cfg (compileAcc e acc) st = some (evalStack cfg e :: st') := by
  induction e with
  | lit a =>
      intro acc st st' hacc _
      show runProg cfg (acc ++ [StackOp.push a]) st = some (a :: st')
      rw [runProg_append cfg acc [StackOp.push a] st st' hacc]
      rfl
  | load i =>
      intro acc st st' hacc _
      show runProg cfg (acc ++ [StackOp.load i]) st = some (cfg i :: st')
      rw [runProg_append cfg acc [StackOp.load i] st st' hacc]
      rfl
  | add x y ihx ihy =>
      intro acc st st' hacc hd
      have hdx : stackDepth x ≤ st'.length := stackDepth_left _ _ _ hd
      have hix := ihx acc st st' hacc hdx
      have hdy : stackDepth y ≤ (evalStack cfg x :: st').length := by
        simp only [List.length_cons]; exact stackDepth_right _ _ _ hd
      have hiy := ihy (compileAcc x acc) st (evalStack cfg x :: st') hix hdy
      show runProg cfg (compileAcc y (compileAcc x acc) ++ [StackOp.add]) st =
        some ((evalStack cfg x + evalStack cfg y) :: st')
      rw [runProg_append cfg (compileAcc y (compileAcc x acc)) [StackOp.add] st
            (evalStack cfg y :: evalStack cfg x :: st') hiy]
      rfl
  | sub x y ihx ihy =>
      intro acc st st' hacc hd
      have hdx : stackDepth x ≤ st'.length := stackDepth_left _ _ _ hd
      have hix := ihx acc st st' hacc hdx
      have hdy : stackDepth y ≤ (evalStack cfg x :: st').length := by
        simp only [List.length_cons]; exact stackDepth_right _ _ _ hd
      have hiy := ihy (compileAcc x acc) st (evalStack cfg x :: st') hix hdy
      show runProg cfg (compileAcc y (compileAcc x acc) ++ [StackOp.sub]) st =
        some ((evalStack cfg x - evalStack cfg y) :: st')
      rw [runProg_append cfg (compileAcc y (compileAcc x acc)) [StackOp.sub] st
            (evalStack cfg y :: evalStack cfg x :: st') hiy]
      rfl
  | mul x y ihx ihy =>
      intro acc st st' hacc hd
      have hdx : stackDepth x ≤ st'.length := stackDepth_left _ _ _ hd
      have hix := ihx acc st st' hacc hdx
      have hdy : stackDepth y ≤ (evalStack cfg x :: st').length := by
        simp only [List.length_cons]; exact stackDepth_right _ _ _ hd
      have hiy := ihy (compileAcc x acc) st (evalStack cfg x :: st') hix hdy
      show runProg cfg (compileAcc y (compileAcc x acc) ++ [StackOp.mul]) st =
        some ((evalStack cfg x * evalStack cfg y) :: st')
      rw [runProg_append cfg (compileAcc y (compileAcc x acc)) [StackOp.mul] st
            (evalStack cfg y :: evalStack cfg x :: st') hiy]
      rfl

/-- **`StackExpr` 的栈深度恒为 1。**

与 `CExpr.depth` 同一形状（`lit`/`load` 给 1，二元节点 `max (d x) (d y - 1)`），
而叶子已贡献 1，所以 `- 1` 永不生效。**归纳与 `Geo.CExprCodegen.CExpr.depth_eq_one` 逐字同构。** -/
theorem stackDepth_eq_one {σ α : Type} (e : StackExpr σ α) : stackDepth e = 1 := by
  induction e with
  | lit a => rfl
  | load p => rfl
  | add x y ihx ihy =>
      show max (stackDepth x) (stackDepth y - 1) = 1
      rw [ihx, ihy]; decide
  | sub x y ihx ihy =>
      show max (stackDepth x) (stackDepth y - 1) = 1
      rw [ihx, ihy]; decide
  | mul x y ihx ihy =>
      show max (stackDepth x) (stackDepth y - 1) = 1
      rw [ihx, ihy]; decide

/-- **编译正确性**：运行生成的程序得到表达式的值。

**第 197 轮删掉了原来的 `(h : stackDepth e ≤ 1)` 假设。** 它是**恒真的**：
`stackDepth_eq_one` 说 `stackDepth e = 1`，而初始栈 `[seed]` 的长度也是 1，所以
`stackDepth e ≤ [seed].length` 自动成立。

⚠ **这类假设比未使用变量更隐蔽**：它在证明里**被使用**（传给 `compileAcc_correct`），
所以 `linter.unusedVariables` 不会报它。它在 `Geo.CExprCodegen` 里有一份**同款**，
第 195 轮已删；**上游这一份当时被漏掉了**——同款缺陷成对存在，正是本库反复出现的形态。 -/
theorem compileProg_correct [Add α] [Sub α] [Mul α] (cfg : σ → α) (e : StackExpr σ α) (seed : α) :
    runProg cfg (compileProg e) [seed] = some (evalStack cfg e :: [seed]) := by
  have := compileAcc_correct cfg e [] [seed] [seed] rfl (by simp [stackDepth_eq_one])
  simpa [compileProg] using this

/-! ## 5. 实例化：泛化的意义在于它真的能用 -/

/-- 具体程序：`(2 + 3) * 4`，在 `ℕ` 上，配置为空类型。 -/
def exampleNat : StackExpr Empty ℕ := .mul (.add (.lit 2) (.lit 3)) (.lit 4)

/-- **`ℕ` 实例真的算出 20。** 生成 5 条指令，运行得到 `[20, 0]`。 -/
theorem exampleNat_runs :
    runProg (fun e : Empty => nomatch e) (compileProg exampleNat) [0] = some (20 :: [0]) := by
  decide

/-- **`ℤ` 实例**：`-3 + 5 = 2`。 -/
def exampleInt : StackExpr Empty ℤ := .add (.lit (-3)) (.lit 5)

theorem exampleInt_runs :
    runProg (fun e : Empty => nomatch e) (compileProg exampleInt) [0] = some (2 :: [0]) := by
  decide

/-- **`Float` 实例存在**——这正是 `CExpr` 轨道需要的载体。

`Float` 的相等不可判定（`NaN`），所以这里只检查**程序长度**，不检查求值结果。
**这正是 `STATE-FINAL` §3.6.2 记录的 `Float` 单向性的具体体现**：生成器可用，
而「运行结果等于什么」不能由 `decide` 判定。 -/
def exampleFloat : StackExpr Empty Float := .mul (.add (.lit 2.0) (.lit 3.0)) (.lit 4.0)

theorem exampleFloat_compiles : (compileProg exampleFloat).length = 5 := by
  decide

/-- **`CExpr` 的常量类型是 `Float`，而 `StackExpr _ Float` 就是这个载体。** -/
theorem float_is_a_valid_carrier : Nonempty (StackExpr Empty Float) := ⟨exampleFloat⟩

end Lattice.Lift.StackCodegen

