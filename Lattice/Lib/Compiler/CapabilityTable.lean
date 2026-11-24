import Lattice.Lib.Compiler.CubicFamily
import Lattice.Lib.Compiler.GridBound

/-!
# **能力表：一条可引用的「按族声明能力」清单**

## 为什么需要它

**到上一轮为止，三个族的能力散在三个文件里，各自的定理名不同、域不同、常数写法的形状也不同。
⇒ 规划 §5.2 要求「手工列出配方」；§1.6 要求「能力选择必须有规则」。
⇒ 而**散落**的清单无法被引用，只能被**阅读**。**

**⇒ 本文件把每个族压成一行**结构体**，其中**每一个字段都是一个已证的命题**：

| 字段 | 含义 |
|:--|:--|
| `semantics` | 该符号项的**源语义**就是 `fn` |
| `compiled` | 编译器在该项上**确实**产出 `target` |
| `family_eq` | `target` 的族**就是** `fn` 的插值族 |
| `bound` | 整域界：`\|fn − 插值\| ≤ constant · (1/n)²` |

**⇒ 于是「能力」不再是一句描述，而是一个**可以传参、可以遍历、可以逐行引用**的对象。**
**⇒ 而 `table_gives_bounds` 说明：拿到一张表，就等于拿到表里每一行的界——不需要知道行的来历。**

## 一行里为什么有 `target` 而不是只用 `fn`

**因为两个族到达同一族的方式不同：`x²` 经 `.squareApprox`（专用离散化），
`x³` 经 `.interp`（一般插值）。⇒ 若只记 `fn`，就丢掉了「编译器是怎么到达的」这一信息，
而 `family_eq` 字段正是把它与 `fn` 的插值族**接起来**的那一步。**
-/

namespace Lattice.Lib.Compiler.CapabilityTable

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.CubicFamily
open Lattice.Lib.Compiler.GridBound
open Lattice.Lib.Compiler.InterpAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.Samples
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.SymbolicEntry.Target

/-- **能力表的一行**：一个符号项、它说的函数、它被编译到哪个目标、以及**被证明的**整域界。 -/
structure CapabilityRow where
  /-- The degree of the monomial this row covers. -/
  degree : ℕ
  /-- The symbolic term. -/
  term : ExprExt
  /-- The real function the term denotes. -/
  fn : ℝ → ℝ
  /-- The compile target the term reaches. -/
  target : Target
  /-- **Source semantics**: the term denotes `fn` at every point. -/
  semantics : ∀ x : ℝ, evalSym x term = some (fn x)
  /-- **Compilation**: the compiler reaches exactly this target on this term. -/
  compiled : ∀ r : CompileRecipe, compileTarget r term = some target
  /-- **Family agreement**: the target's family is the interpolation family of `fn`. -/
  family_eq : ∀ (r : CompileRecipe) (k : ℕ), Target.family r target k = interpFamily r.n fn k
  /-- The constant `C` in `error <= C / n^2`. -/
  constant : ℝ
  /-- **The bound**, on the closed unit interval. -/
  bound : ∀ (n : ℕ), 0 < n → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |fn x - gridEval (interpFamily n fn) n x| ≤ constant * (1 / (n : ℝ)) ^ 2

/-- **⭐ 第 2 行：`x²`，常数 `1/4`。** -/
noncomputable def squareRow : CapabilityRow where
  degree := 2
  term := squareTerm
  fn := fun t : ℝ => t ^ 2
  target := .squareApprox
  semantics := by
    intro x
    rw [evalSym_squareTerm]
    congr 1
    -- **`(fun t => t ^ 2) x` 要 beta 归约，`ring` 一步同时处理它与 `pow_two`。**
    ring
  compiled := by
    intro r
    exact compileTarget_squareTerm r
  family_eq := by
    intro r k
    show decodeGrid (piecewiseIRWeights r.n) k = interpFamily r.n (fun t : ℝ => t ^ 2) k
    rw [interpFamily_sq r.n r.hn]
  constant := 1 / 4
  bound := by
    intro n hn x hx
    -- **先把目标写成既有定理的形状（去掉 lambda 应用）。**
    show |x ^ 2 - gridEval (interpFamily n (fun t : ℝ => t ^ 2)) n x|
        ≤ 1 / 4 * (1 / (n : ℝ)) ^ 2
    have h := interpFamily_sq_error n hn x hx
    have heq : (1 / (n : ℝ)) ^ 2 / 4 = 1 / 4 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h

/-- **⭐ 第 3 行：`x³`，常数 `3/4`。** -/
noncomputable def cubeRow : CapabilityRow where
  degree := 3
  term := cubeTerm
  fn := fun t : ℝ => t ^ 3
  target := .interp (fun t : ℝ => t ^ 3)
  semantics := by
    intro x
    exact evalSym_cubeTerm x
  compiled := by
    intro r
    exact compileTarget_cubeTerm r
  family_eq := by
    intro r k
    rfl
  constant := 3 / 4
  bound := by
    intro n hn x hx
    show |x ^ 3 - gridEval (interpFamily n (fun t : ℝ => t ^ 3)) n x|
        ≤ 3 / 4 * (1 / (n : ℝ)) ^ 2
    have h := Lattice.Lib.Compiler.CubicFamily.cube_uniform_bound n hn x hx
    have heq : 3 * (1 / (n : ℝ)) ^ 2 / 4 = 3 / 4 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h

/-- **⭐⭐⭐ 表是可**消费**的：拿到一行，就拿到它的界。**

**⇒ 这条不是复述 `bound` 字段，而是说明「能力」可以**传参**：调用者不必知道该行来自哪个文件、
经哪条编译路径，只要它在表里，界就成立。** -/
theorem row_gives_bound (row : CapabilityRow) (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |row.fn x - gridEval (interpFamily n row.fn) n x| ≤ row.constant * (1 / (n : ℝ)) ^ 2 :=
  row.bound n hn x hx

/-- **⭐⭐ 表里同时有 `x²` 与 `x³`，且两行的常数不同。**

**⇒ 「不同常数」正是「按族声明能力」的内容：不是所有族同一个精度，也不是同一个数说了算。** -/
theorem table_has_two_rows :
    squareRow.degree = 2 ∧ cubeRow.degree = 3
      ∧ squareRow.constant = 1 / 4 ∧ cubeRow.constant = 3 / 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **⭐⭐ `x³` 的常数**严格大于** `x²` 的常数**。

**⇒ 这不是「三次更难」的修辞，而是两个具体有理数的比较：`1/4 < 3/4`。
⇒ 于是表给出的比较本身是一个**可证的**事实。** -/
theorem cube_constant_exceeds_square :
    squareRow.constant < cubeRow.constant := by
  show (1 : ℝ) / 4 < 3 / 4
  norm_num

end Lattice.Lib.Compiler.CapabilityTable