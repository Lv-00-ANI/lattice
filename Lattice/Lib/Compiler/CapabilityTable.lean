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

/-- **⭐⭐ 着英行：`a·t + b`，常数 **0**——不是近似，而是**精确**。**

**⇒ 这是表结构的第一次真实压力测试：前两行是**无参的常数**（`squareRow`、`cubeRow`），
而这一行是**带参的族元素**——`affineRow a b`。**

**⇒ 它也是能力表里最容易被忽略的一档：**某族不是近似，而是精确**。
常数 0 在表里不是缺失的数据，而是**最强的一种声明**。** -/
noncomputable def affineRow (a b : ℝ) : CapabilityRow where
  degree := 1
  term := affineTerm a b
  fn := fun t : ℝ => a * t + b
  target := .affine a b
  semantics := by
    intro x
    have h := evalSym_affineTerm a b x
    have heq : (fun t : ℝ => a * t + b) x = a * x + b := rfl
    rw [heq]
    exact h
  compiled := by
    intro r
    exact compileTarget_affineTerm r a b
  family_eq := by
    intro r k
    -- **左边是常族，右边是仿射函数的插值族，两者相等由 `interpFamily_affine` 给出。**
    show affineFamily a b k = interpFamily r.n (fun t : ℝ => a * t + b) k
    rw [interpFamily_affine r.n r.hn a b]
  constant := 0
  bound := by
    intro n hn x hx
    -- **插值就是该仿射函数本身，故差为零。**
    rw [interpFamily_affine n hn a b, gridEval_affineFamily]
    show |(fun t : ℝ => a * t + b) x - (a * x + b)| ≤ 0 * (1 / (n : ℝ)) ^ 2
    simp

/-- **⭐⭐ 仿射行是**精确**的：差为**零**（不是「不超过 0」那种弱说法）。**

**⇒ 与 `bound` 字段相比，本条去掉了绝对值与不等号——它说的是**恰好相等**。** -/
theorem affineRow_exact (a b : ℝ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (affineRow a b).fn x - gridEval (interpFamily n (affineRow a b).fn) n x = 0 := by
  show (fun t : ℝ => a * t + b) x - gridEval (interpFamily n (fun t : ℝ => a * t + b)) n x = 0
  rw [interpFamily_affine n hn a b, gridEval_affineFamily]
  simp

/-- **⭐⭐ 表中常数的顺序：`0 ≤ 1/4 < 3/4`。**

**⇒ 把能力强弱变成一条可引用的链：仿射（精确，常数 `0`）不弱于二次，
二次严格优于三次（同 `n` 下）。**

**⇒ 第一段写 `≤` 而非 `<`：它在表中的作用是“常数 0 是最低档”，
而**严格性**只在第二段有意义（两个不同的近似族之间）。** -/
theorem constants_ordered (a b : ℝ) :
    (affineRow a b).constant ≤ squareRow.constant ∧ squareRow.constant < cubeRow.constant := by
  constructor
  · show (0 : ℝ) ≤ 1 / 4
    norm_num
  · exact cube_constant_exceeds_square

/-! ## 四、从表到选择：给定精度，选出一行，并证明它真的达到 -/

/-- **一次请求**：目标精度 `eps` 与网格次 `n`。** -/
structure Request where
  /-- The requested uniform precision on `[0,1]`. -/
  eps : ℝ
  /-- The grid resolution. -/
  n : ℕ
  /-- The grid is non-degenerate. -/
  hn : 0 < n

/-- **表所能**证明**的充分条件：`constant / n² ≤ eps`。

**⇒ 它不是「可能达到」的弱说法，而是**表里每一行的 `bound` 字段直接给出」的那个不等式。**
**⇒ 因此选择器不需要知道该行的由来，只需比较这一个数。** -/
def sufficient (row : CapabilityRow) (req : Request) : Prop :=
  row.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps

/-- **⭐⭐ 充分条件 ⟹ 整域达标。**

**⇒ 一步 `le_trans`：行的界（`row.bound`）+ 充分条件。**
**⇒ 这就是「能力可传参」的实际用法：调用者拿一行与一个 `Request`，不看任何实现细节。** -/
theorem sufficient_implies_meets (row : CapabilityRow) (req : Request)
    (h : sufficient row req) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |row.fn x - gridEval (interpFamily req.n row.fn) req.n x| ≤ req.eps := by
  intro x hx
  exact le_trans (row.bound req.n req.hn x hx) h

/-- **选择器**：在表里找**第一个**满足充分条件的行。

**⇒ 「第一个」是**故意的**：表的顺序就是优先级。
把精确行（常数 0）放在前面，就会优先选它——见 `select_affine_first`。** -/
noncomputable def select (req : Request) (rows : List CapabilityRow) : Option CapabilityRow := by
  -- **实数比较的 `Decidable` 只在 `Classical` 下可用。**
  classical
  exact rows.find? (fun row => decide (sufficient row req))

/-- **⭐⭐ 选出来的行**确实满足充分条件**。

**⇒ 由 `List.find?_some` 与 `of_decide_eq_true`。注意这里的方向：
`find?` 只保证“它为真”，**不**保证“它最优”——后者需要另立声明。** -/
theorem select_sound {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) : sufficient row req := by
  classical
  unfold select at h
  exact of_decide_eq_true (List.find?_some (p := fun row => decide (sufficient row req)) h)

/-- **⭐⭐⭐ 主定理：被选中的行**整域达到请求精度**。**

**⇒ 两步：`select_sound` 给出充分条件，`sufficient_implies_meets` 把它变成整域界。**
**⇒ 这就是规划 §2.1 第 4 层要的东西：**能力选择与证明编排**——选择器的输出直接带着证明。** -/
theorem select_gives_precision {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |row.fn x - gridEval (interpFamily req.n row.fn) req.n x| ≤ req.eps :=
  sufficient_implies_meets row req (select_sound h)

/-- **⭐⭐ 精确优先：若 `eps ≥ 0`，则把仿射行放在表首就会被选中。**

**⇒ 因为它的常数是 `0`，故充分条件退化为 `0 ≤ eps`。**
**⇒ 这使「精确优于近似」成为一条**可执行的选择规则**，而不只是一句评价。** -/
theorem select_affine_first (a b : ℝ) (req : Request) (heps : 0 ≤ req.eps)
    (tail : List CapabilityRow) :
    select req (affineRow a b :: tail) = some (affineRow a b) := by
  classical
  unfold select
  apply List.find?_cons_of_pos
  apply decide_eq_true
  show (affineRow a b).constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
  show (0 : ℝ) * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
  simpa using heps

end Lattice.Lib.Compiler.CapabilityTable