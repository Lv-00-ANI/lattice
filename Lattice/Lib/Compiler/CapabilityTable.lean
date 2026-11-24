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

/-! ## 四、从表到选择：给定目标与精度，选出一行，并证明它真的达到 -/

/-- **一次请求**：一个**目标函数**、目标精度 `eps`、网格次 `n`。

**⇒ `goal` 是第 1065 轮加的字段，而它的存在修正了一个**真缺陷**：
此前的 `sufficient` 只比较常数，**不检查行是否适用于该目标**。
于是一个仿射行（常数 0）在**任何** `eps ≥ 0` 下都看起来“满足”——
即使目标是 `x²`。那不是优先级，**那是错误**。** -/
structure Request where
  /-- The target function. -/
  goal : ℝ → ℝ
  /-- The requested uniform precision on `[0,1]`. -/
  eps : ℝ
  /-- The grid resolution. -/
  n : ℕ
  /-- The grid is non-degenerate. -/
  hn : 0 < n

/-- **适用**：该行说的函数**就是**目标函数。

**⇒ 这是一条**等式**，而不是一个弱一点的条件：一行若不适用于目标，
它的界**根本不关于**该目标。** -/
def applicable (row : CapabilityRow) (req : Request) : Prop := row.fn = req.goal

/-- **表所能**证明**的充分条件：**适用**且 `constant / n² ≤ eps`。** -/
def sufficient (row : CapabilityRow) (req : Request) : Prop :=
  applicable row req ∧ row.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps

/-- **⭐⭐ 充分条件 ⟹ 整域达标（**说的是目标函数**，不是该行的 `fn`）。**

**⇒ 一步 `rw`（用 `applicable` 把 `row.fn` 换成 `req.goal`）加一步 `le_trans`。** -/
theorem sufficient_implies_meets (row : CapabilityRow) (req : Request)
    (h : sufficient row req) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps := by
  obtain ⟨happ, hbound⟩ := h
  intro x hx
  have hb := row.bound req.n req.hn x hx
  rw [happ] at hb
  exact le_trans hb hbound

/-- **选择器**：在表里找**第一个**既适用又满足精度的行。

**⇒ 「第一个」是**故意的**：表的顺序就是优先级。** -/
noncomputable def select (req : Request) (rows : List CapabilityRow) : Option CapabilityRow := by
  classical
  exact rows.find? (fun row => decide (sufficient row req))

/-- **⭐⭐ 选出来的行既**适用**又**达标**。 -/
theorem select_sound {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) : sufficient row req := by
  classical
  unfold select at h
  exact of_decide_eq_true (List.find?_some (p := fun row => decide (sufficient row req)) h)

/-- **⭐⭐⭐ 主定理：被选中的行**整域达到请求精度**（因为它适用）。** -/
theorem select_gives_precision {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps :=
  sufficient_implies_meets row req (select_sound h)

/-! ## 五、选择器的两个真实行为 -/

/-- **⭐⭐ 仿射函数**不是** `t ↦ t²`（三点定値）。 -/
theorem affine_fn_ne_square (a b : ℝ) :
    (fun t : ℝ => a * t + b) ≠ (fun t : ℝ => t ^ 2) := by
  intro h
  -- **从函数相等取三个点的值；`rw [h]` 在这里失败，
  -- 因为目标里的 lambda 应用已被 beta 归约。**
  have h0 : a * 0 + b = (0 : ℝ) ^ 2 := by simpa using congrFun h 0
  have h1 : a * 1 + b = (1 : ℝ) ^ 2 := by simpa using congrFun h 1
  have h2 : a * 2 + b = (2 : ℝ) ^ 2 := by simpa using congrFun h 2
  norm_num at h0 h1 h2
  linarith

/-- **⭐⭐⭐ 仿射行**不适用**于 `x²` 目标——故构造上不可能被选中。

**⇒ 这就是对第 1051 轮 `capability_rule`（`eps < 1/8` 排除仿射族）的**构造侧对应**：
那一条说「不可能达到」，这一条说「不会被选中」，而且后者对**任意** `eps`（含 `eps ≥ 0`）成立。** -/
theorem affine_not_sufficient_for_square (a b : ℝ) (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2) :
    ¬ sufficient (affineRow a b) req := by
  intro h
  have happ : applicable (affineRow a b) req := h.1
  have hfun : (fun t : ℝ => a * t + b) = (fun t : ℝ => t ^ 2) := by
    show (affineRow a b).fn = fun t : ℝ => t ^ 2
    rw [happ, hgoal]
  exact affine_fn_ne_square a b hfun

/-- **⭐⭐⭐ 当目标是 `x²` 且精度满足时，选择器**跨过仿射行、选中二次行**。

**⇒ 这是表结构第二次压力测试的结果：第一次（参数化行）**通过**，
第二次（目标匹配）**暴露了真缺陷**，修正后才通过。** -/
theorem select_square_row (a b : ℝ) (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2)
    (heps : 1 / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps) :
    select req (affineRow a b :: [squareRow]) = some squareRow := by
  classical
  unfold select
  rw [List.find?_cons_of_neg]
  · apply List.find?_cons_of_pos
    apply decide_eq_true
    constructor
    · show squareRow.fn = req.goal
      rw [hgoal]
      rfl
    · show squareRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      show (1 : ℝ) / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      exact heps
  · -- **表头被跳过：它不适用于 `x²` 目标。**
    have hfalse : decide (sufficient (affineRow a b) req) = false :=
      decide_eq_false (affine_not_sufficient_for_square a b req hgoal)
    simpa using hfalse

/-- **⭐⭐ 精确优先（**当目标本身就是仿射函数时**）。**

**⇒ 与 `select_square_row` 对照：同一个选择器，在仿射目标下选仿射行、
在二次目标下跨过它。**⇒ 选择的正确性正在于它区分了这两种情形。** -/
theorem select_affine_first (a b : ℝ) (req : Request)
    (hgoal : req.goal = fun t : ℝ => a * t + b) (heps : 0 ≤ req.eps)
    (tail : List CapabilityRow) :
    select req (affineRow a b :: tail) = some (affineRow a b) := by
  classical
  unfold select
  apply List.find?_cons_of_pos
  apply decide_eq_true
  constructor
  · -- **适用：目标就是该仿射函数。**
    show (affineRow a b).fn = req.goal
    rw [hgoal]
    rfl
  · -- **精度：常数 0 使充分条件退化为 `0 ≤ eps`。**
    show (affineRow a b).constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    show (0 : ℝ) * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    simpa using heps

end Lattice.Lib.Compiler.CapabilityTable
