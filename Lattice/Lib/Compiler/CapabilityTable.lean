import Lattice.Lib.Compiler.CubicFamily
import Lattice.Lib.Compiler.GridBound

/-!
# **能力表：按**族**组织的一行，每个字段都是证明**

## 三条设计判断（第三条是第 1066 轮的重构）

**判断一：一行必须带 `target`，不能只带 `fn`。**
两个族**到达方式不同**（`x²` 经 `.squareApprox`，`x³` 经 `.interp`）；若只记 `fn`，就丢掉「编译器怎么到达的」。
`family_eq` 正是把到达的目标与 `fn` 的插值族**接起来**的那一步，而它对不同行需要不同的既有定理
（`interpFamily_sq`、`interpFamily_affine`，或直接 `rfl`）。

**判断二：行必须有 `constant` 与 `bound`，而不是文档里的期望。**
`bound` 写在**闭区间** `[0,1]` 上（第 1061 轮证明右端点插值精确，故半开限制可以去掉）。

**判断三（本轮）：行覆盖的是一**族函数**，不是单个函数。**
第 1065 轮的 `applicable := row.fn = req.goal` 是一条**函数等式**——它极强也极窄，
只能匹配**恰好那一个**函数。规划 §1.6 要的是「按能力族声明」，而一族覆盖一族函数。
**⇒ 因此引入 `covers : (ℝ → ℝ) → Prop` 与 `covers_bound`：界对**该族每个成员**成立。**

**⇒ 于是 `affineFamilyRow`（**无参**）可以覆盖**所有**仿射函数，而 `affineRow a b` 覆盖那一个。
两者并存不是冗余：前者是族的能力声明，后者是**具体符号项**的完成路径（含 `semantics`/`compiled`）。**
-/

namespace Lattice.Lib.Compiler.CapabilityTable

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.Samples
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler.InterpAlgebra
open Lattice.Lib.Compiler.GridBound
open Lattice.Lib.Compiler.CubicFamily
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.SymbolicEntry.Target

/-- **能力表的一行**：符号代表项、它被编译到哪个目标、它**覆盖哪一族函数**、以及**被证明的**整域界。 -/
structure CapabilityRow where
  /-- The degree of the monomial this row covers. -/
  degree : ℕ
  /-- The symbolic term, as the **representative** of the family. -/
  term : ExprExt
  /-- The function the representative term denotes. -/
  fn : ℝ → ℝ
  /-- The compile target the representative reaches. -/
  target : Target
  /-- **Source semantics** of the representative. -/
  semantics : ∀ x : ℝ, evalSym x term = some (fn x)
  /-- **Compilation** of the representative. -/
  compiled : ∀ r : CompileRecipe, compileTarget r term = some target
  /-- **Family agreement** for the representative. -/
  family_eq : ∀ (r : CompileRecipe) (k : ℕ), Target.family r target k = interpFamily r.n fn k
  /-- The constant `C` in `error <= C / n^2`. -/
  constant : ℝ
  /-- **The bound** for the representative, on the closed unit interval. -/
  bound : ∀ (n : ℕ), 0 < n → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |fn x - gridEval (interpFamily n fn) n x| ≤ constant * (1 / (n : ℝ)) ^ 2
  /-- **The family this row covers.** -/
  covers : (ℝ → ℝ) → Prop
  /-- The representative belongs to the family it covers. -/
  covers_self : covers fn
  /-- **The bound holds for EVERY member of the family**, not just the representative. -/
  covers_bound : ∀ g : ℝ → ℝ, covers g → ∀ (n : ℕ), 0 < n → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |g x - gridEval (interpFamily n g) n x| ≤ constant * (1 / (n : ℝ)) ^ 2

/-- **⭐ 第 2 行：`x²`，常数 `1/4`，覆盖**恰好**该函数。** -/
noncomputable def squareRow : CapabilityRow where
  degree := 2
  term := squareTerm
  fn := fun t : ℝ => t ^ 2
  target := .squareApprox
  semantics := by
    intro x
    rw [evalSym_squareTerm]
    congr 1
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
    show |x ^ 2 - gridEval (interpFamily n (fun t : ℝ => t ^ 2)) n x|
        ≤ 1 / 4 * (1 / (n : ℝ)) ^ 2
    have h := interpFamily_sq_error n hn x hx
    have heq : (1 / (n : ℝ)) ^ 2 / 4 = 1 / 4 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h
  covers := fun g => g = fun t : ℝ => t ^ 2
  covers_self := rfl
  covers_bound := by
    intro g hg n hn x hx
    subst hg
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
  covers := fun g => g = fun t : ℝ => t ^ 3
  covers_self := rfl
  covers_bound := by
    intro g hg n hn x hx
    subst hg
    show |x ^ 3 - gridEval (interpFamily n (fun t : ℝ => t ^ 3)) n x|
        ≤ 3 / 4 * (1 / (n : ℝ)) ^ 2
    have h := Lattice.Lib.Compiler.CubicFamily.cube_uniform_bound n hn x hx
    have heq : 3 * (1 / (n : ℝ)) ^ 2 / 4 = 3 / 4 * (1 / (n : ℝ)) ^ 2 := by ring
    rw [heq] at h
    exact h

/-- **⭐ 第 1 行（参数化）：某个具体仿射函数，常数 `0`。** -/
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
    show affineFamily a b k = interpFamily r.n (fun t : ℝ => a * t + b) k
    rw [interpFamily_affine r.n r.hn a b]
  constant := 0
  bound := by
    intro n hn x hx
    rw [interpFamily_affine n hn a b, gridEval_affineFamily]
    show |(fun t : ℝ => a * t + b) x - (a * x + b)| ≤ 0 * (1 / (n : ℝ)) ^ 2
    simp
  covers := fun g => g = fun t : ℝ => a * t + b
  covers_self := rfl
  covers_bound := by
    intro g hg n hn x hx
    subst hg
    rw [interpFamily_affine n hn a b, gridEval_affineFamily]
    show |(fun t : ℝ => a * t + b) x - (a * x + b)| ≤ 0 * (1 / (n : ℝ)) ^ 2
    simp

/-- **⭐⭐⭐ 第 0 行（**无参**）：**所有**仿射函数，常数 `0`。**

**⇒ 这才是规划 §1.6「按能力族声明」的字面意思：`covers` 不是一个函数等式，
而是「存在 `c`、`d` 使得 `g = c·t+d`」。**
**⇒ 代表项取 `0·t+0`：它的 `semantics`/`compiled` 描述**符号路径**，
而 `covers`/`covers_bound` 描述**族的范围**。两者各司其职，不互相冒充。** -/
noncomputable def affineFamilyRow : CapabilityRow where
  degree := 1
  term := affineTerm 0 0
  fn := fun t : ℝ => 0 * t + 0
  target := .affine 0 0
  semantics := by
    intro x
    have h := evalSym_affineTerm 0 0 x
    have heq : (fun t : ℝ => 0 * t + 0) x = 0 * x + 0 := rfl
    rw [heq]
    exact h
  compiled := by
    intro r
    exact compileTarget_affineTerm r 0 0
  family_eq := by
    intro r k
    show affineFamily 0 0 k = interpFamily r.n (fun t : ℝ => 0 * t + 0) k
    rw [interpFamily_affine r.n r.hn 0 0]
  constant := 0
  bound := by
    intro n hn x hx
    rw [interpFamily_affine n hn 0 0, gridEval_affineFamily]
    show |(fun t : ℝ => 0 * t + 0) x - (0 * x + 0)| ≤ 0 * (1 / (n : ℝ)) ^ 2
    simp
  covers := fun g => ∃ c d : ℝ, g = fun t : ℝ => c * t + d
  covers_self := ⟨0, 0, rfl⟩
  covers_bound := by
    intro g hg n hn x hx
    obtain ⟨c, d, hg⟩ := hg
    subst hg
    rw [interpFamily_affine n hn c d, gridEval_affineFamily]
    show |(fun t : ℝ => c * t + d) x - (c * x + d)| ≤ 0 * (1 / (n : ℝ)) ^ 2
    simp

/-! ## 四、从表到选择：给定目标与精度，选出一行 -/

/-- **一次请求**：一个**目标函数**、目标精度 `eps`、网格次 `n`。 -/
structure Request where
  /-- The target function. -/
  goal : ℝ → ℝ
  /-- The requested uniform precision on `[0,1]`. -/
  eps : ℝ
  /-- The grid resolution. -/
  n : ℕ
  /-- The grid is non-degenerate. -/
  hn : 0 < n

/-- **适用**：该行的**族**含有目标函数。

**⇒ 第 1066 轮把它从 `row.fn = req.goal` 改为 `row.covers req.goal`：
前者只能匹配一个函数，后者可以是一整族。** -/
def applicable (row : CapabilityRow) (req : Request) : Prop := row.covers req.goal

/-- **充分条件**：适用且 `constant / n² ≤ eps`。 -/
def sufficient (row : CapabilityRow) (req : Request) : Prop :=
  applicable row req ∧ row.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps

/-- **⭐⭐ 充分条件 ⟹ 整域达标（说的是目标函数）。**

**⇒ 一步用 `covers_bound`（对**族内每个成员**成立）加一步 `le_trans`。** -/
theorem sufficient_implies_meets (row : CapabilityRow) (req : Request)
    (h : sufficient row req) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps := by
  obtain ⟨hcov, hbound⟩ := h
  intro x hx
  exact le_trans (row.covers_bound req.goal hcov req.n req.hn x hx) hbound

/-- **选择器**：在表里找**第一个**既适用又满足精度的行。 -/
noncomputable def select (req : Request) (rows : List CapabilityRow) : Option CapabilityRow := by
  classical
  exact rows.find? (fun row => decide (sufficient row req))

/-- **⭐⭐ 选出来的行既**适用**又**达标**。 -/
theorem select_sound {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) : sufficient row req := by
  classical
  unfold select at h
  exact of_decide_eq_true (List.find?_some (p := fun row => decide (sufficient row req)) h)

/-- **⭐⭐⭐ 主定理：被选中的行整域达到请求精度。** -/
theorem select_gives_precision {req : Request} {rows : List CapabilityRow} {row : CapabilityRow}
    (h : select req rows = some row) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps :=
  sufficient_implies_meets row req (select_sound h)

/-! ## 五、选择器的行为 -/

/-- **仿射函数不是 `t ↦ t²`**（三点定値）。 -/
theorem affine_fn_ne_square (a b : ℝ) :
    (fun t : ℝ => a * t + b) ≠ (fun t : ℝ => t ^ 2) := by
  intro h
  have h0 : a * 0 + b = (0 : ℝ) ^ 2 := by simpa using congrFun h 0
  have h1 : a * 1 + b = (1 : ℝ) ^ 2 := by simpa using congrFun h 1
  have h2 : a * 2 + b = (2 : ℝ) ^ 2 := by simpa using congrFun h 2
  norm_num at h0 h1 h2
  linarith

/-- **⭐⭐⭐ `t ↦ t²` 不属于仿射族。**

**⇒ 这是新的否定结果：它使「族行」（`affineFamilyRow`）也**恰好拒绝**二次目标，
而不是「因为只匹配一个函数所以拒绝」。** -/
theorem square_not_affine :
    ¬ ∃ c d : ℝ, (fun t : ℝ => t ^ 2) = fun t : ℝ => c * t + d := by
  rintro ⟨c, d, h⟩
  exact affine_fn_ne_square c d h.symm

/-- **⭐⭐ 仿射行不适用于 `x²` 目标。** -/
theorem affine_not_sufficient_for_square (a b : ℝ) (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2) :
    ¬ sufficient (affineRow a b) req := by
  intro h
  have hcov : applicable (affineRow a b) req := h.1
  -- **合成两个假设：`hgoal : goal = t²`，`hcov : goal = a·t+b`，故 `t² = a·t+b`。**
  have hfun : (fun t : ℝ => t ^ 2) = (fun t : ℝ => a * t + b) := by
    rw [← hgoal]
    exact hcov
  exact affine_fn_ne_square a b hfun.symm

/-- **⭐⭐ 族行也不适用于 `x²` 目标**（因为 `x²` 不是仿射函数）。 -/
theorem affineFamily_not_sufficient_for_square (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2) :
    ¬ sufficient affineFamilyRow req := by
  intro h
  have hcov : applicable affineFamilyRow req := h.1
  have h' : ∃ c d : ℝ, (fun t : ℝ => t ^ 2) = fun t : ℝ => c * t + d := by
    obtain ⟨c, d, hcd⟩ := hcov
    exact ⟨c, d, by rw [← hgoal]; exact hcd⟩
  exact square_not_affine h'

/-- **⭐⭐⭐ 当目标是 `x²` 且精度满足时，选择器跨过仿射行、选中二次行。** -/
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
    · show squareRow.covers req.goal
      rw [hgoal]
      rfl
    · show squareRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      show (1 : ℝ) / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      exact heps
  · have hfalse : decide (sufficient (affineRow a b) req) = false :=
      decide_eq_false (affine_not_sufficient_for_square a b req hgoal)
    simpa using hfalse

/-- **⭐⭐ 精确优先：当目标本身就是仿射函数时，仿射行被选中。** -/
theorem select_affine_first (a b : ℝ) (req : Request)
    (hgoal : req.goal = fun t : ℝ => a * t + b) (heps : 0 ≤ req.eps)
    (tail : List CapabilityRow) :
    select req (affineRow a b :: tail) = some (affineRow a b) := by
  classical
  unfold select
  apply List.find?_cons_of_pos
  apply decide_eq_true
  constructor
  · show (affineRow a b).covers req.goal
    rw [hgoal]
    rfl
  · show (affineRow a b).constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    show (0 : ℝ) * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    simpa using heps

/-- **⭐⭐ 族行在仿射目标下也被选中**（它覆盖**所有**仿射函数）。 -/
theorem select_affineFamily_row (req : Request)
    (hgoal : ∃ c d : ℝ, req.goal = fun t : ℝ => c * t + d) (heps : 0 ≤ req.eps) :
    select req (affineFamilyRow :: [squareRow]) = some affineFamilyRow := by
  classical
  unfold select
  apply List.find?_cons_of_pos
  apply decide_eq_true
  constructor
  · show affineFamilyRow.covers req.goal
    exact hgoal
  · show affineFamilyRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    show (0 : ℝ) * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
    simpa using heps

/-- **⭐⭐ 表里三个常数的顺序：`0 ≤ 1/4 < 3/4`。** -/
theorem constants_ordered (a b : ℝ) :
    (affineRow a b).constant ≤ squareRow.constant ∧ squareRow.constant < cubeRow.constant := by
  constructor
  · show (0 : ℝ) ≤ 1 / 4
    norm_num
  · show (1 : ℝ) / 4 < 3 / 4
    norm_num

end Lattice.Lib.Compiler.CapabilityTable