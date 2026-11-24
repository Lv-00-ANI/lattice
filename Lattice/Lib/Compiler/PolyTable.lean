import Lattice.Lib.Compiler.CapabilityTable
import Lattice.Lib.Compiler.QuarticFamily

/-!
# **按度数索引的能力表：从「查表」到「编排」**

## 这一层补什么

**`CapabilityTable.select` 只在一个**固定列表**里查找。规划 §2.1 第 4 层要的是「能力与**证明编排**」，
而编排的前提是：能力**可以按某个参数索引**，从而「先试小的、再试大的」。

**⇒ 本文件引入 `polyRow : ℕ → Option CapabilityRow`：给定**多项式度数**，返回覆盖该度数的行（若库里有）。**

**⇒ 于是「选择」变成**沿度数递增的阶梯**：`d = 1, 2, 3` 依次尝试。
而这正是「低度优先」的机制——**低度行（尤其精确的仿射行）更便宜**，故先试它。**

## 为什么返回值是 `Option` 而不是 `CapabilityRow`

**因为库**并不覆盖所有度数**。`polyRow 0 = none`（常函数不是本文件的关注对象）、
`polyRow 4 = none`（四次族尚未建立）。**⇒ 用 `Option` 就把「未覆盖」写成**类型的一部分**，
而不是靠调用者去猜。**

**⇒ 而「未覆盖」在本文件里也是**被证明**的（`polyRow_four`），不是文档里的一句话。**
-/

namespace Lattice.Lib.Compiler.PolyTable

open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.CapabilityTable
open Lattice.Lib.Compiler.QuarticFamily

/-- **按度数索引的行**：库覆盖 `1`、`2`、`3`、`4` 四档；其余为 `none`。 -/
noncomputable def polyRow : ℕ → Option CapabilityRow
  | 1 => some affineFamilyRow
  | 2 => some squareRow
  | 3 => some cubeRow
  | 4 => some quarticRow
  | _ => none

/-- **⭐ 度数 1 对应无参的仿射**族行**（常数 0）。** -/
theorem polyRow_one : polyRow 1 = some affineFamilyRow := rfl

/-- **⭐ 度数 2 对应二次行（常数 `1/4`）。** -/
theorem polyRow_two : polyRow 2 = some squareRow := rfl

/-- **⭐ 度数 3 对应三次行（常数 `3/4`）。** -/
theorem polyRow_three : polyRow 3 = some cubeRow := rfl

/-- **⭐ 度数 0 未覆盖。** -/
theorem polyRow_zero : polyRow 0 = none := rfl

/-- **⭐⭐⭐ 度数 4 **现已覆盖**——上一轮的边界被推高了一格。

**⇒ 这是对上一轮那句「若将来证出四次族的界，只需在此函数上加一支」
的**实践**：加的正是一支，而其余各层（选择器、桥、精度保证）**一行未动**。** -/
theorem polyRow_four : polyRow 4 = some quarticRow := rfl

/-- **⭐⭐ 未覆盖的度数**恰好是 `0` 与 `≥ 4`。** -/
theorem polyRow_none_iff (d : ℕ) : polyRow d = none ↔ d = 0 ∨ 5 ≤ d := by
  constructor
  · intro h
    match d with
    | 0 => exact Or.inl rfl
    | 1 => rw [polyRow_one] at h; simp at h
    | 2 => rw [polyRow_two] at h; simp at h
    | 3 => rw [polyRow_three] at h; simp at h
    | 4 => rw [polyRow_four] at h; simp at h
    | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))) => exact Or.inr (by omega)
  · rintro (rfl | h)
    · rfl
    · match d with
      | 0 => omega
      | 1 => omega
      | 2 => omega
      | 3 => omega
      | 4 => omega
      | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ _)))) => simp [polyRow]

/-- **⭐⭐ 按度数递增尝试**：`1, 2, 3` 依次，取第一个适用的。 -/
noncomputable def selectByDegree (req : Request) : Option CapabilityRow :=
  select req [affineFamilyRow, squareRow, cubeRow]

/-! ## 一、两个新的否证事实：度数之间的区别

**阶梯要成立，必须证明「上一档不适用」。⇒ 下面两条都是**三点定值**的变体。** -/

/-- **⭐⭐ `t ↦ t³` 不属仿射族。** -/
theorem cube_not_affine :
    ¬ ∃ c d : ℝ, (fun t : ℝ => t ^ 3) = fun t : ℝ => c * t + d := by
  rintro ⟨c, d, h⟩
  have h0 : c * 0 + d = (0 : ℝ) ^ 3 := by simpa using (congrFun h 0).symm
  have h1 : c * 1 + d = (1 : ℝ) ^ 3 := by simpa using (congrFun h 1).symm
  have h2 : c * 2 + d = (2 : ℝ) ^ 3 := by simpa using (congrFun h 2).symm
  norm_num at h0 h1 h2
  linarith

/-- **⭐⭐ `t ↦ t²` 与 `t ↦ t³` 不是同一个函数**（在 `t = 2` 处取值不同）。** -/
theorem square_ne_cube : (fun t : ℝ => t ^ 2) ≠ (fun t : ℝ => t ^ 3) := by
  intro h
  have h2 : (2 : ℝ) ^ 2 = (2 : ℝ) ^ 3 := by simpa using congrFun h 2
  norm_num at h2

/-! ## 二、阶梯的两个落点 -/

/-- **⭐⭐ 二次目标在三次行被排除后**落到度数 2**。** -/
theorem square_not_cube_row (req : Request) (hgoal : req.goal = fun t : ℝ => t ^ 2) :
    ¬ sufficient cubeRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  have hcov' : req.goal = fun t : ℝ => t ^ 3 := hcov
  have : (fun t : ℝ => t ^ 2) = fun t : ℝ => t ^ 3 := by
    rw [← hgoal]
    exact hcov'
  exact square_ne_cube this

/-- **⭐⭐ 度数 3 的目标准时落到三次行**（仿射与二次两档都被排除）。** -/
theorem cube_not_square_row (req : Request) (hgoal : req.goal = fun t : ℝ => t ^ 3) :
    ¬ sufficient squareRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  have hcov' : req.goal = fun t : ℝ => t ^ 2 := hcov
  have : (fun t : ℝ => t ^ 3) = fun t : ℝ => t ^ 2 := by
    rw [← hgoal]
    exact hcov'
  exact square_ne_cube this.symm

/-- **⭐⭐ 度数 3 不属仿射族**（于是 `affineFamilyRow` 也被跳过）。** -/
theorem affineFamily_not_sufficient_for_cube (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 3) :
    ¬ sufficient affineFamilyRow req := by
  intro h
  obtain ⟨hcov, _⟩ := h
  obtain ⟨c, d, hcd⟩ := hcov
  have hcube : (fun t : ℝ => t ^ 3) = fun t : ℝ => c * t + d := by
    rw [← hgoal]
    exact hcd
  exact cube_not_affine ⟨c, d, hcube⟩

/-! ## 三、从生成器到列表：上界成为**参数** -/

/-- **由 `polyRow` 生成的表**：取度数 `< dmax` 的那些行，保序。

**⇒ 用**递归**而不是 `List.range`：`List.range` 的等式不按 `rfl` 化简，
而**这里需要等式能像定义那样直接算出来**。

**⇒ 「表里有什么」完全由 `polyRow` 决定，而「能承受多高的度数」是调用者的一个**参数**。
这才是编排，而不是查找。** -/
noncomputable def degreeList : ℕ → List CapabilityRow
  | 0 => []
  | (n + 1) => degreeList n ++ (polyRow n).toList

/-- **⭐ 上界 `0` 时表为空。** -/
theorem degreeList_zero : degreeList 0 = [] := rfl

/-- **⭐ 上界 `1` 时表为空**——因为它只覆盖度数 `0`，而 `polyRow 0 = none`。

**⇒ 这一条是**必要的提醒**：`degreeList dmax` 覆盖 `0 .. dmax-1`，
故**仿射行在 `dmax = 2` 时才出现**。把它当成“第一行”会把上界弄错一位。** -/
theorem degreeList_one : degreeList 1 = [] := by
  simp [degreeList, polyRow]

/-- **⭐ 上界 `2` 时只有仿射族行。** -/
theorem degreeList_two : degreeList 2 = [affineFamilyRow] := by
  simp [degreeList, polyRow]

/-- **⭐⭐ 上界 `4` 时的表**恰好是那三行，且次序为**仿射 → 二次 → 三次**。

**⇒ 这条把「生成器」与「硬写列表」**接起来**：于是下一条可以说
`selectByDegree` 不是另一条路，而是 `selectUpTo req 4` 的**实例**。** -/
theorem degreeList_four : degreeList 4 = [affineFamilyRow, squareRow, cubeRow] := by
  simp [degreeList, polyRow]

/-- **⭐⭐ 按上界选择**：只在度数 `< dmax` 的行里选。 -/
noncomputable def selectUpTo (req : Request) (dmax : ℕ) : Option CapabilityRow :=
  select req (degreeList dmax)

/-- **⭐ `select` 在空表上返回 `none`。**

**⇒ `select` 是带 `classical` 的定义，`simp` 展不开它；故单独立一条引理。** -/
theorem select_nil (req : Request) : select req [] = none := by
  classical
  unfold select
  rfl

/-- **⭐ 上界 `0` 时无行可选**——因为表是空的。 -/
theorem selectUpTo_zero (req : Request) : selectUpTo req 0 = none := by
  unfold selectUpTo
  rw [degreeList_zero, select_nil]

/-- **⭐⭐⭐ `selectByDegree` **就是** `selectUpTo req 4`。

**⇒ 上一轮遗留的问题：`selectByDegree` 当时硬写了三元列表，**它根本没用上 `polyRow`**。
本条证明两者相同，故硬写的那个只是生成器在 `dmax = 4` 处的**特例**。** -/
theorem selectByDegree_eq_selectUpTo (req : Request) :
    selectByDegree req = selectUpTo req 4 := by
  unfold selectByDegree selectUpTo
  rw [degreeList_four]

/-! ## 四、上界是**保证**，不只是过滤条件 -/

/-- **⭐⭐ `polyRow d` 产生的行度数恰好是 `d`。**

**⇒ 这是 `polyRow` 的**一致性**：下一层要说「表里的行都低于上界」，
而那一步靠的就是**索引与字段一致**。** -/
theorem polyRow_degree (d : ℕ) (row : CapabilityRow) (h : row ∈ (polyRow d).toList) :
    row.degree = d := by
  match d with
  | 0 => rw [polyRow_zero] at h; simp at h
  | 1 =>
      rw [polyRow_one] at h
      simp only [Option.toList_some, List.mem_singleton] at h
      rw [h]
      rfl
  | 2 =>
      rw [polyRow_two] at h
      simp only [Option.toList_some, List.mem_singleton] at h
      rw [h]
      rfl
  | 3 =>
      rw [polyRow_three] at h
      simp only [Option.toList_some, List.mem_singleton] at h
      rw [h]
      rfl
  | 4 =>
      rw [polyRow_four] at h
      simp only [Option.toList_some, List.mem_singleton] at h
      rw [h]
      rfl
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ k)))) =>
      have hnone : polyRow (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ k))))) = none := by
        rw [polyRow_none_iff]
        omega
      rw [hnone] at h
      simp at h

/-- **⭐⭐⭐ 表里每一行的度数都**严格小于**上界。

**⇒ 对 `dmax` 归纳：后继步的表是「旧表 ++ 度数为 `n` 的那一行」，
两部分分别由**归纳假设**与 `polyRow_degree` 处理。** -/
theorem degreeList_degree_lt (dmax : ℕ) :
    ∀ row ∈ degreeList dmax, row.degree < dmax := by
  induction dmax with
  | zero =>
      intro row h
      rw [degreeList_zero] at h
      simp at h
  | succ n ih =>
      intro row h
      rw [show degreeList (n + 1) = degreeList n ++ (polyRow n).toList from rfl] at h
      rw [List.mem_append] at h
      rcases h with h | h
      · have := ih row h; omega
      · have hd := polyRow_degree n row h; omega

/-- **⭐⭐⭐ **被选中的行度数低于调用者给的上界**。

**⇒ 这就是 `dmax` 作为参数的**含义**：它不只过滤，而是给出一个可引用的承诺——
任何被选中的族都不超过调用者愿意承受的复杂度。** -/
theorem selectUpTo_degree_bound {req : Request} {dmax : ℕ} {row : CapabilityRow}
    (h : selectUpTo req dmax = some row) : row.degree < dmax := by
  classical
  unfold selectUpTo at h
  unfold select at h
  exact degreeList_degree_lt dmax row (List.mem_of_find?_eq_some h)

/-! ## 五、阶梯的**落点**：选择器不越级 -/

/-- **⭐⭐⭐ 二次目标在**真实的四级表**上落到二次行。**

**⇒ 注意这不是 `select_square_row` 的重述：那一条用的是**两元**表
`[affineRow a b, squareRow]`，而本条用的是**真实的四级生成表**
`[affineFamilyRow, squareRow, cubeRow]`。**
**⇒ 因此本条的新内容是：`find?` 在**二次行就停下了**，
**从未走到三次行**——即选择器不会为了一个二次目标去拿更贵的族。** -/
theorem select_quadratic_goal_lands_on_square (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2)
    (heps : 1 / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps) :
    selectUpTo req 4 = some squareRow := by
  classical
  unfold selectUpTo
  rw [degreeList_four]
  unfold select
  -- **第一次跳过：仿射族行不适用于 `x²`。**
  rw [List.find?_cons_of_neg]
  · -- **二次行被选中；三次行从未被考虑。**
    apply List.find?_cons_of_pos
    apply decide_eq_true
    constructor
    · show squareRow.covers req.goal
      rw [hgoal]
      rfl
    · show squareRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      show (1 : ℝ) / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
      exact heps
  · have hfalse : decide (sufficient affineFamilyRow req) = false :=
      decide_eq_false (affineFamily_not_sufficient_for_square req hgoal)
    simpa using hfalse

/-- **⭐⭐⭐ 三次目标落到三次行**（两级都被跳过）。

**⇒ 与上一条合起来，两个目标各自落在**自己的最小可行度数**上。
⇒ 这才是「按度数递增尝试」这句话的内容。** -/
theorem select_cubic_goal_lands_on_cube (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 3)
    (heps : 3 / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps) :
    selectUpTo req 4 = some cubeRow := by
  classical
  unfold selectUpTo
  rw [degreeList_four]
  unfold select
  rw [List.find?_cons_of_neg]
  · rw [List.find?_cons_of_neg]
    · apply List.find?_cons_of_pos
      apply decide_eq_true
      constructor
      · show cubeRow.covers req.goal
        rw [hgoal]
        rfl
      · show cubeRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
        show (3 : ℝ) / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
        exact heps
    · have hfalse : decide (sufficient squareRow req) = false :=
        decide_eq_false (cube_not_square_row req hgoal)
      simpa using hfalse
  · have hfalse : decide (sufficient affineFamilyRow req) = false :=
      decide_eq_false (affineFamily_not_sufficient_for_cube req hgoal)
    simpa using hfalse

/-! ## 六、四次目标：表拒绝，而表外可行（与之后的抬高） -/

/-- **⭐⭐ 表内（上界 4，即度数最高 3）没有一行覆盖 `t⁴`。** -/
theorem quartic_not_covered (req : Request) (hgoal : req.goal = fun t : ℝ => t ^ 4)
    (row : CapabilityRow) (hrow : row ∈ degreeList 4) : ¬ row.covers req.goal := by
  rw [degreeList_four] at hrow
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl
  · intro hcov
    obtain ⟨c, d, hcd⟩ := hcov
    have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => c * t + d := by
      rw [← hgoal]
      exact hcd
    exact quartic_not_affine ⟨c, d, hfun⟩
  · intro hcov
    have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => t ^ 2 := by
      rw [← hgoal]
      exact hcov
    exact quartic_ne_square hfun
  · intro hcov
    have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => t ^ 3 := by
      rw [← hgoal]
      exact hcov
    exact quartic_ne_cube hfun

/-- **⭐⭐⭐ 对四次目标，上界 4 的表选不出任何行。** -/
theorem selectUpTo_none_of_quartic_goal (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 4) : selectUpTo req 4 = none := by
  classical
  unfold selectUpTo
  unfold select
  rw [List.find?_eq_none]
  intro row hrow
  have hfalse : decide (sufficient row req) = false :=
    decide_eq_false (by
      intro hsuf
      exact quartic_not_covered req hgoal row hrow hsuf.1)
  simpa using hfalse

/-- **⭐ **上界 5 时的表**——现在包含四次行。** -/
theorem degreeList_five :
    degreeList 5 = [affineFamilyRow, squareRow, cubeRow, quarticRow] := by
  rw [show degreeList 5 = degreeList 4 ++ (polyRow 4).toList from rfl]
  rw [degreeList_four, polyRow_four]
  simp

/-- **⭐⭐⭐ **上限被抬高了一格**：四次目标在上界 5 下落到四次行。

**⇒ 与 `selectUpTo_none_of_quartic_goal`（上界 4）**并置**：同一目标，上界差一位，
结果从 `none` 变为 `some quarticRow`。⇒ 这就是「**表随能力增长**」的实证。** -/
theorem select_quartic_goal_lands_on_quartic (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 4)
    (heps : 3 / 2 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps) :
    selectUpTo req 5 = some quarticRow := by
  classical
  unfold selectUpTo
  rw [degreeList_five]
  unfold select
  rw [List.find?_cons_of_neg]
  · rw [List.find?_cons_of_neg]
    · rw [List.find?_cons_of_neg]
      · apply List.find?_cons_of_pos
        apply decide_eq_true
        constructor
        · show quarticRow.covers req.goal
          rw [hgoal]
          rfl
        · show quarticRow.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
          show (3 : ℝ) / 2 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps
          exact heps
      · have hf : decide (sufficient cubeRow req) = false :=
          decide_eq_false (by
            intro hsuf
            obtain ⟨hcov, _⟩ := hsuf
            have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => t ^ 3 := by
              rw [← hgoal]
              exact hcov
            exact quartic_ne_cube hfun)
        simpa using hf
    · have hf : decide (sufficient squareRow req) = false :=
        decide_eq_false (by
          intro hsuf
          obtain ⟨hcov, _⟩ := hsuf
          have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => t ^ 2 := by
            rw [← hgoal]
            exact hcov
          exact quartic_ne_square hfun)
      simpa using hf
  · have hf : decide (sufficient affineFamilyRow req) = false :=
      decide_eq_false (by
        intro hsuf
        obtain ⟨hcov, _⟩ := hsuf
        obtain ⟨c, d, hcd⟩ := hcov
        have hfun : (fun t : ℝ => t ^ 4) = fun t : ℝ => c * t + d := by
          rw [← hgoal]
          exact hcd
        exact quartic_not_affine ⟨c, d, hfun⟩)
    simpa using hf

/-- **⭐⭐⭐ **表不是上限**（对上界 4 而言）：表拒绝，而表外族达标。

**⇒ 两个合取项：`selectUpTo req 4 = none`；表外的 `interpFamily n (t↦t⁴)` 整域达到 `3/(2n²)`。**
**⇒ 与 `select_quartic_goal_lands_on_quartic`（上界 5）并置阅读：**同一目标，上界多一位，表就能接住它**。
⇒ 故本文件同时说两件事：**表不是上限**，且**上限可以被推高**。** -/
theorem table_is_not_a_ceiling (n : ℕ) (hn : 0 < n) :
    selectUpTo ⟨(fun t : ℝ => t ^ 4), 3 * (1 / (n : ℝ)) ^ 2 / 2, n, hn⟩ 4 = none
      ∧ (∀ x ∈ Set.Ico (0 : ℝ) 1,
          |x ^ 4 - gridEval (interpFamily n (fun t : ℝ => t ^ 4)) n x|
            ≤ 3 * (1 / (n : ℝ)) ^ 2 / 2) :=
  ⟨selectUpTo_none_of_quartic_goal _ rfl,
   fun x hx => quartic_uniform_bound_Icc n hn x ⟨hx.1, le_of_lt hx.2⟩⟩

end Lattice.Lib.Compiler.PolyTable