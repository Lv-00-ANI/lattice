import Mathlib
import Lattice.Runtime.RealLinear
import Lattice.Lift.RealTotalLoss
/-!
# LATTICE: 编译器优化的保语义性 —— 常量折叠 / 死约束消除 / 公共子表达式消除

符号→权重编译链（`ConvertLinear` / `ConvertVectorLinear` / `RealLinear` /
`TotalLoss` / `RealTotalLoss`）证明「转换保语义」与「零损失 ⟺ 全部约束满足」。
真实编译器在编译后还会对**约束程序**做优化；本文件证明三个标准优化各自保语义，
并证明它们的组合序列保语义、且优化前后**损失零化集合相同**：

  1. `const_fold_preserves`（核心）：常量折叠——把常数子表达式 `k₁*(k₂*x)`
     在编译期求值为 `(k₁*k₂)*x`，语义不变（`mul_assoc`）；
     `const_fold_const_independent`：折叠后若系数为 0，则约束与输入无关
     （可静态判定）；
  2. `dead_constraint_elim_preserves`（核心）：死约束消除——删除恒真约束
     （`0*x + 0 = 0`）不改变解集；
  3. `cse_preserves`（核心）：公共子表达式消除/去重——重复约束出现两次
     ⟺ 出现一次（`List.dedup`），解集不变；
  4. `opt_preserves_semantics`（组合）：优化序列（折叠 → 消除 → 去重）
     保语义（逐条 iff 复合）；
  5. `opt_loss_invariant`（加分）：优化前后总平方损失零化集合相同
     （衔接 `RealTotalLoss`：零损失 ⟺ 全部约束满足）。

**诚实假设**：约束是既有 `RealLinear.RealConstraint`（线性：`a*x + b = 0`）——
本文件只讨论**线性等式**（既有结构）；所有优化只做「语义保持」的重写，
不涉及数值近似。`Program` 是约束列表（顺序无关的合取语义 `ProgramSat`）。
不使用 sorry / axiom / admit。
-/

noncomputable section

open Classical

namespace Lattice

open scoped BigOperators

/-! ## 符号程序与语义（约束列表的合取） -/

/-- 符号程序：约束列表（顺序即编译顺序；语义是合取，故与顺序无关）。 -/
abbrev Program := List RealConstraint

/-- 程序语义：`x` 满足程序中的**全部**约束。 -/
def ProgramSat (p : Program) (x : ℝ) : Prop := ∀ c ∈ p, RealConstraintSat c x

/-! ## 优化一：常量折叠 -/

/-- 待折叠的线性表达式：未折叠形式为 `k₁ * (k₂ * x) + b = 0`
（`k₁ * k₂` 是编译期可求值的常数子表达式）。 -/
structure ConstExpr where
  k1 : ℝ
  k2 : ℝ
  b : ℝ

/-- 折叠前语义：`k₁ * (k₂ * x) + b = 0`。 -/
def ConstExprSat (e : ConstExpr) (x : ℝ) : Prop := e.k1 * (e.k2 * x) + e.b = 0

/-- 常量折叠：编译期把常数子表达式 `k₁ * k₂` 求值为单一系数。 -/
def foldExpr (e : ConstExpr) : RealConstraint := { a := e.k1 * e.k2, b := e.b }

/-- **常量折叠保语义**：`(k₁*k₂)*x + b = 0 ⟺ k₁*(k₂*x) + b = 0`（结合律）。 -/
theorem const_fold_preserves (e : ConstExpr) (x : ℝ) :
    RealConstraintSat (foldExpr e) x ↔ ConstExprSat e x := by
  unfold RealConstraintSat ConstExprSat foldExpr
  rw [mul_assoc]

/-- 常量折叠的解集表述。 -/
theorem const_fold_preserves_solution_set (e : ConstExpr) :
    {x : ℝ | RealConstraintSat (foldExpr e) x} = {x : ℝ | ConstExprSat e x} := by
  ext x
  exact const_fold_preserves e x

/-- 折叠后系数为零 ⟹ 约束真值与输入无关（可静态判定——这正是常量折叠的价值）。 -/
theorem const_fold_const_independent (e : ConstExpr) (h : e.k1 * e.k2 = 0) (x y : ℝ) :
    RealConstraintSat (foldExpr e) x ↔ RealConstraintSat (foldExpr e) y := by
  unfold RealConstraintSat foldExpr at *
  rw [h]
  simp

/-! ## 优化二：死约束消除 -/

/-- 恒真约束：`a = 0 ∧ b = 0`（即 `0*x + 0 = 0`）。 -/
def isTrivial (c : RealConstraint) : Prop := c.a = 0 ∧ c.b = 0

/-- 恒真约束在任何输入处都满足。 -/
theorem trivial_sat (c : RealConstraint) (x : ℝ) (h : isTrivial c) :
    RealConstraintSat c x := by
  obtain ⟨ha, hb⟩ := h
  unfold RealConstraintSat
  rw [ha, hb]
  ring

/-- 保留谓词（`Bool` 版本，供 `List.filter` 使用）。 -/
def keepB (c : RealConstraint) : Bool := decide (¬ isTrivial c)

/-- 死约束消除：删去全部恒真约束（如 `0 = 0`）。 -/
def deadElim (p : Program) : Program := p.filter keepB

theorem mem_deadElim {p : Program} {c : RealConstraint} :
    c ∈ deadElim p ↔ c ∈ p ∧ ¬ isTrivial c := by
  unfold deadElim keepB
  rw [List.mem_filter]
  constructor
  · rintro ⟨hmem, hb⟩
    exact ⟨hmem, of_decide_eq_true hb⟩
  · rintro ⟨hmem, hnt⟩
    exact ⟨hmem, decide_eq_true hnt⟩

/-- **死约束消除保语义**：删除恒真约束不改变解集
（被删的都是恒真，保留的都在原程序中）。 -/
theorem dead_constraint_elim_preserves (p : Program) (x : ℝ) :
    ProgramSat (deadElim p) x ↔ ProgramSat p x := by
  constructor
  · intro h c hc
    by_cases htr : isTrivial c
    · exact trivial_sat c x htr
    · exact h c (mem_deadElim.mpr ⟨hc, htr⟩)
  · intro h c hc
    exact h c (mem_deadElim.mp hc).1

/-! ## 优化三：公共子表达式消除（重复约束去重） -/

/-- 公共子表达式消除（重复约束去重）：同一约束出现多次只保留一次。 -/
def cse (p : Program) : Program := p.dedup

theorem mem_cse {p : Program} {c : RealConstraint} : c ∈ cse p ↔ c ∈ p := by
  unfold cse
  exact List.mem_dedup

/-- **去重保语义**：`cse` 只改变重数，不改变成员集合。 -/
theorem cse_preserves (p : Program) (x : ℝ) :
    ProgramSat (cse p) x ↔ ProgramSat p x := by
  constructor
  · intro h c hc
    exact h c (mem_cse.mpr hc)
  · intro h c hc
    exact h c (mem_cse.mp hc)

/-- 去重的语义实质：同一约束出现两次 ⟺ 出现一次（重复约束消除）。 -/
theorem cse_duplicate_preserves (c : RealConstraint) (rest : Program) (x : ℝ) :
    ProgramSat (c :: c :: rest) x ↔ ProgramSat (c :: rest) x := by
  unfold ProgramSat
  constructor
  · intro h d hd
    rcases List.mem_cons.mp hd with hdc | hd'
    · rw [hdc]
      exact h c (by simp)
    · exact h d (by simp [hd'])
  · intro h d hd
    rcases List.mem_cons.mp hd with hdc | hd'
    · rw [hdc]
      exact h c (by simp)
    · exact h d (by simp [hd'])

/-! ## 折叠到程序级 -/

/-- 常量折叠（程序级）：把 `ConstExpr` 程序编译为 `RealConstraint` 程序。 -/
def foldProgram (p : List ConstExpr) : Program := p.map foldExpr

/-- `ConstExpr` 程序的语义。 -/
def ConstProgramSat (p : List ConstExpr) (x : ℝ) : Prop := ∀ e ∈ p, ConstExprSat e x

/-- 程序级常量折叠保语义。 -/
theorem foldProgram_preserves (p : List ConstExpr) (x : ℝ) :
    ProgramSat (foldProgram p) x ↔ ConstProgramSat p x := by
  unfold ProgramSat ConstProgramSat foldProgram
  constructor
  · intro h e he
    exact (const_fold_preserves e x).mp (h (foldExpr e) (List.mem_map.mpr ⟨e, he, rfl⟩))
  · intro h c hc
    rcases List.mem_map.mp hc with ⟨e, he, rfl⟩
    exact (const_fold_preserves e x).mpr (h e he)

/-! ## 组合：优化序列保语义 -/

/-- 优化序列：常量折叠 → 死约束消除 → 公共子表达式消除。 -/
def optimize (p : List ConstExpr) : Program := cse (deadElim (foldProgram p))

/-- 组合优化的程序级保语义（每一步都保语义，逐条 iff 复合）。 -/
theorem opt_preserves_program_sat (p : List ConstExpr) (x : ℝ) :
    ProgramSat (optimize p) x ↔ ProgramSat (foldProgram p) x := by
  unfold optimize
  exact (cse_preserves (deadElim (foldProgram p)) x).trans
    (dead_constraint_elim_preserves (foldProgram p) x)

/-- **优化序列保语义**：折叠 → 消除 → 去重之后，解集与优化前完全相同。 -/
theorem opt_preserves_semantics (p : List ConstExpr) (x : ℝ) :
    ProgramSat (optimize p) x ↔ ConstProgramSat p x :=
  (opt_preserves_program_sat p x).trans (foldProgram_preserves p x)

/-- 优化序列保解集的集合论表述。 -/
theorem opt_preserves_solution_set (p : List ConstExpr) :
    {x : ℝ | ProgramSat (optimize p) x} = {x : ℝ | ConstProgramSat p x} := by
  ext x
  exact opt_preserves_semantics p x

/-! ## 优化与损失零化（衔接 RealTotalLoss） -/

/-- 程序编译为神经元列表。 -/
def compileNeurons (p : Program) : List RealNeuron := p.map convertReal

/-- 列表版总平方损失（与 `RealTotalLoss` 同构，但长度可变——优化会改变约束条数）。 -/
def listLoss (ls : List RealNeuron) (x : ℝ) : ℝ :=
  (ls.map (fun n => (RealNeuronOut n x) ^ 2)).sum

/-- 平方和非负。 -/
theorem list_sq_sum_nonneg (ls : List RealNeuron) (x : ℝ) :
    0 ≤ (ls.map (fun n => (RealNeuronOut n x) ^ 2)).sum := by
  induction ls with
  | nil => simp
  | cons h t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (sq_nonneg _) ih

/-- **损失零化 ⟺ 每个神经元输出为零**（`RealTotalLoss` 的列表版）。 -/
theorem listLoss_zero_iff (ls : List RealNeuron) (x : ℝ) :
    listLoss ls x = 0 ↔ ∀ n ∈ ls, RealNeuronOut n x = 0 := by
  unfold listLoss
  induction ls with
  | nil => simp
  | cons h t ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (list_sq_sum_nonneg t x)]
      constructor
      · rintro ⟨hh, ht⟩ n hn
        rcases List.mem_cons.mp hn with rfl | hn'
        · exact sq_eq_zero_iff.mp hh
        · exact (ih.mp ht) n hn'
      · intro hall
        exact ⟨sq_eq_zero_iff.mpr (hall h (by simp)),
          ih.mpr (fun n hn => hall n (by simp [hn]))⟩

/-- **损失零化 ⟺ 程序满足**（编译保语义 `convertReal_preserves` 的列表版）。 -/
theorem listLoss_compile_iff (p : Program) (x : ℝ) :
    listLoss (compileNeurons p) x = 0 ↔ ProgramSat p x := by
  rw [listLoss_zero_iff]
  unfold compileNeurons ProgramSat
  constructor
  · intro h c hc
    exact (convertReal_preserves c x).mp (h (convertReal c) (List.mem_map.mpr ⟨c, hc, rfl⟩))
  · intro h n hn
    rcases List.mem_map.mp hn with ⟨c, hc, rfl⟩
    exact (convertReal_preserves c x).mpr (h c hc)

/-- **优化保持损失零化集合**：优化前后「总平方损失 = 0」的输入集合相同
（衔接 `RealTotalLoss` 的「零损失 ⟺ 全部约束满足」）。 -/
theorem opt_loss_invariant (p : List ConstExpr) (x : ℝ) :
    listLoss (compileNeurons (optimize p)) x = 0 ↔
      listLoss (compileNeurons (foldProgram p)) x = 0 := by
  rw [listLoss_compile_iff, listLoss_compile_iff]
  exact opt_preserves_program_sat p x

/-- 与 `RealTotalLoss` 的直接衔接：对 `Fin n` 索引的 `ConstExpr` 程序，
常量折叠后的 `RealTotalLoss` 零化 ⟺ 全部未折叠约束满足。 -/
theorem opt_preserves_realTotalLoss {n : Nat} (cs : Fin n → ConstExpr) (x : ℝ) :
    RealTotalLoss (compileFin (fun i => foldExpr (cs i))) x = 0 ↔
      ∀ i : Fin n, ConstExprSat (cs i) x := by
  rw [realTotalLoss_soundness]
  constructor
  · intro h i
    exact (const_fold_preserves (cs i) x).mp (h i)
  · intro h i
    exact (const_fold_preserves (cs i) x).mpr (h i)

end Lattice
