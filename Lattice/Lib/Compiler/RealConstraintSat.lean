import Mathlib
import Lattice.Lib.Compiler.RealCompilerOpt
/-!
# LATTICE: 多约束系统的可满足性

符号程序（约束列表，`RealCompilerOpt.Program`）的可满足性是编译正确性的
「存在侧」对偶：`RealTotalLoss` / `RealCompilerOpt.listLoss` 给出「给定输入处
损失是否为零」，本文件给出「是否存在输入使全部约束成立」，并把两者接起来。

  1. `satisfiable`：约束列表可满足 ⟺ 存在输入 `x` 使程序语义成立；
  2. `sat_iff_loss_zero`：可满足 ⟺ 存在输入使**总平方损失**为零
     （衔接 `TotalLoss` / `RealCompilerOpt.listLoss_compile_iff`）；
     `sat_iff_realTotalLoss_zero` 是 `Fin n` 索引、`RealTotalLoss` 的版本；
  3. `unsat_witness`：**不可满足证书** —— 若程序中存在一对「矛盾约束」
     （不存在同时满足二者的输入），则整个程序不可满足；
     `contradiction_of_same_coeff` 给出矛盾对的具体刻画（同一次系数、常数项
     不同、系数非零），`unsat_of_contradiction_pair` 与 `unsat_pair_concrete`
     是该判据的一般形式与具体实例；
  4. `finite_sat_decidable`：**有限有理数据下可满足性可判定** ——
     候选输入集为 `Fin n`、约束为 ℚ 系数时，「存在候选满足全部约束」有
     **可计算**的 `Decidable` 实例（纯 ℚ 算术，不含 `Classical`）；
     共享结构 `QConstraint` / `QSat` / `QSatisfiableOn`；
     `finite_sat_decidable_z` 是 ℤ 系数版，附一个由 `decide` **自动认证**的
     实例（ℚ 的内部要约化使 `decide` 归约卡住，故可执行认证放在 ℤ 版）；
  5. `sat_monotone`：约束子集可满足 ⟸ 全集可满足（子集更易满足）；
     `unsat_monotone` 是逆否形式（子集不可满足 ⟹ 超集不可满足）。

诚实假设与降级：
- **ℝ 上的可满足性不可计算判定**：`Real.decidableEq` 是 `noncomputable`，
  且 `DecidableEq ℝ` 只能由 `Classical` 提供（`RealConstraintSat` 是 ℝ 上的
  等式）。本文件因此把「可判定」的正面结果放在 **ℚ 有限候选集**上
  （`finite_sat_decidable`，纯可计算），ℝ 版只给出
  `realSatDecidableClassical`（显式 `Classical.propDecidable`，noncomputable）。
  Lean 中**无法**证明「ℝ 可满足性不可判定」（经典逻辑与之一致），故此处只做
  记号与可计算性层面的诚实标注，不主张不可判定性定理。
- `unsat_witness` 要求矛盾对的两个成员都是程序成员（证书只需这一对）；
  一般「找不到矛盾对」并不蕴含可满足（本文件不声称完备性）。
- 不使用 sorry / axiom / admit。
-/

namespace Lattice

/-! ## 一、约束系统的可满足性 -/

/-- 约束系统可满足：存在输入使程序中的**全部**约束成立。 -/
def satisfiable (cs : Program) : Prop := ∃ x : ℝ, ProgramSat cs x

/-- 空程序恒可满足。 -/
theorem satisfiable_empty : satisfiable ([] : Program) := by
  refine ⟨0, ?_⟩
  intro c hc
  simp at hc

/-- 单步展开：`c :: cs` 可满足 ⟺ 存在输入同时满足 `c` 与 `cs`。 -/
theorem satisfiable_cons_iff (c : RealConstraint) (cs : Program) :
    satisfiable (c :: cs) ↔ ∃ x : ℝ, RealConstraintSat c x ∧ ProgramSat cs x := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx c (by simp), fun d hd => hx d (by simp [hd])⟩
  · rintro ⟨x, hc, hx⟩
    refine ⟨x, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with hdc | hd'
    · rw [hdc]
      exact hc
    · exact hx d hd'

/-! ## 二、可满足 ⟺ 总损失可零化 -/

/-- **可满足 ⟺ 存在零损失输入**（列表版总平方损失；
衔接 `RealCompilerOpt.listLoss_compile_iff`）。 -/
theorem sat_iff_loss_zero (cs : Program) :
    satisfiable cs ↔ ∃ x : ℝ, listLoss (compileNeurons cs) x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (listLoss_compile_iff cs x).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (listLoss_compile_iff cs x).mp hx⟩

/-- **可满足 ⟺ 存在零损失输入**（`Fin n` 索引、`RealTotalLoss`；
衔接 `RealTotalLoss.realTotalLoss_soundness`）。 -/
theorem sat_iff_realTotalLoss_zero {n : ℕ} (cs : Fin n → RealConstraint) :
    (∃ x : ℝ, ∀ i : Fin n, RealConstraintSat (cs i) x) ↔
      ∃ x : ℝ, RealTotalLoss (compileFin cs) x = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (realTotalLoss_soundness cs x).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (realTotalLoss_soundness cs x).mp hx⟩

/-! ## 三、不可满足证书：矛盾约束对 -/

/-- **不可满足证书（矛盾对）**：若程序中存在一对约束，没有任何输入能同时
满足二者，则整个程序不可满足。这是不可满足性的**充分**证书。 -/
theorem unsat_witness (cs : Program) (c₁ c₂ : RealConstraint)
    (h₁ : c₁ ∈ cs) (h₂ : c₂ ∈ cs)
    (hd : ¬ ∃ x : ℝ, RealConstraintSat c₁ x ∧ RealConstraintSat c₂ x) :
    ¬ satisfiable cs := by
  rintro ⟨x, hx⟩
  exact hd ⟨x, hx c₁ h₁, hx c₂ h₂⟩

/-- **矛盾对的具体刻画**：两个约束一次系数相同、常数项不同时，
不存在同时满足二者的输入（两式相减即得 `b₁ = b₂`，与假设矛盾；
**无需**一次系数非零——`a = 0` 时退化为 `b₁ = 0 ∧ b₂ = 0`，同样矛盾）。 -/
theorem contradiction_of_same_coeff (a b₁ b₂ : ℝ) (hb : b₁ ≠ b₂) :
    ¬ ∃ x : ℝ, (a * x + b₁ = 0) ∧ (a * x + b₂ = 0) := by
  rintro ⟨x, h₁, h₂⟩
  exact hb (by linarith)

/-- **矛盾对判据（程序级）**：程序中同时含 `a*x+b₁ = 0` 与 `a*x+b₂ = 0`
（`b₁ ≠ b₂`）⟹ 程序不可满足。 -/
theorem unsat_of_contradiction_pair (cs : Program) (a b₁ b₂ : ℝ)
    (hb : b₁ ≠ b₂)
    (h₁ : ({ a := a, b := b₁ } : RealConstraint) ∈ cs)
    (h₂ : ({ a := a, b := b₂ } : RealConstraint) ∈ cs) :
    ¬ satisfiable cs := by
  refine unsat_witness cs _ _ h₁ h₂ ?_
  rintro ⟨x, hx₁, hx₂⟩
  exact contradiction_of_same_coeff a b₁ b₂ hb ⟨x, hx₁, hx₂⟩

/-- **具体不可满足实例**：`x + 1 = 0` 与 `x + 0 = 0` 矛盾，
故程序 `[x+1=0, x=0]` 不可满足。 -/
theorem unsat_pair_concrete :
    ¬ satisfiable [(⟨1, 1⟩ : RealConstraint), (⟨1, 0⟩ : RealConstraint)] := by
  refine unsat_witness [(⟨1, 1⟩ : RealConstraint), (⟨1, 0⟩ : RealConstraint)]
    ⟨1, 1⟩ ⟨1, 0⟩ (by simp) (by simp) ?_
  rintro ⟨x, h₁, h₂⟩
  unfold RealConstraintSat at h₁ h₂
  simp at h₁ h₂
  linarith

/-! ## 四、有限有理数据下的可判定性 -/

/-- ℚ 系数线性约束（ℝ 版 `RealConstraint` 的可计算类比）。 -/
structure QConstraint where
  a : ℚ
  b : ℚ
deriving DecidableEq, Repr

/-- ℚ 约束的满足语义。 -/
def QSat (c : QConstraint) (x : ℚ) : Prop := c.a * x + c.b = 0

/-- `QSat` 的定义展开（`Iff.rfl`：两侧定义相等）。 -/
theorem qSat_unfold (c : QConstraint) (x : ℚ) : QSat c x ↔ c.a * x + c.b = 0 :=
  Iff.rfl

/-- ℚ 约束程序。 -/
abbrev QProgram := List QConstraint

/-- 有限候选输入（`Fin n` 索引）上的可满足性：某个候选满足全部 ℚ 约束。
（用**显式算术表达式**书写，使 `Decidable` 的类型类搜索无需展开 `QSat`；
与 `∃ i, ∀ c ∈ cs, QSat c (xs i)` 定义相等，见 `qSatisfiableOn_iff`。） -/
def QSatisfiableOn (n : ℕ) (cs : QProgram) (xs : Fin n → ℚ) : Prop :=
  ∃ i : Fin n, ∀ c ∈ cs, c.a * (xs i) + c.b = 0

/-- `QSatisfiableOn` 的 `QSat` 表述（定义相等）。 -/
theorem qSatisfiableOn_iff (n : ℕ) (cs : QProgram) (xs : Fin n → ℚ) :
    QSatisfiableOn n cs xs ↔ ∃ i : Fin n, ∀ c ∈ cs, QSat c (xs i) :=
  Iff.rfl

/-- ℚ 版 Bool 判定器：逐个候选检查是否满足全部约束（`List.all`）。 -/
def qSatAllB (cs : QProgram) (v : ℚ) : Bool :=
  cs.all (fun c => decide (c.a * v + c.b = 0))

/-- `qSatAllB` 的正确性：`= true ⟺ 全部约束满足`。 -/
theorem qSatAllB_iff (cs : QProgram) (v : ℚ) :
    qSatAllB cs v = true ↔ ∀ c ∈ cs, QSat c v := by
  unfold qSatAllB QSat
  rw [List.all_eq_true]
  exact ⟨fun h c hc => of_decide_eq_true (h c hc),
    fun h c hc => decide_eq_true (h c hc)⟩

/-- **ℚ 有限数据可满足性可判定（可计算）**：
候选集 `Fin n` 有限、约束系数为 ℚ 时，「存在候选满足全部约束」有
**可计算**的 `Decidable` 实例（由 `Fintype.decidableExistsFintype` 与
`List.decidableBAll` 给出，不使用 `Classical`）。 -/
instance instDecidableQSatisfiableOn (n : ℕ) (cs : QProgram) (xs : Fin n → ℚ) :
    Decidable (QSatisfiableOn n cs xs) := by
  unfold QSatisfiableOn
  infer_instance

/-- 命名入口（与实例等价）。 -/
def finite_sat_decidable (n : ℕ) (cs : QProgram) (xs : Fin n → ℚ) :
    Decidable (QSatisfiableOn n cs xs) :=
  instDecidableQSatisfiableOn n cs xs

/-! ### ℤ 版：可被 `decide` 执行认证的判定

ℚ 的 `DecidableEq` 虽然存在，但其内部要约化（`Rat.normalize` 的 gcd 计算）
使 `decide` 的 `whnf` 归约无法走到 `isTrue`/`isFalse`；而 ℤ 算术与相等判定
是完全可归约的。故把「可执行判定」的 `decide` 认证放在 ℤ 版
（两者都是「有限有理数据」的可计算判定）。 -/

/-- ℤ 系数线性约束。 -/
structure ZConstraint where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

/-- ℤ 约束程序。 -/
abbrev ZProgram := List ZConstraint

/-- 有限候选输入（`Fin n` 索引）上的 ℤ 可满足性（显式算术形式）。 -/
def ZSatisfiableOn (n : ℕ) (cs : ZProgram) (xs : Fin n → ℤ) : Prop :=
  ∃ i : Fin n, ∀ c ∈ cs, c.a * (xs i) + c.b = 0

/-- **ℤ 有限数据可满足性可判定（可执行）**。 -/
instance instDecidableZSatisfiableOn (n : ℕ) (cs : ZProgram) (xs : Fin n → ℤ) :
    Decidable (ZSatisfiableOn n cs xs) := by
  unfold ZSatisfiableOn
  infer_instance

/-- 命名入口（与实例等价）。 -/
def finite_sat_decidable_z (n : ℕ) (cs : ZProgram) (xs : Fin n → ℤ) :
    Decidable (ZSatisfiableOn n cs xs) :=
  instDecidableZSatisfiableOn n cs xs

/-- `decide` 认证：候选 `i = 0 ↦ 1`、`i = 1 ↦ 2` 中，`x = 1` 满足约束
`x - 1 = 0`（一条候选命中），由 `decide` 自动认证。 -/
example : ZSatisfiableOn 2 [(⟨1, -1⟩ : ZConstraint)]
    (fun i => if i = (0 : Fin 2) then (1 : ℤ) else 2) := by
  decide

/-- **ℝ 版判定只能 noncomputable**：`RealConstraintSat` 含 ℝ 上等式，
其判定由 `Classical.propDecidable` 提供（`noncomputable`）——
这正是 ℚ 版本存在的理由。（经典逻辑下无法在 Lean 内证明 ℝ 版不可判定，
故此处只做可计算性标注，不声称不可判定性。） -/
noncomputable def realSatDecidableClassical {n : ℕ} (cs : List RealConstraint)
    (xs : Fin n → ℝ) :
    Decidable (∃ i : Fin n, ∀ c ∈ cs, RealConstraintSat c (xs i)) :=
  Classical.propDecidable _

/-! ## 五、可满足性的单调性 -/

/-- **子集可满足 ⟸ 全集可满足**：约束越少越容易满足。 -/
theorem sat_monotone {cs cs' : Program} (hsub : cs ⊆ cs') (h : satisfiable cs') :
    satisfiable cs := by
  rcases h with ⟨x, hx⟩
  exact ⟨x, fun c hc => hx c (hsub hc)⟩

/-- **逆否形式**：子集不可满足 ⟹ 超集不可满足。 -/
theorem unsat_monotone {cs cs' : Program} (hsub : cs ⊆ cs') (h : ¬ satisfiable cs) :
    ¬ satisfiable cs' :=
  fun h' => h (sat_monotone hsub h')

end Lattice
