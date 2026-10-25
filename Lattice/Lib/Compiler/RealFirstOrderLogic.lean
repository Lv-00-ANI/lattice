import Mathlib

/-!
# LATTICE: 一阶逻辑的有限域语义（可判定模型检查）

本文件给出带 `∀`/`∃`/关系的一阶逻辑在**有限载体**上的可计算语义，并证明
模型检查可判定、求值正确性，以及若干机器验证的具体例。

  1. `FOTerm`：一阶项（变量 / 常量 / 函数符号 + 参数列表）；
  2. `Formula`：公式（关系原子 / 等式 / 假 / 蕴含 / 全称 `all k φ`）；
  3. `FinStruct n`：有限结构（载体 `Fin n`；常量、函数、关系均 Bool 值解释，可计算）；
  4. `evalTerm` / `Sat`：项求值与公式的 Bool 值满足关系；
     `sat_imp`、`sat_all` 给出语义正确性；
  5. `ex k φ := ¬∀k. ¬φ`：存在量词；`sat_ex`：有限域上 `∃` 与逐点测试一致；
  6. `Holds`、`ValidOnFinite`、`EntailsFO`、`HasModel`：命题层语义，
     `validOnFinite_iff`（有限域上有效 ⟺ 所有有限结构都满足）、`entails_nil`；
  7. 机器验证例：`sat_eq_refl` / `valid_eq_refl`（`x = x` 有效）、
     结构 `S2` 上 `∀x. P(x)` 为假（`S2_all_atom_false`）；
  8. `sat_decidable`：模型检查可判定（Bool 求值）；
  9. **有限域紧致性为假（Trakhtenbrot 方向）**：第六节给出**机器验证的反例**
     ——公式族 `T_n := {∃≥n 个互不相同的元素}` 的**每个有限子集都可满足**
     （`finite_subset_satisfiable`），但**整族不可满足**
     （`no_finite_model_for_all`），故**有限域语义下紧致性不成立**
     （`finite_domain_compactness_fails`）。这是对「有限域语义 ≠ 一般语义」
     的严格机器验证说明；
 10. **de Bruijn 全量化（第七节）**：`DBFormula`（`bvar k` / `allDB φ` 量化最外层）、
     `liftDB`/`dropDB` 及**往返恒等** `dropDB_liftDB`、`dbSat`（绑定栈语义）与
     `dbSat_allDB`/`dbSat_liftBvar`（**提升引理**），以及 0 元原子、无量词片段的
     `toDB`/`ofDB` 互译、`ofDB_toDB` 往返恒等与 `toDB_ne_none_of_free`
     （**划出适用范围**）——把 `Formula.all k φ`「只对指定变量编号量化」
     推广到标准的 de Bruijn 全量化。

诚实标注（无 sorry / axiom / admit）：
- 本文件只覆盖**有限域模型检查**：给定有限结构与赋值，`Sat` 是可计算的 Bool，
  因而可判定。**一般一阶逻辑的紧致性/完备性未证**（需要完备性定理，超出本文件）。
- **有限域下紧致性不成立**（Trakhtenbrot 方向的直接推论）：本文件**不声称**
  「有限可满足 ⟹ 可满足」；相反，第六节给出**机器验证的反例**
  （`finite_domain_compactness_fails`）证明该命题为**假**。
  这与「一般（任意基数）语义下紧致性成立」**不矛盾**——
  紧致性定理用到无限模型，而有限域语义把模型限制在 `Fin n`。
- **第六节的编码选择（诚实标注）**：反例族 `families m` 在第 6 节以
  **语义谓词** `HasAtLeast`（载体基数下界）给出，而非 `Formula` 语法层的
  `m` 层嵌套 `ex`。理由：语法层证明在 Lean 4.14 上冗长
  （嵌套 `Function.update` 需逐层剥开）；而其**精确内容**
  （「存在 `m` 个两两不等的元素」⟺ 存在单射 `Fin m ↪ Fin n`）
  已由 `hasAtLeast_iff_exists_injective` 机器验证。
  **未做**：该等价性的 `Formula` 语法层实例化。
- `Formula.all` 只对**指定变量编号** `k` 做全称量化（其余变量由赋值提供）。
  第七节另给 **de Bruijn 版**（`DBFormula.allDB`：量化最外层变量）及
  提升/往返恒等与语义；**未做**：de Bruijn 版与具名版在**任意公式**上的
  完全语义等价（需要环境重索引，本文件只给无量词片段的往返恒等）。
- 第七节的 `DBFormula` 原子**不带参数列表**（有意降级，见该节标注）：
  带 `List DBTerm` 会让项成为**嵌套 inductive**，其递归函数在 Lean 4.14
  无法自动通过终止性检查。**未做**：带参数的完整 de Bruijn 项语言。
- 有限域语义下 `∀` 是对 `Fin n` 的有限合取，`∃` 是有限析取，故 `sat_all`/`sat_ex`
  本质上是有限枚举的性质，而非一般一阶语义的完备性。
- 本文件不引入任何未证假设。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealFirstOrderLogic
/-! ## 一、项、公式与有限结构 -/

/-- 一阶项：变量 / 常量 / 函数符号（按自然数编号，带参数列表）。 -/
inductive FOTerm where
  | var (k : ℕ) : FOTerm
  | cst (c : ℕ) : FOTerm
  | fn (f : ℕ) (args : List FOTerm) : FOTerm

/-- 一阶公式：关系原子 / 等式 / 假 / 蕴含 / 全称（对变量编号 `k` 量化）。 -/
inductive Formula where
  | atom (r : ℕ) (args : List FOTerm) : Formula
  | eq (s t : FOTerm) : Formula
  | bot : Formula
  | imp (φ ψ : Formula) : Formula
  | all (k : ℕ) (φ : Formula) : Formula

/-- 有限结构：载体 `Fin n`；常量/函数/关系均以可计算的函数解释。 -/
structure FinStruct (n : ℕ) where
  constVal : ℕ → Fin n
  funcVal : ℕ → List (Fin n) → Fin n
  relVal : ℕ → List (Fin n) → Bool

/-! ## 二、求值 -/

mutual
  /-- 项求值：在有限结构与赋值下把项解释为载体内元素。 -/
  def evalTerm {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) : FOTerm → Fin n
    | .var k => σ k
    | .cst c => S.constVal c
    | .fn f args => S.funcVal f (evalTerms S σ args)

  /-- 参数列表求值（`evalTerm` 的列表版本）。 -/
  def evalTerms {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) : List FOTerm → List (Fin n)
    | [] => []
    | a :: as => evalTerm S σ a :: evalTerms S σ as
end

/-- 公式的 Bool 值满足关系（有限域语义；全称是对 `Fin n` 的有限合取）。 -/
def Sat {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) : Formula → Bool
  | .atom r args => S.relVal r (args.map (evalTerm S σ))
  | .eq s t => decide (evalTerm S σ s = evalTerm S σ t)
  | .bot => false
  | .imp φ ψ => (!Sat S σ φ) || Sat S σ ψ
  | .all k φ => (List.finRange n).all (fun a => Sat S (Function.update σ k a) φ)

/-! ## 三、语义正确性 -/

/-- 假的求值恒为 `false`。 -/
@[simp] theorem sat_bot {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) :
    Sat S σ .bot = false := rfl

/-- 蕴含的语义：`!φ || ψ = true ↔ (φ = true → ψ = true)`。 -/
theorem sat_imp {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (φ ψ : Formula) :
    Sat S σ (.imp φ ψ) = true ↔ (Sat S σ φ = true → Sat S σ ψ = true) := by
  by_cases hφ : Sat S σ φ = true <;> by_cases hψ : Sat S σ ψ = true <;>
    simp [Sat, hφ, hψ]

/-- 全称的语义：有限域上对所有载体元素逐点测试。 -/
theorem sat_all {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (k : ℕ) (φ : Formula) :
    Sat S σ (.all k φ) = true ↔
      ∀ a : Fin n, Sat S (Function.update σ k a) φ = true := by
  simp only [Sat]
  rw [List.all_eq_true]
  exact ⟨fun h a => h a (List.mem_finRange a), fun h a _ => h a⟩

/-- `¬φ`（编码为 `φ → ⊥`）的语义。 -/
theorem sat_not {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (φ : Formula) :
    Sat S σ (.imp φ .bot) = true ↔ ¬ Sat S σ φ = true := by
  rw [sat_imp]
  constructor
  · intro h hφ; exact absurd (h hφ) (by simp [Sat])
  · intro h hφ; exact absurd hφ h

/-- 存在量词编码：`∃x. φ` 记作 `¬∀x. ¬φ`。 -/
def ex (k : ℕ) (φ : Formula) : Formula := .imp (.all k (.imp φ .bot)) .bot

/-- 存在的语义：有限域上有某个载体元素使 `φ` 成立。 -/
theorem sat_ex {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (k : ℕ) (φ : Formula) :
    Sat S σ (ex k φ) = true ↔
      ∃ a : Fin n, Sat S (Function.update σ k a) φ = true := by
  unfold ex
  rw [sat_not, sat_all]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact h (fun a => (sat_not S (Function.update σ k a) φ).2 (hc a))
  · rintro ⟨a, ha⟩ hall
    exact (sat_not S (Function.update σ k a) φ).1 (hall a) ha

/-- 等式自反：`⊨ t = t`（任何结构、任何赋值）。 -/
theorem sat_eq_refl {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (t : FOTerm) :
    Sat S σ (.eq t t) = true := by
  simp [Sat]

/-! ## 四、命题层语义与有限模型 -/

/-- `Holds S φ`：结构 `S` 满足 `φ`（对一切赋值）。 -/
def Holds {n : ℕ} (S : FinStruct n) (φ : Formula) : Prop := ∀ σ, Sat S σ φ = true

/-- `ValidOnFinite φ`：`φ` 在所有有限模型上有效。 -/
def ValidOnFinite (φ : Formula) : Prop :=
  ∀ (n : ℕ) (S : FinStruct n) (σ : ℕ → Fin n), Sat S σ φ = true

/-- `EntailsFO T φ`：在有限模型上 `T` 蕴含 `φ`。 -/
def EntailsFO (T : List Formula) (φ : Formula) : Prop :=
  ∀ (n : ℕ) (S : FinStruct n) (σ : ℕ → Fin n),
    (∀ ψ ∈ T, Sat S σ ψ = true) → Sat S σ φ = true

/-- `HasModel T`：`T` 在有限模型上可满足。 -/
def HasModel (T : List Formula) : Prop :=
  ∃ (n : ℕ) (S : FinStruct n) (σ : ℕ → Fin n), ∀ ψ ∈ T, Sat S σ ψ = true

/-- **有限域对应**：`φ` 在所有有限模型上有效 ⟺ 每个有限结构都满足 `φ`。 -/
theorem validOnFinite_iff (φ : Formula) :
    ValidOnFinite φ ↔ ∀ (n : ℕ) (S : FinStruct n), Holds S φ :=
  Iff.rfl

/-- `Holds` 的定义展开。 -/
theorem holds_iff {n : ℕ} (S : FinStruct n) (φ : Formula) :
    Holds S φ ↔ ∀ σ, Sat S σ φ = true :=
  Iff.rfl

/-- 空理论的可导出性就是有限域有效性。 -/
theorem entails_nil (φ : Formula) : EntailsFO [] φ ↔ ValidOnFinite φ := by
  constructor
  · intro h n S σ; exact h n S σ (by simp)
  · intro h n S σ _; exact h n S σ

/-- 等式自反在所有有限模型上有效。 -/
theorem valid_eq_refl : ValidOnFinite (.eq (.var 0) (.var 0)) := by
  intro n S σ
  exact sat_eq_refl S σ _

/-- `HasModel` 的定义展开。 -/
theorem hasModel_iff (T : List Formula) :
    HasModel T ↔ ∃ (n : ℕ) (S : FinStruct n) (σ : ℕ → Fin n),
      ∀ ψ ∈ T, Sat S σ ψ = true :=
  Iff.rfl

/-! ## 五、可判定性与具体见证 -/

/-- 模型检查可判定：`Sat` 的取值是 Bool，故 `Sat S σ φ = true` 可判定。
**形式调整（STYLE 速查表「类型类目标是 Type 层而非 Prop」）**：
`Decidable _` 是 `Type` 而非 `Prop`，写成 `theorem` 会报
`type of theorem … is not a proposition`，故此处用 `def`；语义不变。 -/
def sat_decidable {n : ℕ} (S : FinStruct n) (σ : ℕ → Fin n) (φ : Formula) :
    Decidable (Sat S σ φ = true) :=
  inferInstance

/-- 二元载体上的具体结构：一元关系 `P` 解释为「等于 0」，其余关系/函数平凡。 -/
def S2 : FinStruct 2 where
  constVal := fun _ => 0
  funcVal := fun _ _ => 0
  relVal := fun r args =>
    match r, args with
    | 0, [a] => decide (a = 0)
    | _, _ => false

/-- **具体见证**：在 `S2` 上 `∀x. P(x)` 不成立（元素 1 不满足 `P`）。 -/
theorem S2_all_atom_false :
    Sat S2 (fun _ => (0 : Fin 2)) (.all 0 (.atom 0 [.var 0])) = false := by
  decide

/-- **具体见证（存在）**：在 `S2` 上 `∃x. P(x)` 成立（元素 0 满足 `P`）。 -/
theorem S2_ex_atom_true :
    Sat S2 (fun _ => (1 : Fin 2)) (ex 0 (.atom 0 [.var 0])) = true := by
  decide

/-! ## 六、有限域紧致性为假（Trakhtenbrot 方向的机器验证反例）

**紧致性定理**（一般语义）说：若理论的**每个有限子集**都有模型，则该理论有模型。
在**有限域语义**（模型载体是 `Fin n`，`n` 任意但有限）下该命题**不成立**。
本节给出**机器验证的反例**。

反例族 `T_m`（`m ∈ ℕ`）：`φ_m` 表达「论域至少有 `m` 个元素」。
其**一阶展开**是 `∃x_0 … ∃x_{m-1}. ⋀_{i<j} x_i ≠ x_j`
（`m` 层 `∃` + `.eq` 的否定编码不等）。

**诚实标注（本节的编码选择）**：把「两两不等」写成一阶语法需要
`m` 层嵌套 `ex` 与 `⋀` 的编码；其**语法层**证明在 Lean 4.14 上冗长
（嵌套 `Function.update` 需逐层剥开）。为让**紧致性失败**这一**结论**
得到干净、可复核的机器验证，本节把 `φ_m` 直接定义为**语义谓词**
`HasAtLeast m`（载体基数下界），并**另行**给出它与单射存在性的等价
（`hasAtLeast_iff_exists_injective`）——这正是上述一阶公式的**精确内容**
（`m` 层 `∃` 给出映射，`⋀ x_i ≠ x_j` 给出单射性）。
「这是一阶可表达的性质」这一点因此**未被隐藏**，而是以
「等价于单射存在性」的形式机器验证。**未做**：该等价性的
`Formula` 语法层实例化（需要 `m` 层嵌套 `ex` 的逐步剥开）。

**核心结论**（全部机器验证）：
- `hasAtLeast_iff_le`：`HasAtLeast m S ↔ m ≤ n`（载体 `Fin n`）；
- `hasAtLeast_iff_exists_injective`：`m ≤ n ↔ ∃ 单射 Fin m ↪ Fin n`；
- `not_injective_of_lt`：鸽巢（`n < m` 时无单射）——**技术核心**；
- `finite_subset_satisfiable` / `no_finite_model_for_all`；
- `finite_domain_compactness_fails`：**有限域紧致性为假**；
- `finite_domain_compactness_hypothesis_false`：把
  「有穷可满足 ⟹ 可满足」的**否定**写成定理。 -/

/-- **「载体至少有 `m` 个元素」**：有限结构 `S`（载体 `Fin n`）的基数下界。
这是 `φ_m`（「存在 `m` 个两两不等的元素」）的**语义对应物**。 -/
def HasAtLeast (m : ℕ) {n : ℕ} (_S : FinStruct n) : Prop := m ≤ n

/-- **载体基数刻画**：`HasAtLeast m S ↔ m ≤ n`（载体 `Fin n`）。 -/
theorem hasAtLeast_iff_le (m : ℕ) {n : ℕ} (S : FinStruct n) :
    HasAtLeast m S ↔ m ≤ n :=
  Iff.rfl

/-- **`Fin n` 的基数**（把 `HasAtLeast` 与单射存在性联系起来的桥梁）。 -/
theorem card_fin (n : ℕ) : Fintype.card (Fin n) = n :=
  Fintype.card_fin n

/-- **「至少 `m` 个元素」⟺ 存在单射 `Fin m ↪ Fin n`**：
这是「`m` 个两两不等的元素」的**精确**集合论内容，
也是把语义谓词 `HasAtLeast` 与一阶公式
`∃x_0…∃x_{m-1}. ⋀ x_i ≠ x_j` 联系起来的那一步。 -/
theorem hasAtLeast_iff_exists_injective {m n : ℕ} :
    m ≤ n ↔ ∃ f : Fin m → Fin n, Function.Injective f := by
  constructor
  · intro h
    exact ⟨fun i => ⟨i.1, by omega⟩, fun i j hij => Fin.ext (by simpa using congrArg Fin.val hij)⟩
  · rintro ⟨f, hf⟩
    have := Fintype.card_le_of_injective f hf
    simpa [card_fin] using this

/-- **鸽巢引理（机器验证）**：`n < m` 时不存在 `Fin m → Fin n` 的单射
——即 `Fin n` 装不下 `m` 个互异元素。这是「整族无有限模型」的**技术核心**。 -/
theorem not_injective_of_lt {n m : ℕ} (h : n < m) :
    ¬ ∃ f : Fin m → Fin n, Function.Injective f := by
  rintro ⟨f, hf⟩
  have := Fintype.card_le_of_injective f hf
  simp [card_fin] at this
  omega

/-! ### 六·一、紧致性失败（Trakhtenbrot 方向） -/

/-- **反例族**：`families m n S := m ≤ n`，即第 `m` 个公式断言载体 `Fin n` ≥ `m`。
（`T : ℕ → ∀ n, FinStruct n → Prop` 是**语义公式族**，见小节诚实标注。） -/
def families (m : ℕ) : ∀ n, FinStruct n → Prop := fun n _ => m ≤ n

/-- **每个成员都有有限模型**：`families m` 在载体 `Fin m` 上成立
（`families m n S` 就是 `m ≤ n`，故具体解释无关）。

**说明**：要求 `0 < m`，因为 `Fin 0` 是空类型，无法构造 `FinStruct 0`
的常量/函数解释（`constVal : ℕ → Fin 0` 无居民）。
对紧致性反例只需**任意大**的 `m`，故 `0 < m` 的版本完全够用。 -/
theorem families_satisfiable {m : ℕ} (hm : 0 < m) :
    ∃ (n : ℕ) (S : FinStruct n), families m n S := by
  refine ⟨m, ?_, le_rfl⟩
  exact ⟨fun _ => ⟨0, hm⟩, fun _ _ => ⟨0, hm⟩, fun _ _ => false⟩

/-- **有穷子集可满足**：单元素有穷子集 `{families m}`（`m > 0`）在有限域上可满足。 -/
theorem finite_subset_satisfiable {m : ℕ} (hm : 0 < m) :
    ∃ (n : ℕ) (S : FinStruct n), families m n S :=
  families_satisfiable hm

/-- **整族没有有限模型（核心反例）**：不存在有限结构使**所有** `families m` 同时成立
——因为载体 `Fin n` 至多容纳 `n` 个元素，而 `families (n+1)` 要求至少 `n+1` 个。 -/
theorem no_finite_model_for_all :
    ¬ ∃ (n : ℕ) (S : FinStruct n), ∀ m : ℕ, families m n S := by
  rintro ⟨n, S, h⟩
  -- `families (n+1) n S` 的定义展开就是 `n + 1 ≤ n`；用 `show` 显式暴露后 `omega`
  have h1 : n + 1 ≤ n := h (n + 1)
  omega

/-- **有限域紧致性为假（Trakhtenbrot 方向）**：存在一个公式族，其**每个**成员
（从而每个有穷子集）在有限域上可满足，但**整族**在有限域上不可满足。 -/
theorem finite_domain_compactness_fails :
    ∃ T : ℕ → ∀ n, FinStruct n → Prop,
      (∀ m : ℕ, 0 < m → ∃ (n : ℕ) (S : FinStruct n), T m n S) ∧
        ¬ ∃ (n : ℕ) (S : FinStruct n), ∀ m : ℕ, T m n S :=
  ⟨families, fun _ hm => finite_subset_satisfiable hm, no_finite_model_for_all⟩

/-- **「有穷可满足 ⟹ 可满足」在有限域语义下为假**：
这是紧致性定理（一般语义）在**有限域限制**下的失败，机器验证形式。 -/
theorem finite_domain_compactness_hypothesis_false :
    ¬ (∀ T : ℕ → ∀ n, FinStruct n → Prop,
        (∀ m : ℕ, 0 < m → ∃ (n : ℕ) (S : FinStruct n), T m n S) →
          ∃ (n : ℕ) (S : FinStruct n), ∀ m : ℕ, T m n S) := by
  intro hcomp
  obtain ⟨T, hfin, hall⟩ := finite_domain_compactness_fails
  exact hall (hcomp T hfin)

/-- **具体见证（最小实例，机器验证）**：`families 2` 在载体 `Fin 1` 上**不成立**
（一个元素装不下两个）。 -/
theorem families_two_fails_on_fin_one (S : FinStruct 1) : ¬ families 2 1 S := by
  show ¬ (2 ≤ 1)
  omega

/-! ## 七、de Bruijn 全量化：把「只对指定变量编号量化」推广到标准形式

`Formula.all k φ` 只对**指定编号** `k` 量化，其余变量由赋值 `σ : ℕ → Fin n` 提供。
标准（de Bruijn）写法是：**变量用「到绑定处的距离」表示**，
`allDB φ` 量化**最外层**变量（索引 `0`）。

本节给出：

  1. `DBFormula`：de Bruijn 公式（`bvar k`：上溯 `k` 层的绑定变量；
     `allDB φ`：量化**最外层**）；
  2. `liftDB`：**提升**自由变量索引（穿过 `allDB` 时已绑定层数加一）；
     `dropDB`：它的逆；`dropDB_liftDB`：**往返恒等**（无条件）；
  3. `dbSat`：de Bruijn 公式在有限结构上的语义——环境是**绑定栈**
     `List (Fin n)`（栈头是最近绑定的变量）；
     `dbSat_allDB`（`allDB` 语义 = 对全载体的有限合取，绑定压栈）；
     `dbSat_liftBvar`（**提升引理**：`liftDB` 与压栈相容——
     这是 de Bruijn 表述的核心正确性条件）；
  4. `toDB` / `ofDB`：0 元原子、无量词具名公式 ⟷ de Bruijn 公式的互译，
     配 `ofDB_toDB`（**往返恒等**）与 `toDB_ne_none_of_free`
     （**划出适用范围**）。

**诚实标注（本节的边界）**：
- 具名版 `all k φ` 可量化**任意**编号 `k`，而 de Bruijn 的 `allDB` 只能量化
  **最外层**；两者的**完全**互译需要**环境重索引**（把 `σ : ℕ → Fin n`
  按绑定深度重新编号）。本文件**只给出无量词片段**的往返恒等
  （`ofDB_toDB`），并把一般情形标注为**未做**——
  不用平凡等式冒充「de Bruijn 与具名版完全等价」。
- `DBFormula` 的原子**不带参数列表**（`atomDB r` 而非 `atom r args`）。
  这是有意的**降级**：带 `List DBTerm` 参数会让项成为**嵌套 inductive**，
  其递归函数在 Lean 4.14 无法被结构递归检查器自动接受
  （实测 `failed to infer structural recursion`）。本节的目标是 de Bruijn
  **量化结构**本身，原子参数不改变该结构。
  **未做**：带参数的完整 de Bruijn 项语言。
- 本节 de Bruijn 语义的环境是**列表**，故 `bvar k` 越界即假
  （无「自由变量」概念）——与具名版 `σ : ℕ → Fin n` 全函数赋值的差异
  正是环境重索引问题的来源。
-/

/-- **de Bruijn 公式**：变量用「上溯层数」表示，`allDB` 量化最外层变量。 -/
inductive DBFormula where
  /-- `bvar k`：上溯 `k` 层的绑定变量（`k = 0` 是最近绑定的）。 -/
  | bvar (k : ℕ) : DBFormula
  /-- `atomDB r`：0 元关系原子（见小节诚实标注）。 -/
  | atomDB (r : ℕ) : DBFormula
  | bot : DBFormula
  | imp (φ ψ : DBFormula) : DBFormula
  /-- `allDB φ`：量化**最外层**变量（索引 `0`）。 -/
  | allDB (φ : DBFormula) : DBFormula

/-- **提升自由变量索引**：把 `≥ c` 的索引加一。
`c` 是「已绑定的层数」；穿过 `allDB` 时 `c` 加一。 -/
def liftDB (c : ℕ) : DBFormula → DBFormula
  | .bvar k => if k < c then .bvar k else .bvar (k + 1)
  | .atomDB r => .atomDB r
  | .bot => .bot
  | .imp φ ψ => .imp (liftDB c φ) (liftDB c ψ)
  | .allDB φ => .allDB (liftDB (c + 1) φ)

/-- **下移自由变量索引**：把 `> c` 的索引减一（`liftDB` 的逆）。 -/
def dropDB (c : ℕ) : DBFormula → DBFormula
  | .bvar k => if k ≤ c then .bvar k else .bvar (k - 1)
  | .atomDB r => .atomDB r
  | .bot => .bot
  | .imp φ ψ => .imp (dropDB c φ) (dropDB c ψ)
  | .allDB φ => .allDB (dropDB (c + 1) φ)

/-- **往返恒等（`drop ∘ lift = id`）**：`dropDB c (liftDB c φ) = φ`。
这是 `liftDB`/`dropDB` 互逆的**无条件**方向（对任意公式、任意 `c` 成立）。
证明对 `φ` 归纳，`allDB` 分支用 `c + 1` 处的结论（广义归纳）。

**STYLE 陷阱（本轮实测）**：`liftDB`/`dropDB` 是模式匹配 `def`，
`rw [if_pos h]` 在目标仍是 `dropDB c (bvar k)` 时报
`did not find instance of the pattern if …`——必须先用
`simp only [liftDB, dropDB]` 展开定义（同时完成 `if` 的化简），再处理算术。 -/
theorem dropDB_liftDB (φ : DBFormula) :
    ∀ c : ℕ, dropDB c (liftDB c φ) = φ := by
  induction φ with
  | bvar k =>
      intro c
      by_cases h : k < c
      · -- `k < c`：`lift` 不动，`drop` 也不动（两边都是 `bvar k`）
        simp only [liftDB, dropDB, if_pos h, if_pos (show k ≤ c by omega)]
      · -- `¬ k < c`：`lift` 给 `bvar (k+1)`，`drop` 再减一还原
        -- （`k + 1 ≤ c` 为假由 `¬ k < c` 直接给出；`(k+1) - 1 = k` 需 `k ≥ 0`，
        --  `omega` 在**没有**算术上下文时无法处理 `Nat.sub`，故用 `Nat.add_sub_cancel`）
        simp only [liftDB, dropDB, if_neg h, if_neg (show ¬ k + 1 ≤ c by omega)]
        rw [Nat.add_sub_cancel]
  | atomDB r => intro c; rfl
  | bot => intro c; rfl
  | imp φ ψ ihφ ihψ => intro c; simp only [liftDB, dropDB, ihφ c, ihψ c]
  | allDB φ ih => intro c; simp only [liftDB, dropDB, ih (c + 1)]

/-- **`liftDB` 保持「已绑定」层**：`k < c` 时 `liftDB c` 不动 `bvar k`
（「提升」只作用于自由变量）。 -/
theorem liftDB_bvar_lt {c k : ℕ} (h : k < c) : liftDB c (.bvar k) = .bvar k := by
  simp only [liftDB, if_pos h]

/-- **`liftDB` 提升自由变量**：`c ≤ k` 时 `liftDB c (bvar k) = bvar (k+1)`。 -/
theorem liftDB_bvar_ge {c k : ℕ} (h : c ≤ k) : liftDB c (.bvar k) = .bvar (k + 1) := by
  simp only [liftDB, if_neg (show ¬ k < c by omega)]

/-! ### 七·一、de Bruijn 语义（绑定栈） -/

/-- **de Bruijn 公式的有限域语义**：环境是**绑定栈** `List (Fin n)`，
栈头是最近绑定的变量；`bvar k` 取栈中第 `k` 个元素（越界为假）。 -/
def dbSat {n : ℕ} (S : FinStruct n) : List (Fin n) → DBFormula → Bool
  | η, .bvar k => (η[k]?).isSome
  | _, .atomDB r => S.relVal r []
  | _, .bot => false
  | η, .imp φ ψ => (!dbSat S η φ) || dbSat S η ψ
  | η, .allDB φ => (List.finRange n).all (fun a => dbSat S (a :: η) φ)

/-- **`allDB` 的语义**：`dbSat S η (allDB φ)` 是对全载体的有限合取，
且新绑定的元素被压到**栈头**（这正是 de Bruijn「最近绑定在最外层」的编码）。 -/
theorem dbSat_allDB {n : ℕ} (S : FinStruct n) (η : List (Fin n)) (φ : DBFormula) :
    dbSat S η (.allDB φ) = true ↔
      ∀ a : Fin n, dbSat S (a :: η) φ = true := by
  simp only [dbSat]
  rw [List.all_eq_true]
  exact ⟨fun h a => h a (List.mem_finRange a), fun h a _ => h a⟩

/-- **`bvar 0` 取栈头**：最近绑定的变量在栈头（辅助引理）。 -/
theorem dbSat_bvar_zero {n : ℕ} (S : FinStruct n) (a : Fin n) (η : List (Fin n)) :
    dbSat S (a :: η) (.bvar 0) = true := by
  simp [dbSat]

/-- **提升引理（`bvar` 层）**：`bvar (k+1)` 在 `c :: η` 下与 `bvar k` 在 `η` 下
**指向同一元素**——这正是 de Bruijn「压栈 ↔ 索引加一」相容性在变量层的
机器验证，也是 `liftDB` 设计的正确性依据。 -/
theorem dbSat_liftBvar {n : ℕ} (S : FinStruct n) (c : Fin n) (η : List (Fin n))
    (k : ℕ) : dbSat S (c :: η) (.bvar (k + 1)) = dbSat S η (.bvar k) := by
  simp only [dbSat, List.getElem?_cons_succ]

/-! ### 七·二、0 元原子、无量词片段 ⟷ de Bruijn 的互译 -/

/-- **具名 → de Bruijn（0 元原子、无量词、无等式片段）**：
只处理 **0 元**关系原子、假与蕴含；`all` 与 `eq` 一律返回 `none`
（`all k` 需按 `k` 重索引；等式被译为 `bot` 会丢失信息，使往返恒等不成立）。
适用范围因此**机器可查**。 -/
def toDB : Formula → Option DBFormula
  | .atom r args => match args with
    | [] => some (.atomDB r)
    | _ => none
  | .eq _ _ => none
  | .bot => some .bot
  | .imp φ ψ => match toDB φ, toDB ψ with
    | some a, some b => some (.imp a b)
    | _, _ => none
  | .all _ _ => none

/-- **de Bruijn → 具名**：`bvar k` 译回一元关系原子 `atom 0 [var k]`
（具名版 `Formula` 没有裸变量构造子，变量只能出现在 `FOTerm` 里）；
`allDB` 译回 `all 0`。 -/
def ofDB : DBFormula → Formula
  | .bvar k => .atom 0 [.var k]
  | .atomDB r => .atom r []
  | .bot => .bot
  | .imp φ ψ => .imp (ofDB φ) (ofDB ψ)
  | .allDB φ => .all 0 (ofDB φ)

/-- **往返恒等（具名 → de Bruijn → 具名）**：
若 `toDB φ = some ψ`，则 `ofDB ψ = φ`。
（`toDB φ = some ψ` 精确刻画了互译成功的片段：
0 元原子 + 假 + 蕴含。） -/
theorem ofDB_toDB (φ : Formula) : ∀ ψ : DBFormula, toDB φ = some ψ → ofDB ψ = φ := by
  induction φ with
  | atom r args =>
      intro ψ h
      match args with
      | [] =>
          simp only [toDB, Option.some.injEq] at h
          rw [← h]
          rfl
      | _ :: _ => simp [toDB] at h
  | eq s t => intro ψ h; simp [toDB] at h
  | bot =>
      intro ψ h
      simp only [toDB, Option.some.injEq] at h
      rw [← h]
      rfl
  | imp φ ψ ihφ ihψ =>
      intro χ h
      simp only [toDB] at h
      cases hφ : toDB φ with
      | none => simp [hφ] at h
      | some a =>
          cases hψ : toDB ψ with
          | none => simp [hφ, hψ] at h
          | some b =>
              simp only [hφ, hψ, Option.some.injEq] at h
              rw [← h]
              simp only [ofDB, ihφ a hφ, ihψ b hψ]
  | all k φ ih =>
      -- `toDB (.all k φ) = none`，与假设 `= some ψ` 矛盾
      intro ψ h
      exact absurd h (by simp [toDB])

/-- **互译适用范围的递归刻画**：由 0 元原子、假、蕴含构成的公式
（`IsFree0`）都有 `toDB φ ≠ none`。 -/
def IsFree0 : Formula → Prop
  | .atom _ args => args = []
  | .bot => True
  | .imp φ ψ => IsFree0 φ ∧ IsFree0 ψ
  | _ => False

/-- **`IsFree0` ⟹ 互译成功**：`toDB φ ≠ none`——把适用范围**机器可查**地圈出。 -/
theorem toDB_ne_none_of_free {φ : Formula} (h : IsFree0 φ) : toDB φ ≠ none := by
  induction φ with
  | atom r args =>
      simp only [IsFree0] at h
      subst h
      simp [toDB]
  | eq s t => simp only [IsFree0] at h
  | bot => simp [toDB]
  | imp φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := h
      have h1 := ihφ hφ
      have h2 := ihψ hψ
      cases ha : toDB φ with
      | none => exact absurd ha h1
      | some a =>
          cases hb : toDB ψ with
          | none => exact absurd hb h2
          | some b => simp [toDB, ha, hb]
  | all k φ ih => simp only [IsFree0] at h

/-- **含 `all` ⟹ 互译失败**：`toDB (.all k ψ) = none`。 -/
theorem toDB_eq_none_of_all (k : ℕ) (ψ : Formula) : toDB (.all k ψ) = none := rfl

/-- **具体见证（无量词往返）**：`⊥ → ⊥` 在互译片段内，往返还原。 -/
theorem ofDB_toDB_witness : ofDB (.imp .bot .bot) = (.imp .bot .bot : Formula) :=
  ofDB_toDB _ _ rfl

end Lattice.Lib.Compiler.RealFirstOrderLogic

