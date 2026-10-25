import Mathlib

/-!
# LATTICE: 精化演算 —— 转换的「保真度规格」为何不可平凡化

**为什么做这个文件**：项目目标是「**编译（符号 → 权重）保持语义**」。
H3 的核实结论指出，Lv-00 的 `compile_preserves_satisfiability`
（`RealLv00Compiler.compile_preserves_satisfiability`）是**平凡真**：
它的假设 `satisfiable (eval_program initialState prog)` 展开后是纯语法的
`errors = []`，**在证明体中根本没被用到**（同文件的
`compile_preserves_satisfiability_hypothesis_unused` 把这一事实机器化 ——
结论**无条件**成立）。因此那条「保真度定理」对**任何**程序都成立，
**不携带任何编译正确性信息**。

本文件回答一个正面问题：**什么样的「保真度」定义是不可平凡化的？**
答案是**精化关系（refinement）+ 前向模拟**。本文件给出：

1. **精化关系** `Refines R c a`（具体 `c` 精化抽象 `a`），以及**数据精化**的
   一般载体 `R : Concrete → Abstract → Prop`；
2. **前向模拟**：`Simulation R step stepSharp` 定义为
   `∀ c a, R c a → ∀ c', step c c' → ∃ a', stepSharp a a' ∧ R c' a'`
   —— 「具体走一步，抽象**必须**能跟上一步且保持 `R`」；
3. **模拟的可靠性（主定理）**：`R c a` 且 `c →* c'` ⟹ `∃ a', a →* a' ∧ R c' a'`
   （**多步前向模拟**，对 `ReflTransGen` 归纳）；
4. **组合性**：
   * **顺序组合**：`Simulation R s₁ a₁ → Simulation R s₂ a₂ → Simulation R (s₁;s₂) (a₁;a₂)`；
   * **并行组合**：`Simulation R₁ s₁ a₁ → Simulation R₂ s₂ a₂ →
     Simulation (Prod R₁ R₂) (s₁ ‖ s₂) (a₁ ‖ a₂)`；
   这是「**模块化编译正确性**」的钥匙：分量正确 ⟹ 组合正确；
5. **不可平凡化的保真度规格**：把「符号 → 权重」的保真度**定义为**
   `Refines (SemEq) compiled source`（语义保持 = 精化关系成立），
   并给出**判定性分离**（⚠ **订正 B340**：原文此处写"分离定理 `fidelity_not_trivial`"，
   **而**该名字不存在****——**分离性由**两条**定理合成**，**不是一个定理**）：
   * 存在**满足**该规格的编译（`theorem fidelity_satisfied_example`，前一条定理）；
   * 存在**不满足**该规格的编译（`theorem fidelity_fails_example`，后一条定理，机器验证反例）；
   **两者都有**才说明规格**非平凡**（若对一切成立则平凡，若对一切不成立则无用）。
   这正是 H3 那类 `: True` / 假设未用的定理**不具备**的性质；
6. **与 Lv-00 的对照（本文件的关键诊断）**：
   `lv00_style_fidelity_is_trivial` —— 把 Lv-00 式「保真度」
   （`True` 型结论）写成本文件的精化语法后，证明它**对任意编译成立**，
   故**不可能是**非平凡规格。这把 H3 的核实结论升级为**结构性判据**：
   「假设未被使用」不是笔误，而是**规格写法**（无精化关系）的直接后果。

## 诚实边界（本文件不证 / 不声称的）

* **本文件不声称**给出了「符号 → 权重」转换的**具体**编译器实例
  （那需要 `SymbolToWeightCorrectness` 的 `ConstraintSet`/`Layer` 具体语义）。
  本文件给出的是**规格框架** + **非平凡性的判定性证据**
  （一对正例/反例），以及它与既有 `symbolToWeight_correct` 的接口说明。
  **未做**：把 `symbolToWeight_correct` 直接实例化为本文件的 `Refines`
  （需要把 `List Int` 输入提升为抽象状态，**属后续工作**）；
* **模拟的方向**：本文件只做**前向模拟**（`c → c'` ⟹ `∃ a', a →* a'`）。
  **未做**：后向模拟（`a → a'` ⟹ `∃ c', c →* c'`）、
  以及「双向模拟 = 双向精化」的等价刻画；
* **未做**：精化的**格结构**（`⊑` 是否构成格、最大精化、最小精化）
  —— 那需要把「编译」本身作为抽象元素，属**抽象解释**方向
  （见 `RealAbstractInterpretation`）；
* **未做**：**终止性/发散**下的精化（本文件的 `step` 是关系而非函数，
  允许发散，但**未证**任何终止性定理）；
* **未做**：精化关系的**余代数/终余代数**表述（`bisimulation` 的范畴层）；
* 无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

open scoped Classical

namespace Lattice

/-! ## 一、精化关系与数据精化 -/

/-- **精化关系**：具体状态 `c` 精化抽象状态 `a`，记 `Refines R c a`。
这里的 `R : Concrete → Abstract → Prop` 是**数据精化关系**（simulation relation），
`Refines R` 只是它的更可读别名 —— 保留两者是为了让下游定理的陈述
既可以用 `R c a`（在归纳证明中方便 `rw`），也可以用 `Refines R c a`
（在规格陈述中自解释）。 -/
def Refines {Concrete Abstract : Type*} (R : Concrete → Abstract → Prop)
    (c : Concrete) (a : Abstract) : Prop := R c a

/-- `Refines` 与底层关系定义相等（供 `unfold`/`simp` 使用）。 -/
theorem refines_iff {Concrete Abstract : Type*} (R : Concrete → Abstract → Prop)
    (c : Concrete) (a : Abstract) : Refines R c a ↔ R c a := Iff.rfl

/-- **精化的自反性**：相同状态的恒等关系是精化。 -/
theorem refines_refl {α : Type*} : Refines (fun a b : α => a = b) = fun a b => a = b := rfl

/-- **精化的传递性（关系复合）**：若 `R₁ ⊆ R₂`（逐点蕴含）且 `c` 经 `R₁` 精化 `a`，
则 `c` 经 `R₂` 精化 `a`。这是**规格弱化**的标准形式：
更强的数据精化关系蕴含更弱的。 -/
theorem refines_mono {Concrete Abstract : Type*} {R₁ R₂ : Concrete → Abstract → Prop}
    (h : ∀ c a, R₁ c a → R₂ c a) {c : Concrete} {a : Abstract}
    (hc : Refines R₁ c a) : Refines R₂ c a := h c a hc

/-! ## 二、前向模拟 -/

section Simulation

variable {Concrete Abstract : Type*}

/-- **前向模拟（forward simulation）**：具体步骤关系 `step` 与抽象步骤关系
`stepSharp` 在数据精化 `R` 下相容 ——
**具体走一步，抽象必须能跟上（至少）一步，且终态仍满足 `R`**。

这是「转换保真度」的**核心定义**：它把「编译器正确」变成一条**局部**条件，
可以逐构造子（`seq` / `par` / `assign` / …）验证，再靠组合性拼装
（见第四节的顺序/并行组合定理）。 -/
def Simulation (R : Concrete → Abstract → Prop)
    (step : Concrete → Concrete → Prop) (stepSharp : Abstract → Abstract → Prop) : Prop :=
  ∀ c a, R c a → ∀ c', step c c' → ∃ a', stepSharp a a' ∧ R c' a'

/-- **模拟的等价展开**（供 `rintro`/`obtain` 风格使用）。 -/
theorem simulation_iff {R : Concrete → Abstract → Prop}
    {step : Concrete → Concrete → Prop} {stepSharp : Abstract → Abstract → Prop} :
    Simulation R step stepSharp ↔
      ∀ c a, R c a → ∀ c', step c c' → ∃ a', stepSharp a a' ∧ R c' a' :=
  Iff.rfl

/-- **单步模拟的「具体侧」提取**：给定模拟与 `R c b`、`step c c'`，
存在抽象后继 `a'` 满足 `stepSharp b a' ∧ R c' a'`。
这是 `Simulation` 的**消去律**，下游证明中反复使用。

**写法说明**：`b` 的类型必须是 `Abstract`（初稿误写成 `{c a : Concrete}`，
导致 `h c b hR c' hs` 报 `don't know how to synthesize implicit argument 'a'`
—— 因为 `b` 被当成 `Concrete`，与 `stepSharp` 需要的 `Abstract` 冲突）。 -/
theorem simulation_step {R : Concrete → Abstract → Prop}
    {step : Concrete → Concrete → Prop} {stepSharp : Abstract → Abstract → Prop}
    (h : Simulation R step stepSharp) {c : Concrete} {b : Abstract}
    (hR : R c b) {c' : Concrete} (hs : step c c') :
    ∃ a', stepSharp b a' ∧ R c' a' :=
  h c b hR c' hs

/-- **多步前向模拟（主定理）**：若 `R c a` 且 `c` 经 `step` 的**自反传递闭包**
到达 `c'`，则存在 `a'` 使得 `a` 经 `stepSharp` 的自反传递闭包到达 `a'`
且 `R c' a'`。

证明：对 `ReflTransGen` 归纳。零步取 `a' := a`（`ReflTransGen.refl`）；
单步用 `simulation_step` 得 `a''`，再接归纳假设，最后用
`ReflTransGen.tail` 拼接。**这条是「保真度沿执行保持」的形式化**：
一步对一步的局部保证，沿任意步数累积。 -/
theorem simulation_reflTransGen {R : Concrete → Abstract → Prop}
    {step : Concrete → Concrete → Prop} {stepSharp : Abstract → Abstract → Prop}
    (h : Simulation R step stepSharp) {c c' : Concrete} {a : Abstract}
    (hR : R c a) (hc : Relation.ReflTransGen step c c') :
    ∃ a', Relation.ReflTransGen stepSharp a a' ∧ R c' a' := by
  induction hc with
  | refl => exact ⟨a, Relation.ReflTransGen.refl, hR⟩
  | tail hcab hbc ih =>
      obtain ⟨a', ha', hRa'⟩ := ih
      obtain ⟨a'', ha'', hRa''⟩ := simulation_step h hRa' hbc
      exact ⟨a'', Relation.ReflTransGen.tail ha' ha'', hRa''⟩

end Simulation

/-! ## 三、组合性：顺序与并行 -/

section Composition

variable {C₁ A₁ C₂ A₂ B₁ : Type*}

/-- **顺序组合的步骤关系（一般形）**：终止谓词 `done` 的类型抽成**独立参数 `D`**，
并用**显式相等约束** `D = C₁` 把「终止谓词作用在第一分量上」写进类型。

**为什么必须有这条（本文件实际修正过一次）**：初稿把 `StepSeq` 写成
`(done : C₁ → Prop)`，于是 `StepSeq doneA step₁Sharp step₂Sharp`
（`doneA : A₁ → Prop`）**类型不合法**，Lean 报
`application type mismatch StepSeq doneC; argument doneC has type C₁ → Prop
but is expected to have type A₁ → Prop`。
根因是 `Simulation` 的两端是**不同类型**（`C₁ × C₂` 与 `A₁ × A₂`），
故两侧的顺序组合**必须**是两个不同的 `StepSeq` 实例。

**第二次修正**：把 `D` 完全自由化会让构造子 `snd` 的 `done c₁`
类型不符（`done : D → Prop` 而 `c₁ : C₁`，Lean 报
`argument c₁ has type C₁ but is expected to have type D`）。
正确做法：**保留 `D` 作为参数，但在构造子里用 `Eq.rec`/`cast` 型的
显式写法**过于笨重 —— 本文件改用**每侧各自定义一个 `StepSeq`** 的
简洁方案（见下 `StepSeqC` / `StepSeqA`），二者同构但类型各自正确。 -/
inductive StepSeqC {C₁ C₂ : Type*} (done : C₁ → Prop)
    (step₁ : C₁ → C₁ → Prop) (step₂ : C₂ → C₂ → Prop) :
    (C₁ × C₂) → (C₁ × C₂) → Prop
  /-- 第一阶段内走一步。 -/
  | fst {c₁ c₁' : C₁} {c₂ : C₂} (h : step₁ c₁ c₁') :
      StepSeqC done step₁ step₂ (c₁, c₂) (c₁', c₂)
  /-- 第一阶段已完成，第二阶段走一步。 -/
  | snd {c₁ : C₁} {c₂ c₂' : C₂} (hd : done c₁) (h : step₂ c₂ c₂') :
      StepSeqC done step₁ step₂ (c₁, c₂) (c₁, c₂')

/-- **顺序组合的步骤关系（抽象侧对偶）**：与 `StepSeqC` **逐构造子同构**，
只是终止谓词作用在**抽象**第一分量 `A₁` 上。

**诚实标注**：这是 Lean 没有「类型参数化构造子」的**直接后果** ——
两个 `inductive` 体完全相同，唯一差别是 `done` 的定义域。
本文件如实保留两份并在 docstring 说明**为什么不能合并**
（合并需要 `D` 与分量类型相等的依赖约束，Lean 4.14 的 `inductive`
构造子不直接支持）。 -/
inductive StepSeqA {A₁ A₂ : Type*} (done : A₁ → Prop)
    (step₁ : A₁ → A₁ → Prop) (step₂ : A₂ → A₂ → Prop) :
    (A₁ × A₂) → (A₁ × A₂) → Prop
  /-- 第一阶段内走一步。 -/
  | fst {a₁ a₁' : A₁} {a₂ : A₂} (h : step₁ a₁ a₁') :
      StepSeqA done step₁ step₂ (a₁, a₂) (a₁', a₂)
  /-- 第一阶段已完成，第二阶段走一步。 -/
  | snd {a₁ : A₁} {a₂ a₂' : A₂} (hd : done a₁) (h : step₂ a₂ a₂') :
      StepSeqA done step₁ step₂ (a₁, a₂) (a₁, a₂')

/-- **顺序组合的模拟性（组合性主定理之一）**：若 `R₁`/`R₂` 分别是两阶段的
数据精化、各自模拟，且**具体侧的完成蕴含抽象侧的完成**
（`hDone : ∀ c a, R₁ c a → doneC c → doneA a`），
则二元组关系 `R₁ × R₂` 模拟顺序组合。

**`hDone` 的方向（本文件实际修正过两次，这是最终正确的一版）**：
* 具体侧走 `snd`（第一期已完成）时，`cases hstep` 直接给出 `hd : doneC c₁`；
* 要**构造**抽象侧的 `StepSeqA.snd`，需要 `doneA a₁`；
* 故所需的相容性是 **`doneC c → doneA a`**（具体完成 ⟹ 抽象完成），
  而不是反方向。初稿写成 `doneA a → doneC c`，
  Lean 报 `argument hd has type doneC c₁ but is expected to have type doneA a₁`
  —— 这是方向写反的**直接症状**。

**语义解释**：抽象是具体的**过近似**，故「具体跑完了」必须蕴含
「抽象也能跑完」；反之不成立（抽象可能先行完成）。这与 `Simulation`
「抽象能跟上具体」的整体方向**一致**。 -/
theorem simulation_seq {R₁ : C₁ → A₁ → Prop} {R₂ : C₂ → A₂ → Prop}
    {step₁ : C₁ → C₁ → Prop} {step₂ : C₂ → C₂ → Prop}
    {step₁Sharp : A₁ → A₁ → Prop} {step₂Sharp : A₂ → A₂ → Prop}
    (h₁ : Simulation R₁ step₁ step₁Sharp) (h₂ : Simulation R₂ step₂ step₂Sharp)
    {doneC : C₁ → Prop} {doneA : A₁ → Prop}
    (hDone : ∀ c a, R₁ c a → doneC c → doneA a) :
    Simulation (fun p : C₁ × C₂ => fun q : A₁ × A₂ => R₁ p.1 q.1 ∧ R₂ p.2 q.2)
      (StepSeqC doneC step₁ step₂)
      (StepSeqA doneA step₁Sharp step₂Sharp) := by
  rintro ⟨c₁, c₂⟩ ⟨a₁, a₂⟩ ⟨hR₁, hR₂⟩ ⟨c₁', c₂'⟩ hstep
  cases hstep with
  | fst h =>
      obtain ⟨a₁', ha', hR₁'⟩ := h₁ c₁ a₁ hR₁ c₁' h
      exact ⟨(a₁', a₂), StepSeqA.fst ha', hR₁', hR₂⟩
  | snd hd h =>
      obtain ⟨a₂', ha', hR₂'⟩ := h₂ c₂ a₂ hR₂ c₂' h
      exact ⟨(a₁, a₂'), StepSeqA.snd (hDone c₁ a₁ hR₁ hd) ha', hR₁, hR₂'⟩

/-- **`hDone` 的消去形式**：`R₁ c a` 与 `doneC c` 给出 `doneA a` ——
`simulation_seq` 中唯一用到 `hDone` 的地方，也是「抽象过近似具体」的方向性体现。 -/
theorem hDone_apply {R₁ : C₁ → A₁ → Prop} {doneC : C₁ → Prop} {doneA : A₁ → Prop}
    (hDone : ∀ c a, R₁ c a → doneC c → doneA a) {c : C₁} {a : A₁}
    (hR : R₁ c a) (hc : doneC c) : doneA a :=
  hDone c a hR hc

/-- **并行组合的步骤关系**：`StepPar s₁ s₂` 在任一分量内走一步，另一分量不动
（交错语义 / interleaving semantics）。 -/
inductive StepPar {C₁ C₂ : Type*} (step₁ : C₁ → C₁ → Prop) (step₂ : C₂ → C₂ → Prop) :
    (C₁ × C₂) → (C₁ × C₂) → Prop
  /-- 左分量走一步。 -/
  | left {c₁ c₁' : C₁} {c₂ : C₂} (h : step₁ c₁ c₁') : StepPar step₁ step₂ (c₁, c₂) (c₁', c₂)
  /-- 右分量走一步。 -/
  | right {c₁ : C₁} {c₂ c₂' : C₂} (h : step₂ c₂ c₂') : StepPar step₁ step₂ (c₁, c₂) (c₁, c₂')

/-- **并行组合的模拟性（组合性主定理之二）**：若两分量各自模拟，
则逐分量合取的关系模拟 `StepPar`。

与 `simulation_seq` 相比，本条**不需要**任何终止谓词相容性 ——
交错语义下两分量**完全独立**，这正是「并行组合性」比「顺序组合性」更干净的原因。 -/
theorem simulation_par {R₁ : C₁ → A₁ → Prop} {R₂ : C₂ → A₂ → Prop}
    {step₁ : C₁ → C₁ → Prop} {step₂ : C₂ → C₂ → Prop}
    {step₁Sharp : A₁ → A₁ → Prop} {step₂Sharp : A₂ → A₂ → Prop}
    (h₁ : Simulation R₁ step₁ step₁Sharp) (h₂ : Simulation R₂ step₂ step₂Sharp) :
    Simulation (fun p : C₁ × C₂ => fun q : A₁ × A₂ => R₁ p.1 q.1 ∧ R₂ p.2 q.2)
      (StepPar step₁ step₂) (StepPar step₁Sharp step₂Sharp) := by
  rintro ⟨c₁, c₂⟩ ⟨a₁, a₂⟩ ⟨hR₁, hR₂⟩ ⟨c₁', c₂'⟩ hstep
  cases hstep with
  | left h =>
      obtain ⟨a₁', ha', hR₁'⟩ := h₁ c₁ a₁ hR₁ c₁' h
      exact ⟨(a₁', a₂), StepPar.left ha', hR₁', hR₂⟩
  | right h =>
      obtain ⟨a₂', ha', hR₂'⟩ := h₂ c₂ a₂ hR₂ c₂' h
      exact ⟨(a₁, a₂'), StepPar.right ha', hR₁, hR₂'⟩

/-- **模拟的序列复合（组合性主定理之三）**：若 `R₁` 把 `C₁` 精化到 `A₁`、
`R₂` 把 `A₁` 精化到 `B₁`（**两段式编译**：具体 → 中间 → 抽象），
则**关系复合** `R₂ ∘ R₁` 把 `C₁` 精化到 `B₁`。

这是「**模块化编译正确性**」的第三种组合形式，且是最贴近本项目的一种：
「符号 → 权重」的转换通常是**多段**的（符号 → IR → 权重），
本定理说明**每段的正确性证明可以复合**，无需重看整条链。
具体步骤关系同样取复合 `RelComp`（具体走一步 → 中间走一步）。 -/
theorem simulation_comp {R₁ : C₁ → A₁ → Prop} {R₂ : A₁ → B₁ → Prop}
    {step₁ : C₁ → C₁ → Prop} {step₂ : A₁ → A₁ → Prop} {step₃ : B₁ → B₁ → Prop}
    (h₁ : Simulation R₁ step₁ step₂) (h₂ : Simulation R₂ step₂ step₃) :
    Simulation (fun c b => ∃ a, R₁ c a ∧ R₂ a b) step₁ step₃ := by
  rintro c b ⟨a, hR₁, hR₂⟩ c' hstep
  obtain ⟨a', ha', hR₁'⟩ := h₁ c a hR₁ c' hstep
  obtain ⟨b', hb', hR₂'⟩ := h₂ a b hR₂ a' ha'
  exact ⟨b', hb', a', hR₁', hR₂'⟩

/-- **三段复合**：由两段复合直接迭代得到
（「符号 → IR → 权重 → 硬件」式的多段转换链）。
表明组合性是**可叠加**的，不需要为更长链条引入新定理。 -/
theorem simulation_comp_three {R₁ : C₁ → A₁ → Prop} {R₂ : A₁ → A₂ → Prop}
    {R₃ : A₂ → B₁ → Prop}
    {step₁ : C₁ → C₁ → Prop} {step₂ : A₁ → A₁ → Prop}
    {step₃ : A₂ → A₂ → Prop} {step₄ : B₁ → B₁ → Prop}
    (h₁ : Simulation R₁ step₁ step₂) (h₂ : Simulation R₂ step₂ step₃)
    (h₃ : Simulation R₃ step₃ step₄) :
    Simulation (fun c b => ∃ a₂, (∃ a₁, R₁ c a₁ ∧ R₂ a₁ a₂) ∧ R₃ a₂ b) step₁ step₄ :=
  simulation_comp (simulation_comp h₁ h₂) h₃

/-- **复合精化的多步展开**：把 `simulation_comp` 与 `simulation_reflTransGen`
串起来 —— 两段式转换下，具体走任意多步，抽象都能跟上。
这是「多段编译在整条执行上保真」的完整陈述。 -/
theorem simulation_comp_reflTransGen {R₁ : C₁ → A₁ → Prop} {R₂ : A₁ → B₁ → Prop}
    {step₁ : C₁ → C₁ → Prop} {step₂ : A₁ → A₁ → Prop} {step₃ : B₁ → B₁ → Prop}
    (h₁ : Simulation R₁ step₁ step₂) (h₂ : Simulation R₂ step₂ step₃)
    {c c' : C₁} {b : B₁} (hR : ∃ a, R₁ c a ∧ R₂ a b)
    (hc : Relation.ReflTransGen step₁ c c') :
    ∃ b', Relation.ReflTransGen step₃ b b' ∧ ∃ a, R₁ c' a ∧ R₂ a b' :=
  simulation_reflTransGen (simulation_comp h₁ h₂) hR hc

end Composition

/-! ## 四、不可平凡化的保真度规格 —— 与 Lv-00 式 `True` 规格的对照 -/

section Fidelity

/-- **Lv-00 式「保真度」**：结论是 `True`，即**对一切**编译声称成功。

这正是 `RealLv00Compiler.compile_preserves_satisfiability` 的**语义形状**
（其结论由退化环境无条件给出，同文件的
`compile_preserves_satisfiability_hypothesis_unused` 把「假设未被使用」
机器化为「结论无条件成立」）。这里的定义把它写成
本文件的精化语法，以便与下面的**真**规格对照。

**写法说明**：`compile` 被**显式丢弃**（`fun _ => True`），
这**正是**本定义要暴露的缺陷 —— 一条不引用被检验对象的「规格」
不可能对它作出任何断言。`Compiled` 保留在参数里是为了让类型形状
与 `FidelitySpec` 对照。 -/
def TrivialFidelity (Compiled : Type*) (_compile : Compiled → Compiled) : Prop :=
  ∀ _x : Compiled, True

/-- **Lv-00 式规格是不可平凡化的反面：它对一切编译成立。**
「对一切 `compile` 成立」⟹ 该规格**不可能**区分正确与错误的编译 ⟹
它不携带任何正确性信息。这是 H3 核实结论的**结构性判据**：
问题不在证明技巧，而在**规格写法**（没有精化关系）。 -/
theorem lv00_style_fidelity_is_trivial {Compiled : Type*}
    (compile : Compiled → Compiled) : TrivialFidelity Compiled compile :=
  fun _ => trivial

/-- **真保真度规格（语义保持 = 精化关系成立）**：编译产物 `compile s`
在数据精化 `R` 下精化源 `s`，**并且** `compile s` 与 `s` 逐步模拟。

与 `TrivialFidelity` 的差别是**本质的**：这是一条**关于 `R` 与 `step` 的
具体约束**，而不是 `True`。 -/
def FidelitySpec {Source Compiled : Type*}
    (R : Compiled → Source → Prop)
    (stepS : Source → Source → Prop) (stepC : Compiled → Compiled → Prop)
    (compile : Source → Compiled) : Prop :=
  (∀ s, Refines R (compile s) s) ∧
    Simulation (fun c s => R c s) stepC stepS

/-- **`FidelitySpec` 蕴含多步保真**：在 `FidelitySpec` 下，
**编译产物**走任意多步，**源**都能跟上，且关系 `R` 保持。

**方向说明（本文件实际修正过一次）**：`Simulation R step stepSharp` 中
`R : Concrete → Abstract`，而 `FidelitySpec` 取
`Concrete := Compiled`、`Abstract := Source`（「源」是被精化的规范、
「编译产物」是实现）。故 `simulation_reflTransGen` 的**具体侧**是 `Compiled`、
`ReflTransGen` 必须跑在 **`stepC`** 上，结论给 `stepS` 侧的匹配 ——
初稿把两侧写反，症状是
`hs has type ReflTransGen stepS s s' but is expected to have type
ReflTransGen stepC (compile s) ?m`。

**前提**：以「编译产物 `compile s` 具体化——源 `s`」为起点（`h.1 s`），
沿 `stepC` 走任意多步。 -/
theorem fidelity_spec_multistep {Source Compiled : Type*}
    {R : Compiled → Source → Prop}
    {stepS : Source → Source → Prop} {stepC : Compiled → Compiled → Prop}
    {compile : Source → Compiled} (h : FidelitySpec R stepS stepC compile)
    {s : Source} {c' : Compiled}
    (hc : Relation.ReflTransGen stepC (compile s) c') :
    ∃ s', Relation.ReflTransGen stepS s s' ∧ R c' s' :=
  simulation_reflTransGen h.2 (h.1 s) hc

/-- **`FidelitySpec` 的单步保真（消去形式）**：编译产物走一步，
源能跟上一步且 `R` 保持 —— `simulation_step` 在 `FidelitySpec` 上的特化。 -/
theorem fidelity_spec_step {Source Compiled : Type*}
    {R : Compiled → Source → Prop}
    {stepS : Source → Source → Prop} {stepC : Compiled → Compiled → Prop}
    {compile : Source → Compiled} (h : FidelitySpec R stepS stepC compile)
    {s : Source} {c : Compiled} (hR : R c s) {c' : Compiled} (hc : stepC c c') :
    ∃ s', stepS s s' ∧ R c' s' :=
  h.2 c s hR c' hc

/-- **非平凡性的判定性证据（正例侧）**：存在满足 `FidelitySpec` 的编译 ——
取源/编译为同一类型、`R := Eq`、`step` 相同、`compile := id`。
这说明规格**不是不可满足的**（否则它无用）。 -/
theorem fidelity_satisfied_example (α : Type*) (step : α → α → Prop) :
    FidelitySpec (fun c s : α => c = s) step step id := by
  refine ⟨fun s => rfl, ?_⟩
  rintro c a rfl c' hc'
  exact ⟨c', hc', rfl⟩

/-- **非平凡性的判定性证据（反例侧）**：存在**不满足** `FidelitySpec` 的编译。

**构造**（注意 `R` **不能**取 `Eq`：若 `R = Eq` 且两侧 `step` 都取 `Eq`，
则**任何**函数都满足 `Simulation`，反例构造必然失败 ——
这是本文件在形式化过程中**实际踩到的坑**，记录以免重蹈）：

* 源 `Source := Bool`、编译 `Compiled := Bool`；
* 数据精化 `R c s := (c = true ↔ s = true)`（「真值一致」）——
  它实际成立的对只有 `(false, false)` 与 `(true, true)`
  （因为 `false = true ↔ true = true` 是 `False ↔ True`，**假**）；
* 「编译」取 `Bool.not`。

于是 `s = true` 时编译产物是 `false`，而 `R false true` **为假**，
故 `FidelitySpec` 的第一项（`∀ s, Refines R (compile s) s`）在 `s = true` 处失败。

这条与 `fidelity_satisfied_example` 合起来证明：**`FidelitySpec` 的成立与否
依赖被检验的 `compile`** —— 它不是「对一切成立」的 `True` 型规格。
这正是 H3 那类 `: True` / 假设未用的定理**不具备**的性质。 -/
theorem fidelity_fails_example :
    ¬ FidelitySpec (fun c s : Bool => (c = true ↔ s = true))
        (fun s s' : Bool => s' = s) (fun c c' : Bool => c' = c) Bool.not := by
  rintro ⟨h1, _⟩
  have hs : (Bool.not true = true ↔ true = true) := h1 true
  simp at hs

end Fidelity

end Lattice
