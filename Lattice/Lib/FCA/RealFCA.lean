import Mathlib

/-!
# LATTICE: 形式概念分析（FCA）—— 提取方向的数学基础

## ⭐ 定位声明（v15）：本模块是**一般 FCA 理论**，可独立于 LATTICE

⭐ **本模块及其下游（A 层 11 个模块 / 3,162 行）是**纯 FCA 理论**，
零 LATTICE 耦合，可独立成库**（**代码零改动**）。

**依据**：本模块的签名对**任意** `{O A : Type*}` 与**任意** `R : O → A → Prop` 成立：
```lean
def extent {O A : Type*} (R : O → A → Prop) (B : Set A) : Set O
def intent {O A : Type*} (R : O → A → Prop) (O' : Set O) : Set A
```
⇒ ⭐ **它**不是「关于 LATTICE 的定理」，而是「关于 FCA 的定理」**；
**LATTICE 只是它的一个实例**（`R x c := RealConstraintSat c x`）。

⭐⭐ **⇒ 关系已经反过来：不是「FCA 服务于 LATTICE」，
而是「LATTICE 是 FCA 的一个应用实例」。**

⚠ **A 层的依赖是一棵**树**，根就是本模块（**`import Mathlib` only**）：
`RealFCAClosureOperatorLattice` / `RealFCACompleteLattice` / `RealFCAConceptLatticeAlgebra` /
`RealFCADuality` / `RealFCAImplicationBasis` / `RealFCAManyValued` / `RealFCARoughSet` /
`RealFCATriadic` / `RealTemporalLayer`（**均只 `import RealFCA`**）；
`RealUpDown`（**Mathlib-only**）。
⭐ **分层登记与独立方案见 `FCA-LAYERING.md`。**

⚠ **B 层**（`RealCanonicalForm` / `RealCanonicalCompileComm` / `RealFCAElementApplication` /
`RealFCAInstance` / `RealImplication*`）**依赖 LATTICE 转换层 ⟹ 必须留在 LATTICE。**

---

移植 pan-meme（level0000x/pan-meme）的 FCA 概念格数学（↑↓ 互逆、
Galois 闭包、形式概念）到 LATTICE 的**提取方向**：

「非线性层提取不可逆」（开放难题）的结构化解法：提取 = 从满足关系
R ⊆ O×A（对象 O = 数据/激活，属性 A = 符号/约束）提取**形式概念**
（双向闭包不动点）——提取到闭包即稳定（幂等），可逆性在闭包上成立：

  1. extent/intent：属性集 → 满足它的对象集；对象集 → 共享属性集
     （↑↓ 的集合论形式）；
  2. Galois 连接：O' ⊆ extent(B) ⟺ B ⊆ intent(O')（反变伴随，
     提取与反提取的互逆对应）；
  3. 闭包算子：intent∘extent 与 extent∘intent 幂等（提取稳定）；
  4. 形式概念 (A,B)：A = extent(B) ∧ B = intent(A)——闭包不动点；
  5. 概念格偏序：子概念序（外延包含），概念提取幂等。

意义：非线性层的输出（对象）经满足关系提取符号属性，形式概念 =
极大稳定组合；提取是闭包运算 ⟹ 幂等稳定（再提取不变）——
不可逆问题被化为「在闭包子格上可逆」（概念格是完备格，闭包内
有唯一规范表示）。与 LATTICE 约束满足（ConstraintSat）、
提取契约（WeightToSymbolEquivalence 提取候选）衔接。

模型无关：任意对象/属性类型、任意满足关系。
-/

namespace Lattice

/-! ## 外延/内涵（↑↓ 的集合论形式） -/

def extent {O A : Type*} (R : O → A → Prop) (B : Set A) : Set O :=
  {o : O | ∀ a : A, a ∈ B → R o a}

def intent {O A : Type*} (R : O → A → Prop) (O' : Set O) : Set A :=
  {a : A | ∀ o : O, o ∈ O' → R o a}

/-! ## 定理一：外延/内涵反变单调
B₁ ⊆ B₂ ⟹ extent(B₂) ⊆ extent(B₁)；O₁ ⊆ O₂ ⟹ intent(O₂) ⊆ intent(O₁)。-/

theorem extent_antitone {O A : Type*} (R : O → A → Prop) {B₁ B₂ : Set A}
    (h : B₁ ⊆ B₂) :
    extent R B₂ ⊆ extent R B₁ := by
  intro o ho a ha
  exact ho a (h ha)

theorem intent_antitone {O A : Type*} (R : O → A → Prop) {O₁ O₂ : Set O}
    (h : O₁ ⊆ O₂) :
    intent R O₂ ⊆ intent R O₁ := by
  intro a ha o ho
  exact ha o (h ho)

/-! ## 定理二：扩张（闭包性质）
O' ⊆ extent(intent(O'))；B ⊆ intent(extent(B))。 -/

theorem subset_extent_intent {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    O' ⊆ extent R (intent R O') := by
  intro o ho a ha
  exact ha o ho

theorem subset_intent_extent {O A : Type*} (R : O → A → Prop) (B : Set A) :
    B ⊆ intent R (extent R B) := by
  intro a ha o ho
  exact ho a ha

/-! ## 定理三：Galois 连接（提取-反提取伴随）
O' ⊆ extent(B) ⟺ B ⊆ intent(O')。-/

theorem galois_connection {O A : Type*} (R : O → A → Prop) (O' : Set O) (B : Set A) :
    O' ⊆ extent R B ↔ B ⊆ intent R O' := by
  constructor
  · intro h a ha o ho
    -- h : ∀ ⦃o⦄, o ∈ O' → ∀ a, a ∈ B → R o a（⊆ 的绑定子是隐式的）
    exact h ho a ha
  · intro h o ho a ha
    -- h : ∀ ⦃a⦄, a ∈ B → ∀ o, o ∈ O' → R o a
    exact h ha o ho

/-! ## 定理四：闭包幂等（提取稳定）
extent∘intent∘extent∘intent = extent∘intent（对象端闭包幂等）。-/

theorem closure_idempotent {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    extent R (intent R (extent R (intent R O'))) = extent R (intent R O') := by
  apply Set.ext
  intro o
  constructor
  · -- extent(intent(extent(intent O'))) ⊆ extent(intent O')
    -- intent O' ⊆ intent(extent(intent O'))（扩张）⟹ extent 反变
    exact fun ho => (extent_antitone R (subset_intent_extent R (intent R O'))) ho
  · -- extent(intent O') ⊆ extent(intent(extent(intent O')))
    -- extent(intent O') ⊇ O'（扩张）⟹ intent 反变 ⟹ extent 反变
    intro ho
    exact (extent_antitone R (intent_antitone R (subset_extent_intent R O'))) ho

/-! ## 定理五：内涵端闭包幂等
intent∘extent∘intent = intent（属性端闭包幂等，反提取稳定）。-/

theorem intent_closure_idempotent {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    intent R (extent R (intent R O')) = intent R O' := by
  apply Set.ext
  intro a
  constructor
  · -- intent(extent(intent O')) ⊆ intent O'
    -- O' ⊆ extent(intent O')（扩张）⟹ intent 反变
    exact fun ha => (intent_antitone R (subset_extent_intent R O')) ha
  · -- intent O' ⊆ intent(extent(intent O'))（扩张）
    exact fun ha => (subset_intent_extent R (intent R O')) ha

/-! ## 形式概念（双向闭包不动点） -/

def IsFormalConcept {O A : Type*} (R : O → A → Prop) (O' : Set O) (B : Set A) : Prop :=
  O' = extent R B ∧ B = intent R O'

/-! ## 定理六：形式概念 ⟺ 闭包不动点
(A, B) 是概念 ⟺ A = extent(intent(A)) 且 B = intent(A)。-/

theorem formal_concept_iff_closure {O A : Type*} (R : O → A → Prop) (O' : Set O) (B : Set A) :
    IsFormalConcept R O' B ↔ (O' = extent R (intent R O') ∧ B = intent R O') := by
  constructor
  · intro h
    constructor
    · -- O' = extent B = extent(intent O')（B = intent O'；逐段重写避免误改写 O'）
      calc
        O' = extent R B := h.1
        _ = extent R (intent R O') := by rw [h.2]
    · exact h.2
  · intro h
    constructor
    · rw [h.2]
      exact h.1
    · exact h.2

/-! ## 定理七：概念提取幂等（再提取不变，稳定）
概念 (O',B) 经提取（intent/extent 闭包）后仍是同一概念。 -/

theorem concept_extraction_idempotent {O A : Type*} (R : O → A → Prop) (O' : Set O) (B : Set A)
    (h : IsFormalConcept R O' B) :
    IsFormalConcept R (extent R (intent R O')) (intent R O') := by
  constructor
  · -- extent(intent O') = extent(intent O')（rfl）
    rfl
  · -- intent O' = intent(extent(intent O'))（内涵端闭包幂等）
    exact (intent_closure_idempotent R O').symm

/-! ## 概念格偏序（子概念序） -/

def IsSubconcept {O A : Type*} (R : O → A → Prop) (C₁ C₂ : Set O × Set A) : Prop :=
  C₁.1 ⊆ C₂.1

/-! ## 定理八：子概念序传递（概念格是预序） -/

theorem subconcept_trans {O A : Type*} (R : O → A → Prop) (C₁ C₂ C₃ : Set O × Set A)
    (h₁₂ : IsSubconcept R C₁ C₂) (h₂₃ : IsSubconcept R C₂ C₃) :
    IsSubconcept R C₁ C₃ := by
  unfold IsSubconcept at *
  exact fun o ho => h₂₃ (h₁₂ ho)

/-! ## 定理九：extent∘intent∘extent = extent（对偶闭包幂等）
extent(intent(extent(B))) = extent(B)（对象端闭包在属性集外延上不动）。-/

theorem extent_intent_extent {O A : Type*} (R : O → A → Prop) (B : Set A) :
    extent R (intent R (extent R B)) = extent R B := by
  apply Set.ext
  intro o
  constructor
  · -- extent(intent(extent B)) ⊆ extent B：B ⊆ intent(extent B)（扩张）⟹ extent 反变
    exact fun ho => (extent_antitone R (subset_intent_extent R B)) ho
  · -- extent B ⊆ extent(intent(extent B))：扩张
    exact fun ho => (subset_extent_intent R (extent R B)) ho

/-! ## 概念格 meet（外延交 + 交外延的内涵） -/

def concept_meet {O A : Type*} (R : O → A → Prop) (C₁ C₂ : Set O × Set A) : Set O × Set A :=
  (C₁.1 ∩ C₂.1, intent R (C₁.1 ∩ C₂.1))

/-! ## 定理十：概念 meet 是概念（格闭合）
两个概念的 meet 仍是形式概念（完备格的 meet 半边）。-/

theorem concept_meet_is_concept {O A : Type*} (R : O → A → Prop) (C₁ C₂ : Set O × Set A)
    (h₁ : IsFormalConcept R C₁.1 C₁.2) (h₂ : IsFormalConcept R C₂.1 C₂.2) :
    IsFormalConcept R (concept_meet R C₁ C₂).1 (concept_meet R C₁ C₂).2 := by
  unfold concept_meet
  constructor
  · -- C₁.1∩C₂.1 = extent(intent(C₁.1∩C₂.1))
    apply Set.ext
    intro o
    constructor
    · -- o ∈ C₁.1∩C₂.1 ⟹ o ∈ extent(intent(·))（扩张）
      exact fun ho => (subset_extent_intent R (C₁.1 ∩ C₂.1)) ho
    · -- o ∈ extent(intent(·)) ⟹ o ∈ C₁.1∩C₂.1
      intro ho
      constructor
      · -- o ∈ C₁.1：extent(intent(C₁.1∩C₂.1)) ⊆ extent(intent C₁.1) = C₁.1
        have hsub : extent R (intent R (C₁.1 ∩ C₂.1)) ⊆ C₁.1 := by
          calc
            extent R (intent R (C₁.1 ∩ C₂.1)) ⊆ extent R (intent R C₁.1) := by
              -- C₁.1∩C₂.1 ⊆ C₁.1 ⟹ intent C₁.1 ⊆ intent(·) ⟹ extent 反变
              exact extent_antitone R (intent_antitone R (by
                exact Set.inter_subset_left : C₁.1 ∩ C₂.1 ⊆ C₁.1))
            _ = C₁.1 := by
              -- 概念恒等：C₁.1 = extent(intent C₁.1)（h₁.2：C₁.2 = intent C₁.1；h₁.1：C₁.1 = extent C₁.2）
              rw [← h₁.2, ← h₁.1]
        exact hsub ho
      · -- o ∈ C₂.1（对称）
        have hsub₂ : extent R (intent R (C₁.1 ∩ C₂.1)) ⊆ C₂.1 := by
          calc
            extent R (intent R (C₁.1 ∩ C₂.1)) ⊆ extent R (intent R C₂.1) := by
              exact extent_antitone R (intent_antitone R (by
                exact Set.inter_subset_right : C₁.1 ∩ C₂.1 ⊆ C₂.1))
            _ = C₂.1 := by
              rw [← h₂.2, ← h₂.1]
        exact hsub₂ ho
  · -- intent(C₁.1∩C₂.1) = intent(C₁.1∩C₂.1)（第二个分量 rfl）
    rfl

/-! ## 概念格 join（内涵交 + 交内涵外延的意图） -/

def concept_join {O A : Type*} (R : O → A → Prop) (C₁ C₂ : Set O × Set A) : Set O × Set A :=
  (extent R (C₁.2 ∩ C₂.2), intent R (extent R (C₁.2 ∩ C₂.2)))

/-! ## 定理十一：概念 join 是概念（格闭合）
任意两对的 join 自动是形式概念（extent∘intent∘extent = extent，
闭合性对任意输入成立）。-/

theorem concept_join_is_concept {O A : Type*} (R : O → A → Prop) (C₁ C₂ : Set O × Set A) :
    IsFormalConcept R (concept_join R C₁ C₂).1 (concept_join R C₁ C₂).2 := by
  unfold concept_join
  constructor
  · -- extent(C₁.2∩C₂.2) = extent(intent(extent(·)))（对偶闭包幂等）
    exact (extent_intent_extent R (C₁.2 ∩ C₂.2)).symm
  · rfl

/-! ## 注：提取方向闭环
  FCA 概念 = 满足关系 R 下的双向闭包不动点（定理六）：
  从非线性层输出（对象）提取符号（属性）→ 概念格；
  提取幂等（定理七）⟹ 稳定表示；Galois 连接（定理三）⟹
  提取/反提取伴随对应；闭包幂等（定理四/五）⟹ 不可逆问题
  在闭包子格上可逆（概念有唯一规范表示）。
  衔接：约束满足关系（ConstraintSat）实例化 R；提取候选
  （WeightToSymbolEquivalence）的稳定性判定 = 闭包不动点判定。
  pan-meme（FCA ↑↓/概念格/信息守恒）移植完成。 -/

end Lattice
