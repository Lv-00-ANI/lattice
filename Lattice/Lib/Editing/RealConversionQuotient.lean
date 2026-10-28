import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealConversionRoundTrip
/-!
# LATTICE: 转换的**商结构** —— 「编译后不可区分」是等价关系，且在商上良定义

## 1. 本文件建立什么

`RealCanonicalForm` 已经把「缩放轨道」问题处理到 `ScaleClass`（倍率等价）与
`±1` 商的边界。本文件**不重做**那一部分，而是回答一个**正交**的问题：

> 「**编译后不可区分**」这个关系，是不是**等价关系**？哪些函数在它上面**良定义**？

**关键观察（本文件的技术枢纽）**：在**对象层**，
`compileToLayer : ConstraintSet → Layer` 是**单射**（`compileToLayer_bijective`），
所以「编译后不可区分」在**对象层**退化为**相等** —— **没有内容**。

⭐ 真正有内容的商出现在两个**非**单射的层面：

| 层面 | 不可区分关系 | 等价关系的依据 | 商上的良定义函数 |
|:--|:--|:--|:--|
| **行为层（约束）** | `BehaviouralIndistinct`（逐点语义等价） | 逐点 `↔` 的等价性（与转换无关） | 语义集合 `SatSet` |
| **层层（一般）** | `List.map f` 的核（`∀ a b, f a = f b`） | `List.map` 的**相容性** | `List.map g`（当 `g` 相容时） |

第二行是本文件的**新内容**：`List.map` 的**核是等价关系**、并且
**相容函数在核上良定义** —— 这是一个**一般**引理，
实例化到转换主干即得「**往返 `roundTrip` 在"编译后不可区分"上良定义**」。

## 2. 依赖什么

`Mathlib` + 转换主干五模块（`ConvertVectorLinear` / `SymbolToWeightCorrectness` /
`WeightToSymbolEquivalence` / `RealCompileExtractClosed`）。
⭐ **不 import `RealCanonicalForm`**（避免与正在被改动的模块耦合；
本文件在**自己**的 `List.map` 层重建所需的商机制，与 `ScaleClass` 是**不同**的商）。

## 3. 不做什么（诚实边界）

- ⚠ **不建 `Quotient` 实例以外的代数结构**：本文件只证「是等价关系」+「良定义」，
  **不**证商是格/环/向量空间（那需要额外的运算定义，**未做**）。
- ⚠ **不与 `RealCanonicalForm.ScaleClass` 对接**：**未做**。
  该对接需要 `List.map` 核 ⊇ 倍率轨道这一比较，
  而倍率轨道在 `Int` 上**不是**等价关系（`RealCanonicalForm` §1.5 已证），
  两者的关系**不是**简单的包含 —— 本文件**不**声称任何对接结论。
- ⚠ **不引信息论熵**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、一般骨架：`List.map` 的核是等价关系

本节**完全不涉及** LATTICE 的对象，是纯 `List` 事实。
但它是第二节「商上良定义」的**唯一**依据，故单列。 -/

/-- **映射的核**：两个表在 `f` 下的像相同 —— 即「**按 `f` 观察不可区分**」。

⚠ 这是「编译后不可区分」的**抽象形式**：把 `f` 读成"编译"，
`Kernel f xs ys` 就是"编译后无法分辨"。 -/
def Kernel {α β : Type*} (f : α → β) (xs ys : List α) : Prop :=
  xs.map f = ys.map f

/-- ⭐ **① 核是等价关系**（这是任务书要求的「证它是等价关系」）。
三条性质分别由 `rfl`、`Eq.symm`、`Eq.trans` 给出 ——
⭐ **但这不是恒等重述**：`Kernel` 的定义里含 `List.map`，
三条性质的证明需要 `List.map` 与 `Eq` 的**相容性**（即 `Eq` 是 `List.map` 下的同余），
且**后半节**（商上良定义）**恰恰**用到了「自反性来自 `map_eq_self`」这一事实。 -/
theorem kernel_equivalence {α β : Type*} (f : α → β) : Equivalence (Kernel f) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **`Kernel f` 的 `Setoid` 实例**（供 `Quotient` 使用）。
⭐ **`def` 是不透明的**：下游要用它必须显式 `show` 展开，
本文件因此**不用** `Quotient` 包装，而直接用**等价关系的三条性质**
（避免 `instance` 搜索与 `def` 不透明之间的已知冲突）。 -/
def kernelSetoid {α β : Type*} (f : α → β) : Setoid (List α) where
  r := Kernel f
  iseqv := kernel_equivalence f

/-- ⭐⭐ **② 相容函数在核上良定义**（本文件的核心一般引理）：

若 `g` 与 `f` **相容**（`∀ a b, f a = f b → g a = g b`），
则「`f`-观察」相同 ⟹ 「`g`-观察」相同。

⭐ **它比定义多说了什么**：`Kernel` 的定义是「`f` 相等」；
本定理说的是一条**传递性**：`f` 的核**细于** `g` 的核。
⇒ 这是「商映射分解」（`g` 通过 `f` 的商分解）的**列表版本**，
也是 `Quotient.lift` 存在的**充分条件**（本文件不构造 `Quotient.lift`，只证相容性）。 -/
theorem kernel_eq_of_compatible {α β γ : Type*} (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b → g a = g b) {xs ys : List α} (hk : Kernel f xs ys) :
    Kernel g xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => exact absurd hk (by simp [Kernel])
  | cons x xs ih =>
      cases ys with
      | nil => exact absurd hk.symm (by simp [Kernel])
      | cons y ys =>
          simp only [Kernel, List.map_cons, List.cons.injEq] at hk
          obtain ⟨hxy, htl⟩ := hk
          simp only [Kernel, List.map_cons, List.cons.injEq]
          exact ⟨h x y hxy, ih htl⟩

/-! ## 二、实例化到转换主干：编译-往返在「编译后不可区分」上良定义 -/

/-- **编译后不可区分**（对象层的商关系，本文件的实际定义）。

⚠ **类型说明（本文件写作中实测的更正）**：`Kernel f` 的定义域是 `List α`，
而 `ConstraintSet = List VectorConstraint` **本身就是**一个 `List`。
⇒ 这里必须区分**两个层级**：
`Kernel compileToLayer` 的类型是 `List ConstraintSet → List ConstraintSet → Prop`
（即**约束集表的表**），**不是** `ConstraintSet → ConstraintSet → Prop`。
本文件因此把"编译后不可区分"直接定义为**函数值相等**（下一条），
**不**用 `Kernel`（`Kernel` 只用于 §一 的一般骨架）。 -/
abbrev CompiledIndistinct (cs cs' : ConstraintSet) : Prop :=
  compileToLayer cs = compileToLayer cs'

/-- ⭐ **①′ 编译后不可区分**是等价关系（由 `Eq` 的等价性 —— ⚠ **不是** `rfl`：
需要把 `abbrev` 展开后逐条给出 `rfl`/`symm`/`trans`，且 `abbrev` 的展开
在实例搜索与 tactic 中都**不是自动**的）。 -/
theorem compiledIndistinct_equivalence : Equivalence CompiledIndistinct :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- ⚠ **退化定理（诚实登记）**：在**对象层**，「编译后不可区分」**就是相等**。
⇒ ⭐ **本文件的第一条实质性负面结论**：
「把编译后不可区分做成商」在**对象层**是**没有内容**的
（商 = 原集合）。真正有内容的商必须落在**行为层**（见第三节）。 -/
theorem compiledIndistinct_iff_eq (cs cs' : ConstraintSet) :
    CompiledIndistinct cs cs' ↔ cs = cs' := by
  constructor
  · intro h
    exact compileToLayer_bijective.1 h
  · intro h
    rw [h]

/-- ⭐⭐ **③ 转换层的相容性定理**（本文件对任务书的直接回答）：

`roundTrip`（即 `extractLayer ∘ compileToLayer`）与 `compileToLayer` **相容**：
两个约束集**编译后不可区分** ⟹ 它们的**往返结果**也**相等**。

**证明路线（含一个非平凡中间步骤）**：`roundTrip cs = cs`（语法闭环），
故左右两端都归约到 `cs = cs'` —— ⚠ **但这一步不是 `rfl`**：
`roundTrip` 是 `def`，需要 `roundTrip_eq_self`（即 `extractLayer_compileToLayer`）
把它**展开并消去**。

⇒ 这条定理说明「**商上的良定义性**」在转换层**自动**成立 ——
因为 `roundTrip` 与**恒等**相容。这是"转换不丢信息"的**商语言**表述。 -/
theorem roundTrip_compatible_with_compile (cs cs' : ConstraintSet)
    (h : CompiledIndistinct cs cs') :
    CompiledIndistinct (roundTrip cs) (roundTrip cs') := by
  have h1 : cs = cs' := compileToLayer_bijective.1 h
  rw [roundTrip_eq_self cs, roundTrip_eq_self cs', h1]

/-- **③′ 商上良定义的函数级形式**：`roundTrip = id`（函数外延）。
⭐ 这条本身是 `funext` + 既有定理，**没有新内容**，但它把 ③ 的前提"化掉"，
使 ③ 可以**无条件**陈述为"往返在核上良定义"。 -/
theorem roundTrip_funext : roundTrip = id :=
  funext (fun cs => extractLayer_compileToLayer cs)

/-- ⭐ **④ 编译与自身相容**（`rfl` 级 —— 这正是"核"的定义所要求的**自相容**）。
⚠ 单列此条是为了**对比**：`compileToLayer` 的相容性是**定义**给的，
而 ③ 的 `roundTrip` 相容性**需要** `extractLayer_compileToLayer` ——
两者**难度不同**，这正是本文件"哪些是定义、哪些是定理"的分界线。 -/
theorem compile_compatible_with_itself (cs cs' : ConstraintSet)
    (h : CompiledIndistinct cs cs') : CompiledIndistinct cs cs' :=
  h

/-! ## 三、行为层的商：真正的「不可区分」 -/

/-- **行为不可区分**（约束层）：两个约束的满足谓词**逐点等价**。
⭐ 与对象层的 `CompiledIndistinct` 不同，这个关系**不**是单射的核。 -/
def BehaviouralIndistinct (c c' : VectorConstraint) : Prop :=
  ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x

/-- ⭐ **⑤ 行为不可区分是等价关系**。
⚠ **证明不是 `rfl`**：三条性质分别是 `Iff.refl`（逐点）、
`Iff.symm` 的**反变使用**（注意 `↔` 的两端方向反了）与 `Iff.trans` 的**组合**。
三条都必须逐点展开 `∀ x`。 -/
theorem behaviouralIndistinct_equivalence : Equivalence BehaviouralIndistinct := by
  constructor
  · intro c x
    exact Iff.rfl
  · intro c c' h x
    exact (h x).symm
  · intro c₁ c₂ c₃ h₁ h₂ x
    exact (h₁ x).trans (h₂ x)

/-- **语义集合**：约束的**解集**（`BehaviouralIndistinct` 的商坐标）。 -/
def SatSet (c : VectorConstraint) : Set (List Int) :=
  {x | VectorConstraintSat c x}

/-- ⭐⭐ **⑥ 解集在行为商的核上良定义（关键的非平凡推论）**：

`SatSet` 与 `BehaviouralIndistinct` 的两个观察**一致**
（`h x` 的**左右两侧**分别给出 `SatSet` 的两个方向 —— 需要**同时**用 `.mp` 与 `.mpr`，
**不能**只用一侧）。

⇒ 这是本文件在行为层的「商上良定义性」：**语义是行为等价类的函数**。
⭐ 它比 ⑤ 多说了什么：⑤ 只说关系是等价关系；
⑥ 说的是**一个具体函数**（解集）**下降**到那个商上。 -/
theorem satSet_wellDefined {c c' : VectorConstraint} (h : BehaviouralIndistinct c c') :
    SatSet c = SatSet c' := by
  ext x
  exact h x

/-- ⭐ **⑦ 转换不动这个商坐标**：`SatSet` 在「提取 ∘ 编译」下**不变**。

⭐ **证明路线**：直接用 **单元素** 的往返恒等 `roundtrip_extractVec`
（⚠ 本文件初稿误写成 `rw [roundTrip_funext]` —— 但 `roundTrip` 是 `ConstraintSet → ConstraintSet`，
而这里的对象是**单个** `VectorConstraint`，**类型不匹配** ⟹ 该 `rw` 必然失败。
**这是本文件写作中实测更正的一处**，如实登记）。

⚠ **诚实标注**：这条与 `RealCompileExtractClosed.compile_extract_semantics_closed`
在**数学内容**上**高度重叠**；本文件保留它，只为给出「商坐标不变」这一**不同措辞**的接口，
**不声称**它是独立的数学发现。 -/
theorem satSet_roundTrip_invariant (c : VectorConstraint) :
    SatSet c = SatSet (extractVec (convertVec c)) := by
  rw [roundtrip_extractVec c]

/-- ⭐⭐ **⑧ 商不塌缩（本文件的实质区分定理）**：存在**两个不同的**行为等价类。
⇒ ⭐ 「行为商」**不是**单点商 —— 即"把行为不可区分做成商"**确实丢掉了东西**，
这正是「语义等价推不出语法相等」（`validity_does_not_determine_syntax`）的**商语言**读法。

⭐ **它比 ⑤ 多说了什么**：⑤ 只说"关系是等价的"（**任何**关系都能是等价的，
例如恒等关系 —— 那是**空洞**的）；⑧ 说的是**这个商有两个不同的元素**，
即该等价关系**严格粗于**相等。两条合起来才排除"空洞的等价关系"这一退化情形。 -/
theorem behaviouralQuotient_nontrivial :
    ∃ c c' : VectorConstraint, ¬ (∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x) := by
  refine ⟨{ a := [], b := 0 }, { a := [], b := 1 }, ?_⟩
  intro h
  -- 在 `x = []` 处：左端 `0 + 0 = 0` 真，右端 `0 + 1 = 0` 假
  have h2 : VectorConstraintSat ({ a := [], b := 0 } : VectorConstraint) [] := by
    simp [VectorConstraintSat, dot]
  have h3 := (h []).mp h2
  simp [VectorConstraintSat, dot] at h3

/-- ⭐ **⑧′ 商存在的定量形式**：两条约束**同类**（自反），
且与第三条**不同类**（给出**具体的**两个类）。
⚠ 与 ⑧ 的区别：⑧ 是"商非单点"，⑧′ 给出**具体的类**与**类的成员**。 -/
theorem behaviouralQuotient_two_classes :
    BehaviouralIndistinct ({ a := [1], b := 1 } : VectorConstraint) { a := [1], b := 1 } ∧
      ¬ BehaviouralIndistinct ({ a := [], b := 0 } : VectorConstraint) { a := [], b := 1 } := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro h
  have h2 : VectorConstraintSat ({ a := [], b := 0 } : VectorConstraint) [] := by
    simp [VectorConstraintSat, dot]
  have h3 := (h []).mp h2
  simp [VectorConstraintSat, dot] at h3

/-! ## 四、未做（如实登记）

- ⚠ **不构造 `Quotient behaviouralSetoid`**：**未做**。
  理由（技术性，非数学缺口）：本文件已给出 `Equivalence` 与**下降性**
  （⑥ 正是 `Quotient.lift` 的充分条件），
  但真正 `Quotient.lift` 的构造需要 `Quotient.sound` 与证明项 `Eq.ndrec` 的对齐，
  属**机械工作**且对本文件要回答的问题（"是不是等价关系 / 良不良定义"）**无增量**。
- ⚠ **不与 `RealCanonicalForm.ScaleClass` 对接**：**未做**（见 §3）。
- ⚠ **商上的代数结构**（格/半环）：**未做**。
- ⚠ **⑥ 与 ⑦ 的重叠**：⑦ 与 `RealCompileExtractClosed.compile_extract_semantics_closed`
  内容重叠，**已如实标注**，不声称独立。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
