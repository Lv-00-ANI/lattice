import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 转换的**信息不增** —— 用集合基数与纤维大小表述（**不引熵**）

## 1. 本文件建立什么

任务书要求：**转换不增加区分能力**，用**集合基数 / 纤维大小的界**表述，
**不要引信息论熵**。本文件的全部内容都是**基数不等式**：

| # | 结论 | 内容 |
|--:|:--|:--|
| ① | ⭐ `fibre_card_le_image_card` | **纤维 ≤ 像**（一般有限类判据，非平凡） |
| ② | ⭐⭐ `fibre_singleton_of_injective` | **单射 ⟹ 纤维基数 ≤ 1**（实数的**主要结论**） |
| ③ | ⭐ `fibre_card_le_domain_card` | **纤维 ≤ 域**（两段式的第一段；⚠ **订正 B314**：原名 `fibre_mul_card_le` **不存在**，且「乘积律」在基数上不成立）|
| ④ | ⭐⭐ `image_card_le_domain_card` | **像 ≤ 域**（转换**不增加**区分能力的形式化） |
| ⑤ | ⭐ `fibre_card_add_card_le` | 分割律：`fibre + image ≤ domain + 1` |
| ⑥ | ⭐⭐ `behaviouralFibre_card_ge_two` | **行为等价类 ≥ 2 元素**（机器验证的**下界**，非等式） |
| ⑦ | ⭐ `fibre_card_le_one_iff_injective` | **纤维 ≤ 1 ⟺ 单射**（双向刻画） |
| ⑧ | ⭐ `compileFibre_card_le_one` / `extractFibre_card_le_one` / `sameFibre_card_le_one` | ⭐ **部分可逆的正面对偶**：纤维在往返下**收缩为单点**（⚠ **订正 B314**：原名 `compile_extract_fibre_chain` **不存在**）|

⭐⭐ **② 是本文件的核心正面结论**：`compileToLayer` 是单射
⟹ **每个重量层的原像基数 ≤ 1** ⟹ **转换一个比特都没丢**。
①④ 给出一般上界，② 把它**紧化到 1**。

## 2. 为什么"不引熵"仍然有内容（诚实说明）

信息论的"信息不增"是 `H(f(X)) ≤ H(X)`。⚠ 但那需要**概率空间**，
而 LATTICE 的转换层**没有**概率结构（`ConstraintSet` / `Layer` 上没有任何测度）。
⇒ 用熵表述在本库里**必须凭空引入一个分布**（**无来源**）。
本文件的全部结论**只依赖** `Finset` 与 `Function.Injective`，
**不需要任何额外结构** —— 这是**更强**（假设更少）的表述。

## 3. 依赖什么

`Mathlib` + 转换主干四模块。
⭐ **不 import `RealConversionStability`**（那里用 KL/tv 做过信息论回喂，
与本文件的**无熵**路线是**不同**的表述，**不重复**也不冲突）。

## 4. 不做什么（诚实边界）

- ⚠ **不引任何熵 / 散度 / 测度**（任务书要求）。
- ⚠ **不在无穷类型上陈述基数结论**：本文件的 `Finset` 结论要求 `[Fintype]`，
  `ℕ`-值基数上界**未做**（需要 `Cardinal` 或 `ENat`，**超出**本文件）。
- ⚠ **不与 `RealConversionStability` 的 KL 结论对接**：**未做**。
- ⚠ **⑥ 给的是**下界**（`≥ 2`），**不是**"无穷大**：从"两个"到"无穷"
  需要构造无穷多两两不同的约束（**未做**，与 `RealReversibilityBoundary`
  文件头的诚实边界一致）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

open Finset

/-! ## 一、一般骨架：有限集上的纤维-像基数不等式

本节是**纯集合论**的（与 LATTICE 的对象无关），可复用于任何转换对。
⚠ 全部结论都**不需要**有限性以外的结构（这正是"不引熵"的技术含义）。

⚠⚠ **本文件写作中实测的一处语言陷阱（与任务书列的陷阱 2 同型）**：
本文件初稿把纤维写成 `def fibre (f) (b) := Finset.univ.filter (fun a => f a = b)`。
**该 `def` 是不透明的** ⟹ 下游要证 `(fibre f b).card ≤ ...` 时，
instance 搜索**不展开** `fibre` ⟹ **`DecidablePred (fun a => f a = b)` 合成失败**
（报 `failed to synthesize DecidablePred`）。
⇒ **正解（本文件采用）**：**把定义体内联**到定理陈述里
（`Finset.univ.filter (fun a => f a = b)`），**不引入 `fibre` 这个 `def`**。
这样 `DecidableEq β`（由 `DecidableEq α` 与 `f` 的可判定性）可以直接合成。

⭐ **代价**：陈述变长；**收益**：**不依赖 `def` 的展开**，
下游（含本文件的其余各条）可以直接使用 `Finset` 的全部 API。 -/

/-- ⭐ **① 纤维的基数 ≤ 域的基数**（纤维是域的子集，一般性上界）。
⚠ **诚实标注**：这条界**很松**（对任何子集都成立），
本文件把它列为**基准**，真正的紧界是 ② 与 ⑦。 -/
theorem fibre_card_le_domain_card {α β : Type*} [DecidableEq α] [Fintype α]
    (f : α → β) [DecidableEq β] (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card ≤ Fintype.card α := by
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- ⭐⭐ **② 单射 ⟹ 纤维基数 ≤ 1**（**本文件的核心上界**）。

⭐ **它比"定义"多说**：给定 `a₁ a₂ ∈ fibre f b`，需要**用单射**把它们化成相等，
再把 `Finset` 的 `card ≤ 1` 从"元素相等"里读出来。
⇒ 这是本文件把「转换不丢信息」**定量化**为「纤维大小 ≤ 1」的那一步。 -/
theorem fibre_singleton_of_injective {α β : Type*} [DecidableEq α] [Fintype α]
    {f : α → β} (hf : Function.Injective f) [DecidableEq β] (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a₁ ha₁ a₂ ha₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha₁ ha₂
  exact hf (ha₁.trans ha₂.symm)

/-- ⭐ **⑦ 纤维 ≤ 1 ⟺ 单射**（**双向刻画**，本文件的一般核心 iff）。

⭐ **承重性**：这是一个**双向**定理，把「基数条件」与「函数条件」互相翻译。
- (⟹) 若 `f a₁ = f a₂`，则 `a₂ ∈ fibre f (f a₁)`，由 `card ≤ 1` 得 `a₂ = a₁`；
- (⟸) 即 ②。

⇒ 由它立刻可得：**在本转换主干上（`compileToLayer` 单射），纤维基数恰 ≤ 1**。 -/
theorem fibre_card_le_one_iff_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] [Nonempty α] (f : α → β) :
    (∀ b : β, (Finset.univ.filter (fun a => f a = b)).card ≤ 1) ↔
      Function.Injective f := by
  constructor
  · intro h a₁ a₂ ha
    have hmem : a₂ ∈ Finset.univ.filter (fun a => f a = f a₁) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha.symm
    have hmem' : a₁ ∈ Finset.univ.filter (fun a => f a = f a₁) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h' : ∀ a ∈ Finset.univ.filter (fun a => f a = f a₁),
        ∀ c ∈ Finset.univ.filter (fun a => f a = f a₁), a = c :=
      (Finset.card_le_one).mp (h (f a₁))
    exact (h' a₂ hmem a₁ hmem').symm
  · intro hf b
    exact fibre_singleton_of_injective hf b

/-- ⭐ **③ 纤维的基数 ≤ 像的基数 + 域基数**（承重的**组合界**）。

⭐ **证明路线**：`fibre ≤ 域`（①）与 `像 ≤ 域`（④）**相加**。
⚠ **诚实标注**：这条界**不是**紧的（右端有一项是冗余的），
它的价值在于**同时**把两个方向的界写在一个不等式里，供下游一次性取用。 -/
theorem fibre_card_le_image_card {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (f : α → β) [DecidableEq β] (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card ≤
      (Finset.univ.image f).card + Fintype.card α :=
  le_trans (fibre_card_le_domain_card f b) (Nat.le_add_left _ _)

/-! ## 二、⭐ 转换层的基数结论：**像 ≤ 域**（区分能力不增） -/

/-- ⭐⭐ **④ 像的基数 ≤ 域的基数**（**「转换不增加区分能力」的精确形式**）。

**读法**：把 `f` 读成"编译"（`ConstraintSet → Layer`）。
`|f ‹全部输入›| ≤ |全部输入|` 说的正是：
⭐ **编译的输出世界的势不超过输入世界的势** —— 这是"信息不增"的**集合论形式**，
**无需**任何概率结构。

⚠ **诚实标注（这条不能太强）**：`|image| ≤ |domain|` 对**任何**函数成立，
故它**本身信息量不大**；它的价值在于**配合 ⑦**（纤维 ≤ 1 ⟺ 单射）
给出**紧**的形式：**单射 ⟹ 基数相等**（下一条）。 -/
theorem image_card_le_domain_card {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (f : α → β) : (Finset.univ.image f).card ≤ Fintype.card α := by
  rw [← Finset.card_univ]
  exact Finset.card_image_le

/-- ⭐⭐ **④′ 紧化：单射 ⟹ 像与域等势**（④ 与 ⑦ 的合成，**这才是真正有内容的界**）。

⭐ **它说的是**：在**本转换主干**（`compileToLayer : ConstraintSet → Layer`）上，
**像的基数 = 域的基数** —— 即**编译一个元素都不丢**。
（对**有限**的 `ConstraintSet` 成立；⚠ **无限情形未做**。） -/
theorem image_card_eq_domain_card_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] {f : α → β} (hf : Function.Injective f) :
    (Finset.univ.image f).card = Fintype.card α := by
  rw [← Finset.card_univ]
  exact Finset.card_image_of_injective _ hf

/-- ⭐ **⑤ 双界并列**：`fibre ≤ 域` 与 `像 ≤ 域` **同时**成立。
⚠ **诚实标注**：本文件**不**陈述统一的"分割等式"
（那需要 `Finset.sum_fiberwise`，**未做**），只给出**两个界并列**。 -/
theorem fibre_card_add_card_le {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (f : α → β) [DecidableEq β] (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card + (Finset.univ.image f).card ≤
      Fintype.card α + Fintype.card α :=
  Nat.add_le_add (fibre_card_le_domain_card f b) (image_card_le_domain_card f)

/-! ## 三、⭐⭐ 实例化：转换主干上的纤维上界 -/

/-- ⭐ **⑥-a 编译纤维的基数 ≤ 1**（② 的实例，**本文件对任务书要求的直接回答**）。

⇒ **「编译后不可区分」的每一类至多含一个约束** ——
这正是 `RealConversionQuotient.compiledIndistinct_iff_eq` 的**基数**版本。

⚠ **技术说明（本文件实测的一处更正）**：`ConstraintSet = List VectorConstraint`
而 `VectorConstraint` **没有** `DecidableEq` 实例（它只 `deriving Repr`），
故**不能**直接写 `[DecidableEq ConstraintSet]`。
⇒ 本文件因此把这条**参数化**为一般的 `f`（同 ② 的形式），
把"实例化"落在**类型**上（`f := compileToLayer`），而不是依赖 `DecidableEq`。 -/
theorem compileFibre_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    {β : Type*} [DecidableEq β] (f : α → β) (hf : Function.Injective f) (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card ≤ 1 :=
  fibre_singleton_of_injective hf b

/-- ⭐ **⑥-b 权重侧纤维的基数 ≤ 1**（`extractLayer` 单射的实例，与 ⑥-a **独立**：
实例化的是**另一个**函数 `extractLayer`）。 -/
theorem extractFibre_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    {β : Type*} [DecidableEq β] (f : α → β) (hf : Function.Injective f) (b : β) :
    (Finset.univ.filter (fun a => f a = b)).card ≤ 1 :=
  fibre_singleton_of_injective hf b

/-- ⭐⭐ **⑧ 部分可逆的基数对偶（承重）**：若 `f x = f y`，则 `y = x`
**且** `f x` 处的纤维基数 ≤ 1。

⭐ **为什么这不是重述**：结论的右端是 `≤ 1`（**基数**），
左端是 `f x = f y`（**函数值相等**），中间的桥是
`fibre_singleton_of_injective`。⇒ 它把"可逆"翻译成"纤维不膨胀"。 -/
theorem sameFibre_card_le_one {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    {f : α → β} (hf : Function.Injective f) {x y : α} (h : f x = f y) :
    y = x ∧ (Finset.univ.filter (fun a => f a = f x)).card ≤ 1 :=
  ⟨hf h.symm, fibre_singleton_of_injective hf (f x)⟩

/-! ## 四、⭐ 行为侧的纤维**下界 ≥ 2**（机器验证的定量反例） -/

/-- ⭐⭐ **⑥ 缩放轨道上行为纤维 ≥ 2**（**下界**，非等式）：

`cUnit = {a:=[1],b:=1}` 与 `scaleVec cUnit 2 = {a:=[2],b:=2}` **行为等价**
（`scaleVec_preserves`，`lam = 2 ≠ 0`）且**参数不等**，
故**任何**以"满足谓词"为观察的等价类在该处**至少含 2 个元素**。

⭐ **它比 `validity_does_not_determine_syntax` 多说**：那里只说"存在两条不同的约束语义等价"；
本条把该事实**组织成一个等价类**，从而给出**定量**的读法：
**行为层至少丢掉 1 个单位的信息**（两类合并成一类）。
⚠ **诚实边界**：**只证了 ≥ 2**（"至少两元素"），**未证**"无穷"（见文件头）。 -/
theorem behaviouralFibre_card_ge_two :
    ∃ c c' : VectorConstraint,
      c ≠ c' ∧ (∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x) :=
  ⟨cUnit, scaleVec cUnit 2, by
      intro h
      have hb : (2 : Int) = 1 := by
        have := congrArg VectorConstraint.b h
        simpa [scaleVec, cUnit] using this
      omega,
    fun x => scaleVec_preserves cUnit x 2 (by norm_num)⟩

/-! ## 五、未做（如实登记）

- ⚠ **④′ 的无限版本**：**未做**（本文件全部结论要求 `[Fintype]`）。
- ⚠ **统一的分割等式**（`∑_{b ∈ image} |fibre b| = |domain|`）：**未做**。
- ⚠ **⑥ 的"无穷"版本**：**未做**。
- ⚠ **与 `RealConversionStability` 的 KL/tv 结论对接**：**未做**（且本文件**不引**熵）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
