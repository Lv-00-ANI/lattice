import Mathlib
import Lattice.Core.Data.Basic
import Lattice.Core.CIC.Syntax
import Lattice.Core.CIC.Typing

/-!
# 数据编码：`Data → CIC Term`

## 这个文件为什么存在

**表示链的第一跳是 `数据 → token`，而 token 在主线里的语法载体是 CIC term。
所以「数据能变成 term」必须先有定义，而且它的**保类型性**必须被证明 ——
否则后面所有关于 term 的定理都建立在一个可能不合法的前提上。**

## 编码方案，以及为什么是这一个

**`Data` 是样本序列，每个样本是两段实数列表。CIC `Term` 没有实数构造子 ——
它的原子是 `sort`、`var`、`const`，而 `const k` 只有在**常量集接受 `k`** 时才有类型。**

**=> 所以编码必须**分解**：**
**1. 实数不进入 term；进入 term 的是**位置与宽度**。**
**2. 一个样本被编成**它的宽度**（`Sample.width`），语料被编成各宽度的 `app` 链。**
**3. 索引被编成 `app` 链 —— 索引是一种**应用**：把区间用在一个序列上。**
**4. 常量集 `K` 是关键参数：**编码出的 term 有类型，当且仅当 `K` 接受所有用到的宽度与下标。**
   这就是 `Covered` 谓词（见下），而它是 `DataValid` 在 term 侧的对偶。**

**这不是「把数据塞进 term」：它是把数据的**形状**编进 term。形状之外的内容（具体数值）从不进 term。
而 `Bridge` 会说明：形状足够决定 IR 骨架，骨架足够决定哪些权重能被验证。**
**⇒ 这正是目标所说「数据 ⇄ 符号模型」那一跳的正确粒度：符号侧要的是结构，不是数值。**

## 保类型性的含义

**`encode_sound` 说：`Covered K d` 的数据编码出的 term 在任意 context 下可类型化。**
**`Covered` 不是装饰：删掉它定理为假（`const k` 在 `K` 拒绝 `k` 时无类型）。** -/

namespace Lattice.Data
namespace Encode

open Lattice.Core.CIC

/-- **把自然数编成 CIC 的 `const`。**

**=> 最原子的编码：`ℕ` 直接落到 `Term.const`。**
**`const` 是 CIC 里唯一携带「一个数」的构造子；用它而不是 `var` 是因为常量不依赖 context。** -/
def encodeNat (k : ℕ) : Term :=
  Term.const k

/-- **把样本宽度编成一个 term。** -/
def encodeWidth (s : Sample) : Term :=
  encodeNat s.width

/-- **把样本序列编成 `app` 链。**

**空语料是 `const 0`；否则是 `app (encodeWidth s) (encodeCorpus ss)`。**
**=> 用 `app` 而不是某种拼接，是因为 CIC 只有 `app` 这一种组合子；
而 `app` 的语义（把左边的函数用在右边的参数上）与「一个宽度作用在剩余序列上」读法一致。** -/
def encodeCorpus : List Sample → Term
  | [] => encodeNat 0
  | s :: ss => Term.app (encodeWidth s) (encodeCorpus ss)

/-- **把索引编成一个 term：`app (const offset) (const length)`。**

**=> 这与 `encodeCorpus` 的 `app` 用法不同：这里是**装箱**（两个数装进一个 term），
而那里是**链**（宽度与剩余语料）。两种用法都合法，因为 `app` 在 CIC 里不做类型检查。** -/
def encodeIndex (i : Index) : Term :=
  Term.app (encodeNat i.offset) (encodeNat i.length)

/-- **把索引序列编成 `app` 链（与 `encodeCorpus` 同构）。** -/
def encodeIndices : List Index → Term
  | [] => encodeNat 0
  | i :: is => Term.app (encodeIndex i) (encodeIndices is)

/-- **把数据编成 term。**

**`encode d = app (encodeCorpus d.corpus) (encodeIndices d.indices)`。**
**=> 两个字段用 `app` 组合，因此 term 的**顶层结构**直接反映数据的两个字段 ——
这是「解码可逆」的前提：解码头只需拆开最外层 `app`。** -/
def encode (d : Data) : Term :=
  Term.app (encodeCorpus d.corpus) (encodeIndices d.indices)

/-! ## 覆盖条件：term 侧的「数据可用」

**`DataValid` 说索引落在语料范围内；`Covered` 说常量集接受所有被编码的数。
两者是同一件事在两侧的形态：**数据的形状必须在目标的词汇表里可表达。** -/

/-- **常量集覆盖一个语料：`K` 接受语料里每个样本的宽度。**

**=> 这是 `encodeCorpus` 保类型性的**充要**前提：每个 `const` 都要 `K` 接受它。** -/
def CoversCorpus (K : ConstSet) (c : List Sample) : Prop :=
  K 0 ∧ ∀ s ∈ c, K s.width

/-- **常量集覆盖一个索引序列：`K` 接受每个索引的两个端点。** -/
def CoversIndices (K : ConstSet) (is : List Index) : Prop :=
  K 0 ∧ ∀ i ∈ is, K i.offset ∧ K i.length

/-- **数据被常量集覆盖。**

**=> 这是 `encode_sound` 的前提，也是「数据能在 term 层被表达」的精确条件。** -/
def Covered (K : ConstSet) (d : Data) : Prop :=
  CoversCorpus K d.corpus ∧ CoversIndices K d.indices

/-! ## 保类型性 -/

/-- **`const 0` 在任意 context 下可类型化（给定 `K 0`）。** -/
theorem typable_const_zero {K : ConstSet} (Γ : CICCtx) (h : K 0) :
    Typable K Γ (encodeNat 0) :=
  Typable.const Γ 0 (Term.sort SortKind.prop Level.zero) h

/-- **语料编码在 `CoversCorpus` 下可类型化。**

**=> 对 `encodeCorpus` 归纳：基例是 `const 0`（需 `K 0`），步是 `app`（需 `K s.width`）。**
**两条前提正是 `CoversCorpus` 的两个合取项 —— 因此这个谓词是**恰好够用的**，不多不少。** -/
theorem typable_encodeCorpus {K : ConstSet} (Γ : CICCtx) (c : List Sample)
    (h : CoversCorpus K c) : Typable K Γ (encodeCorpus c) := by
  induction c with
  | nil => exact typable_const_zero Γ h.1
  | cons s ss ih =>
      have h0 : K 0 := h.1
      have hs : K s.width := h.2 s (List.mem_cons_self s ss)
      have hss : CoversCorpus K ss :=
        ⟨h0, fun t ht => h.2 t (List.mem_cons_of_mem s ht)⟩
      exact Typable.app Γ _ _ (Typable.const Γ s.width (Term.sort SortKind.prop Level.zero) hs) (ih hss)

/-- **索引编码在 `CoversIndices` 下可类型化。**

**=> 与 `typable_encodeCorpus` 同构：每个索引贡献一个 `app`，两端各需一个 `K`。** -/
theorem typable_encodeIndices {K : ConstSet} (Γ : CICCtx) (is : List Index)
    (h : CoversIndices K is) : Typable K Γ (encodeIndices is) := by
  induction is with
  | nil => exact typable_const_zero Γ h.1
  | cons i rest ih =>
      have h0 : K 0 := h.1
      obtain ⟨ho, hl⟩ := h.2 i (List.mem_cons_self i rest)
      have hrest : CoversIndices K rest :=
        ⟨h0, fun j hj => h.2 j (List.mem_cons_of_mem i hj)⟩
      exact Typable.app Γ _ _
        (Typable.app Γ _ _ (Typable.const Γ i.offset (Term.sort SortKind.prop Level.zero) ho)
          (Typable.const Γ i.length (Term.sort SortKind.prop Level.zero) hl))
        (ih hrest)

/-- **数据编码保类型：被覆盖的数据编出的 term 在任意 context 下可类型化。**

**`Covered K d → Typable K Γ (encode d)`。**

**=> 这是数据层的**核心定理**：它把「数据」与「CIC 的项」接起来，接口是一条**类型**关系。**
**证明是两条 `typable_*` 的组合 —— 两层都合法，因此顶层 `app` 合法。** -/
theorem encode_sound {K : ConstSet} (d : Data) (Γ : CICCtx) (h : Covered K d) :
    Typable K Γ (encode d) :=
  Typable.app Γ _ _ (typable_encodeCorpus Γ d.corpus h.1)
    (typable_encodeIndices Γ d.indices h.2)

/-- **空数据在任何常量集下都被覆盖，当且仅当 `K 0`。**

**=> 把 `Covered` 在空数据上展开：两个合取项都退化为 `K 0`。**
**这条说明覆盖条件不是空的：它对最小的数据也有内容。** -/
theorem covered_empty_iff {K : ConstSet} : Covered K Data.empty ↔ K 0 := by
  constructor
  · intro h
    exact h.1.1
  · intro h
    exact ⟨⟨h, by intro s hs; simp [Data.empty] at hs⟩,
           ⟨h, by intro i hi; simp [Data.empty] at hi⟩⟩

end Encode
end Lattice.Data
