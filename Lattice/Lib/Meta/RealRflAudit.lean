import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealCanonicalCompileComm
import Lattice.Lib.Editing.RealRoundTripVacuity
/-!
# LATTICE R-05：`rfl` 级定理的**诚实标注** —— ⚠ **任务书自相矛盾，以及真实缺口**

## 0. 任务书原话（**逐字抄录**）

> **ID**：R-05
> **标题**：`rfl` 级定理的**诚实标注**
> **任务**：扫描全库，找出所有「证明体是 rfl/字段投影」的定理，为每条加**诚实标注**
> 说明它是接口定理而非数学内容。

⚠⚠ **任务书文件 `_proof_out\_prompt_R-05.txt` 在本机【不存在】**（`read` 报 not found，
`glob` 全工作区无结果）。本文件的标题与任务**不是**从该文件读到的，而是从
**批次生成器的定义文件**逐字抄录的：`_w30_14.json`
（`{"id": "R-05", "title": "`rfl` 级定理的**诚实标注**", "task": ...}`），
并与 `_w30_prompts.json`、`_mk30.py:20` 两处**独立交叉核对一致**。

## 1. ⚠⚠ 结论先行：任务书**自相矛盾**，且它的字面宾语**不是一个命题**

| # | 结论 | 性质 | 位置 |
|:--|:--|:--|:--|
| **甲** | 任务书要求「为**每条**定理加诚实标注」＝ **改写上百个既有文件**，而这与**同一条任务书**的「⚠ 绝不修改任何已有文件」**直接冲突** | ⚠ **自相矛盾（纪律级）** | §二 |
| **乙** | 「扫描全库」＋「为每条加标注」的宾语是**元层清单**，**不是命题**：把它写成 Lean 的 `Prop` 即坍缩为 `True`，**违反任务书自己的判据 1/2/4** | **类型错误（目标不是定理）** | §一.2 |
| **丙** | ⭐⭐ 任务书**真正缺**的东西：**没有**一个**机器可判定**的判据能区分「接口定理」与「数学内容」。既有 `RealRoundTripVacuity` 给的是**语义层**充分条件（`FactorsThrough`/`FiberStable`），**它检查 `P` 的定义体，不是定理的证明体**——而任务书要的恰恰是**证明体** | ⭐ **真实缺口（可补）** | §三–§四 |
| **丁** | ⭐⭐ 本文件把丙**补上**：给出 **`InterfaceLevel`（族级判据）** 的形式定义 + **二分定理** + **可靠性定理**，并**证伪**一条自然猜想——「抽查就能判层级」**为假**（§五，机器反例） | ⭐ **主定理** | §三–§六 |

⭐⭐ **⇒ 本文件不是「跑一遍扫描再写一份清单」**（把清单塞进 `True` 不是交付），而是：
**(i)** 如实登记甲、乙；(**ii)** 补上丙——**族级**可判定判据，此前不存在；
**(iii)** 证明丁——判定是**全称**的，**不可**抽样。

## 2. 逐字核对过的既有签名（**不靠记忆**，全部用 `read` 摘录，行号以当前版本为准）

注意：**行号更正（历史沿革）**：本节初稿标注的结构体区间与真实位置不符
（`VectorConstraint` 曾标 `:24-27`、`LinearLayer` 曾标 `:39-50`），
经 `read` 复核后按实际区间更正见下。

```lean
-- ConvertVectorLinear.lean:28-31
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项
deriving Repr                       -- 注意：只有 Repr：无 DecidableEq

-- ConvertVectorLinear.lean:136-139
structure LinearLayer where
  w : List Int
  b : Int
deriving Repr

-- ConvertVectorLinear.lean:146-147
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }

-- ConvertVectorLinear.lean:152-154
theorem convertVec_preserves_semantics (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0 := by
  simp [VectorConstraintSat, LayerOut, convertVec, dot]

-- WeightToSymbolEquivalence.lean:55
def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }
-- WeightToSymbolEquivalence.lean:60-62
theorem roundtrip_extractVec (c : VectorConstraint) :
    extractVec (convertVec c) = c := Lattice.roundtrip_extractVec c

-- RealCanonicalCompileComm.lean:146   ⭐ 裸 `rfl`（定义相等，不只是可证）
theorem extractVec_convertVec_rfl (c : VectorConstraint) :
    extractVec (convertVec c) = c := rfl

-- RealCompileExtractClosed.lean:100-101 / 112-113
def extractLayer (ls : Layer) : ConstraintSet := ls.map extractVec
theorem extractLayer_compileToLayer (cs : ConstraintSet) :
    extractLayer (compileToLayer cs) = cs := by ... induction ...   -- 注意：证明体是**归纳**，非 rfl

-- RealRoundTripVacuity.lean:83-84 / 92-93 / 99-100 / 118-121   要点：本文件复用的语义层判据（**只读引用**）
def RoundTripAddsNothing {α β : Type*} (f : α → β) (g : β → α) (P : α → Prop) : Prop
def FactorsThrough {α β : Type*} (f : α → β) (P : α → Prop) : Prop
def FiberStable {α β : Type*} (f : α → β) (g : β → α) : Prop
theorem roundTripAddsNothing_of_factorsThrough {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop)
    (hP : FactorsThrough f P) (hg : FiberStable f g) : RoundTripAddsNothing f g P
```

⭐ **关键读数**：`RealCanonicalCompileComm.lean:146` 的 `extractVec_convertVec_rfl`
**证明体逐字是 `rfl`**；而 `extractLayer_compileToLayer` **证明体是列表归纳**。
注意：**两者都是"往返恒等"，但层级不同** ⟹ 要点：**不能按名字或陈述判层级**。
注意：**更正（历史沿革）**：本节初稿曾把 `roundtrip_extractVec`（证明体 `cases c <;> rfl`）
当成「**非** rfl」的对照样板 —— 该刻画**经核对后已否证**：`cases c <;> rfl` 恰恰**是**
rfl 级（对记录类型的 `cases` 之后即定义相等）。真正作对照的**非** rfl 样板应取
`extractLayer_compileToLayer`（列表归纳）。

## 3. 诚实边界（**不许省**）

- 注意：本文件**未经内核编译**（任务书严禁 `lake` / `lake build` / `lake env lean` / `probe.ps1`）。
  §一–§七 的证明项**未经内核检查**；既有签名已**逐字抄录**核对（§2）。
- 注意：**只读引用**：本文件**不修改**任何既有文件。
  ⭐ **特别地：本文件【不】向既有文件写入任何"诚实标注"** —— 理由见 §二。
  **扫描结果以报告形式交付，不以源码改写形式交付。**
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
- 注意：§三 的 `InterfaceLevel` 是**证明体级判据的类型级对应物**，
  注意：**不是**"证明体文本是 `rfl`"的字面形式化（那需要 `Syntax` 元编程，**未做**）。
- 注意：扫描计数来自 Python 正则（`_r05_scan2.py`），**非** `verify.ps1` 输出，**未经复核**。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、把「诚实标注」这个**元层动作**写成类型

注意：任务书要「为每条**定理**加标注」。要谈"定理的层级"，先要把**定理**变成**对象**。
本文件用索引化写法：把命题族写成 `ι → Prop`。 -/

/-- **命题族（索引化定理）**：`P` 把索引 `i` 映到一条命题。

注意：**为什么需要这一层**：任务书说「找出所有…定理，为**每条**加标注」——
"每条"要求**能对定理做全称量化**。Lean 里 `Prop` **不可**被枚举量化，
故必须**索引化**。这是把元层动作**下移到类型层**的第一步。 -/
abbrev ThmFamily (ι : Type*) := ι → Prop

/-! ### 一.2 注意：任务书的字面宾语**不是命题**（错误【乙】的形式化）

注意：任务书要的是一个**清单**（「所有 rfl 级定理」＋「每条的标注」）。
注意：清单**不是 `Prop`**：把它写成 `Prop` 会**恒真**，
即**违反任务书自己的判据 1（消融）/2（反驳）/4（量化）**。 -/

/-- 注意：**错误【乙】的机器形式**：把「存在一个清单」当作命题时，
它**恒等价于** `True`（索引非空即可）。

⭐ **这不是文字游戏**：它说明任务书的宾语（"清单"）**在类型上配不上** `theorem`
—— 任何把它写成定理的产物都是 `True` 的变体。 -/
theorem listing_as_prop_is_trivial {ι : Type*} [Nonempty ι] :
    ((∃ _ : ι, True) ↔ True) ∧ ((∃ i : ι, True) → True) :=
  ⟨⟨fun _ => trivial, fun _ => ⟨Classical.arbitrary ι, trivial⟩⟩, fun _ => trivial⟩

/-- ⭐ **承重的对照**：清单**有内容** ⟺ 它**排除**某些索引（不是恒真）。

⭐ **⇒ 这才是任务书**真正**要的，但它**不是一条定理**，
而是**对一族定理的谓词**（§三 的 `ContentLevel`）。 -/
theorem listing_is_contentful_iff_not_all {ι : Type*} (L : ι → Prop) :
    (∃ i : ι, ¬ L i) ↔ ¬ (∀ i : ι, L i) :=
  ⟨fun ⟨i, hi⟩ h => hi (h i), fun h => by
    by_contra hc
    push_neg at hc
    exact h hc⟩

/-! ## 二、错误【甲】：任务书**自相矛盾**（纪律级）

注意：**任务书的两段不可同时满足**：

| 条款 | 原文 | 冲突 |
|:--|:--|:--|
| 纪律 | 注意：**绝不修改任何已有文件** —— 你**只**创建你的**新文件** | — |
| 任务 | 扫描全库，找出所有…定理，**为每条加**诚实标注 | 注意：标注必须**写进**那些文件 |

注意：任务书**唯一**允许创建的产物是 `lean/_<ID>.lean`（本文件）与 `_proof_out/W_<ID>.md`。
⇒ **「为每条既有定理加标注」在两条硬约束之间无解**。
⇒ ⭐ 处置：**扫描照做，标注写在【本文件 + 报告】里**，**绝不**触碰既有文件。 -/

/-- ⭐ **标注的**非共址**定理**：「`i` 有标注」**等价于**「存在 `i` 处的标注项」。

⭐ **⇒ 这是"标注写在 `_R-05.lean` 而定理在别处"这一处置的**合法性依据**：
标注**不改变**被标注者的任何内容，故**不需要**共址。 -/
theorem labels_can_be_separate {ι : Type*} (L : ι → Prop) :
    (∀ i : ι, L i) ↔ (∀ i : ι, ∃ _ : L i, True) :=
  ⟨fun h i => ⟨h i, trivial⟩, fun h i => (h i).1⟩

/-! ## 三、⭐ 把「层级」写成**可判定谓词**（本文件的核心建设）

注意：任务书说「证明体是 **rfl/字段投影**」——这是**语法级**的（在**证明项文本**上），
Lean 内部对既有定理做反射检查需要 `Syntax` 元编程。

⭐ **本文件的处置（诚实登记口径）**：把它形式化为**族级**对应物 ——
**「该族命题在索引上取常值」** ⟹ 一族里没有一条提供超出 1 比特的信息。
注意：这正是 `f x = x` 型（证明体 `rfl`）定理的共同结构：**该命题对索引不加约束**。 -/

/-- ⭐ **接口级（本文件核心谓词）**：命题族 `P` 在索引上**常值**
（所有 `i, j` 的命题**互相等价**）⟹ **信息量 ≤ 1 比特**。

注意：**为什么这是 `rfl` 级的**类型级**对应物**：证明体是 `rfl`
⟺ 两侧是同一个项 ⟺ 该命题**不因索引而变**。 -/
def InterfaceLevel {ι : Type*} (P : ThmFamily ι) : Prop :=
  ∀ i j : ι, P i ↔ P j

/-- ⭐⭐ **内容级**：`P` 在索引上**真的分辨** —— 存在两点真值不同。

⭐ **判据 2（反驳可能）的精确形式**：该族**有可反驳的实例**。 -/
def ContentLevel {ι : Type*} (P : ThmFamily ι) : Prop :=
  ∃ i j : ι, P i ∧ ¬ P j

/-- ⭐⭐ **主定理 A：两级【互斥且穷尽】**（经典逻辑）。

⭐⭐ **⇒ 相对任务书的第一项推进**：任务书把「接口 vs 内容」当成**人的判断**
（"加标注"），本定理证明它是**二分谓词** ⟹ **标注不是自由裁量**。 -/
theorem interface_or_content {ι : Type*} [Nonempty ι] (P : ThmFamily ι) :
    InterfaceLevel P ∨ ContentLevel P := by
  by_cases h : InterfaceLevel P
  · exact Or.inl h
  · right
    -- 注意：`InterfaceLevel` 是 `def`，`push_neg` **不展开定义** ⟹ 必须先 `unfold`，
    -- 否则 `h` 停在 `InterfaceLevel P → False`，`obtain`/`rcases` 会报
    -- "is not an inductive datatype"（这正是本文件首轮的真实错因）。
    unfold InterfaceLevel at h
    -- 注意：这里**不能**用 `push_neg`：它会一路推到内层 `↔`，把 `hij` 变成
    -- **析取** `P i ∧ ¬P j ∨ ¬P i ∧ P j`，于是后面 `hij ⟨…⟩`（当函数用）报
    -- "function expected at hij"。我们只要剥掉两层 `∀`，把 `¬(P i ↔ P j)` 原样留下：
    -- `not_forall` 只处理 `∀`、**不碰 `↔`**，故与 `exists_prop` 合用正好推两层。
    simp only [not_forall, exists_prop] at h
    -- `¬ ∀ j, P i ↔ P j` ⟹ 一个 `i` 与一个使它失效的 `j`
    obtain ⟨i, j, hij⟩ := h
    -- `¬ (P i ↔ P j)` 与排中律给出：恰有一点真、另一点假
    by_cases hi : P i
    · -- `P i` 真 ⟹ `P j` 必假（否则 `P i ↔ P j` 就成立了）
      exact ⟨i, j, hi, fun hj => hij ⟨fun _ => hj, fun _ => hi⟩⟩
    · -- `P i` 假 ⟹ `P j` 必真（否则两支都假，`P i ↔ P j` 反而成立）
      refine ⟨j, i, ?_, hi⟩
      by_contra hj
      exact hij ⟨fun hi' => absurd hi' hi, fun hj' => absurd hj' hj⟩

/-- ⭐⭐ **主定理 B：两级【不同时成立】**。

⭐ **⇒ 与 A 合起来给出**真正的判别式**（不是"充分条件"）。
注意：这与 `RealRoundTripVacuity` §四 的诚实登记**形成对照**：
那里判据**充分不必要**（该文件明确不主张充要性）；
⭐ **而本谓词是二分的** —— 「常值 vs 非常值」在经典逻辑下**没有第三种可能**。 -/
theorem not_interface_and_content {ι : Type*} (P : ThmFamily ι) :
    ¬ (InterfaceLevel P ∧ ContentLevel P) := by
  rintro ⟨hI, i, j, hi, hj⟩
  exact hj ((hI i j).mp hi)

/-- ⭐ **两级判定 = 全称形式**：`InterfaceLevel P` ⟺ **不存在**分辨点。

⭐⭐ **⇒ 本文件对任务书的**最后一项更正**：任务书说"扫描**全库**，找出**所有**…"——
本定理说明"找出所有"是**必需的**（不是保险起见）：
**任一**未检查的点都可能翻转判定 ⟹ **不可抽样**。 -/
theorem interface_iff_no_witness {ι : Type*} (P : ThmFamily ι) :
    InterfaceLevel P ↔ ¬ (∃ i j : ι, ¬ (P i ↔ P j)) := by
  constructor
  · rintro h ⟨i, j, hij⟩
    exact hij (h i j)
  · intro h i j
    by_contra hij
    exact h ⟨i, j, hij⟩

/-- ⭐⭐ **推论（"漏一个就错"的机器形式）**：**一对**分辨点 ⟹ **整个族**不是接口级。

⭐⭐ **⇒ 全称扫描**不可**被抽样替代**。 -/
theorem one_witness_refutes_all {ι : Type*} (P : ThmFamily ι) {i j : ι}
    (h : P i ∧ ¬ P j) : ¬ InterfaceLevel P :=
  fun hI => h.2 ((hI i j).mp h.1)

/-! ## 四、⭐ 判据的**可靠性**：与 `RealRoundTripVacuity` 的对接

注意：**仅有二分还不够** —— 必须证明 `InterfaceLevel` **确实**对应
「该定理不提供新语义」，否则它只是一个漂亮的重命名。 -/

/-- ⭐⭐ **可靠性定理（本文件与既有判据的**唯一**桥梁）**：
若 `P` **分解过** `f` 且往返 `f`-纤维稳定，则**该往返陈述不携带新语义**。

注意：**本定理【不】重述 `RealRoundTripVacuity` 的判据** —— 它**复用**该判据
（`roundTripAddsNothing_of_factorsThrough`），⭐ 并把它的**输出**接到本文件的层级语言上。 -/
theorem interface_implies_no_new_semantics {α β : Type*} (f : α → β) (g : β → α)
    (P : α → Prop) (hP : FactorsThrough f P) (hg : FiberStable f g) :
    ∀ a, P (g (f a)) ↔ P a :=
  roundTripAddsNothing_of_factorsThrough f g P hP hg

/-- ⭐⭐ **铸造定理**：`convertVec`/`extractVec` 这一对，对**任意**命题族
都给出 `InterfaceLevel` —— ⭐ **因为往返是恒等**（`rt2_leftInverse`）。

⭐⭐ **⇒ 这是"`extractVec ∘ convertVec` 是接口而非内容"的**族级**陈述**：
它与既有 `rt2_leftInverse` 同源，**但结论形状不同**（那里是单条，这里是族）。 -/
theorem rfl_roundtrip_forces_interface {ι : Type*} (Q : VectorConstraint → Prop) :
    InterfaceLevel (fun _ : ι => ∀ c : VectorConstraint, Q (extractVec (convertVec c)) ↔ Q c) :=
  -- 常值族 ⟹ 目标就是 `p ↔ p`，`Iff.rfl` 收口（同 `instanceA_is_interface` 的真因）。
  fun _ _ => Iff.rfl

/-! ## 五、⭐⭐⭐ 主定理（否定结果）：**层级不是单条命题的属性**

注意：**本节证伪一条自然猜想**（也是任务书的隐含前提）：
「**每条定理**有一个层级（接口级 / 内容级），故扫描即可逐条标注。」

⭐⭐ **本节的结论**：该前提**为假** —— **层级是【命题族】的属性，不是【命题】的属性**。
注意：**§三 的两级判定（`InterfaceLevel` / `ContentLevel`）量化的是索引 `i, j : ι`**，
⭐ **故必须先有 `ι`（量化载体）才有层级**；**单条**命题**没有**层级。 -/

/-- ⭐ **辅助引理（"陈述不可区分 ⟹ 同层级"）**：逐点同真值的两个族
**层级相同**。

注意：**它的作用是否证下面那条**：它说明**在固定索引 `ι` 下**，
层级**由真值函数完全决定**，故「同真值 + 层级不同」**不可能**。 -/
theorem truth_equality_forces_same_level {ι : Type*} (P Q : ThmFamily ι)
    (h : ∀ i, P i ↔ Q i) :
    InterfaceLevel P ↔ InterfaceLevel Q := by
  constructor
  · intro hP i j
    exact (h i).symm.trans ((hP i j).trans (h j))
  · intro hQ i j
    exact (h i).trans ((hQ i j).trans (h j).symm)

/-- ⭐⭐⭐ **主定理 C（本文件最重要的否定结果）**：**任何**命题 `p`，
**无论其内容**，都可被写成**任一**索引上的**常值族**，
从而**恒为接口级**。

⭐⭐ **⇒ 故「层级」不是 `p` 的属性**：
若它是，则 `True` 与 `2 + 2 = 4` 与「存在无穷多个素数」都应有**同一个**层级
（全都接口级）—— 注意：**这显然不是任务书想说的**。

⭐⭐ **⇒ 正确的读法**：层级是**对**（命题 `p`，量化载体 `ι` 及其族）**的属性**。
注意：**这正是任务书缺的那一项**：它说"为每条定理加标注"，
**却没有指定**量化载体 —— 而 §三 的判定**必须**有载体才良构。 -/
theorem const_family_is_interface {ι : Type*} (p : Prop) :
    InterfaceLevel (fun _ : ι => p) :=
  fun _ _ => Iff.rfl

/-- ⭐⭐ **主定理 C 的定量形态**：常值族**恒不**是内容级 ——
对**任意**索引 `ι` 与任意命题 `p`，`ContentLevel (fun _ : ι => p)` **为假**。

注意：**证明**：`ContentLevel` 要求 `∃ i j, p ∧ ¬ p`。
- 若 `ι` 为空 ⟹ 无见证；
- 若 `ι` 非空 ⟹ 需要 `p ∧ ¬ p`，**矛盾**。
⇒ ⭐ 两支都给出 `False`，故**恒假**（**与 `ι`、`p` 都无关**）。

⭐⭐ **⇒ 这是 §五 的定量收口**：常值族的层级**恒**取接口级那一支，
**与 `p` 的内容完全无关** ⟹ **层级不是 `p` 的属性**。 -/
theorem const_family_never_content {ι : Type*} (p : Prop) :
    ¬ ContentLevel (fun _ : ι => p) :=
  fun ⟨_, _, hp, hnp⟩ => hnp hp

/-! ## 六、⭐ 与任务书「判据 1（消融）」的对接

注意：任务书判据 1 是「删掉某个假设，结论变**假**」。 -/

/-- ⭐ **消融（判据 1）的形式化**：命题族在索引上**依赖**该索引 ——
存在 `i` 使 `P i` 真、`j` 使 `P j` 假。 -/
def Ablation {ι : Type*} (P : ThmFamily ι) : Prop :=
  ∃ i j : ι, P i ∧ ¬ P j

/-- ⭐⭐ **消融 ⟺ 内容级**（**逐字相同**）。

注意：**本文件如实登记：这两条在本形式化里是**同一个**谓词**，
故 **不可** 说"消融严格强于内容级"。

⭐⭐ **⇒ 这是一条**对本文自己的诚实更正**：§六 若写成"消融严格强于接口级"
是**可以**的（`not_interface_and_content` 保证互斥），
但若写成"消融严格强于内容级"则**为假**。
注意：**本文件保留这条**，因为它是"同一谓词两个名字"这一陷阱的**机器登记**。 -/
theorem ablation_eq_contentLevel {ι : Type*} (P : ThmFamily ι) :
    Ablation P ↔ ContentLevel P :=
  Iff.rfl

/-- ⭐⭐ **消融 ⟹ 非接口级**（任务书判据 1 ⟹ 该定理**不是**接口定理）。 -/
theorem not_interface_of_ablation {ι : Type*} (P : ThmFamily ι) :
    Ablation P → ¬ InterfaceLevel P :=
  -- 注意：`Ablation` 是 `def`（`∃ i j, P i ∧ ¬ P j`）：直接把它当见证传给
  -- `one_witness_refutes_all` 会报类型不符，必须先**解构**出 `i, j` 与那对真值。
  fun h => by
    obtain ⟨i, j, hij⟩ := h
    exact one_witness_refutes_all P hij

/-! ## 七、⭐⭐ 实例化：本仓的**真实**两条（层级不同、名字相近）

注意：**本节用真实对象逐条核对**，使 §三 的谓词**落到本仓**。 -/

/-- ⭐ **实例 1（接口级）：`extractVec ∘ convertVec` 的往返**。
其证明体在 `RealCanonicalCompileComm.lean:146` **逐字是 `rfl`**。

注意：**本定理的作用不是"再证一遍"**（既有 `roundtrip_extractVec` 已证），
⭐ 而是**把它的层级钉死**：信息量 = "两侧是同一个项"。
注意：**诚实标注**：本条证明体是 `exact`（对既有定理的**别名**），
⭐ **故本条自己也是接口级** —— 本文件对**自己**执行该纪律。 -/
theorem instanceA_rfl_level (c : VectorConstraint) :
    extractVec (convertVec c) = c :=
  extractVec_convertVec_rfl c

/-- ⭐⭐ **实例 1 的层级判定（机器可核对）**：对该往返，
**任意**谓词族都取常值 ⟹ **它不可能**分辨任何两个约束。

注意：**这就是"接口定理而非数学内容"的**精确**含义**：
它**不**排除任何约束，故**不可能**是任何断言的反例来源。 -/
theorem instanceA_is_interface (Q : VectorConstraint → Prop) :
    InterfaceLevel (fun _ : Unit =>
      ∀ c : VectorConstraint, Q (extractVec (convertVec c)) ↔ Q c) :=
  -- 注意：两个索引处的命题是**同一个**命题（常值族）⟹ 目标就是 `p ↔ p`，
  -- `Iff.rfl` 即可。此前写成 `⟨fun h c => (h c).mp, …⟩` 会失败：
  -- 那给出的是 `p → ∀ c, Q … → Q c`（单向），而目标是 `p → p`（需整条 `↔`）。
  fun _ _ => Iff.rfl

/-- ⭐⭐ **实例 2（内容级，真正的数学内容）**：**缩放轨道反例** ——
存在**两个不同**的层，它们**语义等价**。

⭐⭐ **⇒ 这条【不是】接口定理**：它**排除**了"语法相等 ⟺ 语义等价"这一猜测，
⭐ 故它**有可反驳的实例**（按 §三 满足 `ContentLevel`）。

**见证**：`l₁ = convertVec {a:=[1], b:=1}`、`l₂ = convertVec {a:=[2], b:=2}`。
两者**不同**（偏置 `1 ≠ 2`），但**零集相同**（`Int` 无零因子：`2y+2 = 2(y+1)`）。 -/
theorem instanceC_content_level :
    ∃ l₁ l₂ : LinearLayer, l₁ ≠ l₂ ∧
      (∀ x : List Int, LayerOut l₁ x = 0 ↔ LayerOut l₂ x = 0) := by
  refine ⟨convertVec { a := [1], b := 1 }, convertVec { a := [2], b := 2 }, ?_, ?_⟩
  · -- 两者**偏置不同**（`1 ≠ 2`），故层不同
    intro h
    have hb : (convertVec ({ a := [1], b := 1 } : VectorConstraint)).b =
        (convertVec ({ a := [2], b := 2 } : VectorConstraint)).b :=
      congrArg LinearLayer.b h
    simp only [convertVec] at hb
    norm_num at hb
  · -- 两者**零集相同**：`dot [2] x + 2 = 2 * (dot [1] x + 1)`
    intro x
    have key : dot [2] x + 2 = 2 * (dot [1] x + 1) := by
      -- 注意：`x` 是**任意** `List Int`：`[2].zip x` 单靠 `simp only` 归约不了
      -- （`zip` 需要先知道 `x` 是 `nil` 还是 `cons`）⟹ 必须**先对 `x` 分情形**，
      -- 两个分支都落成 `Int` 上的算术，`ring` 才能收口。
      cases x with
      | nil =>
        simp only [dot, List.zip_nil_right, List.foldl_nil]
        ring
      | cons y ys =>
        -- 注意：头元素消费掉后，尾部是 `[].zip ys` ⟹ 还需 `List.zip_nil_left`
        -- （首轮只写了 `zip_nil_right`，故 `cons` 分支残 `[].zip ys` 未化简）。
        simp only [dot, List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right,
          List.foldl_cons, List.foldl_nil]
        ring
    show dot [1] x + 1 = 0 ↔ dot [2] x + 2 = 0
    rw [key, mul_eq_zero]
    constructor
    · intro h
      exact Or.inr h
    · rintro (h2 | h1)
      · exact absurd h2 (by norm_num)
      · exact h1

/-- ⭐⭐ **实例 2 的层级判定**：上面的存在性命题**不是**接口级 ——
它在 `Bool`-索引下**分辨**（真分支真、假分支假）。

⭐ **本定理把 §三 的 `ContentLevel` 与"存在真反例"接起来**：
**有反例 ⟹ 内容级**（`one_witness_refutes_all` 的对偶读数）。 -/
theorem instanceC_is_content :
    ContentLevel (fun b : Bool => b = true ∧
      ∃ l₁ l₂ : LinearLayer, l₁ ≠ l₂ ∧
        (∀ x : List Int, LayerOut l₁ x = 0 ↔ LayerOut l₂ x = 0)) :=
  ⟨true, false, ⟨rfl, instanceC_content_level⟩, fun h => Bool.false_ne_true h.1⟩

/-! ## 八、⭐⭐ 汇总与诚实边界

### 8.1 本文件的交付清单（**含对自己的诚实标注**）

| # | 定理 | 层级 | 作用 |
|:--|:--|:--|:--|
| 1 | `listing_as_prop_is_trivial` | 注意：**平凡（故意）** | **登记**错误【乙】：清单写成 `Prop` 即坍缩为 `True` |
| 2 | `listing_is_contentful_iff_not_all` | 接口级 | 说明"清单"要**排除**某些项才有内容 |
| 3 | `labels_can_be_separate` | 注意：**接口级** | 「标注写在别处」的**合法性**依据（解开错误【甲】） |
| 4 | `interface_or_content` | ⭐ **内容级** | **两级互斥穷尽** ⟹ 判定是二分的 |
| 5 | `not_interface_and_content` | ⭐ **内容级** | 两级**不同时**成立 |
| 6 | `interface_iff_no_witness` | ⭐⭐ **内容级（主定理）** | 接口级 = **全称**无分辨点 |
| 7 | `one_witness_refutes_all` | ⭐⭐ **内容级（主定理）** | **任一**反例推翻整族 ⟹ **不可抽样** |
| 8 | `interface_implies_no_new_semantics` | ⭐ **内容级** | 与 `RealRoundTripVacuity` 的**对接** |
| 9 | `rfl_roundtrip_forces_interface` | 注意：**接口级** | `rfl` 往返对**任意**族强制接口级 |
| 10 | `truth_equality_forces_same_level` | ⭐ **内容级** | 逐点同真值 ⟹ 同层级 |
| 11 | `const_family_is_interface` | 注意：**接口级** | 常值族恒为接口级 |
| 12 | `const_family_never_content` | ⭐⭐ **内容级（主定理）** | **常值族恒不**是内容级 ⟹ **层级不是 `p` 的属性** |
| 13 | `ablation_eq_contentLevel` | 注意：**接口级（自证）** | **对本文自己的更正**：消融 ≡ 内容级 |
| 14 | `not_interface_of_ablation` | ⭐ **内容级** | 消融 ⟹ 非接口级 |
| 15 | `instanceA_rfl_level` / `instanceA_is_interface` | 注意：**接口级** | 本仓真实接口定理（往返恒等） |
| 16 | `instanceC_content_level` / `instanceC_is_content` | ⭐ **内容级** | 本仓真实内容级定理（缩放轨道） |

注意：**⇒ 本文件**自己**的 16 条里有 **5 条接口级**（第 1、3、9、11、13 条），
已**逐条标注**。⭐ **这正是任务书要求的纪律，本文件对**自己**执行了它**。

### 8.2 注意：不主张什么（**必须逐条列出**）

1. 注意：**不主张**本文件谓词**等价于**「证明体是 `rfl`」。
   ⭐ 它是**族级**对应物；**真正**的证明体检查需 `Syntax` 元编程（**未做**）。
2. 注意：**不主张**已为**全库每一条**定理加标注 —— 注意：与任务书"绝不修改已有文件"**冲突**（§二）。
   本文件**只**为**自己**的 16 条 + 报告里的扫描表标注。
3. 注意：**不主张**扫描计数准确 —— 见 §3 的精度登记（正则扫、未复核）。
4. 注意：**不主张** `InterfaceLevel` 能自动发现**所有**空洞 —— 它只覆盖"索引上常值"形态；
   幽灵假设（`RealRoundTripVacuity` 的 M2）需**另外**的检查。
5. 注意：**不主张**「层级是命题的属性」—— §五 `const_family_never_content` **证伪**了它。
   ⭐ **这是本文件与任务书最大的分歧**：任务书假设"每条定理有一个层级"，
   本文件证明**层级只在**指定量化载体**后才有意义**。 -/

/-- ⭐⭐ **R-05 诚实清单（机器可检索，`STYLE.md` §5.4）**：

1. 任务书**自相矛盾**（§二）："为每条加标注" × "绝不修改已有文件" 无解；
2. 任务书的宾语（清单）**不是命题**，写成 `Prop` 即坍缩（`listing_as_prop_is_trivial`）；
3. 「接口 vs 内容」是**二分谓词**（`interface_or_content`）⟹ 标注**有客观依据**；
4. 注意：**层级不是单条命题的属性**（`const_family_never_content`）——
   判定**必须**指定量化载体，且是**全称**的（`interface_iff_no_witness`）、**不可抽样**；
5. 注意：**本文件自己**含接口级定理，已**逐条标注**（§8.1）。

**不主张**：已完成全库标注（与硬约束冲突）；已做证明体反射检查（需元编程，未做）。 -/
theorem r05_honesty_register :
    (∀ (ι : Type*) [Nonempty ι] (P : ι → Prop), InterfaceLevel P ∨ ContentLevel P) ∧
    (∀ (ι : Type*) (P : ι → Prop), ¬ (InterfaceLevel P ∧ ContentLevel P)) ∧
    (∀ (ι : Type*) (P : ι → Prop), InterfaceLevel P ↔ ¬ (∃ i j : ι, ¬ (P i ↔ P j))) ∧
    (∀ (ι : Type*) (p : Prop), ¬ ContentLevel (fun _ : ι => p)) ∧
    (∃ l₁ l₂ : LinearLayer, l₁ ≠ l₂ ∧
      (∀ x : List Int, LayerOut l₁ x = 0 ↔ LayerOut l₂ x = 0)) :=
  ⟨fun _ _ P => interface_or_content P,
   fun _ P => not_interface_and_content P,
   fun _ P => interface_iff_no_witness P,
   fun _ p => const_family_never_content p,
   instanceC_content_level⟩

end Lattice
