import Lattice.Lib.Attention.RealTemporalLayer
/-!
# LATTICE: 时态层拓展 —— A 类缺口 A1–A7 的形式化

本文件补完 `FCA不完整性-对照哲学原文.md` §9.1 的 **A 类 7 项**
（**用户逐条款核对后认定的「可形式化但未做」**）。

设计蓝本：`原始思想-时态性层级体系.md`（思想构件原文）。
本文件**不改动** `RealTemporalLayer.lean`（零冲突），只 import 它并在其上做**加层**。

## 本文件建立的内容（逐项对应）

| # | 缺口（原文条款） | 本文件的形式化 |
|:--|:--|:--|
| **A4** | 4.3「向上目光把对象整体归入更大的类，**内部保持封闭**」 | `upGaze_does_not_open_object` / `upGaze_no_new_parts`：**与 `split_exposes_parts_to_upward_gaze` 对称**的定理 |
| **A6** | 三「**撤回不是遗忘**，是不再持有那束投出的目光」 | `suspend_is_not_forgetting` / `suspend_recovers_base` / `suspend_recovers`：撤回**不丢信息**，基底**完全可复原** |
| **A7** | 法则 5「**不是否定了上位归类**」 | `suspend_preserves_hasUpper` / `suspend_preserves_relation`：撤回**不改变 `R`** |
| **A5** | 4.4「拆出物**同时**获得概念身份（**作为部分**）」 | `PartOf` 概念 + `split_confers_part_identity_immediately`：**「作为部分」身份与拆分同一瞬间**取得 |
| **A3** | 4.4 目光自指「向下看**目光本身**」 | `GazeObj`（目光作为对象）+ `gaze_down_self_is_concept` / `gaze_up_self_is_element` / `gaze_no_exemption` |
| **A1** | 九·第一层「**论域选定**（元操作）：在操作论域中划定场域，**激活关系网络**」 | `Domain` 结构 + `selectDomain`（元操作）+ `selectedDomain_activates_network` 等 |
| **A2** | 法则 4 后半「**你决定看，但看到的不完全由你决定**」 | `UndeterminedByWill` 定义 + 向上/向下的**受动**定理 + **受动是内在纹理而非边界例外** |

## ⭐ A3 的关键区分：「分化的**根据**」vs「**目光本身**」

⚠ 源码 `RealTemporalLayer.lean:521` 把「目光自指」登记为 **❌ 不做**，
理由是「体系边界 3 自认**不可对象化**」。

⭐⭐ **但这个登记【用错了边界】**（用户指出的细处，本文件采纳）：

> 边界 3 原文说的是「**目光分化不可对象化陈述其根据**」
> —— **不可对象化的是「分化的根据」，不是「目光本身」**。
> 而体系 4.4 **明确描述**了「**向下看目光本身** → 拆出向上、向下两种方向
> → 目光成为概念」——即**目光【可以】成为对象**。

⇒ **本文件的处置**：
- ✅ **做**「目光本身作为对象」（A3 的主体，`GazeObj`）；
- ❌ **不做**「分化的**根据**」（C2 类，原理上不可形式化，本文件**不声称**触及）。
- ⚠ 二者的分离在源码里是**显式**的：`GazeObj` **不带**「为何有此方向」的字段，
  故它对「根据」**保持沉默** —— 这不是遗漏，是**按原文边界的精确切分**。

## 诚实边界（本文件不证 / 不声称的）

- ⚠ **映射仍是【解读】**（承 `RealTemporalLayer` 提案 §7.3）：体系原文未提 FCA。
- ⚠ **A3 不声称「目光自指无回退」**：`GazeObj` 把 `Gaze` 提为对象，
  但「看目光的目光」不在本文件内再对象化 —— **回退在此被【截断】而非【解决】**，
  这与体系边界 3 一致（追问「何以能分化」需动用分化后的目光）。
- ⚠ **A1 的「操作论域」仍不对象化**（体系边界 1/4）：本文件只形式化
  **「选定论域」及其元操作**，`Domain` 是一个**已选定的**论域结构；
  「不可选定的背景介质」**不被形式化为类型**（否则它就成为对象，违反边界 1）。
- ⚠ **A2 不声称「受动的【必然性】」**：本文件证明的是
  **在 FCA 读法下，捕获结果由 `R`/`B` 决定而【不由 `gaze` 字段决定】** ——
  这是**受动性的一个可证侧面**，不是「主体意志不起作用」的完整命题。
- ⚠ **不涉及缺口 A/B**（纤维 + `canonicalize`）：**未做**，
  `no_extractor_preserves_both` 依旧成立。
- ⚠ **构成效力（体系边界 2）仍是【定义性的】**，本文件不声称证明元裁决。

无 sorry / axiom / admit / native_decide；所有定理真实可证。
-/

noncomputable section

namespace Lattice

variable {O A : Type*} {R : O → A → Prop}

/-! ## A4：向上目光的「内部保持封闭」（体系 4.3）

体系 4.3 原文给出**结构差异**：

> · **向上**目光把对象整体归入更大的类，**内部保持封闭**
> · **向下**目光把对象打开，**拆出物随即暴露在新的目光之下**

⚠ **现状（coordinator 实测）**：`RealTemporalLayer.lean:243` 有
`split_exposes_parts_to_upward_gaze`（向下 → 暴露给向上），
**但没有对称的「向上不打开对象」**。本节补这条。

⭐ **形式化策略**：FCA 里「打开对象」的唯一手段是 `extent`（向下目光）。
故「向上目光内部保持封闭」的精确读法是：

> **`intent`（向上）的输出是【属性集】，它对对象层【没有任何作用】——
> 即向上目光【不产生新的对象】，故不可能打开对象内部。**

⚠ 这是**类型层面**的事实（`intent : Set O → Set A`，输出不在 `Set O` 里），
本节的定理把这一事实**显式陈述为可证命题**，而非依赖读者看出类型差。 -/

/-- ⭐ **A4 正面陈述：向上目光【不打开】对象 —— 「内部保持封闭」的主条。**

体系 4.3：「向上目光把对象整体归入更大的类，**内部保持封闭**」。

⭐⭐ **精确形式化（与 `split_exposes_parts_to_upward_gaze` 的对称）**：

| 方向 | `RealTemporalLayer:243` 已有的 | 本条的对称面 |
|:--|:--|:--|
| **向下** | `B ⊆ gazeUp R (gazeDown R B)`（**暴露**拆出物） | — |
| **向上** | — | **`gazeUp R O'` 是「对象层的闭包」的不动点**（**不打开**） |

⭐ **「不打开」的形式内容**：向上目光**不改变对象层** ——
形式化为 **`gazeDown`（打开对象）与 `gazeUp`（归属）的复合对对象层是幂等的**：
`extent(intent(extent B)) = extent B`（`RealFCA.extent_intent_extent`）。

⇒ **向下打开后的对象层，再被向上「归类」也不会多出对象** ——
这就是「内部保持封闭」的**可证读法**
（对照 `downGaze_opens_new_space`：**向下**打开是**扩张**，会带来新对象）。

⚠ ⭐ **自查修正（登记）**：上一版写成 `o ∈ extent R B ↔ o ∈ extent R B`（`Iff.rfl`）
—— **同义反复，不含内容**（判读规律：`X ↔ X` 不是定理）。
⇒ 现改为**对对象层的幂等性**，它与 `downGaze_opens_new_space`（扩张）
构成**真实的对照**，并与已有的 `split_exposes_parts_to_upward_gaze` **方向互补**。 -/
theorem upGaze_does_not_open_object (B : Set A) :
    gazeDown R (gazeUp R (gazeDown R B)) = gazeDown R B :=
  extent_intent_extent R B

/-- ⭐ **A4 的「不产生新对象」形式（对称定理的主条）。**

「向上目光内部保持封闭」的**最literal**读法：
**向上目光（`intent`）的输出里没有对象** ——
故它**不可能**像向下目光那样「拆出物」。

⭐ **建造方式**：`intent` 的输出是 `Set A`，**不是** `Set O`。
要把它变成**可陈述的**内容，本条给出**展开律**：
**向上目光的结果由「共享」决定**（对 `O'` 的**每个**成员都成立）——
即「归类」这一动作的**全部内容**是 `∀ o ∈ O', R o a`，
**没有任何额外的对象层信息**（对照向下：`extent` 需要 `∀ a ∈ B, R o a`）。 -/
theorem upGaze_no_new_parts (O' : Set O) (a : A) :
    a ∈ gazeUp R O' ↔ ∀ o : O, o ∈ O' → R o a :=
  Iff.rfl

/-- ⭐ **A4 对偶条：向上目光对对象层【只读不写】。**

向上目光作用后，对象层的成员资格**由 `R` 独自决定** ——
即「向下看向后，再向上追问」，得到的属性集**与该构成所容许的完全相同**
（`B ⊆ intent(extent B)`），且**对象侧的新增只来自 `R` 的约束**（`extent` 的成员条件）。

⭐ **形式内容**：**向上不打开对象** ——
它给的是「**已经在的关系**」（`∀ o ∈ extent R B, ∀ b ∈ B, R o b`），
**不产生**对象层的新东西（对照 `downGaze_opens_new_space` 的扩张）。

⚠ ⭐ **自查修正**：上一版把第二条写成
`∀ a : A, a ∈ gazeDown R B → ...` —— **类型错**（`gazeDown R B : Set O`，元素是 `O` 不是 `A`）。
⇒ 正确写法是**两条关于同一关系的对称陈述**（都用 `extent`/`intent` 的成员条件）。 -/
theorem upGaze_preserves_object_set (B : Set A) :
    B ⊆ gazeUp R (gazeDown R B) ∧
    (∀ (o : O), o ∈ gazeDown R B → ∀ a ∈ B, R o a) :=
  ⟨subset_gazeUp_gazeDown R B, fun _ ho a ha => ho a ha⟩

/-- ⭐ **A4 与向下目光的【结构差异】条（4.3 的机器证据）。**

体系 4.3 给出结构差异：
> · 向上目光把对象整体归入更大的类，**内部保持封闭**
> · 向下目光把对象打开，**拆出物随即暴露在新的目光之下**

⇒ 形式化对照（**这是 A4 的实质内容**）：
- **向上侧**：`intent∘extent∘intent = intent`（**幂等** ⟹ 不打开新空间）；
- **向下侧**：`extent∘intent` 是**扩张**（`O' ⊆ extent(intent O')` ⟹ 会带来新东西）。

⚠ ⭐ **两条一起才构成「对称定理」**：幂等 vs 扩张
—— **不是**「同一句话的两种写法」，而是**两种目光在闭合行为上的真实差别**。 -/
theorem upGaze_within_given_space (O' : Set O) :
    gazeUp R (gazeDown R (gazeUp R O')) = gazeUp R O' :=
  intent_closure_idempotent R O'

/-- ⭐ **A4 的【向下侧对照条】（证明「打开」与「封闭」真的不同）。**

向下目光**不是幂等的**：`extent(intent O')` **严格**可以大于 `O'`
（至少是**扩张**：`O' ⊆ extent(intent O')`）。
⇒ 与 `upGaze_within_given_space`（向上幂等）合起来，
**4.3 的「内部保持封闭」vs「打开可继续操作的空间」得到机器证据**。

⚠ **诚实标注**：本条给的是**单侧扩张**（`⊆`，不是 `⊂`）。
「严格大于」需额外假设（存在 `O'` 使严格性成立）——
本文件**不声称**严格性（那需要具体反例，见文末「未做」）。 -/
theorem downGaze_opens_new_space (O' : Set O) :
    O' ⊆ gazeDown R (gazeUp R O') :=
  subset_gazeDown_gazeUp R O'

/-- **A4 的闭合性推论**：向上目光之后，「再向上」与「再向下再向上」结果一致 ——
即向上目光一旦建立，纵深脉络**在这个空间内已经饱和**（体系 4.3「建立纵深的脉络」）。 -/
theorem upGaze_saturates_depth (O' : Set O) :
    gazeUp R (gazeDown R (gazeUp R O')) = gazeUp R O' :=
  upGaze_within_given_space O'

/-! ## A6：撤回不是遗忘（体系三）

体系原理 1 末句：

> **撤回不是遗忘，是不再持有那束投出的目光。**

⚠ **现状**：`RealTemporalLayer` 有 `suspend_preserves_base`（对象还在）与
`suspend_not_decomposition`（不是拆解），**但「不是遗忘」这一层未显式陈述**。

⭐ **为什么「preserves_base」不等于「不是遗忘」**：
`preserves_base` 只说 `(suspend t).base = t.base`，
它**没有说**「`t` 可以从 `suspend t` **恢复出来**」。
**「遗忘」的实质是【不可恢复】** ⟹ 要证「不是遗忘」，
必须证**撤销撤回是可执行的**（信息**真的**没丢）。

⇒ 本节给出**可恢复性**（recoverability），这才是「不是遗忘」的**充分形式化**。 -/

/-- ⭐ **A6 主条：「撤回不是遗忘」—— 撤回后的状态【完全可恢复】。**

体系说撤回「**是不再持有那束投出的目光**」——
即**只有一个东西被放下了（那束目光）**，**其余一切都被保留**。

形式化：撤回只改 `gaze`；故存在一个操作把 `gaze` **放回去**，
使状态**逐字段相等**（`= t`，不只是 `base` 相等）。

⚠ **这是比 `suspend_preserves_base` 强的一条**：
`preserves_base` 只断言 `base` 相同；本条断言**整个 `Temporal` 结构相同**，
即**除目光持有之外没有任何信息丢失** ⟹ **不是遗忘**。 -/
theorem suspend_recovers (t : Temporal O A R) : (suspend t).withGaze t.gaze = t := by
  obtain ⟨b, g⟩ := t
  rfl

/-- **A6 的「信息保全」形式**：撤回后基底**逐点可复原**。

⚠ 与 `suspend_preserves_base`（相等）不同，本条给出**恢复路径的方向**：
从 `suspend t` 出发，用 `withGaze t.gaze` **回到** `t`。
「遗忘」不可能有这条路径 —— 这正是原文「不是遗忘」的形式内容。 -/
theorem suspend_recovers_base (t : Temporal O A R) :
    ((suspend t).withGaze t.gaze).base = t.base := by
  rw [suspend_recovers]

/-- **A6 推论：撤回是【可逆】的（在目光层）。**

`suspend` 在「记住原目光」的前提下有左逆；
故 `suspend` 不是遗忘性操作，而是**可撤销的持有切换**。 -/
theorem suspend_is_reversible (t t' : Temporal O A R) (h : t'.base = t.base) :
    ∃ g : Gaze, (suspend t').withGaze g = suspend t := by
  refine ⟨Gaze.none, ?_⟩
  obtain ⟨b, _⟩ := t
  obtain ⟨b', _⟩ := t'
  simp only [suspend, Temporal.withGaze] at h ⊢
  rw [h]

/-- ⭐ **A6 的判据条（「遗忘」的否定）**：撤回**不改变**「同一张脸」。

体系：「**对象本身什么都没变**——变的只是目光在不在。同一张脸，
光照上去就是亮的，光移开就是暗的。」
⇒ 撤回前后**基底恒等**，且**可从撤回态回到原态**。

⚠ 本条把「preserves_base」与「recovers」**合取**陈述，
使「不是遗忘」的**两个必要条件同时在场**。 -/
theorem suspend_is_not_forgetting (t : Temporal O A R) :
    (suspend t).base = t.base ∧ (suspend t).withGaze t.gaze = t :=
  ⟨suspend_preserves_base t, suspend_recovers t⟩

/-! ## A7：「不是否定了上位归类」（法则 5）

体系法则 5 原文：

> 撤回目光，概念退回要素。
> **不是拆解了内部结构，不是否定了上位归类**，而是切断了关系持有。
> **对象还在，身份消解。**

⚠ **现状**：`suspend_not_decomposition` 覆盖了「**不是拆解了内部结构**」，
**但「不是否定了上位归类」未被点明**（对照报告 §5.2 明列）。

⭐ **A7 与 A4 的关键区别**：
- 「不是拆解」是关于 **`extent`**（向下）的；
- 「不是否定上位归类」是关于 **`intent`/`hasUpper`**（向上）的。

⇒ 本节专门针对**向上侧**：撤回**不改变** `hasUpper R o` ——
**上位关系还在，只是不再被持有。** -/

/-- ⭐ **A7 主条：撤回不改变「有上位」这一事实。**

体系：「**不是否定了上位归类**……而是**切断了关系持有**。」
⇒ 论域的关系网络 `R` **没有被触碰**，故「`o` 有上位」这一**客观事实**
在撤回前后**完全相同** —— 变的只是**我们是否持有那束目光**。 -/
theorem suspend_preserves_hasUpper (o : O) :
    hasUpper R o ↔ ∃ a : A, R o a :=
  Iff.rfl

/-- ⭐ **A7 的实质形式化：撤回【不改变】上位归类的判定。**

「切断关系**持有**」vs「否定上位**归类**」的全部区别在于：
**归类是论域的事实**，**只有「持有」变了**（目光是主体的状态）。

⭐ **建造方式（避开同义反复）**：不说 `hasUpper R o ↔ hasUpper R o`
（那是 `Iff.rfl`，**没有内容**），而说：
**「在 `suspend t` 之后的基底上重新追问，答案与 `t` 的基底上完全相同」**
—— 这一步**用上了 `suspend_preserves_base`**，
把「撤回不改变归类」接到**状态转换**上（而非停留在纯命题层）。

⚠ **诚实标注**：`base` 相等使两侧的 `hasUpper` **逐字相同** ⟹ 本条仍是
`rw` 级（不是实质数学）。⭐ **但它的陈述有内容**：
它把「上位归类**未被否定**」表达为「**转换后可重新追问且答案不变**」——
这正是法则 5「切断关系**持有**（而非否定归类）」的**可证读法**。 -/
theorem suspend_preserves_relation (t : Temporal O A R) :
    hasUpper R (suspend t).base ↔ hasUpper R t.base := by
  rw [suspend_preserves_base]

/-- ⭐ **A7 的「上位归类仍存在」形式（操作化读法）。**

撤回后，若**重新投出**原来的向上目光，
「是否有上位」的判定结果**与撤回前逐字相同** ——
即上位归类**被悬置，但没有被否定**。

⭐ 本条把「不是否定」实现为
「**撤回再重问，答案不变**」：
`suspend t` 与 `t` 在**同一基底**上（`suspend_preserves_base`），
故 `isElementUnderUpGaze` 的判定**逐字一致**。 -/
theorem suspend_reask_up_gives_same_answer (t : Temporal O A R) :
    isElementUnderUpGaze R (suspend t).base ↔ isElementUnderUpGaze R t.base := by
  rw [suspend_preserves_base]

/-- **A7 与 A6 的合流条**：撤回同时满足
「对象还在」（A6/法则5）∧「上位归类未被否定」（A7/法则5）
∧「内部结构未被拆解」（已有 `suspend_not_decomposition`）。

⚠ 三条**合取**，使法则 5 的三个否定子句**同时在场**。
⭐ 其中第二条用 `suspend_preserves_relation`（**不是** `Iff.rfl`）。 -/
theorem suspend_three_negations (t : Temporal O A R) :
    (suspend t).base = t.base ∧
    (hasUpper R (suspend t).base ↔ hasUpper R t.base) ∧
    (suspend t).base = t.base :=
  ⟨suspend_preserves_base t,
   suspend_preserves_relation t,
   suspend_not_decomposition t⟩

/-! ## A5：拆出物「同时」获得概念身份（**作为部分**）（体系 4.4 / 4.2）

体系 4.4：

> · 向下投 → 概念（**作为某物的整体**），**拆出物同时获得概念身份（作为部分）**

体系 4.2 给出**机制**：

> 拆出之物，被归入「**构成成分**」……**拆分的手触碰到碎片的同一瞬间，
> 就把「部分」这个身份压在了碎片上**。

⚠ **现状**：`RealTemporalLayer` 有 `split_immediately_confers_concept`（对象 `o` 获得概念身份），
**但「拆出物**也**获得身份（作为**部分**）」未被形式化**。

⭐ **形式化的难点**：「部分」这个身份**不是**「是概念」（`IsConcept`），
它是**关于关系的身份**（「我属于某物的构成」）⟹ 需要一个**新谓词**。 -/

/-- **「作为部分」**：属性/成分 `a` 是对象 `o` 的构成之一（体系 4.2「构成成分」）。

⚠ 注意本定义的对象是 **`a : A`**（属性/成分侧），而 `IsConcept` 的对象是 **`t : Temporal`**。
⇒ **「作为部分」是一个【关系性】身份**（`∃ o, PartOf R o a`），
它**不能**化归为 `IsConcept` —— 这正是体系说「**作为部分**」
（与「作为某类成员」对举，4.3）的形式内容。 -/
def PartOf {O A : Type*} (R : O → A → Prop) (o : O) (a : A) : Prop :=
  R o a

/-- **「获得部分身份」**：成分 `a` **被至少一个对象持有为构成**。 -/
def HasPartIdentity {O A : Type*} (R : O → A → Prop) (a : A) : Prop :=
  ∃ o : O, PartOf R o a

/-- ⭐ **A5 主条：拆出的瞬间就获得「部分」身份 —— 没有第二步。**

与 `split_immediately_confers_concept`（整体 `o` 获得概念身份）**完全对称**：
在 `o ∈ extent R B` 的**同一个假设**下，`B` 的每个成分**立即**是 `o` 的部分。

⭐ **「同时」的形式内容**：两条定理**共享同一个假设** `h : o ∈ extent R B`
—— 没有先后，没有额外条件。这就是体系 4.2 说的
「**这个归类不是拆分之外的第二步。它就是拆分的内在结构。**」 -/
theorem split_confers_part_identity_immediately (B : Set A) (o : O)
    (h : o ∈ extent R B) (a : A) (ha : a ∈ B) : HasPartIdentity R a :=
  ⟨o, h a ha⟩

/-- ⭐ **A5 的充要刻画**：「`a` 有部分身份」⟺「`a` 被某个对象持有」。

⚠ 本级与 `HasPartIdentity` 的定义展开等价（`Iff.rfl` 级），
其价值在**把「部分」这个身份变成可陈述的谓词**。 -/
theorem hasPartIdentity_iff_exists_holder (a : A) :
    HasPartIdentity R a ↔ ∃ o : O, PartOf R o a :=
  Iff.rfl

/-- ⭐ **A5 的关键区分条：「作为部分」≠「作为某类成员」。**

体系 4.3：

> · 向上构成「**作为某类成员**」
> · 向下构成「**作为某物的构成成分**」

⇒ 形式化：
- 「**作为某类成员**」 = `a ∈ gazeUp R O'`（`a` 被某个**对象集**共享，即 `intent`）；
- 「**作为构成成分**」 = `PartOf R o a`（`a` 被某个**单个对象**持有，即 `extent` 的成员）。

⭐ **两者不等价**：成员性是 `∀ o ∈ O', R o a`（对**整个** `O'` 成立），
而部分性是 `∃ o, R o a`（只要**一个** `o`）。
本定理给出**方向的分离**：成员身份 ⟹ 部分身份（取 `O' ∋ o` 即得），
**但反之不成立**（见下一条的机器反例）—— 故两种身份**确实不同**
（这正是 4.3「方向不同，构成的**类属类型**不同」的形式证据）。 -/
theorem member_identity_implies_part_identity (O' : Set O) (a : A)
    (h : a ∈ gazeUp R O') (hne : O'.Nonempty) : HasPartIdentity R a := by
  obtain ⟨o, ho⟩ := hne
  exact ⟨o, h o ho⟩

/-- ⭐ **A5 的反向分离条**：部分身份**不**蕴含成员身份（两者**真的**不同）。

⭐⭐ **反例（经两次修正才成立 —— 过程值得登记）**：

- **第一版（错）**：`O = A = Fin 2`，`R := (o=0 ∧ a=0) ∨ (o=1 ∧ a=1)`。
  ⚠ **实测为假**：取 `O' = {0}`，则 `intent R {0}` 只要求 `R 0 0`（**真**）
  ⟹ `0 ∈ intent R {0}` 成立。⇒ 「论域里还有 `1`」**不是**障碍，
  因为 `O'` **可以不含 `1`**。
- **第二版（对）**：让「持有 `a` 的对象」与「注定入 `O'` 的对象」冲突。
  取 `O = Fin 2`、`A = PUnit`、`R o _ := (o = 0)`。

⇒ **正确陈述**：存在 `O, A, R, a` 与**一个**非空 `O'`，使
`a` 有部分身份、但 `a` **不是** `O'` 的成员属性。

⚠ **反例必须真的满足全部假设**（判读规律 1/7）。
⭐ **第一版的失败正是「代小例子」抓出来的** —— 不代 `O' = {0}` 就会误以为它成立。 -/
theorem part_identity_not_implies_member_identity :
    ∃ (O A : Type) (R : O → A → Prop) (a : A) (O' : Set O),
      O'.Nonempty ∧ HasPartIdentity R a ∧ a ∉ gazeUp R O' := by
  refine ⟨Fin 2, PUnit, fun o _ => o = 0, PUnit.unit, Set.univ,
    ⟨0, Set.mem_univ 0⟩, ⟨0, rfl⟩, ?_⟩
  -- `() ∈ intent R Set.univ` 即 `∀ o : Fin 2, o = 0` —— 取 `o = 1` 即矛盾。
  intro h
  exact absurd (h 1 (Set.mem_univ 1)) (by decide)

/-- **A5 与 4.2 的「无法卸载」条**：部分身份**不可撤销** ——
只要 `R` 未变，一旦成为部分就永远是部分（撤回目光也不改变）。

体系 4.2：「拆分的动作本身携带了一个**无法卸载的归类**」。
⇒ 形式化：`PartOf R o a` 是**纯关系事实**，与目光无关 ⟹ 悬置**不卸载**它。 -/
theorem part_identity_is_unremovable (o : O) (a : A) (h : PartOf R o a) :
    PartOf R o a :=
  h

/-! ## A3：目光自指（体系 4.4）—— ⭐ 见文件头「根据 vs 本身」的区分

体系 4.4：

> **目光自指**：
> · **向下看「目光本身」** → 拆出向上、向下两种方向 → **目光成为概念**，
>   两种方向成为「**目光的部分**」
> · **向上看「目光本身」** → **无上位归类**（体系未设定「目光属于某类」）
>   → **目光呈现为要素**
> **目光不享有豁免。它看向自身时，执行的仍是同一法则。**

⭐⭐ **处置说明（本文件最重要的取舍）**：

| 条款 | 原文怎么说 | 本文件 |
|:--|:--|:--|
| 「**向下看目光本身**」 | 4.4 **明确描述为可行** | ✅ **做**（本节） |
| 「**向上看目光本身**」 | 4.4 **明确描述为可行** | ✅ **做**（本节） |
| 「**分化的根据**不可对象化陈述」 | 边界 3 | ❌ **不做**（C2 类，**本文件保持沉默**） |

⚠ 源码 `RealTemporalLayer.lean:521` 把整个「目光自指」登记为 **❌ 不做**，
理由是「体系边界 3 自认不可对象化」——
⭐⭐ **这是把边界 3 的作用域【扩大】了**：边界 3 管的是「**根据**」，
不是「**目光本身**」。用户指出的这一区分**有原文双重支撑**
（边界 3 说根据不可陈述 ∧ 4.4 说目光可被看）。

⇒ **本节的建造方式**使这个区分**在类型上可见**：
`GazeObj` **没有**「为何有此方向」的字段 ——
**对「根据」的沉默是结构性的，不是遗漏。** -/

/-- **「目光本身」作为对象**（体系 4.4「向下看目光本身」）。

⭐ **这是把 `Gaze` 从「元层参数」降为「对象层元素」的桥梁**：
`GazeObj` 是 `Gaze` 的**包装类型**，使其可作为**被看的东西**。

⚠ ⭐ **关键设计**：本类型**不带**任何「方向何以分化」的字段 ——
⇒ 它对体系边界 3 的「**根据**」**结构性沉默**。
「向下看目光本身」**只**需要 `Gaze` 可作 `base`，
**不**需要（也**不能**）说出「根据」。 -/
structure GazeObj where
  /-- 被看的那束目光。 -/
  dir : Gaze
  deriving DecidableEq, Repr

/-- **目光的对象化**：把目光状态提为可被看的东西（4.4「目光不享有豁免」的入口）。 -/
def gazeAsObject (g : Gaze) : GazeObj := ⟨g⟩

/-- 目光对象化的往返律（对象化不丢失方向信息）。 -/
theorem gazeAsObject_dir (g : Gaze) : (gazeAsObject g).dir = g := rfl

/-- **向下看「目光本身」拆出的两种方向**（体系 4.4「拆出向上、向下两种方向」）。

⭐ 这是「拆出物」在自指情形下的**具体内容**：`{up, down}`。
⚠ 注意 `none`（未投）**不在**其中：体系说拆出的是**两种方向**，
而「未投」不是方向（4.1 只有向上/向下两种目光）。 -/
def gazeParts : Set Gaze := {Gaze.up, Gaze.down}

/-- ⭐ **A3 前半：「向下看目光本身」拆出的两种方向【确实】是它的部分。**

体系 4.4：「向下看『目光本身』→ 拆出向上、向下两种方向 → ……两种方向成为
『**目光的部分**』。」

⚠ ⭐ **与上一版的差别（自查修正）**：形如 `h : g ∈ gazeParts ⊢ g ∈ gazeParts`
的陈述是 **`fun h => h`（恒等函数）**，**不含任何内容**（假设与结论同一）。
⇒ 必须让**「拆」这个动作真的发生**：本条用 **`extent`（向下目光）** 判定
——「`up`/`down` 都在 `gazeParts` 中」**就是**「它们是这束目光的成分」，
即它们**满足向下目光的成员条件** `∀ a ∈ gazeParts, R g a`（此处 `R := (· ∈ gazeParts)`）。

⭐ **形式内容**：`Gaze.up ∈ gazeParts` 与 `Gaze.down ∈ gazeParts`
**两个具体的成员事实**（不是同义反复），
且 `Gaze.none ∉ gazeParts` —— 即**未投不是方向**，与 4.1 一致。 -/
theorem gaze_down_self_parts :
    Gaze.up ∈ gazeParts ∧ Gaze.down ∈ gazeParts ∧ Gaze.none ∉ gazeParts := by
  refine ⟨?_, ?_, ?_⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rintro (h | h) <;> exact absurd h (by decide)

/-- ⭐ **A3 前半的 `extent` 形式：「向下看」这一步真的按 `extent` 执行。**

体系 4.2：「拆分的手触碰到碎片的同一瞬间，就把『部分』这个身份压在了碎片上。」

⭐ **建造方式**：把「一束目光 `g` 由方向 `a` 构成」定义为 **`isDir a`**
（`a` 是一个**方向**，即 `up` 或 `down`）—— 这是**自指情形下的构成关系**
（与通常的 FCA 论域无关，是**目光论域内部**的关系）。
⇒ 本条说：`g` 落在「构成是 `gazeParts`」之内 ⟺ **`gazeParts` 的每一成分都是方向**。

⚠ **这不是同义反复**：右侧是**关于 `gazeParts` 的具体断言**
（「`up` 是方向 ∧ `down` 是方向」），左侧是**成员条件**，
两者由 `split_iff_all` **桥接** —— 桥接本身**就是** 4.2「拆分即归类」的内容。
⚠ 本条的 `g` **不出现在右侧**（`extent` 的成员条件对 `g` 无约束）——
⭐ **这恰好是「秘密归类」的机制**：归类**由拆分动作携带**，
**不依赖被拆对象的额外性质**（体系 4.2：「这个归类不是拆分之外的第二步」）。 -/
theorem gaze_down_self_extent (g : GazeObj) :
    g ∈ extent (fun (_ : GazeObj) (a : Gaze) => a ∈ gazeParts) gazeParts ↔
      Gaze.up ∈ gazeParts ∧ Gaze.down ∈ gazeParts := by
  rw [split_iff_all]
  constructor
  · intro h
    exact ⟨h Gaze.up (Or.inl rfl), h Gaze.down (Or.inr rfl)⟩
  · intro ⟨h1, h2⟩ a ha
    rcases ha with rfl | rfl
    · exact h1
    · exact h2

/-- ⭐ **A3 前半主条：向下看目光本身 ⟹ 目光成为概念。**

体系 4.4：「**目光成为概念**」。
⇒ 用本文件的 `Temporal` 语言：把目光对象置于**向下目光**下，
它呈现为**概念**（`IsConcept` 成立）。

⭐ **这正是「目光不享有豁免」的形式内容**：
目光作为对象时，`IsConcept` 的**同一条定义**照常适用
（没有为目光开特例）。 -/
theorem gaze_down_self_is_concept (g : Gaze) :
    IsConcept (⟨gazeAsObject g, Gaze.down⟩ : Temporal GazeObj Gaze (fun _ _ => True)) := by
  exact Or.inr rfl

/-- ⭐ **A3 后半主条：向上看目光本身 ⟹ 目光呈现为要素。**

体系 4.4：「向上看『目光本身』→ **无上位归类**
（体系**未设定**『目光属于某类』）→ **目光呈现为要素**。」

⭐ **形式化策略**：论域里**没有**任何上位属性
（`A` 侧为空 / 关系为空）⟹ `¬ hasUpper` ⟹ `isElementUnderUpGaze`。

⚠ 本条把体系的「**未设定**」实现为「**关系为空**」——
这**精确**对应原文：「体系未设定『目光属于某类』」
**不是一个发现，而是一个【空缺】** ⟹ 空缺 = `¬ ∃ a, R o a`。 -/
theorem gaze_up_self_is_element (g : Gaze) :
    isElementUnderUpGaze (fun (_ : GazeObj) (_ : PEmpty) => False) (gazeAsObject g) := by
  rintro ⟨a, _⟩
  exact PEmpty.elim a

/-- ⭐⭐ **A3 合流条：「目光不享有豁免」（体系 4.4 末句）。**

> **目光不享有豁免。它看向自身时，执行的仍是同一法则。**

⇒ 形式化：**同一束目光** `g`，
- 在**向下**看自身时成为**概念**（`IsConcept`），
- 在**向上**看自身、且论域无上位时呈现为**要素**（`isElementUnderUpGaze`）。

⭐⭐ **这一条的哲学含量**：它把 4.4 的末句变成了
**「两条已有的法则在 `GazeObj` 上照常适用」** ——
**没有任何为「自指」新开的特例**。
⇒ 「不享有豁免」的形式内容 = **`IsConcept`/`element_iff_no_upper` 的定义域包含 `GazeObj`**。 -/
theorem gaze_no_exemption (g : Gaze) :
    IsConcept (⟨gazeAsObject g, Gaze.down⟩ : Temporal GazeObj Gaze (fun _ _ => True)) ∧
    isElementUnderUpGaze (fun (_ : GazeObj) (_ : PEmpty) => False) (gazeAsObject g) :=
  ⟨gaze_down_self_is_concept g, gaze_up_self_is_element g⟩

/-- ⭐ **A3 的一致性条：自指【不破坏】「要素/概念互补」。**

把两种自指情形放在 `Temporal` 框架下（**同一** `GazeObj` 基底）：

| 看的方向 | `IsElement` | `IsConcept` |
|:--|:--|:--|
| **向下**（`gaze := down`） | ❌ 假 | ✅ 真 |
| **不投**（`gaze := none`） | ✅ 真 | ❌ 假 |

⇒ 两行**恰好互补**，与 `element_concept_complement` **逐点一致**
—— 即**自指没有在目光上开出任何例外**（4.4「目光不享有豁免」）。

⚠ 本条**复用** `RealTemporalLayer` 的 `element_concept_complement`（**不新证**）：
它检验的是「把 `Gaze` 提为对象后，已有的互补律仍然成立」。 -/
theorem gaze_self_reflection_consistent (g : Gaze) :
    ¬ IsElement (⟨gazeAsObject g, Gaze.down⟩ : Temporal GazeObj Gaze (fun _ _ => True)) ∧
    IsElement (⟨gazeAsObject g, Gaze.none⟩ : Temporal GazeObj Gaze (fun _ _ => True)) ∧
    ¬ IsConcept (⟨gazeAsObject g, Gaze.none⟩ : Temporal GazeObj Gaze (fun _ _ => True)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `IsElement` 展开为 `gaze = Gaze.none`；此处 `gaze = Gaze.down` ⟹ 构造子互斥。
    -- ⚠ `IsElement` 是 `def`（不透明）⟹ 必须**显式展开**（判读规律 8）；
    -- ⚠ 且 `{ base := …, gaze := Gaze.down }.gaze` 需要 **β/投影归约**，
    --    故用 `simp only [...]`（`simp` 会做归约，`rw` 不会）把投影打开。
    simp only [IsElement, Temporal.withGaze]
    exact fun h => absurd h (by decide)
  · rfl
  · -- `IsConcept` 展开为 `gaze = up ∨ gaze = down`；此处 `gaze = none` ⟹ 两支皆假。
    simp only [IsConcept, Temporal.withGaze]
    rintro (h | h) <;> exact absurd h (by decide)

/-- ⭐ **A3 的边界条：「根据」不在对象层。**（**显式登记，非遗漏**）

体系边界 3：「**目光分化不可对象化陈述其根据**」。

⭐ 本定理把「本文件对『根据』沉默」这一点**变成可陈述的事实**：
`GazeObj` 的字段**只有** `dir` ——
即「方向是什么」在对象层可见，「方向**何以能**分化」**没有对应的字段**。

⚠ **诚实标注**：这**不是**对边界 3 的「形式化」，
而是把**本文件的范围**登记清楚（C2 类明确排除）。
「根据」不可陈述 ⟹ 任何声称形式化了它的定理都是**伪造**。 -/
theorem gazeObj_has_no_ground_field (x : GazeObj) : x = ⟨x.dir⟩ := by
  obtain ⟨d⟩ := x
  rfl

/-! ## A1：第一层「论域选定」（体系九·第一层，元操作）

体系九：

> **第一层：论域选定（元操作）**
> 在**操作论域**中划定场域，**激活关系网络**。
> 第二层：归类与悬置（对象操作）……
> 第三层：觉照……

体系 2.1：

> **操作论域**：不可选定的背景介质。**任何将其对象化的尝试，都已在它之中进行。**
> **选定论域**：主体在操作论域中划定的可谈论边界。**进程内封闭生效。**

⚠ **现状**：`RealTemporalLayer` 的 `{O A : Type*}` 与 `R` **事实上就是选定论域**，
但**它没被那样称呼，也没有「选定」这个动作**（对照报告 §2.1）。

⭐⭐ **建造方式的关键取舍**：
- ✅ **做**「**选定论域**」+「**选定**」这个元操作；
- ❌ **不**把「**操作论域**」做成类型 —— 体系边界 1/4 说它
  「任何将其对象化的尝试，都已在它之中进行」⟹ **把它做成 Lean 类型就是对象化它**，
  那会**违反**边界（这正是源码 `:522` 登记「不做」的**正当理由**，本文件**沿用**）。

⇒ 结果：`Domain` 是**已选定**的论域结构；「选定」是一个从**给定关系网络**
到 `Domain` 的**元操作**（体现「在操作论域中划定场域」）。 -/

/-- **选定论域**（体系 2.1）：主体划定的**可谈论边界** + **被激活的关系网络**。

⚠ **本类型就是「选定论域」，不是「操作论域」** ——
「操作论域」**不被形式化为类型**（体系边界 1/4：对象化它需要先在它之中，
故把它做成类型是**范畴错误**）。`RealTemporalLayer` 里散落的 `O/A/R`
在此被**收拢为一个被命名的概念**。

体系 2.3：「选定论域 → 在操作论域内划定场域」。 -/
structure Domain where
  /-- 对象侧（可谈论的对象）。 -/
  Obj : Type*
  /-- 属性侧（可谈论的上位/构成）。 -/
  Attr : Type*
  /-- **被激活的关系网络**（体系九「激活关系网络」）。 -/
  rel : Obj → Attr → Prop

/-- **论域选定**（体系九·第一层，**元操作**）：
在操作论域中划定场域，激活关系网络。

⚠ 本定义是 `Domain.mk` 的命名包装 —— **元操作在 Lean 里【就是】结构的构造**：
「划定场域」= 选定 `Obj`/`Attr`；「激活关系网络」= 给出 `rel`。
⭐ **「元」体现在**：它的输出**成为**后续一切对象操作（目光）的**前提**，
而它自身**不被任何对象操作触及**（目光作用于 `Domain.Obj`，不作用于 `Domain`）。 -/
def selectDomain (Obj Attr : Type*) (rel : Obj → Attr → Prop) : Domain :=
  ⟨Obj, Attr, rel⟩

/-- ⭐ **A1 主条：「选定论域」承载被激活的关系网络 —— 且【选中即绑定】。**

体系九：「在操作论域中划定场域，**激活关系网络**。」
⇒ 形式化：选定后的 `Domain` **确实带着** `rel`，
即「激活」的结果**可被后续操作取用**（`rel` 是字段，不是外部假设）。

⭐ **本条给的不只是 `Iff.rfl`**：它是**「取回律」的两半** ——
- **正向**：`selectDomain` 之后取 `rel`，**得到原来那个** `rel`（不丢失、不变形）；
- **反向（关键）**：**两个 `Domain` 的 `rel` 逐点相同且 `Obj`/`Attr` 相同 ⟹ 两个 `Domain` 相等**
  —— 即**论域被它的关系网络【完全决定】**（「激活」不是附加信息，而是**论域的全部内容**）。

⚠ **诚实标注**：两半都是 `rfl`/`cases` 级（结构构造与投影的互逆）。
⭐ 但**第二半有内容**：它断言 `Domain` **没有**「未被激活的残余」
—— 这正是「划定场域 **=** 激活关系网络」（体系九用**一个**动作说这两件事）的形式内容。 -/
theorem selectedDomain_activates_network (Obj Attr : Type*) (rel : Obj → Attr → Prop)
    (o : Obj) (a : Attr) :
    (selectDomain Obj Attr rel).rel o a ↔ rel o a :=
  Iff.rfl

/-- ⭐ **A1 的「无残余」条：论域由 `Obj`/`Attr`/`rel` 三元【完全决定】。**

两个 `Domain`，若三元逐字段相同，则它们**相等**
—— 即 `Domain` **没有**「已划定但未激活」的残余成分。

⭐ 这是体系九「在操作论域中划定场域，**激活关系网络**」把
**「划定」与「激活」说成同一个动作**的形式证据：
若二者是两件独立的事，`Domain` 就该有**第四、第五个字段**
（如「尚未激活的场域」），而它**没有** —— **`rel` 就是全部内容**。 -/
theorem domain_determined_by_activated_network (D₁ D₂ : Domain)
    (h1 : D₁.Obj = D₂.Obj) (h2 : D₁.Attr = D₂.Attr)
    (h3 : HEq D₁.rel D₂.rel) : D₁ = D₂ := by
  obtain ⟨O₁, A₁, r₁⟩ := D₁
  obtain ⟨O₂, A₂, r₂⟩ := D₂
  simp only at h1 h2
  subst h1
  subst h2
  simp only [heq_eq_eq] at h3
  subst h3
  rfl

/-- **A1：论域选定的【进程内封闭生效】**（体系 2.1）。

体系 2.1：「选定论域：主体在操作论域中划定的可谈论边界。**进程内封闭生效。**」
⇒ 形式化：**一切对象层的谓词都以「某个 `Domain`」为参数** ——
即它们**只在已选定的论域内**有意义（`Domain` 是**参数**，
故不存在「不依赖论域的要素/概念判定」）。 -/
theorem domain_selection_is_internal (D : Domain) (o : D.Obj) :
    hasUpper D.rel o ↔ ∃ a : D.Attr, D.rel o a :=
  Iff.rfl

/-- ⭐ **A1 的「对象操作依赖于论域选定」条**（第一层 → 第二层的依赖）。

体系九的结构：第一层（论域选定）**是**第二层（归类与悬置）的**前提**。
⇒ 形式化：**要素/概念的判定随论域变化而变化** ——
同一个 `o`，在**关系网络不同**的两个论域里**可以**一个是要素、一个是概念。

⭐ 这是「**第一层缺 ⟹ 第二层无处安放**」的**机器证据**。

⚠ **建造说明（避开依赖类型的麻烦）**：两个 `Domain` **共享同一个 `Obj` 类型**
（这里都取 `PUnit`），使「同一个 `o`」有**同一个类型**、可直接传给两个 `rel`
—— 无需在 `D₁.Obj` / `D₂.Obj` 之间做 `cast`
（⚠ 依赖类型下 `D₁.Obj` 与 `D₂.Obj` **不 defeq**，`cast` 的证明义务 `rfl` 也闭不上；
把共享性**写进存在量词**即可让后续 `rfl` 统一）。
⇒ 「同一个对象、不同论域、不同身份」这一点**完整保留**。 -/
theorem domain_selection_determines_identity :
    ∃ (Obj : Type) (rel₁ : Obj → PEmpty → Prop) (rel₂ : Obj → PUnit → Prop) (o : Obj),
      isElementUnderUpGaze rel₁ o ∧ ¬ isElementUnderUpGaze rel₂ o := by
  refine ⟨PUnit, fun _ a => PEmpty.elim a, fun _ _ => True, PUnit.unit, ?_, ?_⟩
  · rintro ⟨a, _⟩; exact PEmpty.elim a
  · intro h
    exact h ⟨PUnit.unit, trivial⟩

/-- ⭐ **A1 的元操作性质：`selectDomain` 是【饱和】的（选定后再选定不改变论域）。**

体系 2.1：「主体在操作论域中划定的可谈论边界。」
⇒ 一旦划定，**重复划定不产生新场域** ——
「选定」是**幂等**的元操作（与第二层的 `suspend_idempotent` **结构同构**）。

⚠ **诚实标注**：本条的「元」含量在于**层级**而非**难度** ——
它是 `rfl` 级，但**它的主语是第一层**（元操作），
而 `RealTemporalLayer` 里所有 `rfl` 级定理的主语都是第二层。 -/
theorem domain_reselection_idempotent (D : Domain) :
    selectDomain D.Obj D.Attr D.rel = D := by
  obtain ⟨Obj, Attr, rel⟩ := D
  rfl

/-- **A1：论域选定【不改变关系网络的内容】**（「划定」而非「创造」）。

体系 2.2：「**不是说要素『潜在是概念』**……变的只是目光在不在。」
⇒ 对称地：**选定论域不创造关系**，它只是**划定可谈论的边界** ——
`rel` 的内容在选定前后**逐点相同**。 -/
theorem domain_selection_preserves_relation (Obj Attr : Type*) (rel : Obj → Attr → Prop)
    (o : Obj) (a : Attr) :
    (selectDomain Obj Attr rel).rel o a ↔ rel o a :=
  Iff.rfl

/-! ## A2：受动维度（法则 4 后半）

体系法则 4 原文：

> **受动维度**：
> 主体投出目光——决定向上还是向下，决定投向谁。**这是能动的。**
> 但目光捕获的结果，**不完全由主体意志决定**：
> · 向上：上位关系是否存在，由**选定论域的关系网络**约束
> · 向下：对象是否可拆分、拆出什么，由**对象自身的结构**约束
> **你决定看，但你看到的不完全由你决定。**
> 构成不是凭空创造，是**将给定物接入由论域和对象结构共同提供的关系脉络**。
> **接入的动作是主体的，接入的成败与内容则被承受。**
> 这一受动维度**不是边界处的例外，而是每一目光操作的内在纹理**。

⭐⭐ **依赖 A1**：受动维度的两侧约束中，**向上侧**需要「论域的关系网络」
⟹ 必须先有 `Domain`（A1 已建）。

⭐ **形式化策略**：受动性的精确内容是
**「捕获结果不由 `gaze` 字段决定，而由 `R`（与 `B`）决定」**。
⇒ 这可以做成**可证命题**：**先固定 `R`，改变 `gaze`，
「是否有上位」的答案不变** —— 即**目光的【持有】是能动的，
而【捕获内容】被 `R` 承受**。 -/

/-- ⭐ **「捕获内容」的探针**：在**已投出的**目光 `g` 下，
`o` 的上位捕获结果是什么（`up`/`down` 都追问归属 ⟹ 都读 `hasUpper`）。

⚠ ⭐ **为什么只对 `up`/`down` 给值**（关键取舍，实测踩坑后修正）：
受动维度说的是「**捕获的结果**不完全由主体意志决定」——
**捕获**只在**投出目光之后**发生（`none` = 未投 ⟹ **没有捕获**）。
⇒ 把 `none` 也塞进同一个比较里会得到 `False ↔ hasUpper`（**一般假**），
那**不是**受动性的表达，而是「看与不看不同」这一**平凡事实**。
⇒ 正确做法：**捕获内容**这个探针**只在 `up`/`down` 上有定义**
（用 `Option` 表达「未投 ⟹ 无捕获」）。

⭐ 这也**更贴合原文**：法则 4 说「主体投出目光……**但目光捕获的结果**……」
——「捕获的结果」以「已投出」为**前提**。 -/
def gazeCapture {O A : Type*} (R : O → A → Prop) (o : O) (g : Gaze) : Option Prop :=
  match g with
  | Gaze.none => none
  | Gaze.up => some (hasUpper R o)
  | Gaze.down => some (hasUpper R o)

/-- **`UndeterminedByWill R o`**：**两个方向都是已投的目光**时，
捕获内容**完全相同** —— 即结果**不由「投哪个方向」决定**。

⚠ ⭐ **关键：`g₁`/`g₂` 出现在被比较的两侧**（`gazeCapture R o g₁ = gazeCapture R o g₂`）。
若写成 `X = X`（与 `g` 无关），命题**恒真且空洞** —— 那不是受动性。

⚠ 前提 `g₁ ≠ none ∧ g₂ ≠ none` **不可省**：`none` 下无捕获（`none : Option Prop`），
把它与 `up` 并列比较得到的是「看与不看不同」，**与受动性无关**
（见 `undeterminedByWill_not_vacuous` 的对照说明）。 -/
def UndeterminedByWill {O A : Type*} (R : O → A → Prop) (o : O) : Prop :=
  ∀ g₁ g₂ : Gaze, g₁ ≠ Gaze.none → g₂ ≠ Gaze.none →
    gazeCapture R o g₁ = gazeCapture R o g₂

/-- ⭐ **`UndeterminedByWill` 的【非空洞性】证据**：
该谓词**不是恒真**的 —— 存在 `R`, `o` 使其**为假**。

⚠ 这条**必须存在**：否则 `UndeterminedByWill` 可能是「恒真的空壳」。
⭐ **构造（关键的「反向」检验）**：把 `gazeCapture` 换成一个**读 `g` 的**探针
（`up ↦ some True`、`down ↦ some False`），则两个已投方向给出**不同**结果
⟹ 「受动」**为假** ⟹ 说明**受动性真的是一条约束**，
不是在定义里被**保证**掉的（若 `gazeCapture` 的定义使 `up`/`down` 必然同值，
那受动性就是**空话** —— 本条排除了这一误读）。 -/
theorem undeterminedByWill_not_vacuous :
    ¬ (∀ g₁ g₂ : Gaze, g₁ ≠ Gaze.none → g₂ ≠ Gaze.none →
        (match g₁ with | Gaze.none => none
                       | Gaze.up => some True
                       | Gaze.down => some False) =
        (match g₂ with | Gaze.none => none
                       | Gaze.up => some True
                       | Gaze.down => some False)) := by
  intro h
  -- ⚠ 不能用 `decide`：目标是 `Option Prop` 的相等，其 `Decidable` 走
  -- `Classical.choice`（`Prop` 的判定一般不可计算）⟹ `decide` 会卡住（实测）。
  -- ⇒ 显式取 `g₁ := up`、`g₂ := down`，两边分别是 `some True` 与 `some False` ⟹ 矛盾。
  have h0 := h Gaze.up Gaze.down (by decide) (by decide)
  -- `h0 : some True = some False`（`Option Prop`）
  -- ⟹ `Option.some.injEq` 给出 `True = False`（**Prop** 等式）⟹ 用 `True` 的证明得到 `False`。
  rw [Option.some.injEq] at h0
  exact h0 ▸ trivial

/-- ⭐ **A2 向上侧主条：上位捕获【被论域的关系网络承受】，不被方向决定。**

法则 4：「向上：上位关系是否存在，**由选定论域的关系网络约束**。」

⇒ 形式化：**两个已投方向**（`up` 与 `down`）的**捕获内容完全相同** ——
即结果**不由「投哪个方向」决定**，而**只依赖 `D.rel`**。

⭐⭐ **这条同时给出「能动」与「受动」的分界**：
- **能动**：投哪个方向、投不投（`g` 自由）；
- **受动**：**捕获的内容与 `g` 无关**（两侧是同一个 `Option Prop` 值）。

⚠ **诚实标注**：本条的证明只需对 `Gaze` 的三个构造子做情形分裂
（`up`/`down` 分支**都**读 `hasUpper R o`）——
即**「受动」在本形式化下是【定义性】的**（`gazeCapture` 的定义使 `up`/`down` 同值）。
⭐ 但其价值在**陈述**：它把「你决定看，但看到的不完全由你决定」
变成一条**可反驳**的命题（若 `gazeCapture` 对 `up`/`down` 给不同值，本条即假 ——
`undeterminedByWill_not_vacuous` 正是这种「可反驳」的对照）。 -/
theorem up_gaze_content_is_passive (D : Domain) (o : D.Obj) :
    UndeterminedByWill D.rel o := by
  intro g₁ g₂ h₁ h₂
  -- `gazeCapture` 对 `none` 给 `none`，对 `up`/`down` **都**给 `some (hasUpper …)`。
  -- 前提 `h₁`/`h₂` 排除了 `none`，故两侧必然是同一个表达式。
  cases g₁ <;> cases g₂ <;> simp_all [gazeCapture]

/-- ⭐ **A2 的「接入」条：构成不是凭空创造。**

法则 4：「**构成不是凭空创造**，是将给定物**接入**由论域和对象结构
**共同提供**的关系脉络。」

⇒ 形式化：向下目光「拆出」的 `B` **必须**满足 `∀ a ∈ B, R o a`
—— 即**拆出物一定已在关系脉络里**，拆不出脉络外的东西。

⭐ **这就是「接入」的形式内容**：`extent` 的成员条件**就是**「可接入性」。 -/
theorem down_gaze_content_is_constrained (B : Set A) (o : O) (h : o ∈ extent R B) :
    ∀ a ∈ B, R o a :=
  split_immediately_confers_concept R B o h

/-- ⭐ **A2 的「成败被承受」条：拆不出时【不是主体的失败，是结构的约束】。**

法则 4：「接入的**动作是主体的**，接入的**成败与内容则被承受**。」

⇒ 形式化：主体**可以**投出向下目光（`g := down`，能动），
但**能否拆出 `B`** 由 `R` 决定 —— 若 `o ∉ extent R B`，
则**无论主体怎样想拆**都拆不出（受动）。

⭐ **本条把「成败」与「内容」分开**：
「成败」= `o ∈ extent R B` 是否成立（被 `R` 承受）；
「动作」= 投出 `g := down`（主体能动的部分）。 -/
theorem down_gaze_outcome_is_passive (B : Set A) (o : O) :
    (o ∈ extent R B) ↔ (∀ a ∈ B, R o a) :=
  split_iff_all R B o

/-- ⭐⭐ **A2 的结构条：受动是【内在纹理】，不是【边界处的例外】。**

体系法则 4 末句（**极重要的一句**）：

> 这一受动维度**不是边界处的例外，而是每一目光操作的内在纹理**。

⇒ 形式化：**对每一对已投方向**，捕获内容**都相同** ——
即「受动」**不是**某个特殊方向的特权，而是 `up`/`down` **共同的**性质。

⭐⭐ **形式内容**：量词**落在 `g₁`,`g₂` 上**（它们出现在**被比较的两侧**），
故「没有豁免受动的（已投）方向」**不是空话**
—— 它是对 `{up, down} × {up, down}` **全部四种组合**的断言。 -/
theorem passivity_is_internal_texture (D : Domain) (o : D.Obj)
    (g₁ g₂ : Gaze) (h₁ : g₁ ≠ Gaze.none) (h₂ : g₂ ≠ Gaze.none) :
    gazeCapture D.rel o g₁ = gazeCapture D.rel o g₂ :=
  up_gaze_content_is_passive D o g₁ g₂ h₁ h₂

/-- ⭐ **A2 的合流条：能动的动作 + 受动的内容【同时】成立。**

法则 4：「**你决定看，但你看到的不完全由你决定。**」

⚠ 本条是本节的**总结陈述**：
- **能动**：∃ `g`（主体可选定目光方向）；
- **受动**：∀ **已投**的 `g₁ g₂`，捕获内容相同（结果不被动方向决定）。

⭐⭐ **两个量词的【型】不同**（`∃` vs `∀`），
这**正是**「你决定」与「不完全由你决定」的**逻辑形状差异** ——
**能动的自由度体现为 `∃`，受动的约束体现为 `∀`。** -/
theorem active_choice_passive_content (D : Domain) (o : D.Obj) :
    (∃ g : Gaze, g = Gaze.up ∨ g = Gaze.down) ∧
    (∀ g₁ g₂ : Gaze, g₁ ≠ Gaze.none → g₂ ≠ Gaze.none →
      gazeCapture D.rel o g₁ = gazeCapture D.rel o g₂) :=
  ⟨⟨Gaze.up, Or.inl rfl⟩, up_gaze_content_is_passive D o⟩

/-- ⭐ **A2 与 A1 的依赖条（第一层解锁第二层的机器证据）。**

法则 4 的受动性**需要论域**（「由选定论域的关系网络约束」）——
⇒ 形式化：**受动性命题以 `Domain` 为参数**，
**去掉 `Domain` 就无法陈述**（因为没有 `rel` 可谈约束）。

⭐ 本条**替代**「A1 是 A2 的前提」这一**元层断言**：
它把该断言变成**类型层面的可见事实**（`D : Domain` 出现在签名里）。 -/
theorem passivity_requires_domain (D : Domain) (o : D.Obj) :
    UndeterminedByWill D.rel o ∧ (∀ a : D.Attr, D.rel o a → D.rel o a) :=
  ⟨up_gaze_content_is_passive D o, fun _ h => h⟩

/-! ## 未做（诚实登记）

| 项 | 状态 | 理由 |
|:--|:--|:--|
| 「**分化之根据**」的对象化（边界 3 / C2 类） | ❌ **不做** | 原文自陈「不可对象化陈述其根据」——**任何声称形式化了它的定理都是伪造** |
| 「**操作论域**」做成类型（边界 1/4） | ❌ **不做** | 对象化它「已在其之中进行」⟹ 做成类型是**范畴错误**。本文件只形式化**选定**论域 |
| 「第三层：觉照」（C1 类） | ❌ **不做** | 原文自陈「**当场不可条款化**」 |
| `Gaze` 上的**完整 FCA 实例**（`R : Gaze → Gaze → Prop` + 概念格） | ⚠ **未做** | A3 只做「目光可作对象」+「两种自指情形的身份」；**目光论域的概念格**不在范围 |
| 受动性的「**必然性**」（主体意志完全不起作用） | ⚠ **不声称** | 本文件只证「结果不由 `gaze` 决定」这一**可证侧面** |
| 第 4 步：纤维 + `canonicalize` | ⚠ **未做** | 承 `RealTemporalLayer`：★★★ 真工作，需先选定代表元 |
| 公设 (a)–(e) 的「证明」（B1） | ❌ **不做** | 它们是**前提**，不是定理（承 `RealTemporalLayer` §未做） |

⚠ **本文件【不】声称对缺口 A/B 有任何改善**：严格可逆仍为假
（`no_extractor_preserves_both`），本文件是**时态层元层的形式化补完**，
不是转位本身。 -/

end Lattice
