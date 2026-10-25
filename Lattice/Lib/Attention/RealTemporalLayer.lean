import Lattice.Lib.FCA.RealFCA
import Mathlib

/-!
# LATTICE: 时态层 —— 「目光」状态与要素/概念的身份时态性

本文件实现 `FCA的拓展与补足.md` §6.1 的最小可行路径（MVP）的
**第 1、2、3、5 步**（全部 ★ 级、零新数学）。第 4 步（纤维 + canonicalize
+ 三性质，★★★）**不在本文件范围内**，见文末「未做」。

设计蓝本：`原始思想-时态性层级体系.md`（思想构件原文）。
本文件把该体系的**概念层之外的那一层**补进 FCA：**要素层 + 目光（时态）**。

## 本文件建立的内容

  1. `Gaze`：目光状态（未投 / 向上 / 向下）—— 公设 (e) 的**给定**，非导出；
  2. `Temporal`：基底 + 目光的二元组。**基底不随目光改变**（体系原理 1）；
  3. `IsElement` / `IsConcept`：要素 = 目光未投，概念 = 至少被一种目光捕获；
     `element_concept_complement`：**「要素是目光不在场的概念，概念是目光在场的
     要素」的逐字形式化**；
  4. `gazeUp` / `gazeDown`：两种目光**接**到既有的 `intent` / `extent`
     （零新证：`rfl`）；
  5. `galois_connection_temporal`：**已证的** `galois_connection` 在时态框架下
     **可直接复用**（把伴随性「接进来」，不是重证）；
  6. `split_immediately_confers_concept`：体系 4.2「向下目光的秘密归类」——
     **拆分的动作本身携带无法卸载的归类**，在 FCA 里是**定义性**的
     （`extent` 的定义体已经内含归类）；本文件进一步给出**恰好刻画**：
     拆分性 ⟺ 整体性（`split_iff_all`），即体系 4.3「同一法则」的机器证据；
  7. `hasUpper` / `isElementUnderUpGaze` / `element_iff_no_upper`：体系 4.1
     「存在论域内的上位，那就是概念。没有上位，就是要素」。
  8. `suspend`：悬置（法则 5）—— 撤回目光，概念退回要素。
     **对象还在（`suspend_preserves_base`），身份消解（`suspend_dissolves_identity`）**；
     并给出**往返律**：投出后再撤回 = 从不曾投出（`suspend_after_withGaze` /
     `suspend_idempotent`）—— 体系「撤回不是遗忘，是不再持有那束投出的目光」。

## 诚实边界（本文件不证 / 不声称的）

- ⚠ **本文件的映射是【解读】，不是体系原文**（提案 §7.3）：体系原文**未提 FCA**。
  本文件的映射（**向上目光 ↔ `intent`**、**向下目光 ↔ `extent`**）是**分析者的解读**，
  **其正确性由映射后的可证性验证，不由原文权威保证**。
  ⇒ 具体地：`gazeUp` / `gazeDown` 是 `intent` / `extent` 的**重命名**（`rfl` 级），
  它们**不证明** FCA 的 `intent` 就是体系所说的「向上目光」——
  只证明**若接受该解读**，则下文诸命题成立。
- ⚠ **不试图「证明」体系的公设 (a)–(e)**（提案 §7.2）：**它们是前提，不是定理**。
  `Gaze` 是**给定的**（对应公设 (e)「认知主体能执行意向切换」），
  **不是导出的**，与 mathlib 里 `Decidable` / `Nonempty` 作为类型类前提同构。
- ⚠ **不形式化「论域本身 / 操作论域 / 目光自指」**（提案 §6.1 明列「不做」）：
  体系自认边界（边界 1/3/4）。**尤其**：`Gaze` **不带论域参数** ——
  这是**显式选择「目光是外部的」**（`实现拓展后还剩哪些问题.md` 新问题 3），
  是**登记为边界**的**抉择**，不是被解决的问题。
- ⚠ **本文件不涉及缺口 A/B 的补足**（第 4 步的纤维 + `canonicalize`）：
  **未做**。本文件**不声称**可逆性有任何改善；`no_extractor_preserves_both`
  依旧成立（提案 §7.1：补足是**转位**，不是消除）。
- ⚠ **构成效力（体系边界 2「归类具有构成效力」）在本文件里是【定义性的】**：
  `split_immediately_confers_concept` 之所以成立，是因为 `extent` 的定义体
  **已经要求 `o` 与 `B` 建立关系**（提案 §拓展 4）——
  **本文件把这一点显式化，并不声称「证明了」构成效力本身**。
  体系的元裁决（法则 4）**依旧不可内证**。

无 sorry / axiom / admit / native_decide；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 一、目光状态与基底（拓展 1）

体系原理 1：「在任一选定论域内，『是要素』或『是概念』并非对象的固有属性，
而是认知目光是否落在其上所构成的功能状态。身份随目光的投出与撤回而转化，
**不涉及基底变更**。」 -/

/-- **目光状态**：未投 / 向上 / 向下（体系 4.4「目光在『不投、向上、向下』之间切换」）。

⚠ **这是【给定的】，不是【导出的】** —— 对应公设 (e)「认知主体能执行意向切换：
目光方向的分化」。体系边界 3 声明「分化的根据不可陈述」⟹ 本类型**不带论域参数**
（显式选择「目光是外部的」），**登记为边界**而非声称已解决（提案 §7.2）。 -/
inductive Gaze where
  | none : Gaze
  | up : Gaze
  | down : Gaze
  deriving DecidableEq, Repr

/-- **时态化的呈现**：同一基底，随目光呈现不同身份（体系原理 1「同一张脸」）。

`base` 是**基底**（不随目光改变），`gaze` 是**当前目光**。
`R` 是满足关系（论域的关系网络），作为参数保留以承载论域 —
⚠ 它**不是** `Temporal` 的字段（`Temporal` 只记录「哪个对象、当前什么目光」）。 -/
structure Temporal (O A : Type*) (R : O → A → Prop) where
  /-- 基底：对象本身，不随目光改变（体系原理 1「对象本身什么都没变」）。 -/
  base : O
  /-- 当前目光。 -/
  gaze : Gaze

/-! ## 二、目光投出 / 撤回（体系 4.4 的转化通道）

「要素 —(目光投出)→ 概念」「概念 —(目光撤回)→ 要素」。 -/

/-- **投出目光**（或换成另一种目光）：基底不变，只改目光。

⚠ 定义在 `Temporal` 的**命名空间**下（`Temporal.withGaze`），
用点记法 `t.withGaze g` 调用。 -/
def Temporal.withGaze (t : Temporal O A R) (g : Gaze) : Temporal O A R :=
  { base := t.base, gaze := g }

/-- ⭐ **体系原理 1 的形式化（「同一张脸」）**：身份随目光转化，**不涉及基底变更**。

⚠ 该命题本身是 `rfl` 级（平凡），**但它必须被【陈述】** ——
现行 FCA **连陈述都做不到**（`RealFCA.lean` 全 19 条签名均为 `{O A : Type*}`，
**没有 `base` 与 `gaze` 的区分**）。提案 §拓展 1 已明记这一点。 -/
theorem gaze_switch_preserves_base (t : Temporal O A R) (g : Gaze) :
    (t.withGaze g).base = t.base := rfl

/-- 目光切换只改目光（与基底对偶的一条，同 `rfl` 级）。 -/
theorem gaze_switch_sets_gaze (t : Temporal O A R) (g : Gaze) :
    (t.withGaze g).gaze = g := rfl

/-- 投出目光**不改变**基底所对应的对象：`withGaze` 保持 `base` 的函数性。 -/
theorem withGaze_base_eq_self (t : Temporal O A R) : t.withGaze t.gaze = t := by
  cases t
  rfl

/-! ## 三、要素与概念的定义（拓展 2）

体系 2.2：「**要素** —— 尚未被任何目光所捕获的给定物。」
「**概念** —— 已被至少一种目光捕获的给定物。」 -/

/-- **要素**：目光未投（尚未被任何目光捕获）。 -/
def IsElement (t : Temporal O A R) : Prop := t.gaze = Gaze.none

/-- **概念**：至少被一种目光捕获（向上或向下）。 -/
def IsConcept (t : Temporal O A R) : Prop :=
  t.gaze = Gaze.up ∨ t.gaze = Gaze.down

/-- ⭐ **体系原话「要素是目光不在场的概念，概念是目光在场的要素」的逐字形式化**。

「不是说要素『潜在是概念』，而是对象本身什么都没变——变的只是目光在不在。」
⇒ 要素与概念**恰好互补**，且**穷尽**三种目光状态（`Gaze` 只有三个构造子）。 -/
theorem element_concept_complement (t : Temporal O A R) :
    IsElement t ↔ ¬ IsConcept t := by
  obtain ⟨b, g⟩ := t
  cases g <;> simp [IsElement, IsConcept]

/-- 对偶方向：非概念 ⟺ 要素（`element_concept_complement` 的 `Not` 形式）。 -/
theorem not_concept_iff_element (t : Temporal O A R) :
    ¬ IsConcept t ↔ IsElement t :=
  (element_concept_complement t).symm

/-- **三态穷尽**：任一时刻，呈现**要么**是要素、**要么**是概念（无第三态）。 -/
theorem element_or_concept (t : Temporal O A R) :
    IsElement t ∨ IsConcept t := by
  obtain ⟨b, g⟩ := t
  cases g <;> simp [IsElement, IsConcept]

/-- **互斥**：不能同时是要素与概念（互补性的另一半）。 -/
theorem not_element_and_concept (t : Temporal O A R) :
    ¬ (IsElement t ∧ IsConcept t) := by
  obtain ⟨b, g⟩ := t
  cases g <;> simp [IsElement, IsConcept]

/-! ## 四、两种目光 = `intent` / `extent`（拓展 3，★ 零新证）

⚠ **以下是解读的落地，不是原文的证明**（提案 §7.3）：
把 `gazeUp` / `gazeDown` **定义为**既有 FCA 算子 `intent` / `extent`
（`RealFCA.lean:34-38`）——「向上目光：追问『它归于何类』」对应
「对象集 → 共享属性集」；「向下目光：追问『它由何构成』」对应
「属性集 → 满足它的对象集」。 -/

/-- **向上目光**：追问「它归于何类」——建立上位归类。= `intent`（已有）。

⚠ 本定义是 `rfl` 级重命名；**它不证明** FCA 的 `intent` 就是体系的向上目光。 -/
def gazeUp {O A : Type*} (R : O → A → Prop) (O' : Set O) : Set A := intent R O'

/-- **向下目光**：追问「它由何构成」——建立内部构成。= `extent`（已有）。 -/
def gazeDown {O A : Type*} (R : O → A → Prop) (B : Set A) : Set O := extent R B

/-- 两种目光的方程（定义性，机器核对「= 既有算子」）。 -/
theorem gazeUp_eq_intent {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    gazeUp R O' = intent R O' := rfl

/-- 向下目光 = `extent`（同上）。 -/
theorem gazeDown_eq_extent {O A : Type*} (R : O → A → Prop) (B : Set A) :
    gazeDown R B = extent R B := rfl

/-- ⭐ **伴随性在时态框架下可直接复用**（体系 4.3「同一法则」/ 提案 §拓展 3）。

**这不是重证** —— 它是**已证的** `galois_connection`（`RealFCA.lean:71-79`）
在 `gazeUp` / `gazeDown` 记法下的**直接引用**（`gazeUp` / `gazeDown` 与
`intent` / `extent` 是 `rfl` 级相等的，故可 `exact`）。
⇒ 两种目光是**一组伴随**：`向上` 是 `向下` 的右伴随（反变）。 -/
theorem galois_connection_temporal {O A : Type*} (R : O → A → Prop)
    (O' : Set O) (B : Set A) :
    O' ⊆ gazeDown R B ↔ B ⊆ gazeUp R O' :=
  galois_connection R O' B

/-- 两种目光的**扩张**（闭包性质，直接复用 `subset_extent_intent`）：
对象集含于「向下看再向上看」的结果。 -/
theorem subset_gazeDown_gazeUp {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    O' ⊆ gazeDown R (gazeUp R O') :=
  subset_extent_intent R O'

/-- 属性集的扩张（对偶，复用 `subset_intent_extent`）。 -/
theorem subset_gazeUp_gazeDown {O A : Type*} (R : O → A → Prop) (B : Set A) :
    B ⊆ gazeUp R (gazeDown R B) :=
  subset_intent_extent R B

/-! ## 五、向下目光的秘密归类（体系 4.2，拓展 4 ★★）

体系论证：「**拆分的动作本身携带了一个无法卸载的归类——拆出之物，被归入
『构成成分』**。这个归类不是拆分之外的第二步。它就是拆分的内在结构。」

⇒ **形式化后果**：`extent` 的定义（`∀ a ∈ B, R o a`）**本身就构成「部分」这个身份**，
**不需要额外一步**。 -/

/-- ⭐ **拆分性即概念性**（体系 4.1「拆分性即概念性」/ 4.2 秘密归类）。

「`o` 可被拆出（在向下目光下呈现为概念，其构成是 `B`）」**就是**
「`o` 与 `B` 中每一成分都已有关系 `R`」——**这一步是定义性的**，
即**拆分的瞬间**（而非拆分之后）就已完成归类。

⚠ **诚实标注**：本命题**平凡**（它就是 `extent` 的成员定义展开），
其价值**不在难度而在【陈述】**：体系说的「秘密归类」在 FCA 里**是定义性的**，
本条把这一点**显式化**。它**不声称**证明了体系边界 2 的「构成效力」。 -/
theorem split_immediately_confers_concept {O A : Type*} (R : O → A → Prop)
    (B : Set A) (o : O) (h : o ∈ extent R B) : ∀ a ∈ B, R o a := h

/-- ⭐ **恰好刻画**：`o` 落在「构成是 `B`」之内 ⟺ `o` 与 `B` 的**每一**成分都有关系。

这是 `split_immediately_confers_concept` 的**逆**，两者合起来给出
**拆分性的充要条件** —— 对应体系 4.2 末句：
「**这就是为什么拆分性能直接作为概念性的充要条件**」。

注：本命题按 `extent` 的定义（以及 `Set` 的成员记法）**定义性成立**。 -/
theorem split_iff_all {O A : Type*} (R : O → A → Prop) (B : Set A) (o : O) :
    o ∈ extent R B ↔ ∀ a ∈ B, R o a :=
  Iff.rfl

/-- **拆分给出身份（向上）**：向下拆出之物，同时获得向上目光的身份 ——
`B` 中的每个成分都在「`o` 的构成」里，故 `B ⊆ gazeUp R (gazeDown R B)`。

体系 4.3：「向下目光把对象打开，拆出物随即暴露在新的目光之下 ——
它们可以继续被追问归属，或继续被分解。」 -/
theorem split_exposes_parts_to_upward_gaze {O A : Type*} (R : O → A → Prop)
    (B : Set A) : B ⊆ gazeUp R (gazeDown R B) :=
  subset_gazeUp_gazeDown R B

/-! ## 六、要素的判据：无上位（体系 4.1，拓展 3 末段）

体系原话：「**存在论域内的上位，那就是概念。没有上位，就是要素。**
一个东西目前是要素，仅仅因为你还没有总结出他的上位。在那个当下，它的确就是要素。」 -/

/-- **有上位**：在选定论域内，`o` 与至少一个属性/上位 `a` 有关系（`R o a`）。 -/
def hasUpper {O A : Type*} (R : O → A → Prop) (o : O) : Prop := ∃ a : A, R o a

/-- **向上目光下呈现为要素**：该论域内**找不到**上位归类（体系 4.1 向上目光的
「若找不到 → 对象呈现为要素」）。

注：这是体系 4.1 的**直接读法** —— 向上目光的判据只依赖 `∃ a, R o a`，
故本定义在形式上是 `¬ hasUpper R o`。 -/
def isElementUnderUpGaze {O A : Type*} (R : O → A → Prop) (o : O) : Prop :=
  ¬ hasUpper R o

/-- **向上目光下呈现为概念**：找到了上位归类（体系 4.1「若在该论域中找到上位归类
→ 对象呈现为概念」）。 -/
def isConceptUnderUpGaze {O A : Type*} (R : O → A → Prop) (o : O) : Prop :=
  hasUpper R o

/-- ⭐ **「为什么某物是要素」是一个可证命题**（提案 §用途 3）：

「无上位 ⟺ 要素」。⚠ **诚实标注**：本命题是 `Iff.rfl`
（因为 `isElementUnderUpGaze` **就是** `¬ hasUpper` 的定义）。
**它的价值在【陈述】而非难度**：体系给出了「要素」的**可判定判据**，
但**现行 FCA 连这个谓词都没有**（`RealFCA.lean` 无「要素」层）。
⇒ 「为什么某物是要素」由此**不再是无从表述的**，而**成为可陈述、可证、可反驳的命题**。 -/
theorem element_iff_no_upper {O A : Type*} (R : O → A → Prop) (o : O) :
    isElementUnderUpGaze R o ↔ ¬ hasUpper R o :=
  Iff.rfl

/-- 向上目光的**三态穷尽**：要么找到上位（概念），要么找不到（要素）。

注：`isElementUnderUpGaze` / `isConceptUnderUpGaze` 是 `¬ hasUpper` / `hasUpper`
的**定义别名**（`exact` 不做定义展开），且展开后 `simp` 会把析取**重排**；
为**避开重排与顺序的耦合**，本证明直接用 `by_cases`，不依赖 `em` 的析取顺序。 -/
theorem up_gaze_element_or_concept {O A : Type*} (R : O → A → Prop) (o : O) :
    isElementUnderUpGaze R o ∨ isConceptUnderUpGaze R o := by
  by_cases h : hasUpper R o
  · exact Or.inr h
  · exact Or.inl h

/-- 向上目光下，要素与概念**互斥**。 -/
theorem up_gaze_not_both {O A : Type*} (R : O → A → Prop) (o : O) :
    ¬ (isElementUnderUpGaze R o ∧ isConceptUnderUpGaze R o) := by
  simp only [isElementUnderUpGaze, isConceptUnderUpGaze, not_and]
  exact fun h => h

/-- **「向上无上位」⟺「向下拆不出任何非空构成」**：
`o` 在论域内无任何上位，**当且仅当**对**任意非空**属性集 `B`，`o` 都不落在 `B` 的构成里。

⚠ **陈述里的「非空」不可省**：`extent R ∅` 对**任意** `o` 都成立
（`∀ a ∈ ∅, R o a` **空洞为真**）⟹ 去掉非空性后命题**为假**。
这正是 STYLE 反复登记的「前提的不满足性会导致空洞」的同族现象，此处**显式排除**。

⚠ ⭐ **本命题是本文件的一个独立发现**（见文末「发现」）：
在 FCA 的读法下，`hasUpper R o` 与「存在非空可拆的 `B`」是**同一个命题**
（`extent` 的定义即 `∀ a ∈ B, R o a`，故 `o ∈ extent R B` 对某个非空 `B`
成立 ⟺ 存在 `a` 使 `R o a`）。

⇒ 这不支持「两种目光有差异」，反而给出**两者的一致性**：
**「无上位」在两种目光下说的是同一件事**（在非空构成的意义上），
这独立印证了体系 4.3「**投向即构成。这是两种目光的共同本质。**」 -/
theorem no_upper_iff_no_split {O A : Type*} (R : O → A → Prop) (o : O) :
    isElementUnderUpGaze R o ↔ ∀ B : Set A, B.Nonempty → o ∉ extent R B := by
  constructor
  · -- 无上位 ⟹ 任意非空 B 都拆不出
    intro h B hB ho
    obtain ⟨a, ha⟩ := hB
    exact h ⟨a, ho a ha⟩
  · -- 非空可拆 ⟹ 有上位（取单点集即得）
    intro h
    rintro ⟨a, ha⟩
    exact h {a} ⟨a, Set.mem_singleton a⟩ (fun b hb => by
      rw [Set.mem_singleton_iff] at hb
      rwa [hb])

/-! ## 七、悬置（法则 5，拓展 5 ★）

体系法则 5 原文：
> **撤回目光，概念退回要素。不是拆解了内部结构，不是否定了上位归类，
> 而是切断了关系持有。对象还在，身份消解。** -/

/-- **悬置**：撤回目光，从概念退回要素（法则 5 的转化通道）。 -/
def suspend (t : Temporal O A R) : Temporal O A R := t.withGaze Gaze.none

/-- ⭐ **法则 5 的「对象还在」**：悬置**不改变基底**。 -/
theorem suspend_preserves_base (t : Temporal O A R) : (suspend t).base = t.base := rfl

/-- ⭐ **法则 5 的「身份消解」**：悬置后**必定**呈现为要素。 -/
theorem suspend_dissolves_identity (t : Temporal O A R) : IsElement (suspend t) := rfl

/-- **悬置并非拆解**：悬置后的对象与原来**是同一个基底**
（「不是拆解了内部结构，不是否定了上位归类」）。 -/
theorem suspend_not_decomposition (t : Temporal O A R) :
    (suspend t).base = t.base := suspend_preserves_base t

/-- ⭐ **往返律（撤回不是遗忘）**：投出目光后再悬置 = 从不曾投出。

体系：「**撤回不是遗忘，是不再持有那束投出的目光。**」
⇒ 投出-撤回是**幂等闭合**的：`suspend (t.withGaze g) = suspend t`
（因为 `suspend` 把目光**无条件**置为 `none`）。 -/
theorem suspend_after_withGaze (t : Temporal O A R) (g : Gaze) :
    suspend (t.withGaze g) = suspend t := rfl

/-- **悬置幂等**：悬置两次 = 悬置一次。 -/
theorem suspend_idempotent (t : Temporal O A R) : suspend (suspend t) = suspend t := rfl

/-- **悬置消去一切身份**：悬置后既非向上概念也非向下概念。 -/
theorem suspend_not_concept (t : Temporal O A R) : ¬ IsConcept (suspend t) := by
  simp [IsConcept, suspend, Temporal.withGaze]

/-- **悬置的普遍性**：悬置结果与悬置前的目光**无关**（撤回切断了目光的持有，
但**没有**切断基底）。 -/
theorem suspend_depends_only_on_base (t₁ t₂ : Temporal O A R) (h : t₁.base = t₂.base) :
    (suspend t₁).base = (suspend t₂).base := by
  rw [suspend_preserves_base, h, suspend_preserves_base]

/-! ## 八、注：本文件与既有文件的衔接

- **不修改 `RealFCA.lean`**（提案 §C6-a：独立新文件，有 `EReal` 迁移先例）；
- 本文件**只 import** `RealFCA`，把「目光」作为**新的一层**加上去，
  `intent` / `extent` / `galois_connection` / `closure_idempotent` **原样复用**；
- ⚠ **命名注意**：`fiber` 在本库已存在（`RealStochasticProcess.lean:69`，
  `(π : α → β) (b : β) : Finset α`）。本文件**不使用**该名字；
  第 4 步的「要素的纤维」若实施，建议命名 `elementFiber`（避免同名不同义）。

## 九、⭐ 实现过程中的发现（对提案判断的核验）

以下五条是**在实现中实测得到的**，不是对提案的照做。
（发现 4/5 来自探针的真实编译诊断：`_probe_mvp1_x.log` 第 1–4 轮。）

### 发现 1：提案 §拓展 3 的 `element_iff_no_upper` **不是一条实质定理**

提案把它列为「用途 3：⭐ 解释并形式化『为什么是要素』」，并称
「**『为什么某物是要素』不再是玄学，而是一个可证命题**」。

⚠ **实测判定：该命题是 `Iff.rfl`** —— 因为 `isElementUnderUpGaze R o`
**按定义就是** `¬ hasUpper R o`（提案 §拓展 3 自己就是这么写的：
`def isElementUnderUpGaze ... := ¬ hasUpper R o`）。
⇒ **它不可能有别的证法，也不可能被反驳**：它**不含任何数学内容**，
是**定义的展开**，而非「可判定的判据」。

**但提案的更深判断仍然成立**（这才是要害）：
> **价值不在难度，在于【能否陈述】** —— 现行 FCA **连 `hasUpper` 这个谓词都没有**，
> 故「为什么某物是要素」**在此之前是无从表述的**。

⇒ ⭐ **精确化**：提案说这是「可证命题」，**严格说应表述为
「可陈述且可判定」**：「要素」由一个**可判定谓词**（`∃ a, R o a` 的否定）
定义，而**不是**由一个实质定理刻画。本文件的
`element_iff_no_upper` 因此**如实标注为 `Iff.rfl`**，不冒充定理。

### 发现 2：两种目光的「无上位」条件**是同一个条件**（不是两个）

体系 4.1 把「向上找不到上位」与「向下无可拆」表述为**两种目光的不同遭遇**。
本文件的 `no_upper_iff_no_split` 给出**机器证据**：在 FCA 的读法下，

  `¬ hasUpper R o`  ⟺  `∀ 非空 B, o ∉ extent R B`

⇒ **两者等价**。这意味着：**「要素」在两种目光下是同一个条件**，
而**不是**两种目光各有各的「要素」。这**独立印证了体系 4.3 的自我论断**：
「**投向即构成。这是两种目光的共同本质。**」——
体系说两者「共同本质」**只是断言**，而这里得到了**在 FCA 读法下的验证**。

⚠ **诚实边界**：这只是**在 FCA 读法下**的等价（因为 `extent` 的定义体
`∀ a ∈ B, R o a` **已经**把「构成」编码为「关系」）。它**不证明**体系
在任何其他读法下也如此。

### 发现 3：⭐ 提案的「★ 零新证」标注**正确**，但**易被误读**

提案 §6.1 把第 2 步标为「★，零新证」，并说「直接复用」。
**实测复核：这一判断正确**，但有一条**必须显式声明的限制**：

`gazeUp` / `gazeDown` 与 `intent` / `extent` 是 **`rfl` 级相等**的
（本文件的 `gazeUp_eq_intent` / `gazeDown_eq_extent` 是 `rfl`）。
⇒ 由 `galois_connection` **直接**得到 `galois_connection_temporal` 确实**零新证** ✅。

⚠ **但「零新证」的代价是：这一步【没有增加任何数学内容】** ——
`gazeUp` 只是 `intent` 的**又一个名字**。因此：

> ⭐ **「向上目光 = `intent`」这一步的全部价值在于【命名】与【可陈述性】，
> 而不在于【结论】。** 提案把这一步标为 ★ 并称「零新证」是**准确的**；
> 但**不应**被读成「FCA 已经（部分）实现了时态层」——
> **改名不构成实现**（这正是 `closed_loop_adds_nothing` /
> 「闭环是字段重命名」在**时态层内部**的**同构重现**）。

⇒ ⭐ **这是一个值得登记的一般模式**：
**「零新证」的步骤，其价值必须由【它使什么变得可陈述】来度量，
而不能由【它证了什么】来度量** —— 因为它**什么都没证**。

### 发现 4：⭐ 提案给出的 `element_concept_complement` **证明体本身不成立**

提案 §拓展 2 逐字给出：

```
theorem element_concept_complement (t : Temporal O A R) :
    IsElement t ↔ ¬ IsConcept t := by
  cases t.gaze <;> simp [IsElement, IsConcept]
```

⚠ **实测：该证明体【编译失败】**（探针 `_probe_mvp1_x.lean` 实测，报 3 条
`unsolved goals`）。**根因**：

> **`cases t.gaze` 只对「字段访问项 `t.gaze`」做情形分裂，
> 它【不会】把 `t` 本身改写/泛化** ⟹ 分裂后目标里**仍然出现 `t.gaze`**
> （未被具体构造子替换）⟹ `simp [IsElement, IsConcept]` 无从化简，
> 三个分支**全部留下未解目标**。

**正确写法**（本文件采用）：先**解构 `t` 本身**，再对目光分裂：

```lean
obtain ⟨b, g⟩ := t
cases g <;> simp [IsElement, IsConcept]
```

⚠ **这个坑值得单独登记**，因为它**恰好落在本仓库已登记的高频陷阱族里** ——
STYLE 的「`unfold … at *` 破坏 `omega` 原子对齐」、
「`rw` 是语法模式匹配」诸条，共同点是：
**tactic 作用的对象（句法项）与你想作用的对象（语义对象）不是同一个**。
`cases t.gaze` 与 `cases t` 的差别就是这一条在 `cases` 上的实例。

⚠ **诚实标注**：本发现**只针对提案稿件里的那一行证明体**，
**不影响**提案的**数学判断**（`element_concept_complement` 是**真命题**，
只是提案给的**证法**不成立）。这正是提案 §7.3 所说
「**映射的正确性由映射后的可证性验证**」的**一次实际兑现** ——
**可证性不仅检验映射，也检验载体代码**。

### 发现 5：⭐ 提案 §拓展 3 的 `def` 别名会导致**排中律也用不上**

提案把 `isElementUnderUpGaze` 写成 `def ... := ¬ hasUpper R o`（**定义别名**）。
**实测后果**（探针第二次，报 1 条 `type mismatch`）：

```lean
theorem up_gaze_element_or_concept : isElementUnderUpGaze R o ∨ isConceptUnderUpGaze R o :=
  em (hasUpper R o)          -- ⚠ 失败：类型是 hasUpper ∨ ¬hasUpper，不是目标类型
```

⇒ ⚠ **`exact` 不做定义展开**（`em` 给的是 `hasUpper ∨ ¬hasUpper`，
而目标写的是**两个 `def` 别名**）⟹ **必须显式展开**。
⚠ **但只加 `simp only` 仍不够**（探针第三次）：`simp` 会把展开后的析取
**重排**成 `¬hasUpper ∨ hasUpper`，与 `em` 的顺序**相反**，报第二条 `type mismatch`。

⇒ **最终解（本文件采用）：绕开析取顺序，直接用 `by_cases`**：

```lean
  by_cases h : hasUpper R o
  · exact Or.inr h
  · exact Or.inl h
```

⚠ **这与 STYLE 已登记的「`def` 别名是不透明的」同族**，但**新增了一个面**：
已登记的三种症状是 **点号投影失败 / `rw` 找不到模式 / `decide` 合成失败**；
**本条是第四种：`exact` 的类型检查不过**（因为目标里是别名、引理给的是展开形）。
⇒ **一般化**：**凡是「把 `hasUpper` 包一层 `def` 别名」的优雅写法，
都会在同一处把「定义展开」的责任转嫁给每个使用点** ——
这解释了为什么提案里
`element_iff_no_upper`（两边都是别名，`Iff.rfl` 可过）
与 `up_gaze_element_or_concept`（一边别名一边展开形，`em` 过不了）
**对定义展开的敏感度不同**。

⭐⭐ **且这条给出了一个可复用的一般教训**（本波次第三次实测）：
**「展开 + 归一化」两步法（`simp only [defs]` 再 `exact`）
会在 `∨`/`∧` 的**交换顺序**上再次失败** ——
因为 `simp` 有**自己的**规范序，而你手中的引理（`em`）
有**它的**固定序。⇒ **当目标里有可交换的连接词时，
用 `by_cases`/`rcases` 这类【不依赖顺序】的手段，比「展开后对齐」更稳。**

## 未做（诚实登记）

| 项 | 状态 | 理由 |
|:--|:--|:--|
| 第 4 步：纤维 + `canonicalize` + 三性质 | ⚠ **未做** | ★★★「真工作」，需先选定代表元；**不在本 MVP 范围** |
| 受动维度（拓展 8） | ⚠ **未做** | 需先形式化「论域关系网络」 |
| 目光自指（体系 4.4 / 拓展 9） | ❌ **不做** | 体系边界 3 自认**不可对象化** |
| 论域本身 / 操作论域 | ❌ **不做** | 体系自认边界（边界 1/4） |
| 公设 (a)–(e) 的「证明」 | ❌ **不做** | 提案 §7.2：**它们是前提，不是定理** |

⚠ **本文件【不】声称对缺口 A/B 有任何改善**：严格可逆仍为假
（`no_extractor_preserves_both`），本文件是**转位的准备**，不是转位本身。 -/

end Lattice
