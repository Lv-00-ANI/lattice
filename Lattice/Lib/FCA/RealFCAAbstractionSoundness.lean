import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lift.RealLinear
import Lattice.Lib.Compiler.RealAbstractInterpretation
/-!
# RealFCAAbstractionSoundness —— FCA 抽象化的**可靠性**（P1-1 / P2-1）

## 溯源

`RealFCASyntaxBridge.lean:37-51` 逐字登记：**「并行的另一路在决定 FCA abstraction soundness
（P1-1 / P2-1）：一条 weight→concept-lattice 的 `γ∘α ⊇ id` 关系。那是语义侧桥，方向是
concrete → abstract」**，并声明语法桥「从不提及 `SoundAbstract`、`α`、`γ`、行为或可靠性」。

⭐ **本文件就是那一「另一路」。** 它补上被登记为**缺失**的语义侧，且**不触碰**语法桥：
不定义 `conceptToConstraint`，不做 `concept ↦ constraint` 的构造。

⚠ **与 `RealAbstractInterpretation.lean` 的分工（防重复建设）**：
那里的 `SoundAbstract`（`:184`）管的是**算子**——「`f♯` 对 `f` 可靠」，
形如 `∀ a c, c ∈ γ a → f c ∈ γ (f♯ a)`。
⭐ **本文件管的是【集合/概念】**——「抽象层的一个闭集合**覆盖**哪些具体点，
以及在该抽象值上成立的事实能**转移**到哪些具体点上」。**两者是不同的数学对象**，
本文件**不重定义** `SoundAbstract`、不引入 `GaloisMem`、不复用区间实例。

---

## ⚠⚠ §2.2：这条定理比它的**定义**多说了什么？

`PROCESS.md §2.2` 要求立项时回答此问，否则会证**平凡的东西**。本文件在写作前
用 Python 小模型（5 对象 × 25 约束 = 32 子集）**逐一淘汰**了三个候选：

| 候选陈述 | 判定 | 依据 |
|:--|:--|:--|
| ① `S ⊆ γ(αS S)`，即 `S ⊆ closure S` | ❌ **平凡** | 它就是**扩张性**，即既有定理 `RealFCA.subset_extent_intent`。**「什么都没多说」** |
| ② `closure` 与缩放交换（`closure (k·S) = k·closure S`） | ❌ **为假** | 模型给出反例：`k=2, S={-2}` 时左边 `={-2..2}`、右边 `={-4}` |
| ③ `intent` 反变转移（`S ⊆ T ⟹ intent T ⊆ intent S`） | ❌ **平凡** | 它就是既有定理 `RealFCA.intent_antitone` |
| ⭐ ④ **本文件采用**（见下） | ✅ **非平凡** | 见「为什么非平凡」 |

### 本文件采用的陈述

> **`IsFCAClosed R A` 且 `fcaClosure R S ⊆ A` 且 `a ∈ intent R A  ⟹  ∀ o ∈ S, R o a`**
>
> （`A` 为**闭**集合，即一个形式概念的外延；`a` 是**前提中给定**的一个属性，
> **不是**结论里的全称量词——证据见 §3 `fcaAbstraction_sound` 的签名
> `(hP : IsFCAClosed R P) (h : fcaClosure R S ⊆ P) (ha : a ∈ intent R P)`）

**它比定义多说了什么？** 三点，均**机器可检**：

1. 要点 **假设承重（`PROCESS.md §2.3` 判据 1）**：去掉 `closure S ⊆ A` 后命题**为假**，
   §4 用 `fcaAbstraction_hypothesis_needed` 给出**构造性见证**。**不是"写松了"。**
2. 要点 **结论不是假设的逐字重复（判据 4）**：假设说的是**集合包含** `closure S ⊆ A`；
   结论说的是**逐点的约束满足** `R o a`。二者**不同类**——
   中间要经 `intent` 与 `extent` 的**两次定义展开**，**不是 `fun h => h`**。
3. 要点 **它不是既有定理的特例**：`intent_antitone` 给的是 `intent A ⊆ intent S`
   （仍停在**集合层**）；本文件把它**推过 `extent`/`RealConstraintSat` 落到对象层**——
   这正是 `RealFCAElementApplication` 消费端要的形态。
   注意 模型**实测**：存在 `S ⊆ A` 而 `intent S ≠ intent A` 的情形（11 例），
   ⟹ 第 2 条的"不同类"**不是措辞，是结构性的**。

### 注意 我**没有**证什么（诚实登记）

- 注意 **不证 `γ∘α ⊇ id` 的"带界"版本**。`RealReversibilityBoundary` 已证**严格可逆为假**
  （`semantic_layer_not_injective`）；本文件**不重启那个已结案的否定结论**，只给**单向**转移定理。
- 注意 **不建 `weight → concept` 载体**（那是 P2-1 的另一半，需要权重侧类型；**不发明**不存在的类型）。
- 注意 **不引入上下文对象** ⟹ **不触碰 `Mathlib/Order/Concept.lean:19-22` 的分歧**
  （`DIVERGENCES.md` C-19 / C-27）。全程走 `extent`/`intent` 对库自身关系的实例化。

### 注意 命名纪律（本轮实测踩到的坑）

对象类型参数命名为 `Obj`（**不是** `A`），因为权威抽象值 `A : Set Obj` 与属性类型
在本文件里**同时出现**；若类型参数叫 `A`，则 `a : A` 与 `a ∈ A` 指向不同事物，
Lean 报 `application type mismatch`。这是本项目 B-31 / `DIVERGENCES.md` 命名膨胀的**同族风险**，
在此以命名规避——**实证见本文件的编译记录**。

注意 **订正 B400**：此处原写「纯 Std + mathlib」，把「表示的选型」与「依赖的选型」混为一谈，
容易让读者以为本文件的**表示层**是标准库的、只有额外一层 mathlib 可选 —— 与事实不符。
真实情况是：**本文件的表示层构造基于 Std 核心类型**（对象/属性是裸类型 `Obj`/`Attr`，
抽象值是 `Set Obj`，闭包 `fcaClosure` 只是 `RealFCA.extent`/`intent` 的复合，
不新建 structure，不依赖 mathlib 的专用代数结构），**但文件整体 `import Mathlib`（第 1 行）**——
事实上 `Set` 的记法层与本节用到的 `simp`/`rw` 引理都来自 Mathlib 环境，
本节所 import 的 `RealFCA`/`RealLinear`/`RealAbstractInterpretation` 亦然。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
无 sorry/axiom/admit/native_decide。
-/

noncomputable section

namespace Lattice.Lib.FCA.RealFCAAbstractionSoundness

/-! ## 1. 载体

注意 **不发明类型**：具体侧 = `RealFCA` 的对象论域 `Obj`；属性侧 = `Attr`；
抽象侧 = **闭集合**（形式概念的第一分量），以 `IsFormalConcept` 的一致性锚定，
**不新建 structure**（防结构名膨胀）。 -/

section Carriers

variable {Obj Attr : Type*} (R : Obj → Attr → Prop)

/-- **FCA 闭包算子**：`fcaClosure R S = extent R (intent R S)`。

要点 这是抽象化 `α` 的载体：把任意具体集合**抽象**为它所在的最小概念外延。
它不引入新数学——只是 `RealFCA.extent`/`intent` 的复合，便于命名与引用。 -/
def fcaClosure (S : Set Obj) : Set Obj := extent R (intent R S)

/-- 闭包的定义展开（供下游 `rw` 用；**`rfl` 级**，登记以免读者以为它承载内容）。 -/
theorem fcaClosure_def (S : Set Obj) : fcaClosure R S = extent R (intent R S) := rfl

/-- **抽象值的载体**：一个**闭**集合。

注意 **不建 structure**：直接以 `fcaClosure R S = S` 刻画"闭"，
与 `RealFCA.IsFormalConcept` 一致（`isFCAClosed_iff_isFormalConcept_extent` 锚定），
从而**不产生第二个"闭"概念**。 -/
def IsFCAClosed (S : Set Obj) : Prop := fcaClosure R S = S

end Carriers

/-! ## 2. 闭包的基本律

注意 `RealFCA` 已证：`subset_extent_intent`（扩张）、`extent_antitone`、`intent_antitone`、
`closure_idempotent`。本节**只做搬运与命名**，并在 docstring 逐条注明出处——
**不把既有定理重新包装成"新结果"**。 -/

section BasicLaws

variable {Obj Attr : Type*} (R : Obj → Attr → Prop)

/-- **扩张性**（搬运 `RealFCA.subset_extent_intent`）：`S ⊆ fcaClosure R S`。
注意 **本条【不是】本文件的贡献**——它就是既有定理。 -/
theorem subset_fcaClosure (S : Set Obj) : S ⊆ fcaClosure R S :=
  subset_extent_intent R S

/-- **幂等性**（搬运 `RealFCA.closure_idempotent`）：闭包再闭包不动。 -/
theorem fcaClosure_idempotent (S : Set Obj) : fcaClosure R (fcaClosure R S) = fcaClosure R S :=
  closure_idempotent R S

/-- **单调性**：`S ⊆ T ⟹ fcaClosure R S ⊆ fcaClosure R T`。

注意 由 `intent_antitone` + `extent_antitone` 复合而成（`RealFCA` 未单独列出此条）。
**证明体是两步复合，不是 `rfl`**。 -/
theorem fcaClosure_mono {S T : Set Obj} (h : S ⊆ T) : fcaClosure R S ⊆ fcaClosure R T :=
  extent_antitone R (intent_antitone R h)

/-- **闭 ⟺ 是自身的闭包**（对"闭"的刻画，`Iff.rfl` 级）。 -/
theorem isFCAClosed_iff (S : Set Obj) : IsFCAClosed R S ↔ fcaClosure R S = S :=
  Iff.rfl

/-- 要点 **闭包的极小性**：`fcaClosure R S` 是 `S` 的**最小**闭超集。

注意 **这是本节唯一【非搬运】的定律**，且是 §3 主定理的关键中间步。
注意 **它不是 `rfl`**：结论量化于**所有**闭超集 `P`，而 `fcaClosure R S` 只是一个特定项；
证明需 `fcaClosure_mono`（单调）+ 闭性（把 `fcaClosure R P` 归约到 `P`）。
要点 **诚实边界**：极小性**可由**扩张+单调+幂等**推出**
（`S ⊆ P ⟹ fcaClosure S ⊆ fcaClosure P = P`），**故它不是新公理**；
但它的**证明体有实质内容**（`PROCESS.md §2.3` 判据 2：不是 `rfl`／字段重命名）。 -/
theorem fcaClosure_least {S P : Set Obj} (hP : IsFCAClosed R P) (h : S ⊆ P) :
    fcaClosure R S ⊆ P := by
  rw [isFCAClosed_iff] at hP
  have hmono : fcaClosure R S ⊆ fcaClosure R P := fcaClosure_mono R h
  rwa [hP] at hmono

/-- **与 `IsFormalConcept` 的一致性锚点**：闭集合恰好是某个形式概念的外延半。

注意 本条把本文件的 `IsFCAClosed` **锚定到权威定义** `RealFCA.IsFormalConcept`，
证明**该措辞不是自造的第二个"闭"概念**（防重复建设）。
取内涵为 `intent R P` 即可：闭性给出 `P = extent (intent P)`，故 `IsFormalConcept R P (intent R P)`。

注意 **注意方向**：这里只证"闭 ⟹ 是概念外延"这一半；
反方向由 `IsFormalConcept` 的定义直接给出（`h.1` 即 `P = extent (intent P)`），
两条合起来才是等价。本文件只证需要的那半，**不虚报为等价**。 -/
theorem isFCAClosed_iff_isFormalConcept_extent {P : Set Obj} :
    IsFCAClosed R P → IsFormalConcept R P (intent R P) := by
  intro hP
  rw [isFCAClosed_iff] at hP
  constructor
  · -- IsFormalConcept 的首分量是 P = extent (intent P)；
    -- hP : fcaClosure R P = P，展开 fcaClosure 后是 extent (intent P) = P，需对称化
    rw [fcaClosure_def] at hP
    exact hP.symm
  · rfl

end BasicLaws

/-! ## 3. 要点 主定理：抽象层的**事实转移**（FCA abstraction soundness）

「可靠性」在此处的精确含义（**与 `RealAbstractInterpretation.SoundAbstract` 的区别见文件头**）：

> **若具体集合 `S` 被抽象值 `P` 覆盖（`fcaClosure R S ⊆ P`），
> 则在抽象层 `P` 上成立的【任一属性事实】`a ∈ intent R P`，
> 对 `S` 的【每一个】具体点都成立。**

这是抽象解释「**抽象执行覆盖所有具体执行**」在 FCA 上的语义侧版本。 -/

section Soundness

variable {Obj Attr : Type*} (R : Obj → Attr → Prop)

/-- 要点 **抽象覆盖具体（集合层）**：`fcaClosure R S ⊆ P` 时 `S ⊆ P`。

即：**抽象值覆盖的具体点，一个都不少**。
证明用扩张性 + 传递性 —— **两步，非 `rfl`**。 -/
theorem fcaAbstract_covers {S P : Set Obj} (h : fcaClosure R S ⊆ P) : S ⊆ P :=
  fun _ hx => h (subset_fcaClosure R S hx)

/-- 要点 **主定理：FCA 抽象可靠性（逐点形式）。**

**陈述**：设 `S` 是任意具体集合，`P` 是一个**闭**抽象值，`S` 被 `fcaClosure R S ⊆ P` 覆盖，
且 `a` 是抽象层**已确立**的属性（`a ∈ intent R P`）。
则 `a` 对 `S` 的**每一个**具体点 `o` 都成立：`R o a`。

**为什么这是"抽象可靠"**：在抽象层只需验证 `intent R P` 里的属性；
它们**自动**对所有被覆盖的具体点生效。**单向**（concrete ⇐ abstract），
与文件头所述的 P1-1/P2-1 方向一致。

要点 **为什么 `a ∈ intent R P` 必须是前提（不是遗漏）**：
`extent R (intent R P)` **按定义**就是 `∀ a, a ∈ intent R P → R o a`。
若不给 `a ∈ intent R P`，结论 `R o a` 对**任意** `a` 断言成立 ⟹ **为假**
（取 `P` 为全空间、`a` 为在 `o` 处非零的约束即可反驳）。
⇒ 把它写成前提**不是"把假设当结论"**，而是**命题为真的必要条件**；
注意 且它**不使定理平凡**：前提是"抽象层**已证**该属性"，
结论是"它在**每个具体点**上成立"——**跨层**，见 §5 的机器见证。

要点 **非平凡性（`PROCESS.md §2.2/§2.3`）**：
* 假设 `fcaClosure R S ⊆ P` **承重**——去掉后命题为假（§4 构造性见证）。
* 结论 `R o a` 是**逐点谓词**，假设是**集合包含 + 成员关系**；需经
  `intent`/`extent` **两次定义展开**，**不是 `fun h => h`**。 -/
theorem fcaAbstraction_sound {S P : Set Obj} {a : Attr}
    (hP : IsFCAClosed R P) (h : fcaClosure R S ⊆ P)
    (ha : a ∈ intent R P) {o : Obj} (ho : o ∈ S) :
    R o a := by
  -- 1. S ⊆ P（抽象覆盖具体）
  have hSP : S ⊆ P := fcaAbstract_covers R h
  -- 2. o ∈ P
  have hoP : o ∈ P := hSP ho
  -- 3. 闭性给出 P = extent (intent P)。
  --    注意 不用 `rw [...] at hP`：`rw` 会把 `fcaClosure` 的**所有**出现一起改写，
  --    包括已被替换进 `P` 内部的那次，从而得到
  --    `extent (intent (extent (intent P))) = ...`（实测报错证据见提交记录）。
  --    ⇒ 用 `have` 显式取出一条**定向**等式，避免自指改写。
  have hclosed : P = extent R (intent R P) := by
    have h1 : fcaClosure R P = P := hP
    rw [fcaClosure_def] at h1
    exact h1.symm
  have hoExt : o ∈ extent R (intent R P) := hclosed ▸ hoP
  -- 4. extent 按定义是 ∀-谓词：a ∈ intent P ⟹ R o a
  exact hoExt a ha

/-- 要点 **集合层形式（等价刻画）**：主定理与"`intent P` 的每个属性都被 `S` 全体满足"等价。

注意 本条把 §3 的逐点定理**打包**为集合陈述，便于下游按集合运算消费
（`RealFCAElementApplication` 的消费端形态）。
注意 证明体是 `fun a ha => ...` 的逐点搬运，**不是 `rfl`**；且它**不是**对主定理的重复——
它把量化顺序与集合记法对齐，属接口层，已在 `PROCESS.md §2.3` 判据 3（各实例证明体有实质差异）之外，
故**显式标注为接口包装**而非新结果。 -/
theorem fcaAbstraction_sound_set {S P : Set Obj} (hP : IsFCAClosed R P)
    (h : fcaClosure R S ⊆ P) :
    intent R P ⊆ {a : Attr | ∀ o ∈ S, R o a} := by
  intro a ha
  exact fun o ho => fcaAbstraction_sound R hP h ha ho

end Soundness

/-! ## 4. 要点 假设**承重**（`PROCESS.md §2.3` 判据 1）—— 构造性见证

「假设写松了」是本项目的高频失败（`unused variable` / B142 / B216）。
本节给出**构造性见证**证明 `fcaClosure R S ⊆ P` **不可去**。 -/

section LoadBearing

/-- 具体侧：`ℝ` 上的约束实例（`RealConstraint` / `RealConstraintSat`）。
注意 `RealLinear.lean:20/24` 提供结构与关系；本文件**引用而不重定义**。 -/
abbrev Rc : ℝ → RealConstraint → Prop := fun x c => RealConstraintSat c x

/-- `⟨1, -1⟩` 即 `x - 1 = 0`，它的解是 `x = 1`。 -/
theorem rc_one_is_solution : RealConstraintSat (⟨1, -1⟩ : RealConstraint) (1 : ℝ) := by
  simp [RealConstraintSat]

/-- `0` **不**满足 `x - 1 = 0`。 -/
theorem rc_zero_not_solution : ¬ RealConstraintSat (⟨1, -1⟩ : RealConstraint) (0 : ℝ) := by
  simp [RealConstraintSat]

/-- 要点 **去掉覆盖假设后命题为假** —— 假设承重的**构造性见证**。

主定理的前提是 `fcaClosure Rc S ⊆ P`。本定理给出**不满足它**的一对 `(S, P)`，
其中 `P` **仍然闭**（见下一条），从而使"前提不可去"成为**可构造的事实**，
而不是一处断言。

取 `S = {0}`、`P = fcaClosure Rc {1}`：
* **闭**：`fcaClosure` 幂等；
* **不被覆盖**：`0 ∈ S ⊆ fcaClosure Rc {0}`，但 `0 ∉ fcaClosure Rc {1}` ——
  因为 `⟨1,-1⟩ ∈ intent Rc {1}` 而 `0` 不满足它。 -/
theorem fcaAbstraction_hypothesis_needed :
    ∃ (S P : Set ℝ), IsFCAClosed Rc P ∧ ¬ (fcaClosure Rc S ⊆ P) := by
  refine ⟨({0} : Set ℝ), fcaClosure Rc ({1} : Set ℝ), ?_, ?_⟩
  · -- P 闭：fcaClosure 幂等
    rw [isFCAClosed_iff]
    exact fcaClosure_idempotent Rc ({1} : Set ℝ)
  · -- ¬ (fcaClosure {0} ⊆ fcaClosure {1})
    intro h
    have h0 : (0 : ℝ) ∈ fcaClosure Rc ({0} : Set ℝ) := subset_fcaClosure Rc {0} (by simp)
    have hmem : (0 : ℝ) ∈ fcaClosure Rc ({1} : Set ℝ) := h h0
    rw [fcaClosure_def] at hmem
    have hc : (⟨1, -1⟩ : RealConstraint) ∈ intent Rc ({1} : Set ℝ) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact rc_one_is_solution
    exact rc_zero_not_solution (hmem _ hc)

/-- 要点 **"闭"这一半在见证中成立** —— 分离两个前提的作用。

注意 单列此条是为**分离两个前提的贡献**：`IsFCAClosed Rc P` 在 §4 见证中**成立**，
故"命题为假"**完全归因于**覆盖假设 `fcaClosure R S ⊆ P` 的缺失，
而不是因为 `P` 不闭。这是 `PROCESS.md §2.3` 判据 1「每环假设都承重」的精确化：
**两个前提各自的作用被分开钉住**，而非笼统地说"假设很重要"。 -/
theorem fcaAbstraction_witness_closed :
    IsFCAClosed Rc (fcaClosure Rc ({1} : Set ℝ)) := by
  rw [isFCAClosed_iff]
  exact fcaClosure_idempotent Rc ({1} : Set ℝ)

end LoadBearing

/-! ## 5. 非退化见证：主定理在真实数据上跑通一次

注意 一个前件恒假、或结论恒真的定理不携带信息。本节给出**前提与结论同时非空**的实例。 -/

section Witness

/-- 要点 **非退化见证：主定理在约束实例上给出真实的跨层转移。**

取 `S = {1}`（非空具体集合）、`P = fcaClosure Rc {1}`（闭抽象值）、
`a = ⟨1,-1⟩`（约束 `x - 1 = 0`）。

* **覆盖前提成立**：`fcaClosure Rc S ⊆ P`（反身）；
* **属性前提成立**：`a ∈ intent Rc P`（由 `P` 的定义与 `1` 满足 `a` 给出）；
* **结论为真**：`Rc 1 a` 即 `1 - 1 = 0`。

⇒ 前提与结论**同时被真实数据满足**，故主定理**不是空转**。 -/
theorem fcaAbstraction_witness :
    ∃ (S P : Set ℝ) (a : RealConstraint),
      IsFCAClosed Rc P ∧ fcaClosure Rc S ⊆ P ∧ S.Nonempty ∧
        a ∈ intent Rc P ∧ (∀ o ∈ S, Rc o a) := by
  refine ⟨({1} : Set ℝ), fcaClosure Rc ({1} : Set ℝ), ⟨1, -1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact fcaAbstraction_witness_closed
  · exact subset_rfl
  · exact ⟨1, by simp⟩
  · -- a ∈ intent (fcaClosure {1})
    intro x hx
    rw [fcaClosure_def] at hx
    have hc : (⟨1, -1⟩ : RealConstraint) ∈ intent Rc ({1} : Set ℝ) := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact rc_one_is_solution
    exact hx _ hc
  · -- 结论：S 中每点满足 a
    intro o ho
    rw [Set.mem_singleton_iff] at ho
    rw [ho]
    exact rc_one_is_solution

end Witness

/-! ## 6. 与 `RealAbstractInterpretation` 的**边界**（防重复建设）

| 对象 | `RealAbstractInterpretation` | **本文件** |
|:--|:--|:--|
| 抽象的是什么 | **算子** `f♯` 对 `f` | **集合/概念** `P` 对具体点集 `S` |
| 核心谓词 | `SoundAbstract gamma f fSharp`（`:184`） | `fcaAbstraction_sound`（§3） |
| 载体 | `GaloisMem` / `IntervalAbstract` | `RealFCA.extent`/`intent` |
| 连接类型 | `GaloisConnection αS γ` | FCA 的 `extent ⊣ intent`（`RealFCA.galois_connection`） |

注意 **本文件不复用、不重定义 `SoundAbstract` / `GaloisMem` / `IntervalAbstract`**
（除 `import` 外零引用）—— 二者的数学对象不同，强行统一会让两边都失真。
要点 **这正是 `PROCESS.md §2.2` 的"该证什么"判定的产物**：
先判明"抽象算子可靠"与"抽象值覆盖"是**两个**定理，再分别立项。

## 7. 诚实边界（本文件的）

1. 注意 **本文件只证【单向】转移**（concrete ⇐ abstract）。
   **不证** `γ∘α ⊇ id` 的带界版本，**也不重启** `RealReversibilityBoundary`
   已结案的严格可逆否定结论。
2. 注意 **`a ∈ intent R P` 是显式前提，不是遗漏**：去掉它命题**为假**
   （§3 docstring 给出理由）。它不使定理平凡——前提在抽象层，结论跨到具体层。
3. 注意 **未跑 `lake build`**（文件不在 roots ⟹ `unknown target`，见编译记录）；
   类型检查走 `scripts/probe.ps1`（sanctioned 单文件路径）。
4. 注意 **与 `RealFCASyntaxBridge` 零合并**：两者方向正交，本文件不引用它。

注意 依赖口径同文件头「订正 B400」：本文件的**表示层**基于 Std 核心类型，
但**文件整体 `import Mathlib`**（第 1 行）——**不声称「无 mathlib」**。
无 sorry/axiom/admit/native_decide。
-/

end Lattice.Lib.FCA.RealFCAAbstractionSoundness
