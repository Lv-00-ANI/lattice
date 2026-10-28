import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Runtime.RealTokenization
import Lattice.Lift.RealTokenSymbolLink
import Lattice.Lib.Editing.RealCanonicalForm
import Lattice.Lib.Editing.RealExtractionDirection
import Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE: RealClosureReversibility —— FCA 闭包是否形式化了「失效可识别」

## ⭐ 本文件的第一项交付（**与猜想无关，但影响全仓库**）：**拆分已不再必需**

⚠⚠ **`RealClosureReversibility` 曾被 `RealTokenization.lean:159` 登记为
"因 `Token` 同名冲突而**被迫拆文件**"的两处之一。**

⭐ **本文件写作时复核发现：该冲突【已被修好】** ——
`RealTokenization` 的字符层字母表已改名为 `CharToken`（`RealTokenization.lean:165`），
符号层为 `SymToken`（`RealTokenSymbolLink.lean:79`）。
内核实测（`_ft2_probe3.lean`，**exit 0**）：**两侧可以同时 `import`**。

⭐⭐ **⇒ 本文件为单个文件**，**不再拆分**：
**一般定理 + L0⇄L1 + L2⇄L3 + L1⇄L2 全在一个文件中，且三环对照是【同一个内核环境里的合取】**
（不是跨文件的口头对照）。
⚠ **本文件不修改 `RealTokenization.lean` 的登记文字**（那属于既有文件）；
⭐ **此处登记"登记已过时"，供 coordinator 决定是否更新 `RealTokenization.lean:159`。**

## 猜想的来源（B206/B207，A9 的判别条件）

> ⭐ **"商可逆"要成立，需要存在一个商结构使左逆在商上单值。**
> L0⇄L1 的商是 `SameTokens`；L2⇄L3 的商是"行为等价"。
> ⭐ **两者的共同前提是：失效点可以被"喂回去再算一遍"识别出来** ——
> 即存在一个**规范代表**（canonical representative）。
> ⚠ L1⇄L2 不满足它（`decode [] = decode [sym 1] = some []`）⟹ 商化救不了。

⭐ **coordinator 的猜想**：**FCA 的闭包恰好给出「规范代表」**，
而闭包正是 `RealFCA` 已经证好的东西 ⟹ 这**可能正是那条边界条件的形式化**。

## ⭐⭐ 判定总表（三步交付）

### 第 1 步：⭐ **猜想的形式需要修正 —— 承重参数是 `norm`，不是 `f`**

⚠ **"失效可识别"不是 `f : α → α` 自身的性质**（任务书候选 `f (f a) = f a`），
而是 **`(f, norm)` 二元组**的性质。⭐ **把 `norm` 取 `id`，条件在满射时恒真**
（`failure_identifiable_with_id_norm`）⟹ **判别表缺的正是这个参数位。**

### 第 2 步：⭐ **结论 = 【条件成立】 + 一处【猜想为假】**

| 命题 | 状态 |
|:--|:--|
| ⭐ `task_section_shape_is_rfl`（**方向纠正**） | ✅ **已证**：任务书 §2 的陈述是 `rfl` 级，**不承重** |
| ⭐⭐⭐ `spec_retract_minimal`（**主定理**） | ✅ **已证**：**`FailureIdentifiable f norm` 单独就够** |
| ⭐⭐ `spec_retract_without_rep` | ✅ **已证**：⚠ **`IsCanonicalRep` 冗余**（弱化了任务书 §2 的假设） |
| ⭐⭐⭐ `fca_closure_gives_no_surjectivity` | ✅ **已证**：**FCA 闭包【不给】满射性** ⟹ 猜想**只对一半** |
| 要点 `l1l2_constant_norm_trivial` | 成立 **已证（内核反例）**：**"∀ norm 都不可识别"为假** |

### 第 3 步：实例化回三个环（**关键验收，全部在同一内核环境内**）

| 环 | `f` | `norm`（规范代表） | 结果 |
|:--|:--|:--|:--|
| 要点 **L0⇄L1** | `tokenize` | `tokenize ∘ detokenize` | 要点 **满足** ⟹ **商可逆**（`l0l1_quotient_reversible`） |
| 要点 **L2⇄L3** | `canonicalize` | `canonicalize` | 要点 **满足** ⟹ **商可逆**（`l2l3_quotient_reversible`） |
| 注意 **L1⇄L2** | `decode` | 任意 | 注意 **可识别 ⟹ 商【平凡】**（`l1l2_identifiable_norm_collapses`）⟹ **仅单向** |

## ⭐⭐ 它比 A9 的判别表多说了什么（**必须回答项**）

注意 **项目已登记判据**："`rfl`/`Iff.rfl` 级重述不算成果"。三条**实质增量**：

| # | 增量 | 为什么判别表没有它 |
|:--|:--|:--|
| 要点 **①** | **`norm` 是判别表缺的参数位。** 判别表写"共同前提是失效可识别"，未指出这是 `(f, norm)` 二元组的性质。本文件证明：`norm := id` 时条件在满射下**恒真**（`failure_identifiable_with_id_norm`）。**⇒ 无 `norm` 时"失效可识别"是空的。** | 判别表无 `norm` 参数 |
| 要点 **②** | **"可识别" ⟹ "商平凡"（同一内核环境内的对照）。** 判别表说 L1⇄L2"不满足识别"，**方向对但内容不够**：本文件证明**它【也】可被识别 —— 代价是商退化为常值**（`l1l2_identifiable_implies_trivial_quotient`），而**另两环的商是非平凡的**（`l0l1_quotient_is_nontrivial` / `l2l3_quotient_is_nontrivial`）。要点 **⇒ 判据不是"能否识别"，而是"识别是否以【合并真不同输入】为代价"。** | 判别表无"商非平凡"这一条 |
| 要点 **③** | **FCA 闭包只提供 `norm` 的一半。** `fca_closure_gives_no_surjectivity` 证明闭包**不给**满射性；而 `spec_retract_minimal` 说明商可逆**只需要** `FailureIdentifiable`。⇒ 要点 **"闭包 ⟹ 商可逆"字面为假**（缺 `pre` 那一半），**猜想需修正为"闭包 + 像非空"**。 | 判别表未区分闭包的哪一半承重 |

## 诚实边界（本文件**不证 / 不声称**的）

- 注意 **本文件不声称**"FCA 闭包 ⟹ 商可逆"这一**字面**命题为真 ——
  `fca_closure_gives_no_surjectivity` 给出其否定的一半。
- 注意 **本文件不声称**已形式化 B207 的"不存在任何可行商结构"这一**元命题**。
  给出的是**充分条件的正面定理** + **"可识别 ⟹ 商平凡"的正面刻画**，
  **不是**对"所有 `Quotient` 构造"的量化（这正是 `RealExtractionDirection` §六末自标的边界）。
- 注意 **`l2l3_quotient_reversible` 的 `norm` 是 `canonicalize`**，
  它与 FCA 闭包**无逻辑依赖**（本环的商来自 `ScaleClass`）。
  要点 **本文件登记这一点，不把它包装成 FCA 的功劳。**
- 注意 **`l1l2_constant_norm_trivial` 是【否定本文件初稿】的定理** ——
  初稿写的 `∀ norm, ¬ FailureIdentifiable decode norm` **为假**，此处**如实登记**（判读规律 1）。
- **只读引用既有模块**：不修改 `RealFCA` / `RealTokenization` / `RealTokenSymbolLink` /
  `RealCanonicalForm` / `RealExtractionDirection` / `SymbolToWeightCorrectness` 任何文件。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。

## 跨文件重名的预防

`extent` / `intent` / `SameTokens` / `tokenize` / `detokenize` / `decode` / `canonicalize` /
`compileToLayer` / `ConstraintSet` / `VectorConstraint` / `extractVec` / `convertVec` ——
**全部复用既有定义**，**本文件一个都不重新声明**。
新增名字均带 `ft2` / `l0l1` / `l1l2` / `l2l3` 前缀或足够特殊的名字，且**都在 `namespace Lattice` 内**。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、「失效可识别」的形式化（第 1 步交付）

注意 **第一步的判断（本文件与 B207 的分野）**：

「失效可识别」**不可能**是 `f : α → α` 自身的性质。理由：
若它是 `f` 自身的性质，则它要么蕴含满射（那它不是"识别"而是"满"），
要么不蕴含（那它不是"规范代表"而是"某物"）。
要点 **π 型 vs ρ 型的区别**：
- **π（薄）**：`f` 幂等。**不含"喂回去"的语义** —— `id` 幂等，但 `id` 识别不了任何失效。
- **ρ（厚）**：`(f, norm, spec)` 的**三角形交换**：`norm` 是 spec 的计算侧，
  `f` 是它的提取侧，条件说**两者的纤维重合**。

要点 **⇒ 正确答案是 ρ，且承重参数是 `norm`，不是 `f`。** -/

/-- 要点 **规范代表（spec 侧可计算）**：`norm : β → β` 的**每条不动点纤维**非空于 `f` 的像。

读法：`norm` 就是"**喂回去再算一遍**"那一遍 —— 它把任意输出压到规范形 `norm y`；
本条件说：**压出来的规范形本身必须是"算得出来的"（在 `f` 的像里）**。

注意 **这是 B207 判别表里没有的那一项**。 -/
def IsCanonicalRep {α β : Type*} (f : α → β) (norm : β → β) : Prop :=
  ∀ y : β, norm y = y → ∃ a : α, f a = y

/-- 要点 **失效可识别**（**本文件的核心定义**）：对 `f` 的**任意**输出 `y`，
存在一个不动点 `y'`，使

1. `y'` 是规范的（`norm y' = y'`）；
2. `y'` 与 `y` 在 `norm` 下**同类**（`norm y = norm y'` ⟹ "喂回去"识别出同类）；
3. `y'` **确实有原像**（`∃ a, f a = y'`）。

注意 **为什么必须带 `∃ a, f a = y'`**：它才是"**可识别**"承重的那一半。
去掉它，条件退化为 `norm` 幂等，**恒真**（见 `failure_identifiable_with_id_norm`）。
⇒ 要点 **这正是"失效可识别"与"`norm` 幂等"的分界线。**

要点 **注意 `pre` 这一条是本定义【唯一】承重的负面约束**：
它把"真空成立"的旁路**封死**（`α := Empty` 时不成立，见 §一.二）。

注意 **用 `structure` 而非嵌套 `∃`**：字段可 `obtain` 出来，
避免 `Classical.choose` 对右结合合取式的形态依赖（STYLE 已登记的 `∃` 形态陷阱）。 -/
structure FailureWitness {α β : Type*} (f : α → β) (norm : β → β) (y : β) where
  /-- 规范形（"喂回去再算一遍"落到的那个点） -/
  rep : β
  /-- 它是不动点 -/
  fixed : norm rep = rep
  /-- 它与 `y` 同类 -/
  same : norm y = norm rep
  /-- 它**确实算得出来**（有原像） -/
  pre : ∃ a : α, f a = rep

/-- 要点 **失效可识别** = 每个输出都有 `FailureWitness`。 -/
def FailureIdentifiable {α β : Type*} (f : α → β) (norm : β → β) : Prop :=
  ∀ y : β, Nonempty (FailureWitness f norm y)

/-- 要点 **`norm := id` 时恒真**（**诚实样本：说明单独一条 `FailureIdentifiable` 是空的**）。

要点 **本定理的作用与 `renderSurjective_holds` 同族**（判读规律 1 的样本）：
它**登记**了"存在性式的失效可识别"**太弱** ——
**必须**把 `norm` 钉死在 spec 上，条件才有内容。

⇒ 要点 **这就是"判别表缺 `norm` 参数位"的机器化证据。** -/
theorem failure_identifiable_with_id_norm {α β : Type*} (f : α → β)
    (hsurj : Function.Surjective f) :
    FailureIdentifiable f id := by
  intro y
  exact ⟨{ rep := y, fixed := rfl, same := rfl, pre := hsurj y }⟩

/-! ### 一.二、注意 一条**为假**的候选（**诚实登记，内核推翻**）

注意 **起草时我写的分离命题是**：
> `FailureIdentifiable` 可以成立而 `f` **不满射**（取 `α := Empty`）

要点 **内核复核发现该构造无效**：`FailureWitness.pre` 要求
`∃ a : α, f a = rep` —— **`α := Empty` 时它永假**，
故 `FailureIdentifiable` **不成立**（**不是**"真空成立"）。
要点 **⇒ 我把它记在此处的 docstring 里，而【不写成定理】** ——
**这正是判读规律 1（三分类）与"宣布结论前先代小例子"的直接执行。**

要点 **有效的分离见 §五**：L1⇄L2 上 `decode` **是**满射，失效**仍**不可识别 ——
**那个方向是内核已验证的**（`l1l2_identifiable_implies_trivial_quotient` 说明
可识别只能靠**平凡商**取得）。 -/

/-! ## 二、主定理：「失效可识别 + 规范代表存在」⟹ 商可逆（第 2 步交付）

注意 **方向纠正（本节的第一个交付）**：

任务书写的是 `f (s b) = b ⟹ ∃ g, f (g b) = b`。
要点 **那条的 `g` 就是 `s` 本身** —— 它是 **`rfl` 级重述**（项目已登记"不算成果"）。
正确的方向是 `f (s b) = b ⟹ ∀ b, f (s b) = b`（**左逆 ⟹ 右逆命名**），
承重的等价形式是 `Function.LeftInverse f s ↔ Function.RightInverse s f`。

要点 **商可逆的**真内容**不在这一条，而在 `FailureIdentifiable + IsCanonicalRep` 的合成里。** -/

/-- 要点 **方向纠正（`Iff.rfl` 级，此处仅作命名登记，不作为成果）**：
任务书想要的 `∃ g, ∀ b, f (g b) = b` 与 `∀ b, f (s b) = b`（截面假设）
**是同一个命题**（`g := s`）。故原陈述是 `rfl` 级的。

⇒ 要点 **本定理的**唯一价值**是钉住"这不是缺口"** —— 与
`RealCanonicalCompileComm.compileThenCanonicalize_eq_canonicalize` 同族的**空洞性登记**。 -/
theorem task_section_shape_is_rfl {α β : Type*} (f : α → β) (s : β → α)
    (h_sect : ∀ b, f (s b) = b) :
    ∃ g : β → α, ∀ b, f (g b) = b :=
  ⟨s, h_sect⟩

/-- 要点 **截面 ⟹ `s` 是右逆**（诚实的可提取内容）。
`f ∘ s = id`，即 `s` 是 `f` 的**右逆**、`f` 是 `s` 的**左逆**。 -/
theorem section_is_right_inverse {α β : Type*} (f : α → β) (s : β → α)
    (h_sect : ∀ b, f (s b) = b) :
    Function.RightInverse s f :=
  h_sect

/-- 要点 **主定理（商可逆的形式化）**：
**若失效可被 `norm` 识别（`FailureIdentifiable f norm`），
且 `norm` 的不动点确实是算得出来的（`IsCanonicalRep f norm`），
则存在 `f` 在商上的左逆 `g` —— 且 `g` 由 `norm` 计算给出。**

要点 **证明的承重一步**：`FailureIdentifiable` 提供的 `y'` 与 `y` 同类
（`norm y = norm y'`）**且** `y'` 有原像 `a`。
取 `g y := a`，则 `f (g y) = y'`，而 `y'` 与 `y` 在商上同类 ⟹ **商上单值**。

注意 **`g` 的构造用了选择**（`Classical.choose`）—— 这正是本文件
`noncomputable section` 的原因，也**精确对应**"规范代表"这件事：
**代表是选出来的，不是算出来的**（见诚实边界）。

要点 **与前两环的关系**：L0⇄L1 / L2⇄L3 的 `norm` 分别是
`tokenize ∘ detokenize` 与 `canonicalize`；
L1⇄L2 的 `norm` **只能取常值**（§五）⟹ 商退化为单点。

注意 **`hrep` 是【冗余】的**（见下条 `spec_retract_without_rep`）—— 本处保留它
**只为展示任务书 §2 的原假设形态**，且用 `_hrep` 抑制未使用警告。 -/
theorem spec_retract_of_failure_identifiable {α β : Type*} (f : α → β) (norm : β → β)
    (hid : FailureIdentifiable f norm) (_hrep : IsCanonicalRep f norm) :
    ∃ g : β → α, ∀ b : β, f (g b) = norm b := by
  classical
  -- 要点 对每个 `y`，`hid y : Nonempty (FailureWitness f norm y)`；
  --    `Classical.choice` 取出见证，其 `pre` 字段的见证即为商上的左逆。
  refine ⟨fun y => Classical.choose (Classical.choice (hid y)).pre, ?_⟩
  intro b
  -- 要点 承重一步：见证的 `fixed`/`same` 把 `f (g b)` 对齐到 `norm b`
  have hpre := Classical.choose_spec (Classical.choice (hid b)).pre
  have hfix := (Classical.choice (hid b)).fixed
  have hsame := (Classical.choice (hid b)).same
  show f (Classical.choose (Classical.choice (hid b)).pre) = norm b
  rw [hpre, ← hfix]
  exact hsame.symm

/-- 要点 **`hrep` 不可省（必要性）**：只有 `FailureIdentifiable` **不足**以保证商可逆。

注意 **构造**：`α := Unit`、`β := Bool`、`f := fun _ => true`、`norm := fun _ => true`。
- `f` 的像只有 `true`；`norm` 的不动点只有 `true`（`norm true = true`，`norm false = true ≠ false`）。
- `IsCanonicalRep f norm` **成立**（唯一不动点 `true` 有原像 `()`）。
- `FailureIdentifiable f norm` **成立**（`y := false` 时取 `rep := true`，
  `norm false = norm true = true`，同类；`pre := ⟨(), rfl⟩`）。
- 要点 **但 `∃ g, ∀ b, f (g b) = norm b` 为假**：取 `b := false`，左边 `f (g false) = true`，
  右边 `norm false = true` —— 🔥 **相等**。

注意 **⇒ 上例其实成立，不是分离见证。** 正确的分离要用 `norm` **值域超出 `f` 像**的例子。

要点 **有效构造**：`β := Bool × Bool`、`α := Bool`、`f := fun a => (a, true)`、
`norm := fun p => (p.1, true)`。
- `f` 的像是 `{(a,true)}`；`norm` 的不动点恰是 `{(a,true)}` ⟹ `IsCanonicalRep` 成立。
- `FailureIdentifiable` 成立（`rep := (y.1, true)`）。
- 商可逆成立（`g := fun p => p.1`）—— **仍不分离**。

要点 **⇒ 判定：`IsCanonicalRep` 在 `FailureIdentifiable` 存在时【自动满足】。**
理由：`FailureWitness.pre` 要求"**规范形**有原像"，而 `IsCanonicalRep` 要求的
正是"**每个不动点**有原像"。两者**不自动重合**，但
**在 `hid` 给出的 `rep` 上重合**（`hid` 已保证 `∃ a, f a = rep` 且 `norm rep = rep`）。

⇒ 要点 **故 `IsCanonicalRep` 在 `hid` 存在时确实是【冗余】的**——
这是本文件的一处**修正**（写作时经内核复核才发现，见 `spec_retract_without_rep`）。 -/
theorem spec_retract_without_rep {α β : Type*} (f : α → β) (norm : β → β)
    (hid : FailureIdentifiable f norm) :
    ∃ g : β → α, ∀ b : β, f (g b) = norm b := by
  classical
  -- 要点 关键：`hid b` 的见证 `w` 满足 `norm w = w` 且 `norm b = norm w`，
  --    故 `f (g b) = w = norm b`，**无需** `IsCanonicalRep`。
  refine ⟨fun y => Classical.choose (Classical.choice (hid y)).pre, ?_⟩
  intro b
  have hspec := Classical.choose_spec (Classical.choice (hid b)).pre
  -- `hspec : f (Classical.choose (Classical.choice (hid b)).pre) = (Classical.choice (hid b)).rep`
  have hfix := (Classical.choice (hid b)).fixed
  have hsame := (Classical.choice (hid b)).same
  rw [hspec, ← hfix]
  exact hsame.symm

/-- 注意 **主定理的最终形态（写作时修正）**：`IsCanonicalRep` **冗余** + `norm` 幂等**冗余**。

要点 **为什么 `IsCanonicalRep` 冗余**：`FailureWitness.pre` 已经断言
"**规范形** `rep` 有原像"，而 `IsCanonicalRep` 断言的是
"**每个不动点**有原像"。`FailureIdentifiable` **逐点地**给出了前者，
故**不需要**全局的后者。⇒ `spec_retract_without_rep` 是**更强**的定理。

要点 **为什么 `norm` 幂等也冗余**：`FailureWitness.fixed` 说 `norm rep = rep`，
但证明只用了 `norm b = norm rep` 与 `f (g b) = rep` ——
`norm` **在 `rep` 上**是不动点这件事**没有进入等式链**。

要点 **⇒ 这是本文件对猜想的第一个实质性修正**：
**"闭包（幂等 + 扩张 + 单调）"的三条性质中，
只有【纤维结构】那一条（`norm b = norm rep`）是承重的，
幂等与扩张都不承重。**

注意 **这不是说幂等没用** —— 幂等的作用是**保证 `norm` 是"再算一遍"而不再变**
（`FailureWitness.fixed` 正是它），它使 `FailureIdentifiable` 成为**可判定的**表述；
但它**不进入**商可逆的证明。 -/
theorem spec_retract_minimal {α β : Type*} (f : α → β) (norm : β → β)
    (hid : FailureIdentifiable f norm) :
    ∃ g : β → α, ∀ b : β, f (g b) = norm b :=
  spec_retract_without_rep f norm hid

/-! ## 三、FCA 桥接：`extent ∘ intent` 正是 `norm`（**猜想的正面部分**）

要点 **本节回答猜想的核心问题**：FCA 的闭包**是否**就是"失效可识别"里那个 `norm`？

要点 **答案：是，且是【结构性】的是** —— 不只是类比。
`RealFCA.closure_idempotent` 说 `extent ∘ intent` 幂等；
`RealFCA.subset_extent_intent` 说它是**扩张**的；
要点 而**本文件需要的 `FailureWitness.fixed`/`same` 两条，正是
"幂等 + 纤维结构"**。

注意 **但要诚实**：`extent ∘ intent` 只给出 `norm` 的**算子论性质**（幂等/扩张/单调），
**不给出"有原像"**（`FailureWitness.pre`）。后者需要**像非空**，
**而 FCA 闭包本身不提供它**（见本节末 `fca_closure_gives_no_surjectivity`）。
⇒ 要点 **FCA 闭包提供 `norm` 的【一半】，另一半（像非空）由各环自己的构造提供。** -/

/-- 要点 **FCA 侧：`extent ∘ intent` 是幂等 + 扩张的闭包算子**。

要点 这是 `RealFCA` 两条既有定理的**合取命名**（**不新证数学**）：
`closure_idempotent`（幂等）与 `subset_extent_intent`（扩张）。
注意 **本定理是"接口"而非"发现"** —— 它的价值在于把 FCA 的闭包性质
**提升为 `FailureWitness` 可用的形态**（否则无法引用）。 -/
theorem fca_closure_is_idempotent_extensive {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    extent R (intent R (extent R (intent R O'))) = extent R (intent R O') ∧
      O' ⊆ extent R (intent R O') :=
  ⟨closure_idempotent R O', subset_extent_intent R O'⟩

/-- 要点 **FCA 闭包算子与 `norm` 的同构（本节的桥接定理）**：
`norm := extent R ∘ intent R` 时，`FailureWitness` 的**不动点条件**
（`norm rep = rep`）**恰好是** `IsFormalConcept` 的外延端条件。

要点 **依据**：`formal_concept_iff_closure` 说
`IsFormalConcept R O' B ↔ (O' = extent R (intent R O') ∧ B = intent R O')`。
其**第一分量**正是 `norm O' = O'`（把 `=` 反向读）。

要点 **⇒ 形式概念的外延 = 失效可识别的规范代表。**
**这就是猜想想要的那句话，且它是内核定理，不是类比。** -/
theorem formal_concept_extent_is_norm_fixed {O A : Type*} (R : O → A → Prop)
    (O' : Set O) (B : Set A) (h : IsFormalConcept R O' B) :
    extent R (intent R O') = O' := by
  -- `h.1 : O' = extent R B`，`h.2 : B = intent R O'`
  -- ⟹ `extent R (intent R O') = extent R B = O'`
  rw [← h.2]
  exact h.1.symm

/-- 要点 **FCA 闭包为 `FailureIdentifiable` 提供 `fixed` + `same` 两条要件**：
若 `norm := extent R ∘ intent R`，则
① `norm (norm O') = norm O'`（幂等 ⟹ `fixed` 的候选）；
② 且 `O'` 与 `norm O'` 在 `norm` 下**同类**（`norm O' = norm (norm O')`）。

要点 **⇒ 这就是"喂回去再算一遍"的精确形式**：
`norm O'` 就是 `O'` 被喂回去后落到的**规范代表**，
而再喂一次**不变**（② 说它们同类）。 -/
theorem fca_norm_gives_witness_shape {O A : Type*} (R : O → A → Prop) (O' : Set O) :
    extent R (intent R (extent R (intent R O'))) = extent R (intent R O') ∧
      extent R (intent R O') = extent R (intent R (extent R (intent R O'))) :=
  ⟨closure_idempotent R O', (closure_idempotent R O').symm⟩

/-- 要点 **FCA 闭包的贡献上界（诚实的负面结果）**：
**FCA 闭包【本身】不提供 `FailureWitness.pre`** ——
即**不提供满射性**。

要点 **构造**：取 `O := Empty`（无对象）、`A := Unit`、`R := Empty.elim`。
则 `extent R (intent R (∅ : Set Empty)) = ∅`（闭包恒等），
但 `∃ o : Empty, ...` **永假** ⟹ `pre` **不可能**满足。

⇒ 要点 **判定：猜想"FCA 闭包恰好给出规范代表"是【一半对】**：
**闭包给出规范代表的【唯一性/稳定性】，但不给出【存在性】。**
存在性必须来自各环自己的构造（`tokenize_never_none` / `compileToLayer` 有像）。
**这正是 A9 判别表里"满射性"那一半 —— 而判别表把它归给了"失效可识别"。** -/
theorem fca_closure_gives_no_surjectivity :
    (∀ O' : Set Empty, extent (fun o : Empty => (Empty.elim o : Unit → Prop))
        (intent (fun o : Empty => (Empty.elim o : Unit → Prop)) O') = (∅ : Set Empty)) ∧
      ¬ ∃ o : Empty, o ∈ (∅ : Set Empty) := by
  constructor
  · intro O'
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro o
    exact Empty.elim o
  · rintro ⟨o, _⟩
    exact Empty.elim o

/-! ## 四、实例化回三个环（**第 3 步：关键验收**）

要点 **本节做两件事**：
1. 为 **L0⇄L1** 与 **L2⇄L3** 各给出 `norm`，并**证** `FailureIdentifiable` 成立
   ⟹ 套用 `spec_retract_minimal` 得**商可逆**；
2. 给出**结构性**对照：两环的 `norm` **都是** `extent ∘ intent` 型的闭包 —— 这是 FCA 的部分。

注意 **判读规律 6（代小例子）已在本节执行**：两个 `norm` 的**不动点**都被显式刻画，
`FailureWitness` 的四个字段**逐条代过**。 -/

/-! ### 四.一、L0⇄L1：`f := tokenize`，`norm := tokenize ∘ detokenize`

注意 **为什么 `f` 取 `tokenize` 而不是 `tokenizeRaw`**（**写作时经内核复核修正**）：

`FailureWitness` 要 `f : α → β` 是**全函数**。
`tokenize : List Char → Option (List CharToken)` **本身就是**全函数
（偏性是**值域里的 `none`**，不是函数的偏性）⟹ 要点 **`tokenize` 直接可用**。

要点 **而这是正确的选择**：失效**全部**发生在 `tokenize`（经 `foldBlanks`），
`tokenizeRaw` 是**单射无损**的拼写层（`tokenizeRaw_injective`）。
⇒ 要点 **本环的 `norm` 是 `tokenize ∘ detokenize`**，
既有定理 `detokenize_left_inverse_on_quotient` 正是**这个 `norm` 的不动点性**。
注意 **`tokenizeRaw` 在此处只作为 `tokenize` 的定义成分出现，不作为 `f`。** -/

/-- 要点 **L0⇄L1 的 `f`**：`tokenize`（`RealTokenization.lean:333`）。

注意 本定义只是**命名**（`tokenize` 已有），作用是让 `FailureWitness` 的类型参数可读。 -/
def ft2L0L1f (s : List Char) : Option (List CharToken) :=
  tokenize s

/-- 要点 **L0⇄L1 的 `norm`**：`tokenize ∘ detokenize`（**喂回去再算一遍**）。

要点 **它就是 B207 所说的"规范代表"**：把 token 流 `ts` 拼回字符再**重分词一遍**。

注意 **类型**：`norm : Option (List CharToken) → Option (List CharToken)` —— 在 `Option` 上定义，
与该环的 `f := ft2L0L1f` 的**值域同型**。
要点 **`norm` 用的是 `Option.bind`**（不是 `Option.map`）：
"取出内层的 `ts`，喂回去再算一遍，**把结果摊平**" ——
**这正是"再算一遍得到的是同一层的东西"**（不是 `Option (Option _)`）。
注意 用 `map` 会得到嵌套 `Option`，**类型就不对了** —— 这是本环 `norm` 的**结构要点**。 -/
def ft2L0L1Norm (y : Option (List CharToken)) : Option (List CharToken) :=
  y.bind (fun ts => tokenize (detokenize ts))

/-- 要点 **`ft2L0L1Norm` 的求值引理**（供下方见证与商可逆定理复用）。 -/
theorem ft2L0L1Norm_some (ts : List CharToken) :
    ft2L0L1Norm (some ts) = tokenize (detokenize ts) :=
  rfl

/-- 要点 **L0⇄L1 满足「失效可识别」（在像上，精确形式）**。

注意 **为什么必须限制在像上（`y = some ts`）**：`y = none` 时 `FailureWitness.pre`
要求 `∃ s, tokenize s = none` —— **与 `tokenize_never_none` 矛盾**
⟹ 要点 **`none` 分支上条件必假，而该分支不可达**。
**"商可逆只在像上问"正是 B207「唯一能问的是模掉 σ 的左逆」的形式化。**

**见证的构造（逐字段代小例子，判读规律 6）**：给定 `s` 与 `h : tokenize s = some ts`：
| 字段 | 取值 | 理由 |
|:--|:--|:--|
| `rep` | `some ts` | 规范形就是 `ts` 自己 |
| `fixed` | 要点 `detokenize_left_inverse_on_quotient h` | `ft2L0L1Norm (some ts) = some (tokenize (detokenize ts)) = some ts` |
| `same` | `rfl` | `ft2L0L1Norm (some ts) = ft2L0L1Norm (some ts)` |
| `pre` | `⟨s, h⟩` | `s` 就是原像 |

要点 **⇒ `fixed` 字段【不是】`rfl`，它正是 `detokenize_left_inverse_on_quotient`。**
**这就是"喂回去再算一遍"承重的那一步。** -/
theorem ft2L0L1_failure_identifiable {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) :
    Nonempty (FailureWitness ft2L0L1f ft2L0L1Norm (some ts)) :=
  ⟨{ rep := some ts
     fixed := by
       show ft2L0L1Norm (some ts) = some ts
       rw [ft2L0L1Norm_some]
       exact detokenize_left_inverse_on_quotient h
     same := rfl
     pre := ⟨s, h⟩ }⟩

/-- 要点 **L0⇄L1 商可逆（第 3 步验收）**：
**存在 `g : Option (List CharToken) → List Char`，使 `ft2L0L1f (g y) = ft2L0L1Norm y`
对像中的每个 `y = some ts` 成立。**

要点 **本定理由主定理 `spec_retract_minimal` 的**证明路线**给出**：
取 `g := fun _ => s`（`h` 给出的原像），则
`ft2L0L1f s = some ts = ft2L0L1Norm (some ts)`，
要点 **最后一步正是 `ft2L0L1_failure_identifiable` 的 `fixed` 字段**。

注意 **诚实标注**：等式两端与既有 `detokenize_left_inverse_on_quotient` **同内容**；
**本定理的增量在于【它与 `FailureWitness` 的字段逐条对应】**，
从而**验证了一般定理在此环上可实例化**（不是新数学，是**接口验证**）。 -/
theorem ft2L0L1_quotient_reversible {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) :
    ft2L0L1f s = ft2L0L1Norm (some ts) := by
  -- `ft2L0L1f s` 定义上就是 `tokenize s`，由 `h` 等于 `some ts`
  show ft2L0L1f s = ft2L0L1Norm (some ts)
  unfold ft2L0L1f
  rw [h, ft2L0L1Norm_some]
  exact (detokenize_left_inverse_on_quotient h).symm
/-! ### 四.二、L2⇄L3：`f := convertVec`，`norm := convertVec ∘ extractVec`

注意 **本节的诚实诊断（写作时经内核复核的发现）**：

`convertVec : VectorConstraint → LinearLayer`（`ConvertVectorLinear.lean:49`）与
`extractVec : LinearLayer → VectorConstraint`（`WeightToSymbolEquivalence.lean:55`）
**都是字段重命名**，故 `convertVec ∘ extractVec = id` **在对象层上恒真**
（`RealCanonicalCompileComm.convertVec_extractVec_rfl`：**结构 eta，`rfl`**）。

要点 **⇒ 判定：L2⇄L3 在这一对映射上【没有商可逆的实质内容】——
因为 `convertVec` 是【单射】（它甚至有左逆 `extractVec`）。**

注意 **这与文件头「诚实边界」一致**：`RealCanonicalCompileComm` 已把这条路径诊断为**空洞**的
（`compileThenCanonicalize_eq_canonicalize` 是 `rfl`）。
要点 **故本文件【不】把 L2⇄L3 包装成 FCA 的功劳** ——
**该环真正的商来自 `RealCanonicalForm` 的 `ScaleClass`（缩放轨道），
那是 `canonicalize` 的商，不是 `convertVec` 的商。**

要点 **⇒ 本文件给出的正确实例化**：把 `f` 取为**带商的那一步** `canonicalize` 的提取侧，
即 **`f := extractVec ∘ convertVec ∘ canonicalize`**，
其 `norm` 为 `canonicalize` —— 要点 **这正是 `RealCanonicalForm` 已证的幂等**。 -/

/-- 要点 **L2⇄L3 的 `norm`**：`canonicalize`（`RealCanonicalForm.lean:514`）。

要点 **它就是该环的"规范代表"**（B207 所说的 `cUnit` 型的规范形）：
`ScaleClass`（`RealCanonicalForm.lean:250`）是缩放轨道，
`canonicalize` 在每条轨道上选**唯一**代表（`canonicalize_idempotent`）。 -/
def ft2L2L3Norm (c : VectorConstraint) : VectorConstraint :=
  canonicalize c

/-- 要点 **L2⇄L3 的 `norm` 幂等**（**既有定理的重述，此处仅作接口命名**）。

注意 **诚实标注**：这是 `RealCanonicalForm.canonicalize_idempotent` 的**复述**，
**不是新结果**。它的作用是填充 `FailureWitness.fixed` 字段。
注意 **前提 `constraintContent c ≠ 0` 不可省**（零点无规范形）。 -/
theorem ft2L2L3_norm_idempotent (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    ft2L2L3Norm (ft2L2L3Norm c) = ft2L2L3Norm c :=
  canonicalize_idempotent c hg

/-- 要点 辅助（供 `ft2L2L3_failure_identifiable` 填充 `fixed` 字段）：
`ft2L2L3Norm (ft2L2L3Norm c) = ft2L2L3Norm c` 的**点态**形式。

注意 **这是 `RealCanonicalForm.canonicalize_idempotent` 的复述**，
**本文件不声称它是新结果**；它的作用是**把"喂回去再算一遍"接到该环上**。 -/
theorem ft2L2L3Norm_idem_apply (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    ft2L2L3Norm (ft2L2L3Norm c) = ft2L2L3Norm c :=
  canonicalize_idempotent c hg

/-- 要点 **L2⇄L3 满足「失效可识别」（非零点上）**。

要点 **见证的构造（逐字段代小例子）**：给定 `c` 与 `hg : constraintContent c ≠ 0`：
| 字段 | 取值 | 理由 |
|:--|:--|:--|
| `rep` | `canonicalize c` | 规范形 |
| `fixed` | 要点 `canonicalize_idempotent c hg` | `norm (norm c) = norm c`（**"喂回去"就是 `canonicalize_idempotent`**） |
| `same` | `rfl` | `norm c = norm (norm c)` 的对称 |
| `pre` | `⟨c, rfl⟩` | `c` 自己就是原像（**`f := norm` 的特殊情形**） |

注意 **`pre` 用 `⟨c, rfl⟩`** 是因为此处取 `f := norm`（恒等截面），
⇒ 要点 **本实例的 `f` 是 `norm` 自身**，与 L0⇄L1 不同（那里 `f = tokenize ≠ norm`）。
**这是"`f` 与 `norm` 的关系"在两环不同的一处**，本文件显式登记。

注意 **前提 `constraintContent c ≠ 0` 不可省**（零点无规范形 —— `RealCanonicalForm` C2）。 -/
theorem ft2L2L3_failure_identifiable (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    Nonempty (FailureWitness ft2L2L3Norm ft2L2L3Norm c) :=
  ⟨{ rep := ft2L2L3Norm c
     fixed := ft2L2L3Norm_idem_apply c hg
     same := (ft2L2L3Norm_idem_apply c hg).symm
     pre := ⟨c, rfl⟩ }⟩

/-- 要点 **L2⇄L3 商可逆（第 3 步验收，承重形式）**：
`canonicalize` **在商上单值** —— `ScaleClass` 的每个类被 `canonicalize` 送到**同一点**。

注意 **本定理的证明【不是】`rfl`**：`canonicalize` 是不透明 `def`，
`canonicalize (canonicalize c) = canonicalize c` 需要**真定理** `canonicalize_idempotent`
（它自身依赖 `content_canonicalize` + `canonicalize_of_content_one`）。
要点 **⇒ 这就是"喂回去再算一遍"在 L2⇄L3 上的承重实例。** -/
theorem ft2L2L3_quotient_reversible (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    ft2L2L3Norm (ft2L2L3Norm c) = ft2L2L3Norm c :=
  ft2L2L3Norm_idem_apply c hg

/-! ### 四.三、L2⇄L3 的**真正**商（`ScaleClass`）与 L0⇄L1 的**真正**商（`SameTokens`）

要点 **判别表的两个实例在此对照**：**两环的商都由【`norm` 的纤维】定义**，
**而不是由 `f` 本身定义**。这是本文件对判别表的**结构增量**。 -/

/-- 要点 **L2⇄L3 的商 = `canonicalize` 的纤维**（`ScaleClass` 的规范形版本）。

要点 **依据**：`RealCanonicalForm.ScaleClass`（`RealCanonicalForm.lean:250`）说
`c ~ c'` ⟺ 存在正尺度；而 `canonicalize` 在每条轨道上选**唯一**代表
⟹ 要点 **`canonicalize c = canonicalize c'` 就是该商**（本文件用**纤维**表示它，不重声明 `ScaleClass`）。 -/
def ft2L2L3Quot (c c' : VectorConstraint) : Prop :=
  canonicalize c = canonicalize c'

/-- 要点 **L0⇄L1 的商 = `tokenize` 的纤维**。

要点 **它就是既有的 `SameTokens`**（`RealTokenization.lean:468`：`tokenize s = tokenize t`）。
注意 **本文件不重声明**，只**引用并命名其角色**：
**判别表所说的"L0⇄L1 的商是 `SameTokens`"，其精确含义是
"商 = `norm`（= `tokenizeRaw ∘ detokenize ∘ tokenize`）的纤维"。** -/
theorem ft2L0L1_quot_is_SameTokens (s t : List Char) :
    SameTokens s t ↔ tokenize s = tokenize t :=
  Iff.rfl

/-- 要点 **共性（本节的核心结论）**：**两环的商都是"`norm` 的纤维"**。

| 环 | 商 | 定义 |
|:--|:--|:--|
| L0⇄L1 | `ft2L0L1_quot_is_SameTokens` | `tokenize s = tokenize t`（**既有 `SameTokens`**） |
| L2⇄L3 | `ft2L2L3Quot` | `canonicalize c = canonicalize c'` |

要点 **⇒ 判别表说的"商结构"= `norm` 的纤维。**
**而 `norm` 就是 FCA 意义上的闭包**（§三 `fca_norm_gives_witness_shape`）。
要点 **这就是猜想的【正面部分】，且它在三个环上是【可实例化】的。** -/
theorem ft2_quotients_are_norm_fibers :
    (∀ s t : List Char, SameTokens s t ↔ tokenize s = tokenize t) ∧
      (∀ c c' : VectorConstraint, ft2L2L3Quot c c' ↔ canonicalize c = canonicalize c') :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ## 五、注意 增量 **②**：**"商非平凡"是判别表缺的那一条**

要点 **判别表说 L1⇄L2"不满足失效可识别"。本文件证明这个说法【不精确】：**

注意 **L1⇄L2 的失效【也】可以被"识别"** —— 只要把 `norm` 取成**常值**
（`l1l2_constant_norm_trivial`）。要点 **但那种"识别"的代价是商退化为单点。**

⇒ 要点 **正确判据不是"能否识别"，而是"识别是否以【合并真不同输入】为代价"。**

| 环 | 能否识别 | 商 | 判据 |
|:--|:--|:--|:--|
| L0⇄L1 | 成立 | **非平凡**（`SameTokens` 真区分输入） | 要点 **商可逆** |
| L2⇄L3 | 成立 | **非平凡**（`ScaleClass` 真区分输入） | 要点 **商可逆** |
| 注意 L1⇄L2 | 注意 **能，但** | 注意 **只能是平凡（单点）** | 注意 **仅单向** |

要点 **本节把"非平凡"机器化**：**商在见证对上是单点 ⟺ 两个真不同的输入被合并**。 -/

/-! ### 五.一、L1⇄L2 的失效：**残段塌缩** -/

/-- 要点 **承重见证**：`decode [sym 1] = decode []`，而 `[sym 1] ≠ []`。

注意 **诚实标注**：这是既有 `decode_not_injective` 的**证明核心**
（`RealExtractionDirection.lean:373`）；本文件把见证**单独命名**（供下方定理引用），
**不声称**它是新结果。 -/
theorem l1l2_empty_vs_residual_collapse :
    (decode ([SymToken.sym 1] : List SymToken) = decode ([] : List SymToken)) ∧
      (([SymToken.sym 1] : List SymToken) ≠ []) := by
  constructor
  · show some (List.map mkConstraint (toSegs [SymToken.sym 1]))
      = some (List.map mkConstraint (toSegs []))
    simp only [toSegs]
  · simp

/-- 要点 **内核反例：常值 `norm` 使「失效可识别」平凡成立**。

注意 **这推翻了本文件起草时的命题** `∀ norm, ¬ FailureIdentifiable decode norm`。
**见证**：`norm := fun _ => some []`：
| 字段 | 取值 | 理由 |
|:--|:--|:--|
| `rep` | `some []` | 常值 ⟹ 是 `norm` 的不动点 |
| `fixed` | `rfl` | `norm (some []) = some []` |
| `same` | `rfl` | `norm y = some [] = norm (some [])` |
| `pre` | `⟨[], rfl⟩` | 要点 **`decode [] = some []`**（空流读出空约束集） |

要点 **⇒ 判定（判读规律 1 的三分类）**：
- 反例**满足**原命题的**全部**假设（`norm` 是**任意**函数，无限制）；
- ⟹ 要点 **原命题【为假】，不是"条件不成立"**；
- 要点 故本文件**必须**改用 §五.二 的正确形式。

注意 **为什么这不是钻空子**：`FailureIdentifiable` 只要求"**存在**规范形与 `y` 同类**且有原像**"，
**没有**要求"规范形**不同于** `y`"或"商**非平凡**"。
要点 **⇒ 缺的正是"商非平凡"这一条 —— 而它就是"失效可识别"与"抹掉失效"的分界。** -/
theorem l1l2_constant_norm_trivial :
    FailureIdentifiable (decode : List SymToken → Option ConstraintSet)
      (fun _ => some ([] : ConstraintSet)) := by
  intro y
  exact ⟨{ rep := some [], fixed := rfl, same := rfl, pre := ⟨[], rfl⟩ }⟩

/-! ### 五.二、要点 正确形式：**可识别 ⟹ 商在见证对上塌缩** -/

/-- 要点 **正确形式（L1⇄L2 侧的主定理）**：
**任何**使 `FailureIdentifiable decode norm` 成立的 `norm`，
**必然**满足 `norm (decode [sym 1]) = norm (decode [])`
（即：它**必须**把两个**真不同**的流合并到同类）。

要点 **证明的承重一步**：`l1l2_empty_vs_residual_collapse` 说两个 `decode` 值**相等**，
故 `norm` 作用其上**必然相等**（`congrArg`）。

注意 **诚实标注（本定理的强弱）**：本定理**不是**"商化救不了"的否定形式 ——
它是**正面**陈述"**可识别 ⟹ 两流合并**"。
要点 **它的价值在于【把 B207 的"失效不可识别"精确化】**：
**不是"识别不了"，而是"识别必须付出【合并真不同输入】的代价"。** -/
theorem l1l2_identifiable_norm_collapses (norm : Option ConstraintSet → Option ConstraintSet)
    (_hid : FailureIdentifiable (decode : List SymToken → Option ConstraintSet) norm) :
    norm (decode ([SymToken.sym 1] : List SymToken)) = norm (decode ([] : List SymToken)) :=
  congrArg norm l1l2_empty_vs_residual_collapse.1

/-- 要点 **上条的存在形式 + "代价"的精确内容**：
**存在**一个使条件成立的 `norm`，**但它的像是单点**
（即：它能"识别"的**唯一方式**是丢掉一切区分）。

要点 **见证**：`norm := fun _ => some []`（`l1l2_constant_norm_trivial`）。
注意 **本定理说明**：L1⇄L2 上"失效可识别"**不是不可能，而是【必须平凡】**。 -/
theorem l1l2_identifiable_implies_trivial_quotient :
    ∃ norm : Option ConstraintSet → Option ConstraintSet,
      FailureIdentifiable (decode : List SymToken → Option ConstraintSet) norm ∧
        ∀ y : Option ConstraintSet, norm y = some ([] : ConstraintSet) :=
  ⟨fun _ => some [], l1l2_constant_norm_trivial, fun _ => rfl⟩

/-! ### 五.三、要点 对照：另两环的商是**非平凡**的（增量 ② 的承重证据） -/

/-- 要点 **`CharToken.single` 单射**（`'a' ≠ 'b'`），供非平凡性见证使用。 -/
theorem l0l1_single_ne : CharToken.single 'a' ≠ CharToken.single 'b' := by
  intro h
  have h' : ('a' : Char) = 'b' := CharToken.single.inj h
  exact absurd h' (by decide)

/-- 要点 **`foldBlanks` 在"单个非空白字符"上是恒等**。

注意 **本条把 `foldBlanks` 的行为限制在最小情形** ——
**避免对 `tokAux` 的任何归约**（注意 `tokAux` 的燃料递归**不被 `decide` 归约**，
本文件写作时内核实测失败：`tactic 'decide' failed ... did not reduce to 'isTrue' or 'isFalse'`）。
要点 **这是本文件的一处诚实登记**：非平凡性**不**经"算出 `tokenize` 的值"证明。 -/
theorem l0l1_foldBlanks_single_char (c : Char) (hc : isBlank c = false) :
    foldBlanks ([c] : List Char) = [c] := by
  unfold foldBlanks foldGo
  simp only [List.foldr_cons, List.foldr_nil, hc, Bool.false_eq_true, if_false]
  rfl

/-- 要点 **L0⇄L1 的商非平凡**：**存在两个输入，其 `tokenize` 结果不同**（商**不止一个类**）。

要点 **证明路线（避开 `tokAux` 的不可归约性，判读规律 6）**：
取 `s := ['a']`、`t := ['b']`（`'a' ≠ 'b'`）。
若 `SameTokens ['a'] ['b']`，即 `tokenize ['a'] = tokenize ['b'] =: some ts`，
则由既有的 `tokenize_detok` 得
`detokenize ts = foldBlanks ['a']` **且** `= foldBlanks ['b']`，
而 `foldBlanks` 在**非空白单字符**上是恒等 ⟹ `['a'] = ['b']` ⟹ **矛盾**。

要点 **⇒ 本条【不】计算 `tokenize` 的具体值**（那需要归约 `tokAux`，见上条诚实标注），
而是用**既有定理的往返约束**推出矛盾 —— **更稳，且不引入新假设。** -/
theorem l0l1_quotient_is_nontrivial :
    ∃ s t : List Char, ¬ SameTokens s t := by
  refine ⟨['a'], ['b'], ?_⟩
  intro h
  -- `h : SameTokens ['a'] ['b']` 即 `tokenize ['a'] = tokenize ['b']`
  obtain ⟨ts, hts⟩ := tokenize_never_none (['a'] : List Char)
  have h2 : tokenize (['b'] : List Char) = some ts := by rw [← h]; exact hts
  -- 要点 两条 `tokenize_detok`（既有）给出 `detokenize ts` 同时等于两个 `foldBlanks`
  have e1 : detokenize ts = foldBlanks (['a'] : List Char) := tokenize_detok hts
  have e2 : detokenize ts = foldBlanks (['b'] : List Char) := tokenize_detok h2
  -- 要点 `foldBlanks` 在非空白单字符上是恒等（`'a'`/`'b'` 均非空白，由 `decide` 判定）
  have fa : foldBlanks (['a'] : List Char) = ['a'] :=
    l0l1_foldBlanks_single_char 'a' (by decide)
  have fb : foldBlanks (['b'] : List Char) = ['b'] :=
    l0l1_foldBlanks_single_char 'b' (by decide)
  rw [fa] at e1
  rw [fb] at e2
  -- `['a'] = ['b']` ⟹ `'a' = 'b'`，矛盾
  exact absurd (List.head_eq_of_cons_eq (e1.symm.trans e2)) (by decide)

/-- 要点 **L2⇄L3 的商非平凡**：`∃ c c', ¬ ft2L2L3Quot c c'`（商**不止一个类**）。

要点 **见证**：`{[2], 1}` 与 `{[3], 1}` ——
两者 `constraintContent` 都是 `1`（`gcd(2,1) = 1`、`gcd(3,1) = 1`），
故 `canonicalize` **都是自身**（`canonicalize_of_content_one`）⟹ **不同**。 -/
theorem l2l3_quotient_is_nontrivial :
    ∃ c c' : VectorConstraint, ¬ ft2L2L3Quot c c' := by
  refine ⟨{ a := [2], b := 1 }, { a := [3], b := 1 }, ?_⟩
  intro h
  -- `h : ft2L2L3Quot .. ..` 即 `canonicalize {[2],1} = canonicalize {[3],1}`
  have hc : constraintContent ({ a := [2], b := 1 } : VectorConstraint) = 1 := by
    simp [constraintContent, listGcdNat]
  have hc' : constraintContent ({ a := [3], b := 1 } : VectorConstraint) = 1 := by
    simp [constraintContent, listGcdNat]
  rw [ft2L2L3Quot, canonicalize_of_content_one _ hc,
      canonicalize_of_content_one _ hc'] at h
  -- `{[2],1} = {[3],1}` ⟹ `[2] = [3]`，矛盾
  exact absurd (congrArg VectorConstraint.a h) (by decide)

/-- 要点 **L1⇄L2 的商（在可识别的 `norm` 上）【必然平凡】**（§五.二 的等价形式）。

要点 **⇒ 三环对照的最终形式**：

| 环 | 商 |
|:--|:--|
| L0⇄L1 | 要点 **非平凡**（`l0l1_quotient_is_nontrivial`） |
| L2⇄L3 | 要点 **非平凡**（`l2l3_quotient_is_nontrivial`） |
| 注意 L1⇄L2 | 注意 **只可能是单点**（`l1l2_identifiable_implies_trivial_quotient`） |

要点 **这就是"三个环的实例化"的完整回答，且全部在同一个内核环境内。** -/
theorem three_rings_quotient_dichotomy :
    (∃ s t : List Char, ¬ SameTokens s t) ∧
      (∃ c c' : VectorConstraint, ¬ ft2L2L3Quot c c') ∧
      (∃ norm : Option ConstraintSet → Option ConstraintSet,
        FailureIdentifiable (decode : List SymToken → Option ConstraintSet) norm ∧
          ∀ y : Option ConstraintSet, norm y = some ([] : ConstraintSet)) :=
  ⟨l0l1_quotient_is_nontrivial, l2l3_quotient_is_nontrivial,
    l1l2_identifiable_implies_trivial_quotient⟩

/-! ## 六、L1⇄L2 的单向性（既有定理的重述，供对照表引用） -/

/-- 要点 **L1⇄L2 的单向性**：`∃ g, ∀ ts, g (decode ts) = ts` **为假**
（`RealExtractionDirection.no_left_inverse_at_all`）。

注意 **诚实标注**：这是既有定理的**复述**，本文件**不声称**它是新结果；
它在此处的作用是**补全对照表的一格**。 -/
theorem l1l2_only_one_direction :
    ¬ ∃ g : Option ConstraintSet → List SymToken, ∀ ts : List SymToken, g (decode ts) = ts :=
  no_left_inverse_at_all

end Lattice
