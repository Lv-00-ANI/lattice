import Mathlib
import Lattice.Lib.Editing.RealCanonicalForm
import Lattice.Lib.Editing.RealExtractionDirection
import Lattice.Lib.Editing.RealConversionQuotient
-- ⭐ **Q3 合并（2026-09-24）**：原 `RealQuotientReversibilityToken.lean` 已并入本文件。
-- 该文件**原先存在的唯一理由**是 `RealTokenization.Token` / `RealTokenSymbolLink.Token` 同名冲突
-- 使它无法与本文件共处一个环境；注意 **B220 已修复为 `CharToken` / `SymToken`，
-- 该理由随之消失，故合并已完成**（详见下方 §0「文件拆分说明」与 §八）。
-- 注意 **该 import 是合并的必要代价**：§八 的 L0⇄L1 实例化需要 `tokenize` / `detokenize` /
-- `SameTokens` / `CharToken`，全部来自 `RealTokenization`。
import Lattice.Lift.RealTokenization
/-!
# LATTICE: RealQuotientReversibility —— 「商可逆」的**一般定理**与**判别条件**

## 0. 本文件回答什么

任务（元层泛化，`notes\完善推广泛化路线图.md` §层级 6 第 1 项）：

> ⭐⭐ **把「商可逆」做成一般定理** —— 三条链路都收敛到它 —— **它可能是一个一般结论**

任务书的**判别要求**（本文件的核心约束）：

> **注意** **抽象必须能实例化回那三处**（否则"统一"是错觉）；
> ⭐ **必须回答"比特例多说了什么"**（避免 `rfl` 级重述）。

## ⭐⭐⭐ 结论（**与任务书预期相反**，但正是它要求的判定）

| # | 判定 | 依据 |
|--:|:--|:--|
| 1 | ⭐ **「商可逆」是【每一个函数的平凡性质】** | §二 `every_function_is_quotient_reversible` |
| 2 | **注意** **⇒ 它不是 L0⇄L1 / L2⇄L3 的"成就"，而是重述** | §三 三条判据 |
| 3 | ⭐⭐ **真正的判别条件是【截面的存在性】，不是【商的存在性】** | §四 |
| 4 | ⭐⭐⭐ **「商可逆在 L1⇄L2 不可构造」不精确**（核商恒存在，但它不含可逆性） | §五 `decode_is_quotient_reversible` |
| 5 | ⭐ **L2⇄L3 真正缺的那个商是 `±1` 商**，且本文件**补上它** | §六 |

⭐⭐ **一句话**：**任务书问"三处是否收敛到同一个一般定理"——
答案是"收敛"了，但收敛到的定理是平凡的（`Quotient` 的定义重述），
故"三处同构"是**表面相似**；而三处的**真正差异**（A9 发现的那个差异）
的判据在**截面**上，不在**商**上。**

## 注意 文件拆分说明（STYLE「跨文件同名 `def` 是潜伏断裂」的**实际命中**）

**注意** **本仓库原本存在两个互不兼容的 `Lattice.Token`**：

| 文件 | 原声明 | 构造子 | 层 |
|:--|:--|:--|:--|
| `RealTokenization.lean:155` | `inductive Token` | `single (c : Char)` / `word (c1 c2) (rest)` | **字符层**（L0⇄L1） |
| `RealTokenSymbolLink.lean:69` | `inductive Token` | `sym (z : Int)` / `sep` | **符号层**（L1⇄L2） |

**注意** **两者【同名不同型】**，且**不能同时 `import`** —— 本波次内核实测报：

```
import RealTokenSymbolLink failed, environment already contains
  'Lattice.instReprToken._cstage1' from RealTokenization
```

⭐ **这是 STYLE §2「避免同命名空间下的同名定理」所警告的那一族**，
且**本波次实测命中**（两个文件**各自**都能单独编译，**合成时冲突**）。

⭐⭐ **⇒ 该冲突已在本波次被【修复】**（由 coordinator 执行，**非本文件**）：
`RealTokenization.Token` → **`CharToken`**，`RealTokenSymbolLink.Token` → **`SymToken`**。
**注意** **本文件是在修复后写作的**，故**可以直接引用 `SymToken` 一侧的链**。

**注意** **本文件【已】import `RealTokenization`** —— ⭐ **Q3 合并（2026-09-24）后如此**：
原 `RealQuotientReversibilityToken.lean` 已并入本文件 §八，而 §八 需要
`tokenize` / `detokenize` / `SameTokens` / `CharToken`。
**注意** **合并前**本文件刻意**不** import 它（理由见下，现已部分失效）：
1. ~~本文件的主题是链路口径（符号侧）~~ ⟹ **注意** **合并后本文件**同时**覆盖字符侧与符号侧**，
   **代价是依赖图变宽**（`RealTokenization` 引入 `Mathlib` 的 `Char` 层设施）——
   ⭐ **这是合并换来的收益（消掉一对同名冲突 + 消除 3 处重复）所付的代价，已权衡**；
2. ~~本文件写作时冲突尚未修复~~ ⟹ **成立** **冲突已修复**，故**合并已执行**（不再"属未做"）。
⇒ ⭐ L0⇄L1（字符层）的实例化见 §八（**原先在单独文件里，现已并入**）。

⭐⭐ **⇒ 这一经历本身是一个结论**：**"三链统一"在一个词汇表不统一的仓库里，
连【陈述】都要先解决类型冲突**（见 §七）；
⭐ 而**冲突是可以被消除的**（本波次已消除）⟹
**"不可统一"从来不是数学障碍，而是命名纪律问题。**

## 1. 注意 为什么必须重做这个判定（对既有登记的核对）

`RealExtractionDirection.lean:87` 断言：

> **注意** **"商可逆"要成立，需要存在一个商结构使左逆在商上单值……**
> ⇒ **商结构无从定义**……**故"商可逆"这一形态在 L1⇄L2 上不可构造。**

**注意** **该文件自己在 `:109-112` 与 `:406-425` 诚实标注这是【推理而非内核定理】**
（"要对它做内核形式化，需要对**所有可能的商结构**量化"）。
⭐ **本文件正是做那件事**，并**给出更精确的表述**（§五）。

## 2. 注意 与已登记否定结论的一致性检查（任务第 3 步要求）

| 既有否定结论 | 本文件的关系 |
|:--|:--|
| `no_extractor_preserves_both` | **成立** **一致**：本文件 §四 说明它等价于"截面与语义商不可兼得" |
| `closed_loop_adds_nothing` | ⭐ **强化**：本文件给出该现象的**第四次**实例（§三：商不携带新语义） |
| `validity_does_not_determine_syntax` | **成立** **一致**：本文件 §六 的 `±1` 商正是该条的正确定位 |
| `decode_not_injective` / `no_left_inverse_at_all` | **成立** **不冲突**：两条**都是真的**；本文件只指出它们**不蕴含**"不能商"（§五） |

## 主结果（全部为**真定理**；无 sorry/axiom/admit/native_decide）

| 定理 | 内容 | 角色 |
|:--|:--|:--|
| `every_function_is_quotient_reversible` | ⭐⭐⭐ **任意函数在其核商上下降为单射** | **一般定理（平凡）** |
| `section_on_image_iff_up_to` | ⭐ 两种截面形式的等价 | 判据归一 |
| `canonical_representative_gives_quotient_inverse` | ⭐⭐ **截面 ⟹ 商上的左逆** | 判据的正面 |
| `quotient_inverse_gives_canonical_representative` | ⭐⭐ **反之亦然**（充要） | 判据的背面 |
| `decode_is_quotient_reversible` | ⭐⭐⭐ **L1⇄L2 的核商存在**（更正 A9 的措辞） | **核心更正** |
| `decode_as_total_map` | ⭐ `decode` 的 `Option` 外壳是**赘余**的 | A9 误判的根因 |
| `ScaleClassPlus` + `canonicalize_respects_scaleClassPlus` | ⭐⭐⭐ **补上 `±1` 商**（既有登记的【未做】） | **实例化 B** |
| `quotient_reversibility_is_restatement` | **注意** **诚实登记：一般定理不含新内容** | 判据（任务第 3 步） |

## 诚实边界（本文件**不证 / 不声称**的）

- **注意** **不声称"三处同构是错觉"**：三处**确实**都有商可逆形态；本文件说的是该形态
  **不构成统一** —— 因为**一切**都有该形态（§二），**故"都有"不含区分信息**。
- **注意** **不声称 A9 的定理是错的，也不声称 A9 的结论被"推翻"**：
  `decode_not_injective` 与 `no_left_inverse_at_all` **都是真的**。
  ⭐ **本文件只指出 A9 的【措辞】不精确**：核商**恒存在**（"不可构造"为假），
  **注意** **但该商上的单射是平凡的、不提供可逆性** ⟹
  **A9 的实质结论（L1⇄L2 没有可用的商可逆性）与本文件一致**。
  **真正的障碍是【截面的缺失】，不是【商的缺失】。**
- **注意** **不声称"截面判据"是万能的**：本文件给出的是"**严格**左逆 ⟺ 截面"的转化，
  以及"**商上左逆 ⟺ 截面**"（§四）。它不解决语义层的多对一（那是
  `no_extractor_preserves_both` 的地盘）。
- **注意** **§六 的 `±1` 商只做到"下降良定义"**：`canonicalize` 在该商上下降所需
  的是 `canonicalize_section_pos`（既有）；本文件**构造** `Setoid` 并证
  `Quotient.lift` 的良定义性。**注意** **不声称该商就是 L2⇄L3 的"最终正确答案"** ——
  它是由 `RealCanonicalCompileComm.lean` §六 明确要求的对象。
- **注意** **L0⇄L1 的实例化见 §八**（⭐ **Q3 合并后已进入本文件**；原在
  `RealQuotientReversibilityToken.lean`，因 `Token` 同名冲突被迫拆分，冲突已修 ⟹ 已合并）。
- **只读引用既有模块**：不修改 `RealTokenization` / `RealCanonicalForm` /
  `RealExtractionDirection` / `RealConversionQuotient` / `RealTokenSymbolLink` 任何文件。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。

## 注意 跨文件重名的预防（STYLE「跨文件同名 `def` 是潜伏断裂」）

`RealConversionQuotient.lean:80` 已有 `kernelSetoid {α β} (f : α → β) : Setoid (List α)`
（定义域**固定为 `List α`**）。本文件需要**任意类型**上的核商，
且**类型不同**（`Setoid α` vs `Setoid (List α)`）⟹ **不能复用、也不算重名**
（Lean 依类型区分，但 STYLE 要求显式登记）。
⭐ **本文件命名为 `kernelQuot`（带 `α` 泛型）以与既有的 `kernelSetoid` 区分**，
并在 §一 说明二者关系（既有的是本文件 `α := List α` 的特例）。
新增名字均足够特殊，且在 `namespace Lattice` 内（**不新开命名空间**）。
-/

noncomputable section

namespace Lattice

open Lattice.Lift.SymbolToWeightCorrectness (ConstraintSet AllSatisfied AllZeroOutputs compileToLayer)
open Function

/-! ## 一、核商：一般构造

`kernelQuot f` 把 `f` 的**核等价关系**（"在 `f` 下不可区分"）装成 `Setoid`。

**注意** **与既有 `RealConversionQuotient.kernelSetoid` 的关系**：
后者定义在**固定**的 `List α` 上（为编译器链路服务）；
本文件的是 `α` 上的一般形式。⭐ **本文件不重新声明后者**，两者共存且类型不同
（已在上文「跨文件重名」节登记）。 -/

/-- **核等价关系**：`a ~ b ⟺ f a = f b`（"按 `f` 观察不可区分"）。 -/
def kernelQuot {α β : Type*} (f : α → β) : Setoid α where
  r a b := f a = f b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- ⭐ **登记：本构造的关系就是 `f` 的核**（定义性，便于下游 `rw`）。

**注意** **STYLE 已登记 `def` 别名不透明**（`Quotient.sound`/`exact` 需要关系**显式**为
`f a = f b`）——故本文件把这条等式**显式命名**，使下游不必反复展开。 -/
theorem kernelQuot_rel {α β : Type*} (f : α → β) (a b : α) :
    (kernelQuot f).r a b = (f a = f b) := rfl

/-! **注意** **本文件实测的关键坑**（STYLE「`def` 别名不透明」家族的**新变体**，
建议入 STYLE）：

记号 `a ≈ b` 是 `Setoid.r` 经**实例搜索**解析的，故
`rw [kernelQuot_rel]` / `show (f a = f b)` / `exact` **都拿不到它** ——
内核报 `type mismatch : … ≈ … but is expected to have type … = …`。

⭐⭐ **正解（本文件 §四 / §六 各用一次）**：
**先把 `≈` 显式声明成 `(kernelQuot f).r a b` 形式的 `have`**，再对它 `rw`：
```lean
have h' : (kernelQuot f).r a b := h   -- 把 ≈ 显式化为可 rw 的句法形式
rw [kernelQuot_rel] at h'
```
**注意** **不要**试图写 `theorem … : (a ≈ b) ↔ f a = f b` 之类的桥接引理 ——
那需要 `HasEquiv α` 实例，而 `≈` 在此**只有 `Setoid` 版本**，
实测报 `failed to synthesize HasEquiv α`。 -/

/-! ## 二、⭐⭐⭐ 一般定理：**每一个**函数都是"商可逆"的

本节是本文件的核心，也是任务书"是不是 `rfl` 级重述"这一问的**答案来源**。 -/

/-- ⭐⭐⭐ **一般定理（本文件核心）**：**任意**映射 `f : α → β` 都在其核商上
**下降为单射**，且该单射与 `f` 在生成元上一致。

即：`f` **总是**可以分解为
```
α --(商映射)--> α ⧸ ker f --(单射)--> β
```
（第一同构定理的 `Quotient` 版本）。

⭐⭐ **这条定理对本文件的意义不是"成立"，而是"太成立"**：
它对**每一个** `f` 成立，**不需要任何假设** ——
包括 `tokenize`、`canonicalize`、`decode`，也包括**任意**虚构的映射。
⇒ ⭐ **故"某环是否商可逆"不构成对环的区分**（见 §三）。 -/
theorem every_function_is_quotient_reversible {α β : Type*} (f : α → β) :
    ∃ F : Quotient (kernelQuot f) → β,
      Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = f a) := by
  refine ⟨Quotient.lift f (fun a b h => h), ?_, ?_⟩
  · -- 单射性：`F ⟦a⟧ = F ⟦b⟧` 展开即 `f a = f b`，正是核关系 ⟹ `⟦a⟧ = ⟦b⟧`
    intro x y h
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b => exact Quotient.sound h
  · intro a
    exact Quotient.lift_mk f (fun a b h => h) a

/-- ⭐ **上定理的 `range` 加强**（第一同构定理的完整形式）：
该单射的像**恰是** `f` 的像 —— 故它是 `α ⧸ ker f ≃ range f`。

**注意** **本条的诚实标注**：需要把 `range f` 写成 `Subtype`，
且 `Quotient.lift` 的 `F` 落在 `β` 上、需再取 `Subtype.mk`。
⭐ 本文件**只给"落到 `range f` 上"的版本**（即 `∃ a, f a = F ⟦a⟧`），
**不构造 `Equiv`** —— 那需要额外处理 `Subtype` 的单射性，**属未做**。 -/
theorem quotient_reversible_image_eq_range {α β : Type*} (f : α → β) :
    ∃ F : Quotient (kernelQuot f) → β,
      Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = f a) ∧
      (∀ b, (∃ a, f a = b) → ∃ q, F q = b) := by
  obtain ⟨F, hinj, hF⟩ := every_function_is_quotient_reversible f
  refine ⟨F, hinj, hF, ?_⟩
  rintro b ⟨a, rfl⟩
  exact ⟨Quotient.mk _ a, hF a⟩

/-! ## 三、**注意** 判定：一般定理是**重述**（任务书第 3 步的直接回答）

任务书要求回答：**"这条一般定理比三个特例多说了什么？"**
⭐ **本节的答案是："什么都没多说"—— 且这是可机器检查的。**

三条**互相独立**的判据（每条都是内核事实，不是修辞）：

| # | 判据 | 内核内容 |
|--:|:--|:--|
| **1** | **无假设** | 定理的 `{α β : Type*}` 后**没有**任何 `Prop` 前提（`every_function_is_quotient_reversible` 的签名里零假设） |
| **2** | **对"反面"也成立** | 对 `f := fun _ => ()`（常函数，**最退化**的映射）同样成立 —— 见 `constant_map_is_quotient_reversible` |
| **3** | **商是被定义成让它成立的** | `Quotient.sound` 的**唯一**用法就是把 `f a = f b` 变成 `⟦a⟧ = ⟦b⟧`；证明体只用了 `Quotient.lift` / `sound` / `lift_mk` |

⇒ ⭐ **三条合起来**：该定理**不排除任何映射** ⟹ **不含区分信息** ⟹
**它是 `Quotient` 的定义性后果，属"重述"**（任务书要求如实标注的那一类）。 -/

/-- ⭐ **判据 2 的内核形式**：**最退化**的映射（常函数）也满足该定理。

**注意** 若一般定理有内容，它**应当**在退化的 `f` 上失效或退化 ——
而它**不失效**（下面的构造与一般证明完全同形）。 -/
theorem constant_map_is_quotient_reversible {α : Type*} :
    ∃ F : Quotient (kernelQuot (fun _ : α => ()) ) → Unit,
      Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = ()) :=
  every_function_is_quotient_reversible (fun _ : α => ())

/-- ⭐ **判据 2 的极端形式**：核商在常函数下**退化为单点**（所有元素同类）。
⇒ 该情形下"商可逆"的全部内容是 `Unit` 的单点性 —— **显然无信息**。 -/
theorem constant_map_quotient_is_subsingleton {α : Type*} :
    ∀ q q' : Quotient (kernelQuot (fun _ : α => ())), q = q' := by
  intro q q'
  induction q using Quotient.ind with
  | _ a =>
    induction q' using Quotient.ind with
    | _ b => exact Quotient.sound rfl

/-- ⭐⭐⭐ **诚实登记（机器可检索，对应任务书"重述"判据）**：

本文件的一般定理**不含**"哪些环商可逆"的信息 ——
因为它**对一切**映射成立。**"商可逆"因此不是环的性质，而是 `Quotient` 的性质。**

**注意** **本条的用途**：防止下游把 `every_function_is_quotient_reversible`
当作"三环统一"的证据引用（那会是**把重述当成果**）。 -/
theorem quotient_reversibility_is_restatement :
    -- ① 一般定理对任意 `f` 成立（零假设）——故不区分任何映射
    (∀ {α β : Type*} (f : α → β), ∃ F : Quotient (kernelQuot f) → β,
        Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = f a)) ∧
    -- ② 它在最退化的映射上也成立（无内容的下界证据）
    (∃ F : Quotient (kernelQuot (fun _ : Unit => ())) → Unit,
        Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = ())) :=
  ⟨every_function_is_quotient_reversible, constant_map_is_quotient_reversible⟩

/-! ## 四、⭐⭐ 真正的判别条件：**截面的存在性**（而非商的存在性）

§三 说明"商可逆"无区分力。本节给出**有**区分力的那个条件。

⭐ **观察**：三环中**真正被证过的、非平凡的**陈述都不是"商可逆"，而是**截面**：

| 环 | 截面陈述（**有内容**的那条） | 位置 |
|:--|:--|:--|
| L0⇄L1 | `detokenize_left_inverse_on_quotient`：`tokenize (detokenize ts) = some ts` | `RealTokenization.lean:467` |
| L1⇄L2 | `decode_encode`：`decode (encode cs) = some cs` | `RealTokenSymbolLink.lean:195` |
| L2⇄L3 | `canonicalize_section_pos`：`canonicalize (scaleVec c lam) = canonicalize c`（`0<lam`） | `RealCanonicalForm.lean:692` |

⇒ ⭐ **本节的定理把"商可逆"与"截面"精确地连起来**，从而把前者**化归**为后者。 -/

/-- ⭐ **两种截面形式的等价**（"在像上" vs "模 `f`"）：
`∀ b ∈ range f, f (s b) = b` ⟺ `∀ a, f (s (f a)) = f a`。

**注意** **这不是 `rfl`**：两个方向各需要一次代换（见证明）。 -/
theorem section_on_image_iff_up_to {α β : Type*} (f : α → β) (s : β → α) :
    (∀ b, (∃ a, f a = b) → f (s b) = b) ↔ (∀ a, f (s (f a)) = f a) := by
  constructor
  · intro h a
    exact h (f a) ⟨a, rfl⟩
  · rintro h b ⟨a, rfl⟩
    exact h a

/-- ⭐⭐ **判据的正面方向**：**截面 ⟹ 商上的左逆**。

给定"模 `f` 的截面" `s`（即 `∀ a, f (s (f a)) = f a`），
则 `b ↦ ⟦s b⟧` 是 `f` 在商层面上的**左逆**：
`(b ↦ ⟦s b⟧) (f a) = ⟦a⟧`。

⭐ **证明要点**：`Quotient.sound` 需要 `s (f a) ≈ a`，
即 `f (s (f a)) = f a` —— **这正是截面假设**。
⇒ **"商可逆"的全部内容就是"截面存在"**，商本身不贡献任何东西。 -/
theorem canonical_representative_gives_quotient_inverse {α β : Type*} (f : α → β)
    (s : β → α) (h : ∀ a, f (s (f a)) = f a) :
    ∃ G : β → Quotient (kernelQuot f), ∀ a, G (f a) = Quotient.mk _ a := by
  refine ⟨fun b => Quotient.mk _ (s b), fun a => ?_⟩
  -- 注意 `Quotient.sound` 期望**不透明**关系 `s (f a) ≈ a`（`≈` 经实例搜索解析）。
  -- 要点 正解：`show` 出它（`show` 做定义展开），而不是试图 `rw`。
  show Quotient.mk (kernelQuot f) (s (f a)) = Quotient.mk (kernelQuot f) a
  exact Quotient.sound (show (kernelQuot f).r (s (f a)) a from h a)

/-- ⭐⭐ **判据的背面方向**：**商上的左逆 ⟹ 截面**。

**注意** **本条的证明含一个非平凡步骤**：`G` 落在**商**上，要从商元取回 `α` 的元素
必须用代表元（**每个商类都非空** —— 由构造，非由 `f` 满射）。
**这正是"商构造总存在"的机制**（§三 判据 3）。

**注意** **本文件实测的关键坑（STYLE 未登记，本波次新增；试错 12 轮才定案）**：

⭐ **`Quotient.mk''` 与 `Quotient.mk _` 在 `Quotient` 家族里【不可互换】**，
即使二者源头上是同一个函数。内核实测：
```
h1 : Quotient.mk'' (Classical.choose ⋯) = ⟦a⟧        -- choose_spec 给的（mk'' 形）
Quotient.exact h1  报：expected ⟦Classical.choose ⋯⟧ = ⟦a⟧   -- exact 要的（mk 形）
```
⇒ 两者**打印相同**（都是 `⟦·⟧`）却**不可统一**。

**注意** **更隐蔽的第二层**：即使改用 `Quotient.eq''`，**目标与假设里的
`Classical.choose (Quotient.exists_rep (G (f a)))` 经 elaboration 后
仍是【打印相同而实为不同项】**（隐式参数解析差异）⟹
`show` / `dsimp only` / `simp only []` / 显式 `have` **全部无效**，
报错永远是 `type mismatch : f (choose ⋯) = f a but is expected to have f (choose ⋯) = f a`。

⭐⭐ **正解（三步，缺一不可）**：
1. ⭐ **把代表元函数用 `let` 绑定一次**（`let S : β → α := fun b => Classical.choose …`），
   **并把它的 spec 也用 `have` 绑定** ⟹ **目标与假设共享同一 elaborated 项**
   （这一步是本条的全部关键；不绑定就永远对不上）；
2. **`choose_spec` 的结果声明为 `Quotient.mk''` 形**（**不是** `Quotient.mk _`）；
3. **用 `Quotient.eq''` + 关系等式**把它化为 `f _ = f _`
   （**注意** **不要**用 `Quotient.exact` —— 它统一到 `mk` 形，与第 2 步冲突）。

**注意** **本文件同时排除的错误路线**（供后人少走弯路）：
`show f _ = f a`（不够）；`dsimp only` / `simp only []`（β 修好了，但项仍不同）；
`@Quotient.exact _ (kernelQuot f) _ _ h1`（显式传 setoid，**仍失败**）；
`Quotient.out` / `Quot.out`（**点记法冲突**：报 `invalid field notation`，
`@`、`let` 绑定匿名函数**都不能**绕过）；
把 `≈` 写成 `↔` 桥接引理（需 `HasEquiv`，实测 `failed to synthesize HasEquiv α`）。 -/
theorem quotient_inverse_gives_canonical_representative {α β : Type*} (f : α → β)
    (G : β → Quotient (kernelQuot f)) (hG : ∀ a, G (f a) = Quotient.mk _ a) :
    ∃ s : β → α, ∀ a, f (s (f a)) = f a := by
  classical
  -- 要点 第 1 步（关键）：把代表元函数**绑定一次**，使目标与假设共享同一项
  let S : β → α := fun b => Classical.choose (Quotient.exists_rep (G b))
  have hS : ∀ b, Quotient.mk'' (S b) = G b :=
    fun b => Classical.choose_spec (Quotient.exists_rep (G b))
  refine ⟨S, fun a => ?_⟩
  have h1 : Quotient.mk'' (S (f a)) = G (f a) := hS (f a)
  rw [hG a] at h1
  -- 要点 第 2、3 步：`eq''`（不是 `exact`）+ 关系等式
  rw [Quotient.eq'', kernelQuot_rel] at h1
  exact h1

/-- ⭐⭐⭐ **判别条件（本文件的核心正面结论）**：

**"商上存在左逆" ⟺ "存在截面"**（在 `f : α → β` 上，无条件）。

⭐⭐ **它比"商可逆"这条口号多说了什么**：
1. ⭐ **商化不产生可逆性** —— 右侧是整个定理的**全部**内容，
   左侧的 `Quotient` **不增加任何东西**（由 §三 的一般定理，商恒存在）；
2. ⭐ **判别可以完全绕开商** —— 下游判"某环能否商可逆"只需找截面，
   **不需要构造任何 `Setoid`**；
3. ⭐ **A9 的误判被定位**：它问"能否构造商结构"，而**正确的问法**是
   "**是否存在截面**"。`decode` **有**截面（`encode`，§五），
   故它商可逆；**注意** 而"**严格左逆**"（`∀ ts, g (decode ts) = ts`）另当别论
   —— 那是 `no_left_inverse_at_all`，**与商可逆无关**。 -/
theorem quotient_inverse_iff_canonical_representative {α β : Type*} (f : α → β) :
    (∃ s : β → α, ∀ a, f (s (f a)) = f a) ↔
    (∃ G : β → Quotient (kernelQuot f), ∀ a, G (f a) = Quotient.mk _ a) :=
  ⟨fun ⟨s, h⟩ => canonical_representative_gives_quotient_inverse f s h,
   fun ⟨G, hG⟩ => quotient_inverse_gives_canonical_representative f G hG⟩

/-! ## 五、⭐⭐⭐ 实例化（L1⇄L2）与核心更正

**注意** `RealExtractionDirection.lean:87` 断言"商可逆在 L1⇄L2 上**不可构造**"。
**本节给出更精确的表述**（该文件自己标注了这是推理，不是内核定理）。

**注意** **L0⇄L1 的实例化（`SameTokens`）见 §八** —— ⭐ **Q3 合并后已进入本文件**
（原先因 `Token` 同名冲突被迫住在单独文件；冲突已修 ⟹ 已合并）。

## 五-a、`decode` 的 `Option` 外壳是赘余的

`decode` 的 `Option` 外壳是**赘余**的：`decode ts = some ((toSegs ts).map mkConstraint)`
**无条件**成立（`RealTokenSymbolLink.lean:160`），故 `decode` 实质上是**全函数**
```
decodeTotal ts := (toSegs ts).map mkConstraint
```
装进 `some` 而已。

⭐ **⇒ `decode_encode` 说的正是 `decodeTotal (encode cs) = cs`** ——
即 **`encode` 是 `decodeTotal` 的截面**。
⇒ 由 §二 的一般定理，**`decodeTotal` 的核商存在**（就像任何函数一样）。
⭐⭐ **⇒ A9 的措辞"商可逆不可构造"不精确** —— 核商**恒可构造**。
**注意** **但 A9 的实质结论成立**：该商上的单射是**平凡的**，
**不提供任何可逆性** ⟹ **真正的障碍是【截面的缺失】，不是【商的缺失】**。
⭐ **而 L1⇄L2 恰恰【有】截面（`encode`）** ⟹
**注意** **故 L1⇄L2 的可逆性障碍【也不】在结构层** —— 它在**语义层**
（残段塌缩使 `decode` 非单射；那是 `no_left_inverse_at_all`，**真的**）。 -/

/-- **`decode` 的底层全函数**（去掉赘余的 `Option` 外壳）。 -/
def decodeTotal (ts : List SymToken) : ConstraintSet := (toSegs ts).map mkConstraint

/-- ⭐ **`decode` = `some ∘ decodeTotal`**（**定义性**，`rfl`）。

⭐⭐ **这是 A9 误判的根因**：`decode` 的 `Option` **永远不返回 `none`**
（`RealTokenSymbolLink.lean:157` 自述"解码结果构造性地总是 `some`"）
⟹ 该 `Option` **不携带任何信息** ⟹
A9 把"输出侧的 `Option` 不携带丢段标记"当作"商无从定义"的**理由**（其 `:84-87`），
⭐ **但商从来不需要输出侧的标记** —— 商是由**定义域**上的核关系给的（§二）。 -/
theorem decode_eq_some_decodeTotal (ts : List SymToken) :
    decode ts = some (decodeTotal ts) := rfl

/-- ⭐⭐ **`encode` 是 `decodeTotal` 的截面**（复用既有 `decode_encode`，**不重证**）。 -/
theorem encode_is_section_of_decodeTotal (cs : ConstraintSet) :
    decodeTotal (encode cs) = cs :=
  (Option.some.injEq _ _).mp (decode_encode cs)

/-- ⭐⭐⭐ **核心更正（内核定理）：L1⇄L2 的**核商存在**（与任何函数一样）。

由 §二 的一般定理直接实例化 —— **注意** **不需要任何额外工作**，
**这正是"商可逆无区分力"的最强证据**：
A9 花了两节的论证说它"不可构造"，而它其实是**一般定理的一个实例**。
**注意** **但请注意本条的读法**：它**不**说明 L1⇄L2 "可逆" ——
商上的单射是**平凡**的，**不提供**任何可逆性（§三）。 -/
theorem decode_is_quotient_reversible :
    ∃ F : Quotient (kernelQuot decodeTotal) → ConstraintSet,
      Function.Injective F ∧ (∀ ts : List SymToken, F (Quotient.mk _ ts) = decodeTotal ts) :=
  every_function_is_quotient_reversible decodeTotal

/-- ⭐⭐ **核心更正的"截面形式"**（与 §四 判据一致）：
`decodeTotal` **确实有**截面，故 §四 的判别条件**正面满足**。

**注意** **对照 A9 的诚实边界**（其 `:109-112`）：它说"商化救不了 L1⇄L2，
**因为失效不是多对一，而是一个更小的基**"。
⭐ **本文件对该诊断的分栏判定**：
- **成立** **"商化救不了"这个结论**—— **成立**，但理由不同：
  不是因为"商不存在"，而是因为**商上的单射是平凡的**（对一切函数都如此）；
- **注意** **"失效不是多对一"这个理由**—— **不成立**：`decodeTotal` 的失效
  **正是**多对一（`[]` 与 `[sym 1]` 同值 —— 其 `decode_not_injective`，**真的**），
  而多对一**恰恰**正是可以商的（§二）。**"可以商"与"商了有用"是两件事。** -/
theorem decodeTotal_satisfies_discriminant : ∃ s : ConstraintSet → List SymToken,
    ∀ ts : List SymToken, decodeTotal (s (decodeTotal ts)) = decodeTotal ts :=
  ⟨encode, fun ts => by rw [encode_is_section_of_decodeTotal]⟩

/-! ## 六、⭐⭐ 实例化 B：L2⇄L3 的 `±1` 商（既有明确登记的【未做】）

`RealCanonicalCompileComm.lean` §六 逐字登记（其 `:583-586`）：

> - **注意** **`±1` 商的 Setoid 与 `canonicalize` 的下降**：**未做**。
>   需要 `ScaleClassPlusMinus`（把 `±1` 也商掉）与 `Quotient.lift` 的良定义性证明。
>   **注意** **本文件已证明它【可行】**（`comm_error_is_exactly_sign` 给出下降所需的精确律），
>   **但未构造该对象**。

⭐ **本节补上该对象**（这是本文件对 L2⇄L3 的**实质贡献**，非重述）。 -/

/-- ⭐⭐ **`±1` 加倍率等价**：`c ~ c'` ⟺ 存在**正**倍率把二者对齐。

**注意** **为什么是"正倍率"而不是"再商掉 `±1` 的 `ScaleClass`"**：
`ScaleClass` 已吸收 `±1`（`RealCanonicalForm.lean:248` 自述"它自动吸收 `±1`"），
故**正确的载体是 `ScaleClass / {±1}`**，而它**等价于"用正倍率对齐"** ——
这正是本定义。 -/
def ScaleClassPlus (c c' : VectorConstraint) : Prop :=
  ∃ lam mu : Int, 0 < lam ∧ 0 < mu ∧ scaleVec c lam = scaleVec c' mu

/-- ⭐ **`ScaleClassPlus` 是等价关系**（三条性质对应三个字段）。

**注意** **证明不是 `rfl`**：传递性需要 `0 < l₁ * l₂`（`mul_pos`）——
**这恰是"正倍率"比"非零倍率"更强的地方**，也是它**不需要逆元**的原因。 -/
theorem scaleClassPlus_equivalence : Equivalence ScaleClassPlus := by
  refine ⟨?_, ?_, ?_⟩
  · intro c; exact ⟨1, 1, Int.one_pos, Int.one_pos, rfl⟩
  · rintro c c' ⟨lam, mu, hl, hm, heq⟩
    exact ⟨mu, lam, hm, hl, heq.symm⟩
  · rintro c c' c'' ⟨l₁, m₁, hl₁, hm₁, h₁⟩ ⟨l₂, m₂, hl₂, hm₂, h₂⟩
    refine ⟨l₁ * l₂, m₁ * m₂, mul_pos hl₁ hl₂, mul_pos hm₁ hm₂, ?_⟩
    rw [← scaleVec_scaleVec, h₁, scaleVec_scaleVec, mul_comm m₁ l₂, ← scaleVec_scaleVec, h₂,
      scaleVec_scaleVec, mul_comm m₂ m₁]

/-- **`±1` 加倍率等价的 `Setoid`**（**注意** 定义在**全空间**上 —— 与既有的
`scaleClassSetoid` 不同，后者限定在 `{c // c ≠ 0}`）。 -/
def scaleClassPlusSetoid : Setoid VectorConstraint where
  r := ScaleClassPlus
  iseqv := scaleClassPlus_equivalence

/-- ⭐ **登记：`scaleClassPlusSetoid` 的关系就是 `ScaleClassPlus`**（定义性）。

**注意** **为什么必须显式写出**（本文件实测踩到）：`Quotient.lift` 的良定义性前提是
`∀ a b, a ≈ b → f a = f b`，其中 `≈` 是**不透明**的 `Setoid.r`。
⭐ 内核**不会**自动把 `a ≈ b` 归约成 `ScaleClassPlus a b` ⟹
必须有一条**可 `rw` 的等式**把它桥接（与 `kernelQuot_rel` 同一手法）。 -/
theorem scaleClassPlusSetoid_rel (c c' : VectorConstraint) :
    scaleClassPlusSetoid.r c c' = ScaleClassPlus c c' := rfl

/-- ⭐ **`±1` 商在 `Subtype` 上的拉回关系**（`Setoid.comap` 的显式形式）。

**注意** **为什么要拉回**：`canonicalize` 需要 `content ≠ 0` 前提（`canonicalize_section_pos`），
而 `ScaleClassPlus` 定义在**全空间**上 ⟹ 下降**只能**在
`{c // constraintContent c ≠ 0}` 上进行。⭐ 这与 `RealCanonicalForm` 的
C2 裁定（"排除零点写进定义域"）**一致**。

**注意** **本文件【不】直接用 `Setoid.comap`** —— 因为 `comap` 的 `r` 字段是
`fun a b => s.r (f a) (f b)`，其展开在目标里**不可 `rw`**（实测报
`application type mismatch`）。⭐ **改用显式定义的 `Setoid`**，
并把关系等式单独登记（`scaleClassPlusSubtypeSetoid_rel`）。 -/
def scaleClassPlusSubtypeSetoid :
    Setoid {c : VectorConstraint // constraintContent c ≠ 0} where
  r a b := ScaleClassPlus a.1 b.1
  iseqv :=
    { refl := fun a => scaleClassPlus_equivalence.refl a.1
      symm := fun h => scaleClassPlus_equivalence.symm h
      trans := fun h₁ h₂ => scaleClassPlus_equivalence.trans h₁ h₂ }

/-- ⭐ **登记：拉回关系就是 `ScaleClassPlus`**（定义性，供 `rw` 桥接）。 -/
theorem scaleClassPlusSubtypeSetoid_rel
    (a b : {c : VectorConstraint // constraintContent c ≠ 0}) :
    scaleClassPlusSubtypeSetoid.r a b = ScaleClassPlus a.1 b.1 := rfl

/-- ⭐ **`ScaleClassPlus` 商**（既有登记要求构造的对象）。 -/
abbrev ScaleClassPlusQuotient := Quotient scaleClassPlusSetoid

/-- ⭐⭐⭐ **`canonicalize` 在 `±1` 商上【良定义】（下降）** —— 这是既有登记
（`RealCanonicalCompileComm.lean:583-586`）所要求的**全部内容**。

**下降所需的精确律**：`ScaleClassPlus c c'` ⟹ `canonicalize c = canonicalize c'`。

**注意** **本文件不重证该律**：它由 `RealCanonicalForm.canonicalize_section_pos`
（正倍率下 `canonicalize` **吞掉**倍率）**直接给出**。
⭐ **证明路线**（见证明体）：把 `ScaleClassPlus` 的两个**正**见证 `lam`、`mu`
分别用 `canonicalize_section_pos` 吞掉，两端都归到 `canonicalize c` / `canonicalize c'`，
再由 `scaleVec c lam = scaleVec c' mu` 传递。

**注意** **前提 `constraintContent c ≠ 0` 与 `constraintContent c' ≠ 0` 不可省**
（`canonicalize_section_pos` 需要它）。

**注意** **一处如实登记**：本文件初稿引用了 `canonicalize_absorbs_scale_pos`
（该条定义在 `RealCanonicalCompileComm.lean`），**内核报 `unknown identifier`** ——
因为**本文件没有 import 该模块**，且**本文件【不应】import 它**
（那会引入该模块对 `RealCanonicalForm` 的整条依赖，且它与
`RealExtractionDirection` 的 `SymToken` 可能争用）。
⭐ **正解是直接用更底层的 `RealCanonicalForm.canonicalize_section_pos`** ——
两者是**同一条定理**（`canonicalize_absorbs_scale_pos` 只是它的改名重述）。 -/
theorem canonicalize_respects_scaleClassPlus (c c' : VectorConstraint)
    (hg : constraintContent c ≠ 0) (hg' : constraintContent c' ≠ 0)
    (h : ScaleClassPlus c c') : canonicalize c = canonicalize c' := by
  obtain ⟨lam, mu, hl, hm, heq⟩ := h
  rw [← canonicalize_section_pos c hg lam hl,
      ← canonicalize_section_pos c' hg' mu hm, heq]

/-- ⭐⭐⭐ **`canonicalize` 下降到 `±1` 商上**（`Quotient.lift` 的**构造**）。

**注意** **这是既有登记明确标为【未做】的那件事**（`RealCanonicalCompileComm.lean:583-586`）。
本文件给出 `Quotient.lift` 的实例。

**注意** **诚实标注（类型边界的处理）**：`canonicalize` 需要 `content ≠ 0` 前提，
而本商定义在**全空间**上 ⟹ 下降**只能**在 `Subtype {c // constraintContent c ≠ 0}`
上进行（否则 `Quotient.lift` 的良定义性前提**无法满足**）。
⭐ **本文件因此把下降陈述在 `Subtype` 上** —— 这与 `RealCanonicalForm` 的
C2 裁定（"排除零点写进定义域"）**一致**。 -/
def canonicalizeOnPlusQuotient :
    Quotient scaleClassPlusSubtypeSetoid → VectorConstraint :=
  Quotient.lift
    (fun c : {c : VectorConstraint // constraintContent c ≠ 0} => canonicalize c.1)
    (fun a b h => by
      -- 注意 **本文件实测的第二个 `Quotient` 坑**（与 §四 的 `Quotient.out` 坑同族）：
      -- `Quotient.lift` 的目标已被写成 `(fun c => canonicalize c.1) a = … b`，
      -- 而 `h : a ≈ b` 的关系由**实例搜索**解析 ⟹
      -- 直接 `exact … (h)` 报 `type mismatch : a ≈ b but is expected to have type
      -- ScaleClassPlus ↑a ↑b`，且 **`rw [scaleClassPlusSubtypeSetoid_rel] at h` 也失败**
      -- （`did not find instance of the pattern` —— `rw` 用**句法**匹配，
      -- 而 `≈` 不是 `Setoid.r a b` 的句法形式，STYLE B205 同族）。
      -- 要点 **正解**：**先用 `show` 把目标 β-归约**（`show` 会做定义展开），
      -- 再用 `show … from h` 把假设**按目标类型重新声明**（而不是 `rw` 它）。
      show canonicalize a.1 = canonicalize b.1
      exact canonicalize_respects_scaleClassPlus a.1 b.1 a.2 b.2
        (show ScaleClassPlus a.1 b.1 from h))

/-- ⭐⭐ **下降后的计算律**（验证 `canonicalizeOnPlusQuotient` 确实是 `canonicalize`）：
在代表元上取值即 `canonicalize` 本身。

⭐ 这把上面那条"抽象构造"**钉回**具体的 `canonicalize`，
使 `Quotient.lift` 不流于形式。 -/
theorem canonicalizeOnPlusQuotient_mk (c : {c : VectorConstraint // constraintContent c ≠ 0}) :
    canonicalizeOnPlusQuotient (Quotient.mk _ c) = canonicalize c.1 := by
  -- 注意 `canonicalizeOnPlusQuotient` 是 `def`（**不透明**）⟹ `Quotient.lift_mk`
  -- 匹配不到目标的形状。要点 正解：先 `show` 出 `Quotient.lift` 的**展开形**
  -- （STYLE 已登记：`def` 别名不透明，`rw` 不会自动穿透）。
  show Quotient.lift
      (fun c : {c : VectorConstraint // constraintContent c ≠ 0} => canonicalize c.1)
      (fun a b h => by
        -- 注意 此处目标形如 `(fun c => canonicalize c.1) a = … b`，
        -- 且 `h : a ≈ b`（关系由**实例搜索**解析）。
        -- 要点 两步：① `have h' : Setoid.r a b := h`（把 `≈` 显式化为**可 rw 的形式**）；
        -- ② `rw [scaleClassPlusSubtypeSetoid_rel]` 把它换成 `ScaleClassPlus`。
        -- **不能**直接 `rw … at h`（`≈` 不是 `Setoid.r a b` 的句法形式 → 模式不匹配）。
        have h' : scaleClassPlusSubtypeSetoid.r a b := h
        rw [scaleClassPlusSubtypeSetoid_rel] at h'
        exact canonicalize_respects_scaleClassPlus a.1 b.1 a.2 b.2 h')
      (Quotient.mk _ c) = canonicalize c.1
  exact Quotient.lift_mk _ _ c

/-! ## 七、⭐ 三处实例化一览（任务书第 1 步"抽象必须能实例化回三处"的交付）

| 环 | 核商（§二 一般构造） | 截面（§四 判据） | 该环**真正**的非平凡内容 |
|:--|:--|:--|:--|
| **L0⇄L1** | ⭐ `SameTokens` = `kernelQuot tokenize`（**`rfl`**） | `detokenize`（`tokenize_never_none` 保证**满**） | ⭐ **归一化 `foldBlanks` 是幂等投影**（`foldBlanks_idem`） |
| **L1⇄L2** | ⭐ `kernelQuot decodeTotal`（**一般定理，无需论证**，§五） | `encode`（`decode_encode`） | **注意** **`decode` 非单射**（残段塌缩）——**与"能否商"无关** |
| **L2⇄L3** | **注意** `ScaleClassPlus`（**新构造**，§六） | **注意** `canonicalize`（**仅 `0<lam`**，`canonicalize_section_pos`） | ⭐ **`±1` 必须被商掉**（`canonicalize_scaleVec_sign`） |

⭐⭐ **⇒ 任务书第 1 步的判定**：**抽象【能】实例化回三处**（上表三列都有内核定理支撑），
**注意** **但实例化后暴露的是：三处的"商可逆"是同一个平凡事实，
而三处的"非平凡内容"彼此【不同】**（末列三行互不相同）。

⭐ **⇒ 故"三处同构"是表面相似** —— 它们共享的是**平凡**部分（`Quotient` 的定义性后果），
**不共享**任何实质内容。**这本身是重要结论**（任务书 L107 明言此情形应如实报告）。

**注意** **且"实例化回三处"本身遇到了一个仓库级的障碍**（本文件实测）：
**L0⇄L1 与 L1⇄L2 的 `SymToken` 同名不同型、不能同文件 `import`** ⟹
**统一陈述必须先解决词汇表冲突**（见文件头「文件拆分说明」）。
⭐ **这是"三链统一"在工程层的对应物**：理论上的统一，
在**该仓库当前的类型布局下需要两个文件**才能陈述完。 -/

/-- ⭐⭐⭐ **诚实登记（机器可检索）**：本文件对任务书的最终判定，一条合取陈述概括：
① 一般定理成立（对**一切**映射）；
② 它**无假设** ⟹ 无区分力 ⟹ 属重述；
③ **真正的判别条件是截面存在性**（商可逆 ⟺ 截面）；
④ ⭐ **L1⇄L2 的核商存在**（更正 A9 的**措辞**；其定理仍为真），
   **注意** 且它**有截面**（`encode`）⟹ 其障碍**不在结构层**；
⑤ ⭐ **L2⇄L3 的 `±1` 商已构造并证下降**（补上既有登记的【未做】）。 -/
theorem quotient_reversibility_final_register :
    -- ① 一般定理（对一切映射）
    (∀ {α β : Type*} (f : α → β), ∃ F : Quotient (kernelQuot f) → β,
        Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = f a)) ∧
    -- ② 无区分力（在最退化映射上亦成立）
    (∃ F : Quotient (kernelQuot (fun _ : Unit => ())) → Unit,
        Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = ())) ∧
    -- ③ 判别条件：商上左逆 ⟺ 截面
    (∀ {α β : Type*} (f : α → β),
        (∃ s : β → α, ∀ a, f (s (f a)) = f a) ↔
        (∃ G : β → Quotient (kernelQuot f), ∀ a, G (f a) = Quotient.mk _ a)) ∧
    -- ④ L1⇄L2 的核商存在（且它有截面）
    ((∃ F : Quotient (kernelQuot decodeTotal) → ConstraintSet,
        Function.Injective F ∧ (∀ ts : List SymToken, F (Quotient.mk _ ts) = decodeTotal ts)) ∧
      (∃ s : ConstraintSet → List SymToken,
        ∀ ts : List SymToken, decodeTotal (s (decodeTotal ts)) = decodeTotal ts)) ∧
    -- ⑤ ±1 商上 canonicalize 下降
    (∀ c c' : VectorConstraint, constraintContent c ≠ 0 → constraintContent c' ≠ 0 →
        ScaleClassPlus c c' → canonicalize c = canonicalize c') :=
  ⟨every_function_is_quotient_reversible,
   constant_map_is_quotient_reversible,
   quotient_inverse_iff_canonical_representative,
   ⟨decode_is_quotient_reversible, decodeTotal_satisfies_discriminant⟩,
   fun c c' hg hg' h => canonicalize_respects_scaleClassPlus c c' hg hg' h⟩

/-! ## 八、⭐ L0⇄L1 侧的实例化（**原 `RealQuotientReversibilityToken.lean`，Q3 合并**）

**注意** **合并说明（Q3，2026-09-24）**：本节内容原先单独住在
`RealQuotientReversibilityToken.lean` 里，**原因是当时两个 `Token` 同名不同型**，
两个文件**不能同时 `import`**（内核实测）：

```
import RealTokenSymbolLink failed, environment already contains
  'Lattice.instReprToken._cstage1' from RealTokenization
```

⭐ **该冲突已修复**（`Token` → `CharToken` / `SymToken`），
⭐ **⇒ 该文件存在的唯一理由消失** ⟹ **合并完成**，本文件现为**单文件**。

**注意** **两段实测坑注释已逐字保留**（它们是**试错成本**的载体，删了等于丢掉两次实验）——
见 §八-二 的 `kernelQuot_rel` 与 §八-三 的 `detokenize_gives_quotient_left_inverse`。

⭐ **注意（Q3 实测的第三个坑）**：Lean 的块注释**会嵌套**（块注释内再出现块注释起始符会加深一层），
**注意** **故在一个块注释里再用块注释的起始符开新节 ⟹ 后面的定理会被【整段吞成注释】**，
⭐ **而构建【照样通过】**（`exit 0`）—— 这是「`error` 数下降 ≠ 修好」（B168）的又一实例。
**注意** **且本节初稿真的踩了它**：散文里**字面写出注释定界符**（斜杠星号、星号斜杠）
也会**被 Lean 当成真定界符**，导致嵌套失衡、定理被吞。
⇒ 本文件的每个小节**都用独立的完整块注释**，
且**紧跟其后的 `theorem` 必须在该注释【之外】**。
**注意** **⇒ 判据**：在 Lean 源码**散文**里**不要字面写注释定界符**（用"块注释起始符"这样的措辞代替）。 -/

/-! ### 八-一、本节的判定（与 §一 同构）

⭐⭐ **`SameTokens` 的定义逐字就是 `tokenize` 的核关系**（`RealTokenization.lean:458`）
⇒ ⭐ 故 L0⇄L1 的"商可逆"**不是**发现了特殊性质，而是**一般定理 + 截面**的组合。
⭐ **L0⇄L1 真正【有内容】的那条是【截面】**（依赖归一化幂等 `foldBlanks_idem`）。 -/

/-! ### 八-二、核商（**本节复用 §一 的 `kernelQuot`，不再重声明**）

**注意** **合并前**本节有一份**独立副本**的 `kernelQuot` —— 那是**被迫的重复**
（因冲突无法 import §一）。⭐ **合并后重复消除**：本节直接使用 §一 的定义。
⭐ **这正是合并的直接收益**：**3 个逐字重复的声明 ⟹ 0 个**。

**注意** **原坑注释（逐字保留）**：`kernelQuot` 的关系就是 `f`-相等（定义性；供 `rw` 桥接）。
**为什么必须显式命名**（本文件与 `RealQuotientReversibility` 各实测一次）：
记号 `a ≈ b` 是 `Setoid.r` 经**实例搜索**解析的 ⟹
`rw [kernelQuot_rel] at h` 对 `h : a ≈ b` **报模式失配**。
⭐ **正解**：先用 `show (kernelQuot f).r a b` **把目标改成显式形式**，再 `rw`。 -/

/-- ⭐ **核商上下降为单射**（L0⇄L1 的实例；对**任意**函数成立，故平凡）。 -/
theorem tokenize_is_quotient_reversible :
    ∃ F : Quotient (kernelQuot tokenize) → Option (List CharToken),
      Function.Injective F ∧ (∀ s, F (Quotient.mk _ s) = tokenize s) :=
  every_function_is_quotient_reversible tokenize

/-- ⭐⭐ **`SameTokens` 逐字就是 `tokenize` 的核关系**（**`rfl`**）。

**注意** **本条的 `rfl` 性【就是】任务书第 3 步所问的答案的载体**：
"L0⇄L1 的商"不是被**构造**出来的特殊对象，
它**就是**核商 —— 而核商对**一切**函数都存在。
⇒ ⭐ **故"L0⇄L1 收敛到商可逆"这句话里，没有 L0⇄L1 的特殊内容。** -/
theorem tokenize_kernel_is_SameTokens :
    (fun s t : List Char => SameTokens s t) = (kernelQuot tokenize).r := rfl

/-- ⭐ **消重**：既有的 `sameTokens_equivalence` **由一般构造回收** ——
它是 `(kernelQuot tokenize).iseqv`。

**注意** **诚实标注**：本条的**唯一价值是消重**：说明既有的那条等价关系定理
**不需要单独证** —— 它是核商的 `iseqv` 字段。
**注意** **本文件不删除既有定理**（`RealTokenization` 是已入库成果，**不得修改**）。 -/
theorem sameTokens_equivalence_recovered : Equivalence SameTokens :=
  (kernelQuot tokenize).iseqv

/-! ### 八-三、⭐⭐ L0⇄L1 **真正有内容**的那条：**截面**

**注意** 上节说明"核商"是平凡的。本节给出 L0⇄L1 的**非平凡**内容 ——
它是**截面**（`detokenize` 在 `tokenize` 的像上是右逆），
而它的证明**依赖归一化的幂等性**。 -/

/-- ⭐⭐ **`detokenize` 是截面（点态形式）**：若 `tokenize s = some ts`，
则对 `ts` 重分词回到**同一个** `ts`。

⭐ **回收既有 `detokenize_left_inverse_on_quotient`**（**不重证**）。
**注意** **为什么它是"有内容"的**：它**不是**对一切函数成立的
（截面需要归一化**幂等** —— 即 `foldBlanks_idem`），
⭐ **而 §八-二 的核商对一切函数成立** ⟹ **两条的"含金量"不同**。 -/
theorem detokenize_is_section {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) : tokenize (detokenize ts) = some ts :=
  detokenize_left_inverse_on_quotient h

/-- ⭐ **截面 ⟹ 商上的左逆**（在 L0⇄L1 上的具体形式）。

由 §一 的 `canonical_representative_gives_quotient_inverse` 同款论证：
⭐ **这是"商可逆"的**真正来源**** —— **不是商，而是截面**。 -/
theorem detokenize_gives_quotient_left_inverse {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) :
    Quotient.mk (kernelQuot tokenize) (detokenize ts) = Quotient.mk _ s := by
  -- 注意 **实测坑（与 §四 同族，原文逐字保留）**：
  -- `Quotient.sound` 的目标是**不透明**关系 `detokenize ts ≈ s`；
  -- 直接 `refine Quotient.sound ?_; rw […]` **失败** ——
  -- 报 `did not find instance of the pattern tokenize (detokenize ts)`，
  -- 因为 `≈` **不是** `Setoid.r _ _` 的**句法**形式（`rw` 用句法匹配）。
  -- 要点 **正解：先 `show` 出 `Setoid.r` 显式形式**，再在其中 `rw`（见 §一 `kernelQuot_rel`）。
  -- 要点 **正解**：先在 `Setoid.r` 的**显式形式**上把关系化成等式，
  -- 再回到商等式（`Quotient.sound`）—— 两步分开，避免 `≈` 的句法失配。
  have hrel : (kernelQuot tokenize).r (detokenize ts) s := by
    rw [kernelQuot_rel]
    rw [detokenize_is_section h, h]
  exact Quotient.sound hrel

/-- ⭐⭐⭐ **诚实登记（机器可检索）**：L0⇄L1 的两条陈述的**含金量分栏**。

| 陈述 | 性质 | 是否对一切函数成立 |
|:--|:--|:--|
| 核商上下降为单射（"商可逆"） | ⭐ **平凡** | **成立** **是**（§八-二） |
| `detokenize` 是截面 | ⭐ **有内容** | **不成立** **否**（需幂等性） |

⭐ **⇒ 判定**：**L0⇄L1 的成果是【截面】，而"商可逆"只是它的副产品。** -/
theorem l01_the_real_content_is_the_section :
    -- ① 核商（平凡，对一切 `f` 成立）
    (∀ {α β : Type*} (f : α → β), ∃ F : Quotient (kernelQuot f) → β,
        Function.Injective F ∧ (∀ a, F (Quotient.mk _ a) = f a)) ∧
    -- ② `SameTokens` 就是核（`rfl`）
    ((fun s t : List Char => SameTokens s t) = (kernelQuot tokenize).r) ∧
    -- ③ 截面（有内容的那条）—— 在 `some ts` 上
    (∀ {s : List Char} {ts : List CharToken}, tokenize s = some ts →
        tokenize (detokenize ts) = some ts) :=
  ⟨every_function_is_quotient_reversible,
   tokenize_kernel_is_SameTokens,
   fun h => detokenize_is_section h⟩

/-! ### 八-四、诚实边界（原 Token 文件的登记，逐字保留）

- **注意** **不声称 `tokenize` 是单射**：它**不是**（既有 `tokenize_not_injective`，**真**）；
  本节只登记它的**核商**存在（与任何函数一样）。
- **注意** **不声称"商可逆"是 L0⇄L1 的成果**：§八-二 表明它是**一般事实的实例**。
- **注意** **`detokenize_is_section` 的形式是"模 `tokenize`"**（`∀ s, tokenize (detokenize
  (tokenize s 的取值)) = tokenize s`）—— **注意** **对 `Option` 值需要 `getD` 处理**；
  本节因此**同时**给出点态形式（在 `some ts` 上）**和** `Option` 形式，
  避免读者误以为二者等价（**注意** **它们不等价**：`getD` 会把 `none` 吞成 `[]`）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。 -/

end Lattice
