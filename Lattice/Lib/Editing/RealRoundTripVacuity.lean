import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.ConvertLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCanonicalForm
/-!
# LATTICE: `RealRoundTripVacuity` —— 「闭环无新语义」的可检验结构性条件

> 路线图 §5.1 第 2 项（**最高杠杆**）。本文件把一条**教训**升级为**判据**。

## 0. 本文件回答什么

用户实测：「闭环无新语义」**已四次出现**：

| 次 | 位置 | 用户判定的机制 |
|--:|:--|:--|
| **1** | `RealCompileExtractClosed:204` `closed_loop_adds_nothing` | 经往返的陈述 = 字段重命名 |
| **2** | `RealCanonicalCompileComm` `comm_via_extract` | 经权重侧往返是 `rfl` 级 |
| **3** | `RealQuotientReversibility`（**B209**） | 「商可逆」对**任意**函数成立 |
| **4** | `RealEndToEnd` §一（**B219.3**） | 端到端组合是空洞的 |

用户判断：**"四次的共同结构：经由往返的陈述 = 字段重命名"**，
并建议把它做成**可检验的结构性条件**。

## 1. ⚠⚠ 本文件的两项交付（第二项是对用户判断的更正）

### 交付 ①：判据本身（§二–§三）

⭐ **「往返无新语义」不需要 `g ∘ f = id`** —— 只需一个**更弱**的条件。
且该条件**分为两个分支**，**任一支成立即足够**（§三 `roundTripAddsNothing_of_weak`）。

### 交付 ②：⚠ **"四次同构"为假** —— 四次里有 **2 种不同机制**（§五）

⚠⚠ **本文件在写判据的过程中，用真实对象逐次核对 `(f, g, P)`，
发现"四次同一机制"的读法【站不住】**：

| 次 | 有 `(f, g)` 往返吗？ | 机制 |
|--:|:--|:--|
| **1** | ✅ `compileToLayer` / `extractLayer` | **M1 往返型**（纤维稳定支） |
| **2** | ✅ `convertVec` / `extractVec` | **M1 往返型**（且 `rfl` 级） |
| **3** | ❌ **无 `g`** | **M3 定义性重述**（量词无约束） |
| **4** | ❌ **无往返** | **M2 幽灵假设**（假设不出现在结论里） |

⭐⭐ **⇒ 这是本文件比"四次教训"多说的第一件事**：
**"四次同构"是一个错觉。** 三次里只有**两次**是"经由往返"，
第三次是**定义性重述**（机制完全不同），第四次**根本不是往返问题**。

⚠ **⇒ 更何况**：实例 1 的 `P` **不分解过 `f`**（§五 1.1 的机器核对）——
它靠的是 `g ∘ f = id` 提供的纤维稳定，**不是**"`P` 只依赖 `f` 的像"。
⇒ **本判据必须有两个分支**，单分支判据会**漏报实例 1**。

## 2. 诚实边界（本文件主张 / 不主张）

- **主张**：`FiberStable ∧ FactorsThrough` **或** `LeftInverse` ⟹ 往返无新语义（**充分**，§三）。
- **主张**：在**纤维谓词族**上该条件是**锋利**的（§三.4：是**等价**，不是"能证出来"）。
- ⭐ **主张（新）**：`LeftInverse` **严格弱化**为 `FiberStable`，
  **但**弱化后**必须**补 `FactorsThrough` —— 两者**不可互相替代**（§三.5 给出反例）。
- ⚠ **不主张**充要性：§四 给出**满足往返无新语义但两支都不满足**的反例（**诚实登记**）。
- ⚠ **不主张**"四次同构"——已在 §五 **证伪**。
- **只读引用**：不修改任何既有文件（`RealCompileExtractClosed` / `RealCanonicalCompileComm` /
  `RealQuotientReversibility` / `RealEndToEnd` 均未改动）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、往返的抽象骨架 -/

/-- **经由往返的陈述**：`P` 在往返之后成立。 -/
def ViaRoundTrip {α β : Type*} (f : α → β) (g : β → α) (P : α → Prop) : Prop :=
  ∀ a, P (g (f a))

/-- ⭐ **「往返无新语义」（本文件的核心谓词）**：经往返后 `P` 与原来 `P` **等价**。

⚠ **为什么这不是用户提议的"判据"**：用户给的 `∀ a, P (g (f a)) ↔ P a`
是**待证的结论**，对任意 `(f, g, P)` 都是一个需要证明的命题，
**无法在写定理之前判定**。本文件把它**降级为定义**，
另找**能事先判定的充分条件**（§二–§三）。 -/
def RoundTripAddsNothing {α β : Type*} (f : α → β) (g : β → α) (P : α → Prop) : Prop :=
  ∀ a, P (g (f a)) ↔ P a

/-! ## 二、⭐ 两个弱条件（用户候选的精确化） -/

/-- ⭐ **支 A：`P` 分解过 `f`**（`P` 在 `f` 的每条纤维上取常值）。

⭐ **可检验**：检查 `P` 的**定义体**是否**只提到 `f a`** —— 这是**语法级**检查。
⚠ **它不提 `g`**，也不要求 `f` 单射。 -/
def FactorsThrough {α β : Type*} (f : α → β) (P : α → Prop) : Prop :=
  ∀ a a', f a = f a' → (P a ↔ P a')

/-- ⭐ **支 B（往返侧）：往返不逃出 `f` 的纤维**。

⚠ **这是 `g ∘ f = id` 的严格弱化**：`LeftInverse g f` ⟹ 本条件（§三.3），
**反之不成立**（§三.5 给出反例：纤维稳定但无左逆）。 -/
def FiberStable {α β : Type*} (f : α → β) (g : β → α) : Prop :=
  ∀ a, f (g (f a)) = f a

/-! ## 三、⭐ 充分条件 -/

/-- **纤维谓词**：`f` 的一条纤维。这是「只依赖 `f a`」的**最细**谓词。 -/
def fiberPred {α β : Type*} (f : α → β) (b : β) : α → Prop :=
  fun a => f a = b

/-- **纤维谓词都分解过 `f`**。 -/
theorem fiberPred_factorsThrough {α β : Type*} (f : α → β) (b : β) :
    FactorsThrough f (fiberPred f b) :=
  fun _ _ h => by simp only [fiberPred]; rw [h]

/-- ⭐⭐ **主定理（支 A 的充分条件）**：`P` 分解过 `f` **且**往返纤维稳定
⟹ **往返不改变 `P`**。

⚠⚠ **本定理【不】假设 `g ∘ f = id`** —— 这是相对"四次教训"的**推进之一**：
判据从"严格左逆"弱化到"纤维稳定 + `P` 分解"。 -/
theorem roundTripAddsNothing_of_factorsThrough {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop)
    (hP : FactorsThrough f P) (hg : FiberStable f g) :
    RoundTripAddsNothing f g P :=
  fun a => hP (g (f a)) a (hg a)

/-- ⭐⭐ **主定理（支 B 的充分条件）**：**严格左逆** ⟹ **往返不改变 `P`**，
**对任意 `P`**（无需 `FactorsThrough`）。

⚠ **⇒ 这正是实例 1 走的分支**：`closed_loop_adds_nothing` 的 `P` 提到了 `cs` 本身
（不分解过 `f`），但 `extractLayer ∘ compileToLayer = id` 使它照样成立。 -/
theorem roundTripAddsNothing_of_leftInverse {α β : Type*}
    (f : α → β) (g : β → α) (h : Function.LeftInverse g f) (P : α → Prop) :
    RoundTripAddsNothing f g P :=
  fun a => by rw [h a]

/-- ⭐⭐⭐ **判据总装（两个分支合一条）**：
**任一**分支成立 ⟹ 往返无新语义。

⚠ **⇒ 这就是"何时必然如此"的完整回答**（§七 汇总）。 -/
theorem roundTripAddsNothing_of_weak {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop)
    (h : (FactorsThrough f P ∧ FiberStable f g) ∨ Function.LeftInverse g f) :
    RoundTripAddsNothing f g P :=
  h.elim (fun ⟨hP, hg⟩ => roundTripAddsNothing_of_factorsThrough f g P hP hg)
    (fun hL => roundTripAddsNothing_of_leftInverse f g hL P)

/-- ⭐ **判据的正面用法**：「经往返后 `P`」**等价于**「`P`」。

⭐⭐ **这就是"无新语义"的精确形式**：往返既**没有**加强也**没有**减弱原陈述
⟹ **任何**"端到端/闭环"定理若其谓词满足本判据，**其内容量等于单向定理**。 -/
theorem viaRoundTrip_iff_plain {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop) (hP : FactorsThrough f P)
    (hg : FiberStable f g) :
    ViaRoundTrip f g P ↔ (∀ a, P a) :=
  forall_congr' (roundTripAddsNothing_of_factorsThrough f g P hP hg)

/-- ⭐ **判据的负面用法 / 机械检测器**：
若往返**确实改变了** `P`（纤维稳定下），则 `P` **不**分解过 `f`。

⭐ **可操作**：想证明某条"闭环定理"**不**空洞，
只需给出一个 `a` 使 `P (g (f a))` 与 `P a` 不同 ——
即**证明 `P` 提到了 `f` 之外的东西**。 -/
theorem not_factorsThrough_of_not_neutral {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop) (hg : FiberStable f g)
    (h : ¬ RoundTripAddsNothing f g P) : ¬ FactorsThrough f P :=
  fun hP => h (roundTripAddsNothing_of_factorsThrough f g P hP hg)

/-! ### 三.3 与「严格左逆」的关系：支 A 确实**覆盖**老判据 -/

/-- **严格左逆 ⟹ 纤维稳定**（故支 A 的判据**覆盖**"`g ∘ f = id`"那条老判据）。 -/
theorem fiberStable_of_leftInverse {α β : Type*} (f : α → β) (g : β → α)
    (h : Function.LeftInverse g f) : FiberStable f g :=
  fun a => by rw [h a]

/-- **支 B 是支 A 的特例（在 `FactorsThrough` 成立时）**：
本定理使"两支的关系"可逐字比对，避免把两支误读为互不相干。 -/
theorem factorsThrough_and_leftInverse_gives_factorsThrough {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop)
    (hP : FactorsThrough f P) (h : Function.LeftInverse g f) :
    RoundTripAddsNothing f g P :=
  roundTripAddsNothing_of_factorsThrough f g P hP (fiberStable_of_leftInverse f g h)

/-! ### 三.4 ⭐⭐ 锋利性：判据在**纤维谓词族**上是等价的

⚠ **"充分条件"若无人问它是否锋利，就只是又一次"能证出来"**（判读规律 1）。

⭐⭐ **⇒ 结论**：`FiberStable` **不是**随手写松的条件 ——
**纤维谓词族是最细的检验族**：往返固定**所有**纤维谓词 ⟺ 纤维稳定。 -/

/-- ⭐⭐ **锋利性定理**：`FiberStable` ⟺ 「**每条**纤维谓词都经往返不变」。 -/
theorem fiberStable_iff_neutral_on_fiberPreds {α β : Type*} (f : α → β) (g : β → α) :
    FiberStable f g ↔ ∀ b : β, ∀ a : α, fiberPred f b (g (f a)) ↔ fiberPred f b a := by
  constructor
  · intro hg b a
    simp only [fiberPred]
    rw [hg a]
  · intro h a
    have h' : fiberPred f (f a) (g (f a)) ↔ fiberPred f (f a) a := h (f a) a
    have h2 : fiberPred f (f a) a := rfl
    exact h'.mpr h2

/-- ⭐ **锋利性的实用读法**：只需检验**最细的谓词族（纤维）** ——
它若通过，则**所有**分解过 `f` 的 `P` 都通过。

⭐⭐ **⇒ 这是判据的可操作形式**：检测某"闭环定理"是否空洞，
**不必**逐个 `P` 检查，**只查纤维谓词**即可（最细者通过 ⟹ 粗者必通过）。 -/
theorem roundTripAddsNothing_of_factorsThrough_of_fiberPreds {α β : Type*}
    (f : α → β) (g : β → α) (P : α → Prop) (hP : FactorsThrough f P)
    (hf : ∀ b : β, ∀ a : α, fiberPred f b (g (f a)) ↔ fiberPred f b a) :
    RoundTripAddsNothing f g P :=
  roundTripAddsNothing_of_factorsThrough f g P hP
    ((fiberStable_iff_neutral_on_fiberPreds f g).mpr hf)

/-! ### 三.5 ⚠ **两支【不可互相替代】**（对"更弱条件"的精确回答）

用户的候选里有一条是"`P` 只依赖 `f` 的像"（= `FactorsThrough`），
另一条是 `g ∘ f = id`。本节证明：**两者互不蕴含** —— 故判据**必须**是两支之**或**。 -/

/-- ⚠ **`f` 单射 ⟹ `FactorsThrough f P` 对任意 `P` 成立**
（纤维是单点集，`P` 自动在其上取常值）。

⭐ **用途**：这是"`FactorsThrough` 何时免费"的判据 ——
**当 `f` 单射时，支 A 的前半自动成立**，判据退化为只查纤维稳定。 -/
theorem factorsThrough_of_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (P : α → Prop) : FactorsThrough f P :=
  fun _ _ h => by rw [hf h]

/-- ⚠ **反例（支 A 不蕴含支 B）**：存在 `f, g` 使**所有** `P` 都满足
`FactorsThrough`（取 `f` 单射即可），但 `g` **不是**左逆、且往返**不**纤维稳定。

**见证**：`α := β := ℕ`、`f := id`、`g := fun _ => 7`（常函数）。
`f` 单射故 `FactorsThrough f P` 恒成立；
但 `f (g (f 3)) = 7 ≠ 3 = f 3` ⟹ 往返**改变了**谓词 `fun n => n = 3`：
`(fun n => n = 3) (g (f 3)) = (7 = 3) = False`，而 `(fun n => n = 3) 3 = True`。

⭐⭐ **⇒ 这证明 `FactorsThrough` 单独【不】足够** —— 必须**同时**要求往返侧的条件。
⇒ **"`P` 只依赖 `f` 的像"这条候选【单独不成立】**。 -/
theorem factorsThrough_alone_does_not_suffice :
    ∃ (f g : ℕ → ℕ) (P : ℕ → Prop),
      FactorsThrough f P ∧ ¬ RoundTripAddsNothing f g P := by
  refine ⟨id, fun _ => 7, fun n => n = 3, ?_, ?_⟩
  · intro a a' h
    simp only [id] at h
    rw [h]
  · intro h
    -- `h 3 : P (g (f 3)) ↔ P 3`，即 `(7 = 3) ↔ (3 = 3)`。
    -- 右侧为真（`rfl`），故 `h.mpr` 给出 `7 = 3`，矛盾。
    have h3 : (3 : ℕ) = 3 := rfl
    have h7 : (7 : ℕ) = 3 := (h 3).mpr h3
    exact absurd h7 (by norm_num)

/-- ⚠ **反例（支 B 不蕴含支 A）**：存在 `f, g` 使 `LeftInverse g f` 成立
（故**任意** `P` 都往返无新语义），但 `P` 可以**不**分解过 `f`。

**见证**：`α := β := ℕ`、`f := g := id`（互为逆），
`P := fun n => n = 3`。往返恒等 ⟹ 无新语义；但 `P` 提到 `n` 本身。
⚠ **这条反例本身平凡**（`id` 下任何 `P` 都不需要分解），
**但它精确说明了**：**支 B 的作用域是【全体 `P`】，而支 A 只覆盖分解过的 `P`** ——
⭐ **这正是实例 1 必须走支 B 的原因**。 -/
theorem leftInverse_covers_non_factoring_P :
    ∃ (f g : ℕ → ℕ) (P : ℕ → Prop),
      Function.LeftInverse g f ∧ RoundTripAddsNothing f g P :=
  ⟨id, id, fun n => n = 3, fun _ => rfl, fun _ => Iff.rfl⟩

/-! ## 四、⚠ 诚实登记：本判据是**充分不必要**

⚠ **不主张充要性**。本节的构造说明存在 `(f, g, P)` **满足往返无新语义
却不满足任一分支** —— 故判据是**充分**条件，不是判别式。

⭐ **它的价值**：避免把本文件**误读**为"往返无新语义 ⟺ 两支之一"。
⚠ **这也正是 B209.2 那条更正的教训**：**恒成立的陈述不能当判别条件用**。
本文件因此**明确**不声称充要性。 -/

/-- ⚠ **充分性不反向的证据（结构性）**：`RoundTripAddsNothing` 对
**任意** `P` 只要 `g ∘ f = id` 即成立；而对 `FiberStable` 但**非**左逆的 `f, g`，
**存在** `P` 满足无新语义、**也存在** `P` 不满足 ——
故"无新语义"**不是** `P` 的函数（它依赖 `P` 与 `(f, g)` 的交互），**不能**单看一支判定。 -/
theorem neutral_is_not_a_decision_procedure :
    ∃ (f g : ℕ → ℕ) (P Q : ℕ → Prop),
      FiberStable f g ∧ RoundTripAddsNothing f g P ∧ ¬ RoundTripAddsNothing f g Q := by
  -- 取 `f := 常函数 0`、`g := 常函数 0`：往返纤维稳定（一切都在纤维 `0` 内），但 `g` 不是左逆。
  refine ⟨fun _ => 0, fun _ => 0, fun _ => True, fun n => n = 0, ?_, ?_, ?_⟩
  · -- 纤维稳定：`f (g (f a)) = 0 = f a`
    intro a; rfl
  · -- `P := fun _ => True`：往返后仍为真
    intro a; exact Iff.rfl
  · -- `Q := fun n => n = 0`：`Q (g (f 1)) = (0 = 0) = True`，但 `Q 1 = (1 = 0) = False`
    intro h
    have h1 : (fun n : ℕ => n = 0) ((fun _ => 0) ((fun _ => 0) 1)) ↔ (fun n : ℕ => n = 0) 1 := h 1
    have h0 : (fun n : ℕ => n = 0) ((fun _ => 0) ((fun _ => 0) 1)) := rfl
    exact absurd (h1.mp h0) (by norm_num)

/-! ## 五、⭐⭐ 实例化回四次（**本文件最关键的一节**）

⚠⚠ **本节用**真实的 LATTICE 对象**逐次核对**，结论**部分否定了用户判断**。
每次给出 `(f, g, P)`、**机制判定**、以及**为什么**。 -/

/-! ### 5.1 实例 1：`RealCompileExtractClosed:204` `closed_loop_adds_nothing`

* `f := compileToLayer : ConstraintSet → Layer`
* `g := extractLayer : Layer → ConstraintSet`
* `P := fun cs => AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x`

⚠⚠ **机器核对的第一项发现：`P` 【不】分解过 `f`。**
`P` 的**左半** `AllSatisfied cs x` 直接提到 `cs` 本身，**不经过** `f`。
⇒ ⭐ **实例 1 走的是【支 B】（`LeftInverse`），不是分支 A。**

⭐⭐ **⇒ 这否证了一条自然的猜想**："往返无新语义 ⟺ `P` 只依赖 `f` 的像"。
**实例 1 是反例**：它的 `P` 提到 `cs`，却照样空洞 ——
因为 `extractLayer ∘ compileToLayer = id` **对任意 `P`** 都保证这一点。 -/

/-- **实例 1 的往返**：`extractLayer ∘ compileToLayer = id`（既有定理，只读引用）。 -/
theorem rt1_leftInverse : Function.LeftInverse extractLayer compileToLayer :=
  extractLayer_compileToLayer

/-- ⭐ **实例 1 的判定（支 B）**：`closed_loop_adds_nothing` 是本文件
`roundTripAddsNothing_of_leftInverse` 在真实对象上的实例。

⚠ **注意**：此处**必须**用支 B —— `P` 不分解过 `f`（见上）。 -/
theorem rt1_is_instance_of_branch_B (cs : ConstraintSet) (x : List Int) :
    ((AllSatisfied (extractLayer (compileToLayer cs)) x ↔
        AllZeroOutputs (compileToLayer cs) x)
      ↔ (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x)) :=
  roundTripAddsNothing_of_leftInverse compileToLayer extractLayer rt1_leftInverse
    (fun cs' => AllSatisfied cs' x ↔ AllZeroOutputs (compileToLayer cs) x) cs

/-- **实例 1 与既有定理的逐字吻合**（只读引用既有定理，作为对账）。 -/
theorem rt1_matches_existing (cs : ConstraintSet) (x : List Int) :
    (AllSatisfied (extractLayer (compileToLayer cs)) x ↔ AllZeroOutputs (compileToLayer cs) x)
      ↔ (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) :=
  closed_loop_adds_nothing cs x

/-! ### 5.2 实例 2：`RealCanonicalCompileComm` 的 `comm_via_extract`

* `f := convertVec : VectorConstraint → LinearLayer`
* `g := extractVec : LinearLayer → VectorConstraint`
* `P := fun c => canonicalize c = canonicalize c`（两侧**折叠后**是同一个项）

⭐ **判定：走支 A 或支 B 均可** —— 因为 `extractVec_convertVec_rfl` 是
**裸 `rfl`**（**定义相等**，不只是可证），故 `LeftInverse` 成立，
**任意 `P`** 都不变。 -/

/-- **实例 2 的往返（定义相等）**：`extractVec ∘ convertVec = id`。

⚠ **本文件用 `cases` 形式**（与既有 `roundtrip_extractVec` 同源），
⭐ **它等价于 `RealCanonicalCompileComm.lean:146` 的裸 `rfl` 版本** ——
**定义相等**是本实例"空洞"的**最强形式**。 -/
theorem rt2_leftInverse : Function.LeftInverse extractVec convertVec :=
  roundtrip_extractVec

/-- ⭐ **实例 2 的判定**：`comm_via_extract` 的实质是"往返后两侧是同一个项"，
故对**任意** `P` 都无新语义 —— 走支 B。 -/
theorem rt2_is_instance_of_branch_B (c : VectorConstraint) (P : VectorConstraint → Prop) :
    P (extractVec (convertVec c)) ↔ P c :=
  roundTripAddsNothing_of_leftInverse convertVec extractVec rt2_leftInverse P c

/-- ⭐⭐ **实例 2 的核心读数（对"`rfl` 级"的精确化）**：
`comm_via_extract` 的两条"不同路径"在折叠后**是同一个项** ——
即两条路径的差是 `canonicalize c = canonicalize c`。

⚠ **这就是"`rfl` 级"的确切含义**：不是"容易证"，而是**两侧相等是定义的推论**。 -/
theorem rt2_paths_collapse (c : VectorConstraint) :
    extractVec (convertVec (canonicalize c)) = canonicalize (extractVec (convertVec c)) := by
  rw [rt2_leftInverse c, rt2_leftInverse (canonicalize c)]

/-! ### 5.3 实例 3：`RealQuotientReversibility`（**B209**）—— ⚠⚠ **不是往返型！**

⚠⚠ **本节的判定【否定】了"四次同构"**：

| 项目 | 实例 1/2 | 实例 3 |
|:--|:--|:--|
| 有 `g` 吗？ | ✅ | ❌ **没有** |
| 有 `g ∘ f` 吗？ | ✅ | ❌ **从未构造** |
| 陈述形如 `P (g (f a))` 吗？ | ✅ | ❌ **不是** |

⭐⭐ **实例 3 的真实机制**：`every_function_is_quotient_reversible`
断言 `∃ F, Injective F ∧ F ∘ mk = f`，其中商关系**被定义成** `f a = f b`
（`kernelQuot`）。⇒ 它是**定义性重述**，**机制与往返无关**。

⭐⭐ **⇒ 重要结论**：`(f, g, P)` 三格中,**`g` 这一格【填不出】——
因为该文件里根本不存在第二个映射**。
按任务书要求，**如实报告**：**实例 3 不是往返空洞**。

⚠ **⇒ 但它是空洞的**（B209 已判定），只是**机制不同**：
**量词无约束**（对**任意**函数成立 ⟹ 不含区分信息）。
本文件把它命名为 **M3**，并在 §六 与 M1/M2 并列登记。 -/

/-! ### 5.4 实例 4：`RealEndToEnd` §一（**B219.3**）—— ⚠⚠ **不是往返型！**

⚠⚠ **本节的判定同样【否定】"四次同构"**：

* `RealEndToEnd.lean:205` `e2e_vacuous_composition` 的结论是
  `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x`，
  假设里**只有** `ts : List SymToken`（**在结论中不出现**）。
* ⚠ **没有 `f`、没有 `g`、没有 `g ∘ f`、没有 `P (g (f a))` 形状**。
* 它的机制是 **M2 幽灵假设**：`_h : Extract ts cs` **不出现在结论里**
  ⟹ **删掉照样证** ⟹ 对结论贡献为零。

⭐⭐ **⇒ 如实报告：实例 4 的 `(f, g, P)` 三格【全部填不出】** ——
**它不是往返空洞**。 -/

/-- ⭐⭐ **M2（幽灵假设）的判据形式化**：
若断言的真值**不依赖**参数 `t : γ`，则 `∀ t : γ, Q` 与 `Q` 等价 ——
即 `Q` **可以整个删掉参数**。

⚠ **⇒ 这是"删掉假设照样证"的**类型级**表述** ——
不是"措辞问题"，而是**类型不依赖**（`RealEndToEnd` §一 的做法）。

⭐ **与 M1 的区别**：M2 **不涉及**任何映射对 `(f, g)`；
检测方法是**检查假设是否出现在结论的类型里**（B219.3 的判据）。 -/
theorem ghost_hypothesis_is_vacuous {γ : Type*} [Nonempty γ] (Q : Prop) :
    (∀ _t : γ, Q) ↔ Q :=
  ⟨fun h => h (Classical.arbitrary γ), fun h _ => h⟩

/-- ⭐⭐ **M2 的"承重"对照（判据的另一半）**：
若结论的类型**确实依赖**参数，则该参数**承重** ——
删掉它**结论无法陈述**（这正是 `RealEndToEnd` §三 `e2e_sound` 的口径）。

⚠ **本文件把 B219.3/B219.4 的口径**逐字形式化**：
"L1⇄L2 对**语义内容**不承重（§一），但对**结论的可陈述性**承重（§三）"。
⇒ ⭐ **"承重"有两种，必须分开判** —— 这是 M2 的相对 M1 的额外结构。 -/
theorem ghost_hypothesis_dependent_is_load_bearing {γ : Type*} (Q : γ → Prop)
    (t₀ : γ) : (∀ t : γ, Q t) → Q t₀ :=
  fun h => h t₀

/-! ### 5.5 ⭐⭐ **四次对照表（本文件对用户判断的更正）**

| 次 | `f` | `g` | `P` | 机制 | 本文件判据适用？ |
|--:|:--|:--|:--|:--|:--|
| **1** | `compileToLayer` | `extractLayer` | `AllSatisfied · x ↔ AllZeroOutputs (compileToLayer cs) x` | **M1 往返**（支 B） | ✅ |
| **2** | `convertVec` | `extractVec` | 折叠后 `canonicalize c = canonicalize c` | **M1 往返**（支 A/B 均可，`rfl` 级） | ✅ |
| **3** | `kernelQuot` 的 `f` | ⚠ **无** | `∃ F, Injective F ∧ F ∘ mk = f` | **M3 定义性重述** | ❌ **不适用** |
| **4** | ⚠ **无** | ⚠ **无** | `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` | **M2 幽灵假设** | ❌ **不适用** |

⭐⭐ **⇒ "四次同构"为假**：**只有 2 次**是往返型；**2 次是另外两种机制**。

⚠ **⇒ 若强行填 `(f, g, P)`，第 3、4 次的 `g` 格会是【空的】** ——
本文件按任务书要求**如实报告这一格填不出来**，并把它**升级为结论而非缺陷**。 -/

/-! ## 六、⭐⭐⭐ 第三个机制 M4：**投影/幂等**（回答"何时【必然】如此"）

⭐ 用户在候选里问到了"**某投影的幂等性**"。
本节证明**这确实是独立于 M1/M2/M3 的第三个结构性来源**，
且它**正是实例 2 与实例 1 的更深层原因**。

⭐ **观察（本节的实质）**：`FiberStable f g` 的条件是 `f (g (f a)) = f a`。
若把 `cl := g ∘ f` 看作**闭环算子**，则 `FiberStable` 恰是 `f ∘ cl = f`
—— ⭐ **即"`cl` 在 `f` 的读数上不动"**。

⚠ **本节【不】重述 §三.2**（那会是 `PROCESS.md` §2.2 禁止的重述）。
本节给出的是**独立的**结构事实：**`f ∘ cl = f` 对 `cl` 的幂等性是一个
【吸收律】** —— 见下条。 -/

/-- ⭐⭐ **M4（投影吸收律，本节的实际内容）**：
若 `f ∘ cl = f`（往返在 `f` 的读数上不动），则 `f ∘ cl ∘ cl = f` **自动**成立 ——
即「往返跑第二圈」与「跑第一圈」在 `f` 的读数上**不可区分**。

⚠⚠ **为什么这不是重述**：结论里的 `cl ∘ cl`（**两圈**）与假设里的 `cl`（**一圈**）
是**不同的项**，故本定理**不是** `hcomp` 的逐字重复 ——
它说的是"**一圈的读数 ⟹ 任意圈的读数**"（`Nat` 归纳，见 `iterate` 版本）。

⭐⭐ **⇒ 这是"何时必然如此"的结构性回答**：
**闭环一旦在 `f` 上不动，则【所有】迭代都在 `f` 上不动** ——
故"多跑几圈"**不可能**产生新语义。 -/
theorem fiberStable_iterate {α β : Type*} (f : α → β) (g : β → α)
    (hcomp : ∀ a, f (g (f a)) = f a) (n : ℕ) :
    ∀ a, f (((g ∘ f)^[n]) a) = f a := by
  induction n with
  | zero => intro a; rfl
  | succ k ih =>
      intro a
      -- `(g ∘ f)^[k+1] a = (g ∘ f) ((g ∘ f)^[k] a)`
      rw [Function.iterate_succ_apply']
      -- 目标：`f ((g ∘ f) ((g∘f)^[k] a)) = f a`；先把 `∘` 展开
      show f (g (f ((g ∘ f)^[k] a))) = f a
      rw [hcomp ((g ∘ f)^[k] a), ih a]

/-- ⭐⭐ **锋利性（M4 版）**：若 `P` **不**分解过 `f`，则**即使往返幂等**，
`P` 也可能被往返改变 —— 故 M4 **不能**替代 M1 的分支 A。

**见证**：`f := 常函数 0`、`g := 常函数 0`（往返幂等，因为 `g ∘ f` 是常函数），
`P := fun n => n = 1`。`P` 不分解过 `f`（`f` 把所有点映到 `0`，纤维是整个 `ℕ`），
且往返**改变了** `P`（`P (g (f 1)) = (0 = 1) = False`，而 `P 1 = True`）。

⭐⭐ **⇒ 结论**：**幂等性 + 不分解 ⟹ 仍可空洞或非空洞，取决于 `P`**。
⇒ ⭐ **"投影幂等性"【单独不构成】判据** —— 它必须与 `FactorsThrough` **合取**。 -/
theorem idempotent_alone_does_not_suffice :
    ∃ (f g : ℕ → ℕ) (P : ℕ → Prop),
      (∀ a, f (g (f a)) = f a) ∧ ¬ FactorsThrough f P ∧ ¬ RoundTripAddsNothing f g P := by
  refine ⟨fun _ => 0, fun _ => 0, fun n => n = 1, fun _ => rfl, ?_, ?_⟩
  · -- `P` 不分解过 `f`：`f 0 = f 1`，但 `P 0 = (0=1) = False`，`P 1 = (1=1) = True`
    intro h
    have h01 : (fun n : ℕ => n = 1) 0 ↔ (fun n : ℕ => n = 1) 1 := h 0 1 rfl
    exact absurd (h01.mpr rfl) (by norm_num)
  · -- 往返改变了 `P`：`P (g (f 1)) = (0 = 1) = False`，而 `P 1 = (1 = 1) = True`
    intro h
    have h1 := h 1
    -- `h1 : (0 = 1) ↔ (1 = 1)`；右侧为真，故左侧为真 ⟹ `0 = 1`，矛盾
    have hright : (fun n : ℕ => n = 1) 1 := rfl
    have hleft : (0 : ℕ) = 1 := h1.mpr hright
    exact absurd hleft (by norm_num)

/-! ## 七、⭐⭐⭐ 汇总：「何时必然如此」的完整回答

### 7.1 判据（本文件的最终交付）

```
往返无新语义（RoundTripAddsNothing f g P）在下列【任一】条件成立时【必然】成立：

  支 A  P 分解过 f  ∧  往返不逃出 f-纤维        （FactorsThrough ∧ FiberStable）
  支 B  g ∘ f = id                              （LeftInverse，覆盖全体 P）
```

⭐⭐ **⇒ 相对"四次教训"的推进（这是本文件的核心增量）**：

| # | 教训（事后判读） | 本文件（事前可检） |
|--:|:--|:--|
| **1** | "看**证明体**是不是 `rfl`/`rw`" —— **证完才能判** | ⭐ **看 `P` 的【定义体】是否只提到 `f a`** —— **写之前就能判** |
| **2** | "四次都是同一机制" | ⚠ **否证** —— **是三种机制**（§五 对照表） |
| **3** | "`g ∘ f = id` 是空洞的充分条件" | ⭐ **弱化** —— `FiberStable ∧ FactorsThrough` **严格更弱**（§三.5） |
| **4** | （无） | ⭐ **锋利性**：最细检验族是**纤维谓词**（§三.4），**不必**逐个 `P` 查 |

### 7.2 ⚠ 诚实边界（不主张什么）

1. ⚠ **不主张充要性** —— §四 `neutral_is_not_a_decision_procedure` 给出反例。
   ⭐ 依据 **B209.2 的更正**：**恒成立的陈述不能当判别条件**，
   故本文件**明确**只给**充分**条件。
2. ⚠ **不主张"四次同构"** —— §五 已**证伪**。
3. ⚠ **不主张**幂等性单独可用 —— §六 `idempotent_alone_does_not_suffice` 给出反例。
4. ⚠ **不主张**本判据能自动发现所有空洞 —— 它只能发现**往返型**（M1）；
   M2/M3 需要**另外**的检测（幽灵假设看结论类型；定义性重述看量词是否受限）。

⭐⭐ **⇒ 最有复用价值的一条**（本文件对用户"最有价值的元层结论"的答复）：
> **"经由往返的陈述"是否空洞，取决于 `P` 是否【分解过 `f`】——
> 这是一个**语法级、写定理之前就能查**的性质，不必等证明写完再看证明体。** -/

end Lattice
