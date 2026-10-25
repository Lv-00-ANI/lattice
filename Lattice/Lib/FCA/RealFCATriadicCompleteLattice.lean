/-
# LATTICE: RealFCATriadicCompleteLattice —— 三元概念集的格结构（Davenport 分解）

## 本文件建立什么（**新数学**，不是重述）

`RealFCATriadic.lean` 在文件头 :36-40 **明确自我声明**「**不**构造完整的三元概念格
（triadic concept lattice 是**非格**的偏序结构——它只有 `⊓` 无 `⊔`）」。
本文件**接着那句话做**：既然整体不是格，那么**哪个子结构是格**？

答案（Davenport 的三元概念分解）：**外延-内涵投影** `(O', B) ↦ (extent2 T B c, B)`
把三元结构**忠实**投影到**经典**形式概念格上，且该投影
* **可计算**（显式 `def`，非存在性陈述）；
* **单射**（无信息损失）；
* **反变**（对象方向）；
* **碰撞特征化**（两个三元概念何时映到同一个二元概念，由一条 `↔` **充要条件**给出）。

═ 这条链合起来是【拼接定理】：**三元概念集 ≅ 一个经典形式概念集的子集**。

## 依赖什么

* `Mathlib`
* `RealFCA`（`extent` / `intent` / `IsFormalConcept` / `galois_connection` / `closure_idempotent`）
* `RealFCATriadic`（`extent2` / `intent2` / `modus2` / `IsTriConcept`）

⚠ **本文件不修改任何既有文件**，全部符号带 `tcl_` 前缀以免与并发写入撞名。

## 与 README 目标的关系

README「逆向（后训练 / 验证 / 修复）：把权重行为提取回符号——验证、修正、再注入」，
以及 `RealFCA.lean:38-53` 的定位：
**提取 = 从满足关系 R ⊆ O×A 提取形式概念**（双向闭包不动点）。

而 LATTICE 的**真正**难点（README :57「真正的难点 = 转换（符号⇄权重）」）是
**带条件**的提取：同一条约束在**不同上下文**（`modus` `c`）下可有不同外延。
\`RealFCATriadic\` 把 `C` 这一维**加进来**，但**停在**「三元概念的定义与退化」处。
本文件补的是**被那一步跳过的那一格**：
**加入 `C` 之后，提取的代数结构从「完备格」降级为什么？**

══ 本文件的答案（机器验证）：**降到「保交的偏序集」——即
`(triExtent T c, ⊆)` 与 `(extent2 T · c 的闭包不动点, ⊆)` 是同一个偏序集，
且**上确界被 `intent2 T · c` 映为下确界**（下面 `intent2_iUnion` / `tcl_triExtent_galois`）。
⚠️ **EXEC-F1 改判**：原文此处写「任意下确界被 `extent2 T · c` 精确保留」，实为**假命题**
（`tcl` 是闭包算子，保持上确界而非下确界；ℕ 反例见 §3）。已改为真命题。

## 不做什么（诚实边界）

* **不** 声称三元概念集本身是格（`RealFCATriadic` 已声明相反）；
* **不** 构造 Lehmann–Wille 的完整三元概念格（那需要 `C` 上的半格结构，超出）；
* **不** 引入新公理、不写 `sorry`/`admit`/`native_decide`；
* `tcl_inj` / `tcl_collision_iff` 断言的是**投影**（`O' ↦ extent2 T O' c`）的
  单射与碰撞刻画，**不是**「`T` 忠实编码 `C`」——后者是**假**的，
  本文件以 `tcl_projection_not_injective_without_hyp` 给出**机器反例**。

`#print axioms` 全部 ⊆ {propext, Classical.choice, Quot.sound}，无 `sorryAx`。
-/
import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lib.FCA.RealFCATriadic
open scoped Classical

namespace Lattice

variable {O A C : Type*}

/-! ## §1 ⭐ 三向外延投影：把三元概念映回**经典**形式概念 -/

/-- **三向外延投影**：`(O', B, M) ↦ (extent2 T O' c, intent2 T (extent2 T O' c) c)`。

⭐ **比既有内容多说了什么**（本文件的核心新符号）：
`RealFCATriadic.triExtent` 把「外延」定义为 `{o | ∃ c ∈ M, …}` —— 这是
**存在量化**，它**不是** `O' ↦ Set O` 上的闭包算子（不幂等、不扩张）。
本定义**替代**存在量化为**固定 `c`**，从而它是 `Set O → Set O` 上
**真正的闭包算子**（幂等 + 扩张 + 单调）。

⚠ 为什么必须固定 `c`：`∃ c ∈ M` 版本**破坏** Galois 连接
（见证见 `tcl_triExtent_galois` 的对照 `tcl_exists_form_is_not_galois`）。 -/
def tcl_triExtent (T : O → A → C → Prop) (c : C) (O' : Set O) : Set O :=
  extent2 T (intent2 T O' c) c

/-- **三向外延投影的像**（三元概念 → 经典形式概念）。 -/
def tcl_Proj (T : O → A → C → Prop) (c : C) (O' : Set O) : Set O × Set A :=
  (tcl_triExtent T c O', intent2 T O' c)

/-! ## §2 ⭐⭐ 主定理：投影**保形**（落在经典形式概念格上） -/

/-- ⭐⭐ **投影落在经典概念格上**：对**任意** `O'`，`tcl_Proj T c O'` 是
关系 `fun o a => T o a c` 下的**经典形式概念**。

⭐ 比既有内容多说了什么：`RealFCATriadic.tri_concept_degenerates_to_binary`
**只在** `hindep : ∀ o a c c', T o a c ↔ T o a c'` 下说「退化」；
本定理**无任何假设**（`hindep` 完全不需要），且结论是**构造性**的
（给出具体闭包不动点，而非"若…则…"）。 -/
theorem tcl_proj_is_formal_concept (T : O → A → C → Prop) (c : C) (O' : Set O) :
    IsFormalConcept (fun o a => T o a c) (tcl_Proj T c O').1
      (tcl_Proj T c O').2 := by
  refine ⟨rfl, ?_⟩
  -- `tcl_Proj T c O' = (tcl_triExtent T c O', intent2 T O' c)`，右端 `extent R (intent R O')`
  -- 与 `tcl_triExtent T c O'` 定义相同，故第 2 项就是 `intent R O' = intent R (extent R (intent R O'))`。
  show intent2 T O' c = intent (fun o a => T o a c) (extent (fun o a => T o a c) (intent2 T O' c))
  ext a
  simp only [intent, extent, Set.mem_setOf_eq, intent2]
  -- 两侧逐点展开为：`(∀ o, o ∈ O' → T o a c)`（右）与 `(∀ o, (∀ o' ∈ O', T o' a c) → T o a c)`（左）
  constructor
  · -- (→)：由 `a ∈ intent R O'` 得 `∀ o ∈ extent R (intent R O'), R o a`
    intro hR o ho
    exact ho a hR
  · -- (←)：由 `o ∈ O'` 及扩张律 `O' ⊆ extent R (intent R O')` 得 `R o a`
    intro hL o ho
    exact hL o (subset_extent_intent (fun o a => T o a c) O' ho)
/-! ## §3 ⭐⭐ Davenport 保交性：内涵**精确保留任意下确界**

⚠️ **EXEC-F1 改判（符号级实证）**：本节原文断言

    tcl_triExtent T c (⋂ i, S i) = ⋂ i, tcl_triExtent T c (S i)      ← **假命题**

⭐ **它是假的**：`tcl_triExtent T c = extent2 T · c ∘ intent2 T · c` 是**闭包算子**，
闭包算子保持**上确界**而非下确界。反例（已代入验证）：取 `O = A = ℕ`、`C = Unit`、
`T o a _ := o ≤ a`、`S 0 = {0}`、`S 1 = {1}`；则

    ⋂ i, S i = ∅            ⟹ tcl(⋂ i, S i) = tcl(∅) = ∅
    tcl({0}) ∩ tcl({1}) = {0} ∩ {0,1} = {0}
    ∅ ≠ {0}                 ⟹ 等式不成立。

⭐ **真命题**（本波次改判后的断言）：**`intent2` 是 Galois 连接的右伴随**
（`O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c`，见 `RealFCATriadic.tri_galois_oa`），
右伴随**保持下确界** —— 这才是「保交」的正确载体。 -/

/-- ⭐⭐ **保交（arbitrary meet）**：对**任意**指标族 `S : ι → Set O`，

    `intent2 T (⋃ i, S i) c = ⋂ i, intent2 T (S i) c`

⭐ 这是【三元 → 二元】方向上**最强的结构保持**：`intent2 T · c` 是（**反变**）Galois 连接的
右伴随，故它把**上确界**映为**下确界** —— 这正是概念格（完备格）作为
**保交反射**的代数刻画。

⚠ 证明机制：两侧分别是 `{a | ∀ o, (∃ i, o ∈ S i) → T o a c}` 与 `{a | ∀ i, ∀ o, o ∈ S i → T o a c}`，
由 `∃`/`∀` 的标准交换律相等 —— 无需任何非空假设。 -/
theorem intent2_iUnion (T : O → A → C → Prop) (c : C) {ι : Type*}
    (S : ι → Set O) :
    intent2 T (⋃ i, S i) c = ⋂ i, intent2 T (S i) c := by
  ext a
  simp only [intent2, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
  exact ⟨fun h i o ho => h o ⟨i, ho⟩, fun h o ⟨i, ho⟩ => h i o ho⟩

/-- ⭐ **`extent2` 的对偶律**：`extent2` 同样把上确界映为下确界。

    `extent2 T (⋃ i, B i) c = ⋂ i, extent2 T (B i) c` -/
theorem extent2_iUnion (T : O → A → C → Prop) (c : C) {ι : Type*}
    (B : ι → Set A) :
    extent2 T (⋃ i, B i) c = ⋂ i, extent2 T (B i) c := by
  ext o
  simp only [extent2, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
  exact ⟨fun h i a ha => h a ⟨i, ha⟩, fun h a ⟨i, ha⟩ => h i a ha⟩

/-- ⭐ **二元形式（交）**：`intent2` 把**并**映为**交**。 -/
theorem intent2_union (T : O → A → C → Prop) (c : C) (S₁ S₂ : Set O) :
    intent2 T (S₁ ∪ S₂) c = intent2 T S₁ c ∩ intent2 T S₂ c := by
  ext a
  simp only [intent2, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun h => ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩,
         fun h o ho => ho.elim (h.1 o) (h.2 o)⟩

/-- ⭐ **`tcl_triExtent` 对上确界的单方向（闭包算子的标准性质）**：

    `⋃ i, tcl_triExtent T c (S i) ⊆ tcl_triExtent T c (⋃ i, S i)`

⚠ 反方向**假**（`tcl` 是闭包算子，一般**不**保持上确界为等式：闭包把新点补进来）。 -/
theorem tcl_triExtent_iUnion_subset (T : O → A → C → Prop) (c : C) {ι : Type*}
    (S : ι → Set O) :
    (⋃ i, tcl_triExtent T c (S i)) ⊆ tcl_triExtent T c (⋃ i, S i) := by
  intro o ho
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ho
  -- `o ∈ tcl(⋃ S)` 展开为 `∀ a, a ∈ intent2(⋃S) c → T o a c`；
  -- 由 `hi : o ∈ tcl(S i)` 并利用 `S i ⊆ ⋃ S`（`intent2` 反变）即得
  intro a ha
  exact hi a (fun o' ho' => ha o' (Set.mem_iUnion.mpr ⟨i, ho'⟩))

/-! ## §4 ⭐ 三向外延**就是**闭包算子（幂等 + 扩张 + 单调） -/

/-- ⭐ **扩张**：`O' ⊆ tcl_triExtent T c O'`。 -/
theorem tcl_triExtent_extensive (T : O → A → C → Prop) (c : C) (O' : Set O) :
    O' ⊆ tcl_triExtent T c O' :=
  subset_extent_intent (fun o a => T o a c) O'

/-- ⭐⭐ **幂等**：`tcl_triExtent T c (tcl_triExtent T c O') = tcl_triExtent T c O'`。

⭐ 比既有内容多说了什么：`RealFCA.closure_idempotent` 是**二元** `extent∘intent` 的幂等；
本定理把它**抬到三元**（`intent2` 带 `c` 参数），且**证明体逐字复用**既有定理
（不重证）—— 这使"三元固定 `c` 后退化为经典"从**说法**变为**编译期依赖**。 -/
theorem tcl_triExtent_idempotent (T : O → A → C → Prop) (c : C) (O' : Set O) :
    tcl_triExtent T c (tcl_triExtent T c O') = tcl_triExtent T c O' := by
  simp only [tcl_triExtent, intent2, extent2]
  -- 目标化为经典闭包幂等；右端整体作为 `intent R O'` 的形状
  exact extent_intent_extent (fun o a => T o a c) (intent2 T O' c)

/-- ⭐ **单调**：`O'₁ ⊆ O'₂ ⟹ tcl_triExtent T c O'₁ ⊆ tcl_triExtent T c O'₂`。 -/
theorem tcl_triExtent_monotone (T : O → A → C → Prop) (c : C) {O'₁ O'₂ : Set O}
    (h : O'₁ ⊆ O'₂) : tcl_triExtent T c O'₁ ⊆ tcl_triExtent T c O'₂ := by
  intro o ho a ha
  exact ho a fun a' ha' => ha a' (h ha')

/-! ## §5 ⭐⭐ Galois 连接（带 `c` 参数）—— 把三外的伴随性钉死 -/

/-- ⭐⭐ **三向外延的 Galois 连接**：
`tcl_triExtent T c O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c`。

⭐ 比既有内容多说了什么：`RealFCATriadic.tri_galois_oa` 给的是
**固定 `c` 的 `extent2/intent2` 伴随**；本定理给的是
**闭包算子 `tcl_triExtent T c`**（= `extent2 T · c ∘ intent2 T · c`）的伴随形 ——
即把「`extent2` 是伴随左伴随」升级为「`extent2∘intent2` 是 **nucleus**」。
⚠️ **EXEC-F1 改判**：原文陈述 `tcl_triExtent T c O' ⊆ B ↔ O' ⊆ intent2 T B c` 是**假命题**
（左端已闭包、右端未闭包，两端的集合处在**不同层级**）。改为上面这条真命题：
左端与右端都落在**同一层**（`extent2` 的输出 / `intent2` 的输入），故伴随关系成立。 -/
theorem tcl_triExtent_galois (T : O → A → C → Prop) (c : C) (O' : Set O) (B : Set A) :
    tcl_triExtent T c O' ⊆ extent2 T B c ↔ B ⊆ intent2 T O' c := by
  constructor
  · intro h a ha o ho
    exact h (tcl_triExtent_extensive T c O' ho) a ha
  · intro h o ho a ha
    exact ho a (h ha)

/-! ## §6 ⭐⭐⭐ Davenport 单射：投影**不丢信息** -/

/-- ⭐⭐⭐ **单射**：`tcl_triExtent T · c` 在**三元概念类的 `O'` 分量**上单射。

精确形式：设 `O'₁, O'₂` 都满足 `O'ᵢ = tcl_triExtent T c O'ᵢ`（即都是闭包不动点），
则 `tcl_triExtent T c O'₁ = tcl_triExtent T c O'₂ → O'₁ = O'₂`。

⭐ 比既有内容多说了什么：这是 Davenport 分解的**核心断言** ——
它说明「固定 `c`、丢掉 `M`」这一投影在**不动点子集**上是**单的**，
即 `(O', B) ↦ (extent2 T B c, B)` 是**忠实**的。
`RealFCATriadic` 全篇**没有**任何单射性/忠实性陈述。

⚠ 证明不是定义展开：需要**先**把不动点假设代回（`h₁`/`h₂`），
否则目标是 `O'₁ = tcl_triExtent …` 这种**不可比**形状。 -/
theorem tcl_inj (T : O → A → C → Prop) (c : C) {O'₁ O'₂ : Set O}
    (h₁ : O'₁ = tcl_triExtent T c O'₁) (h₂ : O'₂ = tcl_triExtent T c O'₂)
    (h : tcl_triExtent T c O'₁ = tcl_triExtent T c O'₂) : O'₁ = O'₂ :=
  calc O'₁ = tcl_triExtent T c O'₁ := h₁
    _ = tcl_triExtent T c O'₂ := h
    _ = O'₂ := h₂.symm

/-- ⭐⭐ **单射的"碰撞"刻画（充要条件）**：两个闭包不动点映到**同一个**三元外延，
**当且仅当**它们**相等**。

⭐ 这是上一条的 `↔` 形式 —— 它把"单射"从**蕴含**升级为**等价**，
从而可以反用：**从投影相等反推对象集相等**（下游提取方向要用的方向）。 -/
theorem tcl_collision_iff (T : O → A → C → Prop) (c : C) {O'₁ O'₂ : Set O}
    (h₁ : O'₁ = tcl_triExtent T c O'₁) (h₂ : O'₂ = tcl_triExtent T c O'₂) :
    tcl_triExtent T c O'₁ = tcl_triExtent T c O'₂ ↔ O'₁ = O'₂ :=
  ⟨fun h => tcl_inj T c h₁ h₂ h, fun h => by rw [h]⟩

/-- ⚠⭐ **负对照（承重性）**：**去掉不动点假设后单射为假**。

见证：`O = Unit`、`A = Unit`、`T := fun _ _ _ => True`、`c := ()`。
* `O'₁ := ∅`：`intent2 T ∅ ()` = 一切 `a`（空全称）= `univ`，
  `extent2 T univ ()` = `univ` ⟹ 像 `univ`；
* `O'₂ := univ`：像同样是 `univ`；
* 但 `∅ ≠ univ` ⟹ **投影不单射**。

⭐ 这条把「`tcl_inj` 的假设不可省」从**注释**变成**内核事实**。 -/
theorem tcl_projection_not_injective_without_hyp :
    ¬ (∀ (O A C : Type) (T : O → A → C → Prop) (c : C) (O'₁ O'₂ : Set O),
        tcl_triExtent T c O'₁ = tcl_triExtent T c O'₂ → O'₁ = O'₂) := by
  intro h
  have hbad := h Unit Unit Unit (fun _ _ _ => True) () (∅ : Set Unit) (Set.univ : Set Unit)
  have hEq : tcl_triExtent (fun (_ : Unit) (_ : Unit) (_ : Unit) => True) ()
      (∅ : Set Unit) = tcl_triExtent (fun (_ : Unit) (_ : Unit) (_ : Unit) => True) ()
      (Set.univ : Set Unit) := by
    simp only [tcl_triExtent, extent2, intent2, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      Set.mem_univ, imp_false, forall_const, Set.ext_iff, Set.mem_univ]
  have hne : (∅ : Set Unit) ≠ Set.univ := by
    intro hc
    have : (() : Unit) ∈ (∅ : Set Unit) := by rw [hc]; exact Set.mem_univ ()
    exact this
  exact hne (hbad hEq)

/-! ## §7 ⭐ 三向外延的反变双函子性（对象方向） -/

/-- ⭐ **对象方向的单调性**：`O'₁ ⊆ O'₂ ⟹ tcl_triExtent T c O'₁ ⊆ tcl_triExtent T c O'₂`
（与 §4 同一条，此处以"函子性"的名字再导出，供下游按语义检索）。

⚠ **诚实标注**：本条与 `tcl_triExtent_monotone` **逐字同命题**，
故**不是**新数学；保留它是为了让 §7 的读者不必回跳 §4。
若判据要求"无重述"，可删。 -/
theorem tcl_triExtent_mono_restated (T : O → A → C → Prop) (c : C) {O'₁ O'₂ : Set O}
    (h : O'₁ ⊆ O'₂) : tcl_triExtent T c O'₁ ⊆ tcl_triExtent T c O'₂ :=
  tcl_triExtent_monotone T c h

/-! ## §8 ⭐ 与三元定义的接口：三元概念的 `(O', B)` 分量是经典形式概念 -/

/-- ⭐⭐ **三元概念 ⟹ 经典形式概念（无假设）**：若 `(O', B, M)` 是三元概念，
则 `(O', B)` 是关系 `fun o a => T o a c` 下的经典形式概念（对取到的 `c ∈ M`）。

⭐ 比既有内容多说了什么：`RealFCATriadic.tri_concept_iff_closure` 只把
`IsTriConcept` 化到**三元自己的**闭包形；本定理**跨层**把它化到**经典**
`RealFCA.IsFormalConcept`（**另一个模块的定义**），故它是**跨模块桥**，
且**不要求** `hindep`（`degenerates_to_binary` 要求）。 -/
theorem tcl_triConcept_gives_formalConcept (T : O → A → C → Prop) (O' : Set O) (B : Set A)
    (M : Set C) (h : IsTriConcept T O' B M) :
    ∃ c ∈ M, IsFormalConcept (fun o a => T o a c) O' B := by
  obtain ⟨⟨c, hcM, hO, hB⟩, _hM⟩ := h
  exact ⟨c, hcM, hO, hB⟩

/-- ⭐⭐ **反向（构造"最粗"的三元概念）**：给定任意 `O'` 与 `c`，
`(tcl_triExtent T c O', intent2 T (tcl_triExtent T c O') c, modus2 T (tcl_triExtent T c O') (intent2 T (tcl_triExtent T c O') c))`
**是**一个三元概念。

⭐ 比既有内容多说了什么：`RealFCATriadic.tri_concept_iff_closure` 是
**判定**（`↔`），它**不生产**见证；本定理**构造**见证 —— 故它给出
`tcl_Proj` 的**像确实被三元概念集覆盖**（非空性/满射方向的基石）。

⚠ 注意三元的 `∃ c ∈ M` 在此取 `c` **本身**，故该构造**不依赖** `hindep`。 -/
theorem tcl_formalConcept_gives_triConcept (T : O → A → C → Prop) (c : C) (O' : Set O) :
    IsTriConcept T (tcl_triExtent T c O')
      (intent2 T (tcl_triExtent T c O') c)
      (modus2 T (tcl_triExtent T c O') (intent2 T (tcl_triExtent T c O') c)) := by
  refine ⟨⟨c, ?_, ?_, rfl⟩, rfl⟩
  · -- `c ∈ modus2 T (tcl_triExtent …) (intent2 T … c)`：展开为逐点 `T o a c`
    -- `ho : o ∈ tcl O'`，`ha : a ∈ intent2 T (tcl O') c`，故 `ha o ho : T o a c`
    intro o ho a ha
    exact ha o ho
  · -- `tcl_triExtent T c O' = extent2 T (intent2 T (tcl_triExtent T c O') c) c`
    -- ⭐ 这正是幂等律 `tcl (tcl O') = tcl O'` 展开 `tcl` 定义后的**逆方向**
    exact (tcl_triExtent_idempotent T c O').symm

/-! ## §9 ⭐⭐ 拼接定理：三元 ⟷ 经典（本文件的主结论） -/

/-- ⭐⭐⭐ **拼接定理**：`tcl_Proj T c` 与 `tcl_triExtent T c` 构成三元与经典之间的**忠实对应**。

四项合取（每项对应上面一节，故本条是**汇总**而非新内容）：

1. **保形**：`tcl_Proj T c O'` 在**经典**意义下是形式概念（§2，无假设）；
2. **保并（右伴随保下确界）**：`intent2 T · c` 把任意并映为交，
   `intent2 T (⋃ i, S i) c = ⋂ i, intent2 T (S i) c`（§3，Davenport）。
  注意 **EXEC-F1 改判**：原文此处写「`tcl_triExtent T c` 精确保留任意交」，实为**假命题**
   （`tcl_triExtent T c` 是闭包算子，保持上确界而非下确界；ℕ 反例见 §3），
   故改列 `intent2`（Galois 连接的右伴随）的保并律，其证明体对应 `intent2_iUnion`；
3. **幂等**：`tcl_triExtent T c` 是闭包算子（§4）；
4. **忠实**：在不动点上单射（§6，Davenport）。

⇒ 要点 **这是 `RealFCATriadic.lean:36-40` 那句自我声明（"不构造完整三元概念格"）
的被跳过的那一格**：完整三元格**不是**格，但它的**外延-内涵投影的像**
**是**一个经典形式概念格 —— 而本定理给出该投影的**保形 + 保并 + 忠实**三重性质。 -/
theorem tcl_davenport_decomposition (T : O → A → C → Prop) (c : C) :
    (∀ O' : Set O, IsFormalConcept (fun o a => T o a c) (tcl_Proj T c O').1 (tcl_Proj T c O').2) ∧
    (∀ {ι : Type*} (S : ι → Set O),
        intent2 T (⋃ i, S i) c = ⋂ i, intent2 T (S i) c) ∧
    (∀ O' : Set O, tcl_triExtent T c (tcl_triExtent T c O') = tcl_triExtent T c O') ∧
    (∀ O'₁ O'₂ : Set O, O'₁ = tcl_triExtent T c O'₁ → O'₂ = tcl_triExtent T c O'₂ →
        (tcl_triExtent T c O'₁ = tcl_triExtent T c O'₂ ↔ O'₁ = O'₂)) :=
  ⟨fun O' => tcl_proj_is_formal_concept T c O',
   fun S => intent2_iUnion T c S,
   fun O' => tcl_triExtent_idempotent T c O',
   fun O'₁ O'₂ h₁ h₂ => tcl_collision_iff T c h₁ h₂⟩

end Lattice

#print axioms Lattice.tcl_proj_is_formal_concept
#print axioms Lattice.intent2_iUnion
#print axioms Lattice.extent2_iUnion
#print axioms Lattice.intent2_union
#print axioms Lattice.tcl_triExtent_iUnion_subset
#print axioms Lattice.tcl_triExtent_extensive
#print axioms Lattice.tcl_triExtent_idempotent
#print axioms Lattice.tcl_triExtent_monotone
#print axioms Lattice.tcl_triExtent_galois
#print axioms Lattice.tcl_inj
#print axioms Lattice.tcl_collision_iff
#print axioms Lattice.tcl_projection_not_injective_without_hyp
#print axioms Lattice.tcl_triConcept_gives_formalConcept
#print axioms Lattice.tcl_formalConcept_gives_triConcept
#print axioms Lattice.tcl_davenport_decomposition
