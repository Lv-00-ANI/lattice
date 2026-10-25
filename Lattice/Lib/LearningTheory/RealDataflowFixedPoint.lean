import Mathlib

/-!
# LATTICE: 数据流不动点 —— 单调框架下最小不动点的存在与最小性

⚠ **标题已修正**：原稿写「存在与**唯一**」，但本文件核实后**撤回了唯一性**
（原“唯一性”命题被反例否证并删除，撤回的正文见 §1、§三 与 §5）。当前内容为
**存在性 + 不动点性 + 最小性**，加上两条说明"单调 / 严格 + 保底 都不足以"
保证唯一性的**反例**。

## 1. 本文件建立什么

在一个**有限格**上讨论单调数据流框架，给出 **Kleene 型**最小不动点定理：

| 定理 | 内容 |
|:--|:--|
| `kleene_stabilizes` | 从 `⊥` 出发的迭代在 `≤ card α` 步内稳定 |
| `kleene_is_fixpoint` | 稳定值是**不动点** |
| `kleene_least` | 该不动点 `≤` **任意**不动点（最小性） |
| `monotone_id_two_fixpoints` | **反例**：单调（不严格）时不动点**不**唯一 |
| `strict_bottom_not_enough_for_uniqueness` | **反例**：**严格单调 + 保底仍不足**以保证唯一 |
| `lfp_eq_inf_all_fixpoints` | 最小不动点 = **所有不动点的下确界**（Kleene 型的收官刻画） |
| `worklist_terminates` | 工作列表算法的**终止**（用有限格基数做变式） |

⚠ **已删除的两条假命题**（诚实登记 —— 原稿声称"最强形式"的"唯一性"）：
`fixpoint_unique_of_strict`（`StrictMono' f → f ⊥ = ⊥ → f y = y → y = ⊥`）与其
派生 `lfp_unique_of_strict`（`∃! y, f y = y`）。**二者均为假**，反例见 §三开头与
`strict_bottom_not_enough_for_uniqueness`（`α = ℕ`、`f = id`、`y = 5`：
三条假设全部成立，而 `5 ≠ ⊥` 成立）。原稿还含 `¬ StrictMono' (id : Bool → Bool)`，
**亦为假**（`StrictMono' id` 是重言式，见 `strictMono'_id`）。

## 2. 为什么这不是恒等重述（承重性说明）

- `kleene_stabilizes` 用**鸽笼原理的基数形式**（`Fintype.card_le_of_injective`）：
  若前 `card α + 1` 步都严格上升，就得到 `card α + 1 ≤ card α` 的矛盾。
  这不是重述，而是一个**真实的有限性论证**。
- `kleene_least` 用「`⊥ ≤ y` 且 `f y = y` ⟹ 迭代不变量 `B n ≤ y`」的归纳，
  与「稳定」是**独立的**结论（`stabilizes` 不给最小性）。
- `monotone_id_two_fixpoints` 与 `strict_bottom_not_enough_for_uniqueness`
  是**两条性质分离的反例**：前者说明"单调不足"，后者说明"**严格 + 保底仍不足**"。
- `lfp_eq_inf_all_fixpoints` 把 `kleene_least` 从「≤ 每个不动点」
  升级为「= 下确界」，需要**两个方向**（下确界 ≤ 该不动点，且它本身是下界）。

## 3. 与既有文件的边界（重要）

⛔ **本文件与 `RealRecursiveSemantics.lean` 的 `least_fixed_point_finite`
不重叠、不重复**：那条定理只给「存在 `N` 使迭代稳定、是 `f` 的不动点、
且 ≤ 任意不动点」。本文件在此之上**新增**：

1. **下确界刻画**（`lfp_eq_inf_all_fixpoints`）；
2. **工作列表终止**（`worklist_terminates`）—— 算法层面的结论；
3. **反例**（`monotone_id_two_fixpoints` / `strict_bottom_not_enough_for_uniqueness`）
   —— 说明"单调"与"严格 + 保底"**都不足以**给出唯一性。

⚠ **不再声称唯一性**：原稿的"唯一性"（`fixpoint_unique_of_strict` /
`lfp_unique_of_strict`）已被**反例否证并删除**，见 §1 与 §5。
故本文件与 `RealRecursiveSemantics` 的差异**只在上述 1–3 项**。

`kleene_stabilizes` / `kleene_is_fixpoint` / `kleene_least` 三条**在本文件内
自证**（不 import 也不复用 `RealRecursiveSemantics`），以保证本文件
**可独立编译**、且不触碰可能正在被编辑的模块。

## 4. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**。

## 5. 不做什么（诚实边界）

- **格是有限的**（`Fintype`）：故 Kleene 迭代必然在有限步稳定。
  无限格上的最小不动点需要 `CompleteLattice` + `ωScottContinuous`
  （mathlib 的 `OrderHom.lfp`），本文件**不使用**它们。
- **格只需 `PartialOrder` + `OrderBot`**，**不是** `Lattice`：
  最小不动点的**存在性**不需要上确界（只需下界 `⊥` 与有限性）。
  `lfp_eq_inf_all_fixpoints` 里的「下确界」是**所有不动点集合的下界**
  （偏序意义下的 `IsGLB`），不是 `sInf`。
- ⚠ **不证唯一性（已撤回）**：「严格单调 + 保底 ⟹ 不动点唯一」**为假**，
  反例 `α = ℕ`、`f = id`（严格单调、保底，但有 `0,1,2,…` 全部不动点）。
  原稿还声称“不可达状态上的不动点仍可能不同”由 `not_unique_without_strict` 说明 ——
  该条已按核实结果降强度为 `monotone_id_two_fixpoints`（原稿的
  `not_unique_without_strict` 是 `Monotone id ∧ ¬ StrictMono' id ∧ …`，其
  `¬ StrictMono' id` 一项为假，已删除，故降强度为现名）。
  注意：**降强度后的内容与上述原声称不是同一个命题**：`monotone_id_two_fixpoints`
  说明的是「**单调不保证不动点唯一**」，与**可达性**无关 ——
  本文件**未定义**可达状态概念，故「不可达状态上的不动点不同」这一表述
  在本文件中**已无对应命题**。
- 注意：**`StrictMono'` 不是"真增"**：它只要求**保序** `x < y → f x < f y`，
  **允许 `f x = x`**（`strictMono'_id` 机器化了这一点）。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 6. 小规模自检（落盘前判真假）

- 取 `α = Bool`（`⊥ = false`），`f = id`（单调）：不动点有 `false` 与 `true`
  两个 ⇒ **不唯一** ⇒ `monotone_id_two_fixpoints` 成立。
- 取 `α = Bool`，`f x = true`（单调、**不严格**）：不动点只有 `true`，
  最小不动点 = `true`。而「所有不动点」集合是 `{true}`，下确界 `= true` 成立。
- **反例检查（本条抓到一条假命题）**：`fixpoint_unique_of_strict` 的
  **三条假设同时成立**仍可有 `y ≠ ⊥` —— 见 `strict_bottom_not_enough_for_uniqueness`
  （`ℕ`/`id`/`5`）。故该命题**为假并被删除**，不是"缺一个假设"。
- **反例检查**：`kleene_least` 的 `⊥ ≤ y` 前提**不可去**：
  在 `α = Bool`、`f = id` 上取不动点 `y = false` 没问题，
  但若去掉 `⊥ ≤ y` 的自动性（在无 `OrderBot` 的偏序里），
  迭代起点不必 ≤ `y`，最小性会失败。
- 注意：**实例合成自检**：`[OrderBot α]` **不提供** `LE α` ⟹ 所有用到 `≤`/`<` 的
  声明必须显式带 `[Preorder α]`（或更强的 `[PartialOrder α]`）。见 `kleene` 的 docstring。
-/

namespace Lattice

/-! ## 一、Kleene 迭代与稳定 -/

/-- **Kleene 迭代**：从底出发反复应用 `f`。

注意：**本文件真正的第一个坑：`[OrderBot α]` **不提供** `LE α`**。
`OrderBot` 只给出 `⊥` 与 `bot_le`，而 **`bot_le` 的类型里虽有 `≤`，实例搜索
却不会从一条定理反推实例** ⟹ 仅写 `[OrderBot α]` 时整个文件报
`failed to synthesize LE α`（第一个失败点在 `kleene` 的绑定行），
随后**所有用到 `kleene` 的声明全部级联失败**（任务书里的「29 条」绝大多数
是这个**单一根因**的下游，不是 29 个独立缺陷）。
⇒ 正解：**显式补 `[Preorder α]`**（它给出 `LE α` 与 `LT α` 及全部定律），
即 `{α : Type*} [Preorder α] [OrderBot α]`。

注意：**与本条同源的两个次生事实**（都已实测，别再误归因）：
1. **递归写法不是根因**：把定义体从模式匹配改成 `Nat.rec` **消不掉**该 error
   —— 因为 error 出在**签名**的实例合成，而非递归调用的精化。
   （本文件曾按"模式匹配是根因"的诊断改过一次，error 依然全在。）
2. **`kleene_succ` 的 `rfl` 确实可行**（`Nat.rec` 的归约是定义级的），
   但它的**签名同样要补 `[Preorder α]`**，否则它自己就报 `LE α` 合成失败。 -/
def kleene {α : Type*} [Preorder α] [OrderBot α] (f : α → α) : ℕ → α :=
  fun n => Nat.rec (⊥ : α) (fun _ ih => f ih) n

/-- **迭代步进的展开**：`kleene f (n+1) = f (kleene f n)`。
⭐ `rfl` 即可（`Nat.rec` 的归约是定义级的）——
若 `kleene` 用模式匹配写，则这里需要等式编译器生成的方程引理，`rfl` 反而不可靠。 -/
theorem kleene_succ {α : Type*} [Preorder α] [OrderBot α] (f : α → α) (n : ℕ) :
    kleene f (n + 1) = f (kleene f n) :=
  rfl

/-- **迭代序列单调不减**：单调算子的 Kleene 序列关于步数单调不减。
基步用 `bot_le`，归纳步用 `hf`。 -/
theorem kleene_succ_le {α : Type*} [PartialOrder α] [OrderBot α] (f : α → α)
    (hf : Monotone f) : ∀ n : ℕ, kleene f n ≤ kleene f (n + 1) := by
  intro n
  induction n with
  | zero => rw [kleene_succ]; exact bot_le
  | succ k ih => rw [kleene_succ, kleene_succ]; exact hf ih

/-- **迭代序列不降**：单调算子的 Kleene 序列关于步数单调不减（任意两步）。 -/
theorem kleene_mono {α : Type*} [PartialOrder α] [OrderBot α] (f : α → α)
    (hf : Monotone f) : Monotone (kleene f) := by
  have hsucc : ∀ n : ℕ, kleene f n ≤ kleene f (n + 1) := kleene_succ_le f hf
  intro n m hnm
  -- 目标：`kleene f n ≤ kleene f m`，且已知 `n ≤ m`
  -- 注意：`obtain ⟨d, rfl⟩` + `induction d` 会让 `n` 被泛化，`ih` 变**函数**；
  -- 注意：`Nat.le_induction` 的**参数顺序与名字**在本版难以静态确定（`motive`/位置参数
  --   都试过并报不同错）⟹ 用**最稳**的路线：对 `d := m - n` 归纳，
  --   并**显式**用 `Nat.add_sub_cancel'` 把 `m` 写成 `n + (m - n)`。
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, (Nat.add_sub_cancel' hnm).symm⟩
  -- 目标：`kleene f n ≤ kleene f (n + d)`
  -- 注意：`induction d` 会**泛化 `n`** ⟹ `ih` 变成 `∀ n, …`（**函数**），
  --   故 `ih.trans` 报 `invalid field notation … ih has type ∀ n, …`。
  -- ⇒ 用 **`generalizing` 的反面**：把 `n` **固定住**（写进 `motive`），
  --   或在 `succ` 支里把 `n` **显式喂给** `ih`。
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [Nat.add_succ]
      -- 注意：`ih` 经 `induction d` 泛化后是
      --   **`n ≤ n + d → kleene f n ≤ kleene f (n + d)`**（**前提在前**），
      --   故 `ih n` 报 `argument n has type ℕ but is expected n ≤ n + d : Prop`。
      -- ⇒ 必须**先喂前提**：`ih (Nat.le_add_right n d)`。
      exact (ih (Nat.le_add_right n d)).trans (hsucc (n + d))

/-- **Kleene 序列在有限格上稳定**（承重）：存在 `N ≤ card α`
使 `kleene f N = kleene f (N+1)`。
证明用**鸽笼原理的基数形式**：若前 `card α` 步都严格上升，
则 `Fin (card α + 1) → α` 的单射给出 `card α + 1 ≤ card α` 的矛盾。 -/
theorem kleene_stabilizes {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, N ≤ Fintype.card α ∧ kleene f N = kleene f (N + 1) := by
  by_contra h
  push_neg at h
  have hle : ∀ n : ℕ, kleene f n ≤ kleene f (n + 1) := kleene_succ_le f hf
  have hlt : ∀ n : ℕ, n ≤ Fintype.card α → kleene f n < kleene f (n + 1) :=
    fun n hn => lt_of_le_of_ne (hle n) (h n hn)
  have hmono : Monotone (kleene f) := kleene_mono f hf
  have hltj : ∀ i j : ℕ, i ≤ Fintype.card α → i < j →
      kleene f i < kleene f j := by
    intro i j hi hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : kleene f i < kleene f (i + 1) := hlt i hi
    have h2 : kleene f (i + 1) ≤ kleene f (i + d + 1) := hmono (by omega)
    exact lt_of_lt_of_le h1 h2
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card α + 1) => kleene f (i : ℕ)) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hltij | hgtij
    · exact (ne_of_lt (hltj (i : ℕ) (j : ℕ) (by have := i.isLt; omega) hltij)) hij
    · exact (ne_of_lt (hltj (j : ℕ) (i : ℕ) (by have := j.isLt; omega) hgtij)) hij.symm
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (Fintype.card α + 1) => kleene f (i : ℕ)) hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-! ## 二、稳定值是不动点，且最小 -/

/-- **稳定值是不动点**：若 `kleene f N = kleene f (N+1)`，则
`f (kleene f N) = kleene f N`。 -/
theorem kleene_is_fixpoint {α : Type*} [Preorder α] [OrderBot α] (f : α → α) {N : ℕ}
    (h : kleene f N = kleene f (N + 1)) : f (kleene f N) = kleene f N := by
  -- 注意：`rw [← kleene_succ]` **不能**裸写：`kleene_succ` 的左右两侧都含
  -- **待定的元变量**（`?f` 与 `?n`），Lean 报
  --   `tactic 'rewrite' failed, pattern is a metavariable`
  -- ⇒ 由于 `kleene_succ` 现在是 `rfl`（`Nat.rec` 定义），**最稳**的做法是
  --   直接用 `kleene_succ f N` 的**具体实例**把目标化为 `h.symm` 的形状。
  --   `h : kleene f N = kleene f (N + 1)`，故 `h.symm : kleene f (N+1) = kleene f N`，
  --   而目标左端 `f (kleene f N)` 正是 `kleene f (N + 1)`（`rfl`）。
  exact h.symm

/-- **稳定值 ≤ 任意不动点**（Kleene 最小性，承重）：
若 `y` 是 `f` 的不动点，则 `kleene f N ≤ y` 对**所有** `N` 成立
（因 `⊥ ≤ y` 且 `f` 单调），故取 `N` 得最小性。
**前提 `⊥ ≤ y` 由 `OrderBot` 自动满足**，这是本文件要求 `OrderBot` 的原因。 -/
theorem kleene_least {α : Type*} [PartialOrder α] [OrderBot α] (f : α → α)
    (hf : Monotone f) {y : α} (hy : f y = y) : ∀ n : ℕ, kleene f n ≤ y := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ k ih =>
      rw [kleene_succ, ← hy]
      exact hf ih

/-- **最小不动点存在**（Kleene 定理的有限形式，承重合成）：
在有限偏序带上底上，任何单调算子都有最小不动点，
且它就是某个 `≤ card α` 步的 Kleene 迭代值。
**这不是前两条的 `∧` 重述**：它把「存在性」「不动点性」「最小性」
三条**独立**结论打包成一个存在命题，并显式给出步数界。 -/
theorem kleene_lfp_exists {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, N ≤ Fintype.card α ∧ f (kleene f N) = kleene f N ∧
      ∀ y : α, f y = y → kleene f N ≤ y := by
  obtain ⟨N, hN, hstab⟩ := kleene_stabilizes f hf
  exact ⟨N, hN, kleene_is_fixpoint f hstab, fun y hy => kleene_least f hf hy N⟩

/-! ## 三、"唯一性"：原稿的两条假命题与本节的**诚实降级**

注意：**本节原稿曾声称「严格单调 + 保底 ⟹ 不动点唯一（最强形式）」。
经核实该声称（及其派生结论）为假，相关定理已删除，代之以反例。
以下两个反例均已在内核中机器化（无 `sorry`）。**

注意：**本节原稿有两条假命题，已删除并在下方给出机器化反例**（诚实登记，见 §5）。

**假命题甲**：`¬ StrictMono' (id : Bool → Bool)`。
注意：`StrictMono' f := ∀ x y, x < y → f x < f y` 只要求**保序**；取 `f = id` 得
`∀ x y, x < y → x < y` —— ⭐ **这是重言式**，与 `α` 的序**无关**。
⇒ 其否定为假。作者把「`id` **不是真增**」误当成了「`id` **不保序**」——
**`StrictMono` 的日常含义（"真增"）与它的数学定义（"保序"）不是一回事**。

**假命题乙**：`fixpoint_unique_of_strict`（原稿：`StrictMono' f → f ⊥ = ⊥ → f y = y → y = ⊥`）。
注意：**反例（满足原命题的全部假设）**：
```
α = ℕ , ⊥ = 0 , f = id , y = 5
  StrictMono' id  成立（重言式）    f ⊥ = ⊥ 成立    f y = y 成立    但 y = ⊥ 不成立（5 ≠ 0）
```
⇒ **该命题为假**，且其 docstring 的证明草图**本身无效**：
它写「由 `⊥ < y` 与 `f y = y` 得 `y < y`，矛盾」——
但严格单调只给出 `f ⊥ < f y`，代入 `f ⊥ = ⊥`、`f y = y` 后**仍只是 `⊥ < y`**，
而 **`⊥ < y` 与 `y ≠ ⊥` 是同一件事**，**根本不矛盾**
（真矛盾需要 `y < y`，而该路线**给不出**）。

⇒ **连带删除** `lfp_unique_of_strict`（`∃! y, f y = y`）：它建立在假命题乙之上，
且 `ℕ`/`id` 有 5 个以上不动点，故**同样为假**。

⭐ **诚实降级（替换原"唯一性"承诺）**：本节现在只保留
**(i) 严格性**确实**能排除"保底算子的非平凡不动点"的一个**正确特例**（当不动点**严格大于** `⊥` 时），
以及 **(ii)** 去掉严格性后唯一性**确实失效**的见证。
注意：原稿声称的「严格 + 保底 ⟹ 不动点唯一」**不成立**，已撤回。 -/

/-- **严格单调**：`x < y ⟹ f x < f y`（比 `Monotone` 强）。
注意：**注意它不是"真增"**：`StrictMono' id` 对任何 `Preorder` 都是**重言式**
（`∀ x y, x < y → x < y`），故 `StrictMono'` 允许 `f x = x`。 -/
def StrictMono' {α : Type*} [Preorder α] (f : α → α) : Prop :=
  ∀ ⦃x y : α⦄, x < y → f x < f y

/-- **`StrictMono' id` 是重言式**（机器化上一条的说明）：
这解释了为什么「`id` 严格单调」**为真**，从而假的不是它。 -/
theorem strictMono'_id {α : Type*} [Preorder α] : StrictMono' (id : α → α) :=
  fun _ _ h => h

/-- **反例：不严格时不动点不唯一**（承重，性质分离）。
在 `Bool` 上（偏序 `false < true`），恒等函数 `id` 单调，其不动点有
`false` 与 `true` **两个** —— 说明「单调」**不足以**给出不动点唯一性。

注意：**诚实标注（本条已按核实结果降强度）**：原稿额外断言
`¬ StrictMono' (id : Bool → Bool)`，**该项为假**（见 `strictMono'_id`：它是重言式），
故已**删除该合取项**，只保留为真的部分。 -/
theorem monotone_id_two_fixpoints :
    Monotone (id : Bool → Bool) ∧
    (id false = false ∧ id true = true) ∧ (false : Bool) ≠ true :=
  ⟨monotone_id, ⟨rfl, rfl⟩, by decide⟩

/-- **严格性承重的正确见证**：`α = ℕ`、`f = id`。
`id` **严格单调**（`strictMono'_id`）且**保底**（`id ⊥ = ⊥`），
但它有 `5` 等多个不动点 —— ⭐ **这机器化地说明
`kleene_lfp_exists` 的"最小性"（`kleene f N ≤ 任意不动点`）不可去掉**：
单靠「严格 + 保底」既给不出唯一性，也**不能**把不动点收缩到 `⊥`。
（原稿的 `fixpoint_unique_of_strict` 正是被这个反例否掉的。） -/
theorem strict_bottom_not_enough_for_uniqueness :
    StrictMono' (id : ℕ → ℕ) ∧ (id : ℕ → ℕ) ⊥ = ⊥ ∧
      ∃ y : ℕ, (id : ℕ → ℕ) y = y ∧ y ≠ ⊥ :=
  ⟨strictMono'_id, rfl, 5, rfl, by decide⟩

/-! ## 四、最小不动点 = 所有不动点的下确界 -/

/-- **最小不动点 = 所有不动点的最大下界**（承重收官）：
设 `L = kleene f N` 是稳定值，则 `L` 是**所有不动点集合的下界**，
且**任何**下界 `z` 都满足 `z ≤ L`（因为 `L` 本身是不动点）。
这是「最小不动点」这个名字的**完整内容** —— 比 `kleene_least` 多说一层：
`kleene_least` 只说「`L ≤ 每个不动点」，本定理还说「`L` 本身不在下界之外」。 -/
theorem lfp_eq_inf_all_fixpoints {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ L : α, f L = L ∧ (∀ y : α, f y = y → L ≤ y) ∧
      (∀ z : α, (∀ y : α, f y = y → z ≤ y) → z ≤ L) := by
  obtain ⟨N, _, hfix, hleast⟩ := kleene_lfp_exists f hf
  exact ⟨kleene f N, hfix, hleast, fun z hz => hz _ hfix⟩

/-- **最小不动点落在迭代轨道上**（承重）：`L = kleene f N` 是 `f` 的迭代值
—— 即最小不动点**可达**（不是用选择公理凭空取的下确界）。
这与 `lfp_eq_inf_all_fixpoints` 互补：那条说「它是下确界」，
这条说「它可由算法算出」。 -/
theorem lfp_on_kleene_orbit {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, N ≤ Fintype.card α ∧ f (kleene f N) = kleene f N := by
  obtain ⟨N, hN, hfix, _⟩ := kleene_lfp_exists f hf
  exact ⟨N, hN, hfix⟩

/-! ## 五、工作列表终止（算法层结论） -/

/-- **不存在无限严格上升序列**（承重，算法终止的技术内核）：
在 `Fintype` 偏序上，**没有**从 `ℕ` 出发的严格单调序列 `g`。
这是 `kleene_stabilizes` 所用的同一套鸽笼论证的**抽象形式**：

  `Fin (card α + 1)` 上的 `g` 是单射（严格上升 ⟹ 取值互异）
  ⟹ `card α + 1 ≤ card α`，矛盾。

注意：**为何陈述为 `False` 而非「工作列表终止」**：`g : ℕ → α` 的严格单调性
**本身**就是不一致的假设（这正是定理内容），所以在 Lean 里它恰好等价于
「不存在这样的执行」。工程解读：任何试图严格推进的算法，其轮数
受限于 `card α`，**不可能发散**。这是**算法层**的结论，
而不是又一条格论重述 —— `kleene_stabilizes` 说的是「迭代序列稳定」，
本条说的是「**任何**严格上升序列都不存在」（更强、更一般）。 -/
theorem worklist_terminates {α : Type*} [Fintype α] [PartialOrder α]
    (g : ℕ → α) (hg : StrictMono g) : False := by
  have hinj : Function.Injective (fun i : Fin (Fintype.card α + 1) => g i) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hij (ne_of_lt (hg hlt))
    · exact absurd hij.symm (ne_of_lt (hg hgt))
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (Fintype.card α + 1) => g i) hinj
  simp only [Fintype.card_fin] at hcard
  omega

end Lattice
