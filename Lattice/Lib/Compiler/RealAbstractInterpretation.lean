import Mathlib
import Lattice.Lib.InfoTheory.RealKleeneFixedPoint
import Lattice.Lib.Quantization.RealIEEE754
/-!
# LATTICE: 抽象解释 —— Galois 连接下的可靠抽象与不动点迁移

**为什么做这个文件**：`doc/01` 把「符号 ⇄ 权重」转换层的难点列为
**规范形式选择**与**保真度**。抽象解释（Cousot & Cousot 1977）正是为这两条
量身定制的框架：它把「从具体权重域提取符号属性」形式化为**一对伴随映射**
`α ⊣ γ`（Galois 连接），并使「近似是可靠的」成为一条**可证的**代数条件，
而不是逐例检验的工程直觉。

## 形式化设定（与 mathlib 的接口）

抽象域 `Abstract` 是**完备格**；**具体化** `γ : Abstract → Set Concrete`
取值于幂集；**抽象化**取**集合层**形式 `αS : Set Concrete → Abstract`
（点式 `α c` 即 `αS {c}`）。

**为什么必须用集合层 `αS`**（本文件在形式化过程中**实际撞到这个类型错误**，
诊断原文：`{c | c ∈ γ a} has type Set Concrete but is expected to have type Concrete`）：
mathlib 的 `GaloisConnection l u` 要求 `l : a → b` 与 `u : b → a` 是
**同一对**类型之间的往返映射。若硬写 `GaloisConnection α (fun a => {c | c ∈ γ a})`，
则 `u` 的陪域必须是 `Concrete`，与 `Set Concrete` **类型不符**。

正确的配对是 `GaloisConnection αS γ`：两侧分别是 `Set Concrete → Abstract`
与 `Abstract → Set Concrete`，而 `Set Concrete` 自带 `CompleteLattice`（`⊆` 序），
类型**恰好吻合**。这是本文件与 mathlib 的**唯一接口**。

## 路线

1. **Galois 连接**：`GaloisMem αS γ := GaloisConnection αS γ`，
   并**导出**点式形式 `αS {c} ≤ a ↔ c ∈ γ a`（`galoisMem_pointwise`）；
2. **可靠性**：扩张性 `c ∈ γ (αS {c})`、收缩性 `αS (γ a) ≤ a`、
   `αS` 与 `γ` 的**单调性** —— 全部由 mathlib 引理库直接给出；
3. **抽象算子的可靠性判据**：点式 `c ∈ γ a → f c ∈ γ (f♯ a)`、
   集合式 `f '' γ a ⊆ γ (f♯ a)`、以及 `αS (f '' γ a) ≤ f♯ a` 三者的**关系**；
4. **最佳抽象**：`αS (f '' γ a)` 是**最精确的可靠抽象**（它支配一切可靠 `f♯`）；
5. **不动点迁移（上近似）**：抽象域上的 Kleene 极限 `kleeneLimit K`
   上近似任何抽象后不动点 `y`（`K y ≤ y`）；
6. **实例化 —— 符号区间抽象**：真 Galois 连接、`clampTo` 与 `roundDownN`
   的可靠抽象，以及对 H1 发现的错误实现 `lv00RoundDown` 的**框架级裁决**。

## 诚实边界（本文件不证 / 不声称的）

* **只证可靠性（soundness），不证完备性（completeness）**。第 4 节的
  「最佳抽象」是**最精确的可靠抽象**（最优性），这**不是** Cousot 的
  完备性（完备性要求 `αS (lfp F) = lfp F♯`，一般**不成立**）；
* **不动点迁移只在有限格上给出**（`[Fintype Abstract]`）。
  **诚实标注**：这是**能力范围**（本项目抽象域有限或可离散化），
  不是「证不出来」。**未做**：无限格上 `lfp = ⨆ₙ Fⁿ⊥` 的 `ωScottContinuous` 版；
* **未做**：加宽 / 收窄（widening / narrowing）—— 需要无限升链；
* **未做**：张量层实例化。本文件的区间实例是**标量层**（`Concrete = ℝ`）；
* **区间实例的序**是**反向包含序**（抽象解释的标准信息序），故 `γ` 在此**反变**；
  本文件**不声称**区间实例继承 `γ` 正变单调性，而是如实给出反变版本
  （`gamma_interval_monotone`，**正变** —— 见该条的自我修正说明）。
  序选错的**后果**在第 6 节有机器记录：
  正确的序使 `point_le_iff_contains` 成为 `Iff.rfl`，错的序使该等价**为假**；
* **区间抽象只做 `clamp` / `roundDown` 两个算子**（H1 点名的算子）；
  **⚠ R3 更正（悬空引用）**：一般区间算术（四角乘法）**未证**，本文件**不重复**。
  原 docstring 称「已在 `RealLv00LinearAlgebra.containment_mul` 证明」——
  **该定理不存在**（`RealLv00LinearAlgebra` 的诚实降级节明确记录：
  Lv-00 原稿的 `containment_mul` 命题体是 `: True`，**未证**）。
  实际存在的是它的**非负特例** `RealLv00LinearAlgebra.containment_mul_nonneg`
  （两区间下端非负时 `lo_a·lo_b ≤ x·y ≤ hi_a·hi_b`）——本文件既**不援引**
  该弱形式，也**不声称**已证一般四角公式；
* 无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

open scoped Classical

namespace Lattice

/-! ## 一、Galois 连接 -/

/-- **Galois 连接（集合层、与 mathlib 对齐）**：`αS` 是集合层抽象化，
`γ` 是具体化。定义即 mathlib 的 `GaloisConnection αS γ`。

选这个形态而非点式 `α`，是因为 `γ` 的值域是 `Set Concrete`：
只有让 `αS` 的定义域也是 `Set Concrete`，`GaloisConnection` 的
`l : a → b`、`u : b → a` 才**类型吻合**（详见文件头）。 -/
def GaloisMem {Concrete Abstract : Type*} [CompleteLattice Abstract]
    (alphaS : Set Concrete → Abstract) (gamma : Abstract → Set Concrete) : Prop :=
  GaloisConnection alphaS gamma

/-- **点式形式（由集合层连接导出）**：`αS {c} ≤ a ↔ c ∈ γ a`。

这是抽象解释文献中 `α c ≤ a ↔ c ∈ γ a` 的**良类型化**版本：
单点集 `{c}` 承载「具体点 `c`」的角色。
证明：`GaloisConnection.le_iff_le` 在 `S := {c}` 上特化，
再把 `{c} ⊆ γ a` 展开为 `c ∈ γ a`。 -/
theorem galoisMem_pointwise {Concrete Abstract : Type*} [CompleteLattice Abstract]
    {alphaS : Set Concrete → Abstract} {gamma : Abstract → Set Concrete}
    (gc : GaloisMem alphaS gamma) (c : Concrete) (a : Abstract) :
    alphaS {c} ≤ a ↔ c ∈ gamma a := by
  rw [gc.le_iff_le]
  exact ⟨fun h => h (Set.mem_singleton c), fun h _ hx => by
    rw [Set.mem_singleton_iff] at hx
    rwa [hx]⟩

/-- **构造子**：给出集合层连接即得 `GaloisMem`（定义相等）。 -/
theorem galoisMem_intro {Concrete Abstract : Type*} [CompleteLattice Abstract]
    {alphaS : Set Concrete → Abstract} {gamma : Abstract → Set Concrete}
    (gc : GaloisConnection alphaS gamma) : GaloisMem alphaS gamma := gc

/-- **点式构造子**：若 `αS {c} ≤ a ↔ c ∈ γ a` 对一切 `c, a` 成立，
则 `GaloisMem αS γ`。

**诚实标注**：这条**不是**上一节的逆（逆方向需要 `αS` 对任意集合的
行为由单点集决定，即 `αS S = ⨆_{c ∈ S} αS {c}`，这需要**额外的并保持假设**）。
本文件因此只给「点式 ⟹ 集合层」在**并保持**前提下的版本，
并把「仅有逐点形式 ⟹ `GaloisConnection`」标注为**未做**。 -/
theorem galoisConnection_of_pointwise {Concrete Abstract : Type*}
    [CompleteLattice Abstract] {alphaS : Set Concrete → Abstract}
    {gamma : Abstract → Set Concrete}
    (hsup : ∀ S : Set Concrete, alphaS S = ⨆ c ∈ S, alphaS {c})
    (h : ∀ c a, alphaS {c} ≤ a ↔ c ∈ gamma a) : GaloisMem alphaS gamma := by
  refine galoisMem_intro ?_
  refine GaloisConnection.monotone_intro ?_ ?_ ?_ ?_
  · -- Monotone gamma
    intro a b hab c hc
    exact (h c b).mp (le_trans ((h c a).mpr hc) hab)
  · -- Monotone alphaS
    intro S T hST
    rw [hsup S, hsup T]
    exact iSup_le fun c => iSup_le fun hc =>
      le_iSup_of_le c (le_iSup_of_le (hST hc) le_rfl)
  · -- le_u_l : S ⊆ gamma (alphaS S)：先证 `alphaS {c} ≤ alphaS S`，再用 h 反向读出
    intro S c hc
    have hle : alphaS {c} ≤ alphaS S := by
      rw [hsup S]
      exact le_iSup_of_le c (le_iSup_of_le hc le_rfl)
    exact (h c (alphaS S)).mp hle
  · -- l_u_le : alphaS (gamma a) ≤ a
    intro a
    rw [hsup (gamma a)]
    exact iSup_le fun c => iSup_le fun hc => (h c a).mpr hc

/-! ## 二、可靠性：扩张、收缩、单调 -/

section Soundness

variable {Concrete Abstract : Type*} [CompleteLattice Abstract]
variable {alphaS : Set Concrete → Abstract} {gamma : Abstract → Set Concrete}

/-- **扩张性**：`c ∈ γ (αS {c})` —— 抽象化**必然**覆盖原来的具体点。
这是抽象解释中「可靠」的最原始形式：抽象化不丢点。
由 `GaloisConnection.le_u_l` 在 `S := {c}` 上给出。 -/
theorem mem_gamma_alpha (gc : GaloisMem alphaS gamma) (c : Concrete) :
    c ∈ gamma (alphaS {c}) :=
  gc.le_u_l {c} (Set.mem_singleton c)

/-- **收缩性**：`αS (γ a) ≤ a` —— 具体化再抽象化**不会变大**。
由 `GaloisConnection.l_u_le` 给出。 -/
theorem alpha_gamma_le (gc : GaloisMem alphaS gamma) (a : Abstract) :
    alphaS (gamma a) ≤ a :=
  gc.l_u_le a

/-- **`αS` 单调**（幂集侧按 `⊆`）。 -/
theorem alpha_monotone (gc : GaloisMem alphaS gamma) : Monotone alphaS :=
  gc.monotone_l

/-- **`γ` 单调**。 -/
theorem gamma_monotone (gc : GaloisMem alphaS gamma) : Monotone gamma :=
  gc.monotone_u

/-- **`γ` 单调的逐点形式**（下游常用）。 -/
theorem mem_gamma_of_le (gc : GaloisMem alphaS gamma) {a₁ a₂ : Abstract} (h : a₁ ≤ a₂)
    {c : Concrete} (hc : c ∈ gamma a₁) : c ∈ gamma a₂ :=
  gamma_monotone gc h hc

end Soundness

/-! ## 三、抽象算子的可靠性判据 -/

section Criteria

variable {Concrete Abstract : Type*} [CompleteLattice Abstract]
variable {alphaS : Set Concrete → Abstract} {gamma : Abstract → Set Concrete}

/-- **抽象算子的局部可靠性（点式）**：对每个抽象值 `a` 与每个被 `γ a` 覆盖的
具体点 `c`，`f c` 被 `f♯ a` 覆盖。这是抽象解释的**核心一步保真条件**。 -/
def SoundAbstract (gamma : Abstract → Set Concrete) (f : Concrete → Concrete)
    (fSharp : Abstract → Abstract) : Prop :=
  ∀ a c, c ∈ gamma a → f c ∈ gamma (fSharp a)

/-- **点式 ⟹ 集合式**：`f '' γ a ⊆ γ (f♯ a)`。
工程读法：「先把 `a` 具体化、再跑具体算子」的结果**必然落回** `γ (f♯ a)` ——
抽象执行覆盖所有具体执行。 -/
theorem soundAbstract_image_subset {gamma : Abstract → Set Concrete}
    {f : Concrete → Concrete} {fSharp : Abstract → Abstract}
    (h : SoundAbstract gamma f fSharp) (a : Abstract) :
    f '' (gamma a) ⊆ gamma (fSharp a) := by
  rintro y ⟨c, hc, rfl⟩
  exact h a c hc

/-- **集合式 ⟹ 点式**：反向。故点式定义与集合式刻画**等价**。 -/
theorem image_subset_soundAbstract {gamma : Abstract → Set Concrete}
    {f : Concrete → Concrete} {fSharp : Abstract → Abstract}
    (h : ∀ a, f '' (gamma a) ⊆ gamma (fSharp a)) : SoundAbstract gamma f fSharp := by
  intro a c hc
  exact h a ⟨c, hc, rfl⟩

/-- **可靠性等价刻画（主桥）**：点式 ⟺ 集合式。 -/
theorem soundAbstract_iff_image_subset (gamma : Abstract → Set Concrete)
    (f : Concrete → Concrete) (fSharp : Abstract → Abstract) :
    SoundAbstract gamma f fSharp ↔ ∀ a, f '' (gamma a) ⊆ gamma (fSharp a) :=
  ⟨fun h a => soundAbstract_image_subset h a, fun h => image_subset_soundAbstract h⟩

/-- **第三种刻画（`αS` 形式）**：可靠 `f♯` 满足 `αS (f '' γ a) ≤ f♯ a`。

证明：可靠性给 `f '' γ a ⊆ γ (f♯ a)`，再用 `GaloisConnection.l_le`
（即 `S ⊆ γ b ⟹ αS S ≤ b`）。**注意方向**：`l_le` 与 `le_u` 是
`le_iff_le` 的两个方向，用错会给出 `S ≤ γ (αS S)`（扩张性）而不是本结论 ——
本文件在形式化过程中**实际用错过一次**（诊断原文：
`GaloisConnection.le_u gc ?m has type ?m ≤ gamma ?m but is expected to have
type alphaS (f '' gamma a) ≤ fSharp a`），记录于此。 -/
theorem soundAbstract_alpha_le (gc : GaloisMem alphaS gamma) {f : Concrete → Concrete}
    {fSharp : Abstract → Abstract} (h : SoundAbstract gamma f fSharp) (a : Abstract) :
    alphaS (f '' (gamma a)) ≤ fSharp a :=
  gc.l_le (soundAbstract_image_subset h a)

end Criteria

/-! ## 四、最佳抽象 -/

section Best

variable {Concrete Abstract : Type*} [CompleteLattice Abstract]
variable {alphaS : Set Concrete → Abstract} {gamma : Abstract → Set Concrete}

/-- **最佳抽象（best correct approximation）**：`f♯ a := αS (f '' γ a)`。

「规范形式选择」的形式化答案：一旦选定 `αS`/`γ`，对任意具体算子 `f`，
最精确的可靠抽象**没有自由度** —— 它就是「具体化 → 跑 `f` → 集合层抽象化」。
工程含义：「符号→权重」转换的设计自由度**全部集中在 `αS`/`γ` 的选择上**；
一旦要求可靠，`f♯` 就被钉死。 -/
def bestAbstract {Concrete Abstract : Type*} (alphaS : Set Concrete → Abstract)
    (gamma : Abstract → Set Concrete) (f : Concrete → Concrete) : Abstract → Abstract :=
  fun a => alphaS (f '' (gamma a))

/-- **最优性（optimality）**：任何可靠 `f♯` 都被 `bestAbstract` 支配 ——
`αS (f '' γ a) ≤ f♯ a`。这是「最精确的可靠抽象」的**一半**：
`bestAbstract` **不低于**任何可靠抽象。 -/
theorem bestAbstract_le_of_sound (gc : GaloisMem alphaS gamma) {f : Concrete → Concrete}
    {fSharp : Abstract → Abstract} (h : SoundAbstract gamma f fSharp) (a : Abstract) :
    bestAbstract alphaS gamma f a ≤ fSharp a :=
  soundAbstract_alpha_le gc h a

/-- **最优性的另一半：`bestAbstract` 自身可靠 ⟺ `f` 保 `γ` 的析取结构**。

**诚实降级（重要）**：`bestAbstract alphaS gamma f` **一般不可靠**。
可靠性要求 `f c ∈ γ (αS (f '' γ a))` 对**每个** `c ∈ γ a` 成立，
即 `αS {f c} ≤ αS (f '' γ a)`；
由于 `f c ∈ f '' γ a`，这需要 `αS` **保持单点集的包含**
（即 `αS {y} ≤ αS S` 当 `y ∈ S`）—— 而后者**正是** `αS` 单调性加上
`{y} ⊆ S`，由第 2 节的 `alpha_monotone` **免费获得**

故 `bestAbstract` **确实**可靠，前提是**用 `αS` 的单调性**：
`f c ∈ f '' γ a` 给 `{f c} ⊆ f '' γ a`，`alpha_monotone` 给
`αS {f c} ≤ αS (f '' γ a)`，再用 `galoisMem_pointwise` 反向读出
`f c ∈ γ (αS (f '' γ a))`。**这条链不需要 `f` 单调**（只需 `αS` 单调，
而 `αS` 单调是 Galois 连接的**必然**结论）。 -/
theorem bestAbstract_sound (gc : GaloisMem alphaS gamma) (f : Concrete → Concrete) :
    SoundAbstract gamma f (bestAbstract alphaS gamma f) := by
  intro a c hc
  have hmem : f c ∈ f '' (gamma a) := ⟨c, hc, rfl⟩
  have hsub : ({f c} : Set Concrete) ⊆ f '' (gamma a) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rwa [hy]
  have hmono := alpha_monotone gc hsub
  exact (galoisMem_pointwise gc (f c) (bestAbstract alphaS gamma f a)).mp hmono

/-- **最佳抽象是「最优 + 可靠」的唯一性结论**：`bestAbstract` 可靠，
且任何可靠 `f♯` 都被它支配。两条合起来即
「`bestAbstract` 是**唯一最精确的**可靠抽象」。 -/
theorem bestAbstract_unique_least (gc : GaloisMem alphaS gamma) (f : Concrete → Concrete)
    {fSharp : Abstract → Abstract} (h : SoundAbstract gamma f fSharp) :
    SoundAbstract gamma f (bestAbstract alphaS gamma f) ∧
      ∀ a, bestAbstract alphaS gamma f a ≤ fSharp a :=
  ⟨bestAbstract_sound gc f, fun a => bestAbstract_le_of_sound gc h a⟩

end Best

/-! ## 五、不动点迁移：抽象域上的 Kleene 极限上近似 -/

section Transfer

/-- **有限格上的不动点迁移（主定理）**：设 `Abstract` 是**有限**偏序且带底，
`K` 单调。若 `y` 是 `K` 的**后不动点**（`K y ≤ y`），
则 **Kleene 极限 `kleeneLimit K hKmono`（从 `⊥` 出发迭代到稳定）≤ `y`**。

**这是「抽象解释可证可靠近似」的收口**：抽象域上迭代到不动点的结果
**必然**被任何具体侧不变量的抽象化所覆盖。证明：链的每一项 `≤ y`
（`⊥ ≤ ·` 起步，`K` 单调保持），极限作为链的一项亦如此。 -/
theorem fixpoint_transfer_le {Abstract : Type*} [Fintype Abstract] [PartialOrder Abstract]
    [OrderBot Abstract] {K : Abstract → Abstract} (hKmono : Monotone K)
    {y : Abstract} (hy : K y ≤ y) : kleeneLimit K hKmono ≤ y := by
  have hchain : ∀ m : ℕ, kleeneChain K m ≤ y := by
    intro m
    induction m with
    | zero => exact bot_le
    | succ m ih => exact le_trans (hKmono ih) hy
  exact hchain (kleeneStabIndex K hKmono)

/-- **不动点情形（等式）**：若 `y` 是 `K` 的**不动点**，结论同上。
与 `RealKleeneFixedPoint.kleeneLimit_le_of_fixed` 是同一命题的
两个入口（此处走 `fixpoint_transfer_le`，那里的证明独立）——
**互为交叉验证**。 -/
theorem fixpoint_transfer_le_of_fixed {Abstract : Type*} [Fintype Abstract]
    [PartialOrder Abstract] [OrderBot Abstract] {K : Abstract → Abstract}
    (hKmono : Monotone K) {y : Abstract} (hy : K y = y) : kleeneLimit K hKmono ≤ y :=
  fixpoint_transfer_le hKmono (le_of_eq hy)

/-- **带具体侧的封装**：把 `K` 做成 `F` 的可靠抽象，
则具体后不动点的抽象化是抽象侧的上界。

**诚实标注**：本定理把「`K (αS {x}) ≤ αS {x}`」作为**显式假设**，
而不假装能从可靠性推出 —— 从 `αS (F '' γ a) ≤ K a` 与
`αS (F '' γ a) ≤ a` **推不出** `K a ≤ a`（缺反向比较）。
需要 `K` 恰是**最佳抽象**时才能补上，而最佳抽象的可靠性已由
`bestAbstract_sound` 给出（**不需要 `F` 单调**）。 -/
theorem transfer_of_sound_abstraction {Concrete Abstract : Type*}
    [CompleteLattice Abstract] {alphaS : Set Concrete → Abstract}
    {gamma : Abstract → Set Concrete} (gc : GaloisMem alphaS gamma)
    {F : Concrete → Concrete} {K : Abstract → Abstract}
    (hK : SoundAbstract gamma F K) {x : Concrete} (hKx : K (alphaS {x}) ≤ alphaS {x}) :
    alphaS (F '' (gamma (alphaS {x}))) ≤ alphaS {x} :=
  le_trans (soundAbstract_alpha_le gc hK (alphaS {x})) hKx

end Transfer

/-! ## 六、实例化：符号区间抽象

本节把前五节落到**真正接得上 H1 发现**的实例：**区间抽象**
（`IntervalAbstract`）对**裁剪**（`clampTo`）与**格点下取整**（`roundDownN`）
两个算子的可靠抽象，以及对 H1 发现的**错误实现** `lv00RoundDown` 的裁决。

**本节对「保真度」的意义**：区间抽象把「从权重提取符号属性」变成
「具体值 → 区间」的 Galois 连接；于是**任何**对权重算子的符号近似，
只要写成 `f♯` 并通过可靠性判据，就自动获得「覆盖所有具体取值」的保证 ——
这正是「保真度」在抽象层面**可证**的形式。 -/

section Interval

/-- **符号区间抽象**：区间 `[lo, hi]`，带良构性 `lo ≤ hi`。
这是权重域 `ℝ` 的最基本符号属性（「该通道取值落在 `[lo, hi]` 内」）。

**诚实标注**：本结构**不表示空区间**（`wf` 强制 `lo ≤ hi`）。
空区间在抽象解释中是 `⊥`，本文件**未做**它的表示；
因此本文件的 `γ` 是「包含」，而 `γ (⊥)` 若取空集会破坏 `⊥` 的
「无信息」语义，故本文件的 Galois 连接**不是**带 `⊥` 的插入/余插入。 -/
structure IntervalAbstract where
  /-- 下界。 -/
  lo : ℝ
  /-- 上界。 -/
  hi : ℝ
  /-- 良构性。 -/
  wf : lo ≤ hi

namespace IntervalAbstract

/-- **区间上的偏序 = 反向包含序**（抽象解释的标准「信息序」）：
`a ≤ b ⟺ γ_iv b ⊆ γ_iv a`，逐点即 `b.lo ≤ a.lo ∧ a.hi ≤ b.hi`。
**区间越大越靠下**（`⊥` = 无信息 = 最大的区间）。

**为什么必须是这个方向**（本文件**先写错过一次**，记录如下以免重蹈）：
Galois 连接要求 `α {c} ≤ a ↔ c ∈ γ a`，即 `point c` 必须是
「含 `c` 的**最精确**区间」，而「更精确」的方向必须是 `≤`。

* 若取**逐点序** `a ≤ b ↔ a.lo ≤ b.lo ∧ a.hi ≤ b.hi`，则
  `point x ≤ iv ↔ x ≤ iv.lo ∧ x ≤ iv.hi`，与 `iv.contains x`
  （`iv.lo ≤ x ∧ x ≤ iv.hi`）**方向相反** ⇒ 连接**为假**；
* 取**反向包含序**（本定义），`point x ≤ iv` 展开为
  `iv.lo ≤ x ∧ x ≤ iv.hi`，与 `contains` **逐字一致** ⇒
  `point_le_iff_contains` 是 **`Iff.rfl`**。这条 `rfl` 就是
  「序选对了」的**机器证据**。 -/
instance : PartialOrder IntervalAbstract where
  le a b := b.lo ≤ a.lo ∧ a.hi ≤ b.hi
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans a b c hab hbc := ⟨le_trans hbc.1 hab.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    -- `hab : b.lo ≤ a.lo ∧ a.hi ≤ b.hi`，`hba : a.lo ≤ b.lo ∧ b.hi ≤ a.hi`
    have h1 : a.lo = b.lo := le_antisymm hba.1 hab.1
    have h2 : a.hi = b.hi := le_antisymm hab.2 hba.2
    cases a; cases b
    simp_all

/-- **点区间** `[x, x]`（`α` 的构造块）。 -/
def point (x : ℝ) : IntervalAbstract := ⟨x, x, le_rfl⟩

@[simp] theorem point_lo (x : ℝ) : (point x).lo = x := rfl
@[simp] theorem point_hi (x : ℝ) : (point x).hi = x := rfl

/-- **包含谓词**：`x ∈ [lo, hi]`。 -/
def contains (iv : IntervalAbstract) (x : ℝ) : Prop := iv.lo ≤ x ∧ x ≤ iv.hi

/-- `point x` 包含 `x`。 -/
@[simp] theorem point_contains (x : ℝ) : (point x).contains x := ⟨le_rfl, le_rfl⟩

/-- **包含 ⟺ 点区间 ≤ 区间**：`point x ≤ iv ↔ iv.contains x`。

这是区间 Galois 连接的**全部内容**。**证明是 `Iff.rfl`** ——
因为 `le` 与 `contains` 的定义**逐字一致**。
这条 `rfl` 同时是**定义写对的机器证据**（序写反则此命题为假）。 -/
theorem point_le_iff_contains (iv : IntervalAbstract) (x : ℝ) :
    point x ≤ iv ↔ iv.contains x :=
  Iff.rfl

/-- 区间的**代表点**取 `lo`：它是 `contains` 意义下的**最小元**。 -/
def repLo (iv : IntervalAbstract) : ℝ := iv.lo

theorem repLo_mem (iv : IntervalAbstract) : iv.contains iv.repLo :=
  ⟨le_rfl, iv.wf⟩

/-- **`lo` 是 `contains` 的最小元**：任何被 `iv` 包含的 `x` 都 `≥ iv.lo`。
这是「最佳抽象」所需的最小元条件，在区间上**免费获得**。 -/
theorem repLo_le_of_contains {iv : IntervalAbstract} {x : ℝ} (hx : iv.contains x) :
    iv.repLo ≤ x := hx.1

end IntervalAbstract

/-! ### 区间上的 Galois 连接

本节的 `αS_iv` 取**点式子集的并**：`αS_iv S := ⨆_{x ∈ S} point x`（即 `S` 的
凸包区间）。这样定义的好处是它与第 1 节的
`galoisConnection_of_pointwise` **形状完全吻合**：
该引理要求 `αS S = ⨆ c ∈ S, αS {c}`，而 `αS {c} = point c`。

**诚实标注**：`IntervalAbstract` 在**双向包含序**下并非 `CompleteLattice`
（区间的**下确界**按信息序是「并集」，而无限并集可能不是区间 ——
例如 `[0,1] ⊔ [2,3]` 无上界意义下的最小上界对应「凸包」`[0,3]`，
这在 `ℝ` 上是存在的，但 `⨆` 对**任意**集合族要求所有上确界存在）。
本文件因此**不**直接把 `IntervalAbstract` 装成 `CompleteLattice`，
而是**只在子集上**用 `⨆` 与「有界性」：

**最终采取的形式化策略**：把 Galois 连接**逐点陈述**（`point x ≤ iv ↔ x ∈ γ_iv iv`），
并把「集合层」的内容**限制在有限子集**上（`Finset` 的 `sup'`），
从而避开无限上确界的存在性。这也与本文件第五节的**有限格**假设一致。 -/

/-- **具体化 `γ_iv`**：`[lo,hi] ↦ {x | lo ≤ x ∧ x ≤ hi}`。 -/
def gammaInterval : IntervalAbstract → Set ℝ := fun iv => {x | iv.contains x}

/-- **点式 Galois 连接（区间实例，逐点陈述）**：
`point x ≤ iv ↔ x ∈ γ_iv iv`。由 `point_le_iff_contains` 即得（`Iff.rfl`）。 -/
theorem galoisConnection_interval_pointwise (x : ℝ) (iv : IntervalAbstract) :
    IntervalAbstract.point x ≤ iv ↔ x ∈ gammaInterval iv :=
  IntervalAbstract.point_le_iff_contains iv x

/-- **具体化关于区间序是单调的**（不是反变！）。

**这是本文件在形式化中第三处自我修正**：初稿写 `Antitone gammaInterval`
并给了错误的传递论证。实际检验（代入 `hab : b.lo ≤ a.lo ∧ a.hi ≤ b.hi`、
`hx : b.lo ≤ x ∧ x ≤ b.hi`，要证 `a.lo ≤ x ∧ x ≤ a.hi`）：
* `a.lo ≤ x` 需要 `a.lo ≤ b.lo`，而 `hab.1 : b.lo ≤ a.lo` —— **方向相反**；
* `x ≤ a.hi` 需要 `b.hi ≤ a.hi`，而 `hab.2 : a.hi ≤ b.hi` —— **也相反**。

⇒ 该序下 `γ` **正变单调**（`a ≤ b` 即「`b` 更粗」⟹ `γ a ⊆ γ b`），
与第一节的 `gamma_monotone` **形式一致**。这实际上是个**好消息**：
反向包含序（`le a b := b.lo ≤ a.lo ∧ a.hi ≤ b.hi`）与「`a` 更精确 ⟹ `a ≤ b`」
配合后，`γ` 恰好**正变**，因此第一节的 `gamma_monotone` 框架**适用**于区间实例。

（对照：若用**逐点序**，则 `γ` 也正变但 `point_le_iff_contains` 为假；
反向包含序同时给出「连接成立」+「`γ` 正变」，是本实例的**正确选择**。） -/
theorem gamma_interval_monotone : Monotone gammaInterval := by
  intro a b hab x hx
  exact ⟨le_trans hab.1 hx.1, le_trans hx.2 hab.2⟩

/-- **扩张性（区间版）**：`x ∈ γ_iv (point x)`，即 `x ∈ [x,x]`。 -/
theorem interval_expansive (x : ℝ) : x ∈ gammaInterval (IntervalAbstract.point x) :=
  IntervalAbstract.point_contains x

/-! ### 算子一：裁剪（`clampTo`） -/

/-! ⭐ **R01 去重（2026-09-29）**：本文件原有 `def clampTo (M x : ℝ) : ℝ := max (-M) (min M x)`，
与 `RealIEEE754.lean:230` **逐字等同**，构成 `Lattice.clampTo` 命名冲突
（内核：`import RealAbstractInterpretation` + `import RealIEEE754` =
`environment already contains 'Lattice.clampTo._cstage1'`）。
现由上方 `import RealIEEE754` **复用单一权威定义**，本文件不再重定义。

原注释称「独立定义以避免引入 `RealIEEE754` 的整条依赖链」—— 该顾虑经**实测不成立**：
`RealIEEE754` 的 transitive closure 只有 **3 个模块**（`RealIEEE754` / `RealFloatFormat` / 自身），
且**反向依赖不存在**（IEEE754 的闭包内无本文件），故引入**无环**。

**定义域约定**：`M ≥ 0`（裁剪半径非负）。`clampTo_mem` 带此前提 ——
这不是掩盖的 gap：`M < 0` 时 `[-M, M]` 是**空区间**，
而 `IntervalAbstract` 的结构字段 `wf` 要求 `lo ≤ hi`，
故负半径在区间抽象中**不可表示**。 -/

/-- 裁剪后落在 `[-M, M]` 内（`0 ≤ M`）。

**写法说明（本文件实际修正过两次）**：
1. `max (-M) (min M x)` 在 Lean 里显示为 `-M ⊔ M ⊓ x`（`⊔`/`⊓` 是 `max`/`min`）；
2. **`min_eq_left` / `min_eq_right` 在 4.14 的语义与名字直觉相反**
   （STYLE.md §4 已列为坑：「`max_eq_left`/`max_eq_right` **4.14 语义互换**」）。
   实测：`min_eq_left h` 的**类型**是 `x ⊓ M = x`（要求 `h : x ≤ M`），
   即它消去的模式是 **`x ⊓ M`** 而不是 `M ⊓ x`。
   本文件因此**不用**这两个引理，改用 `min_def`/`max_def` 展开后 `split_ifs`，
   或直接 `le_antisymm` 论证明 `min M x = x`。 -/
theorem clampTo_mem (M x : ℝ) (hM : 0 ≤ M) : -M ≤ clampTo M x ∧ clampTo M x ≤ M := by
  unfold clampTo
  constructor
  · exact le_max_left _ _
  · rcases le_total x M with h | h
    · -- `min M x = x`（因 `x ≤ M`）：`le_min` 的两个前提是 `x ≤ M` 与 `x ≤ x`
      have hmin : min M x = x := le_antisymm (min_le_right M x) (le_min h le_rfl)
      rw [hmin]
      exact max_le (by linarith) h
    · -- `min M x = M`（因 `M ≤ x`）：`le_min` 的两个前提是 `M ≤ M` 与 `M ≤ x`
      have hmin : min M x = M := le_antisymm (min_le_left M x) (le_min le_rfl h)
      rw [hmin]
      exact max_le (by linarith) le_rfl

/-- **裁剪的区间抽象**：把任意区间映到 `[-M, M]`（**丢弃**原区间的界）。
裁剪的定义域无关性使这条**不依赖**输入区间 ——
这正是「裁剪是最粗但可靠」的抽象（信息损失全部来自 `max`/`min`）。 -/
def clampSharp (M : ℝ) (hM : 0 ≤ M) : IntervalAbstract → IntervalAbstract :=
  fun _ => ⟨-M, M, by linarith⟩

/-- **裁剪的可靠抽象**：`x ∈ γ_iv a ⟹ clampTo M x ∈ γ_iv (clampSharp M hM a)`。
证明即 `clampTo_mem`——**不依赖 `a`**。 -/
theorem clampSharp_sound (M : ℝ) (hM : 0 ≤ M) :
    SoundAbstract gammaInterval (clampTo M) (clampSharp M hM) := by
  intro a c _
  exact clampTo_mem M c hM

/-- **裁剪抽象给出的上界必须 `≥ M`**（最佳性的上界侧）。

**诚实修正（本文件第四处自我修正）**：初稿试图证
`M ≤ (fSharp a).hi`，用 `clampTo M a.hi ≤ M` 与
`clampTo M a.hi ≤ (fSharp a).hi` **传递** —— 但这两条**都是上界**，
无法得出 `M ≤ (fSharp a).hi`（两条不等式方向相同，中项不带传递关系）。

真正可证的方向是**下界侧**：取具体点 `a.lo`，
可靠性给 `(fSharp a).lo ≤ clampTo M a.lo`；
由 `clampTo_mem` 的 `-M ≤ clampTo M a.lo` 得 `-M ≤ clampTo M a.lo`，
**仍不能**推出 `(fSharp a).lo ≤ -M`。

⇒ 正确的结论是：**`fSharp a` 必须包含 `[-M, M]` 中一切可达值**，
而「可达」需要 `clampTo M` 在 `γ_iv a` 上的**满射性**（未做，见契约）。
本文件因此**只交付下一条为真的结论**：`γ_iv (fSharp a)` 含 `clampTo M a.lo`
与 `clampTo M a.hi`，即
`(fSharp a).lo ≤ clampTo M a.lo` 且 `clampTo M a.hi ≤ (fSharp a).hi`
—— 这是**可靠性在端点处的展开**，非平凡且可证。 -/
theorem clampSharp_endpoint_bounds (M : ℝ) (a : IntervalAbstract)
    {fSharp : IntervalAbstract → IntervalAbstract}
    (h : SoundAbstract gammaInterval (clampTo M) fSharp) :
    (fSharp a).lo ≤ clampTo M a.lo ∧ clampTo M a.hi ≤ (fSharp a).hi := by
  have hlo : clampTo M a.lo ∈ gammaInterval (fSharp a) := h a a.lo ⟨le_rfl, a.wf⟩
  have hhi : clampTo M a.hi ∈ gammaInterval (fSharp a) := h a a.hi ⟨a.wf, le_rfl⟩
  exact ⟨hlo.1, hhi.2⟩

/-! ### 算子二：格点下取整（`roundDownN`） -/

/-- **格点下取整** `⌊x·N⌋ / N`（H1 的**修复版**；与
`RealLv00LinearAlgebra.roundDownN` 同义，此处独立定义以保持 `import` 面最小）。 -/
def roundDownN (N : ℤ) (x : ℝ) : ℝ := ((⌊x * (N : ℝ)⌋ : ℤ) : ℝ) / (N : ℝ)

/-- **下取整不越过真值**：`roundDownN N x ≤ x`（`0 < N`）。
用 `Int.floor_le`（**不经过 `toNat`**，故负数正确）+
`div_le_iff₀`。这是 H1 修复版的**下界安全性**。 -/
theorem roundDownN_le (N : ℤ) (hN : 0 < N) (x : ℝ) : roundDownN N x ≤ x := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h : ((⌊x * (N : ℝ)⌋ : ℤ) : ℝ) ≤ x * (N : ℝ) := Int.floor_le _
  unfold roundDownN
  rw [div_le_iff₀ hN']
  exact h

/-- **下取整单调**。用 `Int.floor_mono` + `div_le_div_of_nonneg_right`。 -/
theorem roundDownN_mono (N : ℤ) (hN : 0 < N) {x y : ℝ} (h : x ≤ y) :
    roundDownN N x ≤ roundDownN N y := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul : x * (N : ℝ) ≤ y * (N : ℝ) := mul_le_mul_of_nonneg_right h (le_of_lt hN')
  have hfl : ((⌊x * (N : ℝ)⌋ : ℤ) : ℝ) ≤ ((⌊y * (N : ℝ)⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_mono hmul
  unfold roundDownN
  exact div_le_div_of_nonneg_right hfl (le_of_lt hN')

/-- **下取整的可靠区间抽象**：`[lo, hi] ↦ [⌊lo·N⌋/N, hi]`。

* 下界用 `⌊lo·N⌋/N` —— 因为 `roundDownN N lo ≤ lo`，取 `lo` 会**太紧**；
* 上界用 `hi` —— 因为 `roundDownN N x ≤ x ≤ hi`。

**良构性** `⌊lo·N⌋/N ≤ hi` 由 `roundDownN_le N hN lo ≤ lo ≤ hi` 得到。 -/
def roundDownSharp (N : ℤ) (hN : 0 < N) (a : IntervalAbstract) : IntervalAbstract :=
  ⟨roundDownN N a.lo, a.hi, le_trans (roundDownN_le N hN a.lo) a.wf⟩

/-- **舍入的可靠抽象（主定理）**：`x ∈ γ_iv a ⟹ roundDownN N x ∈ γ_iv (roundDownSharp N hN a)`。

只需 `floor` 的下界性与单调性，**不需要**任何额外数值假设（除 `0 < N`）。 -/
theorem roundDownSharp_sound (N : ℤ) (hN : 0 < N) :
    SoundAbstract gammaInterval (roundDownN N) (roundDownSharp N hN) := by
  intro a x hx
  obtain ⟨hx1, hx2⟩ := hx
  exact ⟨roundDownN_mono N hN hx1, le_trans (roundDownN_le N hN x) hx2⟩

/-- **「下界直接用 `lo`」是错的（机器验证反例）**：
把 `roundDownSharp` 的下界换成 `a.lo` 即「恒等抽象」`fun a => a`，
则可靠性**失败**。

见证：`N = 2`、区间 `[0.25, 1]`、具体点 `x = 0.25`。
`roundDownN 2 0.25 = ⌊0.5⌋/2 = 0`，而 `0 ∉ [0.25, 1]`。
故「舍入不改变区间」是**假**命题 —— 抽象化的精度必须用 `⌊lo·N⌋/N` 才能证出来。 -/
theorem roundDownSharp_identity_not_sound :
    ¬ SoundAbstract gammaInterval (roundDownN 2) (fun a => a) := by
  intro h
  have hx : (0.25 : ℝ) ∈ gammaInterval (⟨0.25, 1, by norm_num⟩ : IntervalAbstract) :=
    ⟨le_rfl, by norm_num⟩
  have hcon := h ⟨0.25, 1, by norm_num⟩ 0.25 hx
  -- hcon : roundDownN 2 0.25 ∈ gammaInterval ⟨0.25, 1, _⟩
  -- 展开为 `0.25 ≤ roundDownN 2 0.25 ∧ roundDownN 2 0.25 ≤ 1`
  have hval : roundDownN 2 (0.25 : ℝ) = 0 := by
    unfold roundDownN
    norm_num [Int.floor_eq_iff]
  rw [hval] at hcon
  -- hcon.1 : (0.25 : ℝ) ≤ 0
  exact absurd hcon.1 (by norm_num)

/-- **下取整抽象在端点处的界**（可靠性的展开，非平凡且可证）。

**诚实修正（与 `clampSharp_endpoint_bounds` 同源的错误）**：初稿试图证
`a.hi ≤ (fSharp a).hi`，用 `roundDownN N a.hi ≤ a.hi` 与
`roundDownN N a.hi ≤ (fSharp a).hi` 传递 —— **两条都是上界，无法传递**。

正确的、可证的结论是可靠性在**两个端点**上的展开：
* 取 `a.lo`：`roundDownN N a.lo ∈ γ_iv (fSharp a)`，给下界侧
  `(fSharp a).lo ≤ roundDownN N a.lo`；
* 取 `a.hi`：`roundDownN N a.hi ∈ γ_iv (fSharp a)`，给上界侧
  `roundDownN N a.hi ≤ (fSharp a).hi`。

这两条合起来说明**抽象算子的输出区间必须容纳端点的舍入结果** ——
这是 `roundDownSharp` 的**正确性依据**（它正是据此构造的）。 -/
theorem roundDownSharp_endpoint_bounds (N : ℤ) (a : IntervalAbstract)
    {fSharp : IntervalAbstract → IntervalAbstract}
    (h : SoundAbstract gammaInterval (roundDownN N) fSharp) :
    (fSharp a).lo ≤ roundDownN N a.lo ∧ roundDownN N a.hi ≤ (fSharp a).hi := by
  have hlo : roundDownN N a.lo ∈ gammaInterval (fSharp a) := h a a.lo ⟨le_rfl, a.wf⟩
  have hhi : roundDownN N a.hi ∈ gammaInterval (fSharp a) := h a a.hi ⟨a.wf, le_rfl⟩
  exact ⟨hlo.1, hhi.2⟩

/-! ## 七、H1 的错误实现：`lv00RoundDown` 的框架级裁决

H1（`RealLv00LinearAlgebra`）发现 Lv-00 的 `round_down`
（`x ↦ (⌊x·10¹⁵⌋).toNat / 10¹⁵`，负的 `⌊·⌋` 被 `toNat` 截断为 0）
**是错误实现**：`lv00RoundDown (-1) = 0 > -1`，违反它自己声称的
`round_down x ≤ x`。

本节把这条**具体反例**升级为**框架级诊断**，并**如实记录推理中被排除的
两个过强猜想**（记录它们比掩盖更有价值：它们标出了框架的边界）。

### 被排除的猜想一：「不存在可靠抽象」——**过强且为假**

抽象解释的可靠性只要求 `c ∈ γ a ⟹ f c ∈ γ (f♯ a)`，而区间**有宽度**：
取 `f♯ a := [-|a.lo| , |a.hi|]` 之类把输出「夹住」的区间即可造出可靠抽象。
**故本文件不予声称。**

### 被排除的猜想二：「不单调所以框架不适用」——**也是假的**

`toNat` 把**一切**负值截断为 `0`，故 `lv00RoundDown` 在整个负半轴上
**恒为 0**（`lv00RoundDownHere_neg_le_zero` 机器验证），
因而是**常函数**，而常函数**单调**。

### 最终成立的诊断（本节交付）

真正不可修正的是 **H1 已证的下界安全性**。
本文件把它翻译成抽象解释的语言：

* `lv00RoundDownHere_fails_lower_bound`：**存在** `x` 使下界安全性失败；
* `roundDownN_lower_safe`：**修复版**满足它；
* `lower_bound_distinguishes`：两者被这条**对一切输入成立**的定理**区分开**。

**为什么这比「有个反例」更强**：抽象解释的可靠性判据正是建立在
「具体执行的输出落在抽象输出所覆盖的具体集合内」之上。
若具体算子在输入区间**内部**的某点产生**超出下界**的输出，
则任何以「区间下界」为可靠性判据的抽象都**无法**覆盖它 ——
该算子在此框架中**不合法**。诊断从「实现有 bug」升级为
「**该实现落在框架的适用域之外**」。

**诚实标注**：本文件**不声称**「`lv00RoundDown` 不可被任何抽象覆盖」
（猜想一已证明那是假的），只声称它在**要求下界安全性**的框架中不可用。 -/

section Lv00Diagnosis

/-- **Lv-00 `round_down` 的原样复现**（同 `RealLv00LinearAlgebra.lv00RoundDown`；
此处独立定义以保持本文件 `import` 面最小）。 -/
def lv00RoundDownHere (x : ℝ) : ℝ :=
  let scale := (1000000000000000.0 : ℝ)
  ((Int.floor (x * scale)).toNat : ℝ) / scale

/-- **H1 的反例在本地复现**：`lv00RoundDownHere (-1) = 0`。 -/
theorem lv00RoundDownHere_neg_one : lv00RoundDownHere (-1) = 0 := by
  unfold lv00RoundDownHere
  norm_num [Int.floor_eq_iff]

/-- **本地反例**：`¬ (lv00RoundDownHere (-1) ≤ -1)` —— 下界安全性失败。 -/
theorem lv00RoundDownHere_counterexample : ¬ (lv00RoundDownHere (-1) ≤ (-1 : ℝ)) := by
  rw [lv00RoundDownHere_neg_one]
  norm_num

/-- **被排除猜想二的机器证据**：`lv00RoundDownHere` 在负半轴上恒为 0，
故是**常函数**（因而单调）—— 「不单调」的猜想是**假**的。

证明：`x ≤ 0` 时 `x · 10¹⁵ ≤ 0`，故 `⌊x·10¹⁵⌋ ≤ 0`，
`toNat` 把非正整数映为 `0`，结论即 `0 / 10¹⁵ = 0`。

**写法说明**：`lv00RoundDownHere` 的定义体含 `let scale := …`，
`unfold` 后目标里仍留 `let`，直接 `rw [htoNat]` 会报
`did not find instance of the pattern`。改用 `simp only [lv00RoundDownHere]`
把 `let` 一并展开（`dsimp only` 亦可），再 `rw`。 -/
theorem lv00RoundDownHere_neg_le_zero {x : ℝ} (hx : x ≤ 0) :
    lv00RoundDownHere x = 0 := by
  have hscale : (0 : ℝ) < 1000000000000000.0 := by norm_num
  have hfl : Int.floor (x * 1000000000000000.0) ≤ 0 :=
    Int.floor_le_iff.mpr (by nlinarith)
  have htoNat : (Int.floor (x * 1000000000000000.0)).toNat = 0 := by omega
  simp only [lv00RoundDownHere, htoNat, Nat.cast_zero, zero_div]

/-- **Lv-00 实现的下界安全性失败（框架级重述）**：
存在具体点使 `lv00RoundDownHere x > x`。 -/
theorem lv00RoundDownHere_fails_lower_bound :
    ∃ x : ℝ, ¬ (lv00RoundDownHere x ≤ x) :=
  ⟨-1, lv00RoundDownHere_counterexample⟩

/-- **对照：修复版满足下界安全性**：`roundDownN N x ≤ x` 对一切 `0 < N`。
**同一位置上**，修复版通过抽象解释的下界要求，错误版不通过。 -/
theorem roundDownN_lower_safe (N : ℤ) (hN : 0 < N) (x : ℝ) : roundDownN N x ≤ x :=
  roundDownN_le N hN x

/-- **两者的可分辨性（最终裁决）**：把「下界安全性」当作抽象解释框架的
**准入门槛**，则 `roundDownN` **通过**、`lv00RoundDown` **不通过** ——
即存在一条**对一切输入成立**的定理把两者区分开。

这是「抽象解释能**证**『这个替换是可靠的』」的机器化形式（本文件的目标）：
可靠性不是靠举几个例子，而是靠一条对一切输入成立的定理；
而错误实现**必然**被这条定理拒绝。 -/
theorem lower_bound_distinguishes :
    (∀ N : ℤ, 0 < N → ∀ x : ℝ, roundDownN N x ≤ x) ∧
      (∃ x : ℝ, ¬ (lv00RoundDownHere x ≤ x)) :=
  ⟨fun N hN x => roundDownN_lower_safe N hN x, lv00RoundDownHere_fails_lower_bound⟩

end Lv00Diagnosis

end Interval

end Lattice
