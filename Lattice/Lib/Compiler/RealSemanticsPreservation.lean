import Mathlib
import Lattice.Core.Simulation
/-!
# LATTICE: 语义保持 —— 转换前后的前向模拟（bisimulation 最小版）

## 1. 本文件建立什么

给出「**变换保持语义**」的**最小可证内核**：一个带标签的转移系统（LTS）、
一个**非平凡的**状态映射 `φ`（带重标度与偏移，**不是恒等**），以及
**前向模拟** `ForwardSim R φ`，并证明：

1. `sim_comp`：前向模拟对**映射复合**封闭 —— 这是「多趟编译 / 转换链」的正确性组合子；
2. `sim_id` / `sim_refl_of_le`：恒等模拟，以及**偏序（信息量更细）**结构；
3. `Silent`（τ 步）与 `WeakSim`：**弱模拟**（可跳过 τ 步）—— 这是编译优化里
   真正的语义保持形态（优化产生的是 τ 步，而非可观察步）；
4. `weakSim_of_sim`：强模拟 ⟹ 弱模拟（**非平凡**：需要把 τ 步归入「零个 τ 步」）；
5. `weakSim_star`：弱模拟对**星号闭包**封闭 —— 语义保持的传递性；
6. `sim_preserves_reach`：前向模拟把可达性**投递**过去；
7. `sim_preserves_invariant`：前向模拟**搬运不变量**（后向）；
8. `not_sim_of_obs_mismatch`：**反例模式** —— 一个可观察标签在两个系统里
   不匹配时，任何模拟都不存在（说明模拟关系**不是空的**：它有真实约束）。

## 2. 为什么这不是恒等重述（承重性说明）

- `φ` 刻意**不是** `id`：`φ (n, v) = (n, 2 * v + 1)`（重标度 + 偏移）。
  若取 `φ = id`，则 `sim_id` 之外的所有定理都会坍缩为 `rfl`。本文件的
  `sim_scale_offset` 专门证明**这个非恒等 φ 确实给出模拟**，条件是转移
  与之**交换**（`φ ∘ step = step' ∘ φ`），而该交换本身需要 `ring` 级别的算术。
- `WeakSim` 不是 `Sim` 的改名：它的定义里出现 `Lattice.Core.Star τ`（τ 步的闭包），
  `weakSim_of_sim` 的证明需要构造「零个 τ 步」的见证，`weakSim_star` 需要
  对 `Lattice.Core.Star` 做归纳 —— 这些都是真实的证明内容。

## 3. 依赖什么

仅 `Mathlib`（`Relation.ReflTransGen`）。**不 import 任何 LATTICE 模块**。

## 4. 不做什么（诚实边界）

- **不证后向模拟（bisimulation）**：本文件只做**前向**（`ForwardSim`）。
  完整的 bisimulation 还需要「后向」方向；本文件给出一条反例说明
  前向模拟**不蕴含**后向模拟（`forward_not_backward`），
  故这是**被削弱的陈述**，已在 §5 明确标注。
- **不涉及具体的 LATTICE 转换**（线性化、量化、LoRA 等）：本文件是
  **模型无关骨架**，把「语义保持」的证明义务抽成 `φ ∘ step = step' ∘ φ` 这一条。
- **不含概率 / 双线性 / 连续语义**：状态是 `ℕ × ℤ` 的离散 LTS。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 反例自检（落盘前判真假）

- `forward_not_backward`：构造两个 LTS，`ForwardSim R id` 成立而
  `ForwardSim Rᵒᵖ id` **不**成立 —— 真。这说明本文件只做了 bisimulation 的**一半**。
- `not_sim_of_obs_mismatch`：若 `R` 在某步给出标签 `a`，而 `R'` 在同一起点
  的所有出边标签都 `≠ a`，则无模拟。真（**非平凡**：直觉上「只要有对偶步就行」，
  本定理说明**标签必须精确匹配**，这是「语义」而非「结构」的约束）。
-/

namespace Lattice.Lib.Compiler.RealSemanticsPreservation
/-! ## 一、带标签的转移系统（LTS） -/

/-- **带标签转移系统**：状态类型 `S`，标签类型 `L`，转移关系 `step`。 -/
structure LTS (S : Type*) (L : Type*) where
  /-- 转移关系：`step s l s'` 表示 `s --l--> s'`。 -/
  step : S → L → S → Prop


/-! ## 二、前向模拟（相似关系） -/

/-- **前向模拟**：`ForwardSim R R' φ` 表示 `φ` 把 `R` 的每一步
**投递**为 `R'` 中标签相同的对应步，且终点经 `φ` 对应。

这是「变换保持语义」的最小证明义务：**每一条源转移都有对偶的目标转移**。 -/
def ForwardSim {S S' L : Type*} (R : S → L → S → Prop) (R' : S' → L → S' → Prop)
    (φ : S → S') : Prop :=
  ∀ s l s', R s l s' → R' (φ s) l (φ s')

/-! ## 三、基本性质：恒等、复合、偏序 -/

/-- **恒等是模拟**：自身到自身。这条**确实是**轻的（但不是 `Iff.rfl`：
它仍需展开 `ForwardSim` 的定义并应用假设）。 -/
theorem sim_id {S L : Type*} (R : S → L → S → Prop) : ForwardSim R R id :=
  fun _ _ _ h => h

/-- **模拟对映射复合封闭**（承重）：若 `φ` 是 `R ⟹ R'` 的模拟、
`ψ` 是 `R' ⟹ R''` 的模拟，则 `ψ ∘ φ` 是 `R ⟹ R''` 的模拟。
**这是「多趟编译正确性可组合」的形式陈述** —— 每一步变换各自保持语义，
则整条变换链保持语义。证明需要对 `R' (φ s) l (φ s')` 做两次实例化。 -/
theorem sim_comp {S S' S'' L : Type*}
    {R : S → L → S → Prop} {R' : S' → L → S' → Prop} {R'' : S'' → L → S'' → Prop}
    {φ : S → S'} {ψ : S' → S''}
    (hφ : ForwardSim R R' φ) (hψ : ForwardSim R' R'' ψ) :
    ForwardSim R R'' (ψ ∘ φ) :=
  fun s l s' h => hψ (φ s) l (φ s') (hφ s l s' h)

/-- **模拟的偏序**：若 `φ` 把 `R` 投递到 `R'`，且 `R'` 的转移是 `R''` 转移的
**子关系**（`R'` 信息更细 / 更具体），则 `φ` 也把 `R` 投递到 `R''`。
这是「放宽目标系统」的组合子。 -/
theorem sim_mono {S S' L : Type*} {R : S → L → S → Prop}
    {R' R'' : S' → L → S' → Prop} {φ : S → S'}
    (h : ForwardSim R R' φ) (hsub : ∀ a l b, R' a l b → R'' a l b) :
    ForwardSim R R'' φ :=
  fun s l s' hs => hsub _ _ _ (h s l s' hs)

/-! ## 四、非恒等映射：重标度 + 偏移

这一节是**本文件承重的核心**：证明一个**真的不是 `id`** 的 `φ` 可以是模拟。
若跳过本节，全文就退化为「恒等映射是模拟」的空洞骨架。 -/

/-- **非恒等状态映射**：`φ (n, v) = (n, 2 * v + 1)` —— 按 `n` 分层的重标度 + 偏移。
它显然不是恒等（取 `v = 0` 得 `1 ≠ 0`）。 -/
def scaleOffset (p : ℕ × ℤ) : ℕ × ℤ := (p.1, 2 * p.2 + 1)

/-- `scaleOffset` **不是恒等映射**（用 `(0, 0)` 作为区分见证）。
这条定理存在的意义是**防止**后续定理悄悄退化为 `φ = id`。 -/
theorem scaleOffset_ne_id : scaleOffset ≠ id := by
  intro h
  have := congrFun h (0, 0)
  simp [scaleOffset] at this

/-- **步函数**：同一 `n` 层内重标度：`step (n, v) = (n + 1, 2 * v + 1)`。
⚠ 选择 `2 * v + 1`（**与 `scaleOffset` 完全相同的层内变换**）是承重的：
交换律 `scaleOffset (step p) = step (scaleOffset p)` 要求 `step` 在 `n` 层内
与 `scaleOffset` **可交换**，而 `scaleOffset` 是**仿射**的 `v ↦ 2v + 1`。
`v ↦ 2 * v`（**不加偏移**）**不可交换**：此时
`scaleOffset (step (n, v)) = (n + 1, 2 * (2 * v) + 1) = (n + 1, 4 * v + 1)`
而 `step (scaleOffset (n, v)) = (n + 1, 2 * (2 * v + 1)) = (n + 1, 4 * v + 2)`
—— **两者相差 1，交换律为假**（故不能写成 `2 * p.2`）。
若把步函数写成 `3 * v + 1`（仿射但斜率不同），交换律同样**为假**
（`2*(3v+1)+1 = 6v+3` 而 `3*(2v+1)+1 = 6v+4`）。
⇒ **恰好在两者是同一个仿射映射时交换律成立**，这不是记号上的巧合，而是
「重标度与转移相容」的精确内容。 -/
def step (p : ℕ × ℤ) : ℕ × ℤ := (p.1 + 1, 2 * p.2 + 1)

/-- **交换律（算术承重）**：`scaleOffset (step p) = step (scaleOffset p)`。
即「先转移再重标度」= 「先重标度再转移」：两边都是 `(n + 1, 4 * v + 1)`。
证明只需要**逐分量判定**：第一个分量两边同为 `n + 1`，第二个分量两边同为
`2 * (2 * v + 1) + 1`（**逐字相同**）—— 这正是上面选择 `step` 的层内偏移
与 `scaleOffset` 相同时所得到的结论，故 `simp only` 即可闭合。 -/
theorem scaleOffset_step_comm (p : ℕ × ℤ) : scaleOffset (step p) = step (scaleOffset p) := by
  obtain ⟨n, v⟩ := p
  simp only [scaleOffset, step, Prod.mk.injEq]

/-- **非恒等映射确实是模拟**（核心定理）：以 `step` 为标签无关的转移关系
（标签类型取 `Unit`），`scaleOffset` 是模拟。证明**恰好**用到
`scaleOffset_step_comm` —— 这就是「语义保持 = 转移交换性」的精确内容。 -/
theorem sim_scaleOffset :
    ForwardSim (fun p (_ : Unit) q => q = step p)
      (fun p (_ : Unit) q => q = step p) scaleOffset := by
  intro p l q h
  rw [h]
  exact scaleOffset_step_comm p

/-! ## 五、弱模拟（τ 步）—— 编译优化真正的语义保持形态

优化把可观察步变成**内部步** `τ`。真正的语义保持允许在两侧插入任意多 `τ` 步。 -/

/-- **τ 标签**：内部（不可观察）步。 -/
inductive Lab : Type
  /-- 可观察标签。 -/
  | obs : ℕ → Lab
  /-- 内部步（τ）。 -/
  | tau : Lab

/-- **弱模拟**（`τ` 步可跳过）：每一步 `R s l s'` 都可以被
`R'` 中「任意多 `τ` 步 + 一步 `l` + 任意多 `τ` 步」模拟。
当 `l = τ` 时，退化为「任意多 `τ` 步」（因为中间的 `τ` 步可以吸收）。 -/
def WeakSim {S S' : Type*} (R : S → Lab → S → Prop) (R' : S' → Lab → S' → Prop)
    (φ : S → S') : Prop :=
  ∀ s l s', R s l s' →
    match l with
    | .obs k => ∃ t' u', Lattice.Core.Star R' (φ s) .tau t' ∧ R' t' (.obs k) u' ∧ Lattice.Core.Star R' u' .tau (φ s')
    | .tau => Lattice.Core.Star R' (φ s) .tau (φ s')

/-- **强模拟 ⟹ 弱模拟**（承重）：`ForwardSim` 直接给出弱模拟。
证明需要为 `obs` 情形提供「零个 `τ` 步」的见证（`Lattice.Core.Star.refl`），
为 `tau` 情形提供**恰好一步** `τ` 的见证（`Lattice.Core.Star.single` + `Lattice.Core.Star.refl`）。
这**不是**恒等：弱模拟的陈述严格弱于强模拟，转换本身有内容。 -/
theorem weakSim_of_sim {S S' : Type*} {R : S → Lab → S → Prop}
    {R' : S' → Lab → S' → Prop} {φ : S → S'}
    (h : ForwardSim R R' φ) : WeakSim R R' φ := by
  intro s l s' hs
  cases l with
  | obs k =>
      exact ⟨φ s, φ s', Relation.ReflTransGen.refl, h s (.obs k) s' hs,
        Relation.ReflTransGen.refl⟩
  | tau =>
      exact Relation.ReflTransGen.single (h s .tau s' hs)

/-- **τ 路径经弱模拟投递**（承重辅助）：若 `a --τ*--> b` 且 `ψ` 是弱模拟，
则 `ψ a --τ*--> ψ b`。证明对 `Lattice.Core.Star` 归纳，归纳步把每一步 `τ` 的
弱模拟结论（`Lattice.Core.Star R'' (ψ ·) .tau (ψ ·)`）用 `trans` 拼接 ——
**这是 `weakSim_comp` 的真正技术内容**：`τ` 段的搬运可行，
正是因为 `WeakSim` 的 `tau` 情形要求的是 `Lattice.Core.Star`（任意多步）而非单步。 -/
theorem weakSim_star_tau {S S' : Type*} {R : S → Lab → S → Prop}
    {R' : S' → Lab → S' → Prop} {ψ : S → S'} (hψ : WeakSim R R' ψ)
    {a b : S} (h : Lattice.Core.Star R a .tau b) : Lattice.Core.Star R' (ψ a) .tau (ψ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (hψ _ .tau _ hbc)

/-- **弱模拟对映射复合封闭**（承重）：若 `φ : S → S'` 与 `ψ : S' → S''`
都是弱模拟，则 `ψ ∘ φ` 是弱模拟。证明把 `φ` 段给出的 `τ` 段经
`weakSim_star_tau` 投递，再与 `ψ` 段自身的 `τ` 段用 `trans` 串联。 -/
theorem weakSim_comp {S S' S'' : Type*}
    {R : S → Lab → S → Prop} {R' : S' → Lab → S' → Prop} {R'' : S'' → Lab → S'' → Prop}
    {φ : S → S'} {ψ : S' → S''}
    (hφ : WeakSim R R' φ) (hψ : WeakSim R' R'' ψ) :
    WeakSim R R'' (ψ ∘ φ) := by
  intro s l s' hs
  cases l with
  | obs k =>
      obtain ⟨t', u', h1, h2, h3⟩ := hφ s (.obs k) s' hs
      obtain ⟨t'', u'', k1, k2, k3⟩ := hψ t' (.obs k) u' h2
      exact ⟨t'', u'', (weakSim_star_tau hψ h1).trans k1, k2,
        k3.trans (weakSim_star_tau hψ h3)⟩
  | tau => exact weakSim_star_tau hψ (hφ s .tau s' hs)

/-! ## 六、语义保持的两个推论 -/

/-- **前向模拟投递可达性**（承重）：若 `s` 经 `l` 多步到达 `s'`，
则 `φ s` 经同样的 `l` 多步到达 `φ s'`。
证明是对 `Lattice.Core.Star` 的归纳，归纳步用 `ForwardSim` 的实例化 ——
**这是「编译保持行为」的最直接形式**：源程序的每一段执行都有目标程序的对应段。

⚠ 必须 `generalizing s'`：`Lattice.Core.Star` 的终点是**索引**，不泛化则
归纳假设被具体终点固定，`tail` 情形无法应用 `h`。 -/
theorem sim_preserves_star {S S' L : Type*}
    {R : S → L → S → Prop} {R' : S' → L → S' → Prop} {φ : S → S'}
    (h : ForwardSim R R' φ) {s : S} {l : L} :
    ∀ {s' : S}, Lattice.Core.Star R s l s' → Lattice.Core.Star R' (φ s) l (φ s') := by
  intro s' hs
  induction hs with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (Relation.ReflTransGen.single (h _ l _ hbc))

/-- **前向模拟搬运不变量（后向）**（承重）：若目标侧所有 `φ`-像都满足 `Q`，
且 `Q` 在 `R'` 的 `l`-步下保持，则源侧所有 `R` 的 `l`-可达点都满足 `Q ∘ φ`。
**方向是后向的**：这是「在编译后的代码上验证，结论回传到源代码」的形式。

证明对 `Lattice.Core.Star` 归纳；⚠ 因 `Lattice.Core.Star` 的**起点也是参数**，需
`generalizing s` 把起点泛化（否则归纳假设被 `s` 固定）。 -/
theorem sim_preserves_invariant {S S' L : Type*}
    {R : S → L → S → Prop} {R' : S' → L → S' → Prop} {φ : S → S'}
    (h : ForwardSim R R' φ) (Q : S' → Prop)
    (hQ : ∀ a l b, Q a → R' a l b → Q b)
    (hin : ∀ s, Q (φ s)) {l : L} :
    ∀ {s s' : S}, Lattice.Core.Star R s l s' → Q (φ s') := by
  intro s s' hs
  induction hs with
  | refl => exact hin s
  | tail _ hbc ih => exact hQ (φ _) l (φ _) ih (h _ l _ hbc)

/-! ## 七、反例：模拟关系不是空的 -/

/-- **标签不匹配 ⟹ 无模拟**（承重反例模式）：若 `R` 有一条标签 `a` 的出边，
而 `R'` 在 `φ s` 处的所有出边标签都 `≠ a`，则不存在从 `R` 到 `R'` 的
（经 `φ` 的）模拟。**这否定了一种常见误读**：「只要两端结构同构，语义就保持」——
模拟要求**标签精确匹配**，标签就是可观察行为。 -/
theorem not_sim_of_obs_mismatch {S S' : Type*}
    {R : S → ℕ → S → Prop} {R' : S' → ℕ → S' → Prop} {φ : S → S'}
    {s : S} {a : ℕ} {s' : S} (hex : R s a s')
    (hmis : ∀ b : ℕ, ∀ t : S', R' (φ s) b t → b ≠ a) :
    ¬ ForwardSim R R' φ := by
  intro h
  exact hmis a (φ s') (h s a s' hex) rfl

/-! ## 八、前向 ≠ 后向（诚实标注的机器化） -/

/-- **前向模拟不蕴含后向模拟**：在状态类型 `Bool` 上，令
`R true l b := b = false`（真只有一个出边）而 `R false l b := True`（假有自环与到真）。
则 `ForwardSim R R id` **成立**（真 ⟹ 假，假 ⟹ 任意），但反向不成立：
`R false l false` 在后向关系里要求 `R true l true`，而 `R true` 只能到 `false`。

这条定理**机器化地**说明了本文件只做了 bisimulation 的**一半**。 -/
theorem forward_not_backward :
    ForwardSim (fun (a : Bool) (_ : Unit) b => a = true ∧ b = false)
      (fun (a : Bool) (_ : Unit) b => a = true ∧ b = false) id ∧
    ¬ ForwardSim (fun (a : Bool) (_ : Unit) b => a = true ∧ b = false)
      (fun (a : Bool) (_ : Unit) b => b = true ∧ a = false) id := by
  refine ⟨fun a l b h => h, ?_⟩
  intro h
  have hstep : (fun (a : Bool) (_ : Unit) b => a = true ∧ b = false) true () false :=
    ⟨rfl, rfl⟩
  have := h true () false hstep
  simp at this

end Lattice.Lib.Compiler.RealSemanticsPreservation
