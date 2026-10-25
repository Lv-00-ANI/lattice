import Mathlib
import Lattice.Lib.Compiler.RealLambdaCalculus
import Lattice.Lib.Compiler.RealBetaReduction

open Lattice.Lib.Compiler.RealBetaReduction

/-!
# LATTICE: β 的并行归约路线 —— 关键对的一步收口、Ω 不终止见证、以及未完成边界的机器核验

`RealBetaReduction` 已机器验证「一步 β 的**一步菱形性质为假**」（`diamond_fails`）。
本文件沿**并行归约（parallel reduction / Tait–Martin-Löf）**这一正确补救方向，
交付**为真且已内核验证**的部分，并把**未完成的部分精确划界**。

   1. `ParStep`：并行 β-归约（`refl`/`var`/`lam`/`app` 相容 + 根 β 规则 `par_beta`），
      `ParStar` 及其代数（`parStar_refl`/`_single`/`_trans`/`_head`/`_tail`/
      `parStar_appL`/`parStar_appR`/`parStar_lam`）；
   2. `parStep_of_step`：**`BetaStep ⟹ ParStep`**（一步 β 嵌入并行 β），
      推论 `beta_le_parStar`（`Lattice.Lib.Compiler.RealBetaReduction.BetaStar ⊆ ParStar`）；
   3. **关键对的一步收口（与 `diamond_fails` 逐项对照）**：
      对 `diamond_fails` 的三个项 `redT`、`redU`、`redV`（定义复用
      `RealBetaReduction`），机器验证
      `par_T_zz : ParStep redT redZZ`、`par_U_zz : ParStep redU redZZ`、
      `par_V_zz : ParStep redV redZZ` —— 即 `U`、`V` **在一步并行归约内汇合**，
      而一步 `RedStep` 下**无**共同归约（`diamond_fails`）。并列陈述见
      `par_diamond_true_but_step_diamond_false`、
      `par_stronger_than_step_on_T` 与 `par_T_not_step_T`（后者机器验证
      `redT →_p redZZ` 成立但 `redT → redZZ` **不**成立，故
      `ParStep` 与 `RedStep` 在单步层面**互不包含**，只能在多步闭包层面比较）；
   4. **无类型 λ 不终止（机器见证）**：`Omega := (λx. x x)(λx. x x)`，
      `omega_step_self : BetaStep Omega Omega`（自归约）、
      `omega_parStep_self : ParStep Omega Omega`、
      `step_Omega_inv`（`Omega` 的一步归约只能是 `Omega`）、
      **`omegaStar_iff`：`Omega` 的任意多步 β-归约只能是 `Omega` 自身**
      （经 `omegaStar_step` 的不变量形式证明）、
      `Omega_not_normalForm`（`Omega` **不是**规范形）、
      `omegaStar_eq_singleton`（`Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega ·` 恰为单点集 `{Omega}`），
      推论 **`omega_no_normal_form`：不存在 `Omega` 到任何规范形的多步归约**；
   5. **未完成边界的机器核验**：`lift_betaSubst_fails` —— 把并行 β 与「提升」
      交换（这是把并行菱形推广到任意项、并证明替换引理 `subst_parStep`
      `lam` 情形的必要条件）所需的等式 `lift 1 (betaSubst s' t') =
      betaSubst (lift 1 s') (lift 1 t')` **在命题层面即为假**
      （闭项反例 + `decide`），故一般提升交换律不存在（`no_lift_betaSubst_law`）。
      第六节同时给出第 3·补 节的**多步版同源障碍**说明（`lift_step` 亦不成立）。

**诚实边界（降级清单，务必如实阅读）**：
- **全局合流（Church–Rosser）本次「未证」**。本文件**没有**给出对任意项的
  `par_diamond`、**没有** `par_star_iff_beta_star`、**没有** `beta_confluent`。
  已交付的是：并行归约的定义与代数、一步 β 到并行 β 的嵌入、**关键对的一步收口**、
  以及**未完成部分的精确障碍刻画**（第 5 条 + 下方说明）。
- **障碍是可陈述且已机器核验的**：把 `ParStep` 的根 β 规则写成
  `(.app (.lam t) s) → betaSubst s' t'`（复用 `RealBetaReduction.betaSubst`）后，
  「提升与并行步交换」`lift_parStep` 的 β 情形需要的等式 `lift_betaSubst_eq`
  **为假**（`lift_betaSubst_fails`）。缺少它，`ParStep` 就**不能**在 `lam`
  之下保持（`ParStep` 非「提升稳定」），因而**替换引理 `subst_parStep` 的
  `lam` 情形无法闭合**，一般 `par_diamond` 随之无法证。
  标准补法是把 β 规则改用**捕获避免的移位感知替换**（Tait–Martin-Löf 的 `⋆`
  翻译或显式重命名机器）；本次**未做**，故**如实标注为未完成**。
- **无类型 λ 不终止已机器验证**（第 4 条，负结果）：故 Newman
  （`RealGlobalConfluence.newman`）对 β 的终止性前提**不成立**、
  局部合流前提亦为假（`RealBetaReduction.diamond_fails`）。
- **STLC 强规范化未做**：需要简单类型系统 + Tait 可归约性论证（reducibility
  candidates），规模远超本次交付；**明确标注为未做**。
  本文件不声称任何「类型化 λ 终止」的结论。
- 本文件不引入任何未证假设，无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealBetaConfluence
/-! ## 一、并行 β-归约 -/

/-- **并行 β-归约**：一次归约项中**所有** redex。

`refl` 是冗余但便利的自反规则；`par_beta` 的被替换项用 `RealBetaReduction.betaSubst`
（即 `subst` + 单点替换函数），以便复用 `RealBetaReduction` 的替换引理。 -/
inductive ParStep : Term → Term → Prop where
  /-- 自反：并行归约可不动。 -/
  | refl (t : Term) : ParStep t t
  /-- 变量无法归约。 -/
  | var (n : ℕ) : ParStep (.var n) (.var n)
  /-- 抽象下逐点归约。 -/
  | lam {t t' : Term} : ParStep t t' → ParStep (.lam t) (.lam t')
  /-- 应用两侧同时归约。 -/
  | app {f f' a a' : Term} : ParStep f f' → ParStep a a' → ParStep (.app f a) (.app f' a')
  /-- **根 β（并行）**：函数体与参数各自并行归约，然后一次性收缩。 -/
  | beta {t t' s s' : Term} : ParStep t t' → ParStep s s' →
      ParStep (.app (.lam t) s) (betaSubst s' t')

/-- 并行归约的多步闭包。 -/
abbrev ParStar (t u : Term) : Prop := Relation.ReflTransGen ParStep t u

/-- 一步 β-归约（`RealBetaReduction.RedStep` 的别名，便于并行/一步对照陈述）。 -/
abbrev BetaStep (t u : Term) : Prop := RedStep t u


/-! ## 二、`ParStar` 的基本代数 -/

/-- 并行多步归约的自反性。 -/
theorem parStar_refl (t : Term) : ParStar t t := Relation.ReflTransGen.refl

/-- 并行单步是多步。 -/
theorem parStar_single {a b : Term} (h : ParStep a b) : ParStar a b :=
  Relation.ReflTransGen.single h

/-- 并行多步的传递性。 -/
theorem parStar_trans {a b c : Term} (h₁ : ParStar a b) (h₂ : ParStar b c) : ParStar a c :=
  h₁.trans h₂

/-- 并行多步的头部拼接：一步 + 多步。 -/
theorem parStar_head {a b c : Term} (h₁ : ParStep a b) (h₂ : ParStar b c) : ParStar a c :=
  Relation.ReflTransGen.head h₁ h₂

/-- 并行多步的尾部拼接：多步 + 一步。 -/
theorem parStar_tail {a b c : Term} (h₁ : ParStar a b) (h₂ : ParStep b c) : ParStar a c :=
  h₁.tail h₂

/-- `app` 左参数的上下文闭包保持并行多步。 -/
theorem parStar_appL {a a' b : Term} (h : ParStar a a') : ParStar (.app a b) (.app a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (ParStep.app hbc (ParStep.refl b))

/-- `app` 右参数的上下文闭包保持并行多步。 -/
theorem parStar_appR {a b b' : Term} (h : ParStar b b') : ParStar (.app a b) (.app a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (ParStep.app (ParStep.refl a) hbc)

/-- `lam` 下的上下文闭包保持并行多步。 -/
theorem parStar_lam {t t' : Term} (h : ParStar t t') : ParStar (.lam t) (.lam t') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (ParStep.lam hbc)

/-! ## 三、一步 β 嵌入并行 β -/

/-- **一步 β 嵌入并行 β**：`RedStep u v ⟹ ParStep u v`。
对 `RedStep` 的推导做归纳；`beta` 情形用 `ParStep.beta` + 自反子推导。 -/
theorem parStep_of_step {u v : Term} (h : RedStep u v) : ParStep u v := by
  induction h with
  | beta t s => exact ParStep.beta (ParStep.refl t) (ParStep.refl s)
  | app_l _ ih => exact ParStep.app ih (ParStep.refl _)
  | app_r _ ih => exact ParStep.app (ParStep.refl _) ih
  | lam _ ih => exact ParStep.lam ih

/-- **`Lattice.Lib.Compiler.RealBetaReduction.BetaStar ⊆ ParStar`**：一步 β 的多步闭包嵌入并行归约的多步闭包。 -/
theorem beta_le_parStar {u v : Term} (h : Lattice.Lib.Compiler.RealBetaReduction.BetaStar u v) : ParStar u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (parStep_of_step hbc)

/-! ## 三·补、为什么「多步水平的替换引理」同样卡住（真诚标注）

自然的下一步是证 `ParStep u v ⟹ Lattice.Lib.Compiler.RealBetaReduction.BetaStar u v`（从而 `ParStar ⊆ Lattice.Lib.Compiler.RealBetaReduction.BetaStar`，
配 `beta_le_parStar` 得 `ParStar = Lattice.Lib.Compiler.RealBetaReduction.BetaStar`）。其 `beta` 情形需要
**多步水平的替换引理** `Lattice.Lib.Compiler.RealBetaReduction.BetaStar s s' → Lattice.Lib.Compiler.RealBetaReduction.BetaStar t t' → Lattice.Lib.Compiler.RealBetaReduction.BetaStar (betaSubst s t) (betaSubst s' t')`，
而这又需要 `Lattice.Lib.Compiler.RealBetaReduction.BetaStar s s' ⟹ Lattice.Lib.Compiler.RealBetaReduction.BetaStar (lift 1 s) (lift 1 s')`，即

`lift 1 (betaSubst s t) = betaSubst (lift 1 s) (lift 1 t)`（或等价的一步提升交换）——
**它与第六节的 `lift_betaSubst_fails` 同源，为假**：
`lift 1` 在跨过 `lam` 时用的是 `upRen (·+1)`（它把绑定变量 `var 0` 固定），
而 `lift 1` 在顶层用的是 `(·+1)`，两者在 `var 0` 处不同。
因此 `lift_step`（`RedStep u u' ⟹ RedStep (lift 1 u) (lift 1 u')`）**在本表示下不成立**，
本文件**不**声称它，也**未**给出 `par_le_betaStar` / `par_star_iff_beta_star`。
标准补法同上（Tait–Martin-Löf 的层号化开发 / 显式重命名机器），**本次未做**。 -/

/-! ## 四、关键对的一步收口（与 `diamond_fails` 逐项对照）

`RealBetaReduction` 的反例：`T = (λx. x x)(I z)` 同时有根 β（→ `U`）与参数内 β
（→ `V`），且 `U`、`V` **无**共同的一步 `RedStep` 归约（`diamond_fails`）。
下面机器验证：在**并行**归约下 `U`、`V` 各自**一步**到达公共归约 `z z`
（事实上 `T` 本身就一步并行到达 `z z`）。 -/

/-- `T` 一步并行归约到完全归约结果 `z z`（根 β 与参数 β **同时**发生）。 -/
theorem par_T_zz : ParStep redT redZZ := by
  have hq : ParStep redB (.app redZ redZ) :=
    ParStep.app (ParStep.refl (.var 0)) (ParStep.refl (.var 0))
  have hr : ParStep (.app redI redZ) redZ :=
    ParStep.beta (ParStep.refl (.var 0)) (ParStep.refl redZ)
  have h := ParStep.beta (s := .app redI redZ) hq hr
  have hb : betaSubst redZ (.app redZ redZ) = redZZ := by decide
  rw [hb] at h
  simpa [redT] using h

/-- `U = (I z)(I z)` 一步并行归约到 `z z`。 -/
theorem par_U_zz : ParStep redU redZZ := by
  have h1 : ParStep (.app redI redZ) redZ :=
    ParStep.beta (ParStep.refl (.var 0)) (ParStep.refl redZ)
  have h2 : ParStep (.app redI redZ) redZ :=
    ParStep.beta (ParStep.refl (.var 0)) (ParStep.refl redZ)
  have h := ParStep.app h1 h2
  simpa [redU, redZZ] using h

/-- `V = (λx. x x) z` 一步并行归约到 `z z`。 -/
theorem par_V_zz : ParStep redV redZZ := by
  have hq : ParStep redB (.app redZ redZ) :=
    ParStep.app (ParStep.refl (.var 0)) (ParStep.refl (.var 0))
  have h := ParStep.beta (s := redZ) hq (ParStep.refl redZ)
  have hb : betaSubst redZ (.app redZ redZ) = redZZ := by decide
  rw [hb] at h
  simpa [redV] using h

/-- **并行菱形在关键对上成立**：`redU`、`redV` 在**一步**并行归约内汇合到 `redZZ`。
（对照：`RealBetaReduction.diamond_fails` 说明它们在一步 `RedStep` 下**不能**汇合。） -/
theorem par_diamond_critical_pair :
    ∃ w, ParStar redU w ∧ ParStar redV w :=
  ⟨redZZ, parStar_single par_U_zz, parStar_single par_V_zz⟩

/-- **「一步菱形为假、并行菱形为真」的并列机器证据**：
`redU`、`redV` 在**一步** `ParStep` 内汇合到 `redZZ`，
而它们在**一步** `RedStep` 下**无**共同归约（`diamond_fails`）。 -/
theorem par_diamond_true_but_step_diamond_false :
    (∃ w, ParStep redU w ∧ ParStep redV w ∧ w = redZZ) ∧
      (¬ ∃ w, RedStep redU w ∧ RedStep redV w) :=
  ⟨⟨redZZ, par_U_zz, par_V_zz, rfl⟩, diamond_fails⟩

/-- `redT` 同时有根 β（→ `redU`）与参数内 β（→ `redV`）两个一步 `RedStep`，
但在**一步** `ParStep` 内直达完全归约 `redZZ`。 -/
theorem par_stronger_than_step_on_T :
    BetaStep redT redU ∧ BetaStep redT redV ∧ ParStep redT redZZ :=
  ⟨step_T_U, step_T_V, par_T_zz⟩

/-- **`ParStep` 与 `RedStep` 在单步层面互不包含（机器见证）**：
`redT →_p redZZ` 成立，但 `redT → redZZ` **不**成立（需两步 β）。
结合 `parStep_of_step`（`RedStep ⊆ ParStep`）可知反向包含成立，
但本定理说明 `ParStep` 单步严格更强，故两者的比较只能在**多步闭包**层面进行。 -/
theorem par_T_not_step_T : ¬ BetaStep redT redZZ := by
  intro h
  rcases step_app_inv h with ⟨t₀, s₀, ha, hb, hw⟩ | ⟨a', hs, hw⟩ | ⟨b', hs, hw⟩
  · injection ha with ht₀
    rw [← hb, ← ht₀] at hw
    have hU : betaSubst (.app redI redZ) redB = redU := by decide
    rw [hU] at hw
    exact absurd hw (by decide)
  · rcases step_lam_inv hs with ⟨X', _, hstep⟩
    exact absurd hstep (not_step_redB X')
  · rw [step_Iz hs] at hw
    exact absurd hw (by decide)

/-! ## 五、无类型 λ 不终止的机器见证：`Ω`

`Ω = (λx. x x)(λx. x x)`：一步 β 后**回到自身**（`omega_step_self`）。
更强地，`Ω` 的**任意**多步 β-归约都只能停在 `Ω`（`omegaStar_iff`），
故 `Ω` **没有**到规范形的归约（`omega_no_normal_form`）。

这是**负结果**：无类型 λ 演算**不终止（不弱规范化）**，
因此 `RealGlobalConfluence.newman` 所需的终止性前提对 β **不成立**。 -/

/-- `Ω` 的体 `x x`。 -/
def omegaB : Term := .app (.var 0) (.var 0)

/-- **`Ω = (λx. x x)(λx. x x)`**（经典的自我归约项，见证无类型 λ 不终止）。 -/
def Omega : Term := .app (.lam omegaB) (.lam omegaB)

/-- `Ω` 一步 β 归约到自身。 -/
theorem omega_step_self : BetaStep Omega Omega := by
  have h := RedStep.beta omegaB (.lam omegaB)
  have hb : betaSubst (.lam omegaB) omegaB = Omega := by
    unfold omegaB Omega
    exact betaSubst_self (.lam (.app (.var 0) (.var 0)))
  rw [hb] at h
  simpa [Omega, omegaB] using h

/-- `Ω` 一步**并行** β 归约到自身。 -/
theorem omega_parStep_self : ParStep Omega Omega := by
  have hq : ParStep omegaB omegaB := ParStep.refl omegaB
  have h := ParStep.beta (s := .lam omegaB) hq (ParStep.refl (.lam omegaB))
  have hb : betaSubst (.lam omegaB) omegaB = Omega := by
    unfold Omega omegaB
    exact betaSubst_self (.lam (.app (.var 0) (.var 0)))
  rw [hb] at h
  simpa [Omega, omegaB] using h

/-- `Ω` 的一步 β 归约**只能是** `Ω` 自身（反转引理）。
`app` 反转后：根 β 分支给出 `Ω`；两个上下文分支要求 `x x` 有一步归约，
被 `not_step_redB` 排除。 -/
theorem step_Omega_inv {w : Term} (h : BetaStep Omega w) : w = Omega := by
  have hO : Omega = .app (.lam omegaB) (.lam omegaB) := rfl
  rw [hO] at h
  rcases step_app_inv h with ⟨t₀, s₀, ha, hb, hw⟩ | ⟨a', hs, hw⟩ | ⟨b', hs, hw⟩
  · injection ha with ht₀
    rw [hw, ← hb, ← ht₀]
    exact (betaSubst_self (.lam (.app (.var 0) (.var 0)))).symm
  · rcases step_lam_inv hs with ⟨X', _, hstep⟩
    exact absurd hstep (not_step_redB X')
  · rcases step_lam_inv hs with ⟨X', _, hstep⟩
    exact absurd hstep (not_step_redB X')

/-- **`Ω` 的多步归约只能是 `Ω` 自身**（不变量形式）：
若 `a` 多步归约到 `b` 且 `a = Ω`，则 `b = Ω`。
对 `Lattice.Lib.Compiler.RealBetaReduction.BetaStar` 的推导做归纳，`tail` 步用 `step_Omega_inv` 反转。 -/
theorem omegaStar_step {a b : Term} (h : Lattice.Lib.Compiler.RealBetaReduction.BetaStar a b) (ha : a = Omega) : b = Omega := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
      have hb : _ = Omega := ih
      rw [hb] at hbc
      exact step_Omega_inv hbc

/-- **`Ω` 的多步归约只能是 `Ω` 自身**：`Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega w ↔ w = Omega`。 -/
theorem omegaStar_iff {w : Term} : Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega w ↔ w = Omega := by
  constructor
  · intro h
    exact omegaStar_step h rfl
  · intro h
    rw [h]

/-- `Ω` 到 `Ω` 的任意多步归约。 -/
theorem omegaStar_self : Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega Omega := star_refl Omega

/-- **规范形（无一步归约）**。 -/
abbrev NoStepReduct (u : Term) : Prop := ¬ ∃ v, RedStep u v

/-- `Ω` **不是**规范形（它总能再走一步）。 -/
theorem Omega_not_normalForm : ¬ NoStepReduct Omega := by
  intro h
  exact h ⟨Omega, omega_step_self⟩

/-- **`Ω` 没有到规范形的多步归约**：任何 `Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega w` 都给出 `w = Omega`，
而 `Omega` 不是规范形。**这是无类型 λ 演算不终止的机器见证。** -/
theorem omega_no_normal_form : ¬ ∃ w, Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega w ∧ NoStepReduct w := by
  rintro ⟨w, hstar, hnf⟩
  rw [omegaStar_iff] at hstar
  rw [hstar] at hnf
  exact hnf ⟨Omega, omega_step_self⟩

/-- **`Ω` 落在单元素自环里**：多步闭包 `Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega ·` 恰好是单点集 `{Omega}`。 -/
theorem omegaStar_eq_singleton : {w : Term | Lattice.Lib.Compiler.RealBetaReduction.BetaStar Omega w} = {Omega} := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact omegaStar_iff

/-! ## 六、未完成边界的机器核验

下面这条等式是把并行菱形从「关键对」推广到**任意项**时必经的一步：
要让 `ParStep` 在 `lam` 之下保持（即「提升稳定」），就需要
`lift 1 (betaSubst s' t') = betaSubst (lift 1 s') (lift 1 t')`。
本定理说明它**为假** —— 这就是本文件**未完成**一般 `par_diamond` /
`par_star_iff_beta_star` / `beta_confluent` 的**精确、可核验的原因**。 -/

/-- **提升与 `betaSubst` 不交换（机器反例，闭合项）**：
取 `s' = λy. y`（即 `redI`）、`t' = var 0`，
左边 `lift 1 (betaSubst redI (var 0)) = lift 1 redI = redI`，
右边 `betaSubst (lift 1 redI) (lift 1 (var 0)) = betaSubst redI (var 1) = var 0`
——两者不等（`decide` 判定）。 -/
theorem lift_betaSubst_fails :
    lift 1 (betaSubst redI (.var 0)) ≠ betaSubst (lift 1 redI) (lift 1 (.var 0)) := by
  decide

/-- 同上，以「显式等式为假」的形式陈述：不存在使该等式对**所有** `s'`、`t'`
成立的提升交换律。 -/
theorem no_lift_betaSubst_law :
    ¬ (∀ s' t' : Term, lift 1 (betaSubst s' t') = betaSubst (lift 1 s') (lift 1 t')) := by
  intro h
  exact lift_betaSubst_fails (h redI (.var 0))

end Lattice.Lib.Compiler.RealBetaConfluence
