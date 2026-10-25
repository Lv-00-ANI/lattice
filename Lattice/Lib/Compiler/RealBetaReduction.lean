import Mathlib
import Lattice.Lib.Compiler.RealLambdaCalculus
/-!
# LATTICE: β-归约、替换引理与局部合流（含一步菱形为假的机器反例）

在 `RealLambdaCalculus` 的 de Bruijn 语法 / 提升 / 并行替换基础设施上，本文件建立
无类型 λ-演算的一步 β-归约与多步归约，并给出：

  1. `betaSubst`：单点替换「把 `var 0` 换成 `s`，其余索引下移一位」；
  2. `RedStep`：一步 β-归约关系（含 `app_l`/`app_r`/`lam` 上下文闭包）；
     `BetaStar := Relation.ReflTransGen RedStep` 及其代数（`star_refl`/`star_single`/
     `star_trans`/`star_head`/`star_tail`/`star_appL`/`star_appR`/`star_lam`）；
  3. 反转引理 `step_app_inv`、`step_lam_inv` 与 `not_step_var`；
  4. **替换引理**：`betaSubst_var0`、`betaSubst_varSucc`、`betaSubst_self`、
     `betaSubst_subst`（复用 `RealLambdaCalculus.subst_subst`）、
     `betaSubst_compose_lift`（复用 `subst_lift`）；
  5. **正向局部合流片段**：不相交余归约的菱形 `join_app_disjoint`，
     以及 `lam` 下的菱形提升 `diamond_lam`；
  6. **负结果（机器验证反例）**：一步 β 的「一步菱形性质」为假。
     取 `T = (λx. x x) (I z)`（`I = λy.y`，`z` 自由变量），
     `T` 同时有根 β 与参数内 β 两个余归约，得到
     `U = (I z)(I z)` 与 `V = (λx. x x) z`；
     `diamond_fails : ¬ ∃ w, RedStep U w ∧ RedStep V w`。

诚实标注（无 sorry / axiom / admit）：
- **全局合流（Church–Rosser）未证**：本文件只给出替换引理、`BetaStar` 代数、
  一步菱形为假的机器反例，以及不相交余归约的**正向**汇合片段。
  一般 β 的局部合流（关键对 `(λx.t) s` 与体内余归约）与终止性均**未证**，
  因此全局合流存在**缺口**；所需条件（终止性 + 局部合流 ⟹ 合流）见
  `RealGlobalConfluence` 的 Newman 引理。
- 「一步菱形为假」是**降级/负结果**：一步 β 不满足一步菱形（需要两步才能汇合），
  这与「合流」本身为真是相容的（`U`、`V` 可经 `z z` 汇合），但不做该汇合的证明。
- 本文件不引入任何未证假设。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealBetaReduction

/-! ## 一、单点替换与一步 β-归约 -/

/-- 单点替换：把 `var 0` 换成 `s`，其余自由索引 `k+1` 换成 `k`（下移一位）。 -/
def betaSubst (s t : Term) : Term :=
  subst (fun n => match n with | 0 => s | k + 1 => .var k) t

/-- 一步 β-归约关系：根 β（redex）加上下文闭包。 -/
inductive RedStep : Term → Term → Prop where
  | beta (t s : Term) : RedStep (.app (.lam t) s) (betaSubst s t)
  | app_l {a a' b : Term} : RedStep a a' → RedStep (.app a b) (.app a' b)
  | app_r {a b b' : Term} : RedStep b b' → RedStep (.app a b) (.app a b')
  | lam {t t' : Term} : RedStep t t' → RedStep (.lam t) (.lam t')

/-- 多步 β-归约（`RedStep` 的自反传递闭包）。 -/
abbrev BetaStar (t u : Term) : Prop := Relation.ReflTransGen RedStep t u

/-! ## 二、`BetaStar` 的基本代数 -/

/-- 多步归约的自反性。 -/
theorem star_refl (t : Term) : BetaStar t t := Relation.ReflTransGen.refl

/-- 单步归约是多步归约。 -/
theorem star_single {a b : Term} (h : RedStep a b) : BetaStar a b :=
  Relation.ReflTransGen.single h

/-- 多步归约的传递性。 -/
theorem star_trans {a b c : Term} (h₁ : BetaStar a b) (h₂ : BetaStar b c) : BetaStar a c :=
  h₁.trans h₂

/-- 多步归约的头部拼接：一步 + 多步。 -/
theorem star_head {a b c : Term} (h₁ : RedStep a b) (h₂ : BetaStar b c) : BetaStar a c :=
  Relation.ReflTransGen.head h₁ h₂

/-- 多步归约的尾部拼接：多步 + 一步。 -/
theorem star_tail {a b c : Term} (h₁ : BetaStar a b) (h₂ : RedStep b c) : BetaStar a c :=
  h₁.tail h₂

/-- `app` 左参数的上下文闭包保持多步归约。 -/
theorem star_appL {a a' b : Term} (h : BetaStar a a') : BetaStar (.app a b) (.app a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (RedStep.app_l hbc)

/-- `app` 右参数的上下文闭包保持多步归约。 -/
theorem star_appR {a b b' : Term} (h : BetaStar b b') : BetaStar (.app a b) (.app a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (RedStep.app_r hbc)

/-- `lam` 下的上下文闭包保持多步归约。 -/
theorem star_lam {t t' : Term} (h : BetaStar t t') : BetaStar (.lam t) (.lam t') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (RedStep.lam hbc)

/-! ## 三、反转引理 -/

/-- 变量没有一步归约。 -/
theorem not_step_var (n : ℕ) (t : Term) : ¬ RedStep (.var n) t := by
  intro h
  cases h

/-- `app` 的一步归约反转：只能是根 β 或左右参数的上下文步。
（`cases h with | beta t₀ s₀` 会失败：`RedStep.beta` 的被绑定项由**指标决定**，
Lean 在 `cases` 时把它们消解掉，多写的名字报 `unknown identifier 's₀'`
——该分支改用 `_` 占位并按指标恢复。） -/
theorem step_app_inv {a b t : Term} (h : RedStep (.app a b) t) :
    (∃ t₀ s₀, a = .lam t₀ ∧ b = s₀ ∧ t = betaSubst s₀ t₀) ∨
    (∃ a', RedStep a a' ∧ t = .app a' b) ∨
    (∃ b', RedStep b b' ∧ t = .app a b') := by
  cases h with
  | beta => exact Or.inl ⟨_, _, rfl, rfl, rfl⟩
  | app_l h' => exact Or.inr (Or.inl ⟨_, h', rfl⟩)
  | app_r h' => exact Or.inr (Or.inr ⟨_, h', rfl⟩)

/-- `lam` 的一步归约反转：只能来自体内一步。 -/
theorem step_lam_inv {X t : Term} (h : RedStep (.lam X) t) : ∃ X', t = .lam X' ∧ RedStep X X' := by
  cases h with
  | lam h' => exact ⟨_, rfl, h'⟩

/-! ## 四、替换引理 -/

/-- 单点替换在 `var 0` 上给出被替换项。 -/
theorem betaSubst_var0 (s : Term) : betaSubst s (.var 0) = s := rfl

/-- 单点替换在 `var (k+1)` 上下移索引。 -/
theorem betaSubst_varSucc (s : Term) (k : ℕ) : betaSubst s (.var (k + 1)) = .var k := rfl

/-- 单点替换对自身应用 `x x` 给出 `s s`。 -/
theorem betaSubst_self (s : Term) :
    betaSubst s (.app (.var 0) (.var 0)) = .app s s := by
  simp [betaSubst, subst]

/-- **替换引理（复合形式）**：单点替换与任意并行替换可交换。 -/
theorem betaSubst_subst (s : Term) (τ : ℕ → Term) (t : Term) :
    betaSubst s (subst τ t) = subst (fun n => betaSubst s (τ n)) t := by
  unfold betaSubst
  exact subst_subst t _ τ

/-- **替换引理（提升形式）**：单点替换与提升按 `RealLambdaCalculus.subst_lift` 相容。 -/
theorem betaSubst_compose_lift (s t : Term) :
    subst (up (fun n => match n with | 0 => s | k + 1 => .var k)) (lift 1 t) =
      lift 1 (betaSubst s t) := by
  unfold betaSubst
  exact subst_lift t _

/-! ## 五、正向局部合流片段（不相交余归约） -/

/-- **不相交余归约的菱形**：两个参数各自一步归约可在 `.app a' b'` 汇合。 -/
theorem join_app_disjoint {a a' b b' : Term} (h₁ : RedStep a a') (h₂ : RedStep b b') :
    ∃ w, BetaStar (.app a' b) w ∧ BetaStar (.app a b') w :=
  ⟨.app a' b', star_single (RedStep.app_r h₂), star_single (RedStep.app_l h₁)⟩

/-- **`lam` 下的菱形提升**：体内两个余归约汇合 ⟹ 抽象下也汇合。 -/
theorem diamond_lam {t₁ t₂ : Term} (h : ∃ w, BetaStar t₁ w ∧ BetaStar t₂ w) :
    ∃ w, BetaStar (.lam t₁) w ∧ BetaStar (.lam t₂) w := by
  rcases h with ⟨w, hw₁, hw₂⟩
  exact ⟨.lam w, star_lam hw₁, star_lam hw₂⟩

/-! ## 六、一步菱形为假（机器验证反例） -/

/-- 恒等组合子 `I = λy. y`。 -/
def redI : Term := .lam (.var 0)

/-- 自由变量 `z`。 -/
def redZ : Term := .var 0

/-- 自应用体 `x x`。 -/
def redB : Term := .app (.var 0) (.var 0)

/-- `T = (λx. x x) (I z)`。 -/
def redT : Term := .app (.lam redB) (.app redI redZ)

/-- 根 β 一步的结果 `U = (I z)(I z)`。 -/
def redU : Term := .app (.app redI redZ) (.app redI redZ)

/-- 参数内 β 一步的结果 `V = (λx. x x) z`。 -/
def redV : Term := .app (.lam redB) redZ

/-- 完全归约的结果 `z z`。 -/
def redZZ : Term := .app redZ redZ

/-- `I z` 没有一步归约到 `λ` 之外；`λ` 体的形式被排除。 -/
theorem not_step_lam_var (t : Term) : ¬ RedStep (.lam (.var 0)) t := by
  intro h
  rcases step_lam_inv h with ⟨X', _, hX'⟩
  exact not_step_var 0 X' hX'

/-- `I z` 的一步归约只有一个结果 `z`。 -/
theorem step_Iz {t : Term} (h : RedStep (.app redI redZ) t) : t = redZ := by
  rcases step_app_inv h with ⟨t₀, s₀, ha, hb, hw⟩ | ⟨a', hs, hw⟩ | ⟨b', hs, hw⟩
  · injection ha with ht₀
    rw [hw]
    rw [← hb, ← ht₀]
    rfl
  · exact absurd hs (not_step_lam_var a')
  · exact absurd hs (not_step_var 0 b')

/-- `U = (I z)(I z)` 的一步归约只有两种结果。 -/
theorem step_redU {w : Term} (h : RedStep redU w) :
    w = .app redZ (.app redI redZ) ∨ w = .app (.app redI redZ) redZ := by
  rcases step_app_inv h with ⟨t₀, s₀, ha, hb, hw⟩ | ⟨a', hs, hw⟩ | ⟨b', hs, hw⟩
  · cases ha
  · exact Or.inl (by rw [hw, step_Iz hs])
  · exact Or.inr (by rw [hw, step_Iz hs])

/-- `x x`（`redB`）没有一步归约：它是 `app` 但两个子项都是变量，而变量无一步归约。 -/
theorem not_step_redB (u : Term) : ¬ RedStep redB u := by
  intro h
  rcases step_app_inv h with ⟨t₀, s₀, ha, _, _⟩ | ⟨a', hs, _⟩ | ⟨b', hs, _⟩
  · exact Term.noConfusion ha
  · exact not_step_var 0 a' hs
  · exact not_step_var 0 b' hs

/-- `V = (λx. x x) z` 的一步归约只有一个结果 `z z`。
（`redB = x x` 是 `app`，其一步归约只能来自左右子项的上下文步，
而 `var _` 无一步归约——故 `app_l`/`app_r` 分支由 `not_step_var` 消解。） -/
theorem step_redV {w : Term} (h : RedStep redV w) : w = redZZ := by
  rcases step_app_inv h with ⟨t₀, s₀, ha, hb, hw⟩ | ⟨a', hs, hw⟩ | ⟨b', hs, hw⟩
  · injection ha with ht₀
    rw [hw]
    rw [← hb, ← ht₀]
    rfl
  · rcases step_lam_inv hs with ⟨X', hX', hstep⟩
    exact absurd hstep (not_step_redB X')
  · exact absurd hs (not_step_var 0 b')

/-- `T` 根 β 一步到 `U`。 -/
theorem step_T_U : RedStep redT redU := by
  have h := RedStep.beta redB (.app redI redZ)
  have hb : betaSubst (.app redI redZ) redB = redU := by decide
  rw [hb] at h
  simpa [redT] using h

/-- `T` 参数内 β 一步到 `V`。 -/
theorem step_T_V : RedStep redT redV := by
  have h : RedStep (.app (.lam redB) (.app redI redZ)) (.app (.lam redB) redZ) :=
    RedStep.app_r (a := .lam redB) (RedStep.beta (.var 0) redZ)
  simpa [redT, redV] using h

/-- **一步菱形性质为假**：`T` 的两个一步归约结果 `U`、`V` 没有共同的一步归约。 -/
theorem diamond_fails : ¬ ∃ w : Term, RedStep redU w ∧ RedStep redV w := by
  rintro ⟨w, hU, hV⟩
  rcases step_redU hU with hw | hw
  · rw [step_redV hV] at hw
    exact absurd hw (by decide)
  · rw [step_redV hV] at hw
    exact absurd hw (by decide)

end Lattice.Lib.Compiler.RealBetaReduction
