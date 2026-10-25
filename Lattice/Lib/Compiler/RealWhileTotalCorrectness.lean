import Mathlib
import Lattice.Lib.Compiler.RealEffectOrdering
import Lattice.Lib.Compiler.RealWP
open Lattice.Lib.Compiler.RealEffectOrdering (State)
open Lattice.Lib.Compiler.RealWP
/-!
# LATTICE: while 的全正确性（终止性 + 退出 + 不变量）

`RealWP` 只做**部分正确性**（`Stmt` 刻意不含 `while`，`exec` 为全函数）。
本文件补上带 `while` 的**全正确性**：

  1. `StmtT`：在 `RealWP.Stmt`（`skip`/`assign`/`seq`/`ite`）上加入 `while b body`；
  2. `execF : ℕ → StmtT → State → Option State`：**带燃料的偏函数**（燃料 0 停机为 `none`）；
     `Denotes`、`Terminates`；
  3. `execF_mono`：燃料单调（多给燃料结果不变且必然停机）；
     `execF_det`：同一程序同一状态的结果唯一；
  4. `Triple P S Q`：全正确性 Hoare 三元组（停机 + 后置条件）；
     `triple_skip`/`triple_assign`/`triple_seq`/`triple_ite`；
  5. **`triple_while`（while 规则）**：若
     `{P ∧ b≠0} body {P}`（保持，且变式 `V` 严格递减）
     且 `P ∧ b=0 ⟹ Q`（退出），
     则 `{P} while {Q}`（**全正确性**）；证明用变式 `V` 上的强归纳 + 燃料累加；
  6. `wpT`：全正确性最弱前置条件；`wpT_while_fixpoint`（while 的 wp 是不动点）、
     `wpT_while_least`（**最小不动点**陈述）；
  7. **与 `RealWP.wp` 的连接**：`embed : Stmt → StmtT`（无 while 片段嵌入），
     `embed_sound`/`embed_complete`/`embed_denotes_iff`，以及
     `wpT_embed : wpT (embed S) Q = wp S Q`。

诚实标注（无 sorry / axiom / admit）：
- 全正确性依赖**变式函数** `V : State → ℕ` 的显式严格递减假设；`while` 规则把
  「终止」化为「变式递减」，不构造一般终止性判定。
- `execF` 的语义是**燃料受限**的：`Terminates` 定义为「存在燃料使其停机」，
  与燃料选择无关（由 `execF_mono`/`execF_det` 保证）。
- 与 `RealWP` 的连接只覆盖**无 while 片段**（`embed`）；while 本身的 wp 以
  **最小不动点**（`wpT_while_least`）刻画，不声称与 `RealWP` 的（不存在 while 的）`wp`
  相等。
- 本文件不引入任何未证假设（除 while 规则显式列出的变式/保持/退出前提外）。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealWhileTotalCorrectness
/-! ## 一、带 while 的命令语言与燃料语义 -/

/-- 带 `while` 的命令语言（扩展 `RealWP.Stmt`）。 -/
inductive StmtT where
  | skip : StmtT
  | assign (n : ℕ) (e : AExp) : StmtT
  | seq (S₁ S₂ : StmtT) : StmtT
  | ite (b : AExp) (S₁ S₂ : StmtT) : StmtT
  | while (b : AExp) (body : StmtT) : StmtT

/-- **带燃料的偏函数语义**：`execF k S σ` 表示「最多 `k` 步」执行 `S` 于 `σ` 的结果；
燃料耗尽（`k = 0`）为 `none`。 -/
def execF : ℕ → StmtT → State → Option State
  | 0, _, _ => none
  | _ + 1, .skip, σ => some σ
  | _ + 1, .assign n e, σ => some (Function.update σ n (evalA σ e))
  | k + 1, .seq S₁ S₂, σ => (execF k S₁ σ).bind (fun σ' => execF k S₂ σ')
  | k + 1, .ite b S₁ S₂, σ => if evalA σ b = 0 then execF k S₂ σ else execF k S₁ σ
  | k + 1, .while b body, σ =>
      if evalA σ b = 0 then some σ
      else (execF k body σ).bind (fun σ' => execF k (.while b body) σ')

/-- `Denotes S σ s`：存在燃料使 `S` 从 `σ` 停机于 `s`。 -/
def Denotes (S : StmtT) (σ s : State) : Prop := ∃ k, execF k S σ = some s

/-- `Terminates S σ`：`S` 从 `σ` 终止（存在停机状态）。 -/
def Terminates (S : StmtT) (σ : State) : Prop := ∃ s, Denotes S σ s

/-! ## 二、燃料单调性与确定性 -/

/-- **燃料单调**：若在燃料 `k` 下停机于 `s`，则任意更多燃料 `k + j` 下同样停机于 `s`。
（`while` 是 **保留字**：`| while b body =>` / `case while b body =>` 都报
`unexpected token 'while'; expected '_' or identifier`（STYLE 速查表「`λ` 是保留字」同类）。
且 `cases S with | … ` 要求**穷尽所有**分支，末尾补 `rename_i` 会报
`alternative 'while' has not been provided`。可行写法：`cases S`（不带 `with`）
+ 前四个用 `case 构造子名 =>` 具名分支 + 最后一个分支用**位置式 `rename_i`** 绑定。） -/
theorem execF_mono (k : ℕ) : ∀ (S : StmtT) (σ s : State),
    execF k S σ = some s → ∀ j, execF (k + j) S σ = some s := by
  induction k with
  | zero => intro S σ s h; simp [execF] at h
  | succ k ih =>
      intro S σ s h j
      rw [Nat.succ_add]
      cases S
      case skip => simpa only [execF] using h
      case assign n e => simpa only [execF] using h
      case seq S₁ S₂ =>
          simp only [execF] at h ⊢
          cases h1 : execF k S₁ σ with
          | none => simp [h1] at h
          | some σ₁ =>
              simp only [h1, Option.some_bind] at h
              rw [ih S₁ σ σ₁ h1 j]
              simp only [Option.some_bind]
              rw [ih S₂ σ₁ s h j]
      case ite b S₁ S₂ =>
          simp only [execF] at h ⊢
          by_cases hb : evalA σ b = 0
          · simp only [hb, if_true] at h ⊢
            exact ih S₂ σ s h j
          · simp only [hb, if_false] at h ⊢
            exact ih S₁ σ s h j
      rename_i b body
      simp only [execF] at h ⊢
      by_cases hb : evalA σ b = 0
      · simp only [hb, if_true] at h ⊢
        exact h
      · simp only [hb, if_false] at h ⊢
        cases h1 : execF k body σ with
        | none => simp [h1] at h
        | some σ₁ =>
            simp only [h1, Option.some_bind] at h
            rw [ih body σ σ₁ h1 j]
            simp only [Option.some_bind]
            rw [ih (.while b body) σ₁ s h j]

/-- **结果唯一**：同一程序在同一状态下任意两个停机燃料的结果相同。 -/
theorem execF_det {S : StmtT} {σ s₁ s₂ : State} {k₁ k₂ : ℕ}
    (h₁ : execF k₁ S σ = some s₁) (h₂ : execF k₂ S σ = some s₂) : s₁ = s₂ := by
  have h₁' : execF (max k₁ k₂) S σ = some s₁ := by
    have := execF_mono k₁ S σ s₁ h₁ (max k₁ k₂ - k₁)
    rwa [Nat.add_sub_cancel' (Nat.le_max_left k₁ k₂)] at this
  have h₂' : execF (max k₁ k₂) S σ = some s₂ := by
    have := execF_mono k₂ S σ s₂ h₂ (max k₁ k₂ - k₂)
    rwa [Nat.add_sub_cancel' (Nat.le_max_right k₁ k₂)] at this
  rw [h₁'] at h₂'
  exact Option.some.inj h₂'

/-! ## 三、全正确性 Hoare 三元组与规则 -/

/-- `Triple P S Q`：全正确性 Hoare 三元组（从 `P` 出发必停机且满足 `Q`）。 -/
def Triple (P : State → Prop) (S : StmtT) (Q : State → Prop) : Prop :=
  ∀ σ, P σ → ∃ s, Denotes S σ s ∧ Q s

/-- `skip` 规则。 -/
theorem triple_skip (P Q : State → Prop) (h : ∀ σ, P σ → Q σ) : Triple P .skip Q := by
  intro σ hP
  exact ⟨σ, ⟨1, rfl⟩, h σ hP⟩

/-- `assign` 规则。 -/
theorem triple_assign (P Q : State → Prop) (n : ℕ) (e : AExp)
    (h : ∀ σ, P σ → Q (Function.update σ n (evalA σ e))) :
    Triple P (.assign n e) Q := by
  intro σ hP
  exact ⟨_, ⟨1, rfl⟩, h σ hP⟩

/-- `seq` 规则。 -/
theorem triple_seq {P Q R : State → Prop} {S₁ S₂ : StmtT}
    (h₁ : Triple P S₁ Q) (h₂ : Triple Q S₂ R) : Triple P (.seq S₁ S₂) R := by
  intro σ hP
  rcases h₁ σ hP with ⟨σ', ⟨k₁, hk₁⟩, hQ⟩
  rcases h₂ σ' hQ with ⟨s, ⟨k₂, hk₂⟩, hR⟩
  refine ⟨s, ⟨k₁ + k₂ + 1, ?_⟩, hR⟩
  show (execF (k₁ + k₂) S₁ σ).bind (fun σ'' => execF (k₁ + k₂) S₂ σ'') = some s
  rw [execF_mono k₁ S₁ σ σ' hk₁ k₂]
  simp only [Option.some_bind]
  rw [Nat.add_comm k₁ k₂, execF_mono k₂ S₂ σ' s hk₂ k₁]

/-- `ite` 规则。 -/
theorem triple_ite {P Q : State → Prop} (b : AExp) {S₁ S₂ : StmtT}
    (h₁ : ∀ σ, P σ → evalA σ b ≠ 0 → ∃ s, Denotes S₁ σ s ∧ Q s)
    (h₂ : ∀ σ, P σ → evalA σ b = 0 → ∃ s, Denotes S₂ σ s ∧ Q s) :
    Triple P (.ite b S₁ S₂) Q := by
  intro σ hP
  by_cases hb : evalA σ b = 0
  · rcases h₂ σ hP hb with ⟨s, ⟨k, hk⟩, hQ⟩
    refine ⟨s, ⟨k + 1, ?_⟩, hQ⟩
    show (if evalA σ b = 0 then execF k S₂ σ else execF k S₁ σ) = some s
    rw [if_pos hb]
    exact hk
  · rcases h₁ σ hP hb with ⟨s, ⟨k, hk⟩, hQ⟩
    refine ⟨s, ⟨k + 1, ?_⟩, hQ⟩
    show (if evalA σ b = 0 then execF k S₂ σ else execF k S₁ σ) = some s
    rw [if_neg hb]
    exact hk

/-- **while 规则（全正确性）**：保持 + 退出 + 变式严格递减 ⟹ `{P} while {Q}`。 -/
theorem triple_while {P Q : State → Prop} (b : AExp) (body : StmtT) (V : State → ℕ)
    (hbody : ∀ σ, P σ → evalA σ b ≠ 0 →
      ∃ σ', Denotes body σ σ' ∧ P σ' ∧ V σ' < V σ)
    (hexit : ∀ σ, P σ → evalA σ b = 0 → Q σ) :
    Triple P (.while b body) Q := by
  intro σ₀ hP₀
  have main : ∀ n, ∀ σ, V σ = n → P σ → ∃ s, Denotes (.while b body) σ s ∧ Q s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ hV hP
      by_cases hb : evalA σ b = 0
      · refine ⟨σ, ⟨1, ?_⟩, hexit σ hP hb⟩
        show (if evalA σ b = 0 then some σ
              else (execF 0 body σ).bind (fun σ'' => execF 0 (.while b body) σ'')) = some σ
        rw [if_pos hb]
      · rcases hbody σ hP hb with ⟨σ', ⟨k, hk⟩, hP', hVlt⟩
        have hlt : V σ' < n := by omega
        rcases ih (V σ') hlt σ' rfl hP' with ⟨s, ⟨k', hk'⟩, hQ⟩
        refine ⟨s, ⟨k + k' + 1, ?_⟩, hQ⟩
        show (if evalA σ b = 0 then some σ
              else (execF (k + k') body σ).bind
                (fun σ'' => execF (k + k') (.while b body) σ'')) = some s
        rw [if_neg hb, execF_mono k body σ σ' hk k']
        simp only [Option.some_bind]
        rw [Nat.add_comm k k', execF_mono k' (.while b body) σ' s hk' k]
  exact main (V σ₀) σ₀ rfl hP₀

/-! ## 四、while 的 wp 与最小不动点 -/

/-- `wpT S Q`：全正确性最弱前置条件（停机 + 后置条件）。 -/
def wpT (S : StmtT) (Q : State → Prop) : State → Prop :=
  fun σ => ∃ s, Denotes S σ s ∧ Q s

/-- `Triple` 与 `wpT` 等价。 -/
theorem triple_iff_wpT (P : State → Prop) (S : StmtT) (Q : State → Prop) :
    Triple P S Q ↔ ∀ σ, P σ → wpT S Q σ :=
  Iff.rfl

/-- while 的谓词变换子（不动点方程的右端）：
`(b = 0 ∧ Q) ∨ (b ≠ 0 ∧ ∃σ'. body 停机于 σ' ∧ X σ')`。 -/
def whileF (b : AExp) (body : StmtT) (Q : State → Prop) (X : State → Prop) : State → Prop :=
  fun σ => (evalA σ b = 0 ∧ Q σ) ∨
    (evalA σ b ≠ 0 ∧ ∃ σ', Denotes body σ σ' ∧ X σ')

/-- **while 的 wp 是不动点**：`wpT (while b body) Q = whileF b body Q (wpT (while b body) Q)`。 -/
theorem wpT_while_fixpoint (b : AExp) (body : StmtT) (Q : State → Prop) :
    wpT (.while b body) Q = whileF b body Q (wpT (.while b body) Q) := by
  funext σ
  apply propext
  constructor
  · rintro ⟨s, ⟨k, hk⟩, hQ⟩
    cases k with
    | zero => simp [execF] at hk
    | succ k =>
        simp only [execF] at hk
        by_cases hb : evalA σ b = 0
        · simp only [hb, if_true] at hk
          injection hk with hs
          subst hs
          exact Or.inl ⟨hb, hQ⟩
        · simp only [hb, if_false] at hk
          cases h1 : execF k body σ with
          | none => simp [h1] at hk
          | some σ₁ =>
              simp only [h1, Option.some_bind] at hk
              exact Or.inr ⟨hb, σ₁, ⟨k, h1⟩, s, ⟨k, hk⟩, hQ⟩
  · intro h
    rcases h with ⟨hb, hQ⟩ | ⟨hb, σ', ⟨k₁, hk₁⟩, s, ⟨k₂, hk₂⟩, hQ⟩
    · refine ⟨σ, ⟨1, ?_⟩, hQ⟩
      show (if evalA σ b = 0 then some σ
            else (execF 0 body σ).bind (fun σ'' => execF 0 (.while b body) σ'')) = some σ
      rw [if_pos hb]
    · refine ⟨s, ⟨k₁ + k₂ + 1, ?_⟩, hQ⟩
      show (if evalA σ b = 0 then some σ
            else (execF (k₁ + k₂) body σ).bind
              (fun σ'' => execF (k₁ + k₂) (.while b body) σ'')) = some s
      rw [if_neg hb, execF_mono k₁ body σ σ' hk₁ k₂]
      simp only [Option.some_bind]
      rw [Nat.add_comm k₁ k₂, execF_mono k₂ (.while b body) σ' s hk₂ k₁]

/-- **while 的 wp 是最小不动点（最小前置不动点）**：
若 `X` 对 `whileF` 封闭（`whileF ... X ≤ X`），则 `wpT (while b body) Q ≤ X`。 -/
theorem wpT_while_least (b : AExp) (body : StmtT) (Q X : State → Prop)
    (hX : ∀ σ, whileF b body Q X σ → X σ) :
    ∀ σ, wpT (.while b body) Q σ → X σ := by
  have main : ∀ k, ∀ σ s, execF k (.while b body) σ = some s → Q s → X σ := by
    intro k
    induction k with
    | zero => intro σ s hk _; simp [execF] at hk
    | succ k ih =>
        intro σ s hk hQ
        simp only [execF] at hk
        by_cases hb : evalA σ b = 0
        · simp only [hb, if_true] at hk
          injection hk with hs
          subst hs
          exact hX σ (Or.inl ⟨hb, hQ⟩)
        · simp only [hb, if_false] at hk
          cases h1 : execF k body σ with
          | none => simp [h1] at hk
          | some σ₁ =>
              simp only [h1, Option.some_bind] at hk
              exact hX σ (Or.inr ⟨hb, σ₁, ⟨k, h1⟩, ih σ₁ s hk hQ⟩)
  intro σ h
  rcases h with ⟨s, ⟨k, hk⟩, hQ⟩
  exact main k σ s hk hQ

/-! ## 五、与 `RealWP.wp` 的连接（无 while 片段） -/

/-- 把无 while 的 `Stmt` 嵌入带 while 的 `StmtT`。 -/
def embed : Stmt → StmtT
  | .skip => .skip
  | .assign n e => .assign n e
  | .seq S₁ S₂ => .seq (embed S₁) (embed S₂)
  | .ite b S₁ S₂ => .ite b (embed S₁) (embed S₂)

/-- **嵌入语义可靠**：`execF` 停机结果与 `RealWP.exec` 一致。 -/
theorem embed_sound (S : Stmt) (k : ℕ) (σ s : State)
    (h : execF k (embed S) σ = some s) : exec S σ = s := by
  induction S generalizing k σ s with
  | skip =>
      cases k with
      | zero => simp [execF] at h
      | succ k => simpa [exec, execF] using h
  | assign n e =>
      cases k with
      | zero => simp [execF] at h
      | succ k => simpa [exec, execF] using h
  | seq S₁ S₂ ih₁ ih₂ =>
      cases k with
      | zero => simp [execF] at h
      | succ k =>
          simp only [embed, execF] at h
          cases h1 : execF k (embed S₁) σ with
          | none => simp [h1] at h
          | some σ₁ =>
              simp only [h1, Option.some_bind] at h
              rw [exec, ih₁ k σ σ₁ h1, ih₂ k σ₁ s h]
  | ite b S₁ S₂ ih₁ ih₂ =>
      cases k with
      | zero => simp [execF] at h
      | succ k =>
          simp only [embed, execF] at h
          by_cases hb : evalA σ b = 0
          · simp only [hb, if_true] at h
            rw [exec_ite_zero b S₁ S₂ σ hb, ih₂ k σ s h]
          · simp only [hb, if_false] at h
            rw [exec_ite_nonzero b S₁ S₂ σ hb, ih₁ k σ s h]

/-- **嵌入语义完备**：`RealWP.exec` 的结果可由足够大的燃料得到。 -/
theorem embed_complete (S : Stmt) (σ : State) :
    ∃ k, execF k (embed S) σ = some (exec S σ) := by
  induction S generalizing σ with
  | skip => exact ⟨1, rfl⟩
  | assign n e => exact ⟨1, rfl⟩
  | seq S₁ S₂ ih₁ ih₂ =>
      obtain ⟨k₁, hk₁⟩ := ih₁ σ
      obtain ⟨k₂, hk₂⟩ := ih₂ (exec S₁ σ)
      refine ⟨k₁ + k₂ + 1, ?_⟩
      show (execF (k₁ + k₂) (embed S₁) σ).bind
        (fun σ'' => execF (k₁ + k₂) (embed S₂) σ'') = some (exec S₂ (exec S₁ σ))
      rw [execF_mono k₁ (embed S₁) σ (exec S₁ σ) hk₁ k₂]
      simp only [Option.some_bind]
      rw [Nat.add_comm k₁ k₂, execF_mono k₂ (embed S₂) (exec S₁ σ) (exec S₂ (exec S₁ σ)) hk₂ k₁]
  | ite b S₁ S₂ ih₁ ih₂ =>
      by_cases hb : evalA σ b = 0
      · obtain ⟨k, hk⟩ := ih₂ σ
        refine ⟨k + 1, ?_⟩
        show (if evalA σ b = 0 then execF k (embed S₂) σ
              else execF k (embed S₁) σ) = some (exec (.ite b S₁ S₂) σ)
        rw [exec_ite_zero b S₁ S₂ σ hb, if_pos hb]
        exact hk
      · obtain ⟨k, hk⟩ := ih₁ σ
        refine ⟨k + 1, ?_⟩
        show (if evalA σ b = 0 then execF k (embed S₂) σ
              else execF k (embed S₁) σ) = some (exec (.ite b S₁ S₂) σ)
        rw [exec_ite_nonzero b S₁ S₂ σ hb, if_neg hb]
        exact hk

/-- **嵌入的停机语义与原语义一致**。 -/
theorem embed_denotes_iff (S : Stmt) (σ s : State) :
    Denotes (embed S) σ s ↔ exec S σ = s := by
  constructor
  · rintro ⟨k, hk⟩
    exact embed_sound S k σ s hk
  · intro h
    rw [← h]
    exact embed_complete S σ

/-- **与 `RealWP.wp` 的连接**：无 while 片段的全正确性 wp 就是 `RealWP.wp`。
（`wp S Q σ` 是 `def` 别名，其体 `Q (exec S σ)` 不透明，
直接 `rw [embed_denotes_iff …]` 会报 `did not find instance of the pattern exec S σ`
——须先 `unfold wp` 把目标暴露成 `Q (exec S σ)`。） -/
theorem wpT_embed (S : Stmt) (Q : State → Prop) :
    wpT (embed S) Q = wp S Q := by
  funext σ
  apply propext
  constructor
  · rintro ⟨s, hD, hQ⟩
    unfold wp
    rw [(embed_denotes_iff S σ s).1 hD]
    exact hQ
  · intro hQ
    exact ⟨exec S σ, (embed_denotes_iff S σ (exec S σ)).2 rfl, hQ⟩

end Lattice.Lib.Compiler.RealWhileTotalCorrectness
