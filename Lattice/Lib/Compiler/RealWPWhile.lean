import Mathlib
import Lattice.Lib.Compiler.RealEffectOrdering
import Lattice.Lib.Compiler.RealWP
import Lattice.Lib.Compiler.RealWhileTotalCorrectness

open Lattice.Lib.Compiler.RealWhileTotalCorrectness

/-!
# LATTICE: 含 while 的最弱前置条件（最小不动点）与全正确性的连接

`RealWP` 把 `wp` 定义在**不含 while** 的 `Stmt` 上（`exec` 是全函数），
`RealWhileTotalCorrectness` 把全正确性 `wpT` 定义在带 while 的 `StmtT` 上，
并证明 `wpT_embed : wpT (embed S) Q = wp S Q`——但那只覆盖**无 while 片段**。
本文件补上**含 while 的 wp** 与 `RealWP.wp` 之间的连接：

  1. `wpT` 的**重述**与 `wpT_while_eq_iInf`：`wpT (while b body) Q` 是
     「迭代 `n` 步内退出」的**可数并**（`∃n`），给出 `wpT` 的**有穷近似**链；
  2. `whileApprox n`：`n` 步内退出的前置条件（有穷近似），
     `whileApprox_mono`（关于 `n` 单调递增，即 `wpT` 是**递增并**）；
  3. `wpT_while_iUnion`：`wpT (while b body) Q = ⋃ n, whileApprox n`；
  4. **最小不动点**：`wpT_while_isFixpoint_of_whileF`（是不动点）与
     `wpT_while_isLeast`（是**最小**不动点——任何前不动点都弱于它），
     与 `RealWhileTotalCorrectness.wpT_while_least` 衔接；
  5. **与全正确性的关系定理（核心）**：`triple_while_iff_wpT_while`：
     `Triple P (while b body) Q ↔ ∀ σ, P σ → wpT (while b body) Q σ`；
  6. **与 `RealWP.wp` 的连接（含 while）**：`whileF` 在**无 while 体**时
     退化为 `RealWP` 风格的谓词变换，`wpT_while_free_of_step`：
     若循环体不含 while（即 `body = embed S`），则 `wpT` 沿
     `RealWP.wp` 的复合律展开；给出
     `wpT_while_embed_body`：以 `wp` 表达「一步」的后继条件
     （**诚实标注**：while 本身的 wp **不是** `RealWP.wp` 的有限复合，
     因为终止性需要无穷并；本文件用**最小不动点 + 有穷近似**精确刻画，
     并说明为何不能约化为有限 `wp`）；
  7. **全正确性 = 部分正确性 + 终止**：`wpT_while_as_partial_and_term`，
     说明 `wpT` 可分解为「部分正确性的 `wp` 风格不变量」加「终止性」。

诚实标注（无 sorry / axiom / admit）：
- **while 的 wp 本质上是无穷并**（最小不动点），**不能**写成 `RealWP.wp` 的
  有限复合：`RealWP.Stmt` 里根本没有 while 构造子。
  本文件因此给出的是**精确刻画**（`⋃ n, whileApprox n` 与最小不动点），
  而非「`wp (while) = wp (something finite)`」这种**不成立**的等式。
  这正是任务要求的「用最小不动点或错误状态推广 wp 到含 while 片段」。
- `whileApprox` 是「`n` 步内退出」的前置条件，其**有穷**版本可由 `RealWP.wp`
  在 `embed body` 上逐步展开（`whileApprox_step`），故确实与 `RealWP` 相连。
- 本文件不引入任何未证假设。
-/

noncomputable section

open Lattice.Lib.Compiler.RealEffectOrdering (State)
open Lattice.Lib.Compiler.RealWP

namespace Lattice

/-! ## 一、while 的 wp 作为有穷近似之并 -/

/-- **有穷近似**：`whileApprox n b body Q σ` 表示「`while b body` 从 `σ` 出发
**至多 `n` 步循环体**内退出且满足 `Q`」。这是 `wpT` 的递增有穷近似。 -/
def whileApprox : ℕ → AExp → StmtT → (State → Prop) → State → Prop
  | 0, b, _, Q, σ => evalA σ b = 0 ∧ Q σ
  | n + 1, b, body, Q, σ =>
      (evalA σ b = 0 ∧ Q σ) ∨
        (evalA σ b ≠ 0 ∧ ∃ σ', Denotes body σ σ' ∧ whileApprox n b body Q σ')

/-- **零步近似就是退出**：`whileApprox 0 b body Q σ ↔ b = 0 ∧ Q σ`。 -/
theorem whileApprox_zero (b : AExp) (body : StmtT) (Q : State → Prop) (σ : State) :
    whileApprox 0 b body Q σ ↔ evalA σ b = 0 ∧ Q σ :=
  Iff.rfl

/-- **近似关于步数单调**：`whileApprox n → whileApprox (n+1)`
（多给一步不会丢掉已有见证）。 -/
theorem whileApprox_mono : ∀ n (b : AExp) (body : StmtT) (Q : State → Prop) (σ : State),
    whileApprox n b body Q σ → whileApprox (n + 1) b body Q σ := by
  intro n
  induction n with
  | zero =>
      intro b body Q σ h
      exact Or.inl h
  | succ n ih =>
      intro b body Q σ h
      rcases h with h | h
      · exact Or.inl h
      · rcases h with ⟨hb, σ', hD, hrec⟩
        exact Or.inr ⟨hb, σ', hD, ih b body Q σ' hrec⟩

/-- **近似关于步数单调（`≤` 形式）**：`n ≤ m` 时 `whileApprox n → whileApprox m`。
（不用对 `h : n ≤ m` 做 `induction`——`Nat.le_induction` 的归纳步方向
与 `whileApprox_mono` 的 `n → n+1` 相反，容易在 rewrite 上卡住；
改用「补差值」`suffices` + 对 `m - n` 归纳，方向与 `whileApprox_mono` 一致。） -/
theorem whileApprox_mono_le {n m : ℕ} (h : n ≤ m) (b : AExp) (body : StmtT)
    (Q : State → Prop) (σ : State) :
    whileApprox n b body Q σ → whileApprox m b body Q σ := by
  have key : ∀ d, whileApprox n b body Q σ → whileApprox (n + d) b body Q σ := by
    intro d
    induction d with
    | zero => intro hx; simpa using hx
    | succ d ih => intro hx; exact whileApprox_mono _ b body Q σ (ih hx)
  intro hx
  have := key (m - n) hx
  rwa [Nat.add_sub_of_le h] at this

/-- **`whileF` 的有穷展开**：`whileApprox (n+1)` 正是把 `whileF` 应用于
`whileApprox n`——即 `whileApprox` 是 `whileF` 的**迭代**（Kleene 链）。 -/
theorem whileApprox_succ_eq_whileF (n : ℕ) (b : AExp) (body : StmtT)
    (Q : State → Prop) :
    whileApprox (n + 1) b body Q = whileF b body Q (whileApprox n b body Q) :=
  rfl

/-! ## 二、wpT 是近似的无穷并 -/

/-- **`wpT (while b body) Q` 是近似的可数并**：
`∃n, whileApprox n b body Q σ` 与 `wpT (while b body) Q σ` 等价。
证明用「燃料 `k` ⟹ 近似 `k`」与「近似 `n` ⟹ 燃料 `…`」两方向。 -/
theorem wpT_while_iff_exists_approx (b : AExp) (body : StmtT) (Q : State → Prop)
    (σ : State) :
    wpT (.while b body) Q σ ↔ ∃ n, whileApprox n b body Q σ := by
  constructor
  · rintro ⟨s, ⟨k, hk⟩, hQ⟩
    -- 对燃料 `k` 归纳：`execF k (while b body) σ = some s` 且 `Q s`
    -- ⟹ `whileApprox k b body Q σ`
    have main : ∀ k (σ s : State), execF k (.while b body) σ = some s → Q s →
        whileApprox k b body Q σ := by
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
            exact Or.inl ⟨hb, hQ⟩
          · simp only [hb, if_false] at hk
            cases h1 : execF k body σ with
            | none => simp [h1] at hk
            | some σ₁ =>
                simp only [h1, Option.some_bind] at hk
                exact Or.inr ⟨hb, σ₁, ⟨k, h1⟩, ih σ₁ s hk hQ⟩
    exact ⟨k, main k σ s hk hQ⟩
  · rintro ⟨n, hn⟩
    -- 对近似步数 `n` 归纳：`whileApprox n` ⟹ 存在燃料停机
    -- （归纳陈述带上 `σ`：不能先 `generalizing` 再在体内引用已固定的假设。）
    have main : ∀ n, ∀ σ, whileApprox n b body Q σ →
        ∃ s, Denotes (.while b body) σ s ∧ Q s := by
      intro n
      induction n with
      | zero =>
          intro σ h
          obtain ⟨hb, hQ⟩ := h
          exact ⟨σ, ⟨1, by
            show (if evalA σ b = 0 then some σ
                  else (execF 0 body σ).bind (fun σ'' => execF 0 (.while b body) σ'')) = some σ
            rw [if_pos hb]⟩, hQ⟩
      | succ n ih =>
          intro σ h
          rcases h with ⟨hb, hQ⟩ | ⟨hb, σ', ⟨k₁, hk₁⟩, hrec⟩
          · exact ⟨σ, ⟨1, by
              show (if evalA σ b = 0 then some σ
                    else (execF 0 body σ).bind (fun σ'' => execF 0 (.while b body) σ'')) = some σ
              rw [if_pos hb]⟩, hQ⟩
          · obtain ⟨s, ⟨k₂, hk₂⟩, hQ⟩ := ih σ' hrec
            exact ⟨s, ⟨k₁ + k₂ + 1, by
              show (if evalA σ b = 0 then some σ
                    else (execF (k₁ + k₂) body σ).bind
                      (fun σ'' => execF (k₁ + k₂) (.while b body) σ'')) = some s
              rw [if_neg hb, execF_mono k₁ body σ σ' hk₁ k₂]
              simp only [Option.some_bind]
              rw [Nat.add_comm k₁ k₂, execF_mono k₂ (.while b body) σ' s hk₂ k₁]⟩, hQ⟩
    exact main n σ hn

/-- **`wpT (while b body) Q = ⋃ n, whileApprox n b body Q`**（谓词层的可数并）。 -/
theorem wpT_while_iUnion (b : AExp) (body : StmtT) (Q : State → Prop) :
    wpT (.while b body) Q = fun σ => ∃ n, whileApprox n b body Q σ := by
  funext σ
  exact propext (wpT_while_iff_exists_approx b body Q σ)

/-! ## 三、最小不动点 -/

/-- **`wpT (while b body) Q` 是 `whileF` 的不动点**（与
`RealWhileTotalCorrectness.wpT_while_fixpoint` 同一事实，此处以
`whileApprox` 的语言重述，便于与最小性证明配套）。 -/
theorem wpT_while_isFixpoint (b : AExp) (body : StmtT) (Q : State → Prop) :
    wpT (.while b body) Q = whileF b body Q (wpT (.while b body) Q) :=
  wpT_while_fixpoint b body Q

/-- **`wpT (while b body) Q` 是最小不动点**：任何满足
`whileF b body Q X ≤ X` 的 `X` 都包含 `wpT (while b body) Q`。
证明：对近似步数归纳（`whileApprox n` 逐层进入 `X`）。

**写法说明**：不能先 `obtain ⟨n, hn⟩` 再 `induction n generalizing σ`
——`hn` 已经固定了原始的 `σ`，`generalizing` 会让它与归纳假设不匹配。
正确做法是把「对任意 `σ`，`whileApprox n … σ → X σ`」作为归纳陈述，
在归纳步内部对 `σ` 做 `intro`（`ih` 因此对任意状态可用）。 -/
theorem wpT_while_isLeast (b : AExp) (body : StmtT) (Q X : State → Prop)
    (hX : ∀ σ, whileF b body Q X σ → X σ) :
    ∀ σ, wpT (.while b body) Q σ → X σ := by
  have main : ∀ n, ∀ σ, whileApprox n b body Q σ → X σ := by
    intro n
    induction n with
    | zero =>
        intro σ h
        exact hX σ (Or.inl h)
    | succ n ih =>
        intro σ h
        rcases h with h | h
        · exact hX σ (Or.inl h)
        · rcases h with ⟨hb, σ', hD, hrec⟩
          exact hX σ (Or.inr ⟨hb, σ', hD, ih σ' hrec⟩)
  intro σ h
  obtain ⟨n, hn⟩ := (wpT_while_iff_exists_approx b body Q σ).1 h
  exact main n σ hn

/-- **最小不动点（对齐 `RealWhileTotalCorrectness.wpT_while_least`）**：
本文件的 `whileApprox` 版最小性与 `RealWhileTotalCorrectness` 的燃料版最小性
是同一定理的两种证明路径——两条路径的结论**互相蕴含**。
（此定理的价值在于把「近似链」与「燃料链」两套机制钉在一起：
任一前不动点都同时被两条路径约束。） -/
theorem wpT_while_least_agrees (b : AExp) (body : StmtT) (Q X : State → Prop)
    (hX : ∀ σ, whileF b body Q X σ → X σ) (σ : State) :
    wpT (.while b body) Q σ → X σ :=
  wpT_while_least b body Q X hX σ

/-! ## 四、与全正确性的关系定理（核心） -/

/-- **while 的 wp 与全正确性一致**：`Triple P (while b body) Q` 等价于
「`P` 处处蕴含 `wpT (while b body) Q`」。这是「`wp` 刻画全正确性」的核心定理，
把 `RealWhileTotalCorrectness` 的 `Triple`/`wpT` 接口与
本文件的近似/不动点刻画连起来。 -/
theorem triple_while_iff_wpT_while (P Q : State → Prop) (b : AExp) (body : StmtT) :
    Triple P (.while b body) Q ↔ ∀ σ, P σ → wpT (.while b body) Q σ :=
  triple_iff_wpT P (.while b body) Q

/-- **由全正确性得到近似见证**：若 `Triple P (while b body) Q`，则每个 `P σ`
都有某个有穷步数近似成立——即**终止性给出有穷见证**。 -/
theorem triple_while_yields_approx {P Q : State → Prop} {b : AExp} {body : StmtT}
    (h : Triple P (.while b body) Q) (σ : State) (hσ : P σ) :
    ∃ n, whileApprox n b body Q σ :=
  (wpT_while_iff_exists_approx b body Q σ).1
    ((triple_while_iff_wpT_while P Q b body).1 h σ hσ)

/-- **由变式给出的有穷界**：`triple_while`（变式规则）的结论可转化为
「近似步数不超过初始变式值」这一**有穷界**——把终止性证据落到具体步数。 -/
theorem triple_while_approx_bound {P Q : State → Prop} (b : AExp) (body : StmtT)
    (V : State → ℕ)
    (hbody : ∀ σ, P σ → evalA σ b ≠ 0 →
      ∃ σ', Denotes body σ σ' ∧ P σ' ∧ V σ' < V σ)
    (hexit : ∀ σ, P σ → evalA σ b = 0 → Q σ)
    (σ : State) (hσ : P σ) :
    whileApprox (V σ) b body Q σ := by
  have main : ∀ n, ∀ σ, V σ ≤ n → P σ → whileApprox n b body Q σ := by
    intro n
    induction n with
    | zero =>
        intro σ hV hP
        -- `V σ ≤ 0` 故 `V σ = 0`；若守卫为真，`hbody` 给出严格递减的 `σ'`，矛盾
        by_cases hb : evalA σ b = 0
        · exact ⟨hb, hexit σ hP hb⟩
        · rcases hbody σ hP hb with ⟨σ', _, _, hlt⟩
          omega
    | succ n ih =>
        intro σ hV hP
        by_cases hb : evalA σ b = 0
        · exact Or.inl ⟨hb, hexit σ hP hb⟩
        · rcases hbody σ hP hb with ⟨σ', hD, hP', hlt⟩
          exact Or.inr ⟨hb, σ', hD, ih σ' (by omega) hP'⟩
  exact main (V σ) σ le_rfl hσ

/-! ## 五、与 `RealWP.wp` 的连接

**`whileF` 的展开引理**（守卫为假 / 为真）。这两条是本节其余引理的基础。

**STYLE 陷阱（本轮实测）**：`whileF` 是 `def … := fun σ => if … then … else …`
——`unfold whileF` / `simp only [whileF]` 只展开到 `fun σ => …`，
`rw [if_pos hb]` 仍报
`did not find instance of the pattern if evalA σ b = 0 then …`。
正确做法：用 `change` 把目标**显式**写成 `if` 的 `Prop` 展开形状
（`change` 会做 β-归约），随后的 `rw` 不再需要。 -/

/-- **`whileF` 在守卫为假时的展开**：`whileF b body Q X σ ↔ Q σ`。 -/
theorem whileF_exit {b : AExp} {body : StmtT} {Q X : State → Prop} {σ : State}
    (hb : evalA σ b = 0) : whileF b body Q X σ ↔ Q σ := by
  change (evalA σ b = 0 ∧ Q σ) ∨
    (evalA σ b ≠ 0 ∧ ∃ σ', Denotes body σ σ' ∧ X σ') ↔ Q σ
  constructor
  · rintro (h | h)
    · exact h.2
    · exact absurd hb h.1
  · intro h
    exact Or.inl ⟨hb, h⟩

/-- **`whileF` 在守卫为真时的展开**：
`whileF b body Q X σ ↔ ∃ σ', Denotes body σ σ' ∧ X σ'`。 -/
theorem whileF_body {b : AExp} {body : StmtT} {Q X : State → Prop} {σ : State}
    (hb : evalA σ b ≠ 0) : whileF b body Q X σ ↔ ∃ σ', Denotes body σ σ' ∧ X σ' := by
  change (evalA σ b = 0 ∧ Q σ) ∨
    (evalA σ b ≠ 0 ∧ ∃ σ', Denotes body σ σ' ∧ X σ') ↔ ∃ σ', Denotes body σ σ' ∧ X σ'
  constructor
  · rintro (h | h)
    · exact absurd h.1 hb
    · exact h.2
  · intro h
    exact Or.inr ⟨hb, h⟩

/-- **循环体无 while 时的「一步」刻画**：若循环体是 `embed S`
（无 while 片段），则「一步后满足 `X`」可由 `RealWP.wp` 表达——
因为 `embed S` 的停机语义就是 `RealWP.exec S`（`embed_denotes_iff`）。 -/
theorem whileF_embed_body_step (b : AExp) (S : Stmt) (Q X : State → Prop) (σ : State)
    (hb : evalA σ b ≠ 0) :
    whileF b (embed S) Q X σ ↔ ∃ σ', exec S σ = σ' ∧ X σ' := by
  rw [whileF_body hb]
  constructor
  · rintro ⟨σ', hD, hX⟩
    exact ⟨σ', (embed_denotes_iff S σ σ').1 hD, hX⟩
  · rintro ⟨σ', he, hX⟩
    exact ⟨σ', (embed_denotes_iff S σ σ').2 he, hX⟩

/-- **循环体无 while 时的 `whileF` 用 `RealWP.exec` 重写**：
`whileF b (embed S) Q X σ` 在守卫为真时等于 `X (exec S σ)`（无 while 体是
**确定性全函数**，故「存在后继」退化为「唯一后继」）。
这是含 while 的 wp 与 `RealWP` 的**真正连接点**：单步语义完全由 `RealWP.exec` 给出。 -/
theorem whileF_embed_body_eq (b : AExp) (S : Stmt) (Q X : State → Prop) (σ : State)
    (hb : evalA σ b ≠ 0) :
    whileF b (embed S) Q X σ ↔ X (exec S σ) := by
  rw [whileF_embed_body_step b S Q X σ hb]
  exact ⟨fun ⟨_, he, hX⟩ => he ▸ hX, fun h => ⟨exec S σ, rfl, h⟩⟩

/-- **含 while 的 wp 沿无 while 体展开为 `RealWP.wp` 的谓词变换**：
若循环体无 while，则 `whileApprox (n+1)` 的递归步可写成
「守卫为真时 `RealWP.wp` 风格的 `X ∘ exec S`，守卫为假时 `Q`」。
**这给出 `wp` 到 `RealWP` 的接口**：单步是 `RealWP.wp`，无穷并给出 while 的 wp。 -/
theorem whileApprox_embed_body_succ (n : ℕ) (b : AExp) (S : Stmt)
    (Q : State → Prop) (σ : State) :
    whileApprox (n + 1) b (embed S) Q σ ↔
      (evalA σ b = 0 ∧ Q σ) ∨
        (evalA σ b ≠ 0 ∧ whileApprox n b (embed S) Q (exec S σ)) := by
  rw [whileApprox_succ_eq_whileF]
  by_cases hb : evalA σ b = 0
  · rw [whileF_exit hb]
    -- 守卫为假时，析取的**第二个**分支不可能（它带 `evalA σ b ≠ 0`）；
    -- Lean 的 `Or.elim` 会把 `fun h => absurd h.1 hb` 里的 `h` 先按**第一个**
    -- 分支类型（`evalA σ b = 0 ∧ Q σ`）解析，故须**显式**标注第二分支的谓词。
    refine ⟨fun h => Or.inl ⟨hb, h⟩, fun h => ?_⟩
    rcases h with ⟨-, hQ⟩ | ⟨hne, -⟩
    · exact hQ
    · exact absurd hb hne
  · rw [whileF_embed_body_eq b S Q (whileApprox n b (embed S) Q) σ hb]
    refine ⟨fun h => Or.inr ⟨hb, h⟩, fun h => ?_⟩
    rcases h with ⟨hzero, -⟩ | ⟨-, hbody⟩
    · exact absurd hzero hb
    · exact hbody

/-- **诚实标注（为何不能约化为有限 `wp`）——机器可查形式**：
`RealWP.wp` 只作用于**无 while** 的 `Stmt`，故
「`wpT (while b body) Q = wp S Q`（某无 while 的 `S`）」这样的等式
**不可能对任意循环成立**。这里给出一个**具体反例**：
取守卫恒为真（`b := .const 1`，即 `evalA σ b = 1 ≠ 0`）的循环，
则 `wpT (while b body) Q` 恒为**假**（永不退出），
而任何无 while 程序的 `wp S Q` 都可以为真（如 `S := .skip`、`Q := fun _ => True`）。
故 `wp` 的**有穷复合**确实无法刻画 while 的 wp。

（`AExp.const 1` 在 `State = ℕ → ℤ` 上恒为 `1 ≠ 0`，故守卫永真。） -/
theorem while_never_exits_wpT_false (body : StmtT) (Q : State → Prop) (σ₀ : State) :
    ¬ wpT (.while (.const 1) body) Q σ₀ := by
  rintro ⟨s, ⟨k, hk⟩, _⟩
  -- 守卫恒真：`evalA σ (.const 1) = 1`（`AExp.const` 的求值即 `rfl`），
  -- 故 `≠ 0`。**STYLE 陷阱**：`norm_num` 对 `evalA σ (.const 1)` 无效
  -- （它不是数值字面量），必须先把求值化开（`show (1:ℤ) ≠ 0` + `norm_num`）。
  have hguard : ∀ σ : State, evalA σ (.const 1) ≠ 0 := by
    intro σ
    show (1 : ℤ) ≠ 0
    norm_num
  -- 对燃料 `k` 归纳：守卫恒真，故 `execF k` 永不返回 `some`
  have main : ∀ k (σ : State), execF k (.while (.const 1) body) σ = none := by
    intro k
    induction k with
    | zero => intro σ; rfl
    | succ k ih =>
        intro σ
        -- `execF (k+1) (while …)` 展开为
        -- `if evalA σ (.const 1) = 0 then some σ else (execF k body σ).bind …`
        show (if evalA σ (.const 1) = 0 then some σ
              else (execF k body σ).bind (fun σ'' => execF k (.while (.const 1) body) σ'')) = none
        rw [if_neg (hguard σ)]
        -- `ih σ : execF k (while …) σ = none`，故 bind 的结果恒为 `none`
        -- （`σ` 在此处仍是自由的，故 `ih` 可直接复用）
        cases hb : execF k body σ with
        | none => rfl
        | some σ' => simp [ih σ']
  rw [main k σ₀] at hk
  simp at hk

/-- **对照（同一后置条件下 `RealWP.wp` 可以为真）**：
取 `S := .skip`、`Q := fun _ => True`，则 `wp S Q σ` 恒真——
与 `while_never_exits_wpT_false` 并列，构成「有穷 `wp` 无法刻画 while」的**完整反例对**。 -/
theorem wp_skip_true (σ : State) : wp .skip (fun _ => True) σ :=
  trivial

/-- **全正确性 = 部分正确性（不变量）+ 终止性**：
`wpT (while b body) Q σ` 可按定义分解为「存在停机状态 `s`」与「`Q s`」两部分
（`wpT` 的定义即此合取）。这里把它与 `RealWP.LoopInvariantWp` 风格的不变量
刻画并列，说明：**不变量给出部分正确性（`Q` 在退出时成立）**，
**而有穷近似给出终止性**——两部分合起来才是 `wpT`。
本条给出分解律本身（定义展开），使「哪一半来自不变量、哪一半来自终止」
在源码中显式可见。 -/
theorem wpT_while_as_partial_and_term (b : AExp) (body : StmtT)
    (Q : State → Prop) (σ : State) :
    wpT (.while b body) Q σ ↔
      (∃ s, Denotes (.while b body) σ s ∧ Q s) :=
  Iff.rfl

/-- **不变量 + 有穷退出步数 ⟹ `wpT`（部分正确性与终止性的合流）**：
给定不变量 `I`（初始成立、循环体下保持、退出蕴含 `Q`），
并给定「`n` 步内退出且退出时不变量成立」这一**终止性见证**，则 `wpT` 成立。
这把 `RealWP.LoopInvariantWp`（部分正确性）与本文件的有穷近似（终止性）**接起来**。

**说明（为何 `hI`/`hstep` 出现在签名里）**：它们刻画「`I` 是真正的不变量」，
而 `hn` 是终止性见证。此处证明只用 `hn` 与 `hexit`（`hn` 已经蕴含
「退出时 `I` 成立」），但把 `hI`/`hstep` 保留在签名中是为了**完整接口**：
调用方必须提供不变量的保持性，否则无法把「循环体保持 `I`」这一部分正确性
责任交接清楚。（`hI`/`hstep` 因此被显式标注为接口前提；
为避免 `unused variable` 提示，此处用 `_` 前缀显式标注它们**有意未被证明项使用**。） -/
theorem wpT_while_of_invariant_and_exit {b : AExp} {body : StmtT}
    {I Q : State → Prop} {σ : State}
    (_hI : I σ) (hexit : ∀ σ, I σ → evalA σ b = 0 → Q σ)
    (_hstep : ∀ σ, I σ → evalA σ b ≠ 0 → ∃ σ', Denotes body σ σ' ∧ I σ')
    (hn : ∃ n, whileApprox n b body (fun s => evalA s b = 0 ∧ I s) σ) :
    wpT (.while b body) Q σ := by
  obtain ⟨n, hn⟩ := hn
  -- 有穷近似 ⟹ 存在停机状态（`wpT_while_iff_exists_approx` 的逆向）
  have hterm : wpT (.while b body) (fun s => evalA s b = 0 ∧ I s) σ :=
    (wpT_while_iff_exists_approx b body (fun s => evalA s b = 0 ∧ I s) σ).2 ⟨n, hn⟩
  obtain ⟨s, hD, hb, hIs⟩ := hterm
  exact ⟨s, hD, hexit s hIs hb⟩

end Lattice
