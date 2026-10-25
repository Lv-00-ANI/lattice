import Mathlib
import Lattice.Lib.Compiler.RealEffectOrdering
import Lattice.Lib.Architectures.RealLoop
/-!
# LATTICE: 最弱前置条件（wp）与完备不变量

本文件把「最弱前置条件」形式化为确定性命令式语言的谓词变换，并证明其可靠性、相对完备性、
复合律与单调性；循环部分用显式循环不变量刻画，衔接 `RealLoop.invariant_preserves_iteration`。

  1. `AExp` / `evalA`：算术表达式（常量、变量、加、乘）与其在 `Lattice.Lib.Compiler.RealEffectOrdering.State = ℕ → ℤ` 上的求值；
  2. `Stmt`：命令（`skip`、`assign`、`seq`、`ite`）——刻意不含 `while`（`exec` 保持全函数）；
     循环不在语法层，而在第五节以显式步骤函数 + 不变量刻画，覆盖部分正确性，不含终止性；
  3. `exec`：确定性全函数语义；配 `exec_skip`、`exec_assign`、`exec_seq`、`exec_ite_zero/nonzero`；
  4. `wp S Q = fun σ => Q (exec S σ)`：最弱前置条件；
  5. `wp_sound`：Hoare 三元组 `{wp S Q} S {Q}` 的可靠性；
  6. `wp_complete`：**相对完备性** —— 任何可靠前置都强于 `wp`（即 `wp` 是最强可靠前置）；
  7. `wp_composition`：顺序复合的 wp 组合律 `wp (seq S T) Q = wp S (wp T Q)`；
  8. `wp_monotone`：`wp` 关于后置条件单调；
  9. `whileStep` / `LoopInvariantWp` / `loop_invariant_wp` / `loop_exit_wp`：
   显式循环不变量刻画，并回收 `RealLoop.invariant_preserves_iteration`。

诚实标注（无 sorry / axiom / admit）：
- **循环语义**：为保持 `exec` 为全函数并避免燃料论证，`Stmt` 刻意不含 `while`；
  循环不在语法层，而在第五节以抽象步骤函数 `f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State` + 不变量 `I` 刻画
  （`whileStep b f`、`LoopInvariantWp`），这覆盖了部分正确性所需的一切，
  但不含终止性/全正确性。
- `wp_complete` 是**相对完备性**：它断言 `wp` 在语义层面是最强可靠前置，
  不含算术（Peano）完备性的可表达性论证。
- `Lattice.Lib.Compiler.RealEffectOrdering.State = ℕ → ℤ` 只是具体的可计算状态模型，结论与状态类型无关。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealWP
/-! ## 一、算术表达式 -/

/-- 算术表达式。 -/
inductive AExp where
  | const (n : ℤ) : AExp
  | var (n : ℕ) : AExp
  | add (e₁ e₂ : AExp) : AExp
  | mul (e₁ e₂ : AExp) : AExp

/-- 算术表达式求值。 -/
def evalA (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) : AExp → ℤ
  | .const n => n
  | .var n => σ n
  | .add e₁ e₂ => evalA σ e₁ + evalA σ e₂
  | .mul e₁ e₂ => evalA σ e₁ * evalA σ e₂

/-! ## 二、命令与确定性语义 -/

/-- 命令语言（不含 `while`，见文件头诚实标注）。 -/
inductive Stmt where
  | skip : Stmt
  | assign (n : ℕ) (e : AExp) : Stmt
  | seq (S₁ S₂ : Stmt) : Stmt
  | ite (b : AExp) (S₁ S₂ : Stmt) : Stmt

/-- 确定性大步语义（全函数）。 -/
def exec : Stmt → Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State
  | .skip, σ => σ
  | .assign n e, σ => Function.update σ n (evalA σ e)
  | .seq S₁ S₂, σ => exec S₂ (exec S₁ σ)
  | .ite b S₁ S₂, σ => if evalA σ b = 0 then exec S₂ σ else exec S₁ σ

@[simp] theorem exec_skip (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) : exec .skip σ = σ := rfl

@[simp] theorem exec_assign (n : ℕ) (e : AExp) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) :
    exec (.assign n e) σ = Function.update σ n (evalA σ e) := rfl

@[simp] theorem exec_seq (S₁ S₂ : Stmt) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) :
    exec (.seq S₁ S₂) σ = exec S₂ (exec S₁ σ) := rfl

theorem exec_ite_zero (b : AExp) (S₁ S₂ : Stmt) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (h : evalA σ b = 0) :
    exec (.ite b S₁ S₂) σ = exec S₂ σ := by
  simp [exec, h]

theorem exec_ite_nonzero (b : AExp) (S₁ S₂ : Stmt) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (h : evalA σ b ≠ 0) :
    exec (.ite b S₁ S₂) σ = exec S₁ σ := by
  simp [exec, h]

/-! ## 三、最弱前置条件 wp -/

/-- **最弱前置条件**：`wp S Q σ` 表示「从 `σ` 执行 `S` 后必满足 `Q`」。 -/
def wp (S : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop := fun σ => Q (exec S σ)

/-- wp 的赋值律。 -/
theorem wp_assign (n : ℕ) (e : AExp) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) :
    wp (.assign n e) Q σ ↔ Q (Function.update σ n (evalA σ e)) := Iff.rfl

/-- wp 的条件律（条件为 0 走 `S₂` 分支）。 -/
theorem wp_ite_zero (b : AExp) (S₁ S₂ : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State)
    (h : evalA σ b = 0) : wp (.ite b S₁ S₂) Q σ ↔ wp S₂ Q σ := by
  unfold wp
  rw [exec_ite_zero b S₁ S₂ σ h]

/-- wp 的条件律（条件非 0 走 `S₁` 分支）。 -/
theorem wp_ite_nonzero (b : AExp) (S₁ S₂ : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State)
    (h : evalA σ b ≠ 0) : wp (.ite b S₁ S₂) Q σ ↔ wp S₁ Q σ := by
  unfold wp
  rw [exec_ite_nonzero b S₁ S₂ σ h]

/-! ## 四、可靠性、完备性、复合律、单调性 -/

/-- **wp 可靠**：`{wp S Q} S {Q}`（Hoare 三元组的可靠性，按确定性语义即定义展开）。 -/
theorem wp_sound (S : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (h : wp S Q σ) :
    Q (exec S σ) := h

/-- **wp 相对完备**：任何可靠前置 `P`（`P σ ⟹ Q (exec S σ)`）都被 `wp S Q` 蕴含，
即 `wp` 是最强可靠前置。 -/
theorem wp_complete (S : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (P : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop)
    (h : ∀ σ, P σ → Q (exec S σ)) : ∀ σ, P σ → wp S Q σ :=
  fun σ hP => h σ hP

/-- **wp 复合律**：`wp (S; T) Q = wp S (wp T Q)`。 -/
theorem wp_composition (S T : Stmt) (Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) :
    wp (.seq S T) Q = wp S (wp T Q) := rfl

/-- **wp 单调**：后置条件变强则前置条件变强。 -/
theorem wp_monotone (S : Stmt) {Q Q' : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop} (h : ∀ σ, Q σ → Q' σ)
    (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (hσ : wp S Q σ) : wp S Q' σ :=
  h _ hσ

/-- **wp 与合取**：`wp S (Q ∧ Q') = wp S Q ∧ wp S Q'`（对偶，逐点）。 -/
theorem wp_and (S : Stmt) (Q Q' : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) :
    wp S (fun τ => Q τ ∧ Q' τ) σ ↔ wp S Q σ ∧ wp S Q' σ := Iff.rfl

/-- **wp 与蕴含**：`wp S (Q → Q') σ` 蕴含 `wp S Q σ → wp S Q' σ`。 -/
theorem wp_imp (S : Stmt) (Q Q' : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) :
    wp S (fun τ => Q τ → Q' τ) σ → wp S Q σ → wp S Q' σ :=
  fun h hq => h hq

/-! ## 五、循环不变量与 wp 刻画 -/

/-- 循环体（以抽象步骤函数 `f` 表示）与守卫 `b` 的一步：守卫为假不动，为真走 `f`。 -/
def whileStep (b : AExp) (f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) : Lattice.Lib.Compiler.RealEffectOrdering.State :=
  if evalA σ b = 0 then σ else f σ

/-- 守卫为真：执行步骤函数。 -/
theorem whileStep_body {b : AExp} {f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State} {σ : Lattice.Lib.Compiler.RealEffectOrdering.State} (h : evalA σ b ≠ 0) :
    whileStep b f σ = f σ := by
  unfold whileStep
  exact if_neg h

/-- 守卫为假：保持不动。 -/
theorem whileStep_exit {b : AExp} {f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State} {σ : Lattice.Lib.Compiler.RealEffectOrdering.State} (h : evalA σ b = 0) :
    whileStep b f σ = σ := by
  unfold whileStep
  exact if_pos h

/-- **循环不变量的 wp 刻画**：`I` 是循环不变量、退出时蕴含 `Q`、
且 `I` 在循环体下保持。 -/
def LoopInvariantWp (b : AExp) (f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State) (I Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop) : Prop :=
  (∀ σ, I σ → evalA σ b = 0 → Q σ) ∧
  (∀ σ, I σ → evalA σ b ≠ 0 → I (f σ))

/-- **循环不变量保持（衔接 `RealLoop.invariant_preserves_iteration`）**：
若 `LoopInvariantWp b f I Q` 且 `I σ`，则任意步数后 `I` 仍成立。 -/
theorem loop_invariant_wp (b : AExp) (f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State) (I Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop)
    (h : LoopInvariantWp b f I Q) (fuel : ℕ) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (hI : I σ) :
    I (iterate (whileStep b f) fuel σ) := by
  apply invariant_preserves_iteration I (whileStep b f) fuel σ hI
  intro τ hτ
  by_cases hb : evalA τ b = 0
  · rw [whileStep_exit hb]
    exact hτ
  · rw [whileStep_body hb]
    exact h.2 τ hτ hb

/-- **退出时的 wp 刻画**：若循环在 `σ` 上（经过 `fuel` 步）退出且不变量成立，
则后置条件 `Q` 成立。 -/
theorem loop_exit_wp (b : AExp) (f : Lattice.Lib.Compiler.RealEffectOrdering.State → Lattice.Lib.Compiler.RealEffectOrdering.State) (I Q : Lattice.Lib.Compiler.RealEffectOrdering.State → Prop)
    (h : LoopInvariantWp b f I Q) (fuel : ℕ) (σ : Lattice.Lib.Compiler.RealEffectOrdering.State) (hI : I σ)
    (hb : evalA (iterate (whileStep b f) fuel σ) b = 0) :
    Q (iterate (whileStep b f) fuel σ) :=
  h.1 _ (loop_invariant_wp b f I Q h fuel σ hI) hb

end Lattice.Lib.Compiler.RealWP
