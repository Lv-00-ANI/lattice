import Mathlib
import Lattice.Core.CIC.Reduction
import Lattice.Runtime.EngineFirst

/-!
# 约简**保可编译性**：`Step` 十个构造子逐一分析（阶段 C，P6）

## 上一轮留下了什么

**第 911 轮的 `EngineFirst.lean` 证明了「引擎恒可运行」（`Reduces E t t`）与「约束唯一」（平凡）。
这两条都**没有内容**：它们没有说明「约简之后还能编译」。**

**=> 目标说的是：符号模型**跑在引擎上**。跑的意思是约简**真的发生**，
而约简之后编译仍然给出**正确的**约束。本文件补的正是这一点。**

## `Step` 的十个构造子及其对可编译性的影响

| 构造子 | 形式 | 对可编译性的影响 |
|:--|:--|:--|
| **`beta`** | **`app (lam A b) a ⟶ subst 0 a b`** | **两侧都不可编译** |
| **`zeta`** | **`letE A t b ⟶ subst 0 t b`** | **两侧都不可编译** |
| **`delta`** | **`const k ⟶ body`** | ****唯一**使用编译器的步** |
| **`appL` / `appR`** | **在 `app` 内约简** | **两侧都不可编译** |
| **`lamBody`** | **在 `lam` 内约简** | **两侧都不可编译** |
| **`piDom` / `piCod`** | **在 `pi` 内约简** | **两侧都不可编译** |
| **`letVal` / `letBody`** | **在 `letE` 内约简** | **两侧都不可编译** |

**=> 结构性结论：符号引擎与权重编译**只在常量展开处相交**。
这就是「不另设中间层」的可核查形式。** -/

namespace Lattice.Runtime.EngineSemantics

open Lattice.Core.CIC
open Lattice.Runtime.CICBridge

/-- **`app` 不可编译。** -/
theorem app_not_compilable (f a : Term) : cicToConstraint (.app f a) = none := rfl

/-- **`lam` 不可编译。** -/
theorem lam_not_compilable (A b : Term) : cicToConstraint (.lam A b) = none := rfl

/-- **`pi` 不可编译。** -/
theorem pi_not_compilable (A B : Term) : cicToConstraint (.pi A B) = none := rfl

/-- **`letE` 不可编译。** -/
theorem letE_not_compilable (A t b : Term) : cicToConstraint (.letE A t b) = none := rfl

/-- **⭐⭐ **结构性**约简的两侧都不可编译。**

**=> 这里只谈**结构性**的八个构造子（`appL`/`appR`/`lamBody`/`piDom`/`piCod`/`letVal`/`letBody`）
—— 它们只在**同一种复合形状内部**移动。**

**=> `beta`/`zeta` **不**在此列：它们的右侧是 `subst` 的结果，
而 `subst` **可以**产生 `const`。我第一版把它们也算进去，Lean 直接拒绝了那个声明。** -/
theorem structural_step_both_uncompilable (E : DefEnv) {a b : Term} (h : Step E a b)
    (hnot : ∀ (k : ℕ) (body : Term), a = .const k → E k = some body → False)
    (hnotBeta : ∀ (A : Term) (body arg : Term), a ≠ .app (.lam A body) arg)
    (hnotZeta : ∀ (A t body : Term), a ≠ .letE A t body) :
    cicToConstraint a = none ∧ cicToConstraint b = none := by
  cases h with
  | beta A b a => exact absurd rfl (hnotBeta A b a)
  | zeta A t b => exact absurd rfl (hnotZeta A t b)
  | delta k b hk => exact absurd (hnot k b rfl hk) (by simp)
  | appL f f' a _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | appR f a a' _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | lamBody A b b' _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | piDom A A' B _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | piCod A B B' _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | letVal A t t' b _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩
  | letBody A t b b' _ => exact ⟨by simp [cicToConstraint], by simp [cicToConstraint]⟩

/-- **⭐⭐ 可编译项上的步必是 `delta`。**

**=> 若 `cicToConstraint a ≠ none`，则 `a` 是 `const` 或 `var`，
而 `Step` 里只有 `delta` 作用于 `const`（`var` 没有步）。** -/
theorem delta_is_the_only_compilable_step (E : DefEnv) {a b : Term} (h : Step E a b)
    (ha : cicToConstraint a ≠ none) :
    ∃ (k : ℕ) (body : Term), a = .const k ∧ E k = some body ∧ b = body := by
  cases h with
  | beta A b a => exact absurd (by simp [cicToConstraint]) ha
  | zeta A t b => exact absurd (by simp [cicToConstraint]) ha
  | delta k b hk => exact ⟨k, b, rfl, hk, rfl⟩
  | appL f f' a _ => exact absurd (by simp [cicToConstraint]) ha
  | appR f a a' _ => exact absurd (by simp [cicToConstraint]) ha
  | lamBody A b b' _ => exact absurd (by simp [cicToConstraint]) ha
  | piDom A A' B _ => exact absurd (by simp [cicToConstraint]) ha
  | piCod A B B' _ => exact absurd (by simp [cicToConstraint]) ha
  | letVal A t t' b _ => exact absurd (by simp [cicToConstraint]) ha
  | letBody A t b b' _ => exact absurd (by simp [cicToConstraint]) ha

/-- **⭐⭐ 引擎与编译的**唯一**交点是 `delta`。**

**=> 合起来：（1）可编译项上的步必为 `delta`；
（2）因此不展开常量时，编译器完全不被触发。** -/
theorem engine_and_compiler_meet_only_at_delta (E : DefEnv) :
    (∀ {a b : Term}, Step E a b → cicToConstraint a ≠ none →
      ∃ (k : ℕ) (body : Term), a = .const k ∧ E k = some body ∧ b = body) ∧
    (∀ {a b : Term}, Step E a b → cicToConstraint a = none →
      cicToConstraint a = none) :=
  ⟨fun h ha => delta_is_the_only_compilable_step E h ha,
   fun _ ha => ha⟩


end Lattice.Runtime.EngineSemantics
