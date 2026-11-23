import Mathlib
import Lattice.Lib.Compiler.RealTypeSoundness
/-!
# LATTICE: 类型系统扩展（变量与 let）+ 健全性

`RealTypeSoundness` 给出极小符号 IR（5 个构造子、无变量、无绑定）的类型系统健全性。
本文件在该方向上做**规模可控的扩展**：加入**变量**与**let 绑定**，环境为
`ℕ → Option TyExt`（变量名 = 自然数），并完整证明：

  1. `TyExt`：类型（`int` / `real` / `bool` / `arr`，保留函数类型以备后续）；
     `ExprExt`：语法（三个字面量 + `var` + `add` + `cmp` + `letIn x e₁ e₂`）；
  2. `extendAt Γ x T`：环境在名字 `x` 处扩展为 `T`；
     `extendAt_comm`（`x ≠ y` 时两次扩展可交换）与 `extendAt_extendAt_same`
     （同一名字连续扩展只保留最后一次）；
  3. `HasTypeExt : (ℕ → Option TyExt) → ExprExt → TyExt → Prop`：归纳式定型；
  4. `ValueExt`：值（当前语言中即三个字面量）；
  5. `substE x v e`：把 `e` 中自由出现的名字 `x` 替换为 `v`；遇到同名
     `let` 绑定（遮蔽）时停止下降，避免捕获；
  6. **`weakening_ext`**：环境单调扩张保持定型；
  7. **`substitution_ext`**：`HasTypeExt (extendAt Γ x S) e T` 且
     `HasTypeExt Γ v S`、`v` 是值 ⟹ `HasTypeExt Γ (substE x v e) T`；
  8. `canonical_forms_ext_int/real/bool`：良类型的值是相应字面量；
  9. **`progress_ext`**：闭项（空环境可定型）要么是值、要么能走一步；
  10. **`preservation_ext`**：步进保持定型；配 `type_soundness_ext` 合取推论。

诚实标注（无 sorry / axiom / admit）：
- **λ/应用不在范围内**：一般 λ 演算的 β 归约需要**一般（非闭）替换引理**，
  在 de Bruijn 表示下还要 `lift`/`subst` 的相容性；本文件刻意**不引入** `lam`/`app`
  构造子，把替换限制为「被替换项是值」的情形（值是字面量，无自由变量，
  故命名变量替换无需移位、也不会捕获）。`TyExt` 中保留 `arr` 只是为后续铺路，
  当前语言没有函数项。docstring 明确：这是**能力裁剪**，不是类型系统能力的声称。
- `substE` 在遇到同名 `let` 绑定时**不下降**（绑定名遮蔽外层的自由变量），
  这是命名变量替换避免捕获的标准做法；替换的项是值，本身无自由变量。
- 环境用 `ℕ → Option TyExt`；空环境 `fun _ => none` 表示闭项。
- 语言仍是**单步小步语义**，无副作用、无递归。
-/

noncomputable section

open Lattice.Lib.Compiler.RealTypeSoundness

namespace Lattice

/-! ## 一、类型与语法 -/

/-- 扩展类型：整数 / 实数 / 布尔 / 函数类型（`arr` 为后续 λ 扩展预留）。 -/
inductive TyExt where
  | int : TyExt
  | real : TyExt
  | bool : TyExt
  | arr (T₁ T₂ : TyExt) : TyExt
deriving DecidableEq, Repr

/-- 扩展语法：三个字面量、变量、加法、比较、`let` 绑定。 -/
inductive ExprExt where
  | litInt (n : ℤ) : ExprExt
  | litReal (r : ℝ) : ExprExt
  | litBool (b : Bool) : ExprExt
  | var (n : ℕ) : ExprExt
  | add (e₁ e₂ : ExprExt) : ExprExt
    /-- **乘法**。⇒ 没有它 `x²` **无法被表示**，P0-b 的样例就只能绕过符号侧。 -/
    | mul (e₁ e₂ : ExprExt) : ExprExt
  | cmp (e₁ e₂ : ExprExt) : ExprExt
  | letIn (x : ℕ) (e₁ e₂ : ExprExt) : ExprExt

/-! ## 二、环境操作 -/

/-- 环境在名字 `x` 处扩展为 `T`。 -/
def extendAt (Γ : ℕ → Option TyExt) (x : ℕ) (T : TyExt) : ℕ → Option TyExt :=
  fun n => if n = x then some T else Γ n

/-- 不同名字的两次扩展可交换。 -/
theorem extendAt_comm {Γ : ℕ → Option TyExt} {x y : ℕ} (hxy : x ≠ y) (S T : TyExt) :
    extendAt (extendAt Γ y T) x S = extendAt (extendAt Γ x S) y T := by
  funext n
  by_cases hx : n = x
  · by_cases hy : n = y
    · exact absurd (hx.symm.trans hy) hxy
    · simp only [extendAt, if_pos hx, if_neg hy]
  · by_cases hy : n = y
    · simp only [extendAt, if_neg hx, if_pos hy]
    · simp only [extendAt, if_neg hx, if_neg hy]

/-- 同一名字的连续扩展只保留最后一次。 -/
theorem extendAt_extendAt_same (Γ : ℕ → Option TyExt) (x : ℕ) (S T : TyExt) :
    extendAt (extendAt Γ x S) x T = extendAt Γ x T := by
  funext n
  by_cases hn : n = x <;> simp [extendAt, hn]

/-! ## 三、定型关系 -/

/-- `HasTypeExt Γ e T`：表达式 `e` 在环境 `Γ` 下有类型 `T`。 -/
inductive HasTypeExt : (ℕ → Option TyExt) → ExprExt → TyExt → Prop where
  | litInt (Γ : ℕ → Option TyExt) (n : ℤ) : HasTypeExt Γ (.litInt n) .int
  | litReal (Γ : ℕ → Option TyExt) (r : ℝ) : HasTypeExt Γ (.litReal r) .real
  | litBool (Γ : ℕ → Option TyExt) (b : Bool) : HasTypeExt Γ (.litBool b) .bool
  | var {Γ : ℕ → Option TyExt} {x : ℕ} {T : TyExt} :
      Γ x = some T → HasTypeExt Γ (.var x) T
  | addInt {Γ : ℕ → Option TyExt} {e₁ e₂ : ExprExt} :
      HasTypeExt Γ e₁ .int → HasTypeExt Γ e₂ .int → HasTypeExt Γ (.add e₁ e₂) .int
  | addReal {Γ : ℕ → Option TyExt} {e₁ e₂ : ExprExt} :
      HasTypeExt Γ e₁ .real → HasTypeExt Γ e₂ .real → HasTypeExt Γ (.add e₁ e₂) .real
  | mulInt {Γ : ℕ → Option TyExt} {e₁ e₂ : ExprExt} :
      HasTypeExt Γ e₁ .int → HasTypeExt Γ e₂ .int → HasTypeExt Γ (.mul e₁ e₂) .int
  | mulReal {Γ : ℕ → Option TyExt} {e₁ e₂ : ExprExt} :
      HasTypeExt Γ e₁ .real → HasTypeExt Γ e₂ .real → HasTypeExt Γ (.mul e₁ e₂) .real
  | cmp {Γ : ℕ → Option TyExt} {e₁ e₂ : ExprExt} :
      HasTypeExt Γ e₁ .int → HasTypeExt Γ e₂ .int → HasTypeExt Γ (.cmp e₁ e₂) .bool
  | letIn {Γ : ℕ → Option TyExt} {x : ℕ} {e₁ e₂ : ExprExt} {T : TyExt}
      (S : TyExt) : HasTypeExt Γ e₁ S →
      HasTypeExt (extendAt Γ x S) e₂ T → HasTypeExt Γ (.letIn x e₁ e₂) T

/-- `ValueExt e`：`e` 是值（当前语言中就是三个字面量）。 -/
inductive ValueExt : ExprExt → Prop where
  | litInt (n : ℤ) : ValueExt (.litInt n)
  | litReal (r : ℝ) : ValueExt (.litReal r)
  | litBool (b : Bool) : ValueExt (.litBool b)

/-- **值的弱化**：值（字面量）在任何环境下都可定型为同一类型
（替换下穿 `let` 绑定时需要）。 -/
theorem value_weakening {v : ExprExt} (hval : ValueExt v) {Γ Δ : ℕ → Option TyExt} {S : TyExt}
    (h : HasTypeExt Γ v S) : HasTypeExt Δ v S := by
  cases hval with
  | litInt n => cases h; exact HasTypeExt.litInt Δ n
  | litReal r => cases h; exact HasTypeExt.litReal Δ r
  | litBool b => cases h; exact HasTypeExt.litBool Δ b

/-! ## 四、替换 -/

/-- 命名变量替换：把 `e` 中自由出现的名字 `x` 替换为 `v`；
遇到同名 `let` 绑定（遮蔽）时停止下降。 -/
def substE (x : ℕ) (v : ExprExt) : ExprExt → ExprExt
  | .litInt n => .litInt n
  | .litReal r => .litReal r
  | .litBool b => .litBool b
  | .var n => if n = x then v else .var n
  | .add e₁ e₂ => .add (substE x v e₁) (substE x v e₂)
  | .mul e₁ e₂ => .mul (substE x v e₁) (substE x v e₂)
  | .cmp e₁ e₂ => .cmp (substE x v e₁) (substE x v e₂)
  | .letIn y e₁ e₂ => .letIn y (substE x v e₁) (if y = x then e₂ else substE x v e₂)

/-! ## 五、弱化 -/

/-- **弱化**：环境单调扩张保持定型。 -/
theorem weakening_ext (e : ExprExt) :
    ∀ {Γ Δ : ℕ → Option TyExt} {T : TyExt}, HasTypeExt Γ e T →
      (∀ n T', Γ n = some T' → Δ n = some T') → HasTypeExt Δ e T := by
  induction e with
  | litInt n => intro Γ Δ T h _; cases h; exact HasTypeExt.litInt Δ n
  | litReal r => intro Γ Δ T h _; cases h; exact HasTypeExt.litReal Δ r
  | litBool b => intro Γ Δ T h _; cases h; exact HasTypeExt.litBool Δ b
  | var x =>
      intro Γ Δ T h hsub
      cases h with
      | var hΓ => exact HasTypeExt.var (hsub x T hΓ)
  | add e₁ e₂ ih₁ ih₂ =>
      intro Γ Δ T h hsub
      cases h with
      | addInt h1 h2 => exact HasTypeExt.addInt (ih₁ h1 hsub) (ih₂ h2 hsub)
      | addReal h1 h2 => exact HasTypeExt.addReal (ih₁ h1 hsub) (ih₂ h2 hsub)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro Γ Δ T h hsub
      cases h with
      | mulInt h1 h2 => exact HasTypeExt.mulInt (ih₁ h1 hsub) (ih₂ h2 hsub)
      | mulReal h1 h2 => exact HasTypeExt.mulReal (ih₁ h1 hsub) (ih₂ h2 hsub)
  | cmp e₁ e₂ ih₁ ih₂ =>
      intro Γ Δ T h hsub
      cases h with
      | cmp h1 h2 => exact HasTypeExt.cmp (ih₁ h1 hsub) (ih₂ h2 hsub)
  | letIn x e₁ e₂ ih₁ ih₂ =>
      intro Γ Δ T h hsub
      cases h with
      | letIn S h1 h2 =>
          refine HasTypeExt.letIn S (ih₁ h1 hsub) (ih₂ h2 ?_)
          intro n T' hn
          by_cases hnx : n = x
          · subst hnx
            simpa [extendAt] using hn
          · simpa [extendAt, hnx] using hsub n T' (by simpa [extendAt, hnx] using hn)

/-! ## 六、替换引理 -/

/-- **替换引理**：在环境 `extendAt Γ x S` 下定型的 `e`，把名字 `x` 替换为
在 `Γ` 下定型为 `S` 的值 `v` 后，在 `Γ` 下仍定型为 `T`。 -/
theorem substitution_ext (e : ExprExt) :
    ∀ (Γ : ℕ → Option TyExt) (x : ℕ) (S T : TyExt) (v : ExprExt),
      HasTypeExt (extendAt Γ x S) e T → HasTypeExt Γ v S → ValueExt v →
      HasTypeExt Γ (substE x v e) T := by
  induction e with
  | litInt n => intro Γ x S T v h hv hval; cases h; exact HasTypeExt.litInt Γ n
  | litReal r => intro Γ x S T v h hv hval; cases h; exact HasTypeExt.litReal Γ r
  | litBool b => intro Γ x S T v h hv hval; cases h; exact HasTypeExt.litBool Γ b
  | var x =>
      intro Γ x₀ S T v h hv hval
      cases h with
      | var hΓ =>
          by_cases hxx : x = x₀
          · subst hxx
            simp only [substE, if_pos rfl]
            have hST : S = T := by simpa [extendAt] using hΓ
            rw [← hST]
            exact hv
          · have hΓ' : Γ x = some T := by simpa [extendAt, hxx] using hΓ
            simp only [substE, if_neg hxx]
            exact HasTypeExt.var hΓ'
  | add e₁ e₂ ih₁ ih₂ =>
      intro Γ x S T v h hv hval
      cases h with
      | addInt h1 h2 =>
          exact HasTypeExt.addInt (ih₁ Γ x S .int v h1 hv hval) (ih₂ Γ x S .int v h2 hv hval)
      | addReal h1 h2 =>
          exact HasTypeExt.addReal (ih₁ Γ x S .real v h1 hv hval) (ih₂ Γ x S .real v h2 hv hval)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro Γ x S T v h hv hval
      cases h with
      | mulInt h1 h2 =>
          exact HasTypeExt.mulInt (ih₁ Γ x S .int v h1 hv hval) (ih₂ Γ x S .int v h2 hv hval)
      | mulReal h1 h2 =>
          exact HasTypeExt.mulReal (ih₁ Γ x S .real v h1 hv hval) (ih₂ Γ x S .real v h2 hv hval)
  | cmp e₁ e₂ ih₁ ih₂ =>
      intro Γ x S T v h hv hval
      cases h with
      | cmp h1 h2 =>
          exact HasTypeExt.cmp (ih₁ Γ x S .int v h1 hv hval) (ih₂ Γ x S .int v h2 hv hval)
  | letIn y e₁ e₂ ih₁ ih₂ =>
      intro Γ x S T v h hv hval
      cases h with
      | letIn S₂ h1 h2 =>
          by_cases hyx : y = x
          · subst hyx
            have h2' : HasTypeExt (extendAt Γ y S₂) e₂ T := by
              rwa [extendAt_extendAt_same] at h2
            simp only [substE, if_pos rfl]
            exact HasTypeExt.letIn S₂ (ih₁ Γ y S S₂ v h1 hv hval) h2'
          · have h2' : HasTypeExt (extendAt (extendAt Γ y S₂) x S) e₂ T := by
              rwa [← extendAt_comm (Ne.symm hyx)] at h2
            simp only [substE, if_neg hyx]
            refine HasTypeExt.letIn S₂ (ih₁ Γ x S S₂ v h1 hv hval) ?_
            exact ih₂ (extendAt Γ y S₂) x S T v h2' (value_weakening hval hv) hval

/-! ## 七、值的小步语义 -/

/-- `StepExt e e'`：`e` 走一步到 `e'`。 -/
inductive StepExt : ExprExt → ExprExt → Prop where
  | addInt (m n : ℤ) : StepExt (.add (.litInt m) (.litInt n)) (.litInt (m + n))
  | addReal (r s : ℝ) : StepExt (.add (.litReal r) (.litReal s)) (.litReal (r + s))
  | cmpInt (m n : ℤ) : StepExt (.cmp (.litInt m) (.litInt n)) (.litBool (decide (m = n)))
  | letInVal (x : ℕ) (e₁ e₂ : ExprExt) :
      ValueExt e₁ → StepExt (.letIn x e₁ e₂) (substE x e₁ e₂)
  | addL {e₁ e₁' e₂ : ExprExt} : StepExt e₁ e₁' → StepExt (.add e₁ e₂) (.add e₁' e₂)
  | addR {e₁ e₂ e₂' : ExprExt} : StepExt e₂ e₂' → StepExt (.add e₁ e₂) (.add e₁ e₂')
  | mulInt (m n : ℤ) : StepExt (.mul (.litInt m) (.litInt n)) (.litInt (m * n))
  | mulReal (r s : ℝ) : StepExt (.mul (.litReal r) (.litReal s)) (.litReal (r * s))
  | mulL {e₁ e₁' e₂ : ExprExt} : StepExt e₁ e₁' → StepExt (.mul e₁ e₂) (.mul e₁' e₂)
  | mulR {e₁ e₂ e₂' : ExprExt} : StepExt e₂ e₂' → StepExt (.mul e₁ e₂) (.mul e₁ e₂')
  | cmpL {e₁ e₁' e₂ : ExprExt} : StepExt e₁ e₁' → StepExt (.cmp e₁ e₂) (.cmp e₁' e₂)
  | cmpR {e₁ e₂ e₂' : ExprExt} : StepExt e₂ e₂' → StepExt (.cmp e₁ e₂) (.cmp e₁ e₂')
  | letInBody {x : ℕ} {e₁ e₁' e₂ : ExprExt} :
      StepExt e₁ e₁' → StepExt (.letIn x e₁ e₂) (.letIn x e₁' e₂)

/-- 多步语义。 -/
inductive MultiStepExt : ExprExt → ExprExt → Prop where
  | refl {e : ExprExt} : MultiStepExt e e
  | step {e e' e'' : ExprExt} : StepExt e e' → MultiStepExt e' e'' → MultiStepExt e e''

/-! ## 八、规范形式引理 -/

/-- **规范形式（整数）**：良类型的值是整数表达式。 -/
theorem canonical_forms_ext_int {e : ExprExt} {Γ : ℕ → Option TyExt}
    (hv : ValueExt e) (ht : HasTypeExt Γ e .int) : ∃ n : ℤ, e = .litInt n := by
  cases hv with
  | litInt n => exact ⟨n, rfl⟩
  | litReal r => cases ht
  | litBool b => cases ht

/-- **规范形式（实数）**：良类型的值是实数表达式。 -/
theorem canonical_forms_ext_real {e : ExprExt} {Γ : ℕ → Option TyExt}
    (hv : ValueExt e) (ht : HasTypeExt Γ e .real) : ∃ r : ℝ, e = .litReal r := by
  cases hv with
  | litInt n => cases ht
  | litReal r => exact ⟨r, rfl⟩
  | litBool b => cases ht

/-- **规范形式（布尔）**：良类型的值是布尔表达式。 -/
theorem canonical_forms_ext_bool {e : ExprExt} {Γ : ℕ → Option TyExt}
    (hv : ValueExt e) (ht : HasTypeExt Γ e .bool) : ∃ b : Bool, e = .litBool b := by
  cases hv with
  | litInt n => cases ht
  | litReal r => cases ht
  | litBool b => exact ⟨b, rfl⟩

/-! ## 九、进度与保持 -/

/-- **进度**：空环境下良类型的项要么是值、要么能走一步。
（`var` 在空环境下不可定型，故无此情形。） -/
theorem progress_ext (e : ExprExt) :
    ∀ {T : TyExt}, HasTypeExt (fun _ => none) e T → ValueExt e ∨ ∃ e', StepExt e e' := by
  induction e with
  | litInt n => intro T h; exact Or.inl (ValueExt.litInt n)
  | litReal r => intro T h; exact Or.inl (ValueExt.litReal r)
  | litBool b => intro T h; exact Or.inl (ValueExt.litBool b)
  | var x =>
      intro T h
      cases h with
      | var hΓ => exact absurd hΓ (by simp)
  | add e₁ e₂ ih₁ ih₂ =>
      intro T h
      cases h with
      | addInt h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · rcases ih₂ h2 with hv2 | ⟨e2', hs2⟩
            · obtain ⟨m, rfl⟩ := canonical_forms_ext_int hv1 h1
              obtain ⟨n, rfl⟩ := canonical_forms_ext_int hv2 h2
              exact Or.inr ⟨_, StepExt.addInt m n⟩
            · exact Or.inr ⟨_, StepExt.addR hs2⟩
          · exact Or.inr ⟨_, StepExt.addL hs1⟩
      | addReal h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · rcases ih₂ h2 with hv2 | ⟨e2', hs2⟩
            · obtain ⟨r, rfl⟩ := canonical_forms_ext_real hv1 h1
              obtain ⟨s, rfl⟩ := canonical_forms_ext_real hv2 h2
              exact Or.inr ⟨_, StepExt.addReal r s⟩
            · exact Or.inr ⟨_, StepExt.addR hs2⟩
          · exact Or.inr ⟨_, StepExt.addL hs1⟩
  | mul e₁ e₂ ih₁ ih₂ =>
      intro T h
      cases h with
      | mulInt h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · rcases ih₂ h2 with hv2 | ⟨e2', hs2⟩
            · obtain ⟨m, rfl⟩ := canonical_forms_ext_int hv1 h1
              obtain ⟨n, rfl⟩ := canonical_forms_ext_int hv2 h2
              exact Or.inr ⟨_, StepExt.mulInt m n⟩
            · exact Or.inr ⟨_, StepExt.mulR hs2⟩
          · exact Or.inr ⟨_, StepExt.mulL hs1⟩
      | mulReal h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · rcases ih₂ h2 with hv2 | ⟨e2', hs2⟩
            · obtain ⟨r, rfl⟩ := canonical_forms_ext_real hv1 h1
              obtain ⟨s, rfl⟩ := canonical_forms_ext_real hv2 h2
              exact Or.inr ⟨_, StepExt.mulReal r s⟩
            · exact Or.inr ⟨_, StepExt.mulR hs2⟩
          · exact Or.inr ⟨_, StepExt.mulL hs1⟩
  | cmp e₁ e₂ ih₁ ih₂ =>
      intro T h
      cases h with
      | cmp h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · rcases ih₂ h2 with hv2 | ⟨e2', hs2⟩
            · obtain ⟨m, rfl⟩ := canonical_forms_ext_int hv1 h1
              obtain ⟨n, rfl⟩ := canonical_forms_ext_int hv2 h2
              exact Or.inr ⟨_, StepExt.cmpInt m n⟩
            · exact Or.inr ⟨_, StepExt.cmpR hs2⟩
          · exact Or.inr ⟨_, StepExt.cmpL hs1⟩
  | letIn x e₁ e₂ ih₁ ih₂ =>
      intro T h
      cases h with
      | letIn S h1 h2 =>
          rcases ih₁ h1 with hv1 | ⟨e1', hs1⟩
          · exact Or.inr ⟨_, StepExt.letInVal x e₁ e₂ hv1⟩
          · exact Or.inr ⟨_, StepExt.letInBody hs1⟩

/-- **保持**：步进保持定型。 -/
theorem preservation_ext {e e' : ExprExt} (hs : StepExt e e') :
    ∀ {Γ : ℕ → Option TyExt} {T : TyExt}, HasTypeExt Γ e T → HasTypeExt Γ e' T := by
  induction hs with
  | addInt m n =>
      intro Γ T h
      cases h with
      | addInt _ _ => exact HasTypeExt.litInt Γ (m + n)
      | addReal h1 _ => cases h1
  | addReal r s =>
      intro Γ T h
      cases h with
      | addInt h1 _ => cases h1
      | addReal _ _ => exact HasTypeExt.litReal Γ (r + s)
  | cmpInt m n =>
      intro Γ T h
      cases h with
      | cmp _ _ => exact HasTypeExt.litBool Γ (decide (m = n))
  | letInVal x e₁ e₂ hval =>
      intro Γ T h
      cases h with
      | letIn S h1 h2 => exact substitution_ext e₂ Γ x S T e₁ h2 h1 hval
  | addL hs1 ih =>
      intro Γ T h
      cases h with
      | addInt h1 h2 => exact HasTypeExt.addInt (ih h1) h2
      | addReal h1 h2 => exact HasTypeExt.addReal (ih h1) h2
  | addR hs2 ih =>
      intro Γ T h
      cases h with
      | addInt h1 h2 => exact HasTypeExt.addInt h1 (ih h2)
      | addReal h1 h2 => exact HasTypeExt.addReal h1 (ih h2)
  | mulInt m n =>
      intro Γ T h
      cases h with
      | mulInt _ _ => exact HasTypeExt.litInt Γ (m * n)
      | mulReal h1 _ => cases h1
  | mulReal r s =>
      intro Γ T h
      cases h with
      | mulInt h1 _ => cases h1
      | mulReal _ _ => exact HasTypeExt.litReal Γ (r * s)
  | mulL hs1 ih =>
      intro Γ T h
      cases h with
      | mulInt h1 h2 => exact HasTypeExt.mulInt (ih h1) h2
      | mulReal h1 h2 => exact HasTypeExt.mulReal (ih h1) h2
  | mulR hs2 ih =>
      intro Γ T h
      cases h with
      | mulInt h1 h2 => exact HasTypeExt.mulInt h1 (ih h2)
      | mulReal h1 h2 => exact HasTypeExt.mulReal h1 (ih h2)
  | cmpL hs1 ih =>
      intro Γ T h
      cases h with
      | cmp h1 h2 => exact HasTypeExt.cmp (ih h1) h2
  | cmpR hs2 ih =>
      intro Γ T h
      cases h with
      | cmp h1 h2 => exact HasTypeExt.cmp h1 (ih h2)
  | letInBody hs1 ih =>
      intro Γ T h
      cases h with
      | letIn S h1 h2 => exact HasTypeExt.letIn S (ih h1) h2

/-- **保持（多步版）**：任意有限步序列保持定型。 -/
theorem preservation_multistep_ext {e e' : ExprExt} (h : MultiStepExt e e') :
    ∀ {Γ : ℕ → Option TyExt} {T : TyExt}, HasTypeExt Γ e T → HasTypeExt Γ e' T := by
  induction h with
  | refl => intro Γ T ht; exact ht
  | step hs _ ih => intro Γ T ht; exact ih (preservation_ext hs ht)

/-- **类型健全性（扩展版）**：闭项或为值、或能继续步进，且任意步保持定型。 -/
theorem type_soundness_ext {e : ExprExt} {T : TyExt}
    (ht : HasTypeExt (fun _ => none) e T) :
    (ValueExt e ∨ ∃ e', StepExt e e') ∧
      (∀ e'', StepExt e e'' → HasTypeExt (fun _ => none) e'' T) :=
  ⟨progress_ext e ht, fun _ hs => preservation_ext hs ht⟩

end Lattice
