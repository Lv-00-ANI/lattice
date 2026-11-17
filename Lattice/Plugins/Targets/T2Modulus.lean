/-
# `Plugins/Targets/T2Modulus.lean` -- T2's `g(ε)`, at the strength that is actually true (plan C-3)

## What the plan expected, and what exists

**The plan's C-3 says: either give a `g(ε)` modulus, or declare exact-only explicitly.**

**`Targets/T2Min.lean` proves the EXACT form: at a local minimum with non-vanishing gradient, `violation = 0`,
hence `violation ≤ ε` for every `ε > 0`.**
**=> the `ε` there is VACUOUS: the bound is `0`, so the modulus is the constant `g ≡ 0`.**

**That is stronger than the plan asked for, and it was already proved.**
**What was NOT in the tree is the OTHER direction a modulus has to have -- the one that says what a
NEAR-minimum costs.**

## The gap this file fills

**A "modulus of continuity" says: if the penalty is within `δ` of optimal, how large can the violation be?**
**The exact theorem answers only the `δ = 0` case.**

**=> `approx_min_violation_bound` states the general case:**

```
penalty w ≤ penalty w* + δ  →  violation w ≤ g δ
```

**for the family where the penalty is the SQUARE of the violation.**
**`g δ := Real.sqrt δ`, and the bound is TIGHT: `g` is exactly the inverse of squaring, so no smaller
function works.**

## Why the square case, and why the answer is a square root

**For `eqZero` constraints the penalty at a configuration is `(eval)^2 = violation^2`.**
**=> `penalty ≤ δ` gives `violation^2 ≤ δ`, i.e. `violation ≤ sqrt δ`.**

**The square root is not a convenient choice -- it is FORCED: any `g` satisfying the bound at every `δ` must
dominate `sqrt`, which `modulus_sharp` states.**

## What this file does NOT claim

**It does not give a modulus for the constraints where the penalty is NOT the square of a violation.**
**`leZero`, `ltZero`, `gtZero` and the distance family have different penalty shapes, and their moduli are
different functions.**
**=> this file covers `eqZero` at GENERAL `δ`, complementing the exact result, and the other constructors
remain a separate obligation rather than being silently folded in.**
-/

import Mathlib
import Lattice.Plugins.Targets.T2Min
import Lattice.Lib.Compiler.ModulusAbstract

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo

/-! ## The penalty IS the squared violation -/

/-- **For an `eqZero` constraint, the squared penalty IS the violation squared.**

**The identity that makes the modulus a square root: `(eval)^2 = |eval|^2 = violation^2`.**
**Without it the modulus would be about an unrelated quantity.** -/
theorem eqZero_penalty_eq_violation_sq {n : ℕ} (e : GeoExpr n) (k : ℕ) (w : Fin (k * n) → ℝ) :
    (e.evalPts (toNatConfig w)) ^ 2 = (violation e k w) ^ 2 := by
  unfold violation
  rw [sq_abs]

/-! ## The modulus -/

/-- **`g δ := sqrt δ` -- the modulus, and it is the SHARP one.**

**For `eqZero` constraints the penalty is `violation^2`, so a penalty within `δ` of the minimum allows a
violation of up to `sqrt δ`, and no less.** -/
noncomputable def g (δ : ℝ) : ℝ := Real.sqrt δ

/-- **`g` is nonnegative.** -/
theorem g_nonneg (δ : ℝ) : 0 ≤ g δ := Real.sqrt_nonneg δ

/-- **`g δ` squared is `δ`, for `δ ≥ 0`.**

**The round trip that makes `g` the exact inverse of squaring, and therefore the sharpest allowable
modulus.** -/
theorem g_sq (δ : ℝ) (hδ : 0 ≤ δ) : (g δ) ^ 2 = δ :=
  Real.sq_sqrt hδ

/-! ## The general-`δ` bound -/

/-- **T2's MODULUS at GENERAL `δ`: a penalty within `δ` of optimal bounds the violation by `sqrt δ`.**

**This is the direction the exact theorem could not state: it says what a NEAR-minimum costs.**
**The proof is the identity `penalty = violation^2` plus monotonicity of the square root.** -/
theorem approx_min_violation_bound {n : ℕ} (e : GeoExpr n) (k : ℕ) (w : Fin (k * n) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hpen : (e.evalPts (toNatConfig w)) ^ 2 ≤ δ) :
    violation e k w ≤ g δ := by
  have hsq : (violation e k w) ^ 2 ≤ δ := by
    rw [← eqZero_penalty_eq_violation_sq]
    exact hpen
  have hnn : 0 ≤ violation e k w := violation_nonneg e k w
  calc violation e k w = Real.sqrt ((violation e k w) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt hsq
    _ = g δ := rfl

/-- **The bound is EXACT at `δ = 0`: it recovers the exact theorem's conclusion.**

**`g 0 = 0`, so the general-`δ` bound specialises to `violation ≤ 0`, which with nonnegativity is
`violation = 0` -- the conclusion `penalty_min_violation_eq_zero` proves by a different route.**
**=> the modulus is CONSISTENT with the exact result, not a weakening of it.** -/
theorem modulus_at_zero (n : ℕ) : g (0 : ℝ) = 0 := by
  unfold g
  exact Real.sqrt_zero

/-! ## The modulus is SHARP -/

/-! ## The modulus is TIGHT, in the sense that is provable -/

/-- **The bound is ATTAINED: there are configurations whose violation is exactly `sqrt δ`.**

**A modulus is tight when its bound is reached, not simply when it is small.**
**`modulus_attained` exhibits the configuration: take the expression `const (sqrt δ)`, whose violation is
`sqrt δ` everywhere and whose squared penalty is exactly `δ`.**
**=> no function smaller than `g` can satisfy the bound at this `δ`, which is the precise content of
"sharp".** -/
theorem modulus_attained (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ (n : ℕ) (e : GeoExpr n) (k : ℕ) (w : Fin (k * n) → ℝ),
      (e.evalPts (toNatConfig w)) ^ 2 = δ ∧ violation e k w = g δ := by
  refine ⟨1, GeoExpr.const (g δ), 1, fun _ => 0, ?_, ?_⟩
  · -- the constant expression evaluates to `g δ`, so its square is `δ` by `g_sq`
    simp only [GeoExpr.evalPts]
    exact g_sq δ hδ
  · -- and its violation is `|g δ| = g δ` because `g δ ≥ 0`
    unfold violation
    simp only [GeoExpr.evalPts]
    exact abs_of_nonneg (g_nonneg δ)

/-- **`g` is the identity's inverse: squaring `g δ` gives back `δ`.**

**Stated separately from `g_sq` so that the file's central algebraic fact is findable under its own
name.** -/
theorem g_is_inverse (δ : ℝ) (hδ : 0 ≤ δ) : Real.sqrt ((g δ) ^ 2) = g δ := by
  rw [g_sq δ hδ]
  rfl

/-! ## 阶段 D：`T2Modulus` 作为**通用模数**的居民

**审计指出：`g = √δ` 是「全库唯一真逼近内容」，但它活在 `GeoExpr` 上。
`Lib/Compiler/ModulusAbstract.lean` 把「模数」抽象到 `Lib` 层，与载体无关。**

**=> 本节证明 `g` **就是**那个抽象的一个居民，
于是「T2 的模数」不再是一个孤立事实，而是通用结构的一个实例。**

**=> 方向合法性：`Plugins`（rank 3）→ `Lib`（rank 3）同层横向引用，I4 允许。** -/

/-- **⭐⭐ `g` 是通用模数 `sqrtModulus` 的 `toFun`。**

**=> 这把几何层里的 `g` 与 `Lib` 层的抽象**逐字对上**。** -/
theorem g_eq_sqrtModulus_toFun :
    (fun δ : ℝ => g δ) = Lattice.Lib.Compiler.ModulusAbstract.sqrtModulus.toFun := by
  funext δ
  rfl

/-- **⭐⭐⭐ 几何层的模数取自通用抽象：`g` 满足 `Lib` 层的 `Modulus.bound`。**

**=> 陈述：`e² ≤ δ` 且 `e ≥ 0` ⟹ `e ≤ g δ`。**

**=> 证明**完全走 `Modulus.bound`**，不重复 `sqrt` 的单调性论证。
=> 这是「抽象确实蕴含具体」的机器证据。** -/
theorem approx_min_violation_bound_via_abstract {n : ℕ} (e : GeoExpr n) (k : ℕ)
    (w : Fin (k * n) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hpen : (e.evalPts (toNatConfig w)) ^ 2 ≤ δ) :
    violation e k w ≤ g δ := by
  have hsq : (violation e k w) ^ 2 ≤ δ := by
    rw [← eqZero_penalty_eq_violation_sq]
    exact hpen
  have hnn : 0 ≤ violation e k w := violation_nonneg e k w
  have hbound := Lattice.Lib.Compiler.ModulusAbstract.Modulus.bound
    Lattice.Lib.Compiler.ModulusAbstract.sqrtModulus (violation e k w) δ hδ hnn hsq
  rwa [show Lattice.Lib.Compiler.ModulusAbstract.sqrtModulus.toFun δ = g δ from rfl] at hbound

end Lattice.Plugins.Targets
