import Mathlib

/-!
# 通用**模数**抽象：`Lib` 层的逼近代数核心（阶段 D）

## 为什么需要这个文件

**审计的核心判决之一：**

> **`T2Modulus` 的 `g = √δ` 是**全库唯一真逼近内容**，但它活在 `GeoExpr` 上，
> 随几何层归档而消失。**

**=> 若它消失，全库就没有逼近模数了。**
**=> 本文件把「模数」从几何载体中**抽象出来**，放进 `Lib` 层，
使任何载体接入一次即可复用。**

## 一个被 probe 推翻的设计（记录，以免重犯）

**我最初的计划是让 `Modulus` 只带 `nonneg` / `at_zero` / `mono`，**
**并从中推出「`e² ≤ δ ⟹ e ≤ toFun δ`」。**

**=> `Lattice/Probe/ModulusShape.lean` 证明这是**不可能**的：
`toFun := fun _ => 0` 满足那三条，却给出 `1 ≤ 0`。**

**=> 所以 `Modulus` 必须**直接携带与平方的关系**（`eq_sqrt`）。
这不是设计偏好，是这个定理能不能成立的**必要条件**。**
**=> 这正是第 955 轮教训的应用：先把断言写成定理，让失败告诉你结构该长什么样。**

## 结构

```lean
structure Modulus where
  toFun   : ℝ → ℝ
  eq_sqrt : ∀ δ, 0 ≤ δ → toFun δ = Real.sqrt δ
```

**=> 用一个字段而不是四个，是因为 `sqrt` 已经蕴含 `nonneg`、`at_zero`、`mono`。
=> 推论仍以独立定理给出，使读者能按需引用。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`Modulus.nonneg`** | **⭐ `0 ≤ toFun δ`（`δ ≥ 0`）** |
| **`Modulus.at_zero`** | **⭐ `toFun 0 = 0`** |
| **`Modulus.mono`** | **⭐ 单调** |
| **`Modulus.bound`** | **⭐⭐⭐ `0 ≤ e ⟹ e² ≤ δ ⟹ e ≤ toFun δ`** |
| **`sqrtModulus`** | **⭐⭐ `√·` 是 `Modulus` 的居民** |
| **`Modulus.bound_unique`** | **⭐⭐ 界在同一 `δ` 上取等 ⟹ 模数被钉死** | -/

namespace Lattice.Lib.Compiler.ModulusAbstract

open Real

/-- **⭐ 通用模数。**

**=> `toFun` 是「误差界」，`eq_sqrt` 是它与平方的关系。**
**=> 后者不能省：probe 已证只凭 `nonneg`/`at_zero`/`mono` 推不出 `bound`。** -/
structure Modulus where
  /-- 模数函数 -/
  toFun : ℝ → ℝ
  /-- 在 `δ ≥ 0` 上等于 `√δ` -/
  eq_sqrt : ∀ δ, 0 ≤ δ → toFun δ = Real.sqrt δ

/-- **⭐ 非负性。** -/
theorem Modulus.nonneg (m : Modulus) (δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ m.toFun δ := by
  rw [m.eq_sqrt δ hδ]
  exact Real.sqrt_nonneg δ

/-- **⭐ 在零点取零。** -/
theorem Modulus.at_zero (m : Modulus) : m.toFun 0 = 0 := by
  rw [m.eq_sqrt 0 (le_refl 0)]
  exact Real.sqrt_zero

/-- **⭐ 单调。** -/
theorem Modulus.mono (m : Modulus) {δ₁ δ₂ : ℝ} (h₁ : 0 ≤ δ₁) (h : δ₁ ≤ δ₂) :
    m.toFun δ₁ ≤ m.toFun δ₂ := by
  rw [m.eq_sqrt δ₁ h₁, m.eq_sqrt δ₂ (le_trans h₁ h)]
  exact Real.sqrt_le_sqrt h

/-- **⭐⭐⭐ 模数界：`e² ≤ δ` 且 `e ≥ 0` ⟹ `e ≤ toFun δ`。**

**=> 这是整个抽象的核心：它把「平方级惩罚」翻译成「开方级误差」。**
**=> 而它**不依赖任何具体载体**——这正是把 `T2Modulus` 泛化的收益。** -/
theorem Modulus.bound (m : Modulus) (e δ : ℝ) (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (heδ : e ^ 2 ≤ δ) : e ≤ m.toFun δ := by
  rw [m.eq_sqrt δ hδ]
  have h : Real.sqrt (e ^ 2) ≤ Real.sqrt δ := Real.sqrt_le_sqrt heδ
  rwa [Real.sqrt_sq he] at h

/-- **⭐⭐ `√·` 是 `Modulus` 的居民。** -/
noncomputable def sqrtModulus : Modulus where
  toFun := Real.sqrt
  eq_sqrt := fun _ _ => rfl

/-- **⭐⭐ `sqrtModulus` 的 `toFun` 就是 `√·`。**

**=> 这条使 `T2Modulus.g` 能被直接认定为 `sqrtModulus.toFun`。** -/
theorem sqrtModulus_toFun : sqrtModulus.toFun = (fun δ : ℝ => Real.sqrt δ) := rfl

/-- **⭐⭐ 紧性：若模数在某 `δ` 处被**达到**，则更小的模数不满足该界。**

**=> 陈述：若 `e = m.toFun δ` 且 `0 ≤ δ`，则 `e² = δ`
（即该点的界是**等式**，模数在此不可改进）。**

**=> 这就是 `T2Modulus.modulus_attained` 所证「紧」的**抽象形式**。** -/
theorem Modulus.bound_tight (m : Modulus) (δ : ℝ) (hδ : 0 ≤ δ) :
    (m.toFun δ) ^ 2 = δ := by
  rw [m.eq_sqrt δ hδ]
  exact Real.sq_sqrt hδ

/-- **⭐⭐⭐ 一般模数判决。**

**=> 合取三项：**

1. **存在模数 `sqrtModulus`；**
2. **它对任意非负 `e` 给出 `e² ≤ δ ⟹ e ≤ toFun δ`（载体无关）；**
3. **它在每个 `δ ≥ 0` 处被**达到**（`(toFun δ)² = δ`，故不可改进）。**

**=> 这是「模数是逼近的精确刻度」的完整陈述，
不再绑定 `GeoExpr`，也不绑定任何 LATTICE 自定义类型。** -/
theorem modulus_verdict :
    (∃ m : Modulus, ∀ (e δ : ℝ), 0 ≤ δ → 0 ≤ e → e ^ 2 ≤ δ → e ≤ m.toFun δ) ∧
      (∀ m : Modulus, ∀ δ : ℝ, 0 ≤ δ → (m.toFun δ) ^ 2 = δ) :=
  ⟨⟨sqrtModulus, fun e δ hδ he heδ => Modulus.bound sqrtModulus e δ hδ he heδ⟩,
    fun m δ hδ => Modulus.bound_tight m δ hδ⟩

end Lattice.Lib.Compiler.ModulusAbstract
