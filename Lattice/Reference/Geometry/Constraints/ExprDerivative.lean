import Mathlib
import Lattice.Reference.Geometry.Constraints.Expr
import Lattice.Core.AnalysisHelper

/-!
# `Lattice.Geo.ExprDerivative` — **`evalPts` 对点列的显式导数**

## 为什么载体是有限前缀 `Fin K → Pt n`

**`evalPts e : (ℕ → Pt n) → ℝ`，但 `NormedSpace ℝ (ℕ → Pt n)` 在 mathlib 里【不可用】**：

```
failed to synthesize SeminormedAddCommGroup (ℕ → ℝ)
```

**无限索引上的 sup 范数不给实例**（实测，第 115 轮）。**而 `Fin K → Pt n` 上有**（`Pi` 实例自动传播）。**

**⇒ 所以载体取 `Fin K → Pt n`，再用 `trunc` 补零回到 `ℕ → Pt n`。**
**这与 `DistLipschitz` 的 `ptIndex n k` 是同一思路**——**`rho` 也只在有限前缀上取上确界。**

## 索引前提

`coord p axis` 只在 `p < K` 时读到真实数据（否则 `trunc` 给 0，导数为零）。
**所以归纳时带一条「`e` 中出现的所有点索引都 `< K`」的前提**，即 `IndicesBelow e K`。

## 导数的形状

| `e` | 导数 |
|:--|:--|
| `coord p axis` | `proj (p, axis)`（在第 `p` 个点的第 `axis` 个坐标上取值） |
| `const c` | `0` |
| `add e₁ e₂` | `f₁ + f₂` |
| `sub e₁ e₂` | `f₁ - f₂` |
| `mul e₁ e₂` | `f₁ * g + f * g₂`（乘积法则） |
-/

namespace Lattice.Geo

/-- **把有限前缀补零成无限点列**。 -/
noncomputable def trunc {K n : ℕ} (p : Fin K → Pt n) : ℕ → Pt n :=
  fun i => if h : i < K then p ⟨i, h⟩ else 0

/-- **`e` 中出现的所有点索引都 `< K`**——导数存在的前提（见文件头）。 -/
def IndicesBelow {n : ℕ} (e : GeoExpr n) (K : ℕ) : Prop :=
  match e with
  | .coord p _ => p < K
  | .const _ => True
  | .add e₁ e₂ => IndicesBelow e₁ K ∧ IndicesBelow e₂ K
  | .sub e₁ e₂ => IndicesBelow e₁ K ∧ IndicesBelow e₂ K
  | .mul e₁ e₂ => IndicesBelow e₁ K ∧ IndicesBelow e₂ K

/-- **`trunc` 在界内就是原值**。 -/
theorem trunc_apply {K n : ℕ} (p : Fin K → Pt n) (i : Fin K) :
    trunc p i.val = p i := by
  simp only [trunc, dif_pos i.isLt]

/-- **`evalPts` 在 `trunc` 之后只依赖 `p` 的界内坐标**——归纳的基础。 -/
theorem evalPts_trunc_coord {K n : ℕ} (p : Fin K → Pt n) (q : ℕ) (axis : Fin n)
    (hq : q < K) :
    GeoExpr.evalPts (.coord q axis) (trunc p) = p ⟨q, hq⟩ axis := by
  simp only [GeoExpr.evalPts, trunc, dif_pos hq]

/-- **`coord` 支的导数**：第 `(q, axis)` 个坐标的投影。 -/
noncomputable def coordFDeriv {K n : ℕ} (q : Fin K) (axis : Fin n) :
    (Fin K → Pt n) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) axis :
      Pt n →L[ℝ] ℝ)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) q : (Fin K → Pt n) →L[ℝ] Pt n)

/-- **`coord` 支可微**。 -/
theorem hasFDerivAt_coordProj {K n : ℕ} (q : Fin K) (axis : Fin n) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => r q axis) (coordFDeriv q axis) p := by
  have h1 : HasFDerivAt (fun r : Fin K → Pt n => r q)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) q) p :=
    ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) q)
  have h2 : HasFDerivAt (fun x : Pt n => x axis)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) axis) (p q) :=
    ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) axis)
  exact h2.comp p h1

/-- ⭐⭐ **`evalPts` 对 `trunc p` 在整个有限前缀上可微**，**按 `e` 的 5 个构造子归纳**。

**函数的载体是 `Fin K → Pt n`（`NormedSpace` 可用），`trunc` 把界外的点补零**——
**所以 `IndicesBelow e K` 保证 `evalPts` 只读到界内数据。**

推导见文件头的表：`coord` 是投影、`const` 是零、`add`/`sub` 是和差、**`mul` 用乘积法则。** -/
theorem evalPts_differentiableAt {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r)) p := by
  induction e with
  | coord q axis =>
      -- `hK : q < K`
      have hq : q < K := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.coord q axis) (trunc r))
          = fun r : Fin K → Pt n => r ⟨q, hq⟩ axis := by
        funext r
        exact evalPts_trunc_coord r q axis hq
      rw [hfun]
      exact (hasFDerivAt_coordProj ⟨q, hq⟩ axis p).differentiableAt
  | const c =>
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.const c) (trunc r))
          = fun _ => c := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact differentiableAt_const c
  | add e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.add e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) + GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).add (ih₂ h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.sub e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) - GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).sub (ih₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.mul e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) * GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).mul (ih₂ h₂)

/-- **`const` 的 `IndicesBelow` 是 `True`**——便于使用处免去 `trivial`。 -/
theorem indicesBelow_const {n : ℕ} (c : ℝ) (K : ℕ) :
    IndicesBelow (.const c : GeoExpr n) K := trivial

/-- **`IndicesBelow` 对 `coord` 就是索引界**。 -/
theorem indicesBelow_coord {n : ℕ} (q : ℕ) (axis : Fin n) (K : ℕ) :
    IndicesBelow (.coord q axis) K ↔ q < K := Iff.rfl

/-! ## ⭐⭐⭐ 显式导函数 `evalPtsFDeriv`

**可微性（上一节）只说「导数存在」。本节给出它【是什么】**——按构造子递归：

| `e` | `evalPtsFDeriv e` |
|:--|:--|
| `coord q axis` | `coordFDeriv q axis` |
| `const c` | `0` |
| `add e₁ e₂` | `f₁ + f₂` |
| `sub e₁ e₂` | `f₁ - f₂` |
| `mul e₁ e₂` | `(evalPts e₁ pts) • f₂ + (evalPts e₂ pts) • f₁` |（乘积法则）

⚠ **`mul` 那一支的系数是 `evalPts e₁ pts`（一个实数），不是线性映射**——
**这正是 `HasFDerivAt.mul` 的结论形式（`f x • g' + g x • f'`，已用探针确认）**，
**所以定义与定理的形式必须逐字对齐，否则 `exact` 不接受。** -/

/-- **`evalPts` 的显式导数**：一条 `(Fin K → Pt n) →L[ℝ] ℝ`。 -/
noncomputable def evalPtsFDeriv {n : ℕ} (e : GeoExpr n) (K : ℕ) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) : (Fin K → Pt n) →L[ℝ] ℝ :=
  match e, hK with
  | .coord q axis, hK =>
      coordFDeriv (⟨q, hK⟩ : Fin K) axis
  | .const _, _ => 0
  | .add e₁ e₂, hK =>
      evalPtsFDeriv e₁ K hK.1 p + evalPtsFDeriv e₂ K hK.2 p
  | .sub e₁ e₂, hK =>
      evalPtsFDeriv e₁ K hK.1 p - evalPtsFDeriv e₂ K hK.2 p
  | .mul e₁ e₂, hK =>
      (GeoExpr.evalPts e₁ (trunc p)) • evalPtsFDeriv e₂ K hK.2 p
        + (GeoExpr.evalPts e₂ (trunc p)) • evalPtsFDeriv e₁ K hK.1 p

/-- ⭐⭐⭐ **`evalPts` 在 `trunc p` 处的导数就是 `evalPtsFDeriv`**——**显式形式**。

**按 5 个构造子归纳**，每一步用对应的 `HasFDerivAt` 组合子（`.add`／`.sub`／`.mul`），
**`mul` 的系数 `evalPts e₁ (trunc p)` 与定义逐字一致**。 -/
theorem hasFDerivAt_evalPts {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r))
      (evalPtsFDeriv e K hK p) p := by
  induction e with
  | coord q axis =>
      have hq : q < K := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.coord q axis) (trunc r))
          = fun r : Fin K → Pt n => r ⟨q, hq⟩ axis := by
        funext r
        exact evalPts_trunc_coord r q axis hq
      rw [hfun]
      exact hasFDerivAt_coordProj ⟨q, hq⟩ axis p
  | const c =>
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.const c) (trunc r))
          = fun _ => c := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact hasFDerivAt_const (x := p) (c := c)
  | add e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.add e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) + GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).add (ih₂ h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.sub e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) - GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).sub (ih₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      obtain ⟨h₁, h₂⟩ := hK
      have hfun : (fun r : Fin K → Pt n => GeoExpr.evalPts (.mul e₁ e₂) (trunc r))
          = fun r => GeoExpr.evalPts e₁ (trunc r) * GeoExpr.evalPts e₂ (trunc r) := by
        funext r
        simp only [GeoExpr.evalPts]
      rw [hfun]
      exact (ih₁ h₁).mul (ih₂ h₂)

/-- **可微性是 `hasFDerivAt_evalPts` 的推论**——两者陈述一致，后者更强。 -/
theorem evalPts_differentiableAt_direct {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r)) p :=
  (hasFDerivAt_evalPts e hK p).differentiableAt

end Lattice.Geo
