import Mathlib
import Lattice.Domains.Constraints.Dist
import Lattice.Core.AnalysisHelper

/-!
# `Lattice.Geo.DistDerivative` — **`sqDist` 对点的显式导数**

## 为什么从这里开始

`penaltyLoss` 的 12 个分支里有 5 支（`sqDistEq`、`equalLength`、`samePoint`，以及经 `seg` 的
`perpendicular`／`rightAngle`）**都通过 `sqDist` 或点坐标进入**。
**所以「罚项对配置的导数」的第一块是 `sqDist` 自己的导数。**

## 导数是什么

`sqDist x q = ∑ i, (x i − q i)²`（`Dist.sqDist_eq_sum`）。每一项是 `sq ∘ (proj i − const (q i))`，
**所以对 `x` 求导时第 `i` 项贡献 `(2 * (p i − q i)) • proj i`，求和就是一条【显式】的连续线性泛函**：

```lean
sqDistFDeriv p q = ∑ i, (2 * (p i - q i)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i
```

**`∑` 是 `ContinuousLinearMap` 的加法、`•` 是标量乘**——**所以这条泛函是构造出来的，
不是「存在某个 `fderiv`」。那正是 `P2-02` 需要的东西：梯度要能被算出来，而不只是存在。**

## 两条被最小探针钉死的事实（第 112–114 轮）

### ① `proj` 的标量域必须与 `hasFDerivAt` 的 `𝕜` 同时固定

`ContinuousLinearMap.proj` 的 `R` 与 `ContinuousLinearMap.hasFDerivAt` 的 `𝕜` 是**两个独立**的隐含参数。
**只固定其中一个，另一个留成元变量，`NormedSpace` 的搜索就卡住：**

```
typeclass instance problem is stuck: NormedSpace ?m.16474 ℝ
```

**可行写法是把【同一个完整表达式】交给两者：**

```lean
have hproj : HasFDerivAt (fun x : Pt n => x i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) p :=
  ContinuousLinearMap.hasFDerivAt
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
```

**注意 `Pt n` 是清白的**：探针用纯 `Fin n → ℝ` 复现了同样的失败，
**所以问题从不在载体，而在那两个参数的固定方式。**

### ② `y ↦ y²` 的导数：不能走 `pow`，也不能走 `HasDerivAt` 桥

- **`fun_prop` 不支持 `HPow.hPow`**（探针报 `No theorems found for HPow.hPow`）；
- **`hasFDerivAt_pow` 不存在**；
- **`hasDerivAt_pow` 存在，但 `HasDerivAt.hasFDerivAt` 卡在同一实例上**（给了 `(𝕜 := ℝ)` 也不行）。

**⇒ 可行写法：把 `y ^ 2` 换成 `y * y`，用 `HasDerivAt.mul`（乘积法则）得
`HasDerivAt (· * ·) (1 * y + y * 1) y`，再 `convert` 到 `smulRight 1 (2 * y)`。**
**那是 `hasFDerivAt_mulSelf`。** -/

namespace Lattice.Geo

open Lattice.Core in
/-- **`sqDist (·, q)` 在 `p` 处的导数**：`d ↦ ∑ i, 2 * (p i − q i) * d i`。

**作为 `ContinuousLinearMap` 显式构造**——`proj` 的 `R`/`φ` 显式给出（见节头 ①）。 -/
noncomputable def sqDistFDeriv {n : ℕ} (p q : Pt n) : (Pt n) →L[ℝ] ℝ :=
  ∑ i, (2 * (p i - q i)) •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)

/-- **`sqDistFDeriv` 的求值**：`∑ i, 2 * (p i − q i) * d i`。 -/
theorem sqDistFDeriv_apply {n : ℕ} (p q d : Pt n) :
    sqDistFDeriv p q d = ∑ i, 2 * (p i - q i) * d i := by
  simp only [sqDistFDeriv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **单坐标项对 `x` 的导数**：`(x i − q i)²` 的导数是 `(2(p i − q i)) • proj i`。

**由「`x i − q i` 的导数是 `proj i`」与 `hasFDerivAt_mulSelf` 复合，再对齐常数。** -/
theorem hasFDerivAt_coordSq {n : ℕ} (p q : Pt n) (i : Fin n) :
    HasFDerivAt (fun x : Pt n => (x i - q i) ^ 2)
      ((2 * (p i - q i)) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)) p := by
  have hproj : HasFDerivAt (fun x : Pt n => x i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) p :=
    ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
  have hf : HasFDerivAt (fun x : Pt n => x i - q i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) p :=
    hproj.sub_const (q i)
  -- `y ↦ y * y` at `p i - q i`, rewritten to `y ^ 2`
  have hmul := Lattice.Core.hasFDerivAt_sq (p i - q i)
  -- compose
  have hcomp := hmul.comp p hf
  convert hcomp using 1

/-- ⭐⭐⭐ **`sqDist (·, q)` 在 `p` 处可微，导数是 `sqDistFDeriv p q`**——**显式导数。**

**由各坐标项的导数求和（`HasFDerivAt.sum`）加 `sqDist_eq_sum` 的展开。** -/
theorem hasFDerivAt_sqDist_left {n : ℕ} (p q : Pt n) :
    HasFDerivAt (fun x : Pt n => sqDist x q) (sqDistFDeriv p q) p := by
  have hsum : HasFDerivAt (fun x : Pt n => ∑ i, (x i - q i) ^ 2) (sqDistFDeriv p q) p := by
    have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin n)))
      (fun i _ => hasFDerivAt_coordSq p q i)
    simpa only [sqDistFDeriv] using h
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun x => (sqDist_eq_sum x q).symm)

/-- **可微性作为推论**——`fderiv` 版本的消费者可以直接用这一条。 -/
theorem differentiableAt_sqDist_left {n : ℕ} (p q : Pt n) :
    DifferentiableAt ℝ (fun x : Pt n => sqDist x q) p :=
  (hasFDerivAt_sqDist_left p q).differentiableAt

/-- ⭐⭐⭐ **`fderiv` 就是那条显式泛函**——**「梯度可计算」的准确形式**：
下游可以绕过 `fderiv` 直接用 `sqDistFDeriv`。 -/
theorem fderiv_sqDist_left {n : ℕ} (p q : Pt n) :
    fderiv ℝ (fun x : Pt n => sqDist x q) p = sqDistFDeriv p q :=
  (hasFDerivAt_sqDist_left p q).fderiv

end Lattice.Geo
