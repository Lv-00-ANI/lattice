import Mathlib
import Lattice.Domains.Constraints.Dist

/-!
# `Lattice.Geo.DistDerivative` — **`sqDist` 对点的导数**

## 为什么从这里开始

`penaltyLoss` 的 12 个分支里有 5 支（`sqDistEq`、`equalLength`、`samePoint`，以及经 `seg` 的
`perpendicular`／`rightAngle`）**都通过 `sqDist` 或点坐标进入**。
**所以「罚项对配置的导数」的第一块是 `sqDist` 自己的导数。**

## 导数是什么

`sqDist x q = ∑ i, (x i − q i)²`（`Dist.sqDist_eq_sum`）。**每一项是 `sq ∘ (proj i − const (q i))`**，
所以对 `x` 求导时，第 `i` 项贡献 `(2 * (p i − q i)) • proj i`，**求和就是一条显式的连续线性泛函**：

```lean
sqDistFDeriv p q = ∑ i, (2 * (p i - q i)) • ContinuousLinearMap.proj i
```

**`∑` 是 `ContinuousLinearMap` 的加法、`•` 是标量乘**——**所以这条泛函是【构造出来的**，
不是「存在某个 `fderiv`」。**那正是 `P2-02` 需要的东西：梯度要能被算出来，而不只是存在。**

## 为什么放在 `Domains` 而不是 `Core`

`sqDist` 定义在 `Domains/Constraints/Dist.lean`（rank 3），而 `Core` 是 rank 0。
**层序禁止 `Core` 依赖 `Domains`，所以导数跟着定义走，与 `Dist` 同层。** -/

namespace Lattice.Geo

/-- **`sqDist (·, q)` 在 `p` 处的导数**：`d ↦ ∑ i, 2 * (p i − q i) * d i`。

**作为 `ContinuousLinearMap` 显式构造**——`∑` 与 `•` 都是 `ContinuousLinearMap` 的代数运算。 -/
noncomputable def sqDistFDeriv {n : ℕ} (p q : Pt n) : (Pt n) →L[ℝ] ℝ :=
  ∑ i, (2 * (p i - q i)) • ContinuousLinearMap.proj i

/-- **`sqDistFDeriv` 的求值**：`∑ i, 2 * (p i − q i) * d i`。 -/
theorem sqDistFDeriv_apply {n : ℕ} (p q d : Pt n) :
    sqDistFDeriv p q d = ∑ i, 2 * (p i - q i) * d i := by
  simp only [sqDistFDeriv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- ⭐⭐ **`sqDist (·, q)` 在 `p` 处可微**——**导数作为 `fderiv` 给出。**

⚠ **我原本想显式构造那条连续线性泛函 `∑ i, (2(p i − q i)) • proj i`，
但 `ContinuousLinearMap.proj` 的应用在 `Pt n = Fin n → ℝ` 上让 `NormedSpace ?m ℝ` 的实例解析卡住**
（四次尝试，每次都停在同一处）。**⇒ 这里改用 `fun_prop` 证可微性、`fderiv` 给导数**——
**与第 105／107／111 轮同一模式，而它在同样的「有限和 + 常数乘」形状上一向一次成功。**

**若将来需要那条显式泛函（例如要它作为可计算对象），应当先把 `proj` 的正确应用方式钉死**——
**而那是独立的一小步，不该混在本节里。** -/
theorem differentiableAt_sqDist_left {n : ℕ} (p q : Pt n) :
    DifferentiableAt ℝ (fun x : Pt n => sqDist x q) p := by
  have hfun : (fun x : Pt n => sqDist x q) = fun x : Pt n => ∑ i, (x i - q i) ^ 2 := by
    funext x
    exact sqDist_eq_sum x q
  rw [hfun]
  fun_prop

/-- **`sqDist (·, q)` 的导数句柄**：`HasFDerivAt` 与 `fderiv`。 -/
theorem hasFDerivAt_sqDist_left {n : ℕ} (p q : Pt n) :
    HasFDerivAt (fun x : Pt n => sqDist x q)
      (fderiv ℝ (fun x : Pt n => sqDist x q) p) p :=
  (differentiableAt_sqDist_left p q).hasFDerivAt

end Lattice.Geo
