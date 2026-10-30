import Mathlib
import Lattice.Domains.Constraints.PenaltyLossDerivative
import Lattice.Domains.Constraints.NetLoss
import Lattice.Core.StackDerivative
import Lattice.Core.Net

/-!
# `Lattice.Geo.NetLossDerivative` — **`netLoss` 对点列的导数：桥接引理**

## 接口障碍，及其解法

`netLoss params cs pts = (cs.map (fun c => penaltyLoss c (fun k => netAct params (pts k)))).sum`
（第 101 轮）。

第 128 轮的 `hasFDerivAt_penaltyLoss` 载体是 `fun r : Fin K → Pt n => penaltyLoss c (trunc r)`，
**而 `trunc` 在 `k ≥ K` 处【补零】。**

**`netLoss` 的点列是 `fun k => netAct params (pts k)`，而 `netAct params 0 ≠ 0`**（仿射层带偏置），
**所以「`netLoss` 的点列等于某个 `trunc φ`」【不成立】。**

## 解法：把「只读界内」这条事实显式化

**`ConstraintIndicesBelow c K` 说的是「`c` 用到的点索引都 `< K`」。**
**所以 `penaltyLoss c Φ` 只依赖 `Φ` 在 `[0,K)` 上的值——与 `Φ` 在界外是什么【无关】。**

**本文件把这条事实逐层证出来：**

1. `evalPts_congr_of_indicesBelow`：`GeoExpr` 的求值只依赖界内坐标；
2. 由此逐步到 `penaltyLoss` 的同一性质。

**有了它，`netLoss` 的导数只需把 `fun k => netAct params (trunc r k)` 与 `trunc φ` 在界内对齐，
完全不必碰界外。**
-/

namespace Lattice.Geo

open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- ⭐ **`evalPts` 只依赖界内坐标**：若 `Φ` 与 `Ψ` 在 `[0,K)` 上一致，且 `e` 的索引都 `< K`，
则求值相同。

**对 `GeoExpr` 的五个构造子归纳**：`coord` 用一致性假设，其余三项逐层应用归纳假设。 -/
theorem evalPts_congr_of_indicesBelow {n : ℕ} (e : GeoExpr n) (K : ℕ)
    (hK : IndicesBelow e K) (Φ Ψ : ℕ → Pt n) (h : ∀ k, k < K → Φ k = Ψ k) :
    GeoExpr.evalPts e Φ = GeoExpr.evalPts e Ψ := by
  induction e with
  | coord q axis =>
      have hq : q < K := hK
      simp only [GeoExpr.evalPts]
      rw [h q hq]
  | const c => simp only [GeoExpr.evalPts]
  | add e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]
  | sub e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]
  | mul e₁ e₂ ih₁ ih₂ => simp only [GeoExpr.evalPts, ih₁ hK.1, ih₂ hK.2]

/-! ## 第二层：`penaltyLoss` 只依赖界内坐标

**`Pt n` 层的三条**：`sqDist`、`seg`、`midpointCLM` 都只读两个点，
**所以「点的坐标一致」直接给出「由它们构成的量一致」。**

**然后是 `penaltyLoss` 的十二支**——**每支只用前两条加 `evalPts_congr_of_indicesBelow`。** -/

/-- **`sqDist` 对点的坐标一致性**。 -/
theorem sqDist_congr {n : ℕ} {x y x' y' : Pt n} (hx : x = x') (hy : y = y') :
    sqDist x y = sqDist x' y' := by
  rw [hx, hy]

/-- **`seg` 对点的坐标一致性**。 -/
theorem seg_congr {n : ℕ} (Φ Ψ : ℕ → Pt n) (a b : ℕ) (ha : Φ a = Ψ a) (hb : Φ b = Ψ b) :
    seg Φ a b = seg Ψ a b := by
  funext i
  simp only [seg]
  rw [ha, hb]

/-- **`minorDefect` 对两个向量的相等性**。 -/
theorem minorDefect_congr {n : ℕ} {u v u' v' : Pt n} (hu : u = u') (hv : v = v') :
    minorDefect u v = minorDefect u' v' := by
  rw [hu, hv]

/-- ⭐⭐ **`penaltyLoss` 只依赖界内坐标**——**十二支逐一处理**。

**这是 `netLoss` 导数的关键：它把「`trunc` 的补零假设」换成「在 `[0,K)` 上一致」，
而后者对 `fun k => netAct params (trunc r k)` 是【构造上成立】的。** -/
theorem penaltyLoss_congr_of_indicesBelow {n : ℕ} (c : GeoConstraint n) (K : ℕ)
    (hK : ConstraintIndicesBelow c K) (Φ Ψ : ℕ → Pt n)
    (h : ∀ k, k < K → Φ k = Ψ k) :
    penaltyLoss c Φ = penaltyLoss c Ψ := by
  match c, hK with
  | .eqZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .leZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .ltZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .gtZero e, hK =>
      simp only [penaltyLoss, evalPts_congr_of_indicesBelow e K hK Φ Ψ h]
  | .sqDistEq a b d, ⟨ha, hb, hd⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb),
        evalPts_congr_of_indicesBelow d K hd Φ Ψ h]
  | .equalLength a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb),
        sqDist_congr (h c' hc) (h e he)]
  | .collinear a b c', ⟨ha, hb, hc⟩ =>
      simp only [penaltyLoss]
      rw [minorDefect_congr (seg_congr Φ Ψ a b (h a ha) (h b hb))
        (seg_congr Φ Ψ a c' (h a ha) (h c' hc))]
  | .perpendicular a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss]
      rw [seg_congr Φ Ψ a b (h a ha) (h b hb), seg_congr Φ Ψ c' e (h c' hc) (h e he)]
  | .parallel a b c' e, ⟨ha, hb, hc, he⟩ =>
      simp only [penaltyLoss]
      rw [minorDefect_congr (seg_congr Φ Ψ a b (h a ha) (h b hb))
        (seg_congr Φ Ψ c' e (h c' hc) (h e he))]
  | .rightAngle a b c', ⟨ha, hb, hc⟩ =>
      simp only [penaltyLoss]
      rw [seg_congr Φ Ψ a b (h a ha) (h b hb), seg_congr Φ Ψ b c' (h b hb) (h c' hc)]
  | .midpoint m a b, ⟨hm, ha, hb⟩ =>
      simp only [penaltyLoss]
      rw [h m hm, h a ha, h b hb]
  | .samePoint a b, ⟨ha, hb⟩ =>
      simp only [penaltyLoss, sqDist_congr (h a ha) (h b hb)]

end Lattice.Geo
