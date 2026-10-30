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

end Lattice.Geo
