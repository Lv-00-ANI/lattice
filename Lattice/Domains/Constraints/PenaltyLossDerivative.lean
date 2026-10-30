import Mathlib
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.DistDerivative
import Lattice.Domains.Constraints.ExprDerivative

set_option maxHeartbeats 800000

/-!
# `Lattice.Geo.PenaltyLossDerivative` — **`penaltyLoss` 对点列的显式导数**

## 载体与前提

**导数载体是 `Fin K → Pt n`**（与 `ExprDerivative` 一致：`NormedSpace ℝ (ℕ → Pt n)` 不存在），
**函数是 `fun r => penaltyLoss c (trunc r)`**，**前提是 `IndicesBelow c K`**。

## 本文件覆盖的分支

`penaltyLoss` 有 12 支，**本文件做【无条件可导】的那些**：

| 分支 | 形状 |
|:--|:--|
| `samePoint a b` | `sqDist (pts a) (pts b)` |
| `eqZero e` | `(evalPts e)²` |
| `sqDistEq a b d` | `(sqDist − evalPts d)²` |
| `equalLength a b c e` | `(sqDist − sqDist)²` |

⚠ **`leZero`/`ltZero`/`gtZero` 走 `max · 0`，在折点 `evalPts e = 0` 处【不可导】**——
**它们需要额外前提，本文件不声称它们是可导的。**

## 为什么先要 `sqDist` 的联合可微性

`samePoint a b` 是 `sqDist (trunc r a) (trunc r b)`——**两个槽都随 `r` 动**，
**所以 `sqDistFDeriv`（单槽）不够，必须有 `(x, y) ↦ sqDist x y` 的联合可微性。**
**而 `fun_prop` 能直接证它**（探针验证，第 117 轮）。
-/

namespace Lattice.Geo

/-- ⭐ **`sqDist` 对【两个】变元联合可微**——`samePoint` 支的前提。 -/
theorem sqDist_differentiableAt_pair {n : ℕ} (x y : Pt n) :
    DifferentiableAt ℝ (fun r : Pt n × Pt n => sqDist r.1 r.2) (x, y) := by
  have hfun : (fun r : Pt n × Pt n => sqDist r.1 r.2)
      = fun r : Pt n × Pt n => ∑ i, (r.1 i - r.2 i) ^ 2 := by
    funext r
    exact sqDist_eq_sum r.1 r.2
  rw [hfun]
  fun_prop

/-- **取第 `a` 个点的投影**：`(Fin K → Pt n) →L[ℝ] Pt n`。 -/
noncomputable def pointProj {K n : ℕ} (a : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Pt n) a

/-- **`trunc r a` 对 `r` 的导数就是 `pointProj a`**。 -/
theorem hasFDerivAt_truncPoint {K n : ℕ} (a : ℕ) (ha : a < K) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => trunc r a) (pointProj ⟨a, ha⟩) p := by
  have hfun : (fun r : Fin K → Pt n => trunc r a) = fun r : Fin K → Pt n => r ⟨a, ha⟩ := by
    funext r
    exact trunc_apply r ⟨a, ha⟩
  rw [hfun]
  exact ContinuousLinearMap.hasFDerivAt (pointProj ⟨a, ha⟩)

/-- **`r ↦ (trunc r a, trunc r b)` 是连续的线性映射**（两个 `pointProj` 的积）。 -/
noncomputable def pairProj {K n : ℕ} (a b : Fin K) :
    (Fin K → Pt n) →L[ℝ] (Pt n × Pt n) :=
  (pointProj a).prod (pointProj b)

/-- **`r ↦ (trunc r a, trunc r b)` 的导数**。 -/
theorem hasFDerivAt_pairProj {K n : ℕ} (a b : ℕ) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => (trunc r a, trunc r b))
      (pairProj ⟨a, ha⟩ ⟨b, hb⟩) p :=
  (hasFDerivAt_truncPoint a ha p).prod (hasFDerivAt_truncPoint b hb p)

/-- ⭐⭐ **`samePoint` 分支可微**：`sqDist (trunc · a) (trunc · b)`。

**由 `sqDist_differentiableAt_pair` 与 `hasFDerivAt_pairProj` 复合。** -/
theorem samePoint_differentiableAt {K n : ℕ} (a b : ℕ) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => sqDist (trunc r a) (trunc r b)) p :=
  (sqDist_differentiableAt_pair (trunc p a) (trunc p b)).comp p
    (hasFDerivAt_pairProj a b ha hb p).differentiableAt

/-- ⭐⭐ **`eqZero` 分支可微**：`(evalPts e (trunc ·))²`。

**由 `evalPts_differentiableAt`（第 115 轮）与 `y ↦ y²`（`Core.hasFDerivAt_sq`）复合。** -/
theorem eqZero_differentiableAt {K n : ℕ} (e : GeoExpr n) (hK : IndicesBelow e K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => GeoExpr.evalPts e (trunc r) ^ 2) p :=
  (Lattice.Core.hasFDerivAt_sq (GeoExpr.evalPts e (trunc p))).differentiableAt.comp p
    (evalPts_differentiableAt e hK p)

/-- ⭐⭐ **`sqDistEq` 分支可微**：`(sqDist (trunc · a) (trunc · b) − evalPts d (trunc ·))²`。

**两个求导对象分别是 `sqDist` 的联合复合与 `evalPts`，相减后用 `y ↦ y²` 复合。** -/
theorem sqDistEq_differentiableAt {K n : ℕ} (a b : ℕ) (d : GeoExpr n)
    (ha : a < K) (hb : b < K) (hd : IndicesBelow d K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n =>
        (sqDist (trunc r a) (trunc r b) - GeoExpr.evalPts d (trunc r)) ^ 2) p := by
  have h1 := samePoint_differentiableAt a b ha hb p
  have h2 := evalPts_differentiableAt d hd p
  exact (Lattice.Core.hasFDerivAt_sq
    (sqDist (trunc p a) (trunc p b) - GeoExpr.evalPts d (trunc p))).differentiableAt.comp p
    (h1.sub h2)

/-- ⭐⭐ **`equalLength` 分支可微**：`(sqDist (trunc · a) (trunc · b) − sqDist (trunc · c) (trunc · e))²`。 -/
theorem equalLength_differentiableAt {K n : ℕ} (a b c e : ℕ)
    (ha : a < K) (hb : b < K) (hc : c < K) (he : e < K) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n =>
        (sqDist (trunc r a) (trunc r b) - sqDist (trunc r c) (trunc r e)) ^ 2) p := by
  have h1 := samePoint_differentiableAt a b ha hb p
  have h2 := samePoint_differentiableAt c e hc he p
  exact (Lattice.Core.hasFDerivAt_sq
    (sqDist (trunc p a) (trunc p b) - sqDist (trunc p c) (trunc p e))).differentiableAt.comp p
    (h1.sub h2)

end Lattice.Geo
