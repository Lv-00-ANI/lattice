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

/-! ## ⭐ `seg` 作为线性映射，以及 `midpoint` 的导数

`seg (trunc r) a b i = trunc r b i − trunc r a i`——**对 `r` 是【线性】的**，
**所以 `seg` 本身就是一条 `(Fin K → Pt n) →L[ℝ] Pt n`，而不是需要乘积法则的东西。**

**这直接给出 `midpoint` 支**（`∑ i, (2·pts m i − pts a i − pts b i)²`，线性形式平方和）：
**每项的导数由 `Core.hasFDerivAt_sq_comp` 给出，求和由 `HasFDerivAt.sum` 收。** -/

/-- **`seg` 作为线性映射**：`r ↦ fun i => r b i − r a i`。 -/
noncomputable def segCLM {K n : ℕ} (a b : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  (pointProj b) - (pointProj a)

/-- **`segCLM` 的求值**：与 `seg (trunc r) a b` 逐点一致。 -/
theorem segCLM_apply {K n : ℕ} (a b : Fin K) (r : Fin K → Pt n) (i : Fin n) :
    segCLM a b r i = trunc r b i - trunc r a i := by
  simp only [segCLM, ContinuousLinearMap.sub_apply, pointProj, Pi.sub_apply,
    ContinuousLinearMap.proj_apply]
  rw [trunc_apply, trunc_apply]

/-- **`segCLM` 的导数**。 -/
theorem hasFDerivAt_segCLM {K n : ℕ} (a b : Fin K) (p : Fin K → Pt n) :
    HasFDerivAt (fun r : Fin K → Pt n => segCLM a b r) (segCLM a b) p :=
  ContinuousLinearMap.hasFDerivAt (segCLM a b)

/-! ## `midpoint` 与 `perpendicular`：两个「平方」分支

`midpoint m a b` 是 `∑ i, (2·pts m i − pts a i − pts b i)²`——**一个线性形式的平方和**。
`perpendicular a b c e` 是 `(∑ i, seg a b i · seg c e i)²`——**一个双线性形式的平方**。

**两者的内层都写成 `segCLM` 的组合：**

- `midpoint` 的内层：`L = 2 • segCLM b m − segCLM a b`（因为 `2·pts m − pts a − pts b = 2(ptm − pta) − (ptb − pta)` 的展开，
  但直接写成 `2 • pointProj m − pointProj a − pointProj b` 更短且逐字正确）；
- `perpendicular` 的内层：`∑ i, segCLM a b r i * segCLM c e r i`。

⚠ **`midpoint` 的内层我用 `2 • pointProj m − pointProj a − pointProj b`**（**不是** `segCLM` 的组合）——
**因为它就是 `2·pts m − pts a − pts b` 的字面翻译**，少一次换形就少一处出错（第 118 轮在这里失败过）。

⚠ **`2` 必须写成 `(2 : ℝ)`**——第 118 轮它被推断成 `ℕ` 而失败。 -/

/-- **`midpoint` 的内层线性形式**：`r ↦ 2·r m − r a − r b`。 -/
noncomputable def midpointCLM {K n : ℕ} (m a b : Fin K) : (Fin K → Pt n) →L[ℝ] Pt n :=
  (2 : ℝ) • pointProj m - pointProj a - pointProj b

/-- **`midpointCLM` 的求值**。 -/
theorem midpointCLM_apply {K n : ℕ} (m a b : Fin K) (r : Fin K → Pt n) (i : Fin n) :
    midpointCLM m a b r i = 2 * trunc r m i - trunc r a i - trunc r b i := by
  simp only [midpointCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    pointProj, Pi.sub_apply, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [trunc_apply, trunc_apply, trunc_apply]

/-- ⭐⭐ **`midpoint` 分支可微**：`∑ i, (2·trunc · m i − trunc · a i − trunc · b i)²`。 -/
theorem midpoint_differentiableAt {K n : ℕ} (m a b : ℕ) (hm : m < K) (ha : a < K) (hb : b < K)
    (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => ∑ i, (2 * trunc r m i - trunc r a i - trunc r b i) ^ 2) p := by
  have hlin : HasFDerivAt (fun r : Fin K → Pt n => midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r)
      (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩) p :=
    ContinuousLinearMap.hasFDerivAt (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩)
  have hfun : (fun r : Fin K → Pt n => ∑ i, (2 * trunc r m i - trunc r a i - trunc r b i) ^ 2)
      = fun r : Fin K → Pt n => ∑ i, (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r i) ^ 2 := by
    funext r
    exact Finset.sum_congr rfl (fun i _ => by rw [midpointCLM_apply])
  rw [hfun]
  refine DifferentiableAt.sum (u := Finset.univ) ?_
  intro i _
  have hcoord : HasFDerivAt (fun r : Fin K → Pt n => midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩ r i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
        (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩)) p :=
    ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
        (midpointCLM ⟨m, hm⟩ ⟨a, ha⟩ ⟨b, hb⟩))
  exact (Lattice.Core.hasFDerivAt_sq_comp hcoord).differentiableAt

end Lattice.Geo
