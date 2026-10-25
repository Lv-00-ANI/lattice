import Mathlib
import Lattice.Lib.Chain.RealLv00GeometryAnalytic
/-! # RealLv00GeometryDifferential

拆分自 `RealLv00Geometry.lean`（第 810–1325 行，原「第四部分：微分几何（DifferentialGeometry）」），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Geometry` 仍有效。

本模块重新声明了原文件的三项作用域设置（缺一不可）：
`noncomputable section`（原 :114）、`namespace Lattice.Lv00.Geometry`（原 :116）、
`open Real`（原 :118）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Geometry

open Real

/-! ===========================================================================
## 第四部分：微分几何（DifferentialGeometry）
===========================================================================

来源：`lvFormal/Theory/DifferentialGeometry.lean`（对应
`bootstrap/src/layer3_geometry/determinism_state.lv`）。

注意 **本部分的核心诚实结论**：上游把 `second_fundamental` 定义为**常函数 `(0,0,0)`**，
于是所有含 `gaussian_curvature` 的"定理"都退化为 `0 = 0`。
上游自己在 docstring 里承认了这一点。本文件因此：

- 把这类定理**显式改名**加 `_degenerate` 后缀，杜绝被误读为真 Theorema Egregium；
- 把**确实为真的**部分（平面/柱面曲率为 0、主曲率乘积 = K）补成真证明；
- 丢弃**为假**的 `gauss_equation`，替换为平面的精确事实。
-/

/-- 曲面参数化 `ℝ² → ℝ³`。来源 `DifferentialGeometry.Surface`。 -/
abbrev Surface := ℝ × ℝ → ℝ × ℝ × ℝ

/-- 三维点。来源 `DifferentialGeometry.Point`。 -/
abbrev Point3 := ℝ × ℝ × ℝ

/-- 第一坐标分量。来源 `coord1`。 -/
def coord1 (p : Point3) : ℝ := p.1

/-- 第二坐标分量。来源 `coord2`。 -/
def coord2 (p : Point3) : ℝ := p.2.1

/-- 第三坐标分量。来源 `coord3`。 -/
def coord3 (p : Point3) : ℝ := p.2.2

/-- 三维点积。来源 `dot3`。**与 mathlib `EuclideanSpace ℝ (Fin 3)` 的 `inner` 重复，见文件头。** -/
def dot3 (v w : Point3) : ℝ :=
  coord1 v * coord1 w + coord2 v * coord2 w + coord3 v * coord3 w

/-- 三维叉积。来源 `cross3`。**与 mathlib `cross` 重复，见文件头。** -/
def cross3 (v w : Point3) : Point3 :=
  (coord2 v * coord3 w - coord3 v * coord2 w,
   coord3 v * coord1 w - coord1 v * coord3 w,
   coord1 v * coord2 w - coord2 v * coord1 w)

/-- 切向量 `S_u`（`∂S/∂u` 的中心差分近似）。来源 `Su`。 -/
def Su (S : Surface) (u v : ℝ) (h : ℝ) : Point3 :=
  let a := S (u + h, v)
  let b := S (u - h, v)
  ((coord1 a - coord1 b) / (2 * h),
   (coord2 a - coord2 b) / (2 * h),
   (coord3 a - coord3 b) / (2 * h))

/-- 切向量 `S_v`（`∂S/∂v` 的中心差分近似）。来源 `Sv`。 -/
def Sv (S : Surface) (u v : ℝ) (h : ℝ) : Point3 :=
  let a := S (u, v + h)
  let b := S (u, v - h)
  ((coord1 a - coord1 b) / (2 * h),
   (coord2 a - coord2 b) / (2 * h),
   (coord3 a - coord3 b) / (2 * h))

/-- 第一基本形式系数 `(E, F, G)`，差分步长 `h = 1e-6`。来源 `first_fundamental`。 -/
def first_fundamental (S : Surface) (u v : ℝ) : ℝ × ℝ × ℝ :=
  let su := Su S u v 1e-6
  let sv := Sv S u v 1e-6
  (dot3 su su, dot3 su sv, dot3 sv sv)

/-- 单位法向量 `n = (S_u × S_v)/|S_u × S_v|`，退化时取 `(0,0,1)`。来源 `unit_normal`。 -/
def unit_normal (S : Surface) (u v : ℝ) : Point3 :=
  let su := Su S u v 1e-6
  let sv := Sv S u v 1e-6
  let cp := cross3 su sv
  let norm_sq := dot3 cp cp
  if norm_sq ≠ 0 then
    let nrm := Real.sqrt norm_sq
    (coord1 cp / nrm, coord2 cp / nrm, coord3 cp / nrm)
  else (0, 0, 1)

/-- **第二基本形式系数 `(L, M, N)` —— 上游定义为常函数 `(0,0,0)`。**

    注意 这是上游最大的诚实缺口：它使所有基于 `gaussian_curvature` 的"定理"退化。
    本文件保留原定义（因为采集目的是忠实存档），但在所有依赖它的定理名上加
    `_degenerate`。真正可用的版本是 `second_fundamental_numeric`。 -/
def second_fundamental (_S : Surface) (_u _v : ℝ) : ℝ × ℝ × ℝ := (0, 0, 0)

/-- 解析曲面：曲面 + 真实的第二基本形式。来源 `AnalyticSurface`。 -/
structure AnalyticSurface where
  /-- 参数化。 -/
  surface : Surface
  /-- 真实的第二基本形式系数场。 -/
  secondFF : ℝ × ℝ → ℝ × ℝ × ℝ
  /-- 曲面名。 -/
  name : String

/-- 解析曲面的高斯曲率（用真实第二基本形式）。来源 `analytic_gaussian_curvature`。 -/
def analytic_gaussian_curvature (as : AnalyticSurface) (u v : ℝ) : ℝ :=
  let (E, F, G) := first_fundamental as.surface u v
  let (L, M, N) := as.secondFF (u, v)
  let denom := E * G - F * F
  if denom ≠ 0 then (L * N - M * M) / denom else 0

/-- 标量场关于 `u` 的中心差分偏导。来源 `partial_uf`。 -/
def partial_uf (f : ℝ × ℝ → ℝ) (u v : ℝ) (h : ℝ := 1e-6) : ℝ :=
  (f (u + h, v) - f (u - h, v)) / (2 * h)

/-- 标量场关于 `v` 的中心差分偏导。来源 `partial_vf`。 -/
def partial_vf (f : ℝ × ℝ → ℝ) (u v : ℝ) (h : ℝ := 1e-6) : ℝ :=
  (f (u, v + h) - f (u, v - h)) / (2 * h)

/-- 标量场关于 `u` 的二阶中心差分。来源 `partial_uuf`。 -/
def partial_uuf (f : ℝ × ℝ → ℝ) (u v : ℝ) (h : ℝ := 1e-6) : ℝ :=
  (f (u + h, v) - 2 * f (u, v) + f (u - h, v)) / h ^ 2

/-- 标量场的混合二阶中心差分。来源 `partial_uvf`。 -/
def partial_uvf (f : ℝ × ℝ → ℝ) (u v : ℝ) (h : ℝ := 1e-6) : ℝ :=
  (f (u + h, v + h) - f (u + h, v - h) - f (u - h, v + h) + f (u - h, v - h)) / (4 * h ^ 2)

/-- 标量场关于 `v` 的二阶中心差分。来源 `partial_vvf`。 -/
def partial_vvf (f : ℝ × ℝ → ℝ) (u v : ℝ) (h : ℝ := 1e-6) : ℝ :=
  (f (u, v + h) - 2 * f (u, v) + f (u, v - h)) / h ^ 2

/-- **Christoffel 符号第二类 `Γ^k_{ij}`**（显式计算版）。
    来源 `christoffel_symbol_explicit`。
    对度量 `g = [[E,F],[F,G]]`，逆度量为 `g¹¹ = G/Δ`、`g¹² = g²¹ = -F/Δ`、`g²² = E/Δ`，
    其中 `Δ = EG - F²`。 -/
def christoffel_symbol_explicit
    (E F G puE pvE puF pvF puG pvG : ℝ) (i j k : ℕ) : ℝ :=
  let Δ := E * G - F * F
  if _h : Δ ≠ 0 then
    match i, j, k with
    | 1, 1, 1 => (G * puE - 2 * F * puF + F * pvE) / (2 * Δ)
    | 1, 2, 1 | 2, 1, 1 => (G * pvE - F * puG) / (2 * Δ)
    | 2, 2, 1 => (2 * G * pvF - G * puG - F * pvG) / (2 * Δ)
    | 1, 1, 2 => (2 * E * puF - E * pvE - F * puE) / (2 * Δ)
    | 1, 2, 2 | 2, 1, 2 => (E * puG - F * pvE) / (2 * Δ)
    | 2, 2, 2 => (E * pvG - 2 * F * pvF + F * puG) / (2 * Δ)
    | _, _, _ => 0
  else 0

/-- 由曲面算出的 Christoffel 符号第二类（差步长 `h = 1e-6`）。
    来源 `christoffel_second`。 -/
def christoffel_second (S : Surface) (u v : ℝ) (i j k : ℕ) : ℝ :=
  let h : ℝ := 1e-6
  let E : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).1
  let F : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).2.1
  let G : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).2.2
  let (E0, F0, G0) := first_fundamental S u v
  christoffel_symbol_explicit E0 F0 G0
    (partial_uf E u v h) (partial_vf E u v h)
    (partial_uf F u v h) (partial_vf F u v h)
    (partial_uf G u v h) (partial_vf G u v h)
    i j k

/-- **(B)** Christoffel 符号只依赖第一基本形式。
    上游为 `sorry`；此处给出真证明——`christoffel_second` 的定义体中
    除 `first_fundamental` 外无其它自由变量，且差步长是硬编码常量。 -/
theorem christoffel_depends_only_on_first_fundamental (S1 S2 : Surface) (u v : ℝ) (i j k : ℕ)
    (h_metric : ∀ p : ℝ × ℝ, first_fundamental S1 p.1 p.2 = first_fundamental S2 p.1 p.2) :
    christoffel_second S1 u v i j k = christoffel_second S2 u v i j k := by
  have hE : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).1)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).1) := by
    funext p; rw [h_metric p]
  have hF : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).2.1)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).2.1) := by
    funext p; rw [h_metric p]
  have hG : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).2.2)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).2.2) := by
    funext p; rw [h_metric p]
  have hff : first_fundamental S1 u v = first_fundamental S2 u v := h_metric (u, v)
  unfold christoffel_second
  rw [hE, hF, hG, hff]

/-- Riemann 张量分量 `R^1_{212}`（显式版）。来源 `riemann_1212_explicit`。 -/
def riemann_1212_explicit
    (E F G puE pvE puF pvF puG pvG : ℝ)
    (puuE puvE pvvE puuF puvF pvvF puuG puvG pvvG : ℝ) : ℝ :=
  let Δ := E * G - F * F
  if _h : Δ ≠ 0 then
    let Γ := christoffel_symbol_explicit E F G puE pvE puF pvF puG pvG
    let d1 := christoffel_symbol_explicit E F G puuE puvE puuF puvF puuG puvG 1 2 2
    let d2 := christoffel_symbol_explicit E F G puvE pvvE puvF pvvF puvG pvvG 1 1 2
    d1 - d2
      + (Γ 1 1 1) * (Γ 1 2 2) + (Γ 1 1 2) * (Γ 2 2 2)
      - (Γ 1 2 1) * (Γ 1 1 2) - (Γ 1 2 2) * (Γ 2 1 2)
  else 0

/-- 由曲面算出的 Riemann 张量分量 `R^1_{212}`。来源 `riemann_1212`。 -/
def riemann_1212 (S : Surface) (u v : ℝ) : ℝ :=
  let h : ℝ := 1e-6
  let E : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).1
  let F : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).2.1
  let G : ℝ × ℝ → ℝ := fun p => (first_fundamental S p.1 p.2).2.2
  let (E0, F0, G0) := first_fundamental S u v
  riemann_1212_explicit E0 F0 G0
    (partial_uf E u v h) (partial_vf E u v h)
    (partial_uf F u v h) (partial_vf F u v h)
    (partial_uf G u v h) (partial_vf G u v h)
    (partial_uuf E u v h) (partial_uvf E u v h) (partial_vvf E u v h)
    (partial_uuf F u v h) (partial_uvf F u v h) (partial_vvf F u v h)
    (partial_uuf G u v h) (partial_uvf G u v h) (partial_vvf G u v h)

/-- **(A)** Riemann 分量只依赖第一基本形式（上游此条有真证明，本文件改用
    `christoffel_depends_only_on_first_fundamental` 所证的同款技术重写）。 -/
theorem riemann_depends_only_on_first_fundamental (S1 S2 : Surface) (u v : ℝ)
    (h_metric : ∀ p : ℝ × ℝ, first_fundamental S1 p.1 p.2 = first_fundamental S2 p.1 p.2) :
    riemann_1212 S1 u v = riemann_1212 S2 u v := by
  have hE : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).1)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).1) := by
    funext p; rw [h_metric p]
  have hF : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).2.1)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).2.1) := by
    funext p; rw [h_metric p]
  have hG : (fun p : ℝ × ℝ => (first_fundamental S1 p.1 p.2).2.2)
          = (fun p : ℝ × ℝ => (first_fundamental S2 p.1 p.2).2.2) := by
    funext p; rw [h_metric p]
  have hff : first_fundamental S1 u v = first_fundamental S2 u v := h_metric (u, v)
  unfold riemann_1212
  rw [hE, hF, hG, hff]

/-- 由 Riemann 张量算的高斯曲率。来源 `gaussian_curvature_riemann`。 -/
def gaussian_curvature_riemann (S : Surface) (u v : ℝ) : ℝ :=
  let (E, F, G) := first_fundamental S u v
  let denom := E * G - F * F
  if denom ≠ 0 then riemann_1212 S u v / denom else 0

/-- **(A)** Theorema Egregium 的 **Riemann 形式**：Riemann 曲率只依赖第一基本形式
    —— 这正是"高斯曲率是内蕴量"的可证内核。 -/
theorem theorema_egregium_riemann (S1 S2 : Surface) (u v : ℝ)
    (h_metric : ∀ p : ℝ × ℝ, first_fundamental S1 p.1 p.2 = first_fundamental S2 p.1 p.2) :
    gaussian_curvature_riemann S1 u v = gaussian_curvature_riemann S2 u v := by
  have hR := riemann_depends_only_on_first_fundamental S1 S2 u v h_metric
  have hff : first_fundamental S1 u v = first_fundamental S2 u v := h_metric (u, v)
  unfold gaussian_curvature_riemann
  rw [hR, hff]

/-- `S` 关于 `u` 的二阶导（中心差分）。来源 `Suu`。 -/
def Suu (S : Surface) (u v : ℝ) (h : ℝ := 1e-6) : Point3 :=
  ((coord1 (S (u + h, v)) - 2 * coord1 (S (u, v)) + coord1 (S (u - h, v))) / h ^ 2,
   (coord2 (S (u + h, v)) - 2 * coord2 (S (u, v)) + coord2 (S (u - h, v))) / h ^ 2,
   (coord3 (S (u + h, v)) - 2 * coord3 (S (u, v)) + coord3 (S (u - h, v))) / h ^ 2)

/-- `S` 混合二阶导（中心差分）。来源 `Suv`。 -/
def Suv (S : Surface) (u v : ℝ) (h : ℝ := 1e-6) : Point3 :=
  ((coord1 (S (u + h, v + h)) - coord1 (S (u + h, v - h)) - coord1 (S (u - h, v + h)) +
      coord1 (S (u - h, v - h))) / (4 * h ^ 2),
   (coord2 (S (u + h, v + h)) - coord2 (S (u + h, v - h)) - coord2 (S (u - h, v + h)) +
      coord2 (S (u - h, v - h))) / (4 * h ^ 2),
   (coord3 (S (u + h, v + h)) - coord3 (S (u + h, v - h)) - coord3 (S (u - h, v + h)) +
      coord3 (S (u - h, v - h))) / (4 * h ^ 2))

/-- `S` 关于 `v` 的二阶导（中心差分）。来源 `Svv`。 -/
def Svv (S : Surface) (u v : ℝ) (h : ℝ := 1e-6) : Point3 :=
  ((coord1 (S (u, v + h)) - 2 * coord1 (S (u, v)) + coord1 (S (u, v - h))) / h ^ 2,
   (coord2 (S (u, v + h)) - 2 * coord2 (S (u, v)) + coord2 (S (u, v - h))) / h ^ 2,
   (coord3 (S (u, v + h)) - 2 * coord3 (S (u, v)) + coord3 (S (u, v - h))) / h ^ 2)

/-- **真正可用的第二基本形式**：`L = S_uu·n`、`M = S_uv·n`、`N = S_vv·n`。
    来源 `second_fundamental_numeric`。这是替代常函数 `second_fundamental` 的正解。 -/
def second_fundamental_numeric (S : Surface) (u v : ℝ) : ℝ × ℝ × ℝ :=
  let n := unit_normal S u v
  (dot3 (Suu S u v) n, dot3 (Suv S u v) n, dot3 (Svv S u v) n)

/-- 数值高斯曲率（用 `second_fundamental_numeric`）。来源 `gaussian_curvature_numeric`。 -/
def gaussian_curvature_numeric (S : Surface) (u v : ℝ) : ℝ :=
  let (E, F, G) := first_fundamental S u v
  let (L, M, N) := second_fundamental_numeric S u v
  let denom := E * G - F * F
  if denom ≠ 0 then (L * N - M * M) / denom else 0

/-- 高斯曲率 `K = (LN - M²)/(EG - F²)`。
    注意 因 `second_fundamental ≡ (0,0,0)`，此函数**恒等于 0**。来源 `gaussian_curvature`。 -/
def gaussian_curvature (S : Surface) (u v : ℝ) : ℝ :=
  let (E, F, G) := first_fundamental S u v
  let (L, M, N) := second_fundamental S u v
  let denom := E * G - F * F
  if denom ≠ 0 then (L * N - M * M) / denom else 0

/-- **(A)** `gaussian_curvature` 恒为 0 —— 这是上游 `second_fundamental ≡ 0` 的
    **直接推论**，也是所有"曲率定理"退化 trivial 的根因。上游从未陈述此事实。 -/
theorem gaussian_curvature_eq_zero (S : Surface) (u v : ℝ) : gaussian_curvature S u v = 0 := by
  unfold gaussian_curvature second_fundamental
  split <;> simp

/-- 平均曲率 `H = (EN + GL - 2FM)/(2(EG - F²))`。来源 `mean_curvature`。 -/
def mean_curvature (S : Surface) (u v : ℝ) : ℝ :=
  let (E, F, G) := first_fundamental S u v
  let (L, M, N) := second_fundamental S u v
  let denom := E * G - F * F
  if denom ≠ 0 then (E * N + G * L - 2 * F * M) / (2 * denom) else 0

/-- **(A)** `mean_curvature` 也恒为 0，同因。 -/
theorem mean_curvature_eq_zero (S : Surface) (u v : ℝ) : mean_curvature S u v = 0 := by
  unfold mean_curvature second_fundamental
  split <;> simp

/-- 主曲率 `κ₁,₂ = H ± √(H² - K)`。来源 `principal_curvatures`。 -/
def principal_curvatures (S : Surface) (u v : ℝ) : ℝ × ℝ :=
  let K := gaussian_curvature S u v
  let H := mean_curvature S u v
  let disc := H * H - K
  if disc ≥ 0 then (H - Real.sqrt disc, H + Real.sqrt disc) else (H, H)

/-- **(A)** 主曲率之积 = 高斯曲率（上游此条有真证明，本文件保留）。
    需要 `H² ≥ K` 以保证判别式分支。 -/
theorem principal_curvatures_product_eq_gaussian (S : Surface) (u v : ℝ)
    (h_disc : mean_curvature S u v ^ 2 ≥ gaussian_curvature S u v) :
    (principal_curvatures S u v).1 * (principal_curvatures S u v).2 =
      gaussian_curvature S u v := by
  have hdisc' : 0 ≤ mean_curvature S u v ^ 2 - gaussian_curvature S u v := by linarith
  unfold principal_curvatures
  simp only []
  -- 目标中判别式写作 `H * H - K`，先把 `^ 2` 归一，再用 if_pos 进入正分支
  have hcond : mean_curvature S u v * mean_curvature S u v -
      gaussian_curvature S u v ≥ 0 := by
    simpa [sq] using hdisc'
  rw [if_pos hcond]
  have hsq : Real.sqrt (mean_curvature S u v * mean_curvature S u v -
      gaussian_curvature S u v) ^ 2 =
      mean_curvature S u v * mean_curvature S u v - gaussian_curvature S u v := by
    rw [Real.sq_sqrt hcond]
  calc (mean_curvature S u v - Real.sqrt (mean_curvature S u v * mean_curvature S u v -
          gaussian_curvature S u v)) *
        (mean_curvature S u v + Real.sqrt (mean_curvature S u v * mean_curvature S u v -
          gaussian_curvature S u v))
      = mean_curvature S u v ^ 2 - Real.sqrt (mean_curvature S u v * mean_curvature S u v -
          gaussian_curvature S u v) ^ 2 := by ring
    _ = mean_curvature S u v ^ 2 - (mean_curvature S u v * mean_curvature S u v -
          gaussian_curvature S u v) := by rw [hsq]
    _ = gaussian_curvature S u v := by ring

/-- 平面 `S(u,v) = (u, v, 0)`。来源 `plane`。 -/
def plane (p : ℝ × ℝ) : Point3 := (p.1, p.2, 0)

/-- 球面（半径 `R`，球坐标）。来源 `sphere`。 -/
def sphere (R : ℝ) (p : ℝ × ℝ) : Point3 :=
  (R * Real.sin p.1 * Real.cos p.2, R * Real.sin p.1 * Real.sin p.2, R * Real.cos p.1)

/-- 圆柱面（半径 `R`）。来源 `cylinder`。 -/
def cylinder (R : ℝ) (p : ℝ × ℝ) : Point3 :=
  (R * Real.cos p.1, R * Real.sin p.1, p.2)

/-- 悬链面。来源 `catenoid`。 -/
def catenoid (p : ℝ × ℝ) : Point3 :=
  (Real.cosh p.2 * Real.cos p.1, Real.cosh p.2 * Real.sin p.1, p.2)

/-- 双曲抛物面 `z = u² - v²`。来源 `hyperbolic_paraboloid`。 -/
def hyperbolic_paraboloid (p : ℝ × ℝ) : Point3 := (p.1, p.2, p.1 ^ 2 - p.2 ^ 2)

/-- **(B)** 平面的第二基本形式（定义性，恒 `(0,0,0)`）。来源
    `plane_second_fundamental_eq`。 -/
theorem plane_second_fundamental_eq (u v : ℝ) : second_fundamental plane u v = (0, 0, 0) := rfl

/-- **(B)** 平面高斯曲率为 0。注意 因 `second_fundamental ≡ 0`，
    此命题**不构成对平面平坦性的实质证明**；真正的证明见 `plane_first_fundamental`。
    来源 `plane_gaussian_curvature_zero`，本文件加 `_degenerate` 后缀。 -/
theorem plane_gaussian_curvature_zero_degenerate (u v : ℝ) :
    gaussian_curvature plane u v = 0 :=
  gaussian_curvature_eq_zero plane u v

/-- **(B)** 柱面高斯曲率为 0（同因，退化）。来源
    `cylinder_gaussian_curvature_zero`，加 `_degenerate` 后缀。 -/
theorem cylinder_gaussian_curvature_zero_degenerate (R u v : ℝ) :
    gaussian_curvature (cylinder R) u v = 0 :=
  gaussian_curvature_eq_zero (cylinder R) u v

/-- **(A)** 平面第一基本形式精确等于 `(1, 0, 1)`：`S_u = (1,0,0)`、`S_v = (0,1,0)`
    是**精确**的（中心差分对仿射函数无误差）。这是可证的真结果，
    也是替代为假的 `gauss_equation` 的正确内核。 -/
theorem plane_first_fundamental (u v : ℝ) : first_fundamental plane u v = (1, 0, 1) := by
  norm_num [first_fundamental, Su, Sv, dot3, coord1, coord2, coord3, plane]

/-- **(A)** 平面的单位法向量精确为 `(0,0,1)`。 -/
theorem plane_unit_normal (u v : ℝ) : unit_normal plane u v = (0, 0, 1) := by
  norm_num [unit_normal, Su, Sv, cross3, dot3, coord1, coord2, coord3, plane]

/-- **(A)** 平面的数值第二基本形式 `(L, M, N) = (0, 0, 0)` —— 二阶导数
    对仿射函数精确为零，所以这才是平面平坦性的**真**证明路径。

    证明分两步：先把法向 `unit_normal plane u v` 化简为 `(0,0,1)`（精确值），
    再算三个点积。 -/
theorem plane_second_fundamental_numeric (u v : ℝ) :
    second_fundamental_numeric plane u v = (0, 0, 0) := by
  have hn : unit_normal plane u v = (0, 0, 1) := by
    norm_num [unit_normal, Su, Sv, cross3, dot3, coord1, coord2, coord3, plane]
  simp only [second_fundamental_numeric, hn]
  norm_num [Suu, Suv, Svv, dot3, coord1, coord2, coord3, plane]

/-- **(A)** 平面数值高斯曲率精确为 0（真结果，非退化）。 -/
theorem plane_gaussian_curvature_numeric_zero (u v : ℝ) :
    gaussian_curvature_numeric plane u v = 0 := by
  have hn : unit_normal plane u v = (0, 0, 1) := by
    norm_num [unit_normal, Su, Sv, cross3, dot3, coord1, coord2, coord3, plane]
  have hff : first_fundamental plane u v = (1, 0, 1) := by
    norm_num [first_fundamental, Su, Sv, dot3, coord1, coord2, coord3, plane]
  simp only [gaussian_curvature_numeric, second_fundamental_numeric, hff, hn]
  norm_num [Suu, Suv, Svv, dot3, coord1, coord2, coord3, plane]

/-- 球面的解析曲面：用已知的第二基本形式 `(R, 0, R sin²u)`。
    注意 上游给出的 `secondFF := (R, 0, R sin²u)` 只有在**单位球坐标约定**下才正确，
    且这是**声明**而非从嵌入推出。此处保留原来的声明形式。 -/
def sphereAnalytic (R : ℝ) : AnalyticSurface where
  surface := sphere R
  secondFF := fun p => (R, 0, R * (Real.sin p.1) ^ 2)
  name := "sphere"

/- **注意 上游 `sphere_analytic_curvature` 已整条丢弃（归 (C)），理由有两层：**

    **(i) 命题为假（缺奇异点假设）**：上游声称
    `analytic_gaussian_curvature (sphereAnalytic R) u v = 1/R²` 只假设 `R > 0`。
    但 `analytic_gaussian_curvature` 在 `EG - F² = 0` 时返回 `0`；
    球面 `E = R²`、`F = 0`、`G = R² sin²u`，故 `EG - F² = R⁴ sin²u`，
    在 `u = 0`（及一切 `sin u = 0` 处）分母为 `0`，函数返回 `0 ≠ 1/R²`。
    **该命题在 `u = 0` 处为假**，上游却用 `sorry` 掩盖。

    **(ii) 即使补上 `sin u ≠ 0`，它仍然不可证**：`first_fundamental` 用的是
    `h = 1e-6` 的**中心差分**，对 `sin`/`cos` **不精确**；
    要证 `Su (sphere R) 0 v 1e-6 = (0,0,0)` 需要 `Real.sin 1e-6 = 0` 这类**假命题**。
    ⇒ 数值定义本身使它不可证，**不是**补假设能救的。

    处置：**丢弃，不在此文件保留任何形状**（也不留 `sorry`）。
    真正可证的正确替代是下面的**解析**版本。 -/

/-- **解析版球面曲率（替代上游那条）**：直接给出球面第一/第二基本形式的**闭式**
    `E = R²`、`F = 0`、`G = R²sin²u`、`L = R`、`M = 0`、`N = Rsin²u`，
    用标准公式 `K = (LN - M²)/(EG - F²)`，**不经差分**，故命题可真证。 -/
def sphere_gaussian_curvature_exact (E F G L M N : ℝ) : ℝ :=
  let denom := E * G - F * F
  if denom ≠ 0 then (L * N - M * M) / denom else 0

/-- **(A)** 球面高斯曲率的**纯代数内核（机器可证的替代品）**：把
    `(E,F,G,L,M,N)` 代成球面解析值 `(R², 0, R²su², R, 0, R·su²)`，
    结论 `K = 1/R²`。这是 `field_simp` + `ring` 级的**真**命题，
    也是上游那条只配 `sorry` 的命题**在剥离数值差分后唯一站得住的核**。

    假设 `R ≠ 0`、`su ≠ 0` 正是上游缺掉的奇异点条件。 -/
theorem sphere_curvature_algebra (R : ℝ) (hR : R ≠ 0) (su : ℝ) (hsu : su ≠ 0) :
    sphere_gaussian_curvature_exact (R ^ 2) 0 (R ^ 2 * su ^ 2) R 0 (R * su ^ 2) =
      1 / R ^ 2 := by
  unfold sphere_gaussian_curvature_exact
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  have hsu2 : su ^ 2 ≠ 0 := pow_ne_zero 2 hsu
  have hden : R ^ 2 * (R ^ 2 * su ^ 2) - 0 * 0 ≠ 0 := by
    simp only [mul_zero, sub_zero]
    exact mul_ne_zero hR2 (mul_ne_zero hR2 hsu2)
  rw [if_pos hden]
  field_simp
  ring

/-- 双曲抛物面的解析曲面（第二基本形式 `(2, 0, -2)`）。来源
    `hyperbolicParaboloidAnalytic`。 -/
def hyperbolicParaboloidAnalytic : AnalyticSurface where
  surface := hyperbolic_paraboloid
  secondFF := fun _ => (2, 0, -2)
  name := "hyperbolic_paraboloid"

/-- **(A)** 双曲抛物面原点曲率 `K = -4`。
    上游此条为 `sorry`；本文件**补出真证明**：
    `first_fundamental` 在原点给出 `(E,F,G) = (1,0,1)`（差分为精确值，
    因 `u² - v²` 的差分公式对二次函数精确），故 `K = (2·(-2) - 0²)/(1·1 - 0²) = -4`。 -/
theorem hyperbolic_paraboloid_analytic_curvature_at_origin :
    analytic_gaussian_curvature hyperbolicParaboloidAnalytic 0 0 = -4 := by
  unfold analytic_gaussian_curvature hyperbolicParaboloidAnalytic hyperbolic_paraboloid
    first_fundamental Su Sv dot3 coord1 coord2 coord3
  norm_num

/-- **(A)** 正曲率蕴涵椭圆点（主曲率之积 > 0）。
    上游此条有真证明，本文件保留（依赖 `principal_curvatures_product_eq_gaussian`）。 -/
theorem positive_curvature_implies_elliptic (S : Surface) (u v : ℝ)
    (hK : gaussian_curvature S u v > 0)
    (h_disc : mean_curvature S u v ^ 2 ≥ gaussian_curvature S u v) :
    (principal_curvatures S u v).1 * (principal_curvatures S u v).2 > 0 := by
  rw [principal_curvatures_product_eq_gaussian S u v h_disc]
  exact hK

/-- **(A)** 负曲率蕴涵双曲点（主曲率之积 < 0）。 -/
theorem negative_curvature_implies_hyperbolic (S : Surface) (u v : ℝ)
    (hK : gaussian_curvature S u v < 0)
    (h_disc : mean_curvature S u v ^ 2 ≥ gaussian_curvature S u v) :
    (principal_curvatures S u v).1 * (principal_curvatures S u v).2 < 0 := by
  rw [principal_curvatures_product_eq_gaussian S u v h_disc]
  exact hK

/-- **(A)** 零曲率蕴涵平坦点。上游为 `sorry`；本文件由
    `principal_curvatures_product_eq_gaussian` **直接推出**，去掉 sorry。 -/
theorem zero_curvature_implies_flat (S : Surface) (u v : ℝ)
    (hK : gaussian_curvature S u v = 0)
    (h_disc : mean_curvature S u v ^ 2 ≥ gaussian_curvature S u v) :
    (principal_curvatures S u v).1 * (principal_curvatures S u v).2 = 0 := by
  rw [principal_curvatures_product_eq_gaussian S u v h_disc]
  exact hK

/-- **(B, 退化)** Theorema Egregium 的**退化形式**：在 `second_fundamental ≡ 0` 的
    约定下，任意两曲面的 `gaussian_curvature` 都相等（都等于 0），
    故命题**空洞为真**，**不构成**对 Theorema Egregium 的证明。
    上游以 `theorema_egregium` 之名陈述此式，本文件**改名加 `_degenerate`**。 -/
theorem theorema_egregium_degenerate (S1 S2 : Surface) (u v : ℝ)
    (_h : first_fundamental S1 u v = first_fundamental S2 u v) :
    gaussian_curvature S1 u v = gaussian_curvature S2 u v := by
  rw [gaussian_curvature_eq_zero, gaussian_curvature_eq_zero]

/-- **(B, 退化)** 等距不变性（同上，空洞为真）。上游
    `curvature_invariant_under_isometry`，改名加 `_degenerate`。 -/
theorem curvature_invariant_under_isometry_degenerate (S1 S2 : Surface) (u v : ℝ)
    (h : first_fundamental S1 u v = first_fundamental S2 u v) :
    gaussian_curvature S1 u v = gaussian_curvature S2 u v :=
  theorema_egregium_degenerate S1 S2 u v h

/-- **(B, 退化)** 局部 Gauss–Bonnet 平坦情形。上游
    `gauss_bonnet_local_flat` 是 `fun hK => hK` 级重言，本文件保留但明确标注退化。 -/
theorem gauss_bonnet_local_flat_degenerate (S : Surface) (u v : ℝ)
    (hK : gaussian_curvature S u v = 0) : gaussian_curvature S u v = 0 := hK

/-- **(A)** 平面主曲率恒为 `(0, 0)`（真结果，由 `gaussian_curvature_eq_zero` /
    `mean_curvature_eq_zero` 与判别式分支推出）。 -/
theorem plane_principal_curvatures_zero (u v : ℝ) :
    principal_curvatures plane u v = (0, 0) := by
  unfold principal_curvatures
  rw [gaussian_curvature_eq_zero, mean_curvature_eq_zero]
  norm_num


end Lattice.Lv00.Geometry
