import Mathlib
import Lattice.Lib.Chain.RealLv00GeometrySymbolics
/-! # RealLv00GeometryAnalytic

拆分自 `RealLv00Geometry.lean`（第 549–809 行，原「第三部分：平面解析几何（GeometryPresetDefs + PresetGeometryDefs）」），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Geometry` 仍有效。

本模块重新声明了原文件的三项作用域设置（缺一不可）：
`noncomputable section`（原 :114）、`namespace Lattice.Lv00.Geometry`（原 :116）、
`open Real`（原 :118）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Geometry

open Real

/-! ===========================================================================
## 第三部分：平面解析几何（GeometryPresetDefs + PresetGeometryDefs）
===========================================================================

来源：`lvFormal/Theory/GeometryPresetDefs.lean` 与 `PresetGeometryDefs.lean`。
-/

/-- 平面点（ℝ 坐标）。来源 `GeometryPresetDefs.Pt`。 -/
structure Pt where
  /-- 横坐标。 -/
  x : ℝ
  /-- 纵坐标。 -/
  y : ℝ
  deriving DecidableEq

/-- 欧氏距离。来源 `GeometryPresetDefs.dist`。 -/
def dist (p q : Pt) : ℝ := Real.sqrt ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2)

/-- 平移。来源 `GeometryPresetDefs.translate`。 -/
def translate (p : Pt) (dx dy : ℝ) : Pt := { x := p.x + dx, y := p.y + dy }

/-- 绕 `center` 旋转 `angle_rad`。来源 `GeometryPresetDefs.rotate`。 -/
def rotate (p center : Pt) (angle_rad : ℝ) : Pt :=
  let dx := p.x - center.x
  let dy := p.y - center.y
  let c := Real.cos angle_rad
  let s := Real.sin angle_rad
  { x := center.x + dx * c - dy * s, y := center.y + dx * s + dy * c }

/-- 以 `center` 为中心缩放 `s` 倍并旋转 `θ`。来源 `scale_rotate`。 -/
def scale_rotate (p center : Pt) (s θ : ℝ) : Pt :=
  let dx := p.x - center.x
  let dy := p.y - center.y
  let c := Real.cos θ
  let sn := Real.sin θ
  { x := center.x + s * (dx * c - dy * sn), y := center.y + s * (dx * sn + dy * c) }

/-- `∠ABC`（弧度），退化时返回 0。来源 `GeometryPresetDefs.angle`。 -/
def angle (A B C : Pt) : ℝ :=
  let vBA := (A.x - B.x, A.y - B.y)
  let vBC := (C.x - B.x, C.y - B.y)
  let dot := vBA.1 * vBC.1 + vBA.2 * vBC.2
  let nBA := Real.sqrt (vBA.1 ^ 2 + vBA.2 ^ 2)
  let nBC := Real.sqrt (vBC.1 ^ 2 + vBC.2 ^ 2)
  if nBA = 0 ∨ nBC = 0 then 0 else Real.arccos (dot / (nBA * nBC))

/-- 三角形相似性（存在正比例 + 旋转 + 平移）。来源 `similarity`。 -/
def similarity (A B D E : Pt) : Prop :=
  ∃ (s : ℝ) (θ : ℝ) (tx ty : ℝ),
    s > 0 ∧
    D = translate (scale_rotate A A s θ) tx ty ∧
    E = translate (scale_rotate B A s θ) tx ty

/-- 交比。来源 `cross_ratio`。 -/
def cross_ratio (A B C D : Pt) : ℝ :=
  let AC := dist A C
  let BC := dist B C
  let AD := dist A D
  let BD := dist B D
  if BC = 0 ∨ BD = 0 then 0 else (AC * BD) / (BC * AD)

/-- 调和点列 `(A,B;C,D) = -1`。来源 `is_harmonic`。 -/
def is_harmonic (A B C D : Pt) : Prop := cross_ratio A B C D = -1

/-- 鞋带公式（有向面积的两倍）。来源 `shoelace_sum`。 -/
def shoelace_sum (pts : List Pt) : ℝ :=
  match pts with
  | [] => 0
  | [_p] => 0
  | _ps =>
    let pairs := List.zip pts (pts.tail ++ [pts.head?].filterMap id)
    (pairs.map (fun (p, q) => p.x * q.y - q.x * p.y)).sum

/-- 多边形面积（鞋带公式）。来源 `polygon_area`。 -/
def polygon_area (pts : List Pt) : ℝ := |shoelace_sum pts| / 2

/-- 海伦公式（半周长形式）。来源 `triangle_area_sss`。 -/
def triangle_area_sss (a b c : ℝ) : ℝ :=
  let s := (a + b + c) / 2
  Real.sqrt (s * (s - a) * (s - b) * (s - c))

/-- 海伦公式（标准形式）。来源 `heron_formula_standard`。 -/
def heron_formula_standard (a b c : ℝ) : ℝ :=
  (1 / 4) * Real.sqrt ((a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c))

/-- 正 `n` 边形边长（外接圆半径 `R`）。来源 `regular_polygon_edge_length`。 -/
def regular_polygon_edge_length (n : ℕ) (R : ℝ) : ℝ :=
  if n < 3 ∨ R ≤ 0 then 0 else 2 * R * Real.sin (Real.pi / (n : ℝ))

/-- 三角形相似。来源 `triangle_similarity`。 -/
def triangle_similarity (A B C D E F : Pt) : Prop :=
  ∃ (s : ℝ) (θ : ℝ) (tx ty : ℝ),
    s > 0 ∧
    D = translate (scale_rotate A A s θ) tx ty ∧
    E = translate (scale_rotate B A s θ) tx ty ∧
    F = translate (scale_rotate C A s θ) tx ty

/- **降级 (C)**：上游 `GeometryPresetDefs.lean` 尾部全部 7 条
   （`shoelace_sum_cons_cons`、`shoelace_triangulate`、`heron_formula_standard_valid`、
   `dot_product_scales`、`norm_sq_scales`、`angle_invariant_under_similarity`）
   **证明体全为 `sorry`**，即上游自称的"0 sorry 干净模块"在这两个文件上不成立。
   → 全部丢弃，不在本文件出现。 -/

/-- 带标签的平面点。来源 `PresetGeometryDefs.LvPoint`。 -/
structure LvPoint where
  /-- 点名。 -/
  label : String
  /-- 坐标。 -/
  coord : Pt

/-- 由两点确定的直线。来源 `PresetGeometryDefs.LvLine`。 -/
structure LvLine where
  /-- 端点 A。 -/
  a : LvPoint
  /-- 端点 B。 -/
  b : LvPoint

/-- 三点共线（叉积判据）。来源 `PresetGeometryDefs.collinear`。 -/
def collinear (A B C : LvPoint) : Prop :=
  (B.coord.x - A.coord.x) * (C.coord.y - A.coord.y) =
    (C.coord.x - A.coord.x) * (B.coord.y - A.coord.y)

/-- 带标签点之间的距离。来源 `PresetGeometryDefs.dist`。 -/
def lvDist (p q : LvPoint) : ℝ := dist p.coord q.coord

/-- 等边三角形。来源 `is_equilateral`。 -/
def is_equilateral (A B C : LvPoint) : Prop :=
  lvDist A B = lvDist B C ∧ lvDist B C = lvDist C A

/-- 点在直线上。来源 `on_line`。 -/
def on_line (P : LvPoint) (L : LvLine) : Prop := collinear P L.a L.b

/-- 重心。来源 `centroid`。 -/
def centroid (A B C : LvPoint) : LvPoint :=
  { label := s!"centroid_({A.label},{B.label},{C.label})"
    coord := { x := (A.coord.x + B.coord.x + C.coord.x) / 3
               y := (A.coord.y + B.coord.y + C.coord.y) / 3 } }

/-- 外心（余切/行列式公式）。来源 `circumcenter`。 -/
def circumcenter (A B C : LvPoint) : LvPoint :=
  let d := 2 * (A.coord.x * (B.coord.y - C.coord.y) +
                B.coord.x * (C.coord.y - A.coord.y) +
                C.coord.x * (A.coord.y - B.coord.y))
  if d = 0 then A
  else
    let ux := ((A.coord.x ^ 2 + A.coord.y ^ 2) * (B.coord.y - C.coord.y) +
               (B.coord.x ^ 2 + B.coord.y ^ 2) * (C.coord.y - A.coord.y) +
               (C.coord.x ^ 2 + C.coord.y ^ 2) * (A.coord.y - B.coord.y)) / d
    let uy := ((A.coord.x ^ 2 + A.coord.y ^ 2) * (C.coord.x - B.coord.x) +
               (B.coord.x ^ 2 + B.coord.y ^ 2) * (A.coord.x - C.coord.x) +
               (C.coord.x ^ 2 + C.coord.y ^ 2) * (B.coord.x - A.coord.x)) / d
    { label := s!"circum_({A.label},{B.label},{C.label})"
      coord := { x := ux, y := uy } }

/-- 垂心（`OH = 3OG`）。来源 `orthocenter`。 -/
def orthocenter (A B C : LvPoint) : LvPoint :=
  let O := circumcenter A B C
  let G := centroid A B C
  { label := s!"ortho_({A.label},{B.label},{C.label})"
    coord := { x := O.coord.x + 3 * (G.coord.x - O.coord.x)
               y := O.coord.y + 3 * (G.coord.y - O.coord.y) } }

/-- 角平分线（退化判据：等距）。来源 `is_angle_bisector`。 -/
def is_angle_bisector (L : LvLine) (A B C : LvPoint) : Prop :=
  on_line B L ∧ (lvDist A L.a = lvDist C L.a)

/-- 中垂线。来源 `is_perpendicular_bisector`。 -/
def is_perpendicular_bisector (L : LvLine) (A B : LvPoint) : Prop :=
  let M : LvPoint :=
    { label := s!"mid_({A.label},{B.label})"
      coord := { x := (A.coord.x + B.coord.x) / 2, y := (A.coord.y + B.coord.y) / 2 } }
  on_line M L ∧
  (L.a.coord.x - L.b.coord.x) * (A.coord.x - B.coord.x) +
  (L.a.coord.y - L.b.coord.y) * (A.coord.y - B.coord.y) = 0

/-- 由三点确定的圆：共线时为 `none`。来源 `circle_defined_by`。
    注意 v17 修复（W2）：原稿用 dependent-if `if _h : collinear A B C`，并注释称
    "Lean 会为 `Prop` 自动补经典判定" —— **该假设是错的**。`decide`/`dite` 的
    `Decidable` 实例搜索**不会**为一般 `Prop` 自动合成（只有 `Classical.decEq`-风格
    的经典实例在 `open Classical` 或 `noncomputable`+`Classical.propDecidable` 下才可用），
    故 `:725:2` 报 **`failed to synthesize Decidable (collinear A B C)`**。
    ⇒ 正解（**与 `RealHypothesisTesting` 同一修法**）：把判定写在**内联的展开式**上 ——
    叉积判据是两个 `ℝ` 表达式的相等，`Decidable` 对 `ℝ` 的 `=` **有**实例，
    而内联式与 `collinear A B C` **定义等价** ⟹ 语义完全不变，
    **两条定理的陈述逐字不变**。 -/
def circle_defined_by (A B C : LvPoint) : Option (LvPoint × ℝ) :=
  if _h : (B.coord.x - A.coord.x) * (C.coord.y - A.coord.y) =
      (C.coord.x - A.coord.x) * (B.coord.y - A.coord.y) then none
  else
    let O := circumcenter A B C
    some (O, lvDist O A)

/-- **(A)** 非共线三点确定的圆非 `none`。 -/
theorem circle_defined_by_noncollinear (A B C : LvPoint) (h : ¬ collinear A B C) :
    circle_defined_by A B C ≠ none := by
  -- v17 修复（W2）：`unfold` **不做 β-归约**（STYLE 已登记），故 `def` 体里的
  -- `dite` 仍埋在 λ 内 ⟹ `rw [dif_neg h]` 报
  -- `did not find instance of the pattern … dite (collinear A B C) ?m ?m`。
  -- ⇒ 改写为 `simp only [circle_defined_by, dif_neg h]`（`simp` **会**做 β-归约）。
  -- 侧条件按**内联式**给（与定义体的判别式逐字同形）。
  simp only [circle_defined_by, dif_neg (by simpa only [collinear] using h)]
  exact Option.noConfusion

/-- **(A)** 共线三点确定的圆为 `none`。 -/
theorem circle_defined_by_collinear (A B C : LvPoint) (h : collinear A B C) :
    circle_defined_by A B C = none := by
  -- v17 修复（W2）：同上，`rw [dif_pos h]` → `simp only [circle_defined_by, dif_pos h]`。
  simp only [circle_defined_by, dif_pos (by simpa only [collinear] using h)]

/-- 介于关系（参数化）。来源 `PresetGeometryDefs.between`。 -/
def between (A B C : LvPoint) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
    B.coord.x = A.coord.x + t * (C.coord.x - A.coord.x) ∧
    B.coord.y = A.coord.y + t * (C.coord.y - A.coord.y)

/-- **(A)** 共线自反：`collinear A A B`。 -/
theorem collinear_refl (A B : LvPoint) : collinear A A B := by
  unfold collinear
  ring

/-- **(A)** 共线对称：`collinear A B C → collinear C B A`。 -/
theorem collinear_symm (A B C : LvPoint) (h : collinear A B C) : collinear C B A := by
  unfold collinear at h ⊢
  linarith

/-- **(A)** 介于蕴涵共线（上游此条有真证明）。 -/
theorem collinear_of_between (A B C : LvPoint) (h_bet : between A B C) :
    collinear A B C := by
  rcases h_bet with ⟨t, _ht0, _ht1, hx, hy⟩
  unfold collinear
  calc
    (B.coord.x - A.coord.x) * (C.coord.y - A.coord.y)
        = (t * (C.coord.x - A.coord.x)) * (C.coord.y - A.coord.y) := by rw [hx]; ring
    _ = (C.coord.x - A.coord.x) * (t * (C.coord.y - A.coord.y)) := by ring
    _ = (C.coord.x - A.coord.x) * (B.coord.y - A.coord.y) := by rw [hy]; ring

/-- **(B)** 距离相等蕴涵距离平方相等（上游 `sq_dist_eq_of_dist_eq` 有真证明）。 -/
theorem sq_dist_eq_of_dist_eq {A B C D : LvPoint} (h : lvDist A B = lvDist C D) :
    (A.coord.x - B.coord.x) ^ 2 + (A.coord.y - B.coord.y) ^ 2 =
    (C.coord.x - D.coord.x) ^ 2 + (C.coord.y - D.coord.y) ^ 2 := by
  unfold lvDist dist at h
  have h1 : 0 ≤ (A.coord.x - B.coord.x) ^ 2 + (A.coord.y - B.coord.y) ^ 2 := by positivity
  have h2 : 0 ≤ (C.coord.x - D.coord.x) ^ 2 + (C.coord.y - D.coord.y) ^ 2 := by positivity
  exact (Real.sqrt_inj h1 h2).mp h

/-- **(A)** 同一圆的定义蕴涵共线性质保持不变。 -/
theorem circle_inj_implies_noncollinear (A B C D E F : LvPoint)
    (h1 : circle_defined_by A B C = circle_defined_by D E F) (h2 : ¬ collinear A B C) :
    ¬ collinear D E F := by
  intro hcol
  have h_none : circle_defined_by D E F = none := circle_defined_by_collinear D E F hcol
  have h_none' : circle_defined_by A B C = none := by rw [h1, h_none]
  exact circle_defined_by_noncollinear A B C h2 h_none'

/- **降级 (C)**：`dist_additive_of_collinear` 与
   `circumcenter_equals_centroid_of_equilateral`
   **证明体为 `sorry`** → 丢弃。
   （由 `circumcenter_equals_centroid_of_equilateral` 推出的
   `circumcenter_equals_orthocenter_of_equilateral` 因此也是**悬空**的，
   其 `have` 步骤引用了不存在的证明 → 一并丢弃。） -/


end Lattice.Lv00.Geometry
