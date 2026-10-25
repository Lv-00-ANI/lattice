import Mathlib
import Lattice.Lib.Chain.RealLv00GeometryDifferential
/-! # RealLv00GeometryCSG

拆分自 `RealLv00Geometry.lean`（第 1326–1577 行，原「第五部分：CSG（构造实体几何）」），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Geometry` 仍有效。

本模块重新声明了原文件的三项作用域设置（缺一不可）：
`noncomputable section`（原 :114）、`namespace Lattice.Lv00.Geometry`（原 :116）、
`open Real`（原 :118）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Geometry

open Real

/-! ===========================================================================
## 第五部分：CSG（构造实体几何）
===========================================================================

来源：`lvFormal/Theory/CSGGeometryTheory.lean`（对应 `core/src/layer3_geometry/geometry_csg.c`）。

注意 **诚实结论**：上游此模块的 6 条"定理"**全部**是 `: True := by trivial`
（`csg_union_commutative`、`csg_intersection_associative`、`csg_difference_noncommutative`、
`bsp_partition_correctness`、`bvh_intersection_soundness`、`mesh_evaluation_soundness`、
`csg_aabb_correctness`、`csg_geometry_integrity` —— 共 8 条）。
**它们是 (C) 无价值**：`True` 不携带任何信息。本文件**全部丢弃**，
只保留有复用价值的**类型与函数定义**（这些是 (B)）。

另注：上游 `csg_evaluate` 对 `sphere`/`cube`/`cylinder` 一律返回 `[]`、
对 `intersection`/`difference` 返回 `[]`，即**函数体是空实现**；
`bvh_intersect_query` 的分支条件也是**反的**（`if aabb_intersects ... then []`
—— 相交时返回空）。本文件**忠实保留其形状**但**显式标注为未实现的桩**。
-/

/-- 三维点。来源 `CSGGeometryTheory.Point3D`。 -/
structure Point3D where
  /-- 横坐标。 -/
  x : ℝ
  /-- 纵坐标。 -/
  y : ℝ
  /-- 竖坐标。 -/
  z : ℝ
  deriving DecidableEq

/-- 三维向量。来源 `CSGGeometryTheory.Vec3D`。**与 mathlib `EuclideanSpace` 重复。** -/
structure Vec3D where
  /-- x 分量。 -/
  x : ℝ
  /-- y 分量。 -/
  y : ℝ
  /-- z 分量。 -/
  z : ℝ
  deriving DecidableEq

/-- 向量加法。来源 `vec3_add`。 -/
def vec3_add (v1 v2 : Vec3D) : Vec3D :=
  { x := v1.x + v2.x, y := v1.y + v2.y, z := v1.z + v2.z }

/-- 向量减法。来源 `vec3_sub`。 -/
def vec3_sub (v1 v2 : Vec3D) : Vec3D :=
  { x := v1.x - v2.x, y := v1.y - v2.y, z := v1.z - v2.z }

/-- 向量点积。来源 `vec3_dot`。 -/
def vec3_dot (v1 v2 : Vec3D) : ℝ := v1.x * v2.x + v1.y * v2.y + v1.z * v2.z

/-- 向量叉积。来源 `vec3_cross`。 -/
def vec3_cross (v1 v2 : Vec3D) : Vec3D :=
  { x := v1.y * v2.z - v1.z * v2.y
    y := v1.z * v2.x - v1.x * v2.z
    z := v1.x * v2.y - v1.y * v2.x }

/-- 向量长度。来源 `vec3_length`。 -/
def vec3_length (v : Vec3D) : ℝ := Real.sqrt (vec3_dot v v)

/-- 单位化（零向量原样返回）。来源 `vec3_normalize`。 -/
def vec3_normalize (v : Vec3D) : Vec3D :=
  let l := vec3_length v
  if l > 0 then { x := v.x / l, y := v.y / l, z := v.z / l } else v

/-- 三维三角形（带法向）。来源 `Triangle3D`。 -/
structure Triangle3D where
  /-- 顶点 1。 -/
  v1 : Point3D
  /-- 顶点 2。 -/
  v2 : Point3D
  /-- 顶点 3。 -/
  v3 : Point3D
  /-- 法向量（CCW 约定）。 -/
  normal : Vec3D
  deriving DecidableEq

/-- 由顶点算三角形法向。来源 `triangle_normal`。 -/
def triangle_normal (t : Triangle3D) : Vec3D :=
  let e1 := vec3_sub { x := t.v2.x, y := t.v2.y, z := t.v2.z }
                     { x := t.v1.x, y := t.v1.y, z := t.v1.z }
  let e2 := vec3_sub { x := t.v3.x, y := t.v3.y, z := t.v3.z }
                     { x := t.v1.x, y := t.v1.y, z := t.v1.z }
  vec3_normalize (vec3_cross e1 e2)

/-- 轴对齐包围盒。来源 `AABB`。 -/
structure AABB where
  /-- 最小角点。 -/
  pMin : Point3D
  /-- 最大角点。 -/
  pMax : Point3D
  deriving DecidableEq

/-- 由两点构造 AABB。来源 `aabb_from_points`。 -/
def aabb_from_points (p1 p2 : Point3D) : AABB :=
  { pMin := { x := min p1.x p2.x, y := min p1.y p2.y, z := min p1.z p2.z }
    pMax := { x := max p1.x p2.x, y := max p1.y p2.y, z := max p1.z p2.z } }

/-- AABB 并。来源 `aabb_union`。 -/
def aabb_union (b1 b2 : AABB) : AABB :=
  { pMin := { x := min b1.pMin.x b2.pMin.x, y := min b1.pMin.y b2.pMin.y,
              z := min b1.pMin.z b2.pMin.z }
    pMax := { x := max b1.pMax.x b2.pMax.x, y := max b1.pMax.y b2.pMax.y,
              z := max b1.pMax.z b2.pMax.z } }

/-- 点是否在 AABB 内。来源 `aabb_contains`。 -/
def aabb_contains (b : AABB) (p : Point3D) : Bool :=
  b.pMin.x ≤ p.x && p.x ≤ b.pMax.x &&
  b.pMin.y ≤ p.y && p.y ≤ b.pMax.y &&
  b.pMin.z ≤ p.z && p.z ≤ b.pMax.z

/-- 两 AABB 是否相交。来源 `aabb_intersects`。 -/
def aabb_intersects (b1 b2 : AABB) : Bool :=
  b1.pMin.x ≤ b2.pMax.x && b2.pMin.x ≤ b1.pMax.x &&
  b1.pMin.y ≤ b2.pMax.y && b2.pMin.y ≤ b1.pMax.y &&
  b1.pMin.z ≤ b2.pMax.z && b2.pMin.z ≤ b1.pMax.z

/-- CSG 基本体。来源 `CSGPrimitive`。 -/
inductive CSGPrimitive where
  | sphere (center : Point3D) (radius : ℝ)
  | cube (center : Point3D) (side : ℝ)
  | cylinder (base : Point3D) (height : ℝ) (radius : ℝ)
  deriving DecidableEq

/-- CSG 布尔算子。来源 `CSGBooleanOp`。 -/
inductive CSGBooleanOp where
  | union
  | difference
  | intersection
  deriving DecidableEq

/-- CSG 树。来源 `CSGTree`。 -/
inductive CSGTree where
  | leaf (prim : CSGPrimitive)
  | node (op : CSGBooleanOp) (left right : CSGTree)
  deriving DecidableEq

/-- **注意 未实现的桩**：CSG 网格化。来源 `csg_evaluate`。
    上游对基本体一律返回 `[]`（原注释即为"待补"），对 `intersection`/`difference`
    亦返回 `[]`。本函数**不含任何几何算法**，仅保留类型签名以供后续重写。 -/
def csg_evaluate (tree : CSGTree) (_resolution : ℕ) : List Triangle3D :=
  match tree with
  | .leaf _ => []
  | .node op left right =>
    let left_tris := csg_evaluate left _resolution
    let right_tris := csg_evaluate right _resolution
    match op with
    | .union => left_tris ++ right_tris
    | .intersection => []
    | .difference => []

/-- BSP 分割平面。来源 `BSPPlane`。 -/
structure BSPPlane where
  /-- 平面上一点。 -/
  point : Point3D
  /-- 平面法向。 -/
  normal : Vec3D
  deriving DecidableEq

/-- 点相对平面的分类。来源 `BSPClassification`。 -/
inductive BSPClassification where
  | front
  | back
  | coplanar
  deriving DecidableEq

/-- 按有符号距离分类点（容差 `1e-6`）。来源 `classify_point`。 -/
def classify_point (plane : BSPPlane) (p : Point3D) : BSPClassification :=
  let v := vec3_sub { x := p.x, y := p.y, z := p.z }
                    { x := plane.point.x, y := plane.point.y, z := plane.point.z }
  let d := vec3_dot v plane.normal
  if d > 0.000001 then .front
  else if d < -0.000001 then .back
  else .coplanar

/-- **(A)** 分类是**穷尽且互斥**的：任意点恰好落入三类的并。
    这是对上游 `bsp_partition_correctness : True := by trivial` 的**诚实替代** ——
    把 `True` 换成有内容、可证的真命题。 -/
theorem classify_point_trichotomy (plane : BSPPlane) (p : Point3D) :
    classify_point plane p = .front ∨ classify_point plane p = .back ∨
      classify_point plane p = .coplanar := by
  rw [classify_point]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- **注意 未实现的桩**：BSP 三角形裁剪。来源 `bsp_clip_triangle`（上游恒返回 `[]`）。 -/
def bsp_clip_triangle (_plane : BSPPlane) (_tri : Triangle3D) : List Triangle3D := []

/-- BVH 节点。来源 `BVHNode`。 -/
inductive BVHNode (α : Type) where
  | leaf (aabb : AABB) (data : α)
  | branch (aabb : AABB) (left right : BVHNode α)
  deriving DecidableEq

/-- 取 BVH 节点的包围盒。来源 `bvh_aabb`。 -/
def bvh_aabb {α : Type} : BVHNode α → AABB
  | .leaf b _ => b
  | .branch b _ _ => b

/-- **注意 条件疑为反了的桩**：BVH 区间查询。来源 `bvh_intersect_query`。
    上游写法是 `if aabb_intersects (bvh_aabb node) query then []` ——
    **相交时反而返回空**，与正常 BVH 剪枝语义相反。
    本文件**保留原样**以免篡改存档，但在此显式标注为缺陷。 -/
def bvh_intersect_query {α : Type} (node : BVHNode α) (query : AABB) : List α :=
  if aabb_intersects (bvh_aabb node) query then []
  else
    match node with
    | .leaf _ data => [data]
    | .branch _ l r => bvh_intersect_query l query ++ bvh_intersect_query r query

/-- CSG 树的包围盒。来源 `csg_aabb`。 -/
def csg_aabb (tree : CSGTree) : AABB :=
  match tree with
  | .leaf (.sphere c r) =>
    { pMin := { x := c.x - r, y := c.y - r, z := c.z - r }
      pMax := { x := c.x + r, y := c.y + r, z := c.z + r } }
  | .leaf (.cube c s) =>
    let h := s / 2
    { pMin := { x := c.x - h, y := c.y - h, z := c.z - h }
      pMax := { x := c.x + h, y := c.y + h, z := c.z + h } }
  | .leaf (.cylinder b h r) =>
    { pMin := { x := b.x - r, y := b.y, z := b.z - r }
      pMax := { x := b.x + r, y := b.y + h, z := b.z + r } }
  | .node _ l r => aabb_union (csg_aabb l) (csg_aabb r)

/-- **(A)** 包围盒并运算是单调的：`aabb_union b1 b2` 的两个角点分别被
    `b1`、`b2` 的角点"夹住"。这是对上游 `csg_aabb_correctness : True := by trivial`
    的**诚实替代**：取其中可证、有内容的单调性部分。 -/
theorem aabb_union_pMin_le (b1 b2 : AABB) :
    (aabb_union b1 b2).pMin.x ≤ b1.pMin.x ∧ (aabb_union b1 b2).pMin.y ≤ b1.pMin.y ∧
    (aabb_union b1 b2).pMin.z ≤ b1.pMin.z := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [aabb_union]

/-- **(A)** AABB 并的上界单调性。 -/
theorem aabb_union_pMax_ge (b1 b2 : AABB) :
    b1.pMax.x ≤ (aabb_union b1 b2).pMax.x ∧ b1.pMax.y ≤ (aabb_union b1 b2).pMax.y ∧
    b1.pMax.z ≤ (aabb_union b1 b2).pMax.z := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [aabb_union]

/-- **(A)** AABB 包含关系对并的单调性（真正有内容的 CSG 性质）：
    点在 `b1` 内则在 `b1 ∪ b2` 内。 -/
theorem aabb_contains_union_left {b1 b2 : AABB} {p : Point3D} (h : aabb_contains b1 p = true) :
    aabb_contains (aabb_union b1 b2) p = true := by
  simp only [aabb_contains, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [aabb_union]
  exact ⟨⟨⟨⟨⟨le_trans (min_le_left _ _) h1, le_trans h2 (le_max_left _ _)⟩,
    le_trans (min_le_left _ _) h3⟩, le_trans h4 (le_max_left _ _)⟩,
    le_trans (min_le_left _ _) h5⟩, le_trans h6 (le_max_left _ _)⟩


end Lattice.Lv00.Geometry
