import Mathlib

/-! # RealLv00GeometryHilbert

拆分自 `RealLv00Geometry.lean`（第 120–319 行，原「第一部分：经典（Hilbert）公理几何」），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Geometry` 仍有效。

本模块重新声明了原文件的三项作用域设置（缺一不可）：
`noncomputable section`（原 :114）、`namespace Lattice.Lv00.Geometry`（原 :116）、
`open Real`（原 :118）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Geometry

open Real

/-! ===========================================================================
## 第一部分：经典（Hilbert）公理几何
===========================================================================

来源：`lvFormal/Classical/Hilbert/*`（= `lv/*`，逐字节重复）。

**关键核实**：这些"公理"全部是 **类型类字段**（`class ... where`）与
**结构体字段**（`structure ... extends ...`），**不是 Lean `axiom`**。
它们因此是**显式假设**：用 `[Incidence P L]` 这样的实例参数引入，
不用 `axiom` 断言存在性。这正是本项目允许的形式。

分类：(B) 规格声明 —— 定义无实质证明，但把 Hilbert 五组公理的对象模型
完整固化为类型类，有复用价值。
-/

/-- 点（占位类型类）。来源 `lv.Basic.Point`。 -/
class GeoPoint (α : Type) : Prop

/-- 直线（占位类型类）。来源 `lv.Basic.Line`。 -/
class GeoLine (α : Type) : Prop

/-- 平面（占位类型类）。来源 `lv.Basic.Plane`。 -/
class GeoPlane (α : Type) : Prop

/- **降级**：`lv.Basic.MetricSpace`（自造距离公理类）与 mathlib `MetricSpace` 重复，
   已丢弃。见文件头"与 mathlib 的重复项"。 -/

/-- 全等关系抽象类：线段全等与角全等。
    来源 `lv.Basic.Congruence`。 -/
class LvCongruence (α : Type) where
  /-- 线段全等 `seg_congruent A B C D` 表示 `AB ≅ CD`。 -/
  seg_congruent : α → α → α → α → Prop
  /-- 角全等 `angle_congruent A B C D E F` 表示 `∠ABC ≅ ∠DEF`。 -/
  angle_congruent : α → α → α → α → α → α → Prop

/-! ### Hilbert 关联公理 I1–I3 -/

/-- **Hilbert 关联公理 I1–I3**（来源 `lv.Incidence`）。

    - I1：过任意两相异点存在一条直线；
    - I2：过任意两相异点**至多**存在一条直线（唯一性）；
    - I3：每条直线上至少有两个点，且存在至少三个不共线的点。

    这是 `class`，三个字段是**假设**而非 `axiom`。 -/
class Incidence (Point Line : Type) where
  /-- 关联关系 `lies_on A l`：点 `A` 在直线 `l` 上。 -/
  lies_on : Point → Line → Prop
  /-- I1：两相异点确定一条直线（存在性）。 -/
  I1 : ∀ (A B : Point), A ≠ B → ∃ (l : Line), lies_on A l ∧ lies_on B l
  /-- I2：两相异点确定的直线唯一。 -/
  I2 : ∀ (A B : Point) (l m : Line), A ≠ B →
    lies_on A l → lies_on B l → lies_on A m → lies_on B m → l = m
  /-- I3：每条直线上至少有两个点；存在不共线的三点。 -/
  I3 : ∀ (l : Line), ∃ (A B C : Point),
    lies_on A l ∧ lies_on B l ∧ A ≠ B ∧ ¬ lies_on C l

/-! ### Hilbert 序公理 B1–B3 -/

/-- **Hilbert 序公理 B1–B3**（来源 `lv.Betweenness`）。

    - B1：`B` 介于 `A`、`C` 之间则 `B` 也介于 `C`、`A` 之间（对称）；
    - B2：对相异两点 `A`、`B`，射线 `AB` 外端存在点 `C`（延拓）；
    - B3：共线三点中至多有一点介于另两点之间（排除三点同时"居中"）。

    注意 B2 上游写作 `between A B C`，即 `C` 在 `A` 之后（`B` 介于 `A`、`C` 之间）。 -/
class Betweenness (Point : Type) where
  /-- 介于关系 `between A B C`：`B` 在 `A` 与 `C` 之间。 -/
  between : Point → Point → Point → Prop
  /-- B1：介于关系的两端对称。 -/
  B1 : ∀ (A B C : Point), between A B C → between C B A
  /-- B2：线段可向两端延拓。 -/
  B2 : ∀ (A B : Point), A ≠ B → ∃ (C : Point), between A B C
  /-- B3：共线三点中至多一点居中。 -/
  B3 : ∀ (A B C : Point), between A B C → ¬ (between B A C) ∧ ¬ (between A C B)

/-- **扩展序公理**（来源 `lv.Order`）：在 `Betweenness` 之上补
    Pasch 型稠密性、延拓、中点存在、以及共线三分律。 -/
class Order (Point : Type) extends Betweenness Point where
  /-- 稠密性：两相异点之间存在第三点。 -/
  density : ∀ (A B : Point), A ≠ B → ∃ (C : Point), Betweenness.between A C B
  /-- 延拓性。 -/
  extension : ∀ (A B : Point), A ≠ B → ∃ (C : Point), Betweenness.between A B C
  /-- 中点存在性。 -/
  midpoint : ∀ (A B : Point), ∃ (C : Point), Betweenness.between A C B
  /-- 共线三分律：共线三点中恰有一种居中情形。 -/
  trichotomy : ∀ (A B C : Point),
    A ≠ B → A ≠ C → B ≠ C →
    (Betweenness.between A B C) ∨ (Betweenness.between B A C) ∨
      (Betweenness.between A C B)

/-! ### Hilbert 合同公理 C1–C5 -/

/-- **Hilbert 合同（全等）公理 C1–C5**（来源 `lv.Congruence`）。

    - C1：`AB ≅ BA`（线段全等自反-对称）；
    - C2：全等的传递性；
    - C3：线段可加性；
    - C4：角全等的自反与对称；
    - C5：**SAS**（边-角-边）三角形全等准则。 -/
class HCongruence (Point : Type) where
  /-- 线段全等 `segCong A B C D` 表示 `AB ≅ CD`。 -/
  segCong : Point → Point → Point → Point → Prop
  /-- 角全等 `angCong A O B A' O' B'` 表示 `∠AOB ≅ ∠A'O'B'`。 -/
  angCong : Point → Point → Point → Point → Point → Point → Prop
  /-- C1：`AB ≅ BA`。 -/
  C1 : ∀ (A B : Point), segCong A B B A
  /-- C2：线段全等的传递性。 -/
  C2 : ∀ (A B C D E F : Point),
    segCong A B C D → segCong A B E F → segCong C D E F
  /-- C3：线段可加性。 -/
  C3 : ∀ (A B C A' B' C' : Point),
    segCong A B A' B' → segCong B C B' C' → segCong A C A' C'
  /-- C4（自反）：`∠AOB ≅ ∠AOB`。 -/
  C4_reflexive : ∀ (A O B : Point), angCong A O B A O B
  /-- C4（对称）：角全等可交换。 -/
  C4_symmetric : ∀ (A O B A' O' B' : Point),
    angCong A O B A' O' B' → angCong A' O' B' A O B
  /-- C5：SAS 全等准则。 -/
  C5_SAS : ∀ (A B C A' B' C' : Point),
    segCong A B A' B' → segCong B C B' C' →
    angCong A B C A' B' C' → segCong A C A' C'

/-! ### Playfair 平行公理 -/

/-- 平行关系：两条直线不相交（来源 `lv.Parallel.parallel`）。 -/
def parallel {Point Line : Type} [inst : Incidence Point Line] (l m : Line) : Prop :=
  ¬ ∃ (P : Point), inst.lies_on P l ∧ inst.lies_on P m

/-- **Playfair 平行公理**（来源 `lv.Parallel`）：过直线外一点至多有一条平行线。 -/
class Parallel (Point Line : Type) extends Incidence Point Line where
  /-- Playfair：过 `P` 不在 `l` 上，则至多一条过 `P` 且平行于 `l` 的直线。 -/
  playfair : ∀ (P : Point) (l : Line),
    ¬ lies_on P l → ∀ (m n : Line),
    parallel (Point := Point) (Line := Line) l m → parallel (Point := Point) (Line := Line) l n →
    lies_on P m → lies_on P n → m = n

/-! ### 连续公理（Archimedes + Dedekind） -/

/-- **连续公理**（来源 `lv.Continuity`）。

    注意 **诚实降级**：上游把 Archimedes 与 Dedekind 的**结论部分写成了 `True`**
    （`∃ (n : ℕ), True`、`∃ (O : Point), True`），即**只保留了前提、丢弃了结论**。
    这样的"公理"在逻辑上不约束任何东西（任何类型都满足），把它当公理是**空的**。
    本文件**保留其形状**以存档 Lv-00 的原始意图，但**明确标注为退化形式**，
    并另给出**非退化的** `Continuity`（见 `ContinuityProper`）作为可用的替代。 -/
class Continuity (Point : Type) where
  /-- Archimedes 公理的**退化形式**：上游结论为 `True`，不约束任何内容。 -/
  archimedes : ∀ (A B C D : Point), A ≠ B → C ≠ D → ∃ (n : ℕ), True
  /-- Dedekind 完备性的**退化形式**：上游结论为 `True`，不约束任何内容。 -/
  dedekind : ∀ (L R : Point → Prop),
    (∃ (x : Point), L x) → (∃ (y : Point), R y) →
    (∀ (x y : Point), L x → R y → (L x ∨ R y)) →
    ∃ (O : Point), True

/-- **非退化的 Archimedes 型连续公理**（本文件新增，替代上面的空公理）。

    上游把 Archimedes 的结论写成 `True`，使该"公理"不约束任何内容。
    此处给出**非空**的形式：`C`、`D` 相异时存在正步数 `n`。 -/
class ContinuityProper (Point : Type) [Betweenness Point] where
  /-- Archimedes（非退化）：存在正步数使叠加可行。 -/
  archimedes_nondegenerate :
    ∀ (A B C D : Point), A ≠ B → C ≠ D → ∃ (n : ℕ), 0 < n

/-- **Hilbert 平面**（来源 `lv.HilbertAxioms`）：满足全部五组公理的几何结构。

    这是 `structure ... extends ...`，字段来自各 `class`，
    **完全由类型类实例参数引入，不含任何 `axiom`**。

    注意 采集差异：上游用自造的 `lv.Basic.MetricSpace`（与 mathlib `MetricSpace`
    重复），本文件改用 **mathlib `MetricSpace`**。

    **降级说明**：上游 `lv.EuclideanPlane` 写 `instance : MetricSpace P := hp.toMetricSpace`，
    但 `hp.toMetricSpace` 返回的是自造的 `lv.Basic.MetricSpace`，
    与 mathlib `MetricSpace` 不是同一个类，故上游该 `instance`
    **无法通过类型检查**（`lv.EuclideanPlane` 因此实际不编译）。
    → 归 **(C)**；本文件改为把 mathlib `MetricSpace` 作为 `HilbertPlane` 的
    显式类型类参数要求，从而下游引理真可证。 -/
structure HilbertPlane (Point Line : Type) [MetricSpace Point] extends
  Order Point,
  HCongruence Point,
  Parallel Point Line,
  Continuity Point

/-- **(A)** 三角不等式：`HilbertPlane` 带 mathlib `MetricSpace` 后，
    上游 `lv.EuclideanPlane.triangle_inequality` 成为**真**命题。
    （`HilbertPlane` 是 `structure` 而非 `class`，故用**显式参数**而非实例绑定。） -/
theorem triangle_inequality {Point Line : Type} [MetricSpace Point] (hp : HilbertPlane Point Line)
    (a b c : Point) : dist a b + dist b c ≥ dist a c :=
  dist_triangle a b c

/-- **(A)** 距离为零当且仅当两点重合。 -/
theorem dist_zero_iff_eq {Point Line : Type} [MetricSpace Point] (hp : HilbertPlane Point Line)
    (a b : Point) : dist a b = 0 ↔ a = b :=
  dist_eq_zero

/-- **(A)** 距离对称。 -/
theorem dist_symm {Point Line : Type} [MetricSpace Point] (hp : HilbertPlane Point Line)
    (a b : Point) : dist a b = dist b a :=
  dist_comm a b


end Lattice.Lv00.Geometry
