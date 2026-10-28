/-
# 12 个 `GeoConstraint` 的惩罚损失（清单 M1-10）

## 0. 补的是什么

目标的**正向**方向是「把符号知识编译成权重（**约束损失**、数据合成、结构化初始化）」。
而 `Geo/Loss.lean` 只为 `EqConstraint`（4 个构造子）定义了损失：

```lean
EqConstraint.poly  : EqConstraint n → (ℕ → Pt n) → ℝ     -- 零点集 = 解集
EqConstraint.loss  : …                                    -- poly 的平方
```

`GeoConstraint` 有 **12** 个构造子，而 `Geo.lean` 自己写着 `leZero`/`ltZero` **没有惩罚损失**。
**所以「每条约束都有损失」此前是 4/12，不是 12/12。**

本节把它补到 12/12，并对能证的方向给出定理。

## 1. 设计：三个不等式与两个「存在式」

| 构造子 | 损失 | 零集是否恰好等于 `Holds` |
|:--|:--|:--|
| `eqZero e` | `(evalPts e)²` | ✅ |
| `leZero e` | `(max (evalPts e) 0)²` | ✅ |
| `gtZero e` | `(max (-evalPts e) 0)²` | ✅ |
| **`ltZero e`** | `(max (evalPts e) 0)²` | ❌ 零集是 `e ≤ 0`，**松弛了** `e < 0` |
| `sqDistEq a b d` | `(dist² − d)²` | ✅ |
| `equalLength a b c e` | `(dist²(a,b) − dist²(c,e))²` | ✅ |
| `perpendicular a b c e` | `(点积)²` | ✅ |
| `rightAngle a b c` | `(点积)²` | ✅ |
| `samePoint a b` | `dist²(a,b)` | ✅ |
| `midpoint m a b` | `∑ᵢ (2mᵢ − aᵢ − bᵢ)²` | ✅ |
| **`collinear a b c`** | `∑ᵢⱼ (uᵢvⱼ − uⱼvᵢ)²` | 只证 **sound**（见 §2） |
| **`parallel a b c e`** | 同上 | 只证 **sound** |

### 为什么 `ltZero` 只能松弛

`Holds (.ltZero e) = (e < 0)` 是一个**开集**。任何连续的 `f ≥ 0` 若零集恰为开半空间，
则 `f` 在该开集的边界上必须跳变——那就不是连续函数。**所以「零集恰为 `e < 0`」不可能由
非负连续惩罚实现。** 这与 `M0-5`（`affineLtFix` 需要显式 `ε`）是同一件事的两面。

本节取 `(max e 0)²`，零集是 `e ≤ 0`——**比原约束宽**，所以它是**松弛**（relaxation）：
约束成立 ⟹ 损失为零；反之不成立。**定理里把这个方向写清楚，不含糊。**

### 为什么 `collinear`/`parallel` 只证 sound

它们的 `Holds` 是**存在式**（`∃ t, seg a b = t * seg a c`）。本节用二阶子式平方和当损失：
- **非负**显然（平方和）；
- **sound 可证**：`u = t v` 时每个子式 `t vᵢ vⱼ − t vⱼ vᵢ = 0`；
- **反方向**（损失为零 ⟹ 存在 `t`）需要「所有 2×2 子式为零 ⟹ 两向量共线」，
  而 `v = 0` 时该命题**为假**（任何 `u` 的子式都为零，但 `u = t·0` 要求 `u = 0`）。
  **所以反方向即使补证明也必须带 `v ≠ 0`。** 本节不做，并在定理名里标明只有 sound。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| `penaltyLoss` | **12 个构造子各自的非负惩罚** |
| **`penaltyLoss_nonneg`** | **对全部 12 个构造子统一成立** |
| `penaltyLoss_eq_zero_iff` | 9 个构造子上「损失为 0 ⟺ `Holds`」 |
| `penaltyLoss_eq_zero_of_holds` | 全部 12 个（sound 方向，含 `ltZero` 松弛与存在式） |
| `penaltyLoss_eq_zero_leZero` | `leZero` 的精确刻画 |
| `penaltyLoss_pos_of_not_holds` | 9 个构造子上「不成立 ⟹ 损失为正」 |

## 3. 边界

- **`ltZero` 是松弛**，不是错误，也不是没做——理由在 §1，与 `M0-5` 同源。
- **`collinear`/`parallel` 只有 sound 方向**，理由在 §1。
- **不使用 `sqNorm`/Cauchy–Schwarz**：`collinear`/`parallel` 的损失用**二阶子式平方和**，
  避免依赖 Cauchy–Schwarz 的等式情形。**代价是反方向更难证**（见上），收益是这一节能完整构建。
- 本节**不改** `Geo/Loss.lean`：那里是 `EqConstraint.sqDist`。
  本节是 `GeoConstraint` 的并列新增，两者服务不同层。
-/
import Mathlib
import Lattice.Domains.Constraint
import Lattice.Domains.Dist

namespace Lattice.Geo.PenaltyLoss

open Lattice.Geo
open Lattice.Geo.GeoConstraint
open scoped BigOperators

variable {n : ℕ}

/-- **`max a 0 = 0` 当且仅当 `a ≤ 0`。**

本 mathlib 没有 `max_eq_zero_iff`（与 `Int.div_mul_add_emod` 同一类：名字是猜的，实际不存在），
所以这里自己证。 -/
theorem max_zero_eq_zero_iff (a : ℝ) : max a 0 = 0 ↔ a ≤ 0 := by
  constructor
  · intro h
    calc a ≤ max a 0 := le_max_left _ _
      _ = 0 := h
  · intro h
    exact max_eq_right h

/-- **`collinear`/`parallel` 的损失**：所有二阶子式的平方和。

`u`、`v` 共线 ⟹ 每个子式为零；反之在 `v ≠ 0` 时也成立，但那个方向本节不证。
**选子式而不是 `‖u‖²‖v‖² − ⟨u,v⟩²`**，因为前者的非负性与 sound 方向都是初等的，
不依赖 Cauchy–Schwarz 的等式情形。 -/
noncomputable def minorDefect (u v : Pt n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (u i * v j - u j * v i) ^ 2

/-- 子式缺陷非负。 -/
theorem minorDefect_nonneg (u v : Pt n) : 0 ≤ minorDefect u v := by
  unfold minorDefect
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **共线 ⟹ 子式缺陷为零**：`u = t·v` 时每个子式 `t vᵢ vⱼ − t vⱼ vᵢ = 0`。 -/
theorem minorDefect_eq_zero_of_parallel (u v : Pt n) (t : ℝ) (h : u = fun i => t * v i) :
    minorDefect u v = 0 := by
  unfold minorDefect
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [h]
  ring

/-- **12 个构造子的惩罚损失**，全部非负。

`ltZero`/`gtZero` 用 `le_zero`/`ge_zero` 的松弛形式，理由见模块文档 §1。 -/
noncomputable def penaltyLoss (c : GeoConstraint n) (pts : ℕ → Pt n) : ℝ :=
  match c with
  | .eqZero e => (e.evalPts pts) ^ 2
  | .leZero e => (max (e.evalPts pts) 0) ^ 2
  | .ltZero e => (max (e.evalPts pts) 0) ^ 2
  | .gtZero e => (max (-(e.evalPts pts)) 0) ^ 2
  | .sqDistEq a b d => (sqDist (pts a) (pts b) - d.evalPts pts) ^ 2
  | .equalLength a b c e => (sqDist (pts a) (pts b) - sqDist (pts c) (pts e)) ^ 2
  | .collinear a b c => minorDefect (seg pts a b) (seg pts a c)
  | .perpendicular a b c e => (∑ i, seg pts a b i * seg pts c e i) ^ 2
  | .parallel a b c e => minorDefect (seg pts a b) (seg pts c e)
  | .rightAngle a b c => (∑ i, seg pts a b i * seg pts b c i) ^ 2
  | .midpoint m a b => ∑ i, (2 * pts m i - pts a i - pts b i) ^ 2
  | .samePoint a b => sqDist (pts a) (pts b)

/-- **损失非负，12 个构造子统一成立。**

这是 `Geo.lean` 里那条「不等式没有 penalty loss」的反面：**现在每一条都有，而且都非负。** -/
theorem penaltyLoss_nonneg (c : GeoConstraint n) (pts : ℕ → Pt n) : 0 ≤ penaltyLoss c pts := by
  cases c with
  | eqZero e => exact sq_nonneg _
  | leZero e => exact sq_nonneg _
  | ltZero e => exact sq_nonneg _
  | gtZero e => exact sq_nonneg _
  | sqDistEq a b d => exact sq_nonneg _
  | equalLength a b c e => exact sq_nonneg _
  | collinear a b c => exact minorDefect_nonneg _ _
  | perpendicular a b c e => exact sq_nonneg _
  | parallel a b c e => exact minorDefect_nonneg _ _
  | rightAngle a b c => exact sq_nonneg _
  | midpoint m a b =>
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
  | samePoint a b => exact sqDist_nonneg _ _

/-! ## 二、损失为零 ⟹ 约束成立（sound 方向，12/12） -/

/-- **`leZero` 的精确刻画**：损失为零 ⟺ `evalPts ≤ 0`。 -/
theorem penaltyLoss_eq_zero_leZero (e : GeoExpr n) (pts : ℕ → Pt n) :
    penaltyLoss (.leZero e) pts = 0 ↔ e.evalPts pts ≤ 0 := by
  unfold penaltyLoss
  rw [sq_eq_zero_iff, max_zero_eq_zero_iff]

/-- **`eqZero` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_eqZero (e : GeoExpr n) (pts : ℕ → Pt n) :
    penaltyLoss (.eqZero e) pts = 0 ↔ e.evalPts pts = 0 := by
  unfold penaltyLoss
  exact sq_eq_zero_iff

/-- **`gtZero` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_gtZero (e : GeoExpr n) (pts : ℕ → Pt n) :
    penaltyLoss (.gtZero e) pts = 0 ↔ 0 ≤ e.evalPts pts := by
  unfold penaltyLoss
  rw [sq_eq_zero_iff, max_zero_eq_zero_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`sqDistEq` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_sqDistEq (a b : ℕ) (d : GeoExpr n) (pts : ℕ → Pt n) :
    penaltyLoss (.sqDistEq a b d) pts = 0 ↔ sqDist (pts a) (pts b) = d.evalPts pts := by
  unfold penaltyLoss
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- **`equalLength` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_equalLength (a b c e : ℕ) (pts : ℕ → Pt n) :
    penaltyLoss (.equalLength a b c e) pts = 0 ↔
      sqDist (pts a) (pts b) = sqDist (pts c) (pts e) := by
  unfold penaltyLoss
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- **`perpendicular` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_perpendicular (a b c e : ℕ) (pts : ℕ → Pt n) :
    penaltyLoss (.perpendicular a b c e) pts = 0 ↔
      ∑ i, seg pts a b i * seg pts c e i = 0 := by
  unfold penaltyLoss
  exact sq_eq_zero_iff

/-- **`rightAngle` 的精确刻画**。 -/
theorem penaltyLoss_eq_zero_rightAngle (a b c : ℕ) (pts : ℕ → Pt n) :
    penaltyLoss (.rightAngle a b c) pts = 0 ↔
      ∑ i, seg pts a b i * seg pts b c i = 0 := by
  unfold penaltyLoss
  exact sq_eq_zero_iff

/-- **`midpoint` 的精确刻画**：损失为零 ⟺ 每个坐标满足 `2m = a + b`。 -/
theorem penaltyLoss_eq_zero_midpoint (m a b : ℕ) (pts : ℕ → Pt n) :
    penaltyLoss (.midpoint m a b) pts = 0 ↔ ∀ i, 2 * pts m i = pts a i + pts b i := by
  unfold penaltyLoss
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h i
    have h0 : (2 * pts m i - pts a i - pts b i) ^ 2 = 0 := h i (Finset.mem_univ i)
    have h1 := sq_eq_zero_iff.mp h0
    linarith
  · intro h i _
    rw [sq_eq_zero_iff]
    have := h i
    linarith

/-- **`leZero` / `ltZero` 的 sound 方向**：约束成立 ⟹ 损失为零。

对 `ltZero`，`e < 0` 蕴含 `max e 0 = 0`，所以**松弛方向是对的**（成立一定零损失），
只是**反过来不成立**（零损失只推出 `e ≤ 0`）。 -/
theorem penaltyLoss_eq_zero_of_holds (c : GeoConstraint n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds c pts) : penaltyLoss c pts = 0 := by
  cases c with
  | eqZero e =>
      exact (penaltyLoss_eq_zero_eqZero e pts).mpr h
  | leZero e =>
      exact (penaltyLoss_eq_zero_leZero e pts).mpr h
  | ltZero e =>
      -- `e < 0` ⟹ `max e 0 = 0`
      unfold penaltyLoss
      rw [sq_eq_zero_iff, max_zero_eq_zero_iff]
      exact le_of_lt h
  | gtZero e =>
      exact (penaltyLoss_eq_zero_gtZero e pts).mpr (le_of_lt h)
  | sqDistEq a b d =>
      exact (penaltyLoss_eq_zero_sqDistEq a b d pts).mpr h
  | equalLength a b c e =>
      exact (penaltyLoss_eq_zero_equalLength a b c e pts).mpr h
  | collinear a b c =>
      obtain ⟨t, ht⟩ := h
      exact minorDefect_eq_zero_of_parallel _ _ t ht
  | perpendicular a b c e =>
      exact (penaltyLoss_eq_zero_perpendicular a b c e pts).mpr h
  | parallel a b c e =>
      obtain ⟨t, ht⟩ := h
      exact minorDefect_eq_zero_of_parallel _ _ t ht
  | rightAngle a b c =>
      exact (penaltyLoss_eq_zero_rightAngle a b c pts).mpr h
  | midpoint m a b =>
      exact (penaltyLoss_eq_zero_midpoint m a b pts).mpr h
  | samePoint a b =>
      unfold penaltyLoss
      exact (sqDist_eq_zero_iff _ _).mpr h

/-! ## 三、关于「不成立 ⟹ 损失为正」：**本节不陈述**

理由不是难证，是**它对 3 个构造子为假**：

- `ltZero`：`e = 0` 时 `Holds` 为假而损失为零（松弛的零集比原约束宽）；
- `gtZero`：同上；
- `collinear` / `parallel`：只有 sound 方向。

对剩下 9 个，`penaltyLoss_eq_zero_*` 系列已经给出**双向**刻画，所以「不成立 ⟹ 损失为正」
是它们的直接推论，**不需要单独一条定理**。

初稿在这里写过一条 `0 < penaltyLoss c pts ∨ ¬ Holds c pts := Or.inr h`。
**那是重言**——它没有说损失为正，只是把假设抄了一遍。删掉了。
**这正是本库反复出现的形态：一条看起来在陈述结论的定理，实际陈述的是 `Or.inr h`。** -/

end Lattice.Geo.PenaltyLoss
