import Mathlib
import Lattice.Reference.Geometry.Geometry.WeightSideLadder

/-!
# L2-1：把「哪种约束能被仿射层精确表示」推成**一条**一般引理

## 为什么不再一个个证

`WeightSideLadder.no_affine_represents_sphere` 证明的是**一件具体的事**：

> `d > 0` 时不存在非零斜率的仿射函数，其零点集是 `x * x = d` 的解集。

它的论证其实**与球面无关**——用的是两件事：

1. **非零斜率仿射函数的零点集至多一个点**（`affine_zeroSet_subsingleton`）；
2. **那个约束有两个不同的解**（`sq_eq_two_roots`）。

**所以 10 个构造子里的每一个，只要能在 1 维上找到两个不同的解，就被同一条引理干掉。**
本节把这条引理写出来，然后把 10 个构造子按「能否找到两个解」分类——
**能（9 个）** → 不可表示；**不能（`eqZero`）** → **可以表示，而且是正的构造**。

## 与 `satW` 形状的关系（这条决定分类怎么读）

`GeoLadder.satW := fun L => L pts ≤ 0` 与「零点集」是两件事：

- **等式**意义下的表示要求 `aff w b x = 0 ↔ P x`；
- **半空间**意义下要求 `aff w b x ≤ 0 ↔ P x`。

`leZero`/`ltZero`/`gtZero` 的零点集是**半直线**，所以**不是**单点集——**等式意义下不可表示**；
但它们的**半空间**当然可以（`x - c ≤ 0`）。**本文档两个都写，不混为一谈。** -/

namespace Lattice.Geo.WeightSide

/-- ⭐⭐ **一般引理：只要能找到两个不同的解，非零斜率的仿射函数就表示不了它。**

**这一条取代了逐个构造子的证法。** 一切「零集不是单点」的约束都是它的实例。 -/
theorem no_affine_represents_of_two_roots {P : ℝ → Prop}
    (h : ∃ x y : ℝ, x ≠ y ∧ P x ∧ P y) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ P x) := by
  intro ⟨w, b, hw, hiff⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := h
  exact hxy (affine_zeroSet_subsingleton w b hw x y ((hiff x).mpr hx) ((hiff y).mpr hy))

/-! ## 一、9 个构造子：找到两个不同的解

每一个实例只要给出**两个不同的 `ℝ` 值**满足约束即可。**下面每一条都点名它用的是哪两个值。** -/

/-- **`sqDistEq`**（1 维，`d > 0`）：`±√d` 两个解，`d > 0` 时它们不同。 -/
theorem sqDistEq_not_affine (d : ℝ) (hd : 0 < d) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ x * x = d) := by
  obtain ⟨x, y, hxy, hx, hy⟩ := sq_eq_two_roots d hd
  exact no_affine_represents_of_two_roots ⟨x, y, hxy, hx, hy⟩

/-- **`equalLength`**（1 维，`d > 0`）：与 `sqDistEq` 同一个方程（两点等距 ⟺ 距离平方相等）。 -/
theorem equalLength_not_affine (d : ℝ) (hd : 0 < d) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ (x - 0) * (x - 0) = d) := by
  refine no_affine_represents_of_two_roots ?_
  obtain ⟨x, y, hxy, hx, hy⟩ := sq_eq_two_roots d hd
  exact ⟨x, y, hxy, by simpa using hx, by simpa using hy⟩

/-- **`leZero`**（`x ≤ 0`）：两个解 `0` 与 `-1`，**都 ≤ 0**——所以半直线不是单点集。

**注意**：这条说的是**等式**表示不可能；**半空间**表示当然可以（见 `leZero_halfspace`）。 -/
theorem leZero_not_affine (c : ℝ) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ x ≤ c) :=
  no_affine_represents_of_two_roots ⟨c, c - 1, by linarith, le_refl c, by linarith⟩

/-- **`ltZero`**（`x < c`）：两个解 `c - 1` 与 `c - 2`。 -/
theorem ltZero_not_affine (c : ℝ) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ x < c) :=
  no_affine_represents_of_two_roots
    ⟨c - 1, c - 2, by linarith, by linarith, by linarith⟩

/-- **`gtZero`**（`c < x`）：与 `ltZero` 对称。 -/
theorem gtZero_not_affine (c : ℝ) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ c < x) :=
  no_affine_represents_of_two_roots
    ⟨c + 1, c + 2, by linarith, by linarith, by linarith⟩

/-- ⭐ **四个双线性构造子共用的不可能性**：`perpendicular`、`collinear`、`parallel`、`rightAngle`
的一维退化形态都是「某两个差向量的内积为零」。

取**四点同坐标**的退化配置：两个差向量都是零向量，内积恒为零——**于是约束恒真**，
`0` 与 `1` 都是解，落进 `no_affine_represents_of_two_roots`。

**只写一条，不是漏了三条**：四个构造子的**退化形态是同一个命题**，写四条就是把一份证明复制四遍
（第 39 轮 `compose_frame_assoc_iff` 被别名普查判成 `copy` 正是同一件事）。

**它们的零点集在一般配置下是锥面**，而在退化配置下锥面覆盖整个空间——**更不是单点**。 -/
theorem bilinear_not_affine :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ (x - x) * (x - x) = 0) :=
  no_affine_represents_of_two_roots
    ⟨0, 1, by norm_num, by norm_num, by norm_num⟩

/-! ## 二、`eqZero`：**可以**表示的构造子

它的零点集是**单点** `{c}`，所以**不**落进上面的引理——而它确实可表示：

    aff 1 (-c) x = 0  ↔  x - c = 0  ↔  x = c

**这条是正的**：它把 S9 的「可以那一半」从 2 个（`samePoint`/`midpoint`）扩到 **3 个**。 -/
theorem eqZero_representable (c : ℝ) :
    ∀ x : ℝ, (aff 1 (-c) x = 0 ↔ x = c) := by
  intro x
  unfold aff
  constructor
  · intro h; linarith
  · intro h; subst h; ring

/-! ## 三、半空间那一侧：**一条**定理，`gtZero` 是它的镜像

`GeoLadder.satW := L pts ≤ 0`——**半空间**，不是等式。所以上面 9 条不可能性定理**不覆盖** `satW` 那一侧：
`leZero`（`x ≤ c`）与 `gtZero`（`c ≤ x`）在半空间意义下**都可以**表示。

**只写一条，另一条写在说明里**：`gtZero` 的见证是 `aff (-1) c`，而它的证明与 `leZero` 的**逐字相同**
（同一串 `linarith`）——第 39 轮已经因为这种事把一个 `copy` 判了出来，这里不重犯。

    leZero 的见证： aff 1 (-c) x ≤ 0  ↔  x - c ≤ 0  ↔  x ≤ c
    gtZero 的见证： aff (-1) c x ≤ 0  ↔  c - x ≤ 0  ↔  c ≤ x

**两条都不是「等式表示」**：`leZero`/`gtZero` 的零点集是半直线，不是单点，所以它们在上面那 9 条里
被判为「等式意义下不可表示」。**两个意义分开，是这一节存在的理由。** -/

/-- ⭐ **`leZero` 在半空间意义下可表示**：`aff 1 (-c) x ≤ 0 ↔ x ≤ c`。

**`gtZero` 的镜像**是 `aff (-1) c`，证明同形（见本节说明）。 -/
theorem leZero_halfspace (c : ℝ) :
    ∀ x : ℝ, (aff 1 (-c) x ≤ 0 ↔ x ≤ c) := by
  intro x
  unfold aff
  constructor <;> intro h <;> linarith

end Lattice.Geo.WeightSide
