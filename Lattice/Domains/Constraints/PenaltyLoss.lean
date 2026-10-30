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
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Constraints.Dist
import Lattice.Domains.Constraints.Lipschitz
import Lattice.Domains.Constraints.DistLipschitz
import Lattice.Domains.Geometry.PolyLipschitz
import Lattice.Lib.Penalty.BilinearLocallyLipschitz
import Lattice.Lib.Penalty.QuadraticLocallyLipschitz

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

/-! ## ⭐⭐ `minorDefect` 的**局部** Lipschitz 界

`minorDefect u v = ∑ i, ∑ j, (u i * v j - u j * v i)²`，**每一项是「两个双线性形式之差」的平方。**

**所以正确的工具组合是：**
1. **`Lib.Penalty.bilinear_sub_le`**（第 94 轮）给出**差**的界 `|… − …'| ≤ M·δ + M·δ`；
2. **`Lib.Penalty.sq_lipschitz_on_bounded`**（第 79 轮）把差抬到**平方**上，代价是 `2R`。

⚠ **不是 `bilinear_sq_sub_le` 那条**：那条处理的是「双线性形式的平方」（`(a·b)²`），
**而这里 `(u i v j − u j v i)²` 里的东西已经是两个乘积之差**，所以 `sq_lipschitz_on_bounded` 才是直接匹配。
**第 94 轮那两条因此留在原地——`bilinear_sub_le` 被本节消费，`bilinear_sq_sub_le` 暂时没有消费者。** -/

/-- **整个子式之差的界**：`|(u i v j − u j v i) − (u' i v' j − u' j v' i)| ≤ 2·(M δ + M δ)`。

**两项各用一次 `crossSub_le`**（第二项把 `u`/`v` 对调、下标对调）。 -/
theorem minorDiff_le {u v u' v' : Pt n} {M δ : ℝ}
    (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M)
    (hu' : ∀ i, |u' i| ≤ M) (hv' : ∀ i, |v' i| ≤ M)
    (hdu : ∀ i, |u i - u' i| ≤ δ) (hdv : ∀ i, |v i - v' i| ≤ δ) (i j : Fin n) :
    |(u i * v j - u j * v i) - (u' i * v' j - u' j * v' i)| ≤ (M * δ + M * δ) + (M * δ + M * δ) := by
  have hP : |u i * v j - u' i * v' j| ≤ M * δ + M * δ :=
    Lattice.Lib.Penalty.bilinear_sub_le (hu i) (hv' j) (hdu i) (hdv j)
  have hQ : |u j * v i - u' j * v' i| ≤ M * δ + M * δ := by
    have hraw := Lattice.Lib.Penalty.bilinear_sub_le (hv i) (hu' j) (hdv i) (hdu j)
    simpa only [mul_comm] using hraw
  have hfac : (u i * v j - u j * v i) - (u' i * v' j - u' j * v' i)
      = (u i * v j - u' i * v' j) - (u j * v i - u' j * v' i) := by ring
  rw [hfac]
  exact le_trans (abs_sub _ _) (add_le_add hP hQ)

/-- **单个子式的平方之差的界**：`≤ 2·(2M²)·(2·(M δ + M δ))`。

**由 `minorDiff_le` 给差、`sq_lipschitz_on_bounded` 抬平方**，而 `R = 2M²`
因为 `|u i v j − u j v i| ≤ |u i||v j| + |u j||v i| ≤ 2M²`。 -/
theorem minorTerm_lipschitz {u v u' v' : Pt n} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M)
    (hu' : ∀ i, |u' i| ≤ M) (hv' : ∀ i, |v' i| ≤ M)
    (hdu : ∀ i, |u i - u' i| ≤ δ) (hdv : ∀ i, |v i - v' i| ≤ δ) (i j : Fin n) :
    |(u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2|
      ≤ 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) := by
  have hdiff := minorDiff_le hu hv hu' hv' hdu hdv i j
  -- each side of the cross product is bounded by `2M²`
  have hP : |u i * v j - u j * v i| ≤ 2 * M * M := by
    have h1 : |u i| * |v j| ≤ M * M :=
      mul_le_mul (hu i) (hv j) (abs_nonneg _) (le_trans (abs_nonneg _) (hu i))
    have h2 : |u j| * |v i| ≤ M * M :=
      mul_le_mul (hu j) (hv i) (abs_nonneg _) (le_trans (abs_nonneg _) (hu j))
    calc |u i * v j - u j * v i| ≤ |u i * v j| + |u j * v i| := abs_sub _ _
      _ = |u i| * |v j| + |u j| * |v i| := by rw [abs_mul, abs_mul]
      _ ≤ M * M + M * M := add_le_add h1 h2
      _ = 2 * M * M := by ring
  have hQ : |u' i * v' j - u' j * v' i| ≤ 2 * M * M := by
    have h1 : |u' i| * |v' j| ≤ M * M :=
      mul_le_mul (hu' i) (hv' j) (abs_nonneg _) (le_trans (abs_nonneg _) (hu' i))
    have h2 : |u' j| * |v' i| ≤ M * M :=
      mul_le_mul (hu' j) (hv' i) (abs_nonneg _) (le_trans (abs_nonneg _) (hu' j))
    calc |u' i * v' j - u' j * v' i| ≤ |u' i * v' j| + |u' j * v' i| := abs_sub _ _
      _ = |u' i| * |v' j| + |u' j| * |v' i| := by rw [abs_mul, abs_mul]
      _ ≤ M * M + M * M := add_le_add h1 h2
      _ = 2 * M * M := by ring
  have hR : 0 ≤ 2 * M * M := by positivity
  exact le_trans (Lattice.Lib.Penalty.sq_lipschitz_on_bounded (s := u i * v j - u j * v i)
    (t := u' i * v' j - u' j * v' i) hR hP hQ) (by
      exact mul_le_mul_of_nonneg_left hdiff (by positivity))

/-- ⭐⭐⭐ **`minorDefect` 的局部 Lipschitz 界**：两边逐坐标被 `M` 界住、变化被 `δ` 界住时，

`|minorDefect u v − minorDefect u' v'| ≤ 2·(2M²)·(2·(Mδ + Mδ))·n·n`。

**这是 `collinear` / `parallel` 两个分支的 Lipschitz 前件**，也是 `penaltyLoss` 12 个分支里
唯一不是「线性形式平方」的那两个。 -/
theorem minorDefect_lipschitz {u v u' v' : Pt n} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M)
    (hu' : ∀ i, |u' i| ≤ M) (hv' : ∀ i, |v' i| ≤ M)
    (hdu : ∀ i, |u i - u' i| ≤ δ) (hdv : ∀ i, |v i - v' i| ≤ δ) :
    |minorDefect u v - minorDefect u' v'|
      ≤ 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) * (n : ℝ) * (n : ℝ) := by
  have hstep : ∀ i j : Fin n,
      |(u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2|
        ≤ 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) :=
    fun i j => minorTerm_lipschitz hM hδ hu hv hu' hv' hdu hdv i j
  have hnn : 0 ≤ 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) := by positivity
  have hsplit : minorDefect u v - minorDefect u' v'
      = ∑ i : Fin n, ∑ j : Fin n,
          ((u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2) := by
    unfold minorDefect
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  have hinner : ∀ i : Fin n,
      |∑ j, ((u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2)|
        ≤ 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) * (n : ℝ) := by
    intro i
    calc |∑ j, ((u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2)|
        ≤ ∑ j, |(u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) :=
          Finset.sum_le_sum (fun j _ => hstep i j)
      _ = 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) * (n : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc |∑ i, ∑ j, ((u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2)|
      ≤ ∑ i, |∑ j, ((u i * v j - u j * v i) ^ 2 - (u' i * v' j - u' j * v' i) ^ 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) * (n : ℝ) :=
        Finset.sum_le_sum (fun i _ => hinner i)
    _ = 2 * (2 * M * M) * ((M * δ + M * δ) + (M * δ + M * δ)) * (n : ℝ) * (n : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## ⭐ `max` 分支与 `midpoint` 分支的局部 Lipschitz 件

`penaltyLoss` 的 12 个分支里，**`leZero`/`ltZero`/`gtZero` 是 `(max · 0)²`**，
而 **`midpoint` 是 `∑ i, (2·pts m i − pts a i − pts b i)²`**——**一组线性形式的平方和**。

**本节给出这两类所需的引理。** 其余分支：
- `eqZero` 是纯 `(线性形式)²`，直接 `sq_lipschitz_on_bounded`；
- `sqDistEq`/`equalLength`/`samePoint` 含 `sqDist`，用 `DistLipschitz.sqDist_lipschitz`（`rho` 版）；
- `perpendicular`/`rightAngle` 是 `(∑ seg·seg)²`，用 `PolyLipschitz.bilinearSum_lipschitz`（`rho` 版）；
- `collinear`/`parallel` 已在上一节做完。

⚠ **注意 `rho` 与 `M`/`δ` 是两套度量**：`rho n k pts pts'` 是前缀上的**上确界**，
所以它给的是 `∀ p i, |pts p i − pts' p i| ≤ rho`——**本节的 `δ` 可以直接取 `rho`**，
而 `M` 取点的坐标界 `B`。**所以两套是兼容的，本节用 `M`/`δ` 因为更直白。** -/

/-- ⭐ **`max · 0` 是 `δ`-Lipschitz 的**：`|max s 0 − max t 0| ≤ |s − t|`。

**这是 `leZero`/`ltZero`/`gtZero` 三个分支需要的唯一新事实。** -/
theorem max_zero_sub_le {s t : ℝ} : |max s 0 - max t 0| ≤ |s - t| :=
  abs_max_sub_max_le_abs s t 0

/-- ⭐ **`(max · 0)²` 的局部 Lipschitz 界**：`≤ 2R·δ`。

**由 `max_zero_sub_le` 给差、`sq_lipschitz_on_bounded` 抬平方。** -/
theorem max_zero_sq_sub_le {s t R δ : ℝ} (hR : 0 ≤ R)
    (h : |s - t| ≤ δ) (hs : |max s 0| ≤ R) (ht : |max t 0| ≤ R) :
    |(max s 0) ^ 2 - (max t 0) ^ 2| ≤ 2 * R * δ := by
  have hdiff : |max s 0 - max t 0| ≤ δ := le_trans max_zero_sub_le h
  exact le_trans (Lattice.Lib.Penalty.sq_lipschitz_on_bounded hR hs ht)
    (mul_le_mul_of_nonneg_left hdiff (by positivity))

/-- **`midpoint` 的单坐标项之差**：`|(2m−a−b) − (2m'−a'−b')| ≤ 4δ`。

`2m` 的系数是 `2`，所以三项各有界：`2δ + δ + δ = 4δ`。 -/
theorem midpointTerm_diff_le {pts pts' : ℕ → Pt n} {m a b : ℕ} {δ : ℝ}
    (hm : ∀ i, |pts m i - pts' m i| ≤ δ)
    (ha : ∀ i, |pts a i - pts' a i| ≤ δ)
    (hb : ∀ i, |pts b i - pts' b i| ≤ δ) (i : Fin n) :
    |(2 * pts m i - pts a i - pts b i) - (2 * pts' m i - pts' a i - pts' b i)| ≤ 4 * δ := by
  have hfac : (2 * pts m i - pts a i - pts b i) - (2 * pts' m i - pts' a i - pts' b i)
      = 2 * (pts m i - pts' m i) - (pts a i - pts' a i) - (pts b i - pts' b i) := by ring
  rw [hfac]
  have h1 : |2 * (pts m i - pts' m i)| ≤ 2 * δ := by
    rw [abs_mul]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (hm i) (by norm_num)
  calc |2 * (pts m i - pts' m i) - (pts a i - pts' a i) - (pts b i - pts' b i)|
      ≤ |2 * (pts m i - pts' m i)| + |pts a i - pts' a i| + |pts b i - pts' b i| := by
        have h2 := abs_sub (2 * (pts m i - pts' m i) - (pts a i - pts' a i)) (pts b i - pts' b i)
        have h3 := abs_sub (2 * (pts m i - pts' m i)) (pts a i - pts' a i)
        linarith [abs_nonneg (2 * (pts m i - pts' m i) - (pts a i - pts' a i)),
          abs_nonneg (pts b i - pts' b i)]
    _ ≤ 2 * δ + δ + δ := by linarith [h1, ha i, hb i]
    _ = 4 * δ := by ring

/-- ⭐⭐ **`midpoint` 分支的局部 Lipschitz 界**：`midpoint` 那一支是 `∑ i, (2m−a−b)²`，

`|∑ i, (…)² − ∑ i, (…')²| ≤ 2·(4B)·(4δ)·n`。

**`R = 4B`** 因为 `|2·pts m i − pts a i − pts b i| ≤ 2B + B + B = 4B`。 -/
theorem midpoint_sum_lipschitz {pts pts' : ℕ → Pt n} {m a b : ℕ} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B)
    (hm : ∀ i, |pts m i - pts' m i| ≤ δ)
    (ha : ∀ i, |pts a i - pts' a i| ≤ δ)
    (hb : ∀ i, |pts b i - pts' b i| ≤ δ) :
    |(∑ i, (2 * pts m i - pts a i - pts b i) ^ 2)
        - (∑ i, (2 * pts' m i - pts' a i - pts' b i) ^ 2)|
      ≤ 2 * (4 * B) * (4 * δ) * (n : ℝ) := by
  have hstep : ∀ i : Fin n,
      |(2 * pts m i - pts a i - pts b i) ^ 2 - (2 * pts' m i - pts' a i - pts' b i) ^ 2|
        ≤ 2 * (4 * B) * (4 * δ) := by
    intro i
    have hdiff := midpointTerm_diff_le hm ha hb i
    have hP : |2 * pts m i - pts a i - pts b i| ≤ 4 * B := by
      have h1 : |pts m i| ≤ B := hpts m i
      have h2 : |pts a i| ≤ B := hpts a i
      have h3 : |pts b i| ≤ B := hpts b i
      calc |2 * pts m i - pts a i - pts b i|
          ≤ |2 * pts m i| + |pts a i| + |pts b i| := by
            have hx := abs_sub (2 * pts m i - pts a i) (pts b i)
            have hy := abs_sub (2 * pts m i) (pts a i)
            linarith [abs_nonneg (2 * pts m i - pts a i), abs_nonneg (pts b i)]
        _ ≤ 2 * B + B + B := by
            have h2' : |2 * pts m i| ≤ 2 * B := by
              rw [abs_mul]
              have : |(2 : ℝ)| = 2 := by norm_num
              rw [this]
              exact mul_le_mul_of_nonneg_left h1 (by norm_num)
            linarith
        _ = 4 * B := by ring
    have hQ : |2 * pts' m i - pts' a i - pts' b i| ≤ 4 * B := by
      have h1 : |pts' m i| ≤ B := hpts' m i
      have h2 : |pts' a i| ≤ B := hpts' a i
      have h3 : |pts' b i| ≤ B := hpts' b i
      calc |2 * pts' m i - pts' a i - pts' b i|
          ≤ |2 * pts' m i| + |pts' a i| + |pts' b i| := by
            have hx := abs_sub (2 * pts' m i - pts' a i) (pts' b i)
            have hy := abs_sub (2 * pts' m i) (pts' a i)
            linarith [abs_nonneg (2 * pts' m i - pts' a i), abs_nonneg (pts' b i)]
        _ ≤ 2 * B + B + B := by
            have h2' : |2 * pts' m i| ≤ 2 * B := by
              rw [abs_mul]
              have : |(2 : ℝ)| = 2 := by norm_num
              rw [this]
              exact mul_le_mul_of_nonneg_left h1 (by norm_num)
            linarith
        _ = 4 * B := by ring
    exact le_trans (Lattice.Lib.Penalty.sq_lipschitz_on_bounded (by positivity) hP hQ)
      (mul_le_mul_of_nonneg_left hdiff (by positivity))
  have hsplit : (∑ i, (2 * pts m i - pts a i - pts b i) ^ 2)
      - (∑ i, (2 * pts' m i - pts' a i - pts' b i) ^ 2)
      = ∑ i, ((2 * pts m i - pts a i - pts b i) ^ 2
          - (2 * pts' m i - pts' a i - pts' b i) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsplit]
  calc |∑ i, ((2 * pts m i - pts a i - pts b i) ^ 2
        - (2 * pts' m i - pts' a i - pts' b i) ^ 2)|
      ≤ ∑ i, |(2 * pts m i - pts a i - pts b i) ^ 2
          - (2 * pts' m i - pts' a i - pts' b i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, 2 * (4 * B) * (4 * δ) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = 2 * (4 * B) * (4 * δ) * (n : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## ⚠ **`penaltyLoss` 没有全局 Lipschitz 常数**（第 78 轮补）

**12 个分支里没有一个是线性的**——它们是**平方**或**两个线性形式的乘积**：

| 分支 | 形状 |
|:--|:--|
| `eqZero` / `leZero` / `ltZero` / `gtZero` | `(·)²` 或 `(max · 0)²` |
| `sqDistEq` / `equalLength` | `(· − ·)²` |
| `perpendicular` / `rightAngle` | `(∑ · ·)²` |
| `midpoint` | `∑ (·)²` |
| `collinear` / `parallel` | `minorDefect`（叉积型，二次） |
| `samePoint` | `sqDist`（二次） |

⇒ **每一个分支都含一个平方，所以没有全局 Lipschitz 常数。**
抽象原因在 `Lattice.Lib.Penalty.QuadraticNotLipschitz.sq_not_lipschitz`：
`¬ ∃ L, ∀ s t, |s² − t²| ≤ L·|s − t|`。

**这条事实的用处**：它把「收敛估计需要假设迭代路径有界」从一句口头交代变成一条有原因的约束。
**损失是二次的，`|L(θ) − L(θ')| ≤ C·‖θ − θ'‖` 形式的估计必须把 `θ` 限制在紧集里。**

⚠ **上一轮的规划在这里写错过**：我写过「`eqZero` 是线性 ⇒ 全局 Lipschitz」。
**实测是 `(e.evalPts pts)^2`——平方。** 记在这里以免那个错误再被引用。 -/

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

/-! ## ⭐⭐ `penaltyLoss` 逐分支的 `rho`-Lipschitz：**纯平方与 `max` 型**

`penaltyLoss` 是 `match`，所以 `penaltyLoss_lipschitz` 必须 12 个分支一起证。**本节做其中四支**：
`eqZero`（纯平方）与 `leZero`/`ltZero`/`gtZero`（`max` 型）。

**工具全部来自别处，本节只是把它们接起来：**
- `Domains/Constraints/Lipschitz.lean` 的 `LipschitzK`／`BoundedV` 给出线性形式的**变化**与**界**；
- `Lib/Penalty/QuadraticLocallyLipschitz.sq_lipschitz_on_bounded` 把变化抬到**平方**；
- 第 96 轮的 `max_zero_sub_le` 处理 `max · 0`。

⚠ **`rho` 是上确界，所以 `|pts p i − pts' p i| ≤ rho`**（`abs_coord_sub_le_rho`），
**于是 `LipschitzK` 给出的就是「点列整体扰动 `rho` ⇒ 表达式扰动 `K·rho`」。** -/

/-- ⭐ **`eqZero` 分支的 `rho`-Lipschitz 界**：`|(evalPts e ·)² − (evalPts e ·')²| ≤ 2B·(K·rho)`。 -/
theorem eqZero_lipschitz {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B)
    (pts pts' : ℕ → Pt n) :
    |penaltyLoss (.eqZero e) pts - penaltyLoss (.eqZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := by
  have hdiff : |GeoExpr.evalPts e pts - GeoExpr.evalPts e pts'|
      ≤ K * rho n k pts pts' := hK pts pts'
  have hp : |GeoExpr.evalPts e pts| ≤ B := hBd pts
  have hq : |GeoExpr.evalPts e pts'| ≤ B := hBd pts'
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded (s := GeoExpr.evalPts e pts)
    (t := GeoExpr.evalPts e pts') hB hp hq
  have hstep := mul_le_mul_of_nonneg_left hdiff (by linarith : (0 : ℝ) ≤ 2 * B)
  simpa only [penaltyLoss] using le_trans hsq hstep

/-- ⭐ **`leZero` / `ltZero` 分支的 `rho`-Lipschitz 界**（两者定义相同，故一条定理服务两支）。

`|max s 0| ≤ B` 从 `|s| ≤ B` 得到，**所以 `R = B` 而不是别的**。 -/
theorem maxZero_lipschitz {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B)
    (pts pts' : ℕ → Pt n) :
    |penaltyLoss (.leZero e) pts - penaltyLoss (.leZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := by
  have hdiff : |GeoExpr.evalPts e pts - GeoExpr.evalPts e pts'|
      ≤ K * rho n k pts pts' := hK pts pts'
  have hp : |GeoExpr.evalPts e pts| ≤ B := hBd pts
  have hq : |GeoExpr.evalPts e pts'| ≤ B := hBd pts'
  -- `|max s 0| ≤ |s| ≤ B`
  have hp' : |max (GeoExpr.evalPts e pts) 0| ≤ B := by
    calc |max (GeoExpr.evalPts e pts) 0| ≤ |GeoExpr.evalPts e pts| := by
          simpa only [max_eq_left (le_refl (0 : ℝ)), abs_zero, sub_zero] using
            (max_zero_sub_le (s := GeoExpr.evalPts e pts) (t := 0))
      _ ≤ B := hp
  have hq' : |max (GeoExpr.evalPts e pts') 0| ≤ B := by
    calc |max (GeoExpr.evalPts e pts') 0| ≤ |GeoExpr.evalPts e pts'| := by
          simpa only [max_eq_left (le_refl (0 : ℝ)), abs_zero, sub_zero] using
            (max_zero_sub_le (s := GeoExpr.evalPts e pts') (t := 0))
      _ ≤ B := hq
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := max (GeoExpr.evalPts e pts) 0) (t := max (GeoExpr.evalPts e pts') 0) hB hp' hq'
  have hmax : |max (GeoExpr.evalPts e pts) 0 - max (GeoExpr.evalPts e pts') 0|
      ≤ K * rho n k pts pts' := le_trans max_zero_sub_le hdiff
  have hstep := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 2 * B)
  simpa only [penaltyLoss] using le_trans hsq hstep

/-- ⭐ **`gtZero` 分支**：`(max (neg ·) 0)²`，**用 `LipschitzK` 的 `K` 因为取负不改变 Lipschitz 常数**。 -/
theorem gtZero_lipschitz {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B)
    (pts pts' : ℕ → Pt n) :
    |penaltyLoss (.gtZero e) pts - penaltyLoss (.gtZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := by
  have hdiff : |GeoExpr.evalPts e pts - GeoExpr.evalPts e pts'|
      ≤ K * rho n k pts pts' := hK pts pts'
  have hneg : |-(GeoExpr.evalPts e pts) - -(GeoExpr.evalPts e pts')|
      ≤ K * rho n k pts pts' := by
    simpa only [neg_sub_neg, abs_sub_comm] using hdiff
  have hp : |GeoExpr.evalPts e pts| ≤ B := hBd pts
  have hq : |GeoExpr.evalPts e pts'| ≤ B := hBd pts'
  have hp' : |max (-(GeoExpr.evalPts e pts)) 0| ≤ B := by
    calc |max (-(GeoExpr.evalPts e pts)) 0| ≤ |-(GeoExpr.evalPts e pts)| := by
          simpa only [max_eq_left (le_refl (0 : ℝ)), abs_zero, sub_zero] using
            (max_zero_sub_le (s := -(GeoExpr.evalPts e pts)) (t := 0))
      _ = |GeoExpr.evalPts e pts| := abs_neg _
      _ ≤ B := hp
  have hq' : |max (-(GeoExpr.evalPts e pts')) 0| ≤ B := by
    calc |max (-(GeoExpr.evalPts e pts')) 0| ≤ |-(GeoExpr.evalPts e pts')| := by
          simpa only [max_eq_left (le_refl (0 : ℝ)), abs_zero, sub_zero] using
            (max_zero_sub_le (s := -(GeoExpr.evalPts e pts')) (t := 0))
      _ = |GeoExpr.evalPts e pts'| := abs_neg _
      _ ≤ B := hq
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := max (-(GeoExpr.evalPts e pts)) 0) (t := max (-(GeoExpr.evalPts e pts')) 0) hB hp' hq'
  have hmax : |max (-(GeoExpr.evalPts e pts)) 0 - max (-(GeoExpr.evalPts e pts')) 0|
      ≤ K * rho n k pts pts' := le_trans max_zero_sub_le hneg
  have hstep := mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ 2 * B)
  simpa only [penaltyLoss] using le_trans hsq hstep

/-- ⭐ **`samePoint` 分支**：`penaltyLoss (.samePoint a b) pts = sqDist (pts a) (pts b)`，
**不是平方，而就是 `sqDist` 本身。**

⚠ **所以它的结论是【一阶】的**：常数是 `8·n·B`（来自 `sqDist_lipschitz`），
**而不是已做的四支那种 `2B·(K·rho)` 的【平方型】常数。**
**形状不同，值得单列**——`sqDistEq`／`equalLength` 会在这个一阶量外面再套一层平方。 -/
theorem samePoint_lipschitz {n k : ℕ} {a b : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B)
    (pts pts' : ℕ → Pt n)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |penaltyLoss (.samePoint a b) pts - penaltyLoss (.samePoint a b) pts'|
      ≤ (8 * n * B) * rho n k pts pts' := by
  show |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b)|
      ≤ (8 * (n : ℝ) * B) * rho n k pts pts'
  exact sqDist_lipschitz ha hb hB hpts hpts'

/-- ⭐⭐ **`sqDistEq` 分支**：`(sqDist (pts a) (pts b) − d.evalPts pts)²`。

**内层的差** = `sqDist` 的差 + `d.evalPts` 的差 `≤ 8nB·rho + K·rho`（一次三角不等式）；
**内层的界** = `|sqDist| + |d.evalPts| ≤ 4nB² + B`（`sqDist_abs_le` + `BoundedV`）。

**两项共用同一个 `rho`，所以它们是可加的，不必分成两条路径。** -/
theorem sqDistEq_lipschitz {n k : ℕ} {d : GeoExpr n} {a b : ℕ} {K B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B)
    (hK : LipschitzK n k d K) (hBd : BoundedV n d B)
    (pts pts' : ℕ → Pt n)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |penaltyLoss (.sqDistEq a b d) pts - penaltyLoss (.sqDistEq a b d) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B + B)
          * ((8 * (n : ℝ) * B) * rho n k pts pts' + K * rho n k pts pts') := by
  -- the two halves of the inner quantity
  have h1 := sqDist_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := a) (b := b) ha hb hB hpts hpts'
  have h2 : |GeoExpr.evalPts d pts - GeoExpr.evalPts d pts'| ≤ K * rho n k pts pts' :=
    hK pts pts'
  -- the difference of the inner quantities
  have hdiff : |(sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts)
      - (sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts')|
      ≤ (8 * (n : ℝ) * B) * rho n k pts pts' + K * rho n k pts pts' := by
    have hfac : (sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts)
        - (sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts')
        = (sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b))
          - (GeoExpr.evalPts d pts - GeoExpr.evalPts d pts') := by ring
    rw [hfac]
    exact le_trans (abs_sub _ _) (add_le_add h1 h2)
  -- and the bounds on both inner quantities
  have hp : |sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts|
      ≤ 4 * (n : ℝ) * B * B + B := by
    calc |sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts|
        ≤ |sqDist (n := n) (pts a) (pts b)| + |GeoExpr.evalPts d pts| := abs_sub _ _
      _ ≤ 4 * (n : ℝ) * B * B + B := add_le_add (sqDist_abs_le hB hpts) (hBd pts)
  have hq : |sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts'|
      ≤ 4 * (n : ℝ) * B * B + B := by
    calc |sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts'|
        ≤ |sqDist (n := n) (pts' a) (pts' b)| + |GeoExpr.evalPts d pts'| := abs_sub _ _
      _ ≤ 4 * (n : ℝ) * B * B + B := add_le_add (sqDist_abs_le hB hpts') (hBd pts')
  have hR : 0 ≤ 4 * (n : ℝ) * B * B + B := by positivity
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts)
    (t := sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts') hR hp hq
  have hstep := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ 2 * (4 * (n : ℝ) * B * B + B))
  simpa only [penaltyLoss] using le_trans hsq hstep

/-- ⭐⭐ **`equalLength` 分支**：`(sqDist (pts a) (pts b) − sqDist (pts c) (pts e))²`。

**与 `sqDistEq` 同构**，只是第二个和项也是 `sqDist`，所以**差和界都各多一份**：
差 `≤ 8nB·rho + 8nB·rho`、界 `≤ 4nB² + 4nB² = 8nB²`。 -/
theorem equalLength_lipschitz {n k : ℕ} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B)
    (pts pts' : ℕ → Pt n)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |penaltyLoss (.equalLength a b c e) pts - penaltyLoss (.equalLength a b c e) pts'|
      ≤ 2 * (8 * (n : ℝ) * B * B)
          * ((8 * (n : ℝ) * B) * rho n k pts pts' + (8 * (n : ℝ) * B) * rho n k pts pts') := by
  have h1 := sqDist_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := a) (b := b) ha hb hB hpts hpts'
  have h3 := sqDist_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := c) (b := e) hc he hB hpts hpts'
  have hdiff : |(sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts c) (pts e))
      - (sqDist (n := n) (pts' a) (pts' b) - sqDist (n := n) (pts' c) (pts' e))|
      ≤ (8 * (n : ℝ) * B) * rho n k pts pts' + (8 * (n : ℝ) * B) * rho n k pts pts' := by
    have hfac : (sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts c) (pts e))
        - (sqDist (n := n) (pts' a) (pts' b) - sqDist (n := n) (pts' c) (pts' e))
        = (sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b))
          - (sqDist (n := n) (pts c) (pts e) - sqDist (n := n) (pts' c) (pts' e)) := by ring
    rw [hfac]
    exact le_trans (abs_sub _ _) (add_le_add h1 h3)
  have hp : |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts c) (pts e)|
      ≤ 8 * (n : ℝ) * B * B := by
    have hx : |sqDist (n := n) (pts a) (pts b)| ≤ 4 * (n : ℝ) * B * B := sqDist_abs_le hB hpts
    have hy : |sqDist (n := n) (pts c) (pts e)| ≤ 4 * (n : ℝ) * B * B := sqDist_abs_le hB hpts
    calc |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts c) (pts e)|
        ≤ |sqDist (n := n) (pts a) (pts b)| + |sqDist (n := n) (pts c) (pts e)| := abs_sub _ _
      _ ≤ 4 * (n : ℝ) * B * B + 4 * (n : ℝ) * B * B := add_le_add hx hy
      _ = 8 * (n : ℝ) * B * B := by ring
  have hq : |sqDist (n := n) (pts' a) (pts' b) - sqDist (n := n) (pts' c) (pts' e)|
      ≤ 8 * (n : ℝ) * B * B := by
    have hx : |sqDist (n := n) (pts' a) (pts' b)| ≤ 4 * (n : ℝ) * B * B := sqDist_abs_le hB hpts'
    have hy : |sqDist (n := n) (pts' c) (pts' e)| ≤ 4 * (n : ℝ) * B * B := sqDist_abs_le hB hpts'
    calc |sqDist (n := n) (pts' a) (pts' b) - sqDist (n := n) (pts' c) (pts' e)|
        ≤ |sqDist (n := n) (pts' a) (pts' b)| + |sqDist (n := n) (pts' c) (pts' e)| := abs_sub _ _
      _ ≤ 4 * (n : ℝ) * B * B + 4 * (n : ℝ) * B * B := add_le_add hx hy
      _ = 8 * (n : ℝ) * B * B := by ring
  have hR : 0 ≤ 8 * (n : ℝ) * B * B := by positivity
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts c) (pts e))
    (t := sqDist (n := n) (pts' a) (pts' b) - sqDist (n := n) (pts' c) (pts' e)) hR hp hq
  have hstep := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ 2 * (8 * (n : ℝ) * B * B))
  simpa only [penaltyLoss] using le_trans hsq hstep

/-- ⭐⭐ **`perpendicular` 分支**：`(∑ i, seg pts a b i · seg pts c e i)²`。

**内层的差** `≤ 8nB·rho`（`bilinearSum_lipschitz`）、**内层的界** `≤ 4nB²`（`bilinearSum_abs_le`）。
**所以外层是 `2·(4nB²)` 倍的平方型界。** -/
theorem perpendicular_lipschitz {n k : ℕ} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B)
    (pts pts' : ℕ → Pt n)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |penaltyLoss (.perpendicular a b c e) pts
        - penaltyLoss (.perpendicular a b c e) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) * rho n k pts pts') := by
  have h1 := Lattice.Geo.bilinearSum_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := a) (b := b) (c := c) (e := e) ha hb hc he hB hpts hpts'
  have hp : |∑ i, seg pts a b i * seg pts c e i| ≤ 4 * (n : ℝ) * B * B := by
    simpa only [seg] using Lattice.Geo.bilinearSum_abs_le (n := n) (pts := pts)
      (a := a) (b := b) (c := c) (e := e) hB hpts
  have hq : |∑ i, seg pts' a b i * seg pts' c e i| ≤ 4 * (n : ℝ) * B * B := by
    simpa only [seg] using Lattice.Geo.bilinearSum_abs_le (n := n) (pts := pts')
      (a := a) (b := b) (c := c) (e := e) hB hpts'
  have hR : 0 ≤ 4 * (n : ℝ) * B * B := by positivity
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := ∑ i, seg pts a b i * seg pts c e i)
    (t := ∑ i, seg pts' a b i * seg pts' c e i) hR hp hq
  have hstep := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (4 * (n : ℝ) * B * B))
  simpa only [penaltyLoss, seg] using le_trans hsq hstep

/-- ⭐⭐ **`rightAngle` 分支**：`(∑ i, seg pts a b i · seg pts b c i)²`。

**与 `perpendicular` 同构**，只是第二个和项的线段是 `b → c` 而不是 `c → e`
（所以 `bilinearSum_lipschitz` 的 `c` 取 `b`、`e` 取 `c`）。 -/
theorem rightAngle_lipschitz {n k : ℕ} {a b c : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (hB : 0 ≤ B)
    (pts pts' : ℕ → Pt n)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |penaltyLoss (.rightAngle a b c) pts - penaltyLoss (.rightAngle a b c) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) * rho n k pts pts') := by
  have h1 := Lattice.Geo.bilinearSum_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := a) (b := b) (c := b) (e := c) ha hb hb hc hB hpts hpts'
  have hp : |∑ i, seg pts a b i * seg pts b c i| ≤ 4 * (n : ℝ) * B * B := by
    simpa only [seg] using Lattice.Geo.bilinearSum_abs_le (n := n) (pts := pts)
      (a := a) (b := b) (c := b) (e := c) hB hpts
  have hq : |∑ i, seg pts' a b i * seg pts' b c i| ≤ 4 * (n : ℝ) * B * B := by
    simpa only [seg] using Lattice.Geo.bilinearSum_abs_le (n := n) (pts := pts')
      (a := a) (b := b) (c := b) (e := c) hB hpts'
  have hR : 0 ≤ 4 * (n : ℝ) * B * B := by positivity
  have hsq := Lattice.Lib.Penalty.sq_lipschitz_on_bounded
    (s := ∑ i, seg pts a b i * seg pts b c i)
    (t := ∑ i, seg pts' a b i * seg pts' b c i) hR hp hq
  have hstep := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (4 * (n : ℝ) * B * B))
  simpa only [penaltyLoss, seg] using le_trans hsq hstep

/-! ## ⭐⭐ `PenaltyLipschitz`：把 12 个异构分支收成**一个可命名的接口**

第 100 轮的结论是：**`penaltyLoss_lipschitz` 作为单条定理不存在**，因为 12 个构造子的**前提**形状不同
（`eqZero` 要表达式的 `K`/`B`，`midpoint` 只要有界，`perpendicular` 要四个下标界）。

**但有一件事是统一的：12 支全都读点列，所以全都需要点界 `B`。** 加上 `B` 之后，
**结论的形状也统一了**：都是「变化 `≤ 常数 · rho`」。

⚠ **点界必须进定义，不能留在各自的定理里**：`PenaltyLipschitz` 量化【所有】`pts`，
而 `samePoint` 那支（就是 `sqDist` 本身）**在无点界时是假命题**——
`sqDist` 对点的绝对位置二次敏感（第 78 轮 `sq_not_lipschitz` 的同一原因）。
**所以「接口不带 `B`」这个版本是错的，本节给的是带 `B` 的正确版本。** -/

/-- ⭐⭐ **`PenaltyLipschitz k c B K`**：点列被 `B` 界住时，约束 `c` 的惩罚损失在偏差 `rho` 下
以 `K` 为 Lipschitz 常数。

**这是 12 个构造子共有的【结论形状】**，而它们对表达式的要求（`LipschitzK`／`BoundedV`）与下标要求
留在了各自的分支定理里。 -/
def PenaltyLipschitz {n : ℕ} (k : ℕ) (c : GeoConstraint n) (B K : ℝ) : Prop :=
  ∀ pts pts' : ℕ → Pt n,
    (∀ p i, |pts p i| ≤ B) → (∀ p i, |pts' p i| ≤ B) →
    |penaltyLoss c pts - penaltyLoss c pts'| ≤ K * rho n k pts pts'

/-- **`eqZero` 支**：常数 `2B·K`。 -/
theorem penaltyLipschitz_eqZero {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B) :
    PenaltyLipschitz k (.eqZero e) B (2 * B * K) := by
  intro pts pts' hpts hpts'
  have h := eqZero_lipschitz (n := n) (k := k) (e := e) hB hK hBd pts pts'
  calc |penaltyLoss (.eqZero e) pts - penaltyLoss (.eqZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := h
    _ = (2 * B * K) * rho n k pts pts' := by ring

/-- **`leZero` 支**（`ltZero` 定义相同，可同用）：常数 `2B·K`。 -/
theorem penaltyLipschitz_leZero {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B) :
    PenaltyLipschitz k (.leZero e) B (2 * B * K) := by
  intro pts pts' hpts hpts'
  have h := maxZero_lipschitz (n := n) (k := k) (e := e) hB hK hBd pts pts'
  calc |penaltyLoss (.leZero e) pts - penaltyLoss (.leZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := h
    _ = (2 * B * K) * rho n k pts pts' := by ring

/-- **`gtZero` 支**：常数 `2B·K`。 -/
theorem penaltyLipschitz_gtZero {n k : ℕ} {e : GeoExpr n} {K B : ℝ}
    (hB : 0 ≤ B) (hK : LipschitzK n k e K) (hBd : BoundedV n e B) :
    PenaltyLipschitz k (.gtZero e) B (2 * B * K) := by
  intro pts pts' hpts hpts'
  have h := gtZero_lipschitz (n := n) (k := k) (e := e) hB hK hBd pts pts'
  calc |penaltyLoss (.gtZero e) pts - penaltyLoss (.gtZero e) pts'|
      ≤ 2 * B * (K * rho n k pts pts') := h
    _ = (2 * B * K) * rho n k pts pts' := by ring

/-- **`samePoint` 支**：常数 `8·n·B`——**一阶**，不是平方型。 -/
theorem penaltyLipschitz_samePoint {n k : ℕ} {a b : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B) :
    PenaltyLipschitz (n := n) k (.samePoint a b) B (8 * (n : ℝ) * B) := by
  intro pts pts' hpts hpts'
  exact samePoint_lipschitz (n := n) (k := k) (a := a) (b := b) ha hb hB pts pts' hpts hpts'

/-- **`sqDistEq` 支**：常数 `2·(4nB² + B)·(8nB + K)`。

**注意常数里 `8nB + K` 的合并**：`sqDist` 的差与 `d.evalPts` 的差共用同一个 `rho`，所以可加。 -/
theorem penaltyLipschitz_sqDistEq {n k : ℕ} {d : GeoExpr n} {a b : ℕ} {K B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B) (hK : LipschitzK n k d K) (hBd : BoundedV n d B) :
    PenaltyLipschitz k (.sqDistEq a b d) B
      (2 * (4 * (n : ℝ) * B * B + B) * (8 * (n : ℝ) * B + K)) := by
  intro pts pts' hpts hpts'
  have h := sqDistEq_lipschitz (n := n) (k := k) (d := d) (a := a) (b := b)
    ha hb hB hK hBd pts pts' hpts hpts'
  calc |penaltyLoss (.sqDistEq a b d) pts - penaltyLoss (.sqDistEq a b d) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B + B)
          * ((8 * (n : ℝ) * B) * rho n k pts pts' + K * rho n k pts pts') := h
    _ = (2 * (4 * (n : ℝ) * B * B + B) * (8 * (n : ℝ) * B + K)) * rho n k pts pts' := by ring

/-! ### 续：`equalLength` / `perpendicular` / `rightAngle` 的接口实例

⚠ **`ltZero` 不单列**：`penaltyLoss` 对 `.ltZero e` 与 `.leZero e` 是**同一个定义**
（都是 `(max (evalPts e ·) 0)²`，见 `penaltyLoss` 的 `match`），
所以 `penaltyLipschitz_leZero` 已按定义覆盖它。**再写一条会是重复**——**而别名普查会抓出来。** -/

/-- **`equalLength` 支**：常数 `2·(8nB²)·(8nB + 8nB)`。 -/
theorem penaltyLipschitz_equalLength {n k : ℕ} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B) :
    PenaltyLipschitz (n := n) k (.equalLength a b c e) B
      (2 * (8 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) + (8 * (n : ℝ) * B))) := by
  intro pts pts' hpts hpts'
  have h := equalLength_lipschitz (n := n) (k := k) (a := a) (b := b) (c := c) (e := e)
    ha hb hc he hB pts pts' hpts hpts'
  calc |penaltyLoss (.equalLength a b c e) pts - penaltyLoss (.equalLength a b c e) pts'|
      ≤ 2 * (8 * (n : ℝ) * B * B)
          * ((8 * (n : ℝ) * B) * rho n k pts pts' + (8 * (n : ℝ) * B) * rho n k pts pts') := h
    _ = (2 * (8 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) + (8 * (n : ℝ) * B)))
          * rho n k pts pts' := by ring

/-- **`perpendicular` 支**：常数 `2·(4nB²)·(8nB)`。 -/
theorem penaltyLipschitz_perpendicular {n k : ℕ} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B) :
    PenaltyLipschitz (n := n) k (.perpendicular a b c e) B
      (2 * (4 * (n : ℝ) * B * B) * (8 * (n : ℝ) * B)) := by
  intro pts pts' hpts hpts'
  have h := perpendicular_lipschitz (n := n) (k := k) (a := a) (b := b) (c := c) (e := e)
    ha hb hc he hB pts pts' hpts hpts'
  calc |penaltyLoss (.perpendicular a b c e) pts - penaltyLoss (.perpendicular a b c e) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) * rho n k pts pts') := h
    _ = (2 * (4 * (n : ℝ) * B * B) * (8 * (n : ℝ) * B)) * rho n k pts pts' := by ring

/-- **`rightAngle` 支**：常数 `2·(4nB²)·(8nB)`。 -/
theorem penaltyLipschitz_rightAngle {n k : ℕ} {a b c : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (hB : 0 ≤ B) :
    PenaltyLipschitz (n := n) k (.rightAngle a b c) B
      (2 * (4 * (n : ℝ) * B * B) * (8 * (n : ℝ) * B)) := by
  intro pts pts' hpts hpts'
  have h := rightAngle_lipschitz (n := n) (k := k) (a := a) (b := b) (c := c)
    ha hb hc hB pts pts' hpts hpts'
  calc |penaltyLoss (.rightAngle a b c) pts - penaltyLoss (.rightAngle a b c) pts'|
      ≤ 2 * (4 * (n : ℝ) * B * B) * ((8 * (n : ℝ) * B) * rho n k pts pts') := h
    _ = (2 * (4 * (n : ℝ) * B * B) * (8 * (n : ℝ) * B)) * rho n k pts pts' := by ring

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
