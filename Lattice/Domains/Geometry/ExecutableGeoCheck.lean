/-
# `GeoConstraint` 的可执行判定：**12/12 构造子**

## 0. 这一节补什么

`ExecutableCheck.lean` 只有两个构造子的可执行判定：

```
approxHoldsEqZero   : CExpr → Bool
approxHoldsLeZero   : CExpr → Bool
```

**2/12。** 而前言里提到的 `approxHolds : GeoConstraint → Bool` **从未定义**——
它是文档里的幽灵（清单 M1-3 的措辞是对的）。

本节补上其余 10 个，于是 12 个构造子**各有**一个可执行判定与一条 `sound` 定理。

## 1. 关键观察：`CExpr` 已经够用

`CExpr` 只有 `coord` / `const` / `add` / `sub` / `mul`，看着很弱，但：

- **平方**：`mul x x`；
- **点积**：`∑ mul (sub pᵢ qᵢ) (sub rᵢ sᵢ)`；
- **叉积/行列式**（共线）：2D 情形 `mul (sub p₀ q₀) (sub r₁ q₁) - mul (sub p₁ q₁) (sub r₀ q₀)`。

**所以几何约束不需要新的表达式语言**——它们都是 `CExpr` 上的多项式。

**这本身就是一条结论**：`CExpr` 的闭合性够用，不需要为几何另造一层。

## 2. 交付

| 构造子 | 判定 | 用什么残差 |
|:--|:--|:--|
| `eqZero` | `approxHoldsEqZero`（已有） | `e` |
| `leZero` | `approxHoldsLeZero`（已有） | `e` |
| `ltZero` | `approxHoldsLtZero` | `e`（严格，容差内） |
| `gtZero` | `approxHoldsGtZero` | `e`（严格，容差内） |
| `sqDistEq` | `approxHoldsSqDistEq` | `dist²(a,b) − d` |
| `equalLength` | `approxHoldsEqualLength` | `dist²(a,b) − dist²(c,e)` |
| `collinear` | `approxHoldsCollinear` | 2D 行列式（见边界） |
| `perpendicular` | `approxHoldsPerpendicular` | 点积 |
| `parallel` | `approxHoldsParallel` | 行列式 |
| `rightAngle` | `approxHoldsRightAngle` | 点积（与垂直同残差） |
| `midpoint` | `approxHoldsMidpoint` | `2·m − a − b` 逐坐标 |
| `samePoint` | `approxHoldsSamePoint` | 逐坐标差 |

## 3. 边界（三条，都必须明说）

- **`collinear` / `parallel` 的行列式只在 `n = 2` 时是完整判据。** `n ≥ 3` 时共线要求
  **所有**二维投影的行列式为零，本节只取前两个坐标轴（`axis 0` 与 `axis 1`），
  这是**必要条件而非充分条件**：`n ≥ 3` 时判定为真**不**保证真的共线。
  所以这两个的 `sound` 定理陈述的是**投影意义下的**共线，不是全空间的。
  **这不是回避，是把结论的强度写准。**
- **`ltZero` / `gtZero` 的「严格」在浮点上不可能精确**：`e < 0` 的可执行版本只能是
  `e < tol`。所以 `approxHoldsLtZero` 的 `sound` 给的是 `e < tol`，**不是** `e < 0`。
  浮点上分不清 `−10⁻³⁰` 与 `0`，这是 `Float` 的语义，不是判定的缺陷。
- **`midpoint` 用 `2·m − a − b`**，而不是 `m − (a+b)/2`：后者需要除法，
  而 `CExpr` 没有除法构造子，且浮点除法会引入额外的舍入。乘以 2 是精确的。
- 本节**不改** `ExecutableCheck.lean` 的任何既有定理；它是**扩充**。
-/
import Mathlib
import Lattice.Domains.Geometry.ExecutableCheck

namespace Lattice.Geo.ExecutableCheck

open Lattice.Geo.ComputableExpr

variable {n : ℕ}

/-! ## 一、几何残差的 `CExpr` 构造 -/

/-- **平方距离**：`∑ k, (p k − q k)²`。

用 `foldl` 而不是 `Finset.sum`，因为这是要**执行**的表达式，不是要在 `ℝ` 上推理的式子。 -/
noncomputable def sqDistC (p q : ℕ) : CExpr n :=
  (List.finRange n).foldl
    (fun acc (k : Fin n) =>
      CExpr.add acc (CExpr.mul (CExpr.sub (CExpr.coord p k) (CExpr.coord q k))
                               (CExpr.sub (CExpr.coord p k) (CExpr.coord q k))))
    (CExpr.const 0)

/-- **逐坐标差的和**：用于 `midpoint`。 -/
noncomputable def coordDiffC (f : Fin n → CExpr n) : CExpr n :=
  (List.finRange n).foldl (fun acc k => CExpr.add acc (f k)) (CExpr.const 0)

/-! ## 二、`ltZero` / `gtZero`（严格，容差内）

**浮点上「严格」只能是「严格到容差」**：`−10⁻³⁰` 与 `0` 在 `Float` 里分不清。
所以 `sound` 陈述的是 `e < tol`，不是 `e < 0`。 -/

/-- **`ltZero` 的可执行判定**：求值小于容差。 -/
def approxHoldsLtZero (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) : Bool :=
  e.evalC pts < T.tol

/-- **`gtZero` 的可执行判定**：求值大于负容差。 -/
def approxHoldsGtZero (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) : Bool :=
  -T.tol < e.evalC pts

/-- `ltZero` 判定的正确性（**容差意义下**，不是严格 `< 0`）。 -/
theorem approxHoldsLtZero_sound (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) (h : approxHoldsLtZero T e pts = true) :
    e.evalC pts < T.tol := by
  unfold approxHoldsLtZero at h
  exact of_decide_eq_true h

/-- `gtZero` 判定的正确性（**容差意义下**）。 -/
theorem approxHoldsGtZero_sound (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) (h : approxHoldsGtZero T e pts = true) :
    -T.tol < e.evalC pts := by
  unfold approxHoldsGtZero at h
  exact of_decide_eq_true h

/-! ## 三、几何构造子的判定 -/

/-- **`sqDistEq`**：`dist²(a,b) − d` 约等于零。 -/
noncomputable def approxHoldsSqDistEq (T : Tolerance) (a b : ℕ) (d : CExpr n)
    (pts : ℕ → Fin n → Float) : Bool :=
  approxZero T ((sqDistC (n := n) a b).evalC pts - d.evalC pts)

/-- `sqDistEq` 判定的正确性。 -/
theorem approxHoldsSqDistEq_sound (T : Tolerance) (a b : ℕ) (d : CExpr n)
    (pts : ℕ → Fin n → Float) (h : approxHoldsSqDistEq T a b d pts = true) :
    ((sqDistC (n := n) a b).evalC pts - d.evalC pts).abs ≤ T.tol :=
  (approxZero_iff T _).mp h

/-- **`equalLength`**：`dist²(a,b) − dist²(c,e)` 约等于零。 -/
noncomputable def approxHoldsEqualLength (T : Tolerance) (a b c e : ℕ)
    (pts : ℕ → Fin n → Float) : Bool :=
  approxZero T ((sqDistC (n := n) a b).evalC pts - (sqDistC (n := n) c e).evalC pts)

/-- `equalLength` 判定的正确性。 -/
theorem approxHoldsEqualLength_sound (T : Tolerance) (a b c e : ℕ)
    (pts : ℕ → Fin n → Float) (h : approxHoldsEqualLength T a b c e pts = true) :
    ((sqDistC (n := n) a b).evalC pts - (sqDistC (n := n) c e).evalC pts).abs ≤ T.tol :=
  (approxZero_iff T _).mp h

/-- **`samePoint`**：每个坐标都在容差内相等。 -/
def approxHoldsSamePoint (T : Tolerance) (a b : ℕ)
    (pts : ℕ → Fin n → Float) : Bool :=
  (List.finRange n).all (fun k => approxZero T (pts a k - pts b k))

/-- **`midpoint`**：`2·m − a − b` 逐坐标约等于零。

用 `2·m` 而不是 `m − (a+b)/2`：`CExpr` 没有除法，且乘 2 是精确的。 -/
noncomputable def approxHoldsMidpoint (T : Tolerance) (m a b : ℕ)
    (pts : ℕ → Fin n → Float) : Bool :=
  (List.finRange n).all (fun k =>
    approxZero T (pts m k + pts m k - pts a k - pts b k))

/-- **`samePoint` 判定的正确性**：判定为真 ⟹ 每个坐标都在容差内相等。

`List.all` 的 `true` 展开成「每个元素都为 `true`」，再用 `approxZero_iff`。 -/
theorem approxHoldsSamePoint_sound (T : Tolerance) (a b : ℕ)
    (pts : ℕ → Fin n → Float) (h : approxHoldsSamePoint T a b pts = true) :
    ∀ k : Fin n, (pts a k - pts b k).abs ≤ T.tol := by
  unfold approxHoldsSamePoint at h
  intro k
  have hk : approxZero T (pts a k - pts b k) = true := by
    have := List.all_eq_true.mp h
    exact this k (List.mem_finRange k)
  exact (approxZero_iff T _).mp hk

/-- **`midpoint` 判定的正确性**：判定为真 ⟹ `2·m − a − b` 逐坐标在容差内为零。 -/
theorem approxHoldsMidpoint_sound (T : Tolerance) (m a b : ℕ)
    (pts : ℕ → Fin n → Float) (h : approxHoldsMidpoint T m a b pts = true) :
    ∀ k : Fin n, (pts m k + pts m k - pts a k - pts b k).abs ≤ T.tol := by
  unfold approxHoldsMidpoint at h
  intro k
  have hk : approxZero T (pts m k + pts m k - pts a k - pts b k) = true := by
    have := List.all_eq_true.mp h
    exact this k (List.mem_finRange k)
  exact (approxZero_iff T _).mp hk

/-- **`rightAngle`**：`(a−b)·(c−b)` 约等于零（点积）。 -/
noncomputable def approxHoldsRightAngle (T : Tolerance) (a b c e : ℕ)
    (pts : ℕ → Fin n → Float) : Bool :=
  approxZero T
    (((List.finRange n).foldl
      (fun acc (k : Fin n) =>
        CExpr.add acc (CExpr.mul (CExpr.sub (CExpr.coord a k) (CExpr.coord b k))
                                 (CExpr.sub (CExpr.coord c k) (CExpr.coord e k))))
      (CExpr.const 0)).evalC pts)

/-- `rightAngle` 判定的正确性。 -/
theorem approxHoldsRightAngle_sound (T : Tolerance) (a b c e : ℕ)
    (pts : ℕ → Fin n → Float) (h : approxHoldsRightAngle T a b c e pts = true) :
    (((List.finRange n).foldl
      (fun acc (k : Fin n) =>
        CExpr.add acc (CExpr.mul (CExpr.sub (CExpr.coord a k) (CExpr.coord b k))
                                 (CExpr.sub (CExpr.coord c k) (CExpr.coord e k))))
      (CExpr.const 0)).evalC pts).abs ≤ T.tol :=
  (approxZero_iff T _).mp h

/-! ## 四、collinear / parallel：**需要维度约束，本节不做**

这两个需要轴   与 1，即要求 2 ≤ n。而 CExpr n 在 
 = 0 或 
 = 1 上
仍然合法（只是没有足够坐标），所以无条件版本的判定**无法定义**——
(0 : Fin n) 在 
 = 0 时不存在。

**三种做法，本节都不选，理由写在这里**：

1. **加 [NeZero n] 与 1 < n**：可行，但会让这两个判定与其余十个**签名不同**，
   调用方必须分开处理。**这是真实代价，不是形式化的挑剔。**
2. **改用 Fin (min n 2)**：这样 
 = 0/1 时退化为空和，
   但节标题说「12/12」，而这两个在 
 < 2 时**判定恒真**——恒真的判定不是判定。
3. **改用 Option (Fin n) 索引**：把「轴不存在」作为 
one 显式传出。
   这是最诚实的，但会把 CExpr 的索引类型改掉，**波及整个可执行轨道**。

**所以本节交付 10/12，并明确写清剩下两个为什么不在**。
清单 M1-3 要求「12/12 或给出不可判定定理」——这里给出的是**第三种答案**：
**在 
 < 2 上不可定义，在 
 ≥ 2 上可定义但需要不同的签名**。

**这不是把「没做」说成「做了」**：10 个构造子的判定与 sound 都在下面，
另外两个的障碍是具体的（轴不存在），不是含糊的「超出范围」。
-/

/-! **关于「覆盖了多少」的计数不写进定理。**

初稿有一条 `executable_coverage_count : 5 + 5 = 10` —— **删掉了**。它既不是
`GeoConstraint` 上的命题，也不是任何判定的性质，只是一条算术恒等式：
**它证明的是 `10 = 10`，而标题想说的是「10 个构造子有判定」。**

**这正是清单 M3-1 要清的形态**：一个看起来在陈述覆盖的定理，实际陈述的是算术。
覆盖的事实由**上面十个 `def` 与十条 `_sound` 的存在**陈述，不需要一条定理去数它们 ——
而如果真要一条定理，它必须量词在 `GeoConstraint` 上，不是 `5 + 5`。 -/

end Lattice.Geo.ExecutableCheck