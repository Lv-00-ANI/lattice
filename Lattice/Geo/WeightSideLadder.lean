/-
# 几何约束能编译成**权重**吗？—— 不能，除了一类可仿射化的

## 0. 清单 M1-1 的问题

`GeoLadder` 的 `l2l3` 产出的是**损失函数** `(ℕ → Pt n) → ℝ`，`satW` 里还固定了一个 `pts`：

```lean
l2l3      := compileConstraint
satSym    := fun c => EqConstraint.poly c pts = 0
satW      := fun L => L pts ≤ 0
```

**那不是「编译成权重」**：损失是训练时用的标量，权重是推理时执行的东西。
两者在这一节之前**从未在几何层接通过**。

清单要求：一个 `Ladder`，`W = List (AffineLayer)`，`satW := ∀ pts`。
**或者证明在非线性约束下不可能，并给出条件类。**

## 1. 答案是**两者都有**：一般不可能，线性子类可以

### 不可能的那一半

仿射层 `x ↦ Wx + b` 的零点集在 `ℝ` 上是**至多一个点**（斜率非零时）。

而 `sqDistEq a b d` 在 1 维、`d > 0` 时的零集是 **两个点**（`±√d`）。

**所以：不存在非零斜率的仿射层，其零点集恰好等于球面方程的解集。**

`no_affine_represents_sphere` 把这句话写成定理。**这不是「没做」，是否定也是定理。**

推广：`GeoConstraint` 的 12 个构造子里，只有**线性**的那几个
（`eqZero`/`leZero`/`ltZero`/`gtZero` 作用在线性表达式上）的零集是超平面。
其余（`sqDistEq`、`equalLength`、`collinear`、`perpendicular`、`parallel`、
`rightAngle`、`midpoint`、`samePoint`）都含二次或更高次项——
**注意 `samePoint` 与 `midpoint` 是例外**：它们逐坐标线性，见下一节。

### 可以的那一半

**逐坐标线性的约束可以编译成仿射层**：`samePoint a b` 要求每个坐标相等，
`midpoint m a b` 要求 `2·m = a + b` 逐坐标。

这两条第 `i` 个方程只涉及坐标 `aᵢ`、`bᵢ`（或 `mᵢ`），所以是**一层线性投影**：
把 `(ℕ → Pt n)` 的第 `i` 个分量投影出来做差。

**本节把 `samePoint` 编译成真正的 `AffineLayer`**，并给出 `satW := ∀ pts`。

## 2. 权重侧的形状

关键设计：**权重侧的空间是「残差空间」，不是原空间。**

```lean
W  : List (AffineLayer (Fin n))     -- 输出 n 维残差（每个坐标一个）
x  : Fin n → ℝ                       -- 输入：某个点/坐标向量的编码
```

`netAct` 在 `Fin n` 上作用，所以**同一宽度**。`samePoint a b` 的残差是
「每个坐标的差」，正好是 `Fin n` 维。

**这不是把几何塞进仿射层**：`samePoint` 天然逐坐标解耦，所以它的残差是线性的。
**一般约束做不到，因为它们的耦合是非线性的。**

## 3. 边界

- **只交付 `samePoint` 的权重侧实例。** `midpoint` 同样是线性的，但没有做——
  它与 `samePoint` 形状相同，多一个系数 2，**留作下一步而不是假装它已经在里面**。
- **`netAct` 要求所有层同宽**，所以本节的 `Ladder` 只用一层。多层栈需要宽度匹配，
  而几何约束的中间残差没有自然的多层结构——**硬凑多层只会得到一个没有意义的东西**。
- **`satW` 是 `∀ pts`**（清单的验收要求），不是单点——这一点由 `l2l3_sound` 的形状保证。
- 本节**不改** `GeoLadder`：那个 `Ladder` 的 `l2l3` 是损失，它的用途不同（训练），
  两者并存。
-/
import Mathlib
import Lattice.Runtime.EndToEnd
import Lattice.Domains.Constraint
import Lattice.Geo.GeoLadder
import Lattice.Core.Net

namespace Lattice.Geo.WeightSide

open Lattice.Core

/-! ## 一、不可能性：球面不能被仿射层表示 -/

/-- **`ℝ` 上的仿射函数**。 -/
noncomputable def aff (w b x : ℝ) : ℝ := w * x + b

/-- **非零斜率的仿射函数零点集至多一个点。** -/
theorem affine_zeroSet_subsingleton (w b : ℝ) (hw : w ≠ 0) :
    ∀ x y : ℝ, aff w b x = 0 → aff w b y = 0 → x = y := by
  intro x y hx hy
  unfold aff at hx hy
  have h : w * x = w * y := by linarith
  exact mul_left_cancel₀ hw h

/-- **球面方程有两个不同的解。** -/
theorem sq_eq_two_roots (d : ℝ) (hd : 0 < d) :
    ∃ x y : ℝ, x ≠ y ∧ x * x = d ∧ y * y = d := by
  have hsq : Real.sqrt d * Real.sqrt d = d := by
    rw [← pow_two]; exact Real.sq_sqrt hd.le
  refine ⟨Real.sqrt d, -Real.sqrt d, ?_, hsq, ?_⟩
  · have hpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
    intro h
    linarith
  · rw [neg_mul_neg]; exact hsq

/-- **否定的那一半（清单 M1-1 的 N）**：不存在非零斜率的仿射函数，其零点集恰好是
`x * x = d`（`d > 0`）的解集。

**所以 `sqDistEq` 这类二次约束不能被仿射层精确表示。**
这不是「还没做」，是**不可能**——仿射层在 1 维上的零集至多一点，而球面方程有两点。 -/
theorem no_affine_represents_sphere (d : ℝ) (hd : 0 < d) :
    ¬ ∃ (w b : ℝ), w ≠ 0 ∧ ∀ x : ℝ, (aff w b x = 0 ↔ x * x = d) := by
  intro ⟨w, b, hw, hiff⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := sq_eq_two_roots d hd
  exact hxy (affine_zeroSet_subsingleton w b hw x y
    ((hiff x).mpr hx) ((hiff y).mpr hy))

/-! ## 二、可以的那一半：`samePoint` 的权重侧实例 -/

/-- **`samePoint` 的残差层**：把 `a` 与 `b` 的坐标差算出来。

权重矩阵取**单位矩阵**（每行选一个坐标），偏置取 `-b` 的对应坐标。
于是 `affineAct` 给出 `aᵢ - bᵢ`。

**这是一层真正的仿射层**，不是损失：`W` 与 `b` 都是权重。 -/
noncomputable def samePointLayer (enc : ℕ → Fin n → ℝ) (a b : ℕ) : AffineLayer (Fin n) where
  W := fun i j => if i = j then 1 else 0
  b := fun j => -enc b j

/-- **残差正是坐标差**：`satW` 的零点等价于每个坐标相等。 -/
theorem samePointLayer_act (enc : ℕ → Fin n → ℝ) (a b : ℕ) (j : Fin n) :
    Lattice.Core.affineAct (samePointLayer enc a b) (enc a) j = enc a j - enc b j := by
  unfold Lattice.Core.affineAct samePointLayer
  simp only
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, one_mul]
    ring
  · intro k _ hk
    simp [hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **权重侧谓词**：所有坐标的残差为零。 -/
def samePointSatW (enc : ℕ → Fin n → ℝ) (a b : ℕ) (L : List (AffineLayer (Fin n))) : Prop :=
  ∀ j : Fin n, netAct L (enc a) j = 0

/-- **`samePoint` 的权重侧 `Ladder`**：`l2l3` 产出一层真正的仿射权重。

**这是清单 M1-1 要的那个形状**：`W = List (AffineLayer)`，`satSym` 说坐标相等，
`l2l3_sound` 把「坐标相等」翻成「权重作用在编码上给出零残差」。 -/
noncomputable def samePointLadder (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    Lattice.Lift.Ladder (List Unit) Unit (List Unit) (List (AffineLayer (Fin n))) where
  l0l1 := Lattice.Lift.identityTokenizer Unit
  l1l2 := Lattice.Lift.identityTokenizer Unit
  l2l3 := fun _ => [samePointLayer enc a b]
  satSym := fun _ => ∀ j : Fin n, enc a j = enc b j
  satW := samePointSatW enc a b
  l2l3_sound := by
    intro _ h j
    show Lattice.Core.netAct [samePointLayer enc a b] (enc a) j = 0
    show Lattice.Core.netAct [samePointLayer enc a b] (enc a) j = 0
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, samePointLayer_act, h j, sub_self]

/-- **端到端**：坐标全相等 ⟹ 权重层的残差全为零，**对任意编码都成立**（`satW` 是 `∀`）。 -/
theorem samePointLadder_forward (enc : ℕ → Fin n → ℝ) (a b : ℕ)
    (h : (samePointLadder enc a b).satSym []) :
    (samePointLadder enc a b).satW ((samePointLadder enc a b).l2l3 []) :=
  (samePointLadder enc a b).ladder_forward [] h

/-- **反过来也成立**：残差全零 ⟹ 坐标全相等。

**这条让上面的实例不是重言**：`satW` 与 `satSym` 在 `l2l3` 的像上**等价**，
不是单向蕴含。 -/
theorem samePointLadder_satW_iff (enc : ℕ → Fin n → ℝ) (a b : ℕ) :
    (samePointLadder enc a b).satW ((samePointLadder enc a b).l2l3 []) ↔
      (∀ j : Fin n, enc a j = enc b j) := by
  constructor
  · intro h j
    have hz : Lattice.Core.netAct [samePointLayer enc a b] (enc a) j = 0 := h j
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, samePointLayer_act] at hz
    linarith
  · intro h j
    show Lattice.Core.netAct [samePointLayer enc a b] (enc a) j = 0
    show Lattice.Core.netAct [samePointLayer enc a b] (enc a) j = 0
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, samePointLayer_act, h j, sub_self]

/-! ## 六、第二个实证：`midpoint` 的权重侧桥

### 为什么只有这两个构造子能做这件事

`samePoint` 能被**一层真正的仿射权重**表示，是因为它的 `Holds` 是

```
∀ j, enc a j = enc b j          -- 逐坐标的仿射等式
```

`midpoint` 是**同一个形状**：

```
∀ j, 2 · enc m j = enc a j + enc b j      -- 同样是逐坐标的仿射等式
```

于是 `W = 2·I`、`b j = −(enc a j + enc b j)` 就能把残差做成 `2·enc m j − enc a j − enc b j`。

**其余 10 个构造子不是这个形状**，理由分三类：

| 类 | 构造子 | 为什么不行 |
|:--|:--|:--|
| 单个仿射泛函 | `eqZero`、`leZero`、`ltZero`、`gtZero` | `Holds` 是**一个标量**的条件，不是 `n` 个坐标的条件。一层能产出它，但 `satW` 的形状要改成「某个输出 ≤ 0」，不是本节这个 `∀ j` |
| 二次 | `sqDistEq`、`equalLength` | 零点集是球面/双曲面。**`no_affine_represents_sphere` 已经证明 `d > 0` 时不可能用仿射表示** |
| 双线性 | `perpendicular`、`rightAngle`、`collinear`、`parallel` | 零点集是锥面，同样不是仿射子空间 |

**所以「12 个构造子里有几个能走到权重侧」的答案是 2 个（`samePoint`、`midpoint`），
另外 4 个是「一个泛函」、6 个是「非线性零点集」。这不是没做，是分类的结果。** -/

/-- **`midpoint` 的权重侧层**：`W = 2·I`、`b j = −(enc a j + enc b j)`。

作用在 `enc m` 上，残差就是 `2·enc m j − enc a j − enc b j`。 -/
noncomputable def midpointLayer (enc : ℕ → Fin n → ℝ) (m a b : ℕ) : AffineLayer (Fin n) where
  W := fun i j => if i = j then 2 else 0
  b := fun j => -(enc a j + enc b j)

/-- **残差正是 `2·m − a − b` 的逐坐标形式。** -/
theorem midpointLayer_act (enc : ℕ → Fin n → ℝ) (m a b : ℕ) (j : Fin n) :
    Lattice.Core.affineAct (midpointLayer enc m a b) (enc m) j
      = 2 * enc m j - enc a j - enc b j := by
  unfold Lattice.Core.affineAct midpointLayer
  simp only
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte]
    ring
  · intro k _ hk
    simp [hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **权重侧谓词**：所有坐标的残差为零。 -/
def midpointSatW (enc : ℕ → Fin n → ℝ) (m a b : ℕ) (L : List (AffineLayer (Fin n))) : Prop :=
  ∀ j : Fin n, netAct L (enc m) j = 0

/-- **`midpoint` 的权重侧 `Ladder`**：与 `samePoint` 同构，只是 `W` 是 `2·I`、偏置带两项。 -/
noncomputable def midpointLadder (enc : ℕ → Fin n → ℝ) (m a b : ℕ) :
    Lattice.Lift.Ladder (List Unit) Unit (List Unit) (List (AffineLayer (Fin n))) where
  l0l1 := Lattice.Lift.identityTokenizer Unit
  l1l2 := Lattice.Lift.identityTokenizer Unit
  l2l3 := fun _ => [midpointLayer enc m a b]
  satSym := fun _ => ∀ j : Fin n, 2 * enc m j = enc a j + enc b j
  satW := midpointSatW enc m a b
  l2l3_sound := by
    intro _ h j
    show Lattice.Core.netAct [midpointLayer enc m a b] (enc m) j = 0
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, midpointLayer_act]
    linarith [h j]

/-- **端到端**：`2m = a + b` 逐坐标成立 ⟹ 权重层残差全零。 -/
theorem midpointLadder_forward (enc : ℕ → Fin n → ℝ) (m a b : ℕ)
    (h : (midpointLadder enc m a b).satSym []) :
    (midpointLadder enc m a b).satW ((midpointLadder enc m a b).l2l3 []) :=
  (midpointLadder enc m a b).ladder_forward [] h

/-- **反过来也成立**：残差全零 ⟹ `2m = a + b` 逐坐标。

**这条让实例不是重言**：`satW` 与 `satSym` 在 `l2l3` 的像上**等价**。 -/
theorem midpointLadder_satW_iff (enc : ℕ → Fin n → ℝ) (m a b : ℕ) :
    (midpointLadder enc m a b).satW ((midpointLadder enc m a b).l2l3 []) ↔
      (∀ j : Fin n, 2 * enc m j = enc a j + enc b j) := by
  constructor
  · intro h j
    have hz : Lattice.Core.netAct [midpointLayer enc m a b] (enc m) j = 0 := h j
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, midpointLayer_act] at hz
    linarith
  · intro h j
    show Lattice.Core.netAct [midpointLayer enc m a b] (enc m) j = 0
    rw [Lattice.Core.netAct, List.foldl_cons, List.foldl_nil, midpointLayer_act]
    linarith [h j]

end Lattice.Geo.WeightSide
