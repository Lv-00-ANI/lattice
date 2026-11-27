import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Compiler.WeightSequence
import Lattice.Lib.Compiler.GridAlgebra
import Lattice.Lib.Compiler.PiecewiseWeights
import Lattice.Lib.Compiler.PowChord

/-!
# **`RealLayer`：两套「符号 ⇄ 权重」实现的共同推广**（架构级尝试，分支 `feat-real-layer`）

## 为什么需要它

**第 1087 轮的对照文档记录了：条款 1.3/1.4 有两套互不引用的实现，且不可合并，理由有三
（数的域 `ℤ` vs `ℝ`、判据「恰为零」vs「有界」、组织轴「按约束」vs「按段」）。**

**⇒ 但「不可合并」不等于「无法解释」。⇒ 本文件给出一个共同推广：**

```lean
structure RealLayer where
  w : List ℝ
  b : ℝ
```

**⇒ 在这个载体上：**
- **主链是它在整数子环上的像**（`realLayerOfInt`：系数与输入都取整数）；
- **新线的 `Segment` 是它在单元素向量上的像**（`⟨[m], c⟩` 在 `[x]` 上）。

**⇒ 若两条都成立，「两套实现」就不是竞争关系，而是同一个推广的两个截面。**

## 本文件不改动两件东西

**⇒ 不改 `LinearLayer`、不改 `Segment`、不改它们的任何定理。**
**⇒ 本文件是并列新增：只提供推广与两条截面定理。**
-/

namespace Lattice.Lib.Compiler.RealLayer

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.GridAlgebra

/-- **显式的 `ℤ→ℝ` 强转**——定义成命名函数，使项的形状稳定。 -/
def castI (z : ℤ) : ℝ := (z : ℝ)

/-- **实数点积**（与主链 `dot` 同构：`zip` + `foldl`，故截断行为相同）。 -/
def dotR (a x : List ℝ) : ℝ :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0

/-- **实数线性层**：主链 `LinearLayer`（`ℤ`）与新线 `Segment`（`ℝ`）的共同推广。 -/
structure RealLayer where
  /-- The weight vector. -/
  w : List ℝ
  /-- The bias. -/
  b : ℝ

/-- **实数层的输出**：加权和加偏置。 -/
def RealLayer.out (l : RealLayer) (x : List ℝ) : ℝ :=
  dotR l.w x + l.b

/-- **整数层嵌入实数层**（系数与偏置逐项强转）。 -/
def realLayerOfInt (l : Lattice.LinearLayer) : RealLayer where
  w := l.w.map castI
  b := castI l.b

/-! ## 一、两个把 `zip` 与强转对齐的引理 -/

/-- **`zip` 与强转可交换**（逐元素强转后再 `zip` = 先 `zip` 再强转）。 -/
theorem zip_map_cast : ∀ (a x : List ℤ),
    (a.map castI).zip (x.map castI)
      = (a.zip x).map (fun p : ℤ × ℤ => (castI p.1, castI p.2))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | _ :: ys, _ :: zs => by
      simp only [List.map_cons, List.zip_cons_cons]
      rw [zip_map_cast ys zs]

/-- **`foldl` 与强转可交换**（带任意整数累加器）。

**⇒ 这是嵌入定理的算术内核：`ℤ` 上的加权和强转到 `ℝ`，等于在 `ℝ` 上做同一个加权和。 -/
theorem zip_fold_cast : ∀ (a x : List ℤ) (accZ : ℤ),
    (a.zip x).foldl (fun acc (uv : ℤ × ℤ) => acc + castI uv.1 * castI uv.2) (castI accZ)
      = castI ((a.zip x).foldl (fun acc (uv : ℤ × ℤ) => acc + uv.1 * uv.2) accZ)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | y :: ys, z :: zs, accZ => by
      have hacc : castI (accZ + y * z) = castI accZ + castI y * castI z := by
        simp only [castI]
        push_cast
        ring
      simp only [List.zip_cons_cons, List.foldl_cons]
      rw [← hacc, zip_fold_cast ys zs (accZ + y * z)]

/-- **⭐⭐ 点积与强转可交换**：`dotR (↑a) (↑x) = ↑(dot a x)`。 -/
theorem dot_cast (a x : List ℤ) :
    dotR (a.map castI) (x.map castI) = castI (Lattice.dot a x) := by
  unfold dotR Lattice.dot
  rw [zip_map_cast a x, List.foldl_map]
  simpa [castI] using zip_fold_cast a x 0

/-! ## 二、主链是它在整数子环上的像 -/

/-- **⭐⭐⭐ 主链嵌入**：整数层的输出强转到 `ℝ`，等于该层在实数层的输出（在逐项强转的输入上）。

**⇒ 这就是「主链 = 共同推广的整数截面」这句话的内容。**
**⇒ 它不改动 `LayerOut`：左边仍是主链的 `LayerOut`，右边才是新载体。 -/
theorem realLayer_ofInt_out (l : Lattice.LinearLayer) (x : List ℤ) :
    castI (Lattice.LayerOut l x) = (realLayerOfInt l).out (x.map castI) := by
  have h : dotR (l.w.map castI) (x.map castI) = castI (Lattice.dot l.w x) := dot_cast l.w x
  show castI (Lattice.dot l.w x + l.b)
      = dotR (l.w.map castI) (x.map castI) + castI l.b
  rw [h]
  simp only [castI]
  push_cast
  ring

/-! ## 三、新线是它在单元素向量上的像 -/

/-- **⭐⭐⭐ 新线嵌入**：实数层在 `[m]`、`[x]` 上的输出，就是新线那个分段在 `x` 处的求值。

**⇒ 故 `Segment` 是 `RealLayer` 的单段常数截面：`⟨m, c⟩` 即 `⟨[m], c⟩`。 -/
theorem realLayer_single_eq_segment (m c x : ℝ) :
    (RealLayer.out ⟨[m], c⟩ [x]) = (⟨m, c⟩ : Segment).eval x := by
  simp [RealLayer.out, dotR, Segment.eval]

/-! ## 四、两条截面合起来的读法 -/

/-- **⭐⭐ 主链的标量层就是共同推广在整数上的截面。**

**⇒ 这是第 1081 轮那条桥（`segment_eval_eq_scalar_layer_out`）在推广层上的解释：
两条桥各自只是「同一推广的两个截面」的特例。 -/
theorem two_sections_of_one_generalisation (w b x : ℤ) :
    castI (Lattice.LayerOut ⟨[w], b⟩ [x])
      = (RealLayer.out ⟨[castI w], castI b⟩ [castI x]) := by
  have h := realLayer_ofInt_out (⟨[w], b⟩ : Lattice.LinearLayer) [x]
  simpa [realLayerOfInt] using h

/-! ## 五、新线**消费**这个推广：`gridEval` 就是实数层上的求值 -/

/-- **每个 `Segment` 都是一个 `RealLayer`**（单坐标）。

**⇒ 这是一个**包装**，而不是一个新的定义：它不改 `Segment`，只把它**看成**推广的一个点。** -/
def segmentToRealLayer (s : Segment) : RealLayer :=
  ⟨[s.m], s.c⟩

/-- **⭐ 包装保求值**：它们在单点上的输出相同。** -/
theorem segmentToRealLayer_out (s : Segment) (x : ℝ) :
    (segmentToRealLayer s).out [x] = s.eval x := by
  simp [segmentToRealLayer, RealLayer.out, dotR, Segment.eval]

/-- **把一个分段族看成一个实数层族**（逐段包装）。** -/
def familyToRealLayers (g : ℕ → Segment) : ℕ → RealLayer :=
  fun k => segmentToRealLayer (g k)

/-- **⭐ 族级保求值**。** -/
theorem familyToRealLayers_out (g : ℕ → Segment) (k : ℕ) (x : ℝ) :
    (familyToRealLayers g k).out [x] = (g k).eval x :=
  segmentToRealLayer_out (g k) x

/-- **⭐⭐⭐ `gridEval` 就是实数层上的求值**——这是推广**被新线消费**的那一步。

**⇒ `gridEval g n x` 先选段号、再求值；而本条说「先选段号、再在实数层上求值」是**同一件事**。
⇒ 故新线所有精度定理（`pow_uniform_bound`、`quartic_uniform_bound_Icc` 等）
的结论，都可以读作**关于 `RealLayer` 输出的界**。**
**⇒ 而它**不改** `gridEval` 的定义：只提供一条等式，使两种写法可以互相带入。** -/
theorem gridEval_eq_realLayer_out (g : ℕ → Segment) (n : ℕ) (x : ℝ) :
    gridEval g n x = (familyToRealLayers g (segmentIndex n x)).out [x] := by
  unfold gridEval
  exact (segmentToRealLayer_out (g (segmentIndex n x)) x).symm

/-- **⭐⭐⭐ 新线最强的界现在是**关于 `RealLayer` 输出的界**。

**⇒ 这是推广**被新线消费**的实质证据：不是「有一个推广存在」，而是「新线的定理**可以改写成它**」。**
**⇒ 故 `RealLayer` 不是一个新小叶，而是一个**可带入下游的语言**。** -/
theorem pow_uniform_bound_as_realLayer (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 0 < n) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1,
      |x ^ d
          - (familyToRealLayers (Lattice.Lib.Compiler.SymbolicEntry.interpFamily n (fun t : ℝ => t ^ d))
              (segmentIndex n x)).out [x]|
        ≤ ((d * (d - 1) : ℕ) : ℝ) * (1 / (n : ℝ)) ^ 2 / 8 := by
  intro x hx
  have h := Lattice.Lib.Compiler.PowChord.pow_uniform_bound d hd n hn x hx
  rwa [gridEval_eq_realLayer_out] at h

/-! ## 五、嵌入是**单射**（Phase 1 的第一步） -/

/-- **`realLayerOfInt` 是单射**。

**⇒ 这是 W1-1 里一直缺的那一半：正向嵌入（`realLayerOfInt`）与它的语义定理**
**（`realLayer_ofInt_out`）已存在，但**反方向没有任何声明**——故「两个截面」一直只是一个嵌入。**
**⇒ 单射性是能在**不引入 `Option`** 的情录下证明的最强那条：它说「整数截面里不会两个不同层被嵌成同一个实数层」。 -/
theorem realLayerOfInt_injective {l₁ l₂ : Lattice.LinearLayer}
    (h : realLayerOfInt l₁ = realLayerOfInt l₂) : l₁ = l₂ := by
  -- **形式上的一个坑（记在证明里，因为下一个人会重犯）**：`induction l₁.w generalizing l₂.w`
  -- **报「unexpected term l₂.w」——**不能 generalize 一个投影**。故先把两个列表抽成变量。**
  have list_inj : ∀ (a b : List ℤ), a.map castI = b.map castI → a = b := by
    intro a b hab
    induction a generalizing b with
    | nil =>
        cases b with
        | nil => rfl
        | cons _ _ => simp at hab
    | cons x t ih =>
        cases b with
        | nil => simp at hab
        | cons y s =>
            simp only [List.map_cons, List.cons.injEq] at hab
            obtain ⟨hxy, hts⟩ := hab
            have hEq : x = y := Int.cast_injective hxy
            subst hEq
            rw [ih s hts]
  have hw : l₁.w = l₂.w := list_inj _ _ (congrArg RealLayer.w h)
  have hb : l₁.b = l₂.b := by
    have hbmap : castI l₁.b = castI l₂.b := congrArg RealLayer.b h
    exact Int.cast_injective hbmap
  cases l₁
  cases l₂
  simp_all

end Lattice.Lib.Compiler.RealLayer