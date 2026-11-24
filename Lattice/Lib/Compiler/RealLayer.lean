import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.Compiler.WeightSequence

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

end Lattice.Lib.Compiler.RealLayer