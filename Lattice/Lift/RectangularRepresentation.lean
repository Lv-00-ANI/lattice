/-
# 任意形状的层可**精确**往返：`m × n` 的 `Representation`

## 0. 这一节补什么

第 181 轮把满宽编码器推广到长方阵（`RectangularWeightEncoding.lean`），交付了编码器、逆与往返。
**但那三条是三个独立定理，不是「一个精确的双向表示」。**

方阵的情形第 168 轮已经装进了 `weightSymbolRep : Representation … `。**长方阵还没有。**
所以「任意形状的层都可精确往返」这句话，在库里此前**不能被引用为一条定理**——
读者得自己去拼 `roundtrip_rect` + `layerOfListRect_eq_full_width`。

本节把它装进 `Representation`，于是逆向是 `extract`、往返是 `roundtrip`，与方阵版同构。

## 1. 长度约束进类型

`Representation.roundtrip : ∀ p, extract (compile p) = p` 没有给前提留位置，
而 `roundtrip_rect` 需要 `p.val.length = m*n + n`。所以符号侧取**子类型**：

```lean
P := { s : List ℝ // s.length = m * n + n }
```

**这不是回避**：一个 `m × n` 矩阵加 `n` 个偏置，其符号侧**本来就是定长的**。
写成裸 `List ℝ` 只是丢掉一个约束再从外部补回来——方阵版第 168 轮做过同一个判断。

## 2. 与方阵版的关系

`m = n` 时本节退化为 `weightSymbolRep`。`rectangularRep_degenerates` 把这一点写成定理：
两个 `Representation` 的 `compile` 在 `m = n` 时逐字相同。

**所以本节是推广，不是平行的一条路。**

## 3. 边界

- **`0 < n` 必需**（`Fin n` 可居留、`k % n` 有意义）。
- **`m = 0` 是允许的**：没有系数、`n` 个偏置、长度 `n`。方阵版表达不了这个情形。
- **`encode` / `decode` 取 `id`**：与方阵版同一处理——两侧的输入空间在这里恰好相同
  （都是 `Fin n → ℝ`，即被作用的点）。这不是偷懒：`Representation` 要求这两者只是为了
  允许两侧输入空间不同（例如 token 化），这里不需要。
- 本节**不改** `Extraction.lean`、`WeightSymbolRepresentation.lean`、
  `RectangularWeightEncoding.lean` 的任何既有定理。
-/
import Mathlib
import Lattice.Lift.Extraction
import Lattice.Lift.RectangularWeightEncoding
import Lattice.Lift.WeightSymbolRepresentation

namespace Lattice.Lift.Rectangular

open Lattice.Core

variable {m n : ℕ}

/-- **任意 `m × n` 层的精确双向表示**：`compile := layerOfListRect`，`extract := listOfLayerRect`。

`roundtrip` 用的是 `roundtrip_rect`，不是假设。 -/
noncomputable def rectangularRep (hn : 0 < n) :
    Representation { s : List ℝ // s.length = m * n + n } (LayerParams (Fin m) (Fin n)) where
  inputP := Fin n → ℝ
  inputW := Fin n → ℝ
  encode := id
  decode := id
  compile := fun p => layerOfListRect (m := m) (n := n) p.val
  extract := fun L => ⟨listOfLayerRect hn L, listOfLayerRect_length hn L⟩
  roundtrip := by
    intro p
    apply Subtype.ext
    exact roundtrip_rect hn p.val p.property

/-- **往返**：提取是编译的逆。 -/
theorem rectangularRep_roundtrip (hn : 0 < n)
    (p : { s : List ℝ // s.length = m * n + n }) :
    (rectangularRep (m := m) (n := n) hn).extract
        ((rectangularRep (m := m) (n := n) hn).compile p) = p :=
  (rectangularRep (m := m) (n := n) hn).roundtrip p

/-- **读回的值就是原来的列表**。 -/
theorem rectangularRep_val_roundtrip (hn : 0 < n) (s : List ℝ)
    (hlen : s.length = m * n + n) :
    ((rectangularRep (m := m) (n := n) hn).extract
        ((rectangularRep (m := m) (n := n) hn).compile ⟨s, hlen⟩)).val = s := by
  rw [rectangularRep_roundtrip]

/-- **读回系数**：逆读出的第 `i*n + j` 项就是编译进去的 `W i j`。

这条把「提取」与权重矩阵的**分量**连起来，而不只是说两个列表相等。 -/
theorem rectangularRep_coeff (hn : 0 < n) (s : List ℝ) (hlen : s.length = m * n + n)
    (i : Fin m) (j : Fin n) :
    ((rectangularRep (m := m) (n := n) hn).extract
        ((rectangularRep (m := m) (n := n) hn).compile ⟨s, hlen⟩)).val.getD
        (i.val * n + j.val) 0 =
      (layerOfListRect (m := m) (n := n) s).W i j := by
  rw [rectangularRep_val_roundtrip]
  exact (layerOfListRect_W s i j).symm

/-- **读回偏置**：第 `m*n + j` 项就是 `b j`。 -/
theorem rectangularRep_bias (hn : 0 < n) (s : List ℝ) (hlen : s.length = m * n + n)
    (j : Fin n) :
    ((rectangularRep (m := m) (n := n) hn).extract
        ((rectangularRep (m := m) (n := n) hn).compile ⟨s, hlen⟩)).val.getD
        (m * n + j.val) 0 =
      (layerOfListRect (m := m) (n := n) s).b j := by
  rw [rectangularRep_val_roundtrip]
  exact (layerOfListRect_b s j).symm

/-- **`m = n` 时退化为方阵版**：两个 `Representation` 的 `compile` 逐字相同。

这是「推广而非平行」的机器检查形式：方阵版不是被取代，而是本节的一个特例。 -/
theorem rectangularRep_degenerates (h : 0 < n) (s : List ℝ)
    (hlen : s.length = n * n + n) (i j : Fin n) :
    ((rectangularRep (m := n) (n := n) h).compile ⟨s, hlen⟩).W i j =
        ((FullWidth.weightSymbolRep h).compile ⟨s, hlen⟩).W i j ∧
      ((rectangularRep (m := n) (n := n) h).compile ⟨s, hlen⟩).b j =
        ((FullWidth.weightSymbolRep h).compile ⟨s, hlen⟩).b j := by
  refine ⟨?_, ?_⟩
  · show (layerOfListRect (m := n) (n := n) s).W i j =
      (FullWidth.layerOfListFull (n := n) s).W i j
    exact (layerOfListRect_eq_full_width s i j).1
  · show (layerOfListRect (m := n) (n := n) s).b j =
      (FullWidth.layerOfListFull (n := n) s).b j
    exact (layerOfListRect_eq_full_width s i j).2

/-- **任意形状的层都可精确往返**——本节的主结论，一条可引用的陈述。

它说的是：对**任意** `m`、`n`（`n > 0`），存在一个 `Representation`，其 `compile` 是本节
的满宽编码器，且 `roundtrip` 已证。**方阵只是 `m = n` 的特例。** -/
theorem any_shape_is_exactly_representable :
    ∀ (m n : ℕ) (_hn : 0 < n),
      ∃ R : Representation { s : List ℝ // s.length = m * n + n }
              (LayerParams (Fin m) (Fin n)),
        (∀ p, R.compile p = layerOfListRect (m := m) (n := n) p.val) ∧
        (∀ p, R.extract (R.compile p) = p) :=
  fun m n hn =>
    ⟨rectangularRep (m := m) (n := n) hn, fun _ => rfl,
     rectangularRep_roundtrip (m := m) (n := n) hn⟩

end Lattice.Lift.Rectangular
