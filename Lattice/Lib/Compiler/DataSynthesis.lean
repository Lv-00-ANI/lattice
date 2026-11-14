import Mathlib
import Lattice.Lib.Compiler.CarrierClosure
import Lattice.Runtime.LoopClosure

/-!
# 数据合成：从**一个**满足点生成**一族**满足样本（阶段 C，P6）

## 为什么这一轮要做

**目标里的三种正向产物：**

| 产物 | 状态 |
|:--|:--|
| **约束损失** | **`Runtime/ConstraintToLoss.lean`（第 915 轮实测存在）** |
| **结构化初始化** | **`Runtime/StructuredInit.lean`（第 915 轮新建）** |
| **数据合成** | **只在 `Lattice/Reference/Geometry/Geometry/Synthesis*.lean`，且**绑定到 `GeoConstraint`**** |

**=> 数据合成确实存在，但它的载体是**几何约束**，不是表示链的约束。**
**它的定理（如 `synthesize_perpendicular_samples`）说的是「从一个满足的几何配置出发，
标准变换族给出五个满足的样本」——**形态**是对的，但**载体**不对。**

## 本文件做的是**推广**，不是重写

**`Synthesis.lean` 的模式可以一字不改地抽象掉几何：**

```
给定约束集 cs、一个满足点 seed、一个保持满足的变换族 Ts
⟹ 生成的样本列表全部满足 cs
```

**=> 这个模式与 `GeoConstraint` 无关。本文件把它提到 `Carrier` 层面，
于是它对**所有**载体成立 —— 线性、relu、sign，以及将来任何满足两条义务的载体。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `preserving_family` | **⭐ 保持满足的变换族** |
| **`samples_sound`** | **⭐⭐ 生成的样本全部满足约束** |
| **`synthesize_from_satisfying`** | **⭐⭐ 从一个满足点生成一族满足样本** |
| **`synthesis_is_nonvacuous`** | **⭐ 非空性：满足点存在时，合成真的产出样本** |

**=> 第 3 条是本轮的交付：它把几何版的那个模式，变成**任何载体**上的定理。** -/

namespace Lattice.Lib.Compiler.DataSynthesis

open Lattice.Lib.Compiler.CarrierClosure

/-- **⭐ 保持满足的变换族。**

**=> `Ts` 是一列变换，每个都把满足 `Sat` 的点映成满足 `Sat` 的点。**

**=> 几何版的 `standardFamily_preserves_perpendicular` 是这个定义的一个实例；
这里去掉几何，只留结构。** -/
structure PreservingFamily (C : Carrier) where
  /-- 变换族（一列变换）。 -/
  Ts : List (C.Symbol → C.Symbol)
  /-- **每个变换都保持满足。** -/
  preserves : ∀ T ∈ Ts, ∀ s, C.Sat s → C.Sat (T s)

/-- **⭐ 把变换族作用在种子上，得到样本列表。**

**=> 与几何版的 `samples` 同构造：逐项作用。** -/
def synthSamples (C : Carrier) (F : PreservingFamily C) (seed : C.Symbol) : List C.Symbol :=
  F.Ts.map (fun T => T seed)

/-- **⭐⭐ 生成的样本**全部**满足约束。**

**=> 陈述：若种子满足 `C.Sat`，则 `synthSamples C F seed` 的**每一项**都满足 `C.Sat`。**

**=> 这是几何版 `samples_sound` 的**载体无关**形式。**
**证明只用 `PreservingFamily.preserves` 与 `List.mem_map`，因此对任何载体成立。** -/
theorem samples_sound (C : Carrier) (F : PreservingFamily C) {seed : C.Symbol}
    (h : C.Sat seed) : ∀ s ∈ synthSamples C F seed, C.Sat s := by
  intro s hs
  unfold synthSamples at hs
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hs
  exact F.preserves T hT seed h

/-- **⭐⭐ 从一个满足点，生成一族满足样本。**

**=> 这条把「数据合成」写成一条定理：**给定一个满足约束的种子，
存在一个样本列表，其每一项都满足约束。**

**=> **它同时给出判据侧的形式**：每个生成的样本经 `Carrier.criterion` 也对应一个权重层，
其输出为零。于是合成出的数据**直接可用作训练样本**。** -/
theorem synthesize_from_satisfying (C : Carrier) (F : PreservingFamily C) {seed : C.Symbol}
    (h : C.Sat seed) :
    (∀ s ∈ synthSamples C F seed, C.Sat s) ∧
      (∀ s ∈ synthSamples C F seed, C.out (C.compile s)) := by
  refine ⟨fun s hs => samples_sound C F h s hs, ?_⟩
  intro s hs
  exact C.sound s (samples_sound C F h s hs)

/-- **⭐ 非空性：若变换族非空，则合成真的产出样本。**

**=> 这条排除「合成了一个空列表」这种空洞满足。
一个非空的 `Ts` 保证 `synthSamples` 非空。** -/
theorem synthesis_is_nonvacuous (C : Carrier) (F : PreservingFamily C)
    (hne : F.Ts ≠ []) (seed : C.Symbol) : synthSamples C F seed ≠ [] := by
  unfold synthSamples
  intro h
  apply hne
  exact (List.map_eq_nil_iff.mp h)

/-- **⭐⭐ 总结：数据合成在本链上的完整内容。**

**=> （1）从满足点生成；（2）每一项满足；（3）每一项编译出的权重层输出为零；（4）非空。**

**=> 四条合起来，就是目标里「数据合成」这一产物在**任意载体**上的精确定义与保证。** -/
theorem synthesis_complete (C : Carrier) (F : PreservingFamily C)
    (hne : F.Ts ≠ []) {seed : C.Symbol} (h : C.Sat seed) :
    (∀ s ∈ synthSamples C F seed, C.Sat s) ∧
      (∀ s ∈ synthSamples C F seed, C.out (C.compile s)) ∧
      synthSamples C F seed ≠ [] :=
  ⟨fun s hs => samples_sound C F h s hs,
   fun s hs => C.sound s (samples_sound C F h s hs),
   synthesis_is_nonvacuous C F hne seed⟩

end Lattice.Lib.Compiler.DataSynthesis
