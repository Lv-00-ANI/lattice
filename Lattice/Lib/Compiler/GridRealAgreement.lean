/-
# `GridRealAgreement` —— L3 的两个入口在**求值**上给出同一个数

**这个文件为什么存在（第 1184 轮，Phase 1 的 W1-3）**

`Lib/Compiler/` 里有**两条**把「分段族」变成权重侧的入口，形状不同：

| 入口 | 类型 | 形状 |
|:--|:--|:--|
| `encodeGrid` | `(ℕ → Segment) → ℕ → ℝ` | **交错扁向量**：偶数位放斜率 `m`，奇数位放截距 `c` |
| `familyToRealLayers` | `(ℕ → Segment) → ℕ → RealLayer` | **每段一个只含一个权重的层**：`⟨[m], c⟩` |

**⇒ 二者此前**只有各自的求值定理**（`modelsBehavior_encodeGrid`、`familyToRealLayers_out`），**
**⇒ 而**没有一条定理说它们给的是同一个数**——「三个 L3 入口」的缺口里，这是最小的那一个。**

**⇒ 本文件的定理把它补上：同一段、同一个 `x`，两条入口求值相等。**

**⇒ 为什么不写进 `IRWeightsBridge.lean` 或 `RealLayer.lean`**：两个方向都试过，**都成环**——
`IRWeightsBridge → RealLayer → WeightSequence/PiecewiseWeights → SymbolicEntry → IRWeightsBridge`。
**⇒ 故另立一个**只做这一座桥**的文件，它同时 import 两侧，因而不成环；**
**⇒ 名字空间取 `GridRealAgreement`，避免与两侧的 `LayerOut`/`encodeGrid` 同名冲突（本会话已因同名吃过一次亏）。**
-/

import Lattice.Lib.Compiler.IRWeightsBridge
import Lattice.Lib.Compiler.RealLayer

namespace Lattice.Lib.Compiler.GridRealAgreement

/-- **⭐⭐ L3 的两个表示在求值上一致**。

**⇒ 左边是**结构化**的读法（一个 `RealLayer` 在把 `x` 看作单点输入时的输出）；**
**⇒ 右边是**扁平**的读法（交错向量里取该段的 `m`、`c`，再作仿射组合）。**
**⇒ 二者相等，故「两种编码」不是两套语义，而是**同一语义的两种形状**。 -/
theorem familyToRealLayers_out_eq_encodeGrid (g : ℕ → Lattice.Lib.Compiler.WeightSequence.Segment)
    (k : ℕ) (x : ℝ) :
    (Lattice.Lib.Compiler.RealLayer.familyToRealLayers g k).out [x]
      = (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g) (2 * k) * x
        + (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g) (2 * k + 1) := by
  rw [Lattice.Lib.Compiler.RealLayer.familyToRealLayers_out,
      Lattice.Lib.Compiler.WeightSequence.Segment.eval,
      Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid_even,
      Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid_odd]

/-- **⭐ 推论：整族一致**（把上一条对**任意段**用量词形式写出，便于下游一次引用）。 -/
theorem encoding_agreement (g : ℕ → Lattice.Lib.Compiler.WeightSequence.Segment) :
    ∀ k : ℕ, ∀ x : ℝ,
      (Lattice.Lib.Compiler.RealLayer.familyToRealLayers g k).out [x]
        = (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g) (2 * k) * x
          + (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g) (2 * k + 1) :=
  fun k x => familyToRealLayers_out_eq_encodeGrid g k x

/-- **⭐⭐⭐ 全域对齐：`gridEval` 的**扁读法**。

**⇒ 左边是新线的「选段再求值」（`gridEval g n x`）；**
**⇒ 右边是「从交错向量里取该段的 `m`、`c`」。**
**⇒ 由两条既有桥**直接夹出来**：`gridEval_eq_realLayer_out`（`RealLayer.lean`）把 `gridEval` 接到 `familyToRealLayers`，**
**⇒ 而本文件的 `familyToRealLayers_out_eq_encodeGrid` 把 `familyToRealLayers` 接到 `encodeGrid`。**

**⇒ 故本条**不是新假设**，而是把两条现有定理**合成一条可直接引用的陈述**。 -/
theorem gridEval_eq_encodeGrid (g : ℕ → Lattice.Lib.Compiler.WeightSequence.Segment)
    (n : ℕ) (x : ℝ) :
    Lattice.Lib.Compiler.GridAlgebra.gridEval g n x
      = (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g)
          (2 * Lattice.Lib.Compiler.PiecewiseWeights.segmentIndex n x) * x
        + (Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g)
          (2 * Lattice.Lib.Compiler.PiecewiseWeights.segmentIndex n x + 1) := by
  rw [Lattice.Lib.Compiler.RealLayer.gridEval_eq_realLayer_out]
  exact familyToRealLayers_out_eq_encodeGrid g
    (Lattice.Lib.Compiler.PiecewiseWeights.segmentIndex n x) x

end Lattice.Lib.Compiler.GridRealAgreement