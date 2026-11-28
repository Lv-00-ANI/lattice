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
import Lattice.Core.IR.Chain  -- L3's third entry: Lib -> Core is DOWNWARD (3 -> 0)

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

/-! ## 三、第三处入口：**不可比**（实测，而非判断） -/

/-- **⭐⭐ 第三处 L3 入口与本文件的两处**不是同一个编码**。

**⇒ `compileSkel k = fun n => if n = 0 then (skeletonCode k : ℝ) else 0`**（`Core/IR/Chain.lean:69`）：**
**⇒ 它只在 **0 号槽**放一个 **Nat 码**，**其余位置恒为 0**。**
**⇒ 而 `encodeGrid g` 的奇数位是 `(g (i/2)).c`，可以是**任意实数**。**

**⇒ 故此处的不可比**不是一个判断，而是一个可证的**否定**：只要某段的截距非 0，**
**⇒ `encodeGrid g` 就与任何 `compileSkel k` 在 1 号位上不同。**

**⇒ ⊨ 而这正是规划 W1-3 要的那条：「若两者都不可，写一条『L3 有三个互不等价表示』的定理」。**
**⇒ 故本文件的结论是两条定理合起来：**前两处入口逐段与全域都接通（§一/§二），**
**⇒ 而第三处**原则上不能接**，因为它编码的是**结构（形状）**而不是**函数（分段仿射）**。** -/
theorem encodeGrid_ne_compileSkel (g : ℕ → Lattice.Lib.Compiler.WeightSequence.Segment)
    (k : Lattice.Core.IR.IRSkeleton) (hc : (g 0).c ≠ 0) :
    Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g ≠ Lattice.Core.IR.compileSkel k := by
  intro h
  have h1 := congrFun h 1
  -- 左边在 1 号位是 `(g 0).c`（奇数位），右边恒为 0（1 ≠ 0）
  have hleft : Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid g 1 = (g 0).c := by
    have := Lattice.Lib.Compiler.IRWeightsBridge.encodeGrid_odd g 0
    simpa using this
  have hright : Lattice.Core.IR.compileSkel k 1 = 0 := by
    simp [Lattice.Core.IR.compileSkel]
  rw [hleft, hright] at h1
  exact hc h1

end Lattice.Lib.Compiler.GridRealAgreement