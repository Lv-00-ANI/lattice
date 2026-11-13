import Mathlib
import Lattice.Runtime.CICToConstraintSet
import Lattice.Runtime.DataToConstraint
import Lattice.Runtime.AcceptanceLayer

/-!
# 端到端：`数据 → CIC → ConstraintSet → Layer` 的**单一陈述**（阶段 C，P4 收口）

## 为什么还要一个文件

**前几轮分别建立了四段：**

| 段 | 文件 | 内容 |
|:--|:--|:--|
| **数据 → CIC** | **`DataToConstraint.lean`** | **`corpusConstraints : List Sample → CICCtx`** |
| **CIC → ConstraintSet** | **`CICToConstraintSet.lean`** | **`cicCtxToConstraintSet : CICCtx → List VectorConstraint`** |
| **CIC → 权重** | **`CICToConstraintSet.lean`** | **`cic_loop_reaches_weight`** |
| **判定对齐** | **`AcceptanceLayer.lean`** | **`acceptanceLayer_zero_iff`** |

**=> 但没有一条定理同时提到**数据的覆盖条件**与**权重层的输出**。
读代码的人必须自己把四段接起来 —— 而「读者自己接」正是这条链最容易断的地方。**

**本文件提供那条单一陈述，并把**复合**本身写成定理。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| `corpusToConstraintSet` | **⭐ 复合定义：`样本列表 → 约束列表`，一步到位** |
| `corpusToLayer` | **⭐ 复合定义：`样本列表 → 权重层`，一步到位** |
| `corpusToConstraintSet_eq_comp` | **复合等于两段的依次应用（可展开）** |
| **`data_to_weight_iff`** | **⭐⭐ 数据的约束全部成立 ⟺ 权重层输出全部为零** |
| `data_to_weight_honest` | **覆盖率在零宽度假设下推到这个等价** |

**=> `data_to_weight_iff` 是**端到端的单一陈述**：
左边是数据侧的逐样本判定，右边是权重侧的零化条件，中间的三跳由复合定义一次性穿过。**

**它**不**声称「数据总是导出零输出」（第 895 轮已否证那是假的）；
它声称**两侧的判定是同一个判定** —— 那正是验证回路所需要的。** -/

namespace Lattice.Runtime.CICBridge

open Lattice.Core.CIC
open Lattice.Data
open Lattice.Data.Encode
open Lattice.Lift.SymbolToWeightCorrectness

/-- **⭐ 复合一：样本列表 → 约束列表。一步穿过「数据 → CIC → 约束」。** -/
def corpusToConstraintSet (c : List Sample) : List VectorConstraint :=
  cicCtxToConstraintSet (corpusConstraints c)

/-- **⭐ 复合二：样本列表 → 权重层。一步穿过「数据 → CIC → 约束 → 权重」。** -/
def corpusToLayer (c : List Sample) : Layer :=
  compileToLayer (corpusToConstraintSet c)

/-- **复合可展开：`corpusToConstraintSet` 就是两段的依次应用。**

**=> 这条使复合**不是一个黑箱**：任何关于它的断言都能立即回到两个具名定义上。** -/
theorem corpusToConstraintSet_eq_comp (c : List Sample) :
    corpusToConstraintSet c = cicCtxToConstraintSet (corpusConstraints c) := rfl

/-- **⭐ 复合可展开：`corpusToLayer` 就是三段复合。** -/
theorem corpusToLayer_eq_comp (c : List Sample) :
    corpusToLayer c = compileToLayer (cicCtxToConstraintSet (corpusConstraints c)) := rfl

/-- **⭐⭐ 端到端的单一陈述：数据的约束全部成立 ⟺ 权重层输出全部为零。**

**=> 左端：`∀ v ∈ corpusToConstraintSet c, VectorConstraintSat v x`（数据/符号侧判定）。
右端：`AllZeroOutputs (corpusToLayer c) x`（权重侧零化）。**

**=> 证明只用 `cic_loop_reaches_weight` 与两个复合定义的展开 ——
**内容不在证明里，在这条链被写成一条定理里**。** -/
theorem data_to_weight_iff (c : List Sample) (x : List Int) :
    (∀ v ∈ corpusToConstraintSet c, VectorConstraintSat v x) ↔
      AllZeroOutputs (corpusToLayer c) x := by
  unfold corpusToConstraintSet corpusToLayer
  have h1 : (∀ v ∈ cicCtxToConstraintSet (corpusConstraints c), VectorConstraintSat v x)
      ↔ (∀ t ∈ corpusConstraints c, ∀ v, cicToConstraint t = some v → VectorConstraintSat v x) :=
    cicCtxToConstraintSet_sat_iff (corpusConstraints c) x
  have h2 : (∀ t ∈ corpusConstraints c, ∀ v, cicToConstraint t = some v → VectorConstraintSat v x)
      ↔ AllZeroOutputs (compileToLayer (cicCtxToConstraintSet (corpusConstraints c))) x :=
    cic_loop_reaches_weight (corpusConstraints c) x
  exact h1.trans h2

/-- **诚实形式：零宽度假设下，覆盖率一路推到权重侧。**

**=> `CoversCorpus K c` **加上**「所有宽度为零」，给出 `corpusToLayer c` 对任何输入输出全零。**

**=> 这是第 895 轮那条被否证的论断的**正确形式**：那个否证说明**缺的不是桥，是一个前提**。** -/
theorem data_to_weight_honest (K : ConstSet) (c : List Sample) (x : List Int)
    (h : CoversCorpus K c) (hzero : ∀ s ∈ c, Sample.width s = 0) :
    AllZeroOutputs (corpusToLayer c) x := by
  unfold corpusToLayer corpusToConstraintSet
  rw [← cic_loop_reaches_weight]
  intro t ht v hv
  unfold corpusConstraints at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  simp only [cicToConstraint] at hv
  injection hv with hveq
  rw [← hveq, hzero s hs]
  simp [VectorConstraintSat, dot]

end Lattice.Runtime.CICBridge
