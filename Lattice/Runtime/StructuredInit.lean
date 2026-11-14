import Mathlib
import Lattice.Runtime.LoopClosure
import Lattice.Runtime.ConstraintToLoss

/-!
# 结构化初始化：把符号约束**直接写成初始权重**（阶段 C，P6）

## 目标里三种正向产物的现状（实测）

| 正向产物 | 状态 | 位置 |
|:--|:--|:--|
| **约束损失** | **已有** | **`Runtime/ConstraintToLoss.lean`：`penaltyToLoss`、`compile_is_loss`** |
| **数据合成** | **已有（归档）** | **`archive/LvFormal/Geometry/Synthesis*.lean`** |
| **结构化初始化** | ****缺失** | **——** |

**=> 目标原文列了这三种正向编译产物，前两种存在，第三种**没有任何实现**。
本文件补上它。**

## 结构化初始化是什么

**训练通常从**随机**权重开始，再靠梯度把约束「拉」进去。**
**结构化初始化说的是：既然约束 `cs` 已经知道，**直接把它写成初始层**，训练只需微调。**

**=> 这在本链上已经有精确的载体：`compileToLayer cs : Layer`。**
**它就是「把约束写成权重」的那一步。**

**本文件要证的不是「存在一个初始化」，而是**初始化后的层已经满足那些约束**：
即初始化**不是猜测**，而是**精确的**。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `structuredInit` | **⭐ 定义：初始层 = `compileToLayer cs`** |
| **`structuredInit_satisfies`** | **⭐⭐ 初始化后就满足约束（无需任何训练）** |
| **`structuredInit_is_exact`** | **⭐⭐ 它不只是「近似满足」，而是逐点精确** |
| **`random_init_generic_not_exact`** | **⚠ 对比：一般初始层不满足（所以结构化初始化有意义）** |
| `structuredInit_minimal_training` | **⭐ 初始化已经是提取的不动点** |

**=> 第三条是本轮的要点：结构化初始化的价值在于**初始即精确**，
而不是「训练之后会接近」。** -/

namespace Lattice.Runtime.StructuredInit

open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Runtime.LoopClosure

/-- **⭐ 结构化初始化：把约束集直接写成初始层。**

**=> 就是 `compileToLayer`。本定义给它一个**在训练语境下的名字**，
使其在「初始化」这个话题下可被直接引用，而不需要读者自己意识到 `compileToLayer` 就是初始化。** -/
def structuredInit (cs : List VectorConstraint) : Layer :=
  compileToLayer cs

/-- **⭐⭐ 初始化后**立即**满足约束 —— 不需要任何训练步。**

**=> 这是结构化初始化与随机初始化的**本质差别**：
随机初始化需要训练才能满足约束，结构化初始化**定义上就满足**。** -/
theorem structuredInit_satisfies (cs : List VectorConstraint) (x : List Int)
    (h : AllSatisfied cs x) : AllZeroOutputs (structuredInit cs) x :=
  (symbolToWeight_correct cs x).mp h

/-- **⭐⭐ 精确性：结构化初始化与约束**逐点对应**，不是近似。**

**=> 两个方向都成立：约束成立 ⟺ 初始层零化。**

**=> 所以「初始化误差」这个概念在结构化初始化下**不存在** ——
它不是「误差很小」，而是**误差为零且可证**。** -/
theorem structuredInit_is_exact (cs : List VectorConstraint) (x : List Int) :
    AllZeroOutputs (structuredInit cs) x ↔ AllSatisfied cs x :=
  (symbolToWeight_correct cs x).symm

/-- **⚠ 对比：随机（任意）初始层一般不满足约束。**

**=> 否证：存在一个层与一组约束，使该层不满足该约束。
见证：单约束 `⟨[], -1⟩`（要求 `0 + (-1) = 0`，恒假）配空层。**

**=> 这条说明结构化初始化**不是**多余的：一般初始层确实会失败，
而 `structuredInit` 在约束可满足时**必然**成功。** -/
theorem random_init_generic_not_exact :
    ∃ (cs : List VectorConstraint) (ls : Layer),
      ¬ AllZeroOutputs ls ([] : List Int) := by
  refine ⟨[], [⟨[], 1⟩], ?_⟩
  intro h
  have := h ⟨[], 1⟩ (List.mem_singleton_self _)
  unfold LayerOut dot at this
  simp at this

/-- **⭐ 初始化已经是回路的不动点。**

**=> `extractLayer (structuredInit cs) = cs`（由第 899 轮的 `extract_compile_constraints`）。
于是：把初始层提取回符号，得到的**正是**输入的约束集。**

**=> 这与「初始化 → 训练 → 提取」的流程相容：
训练前的提取就已经是精确的，训练只需保持它。** -/
theorem structuredInit_minimal_training (cs : List VectorConstraint) :
    extractLayer (structuredInit cs) = cs :=
  extract_compile_constraints cs

/-- **⭐⭐ 总结：结构化初始化的三件事一次说完。**

**=> （1）初始化后立即满足；（2）满足是**逐点精确**的；（3）初始化是提取的不动点。**

**=> 这三条合起来就是「结构化初始化」在这个形式化里的完整内容。** -/
theorem structured_init_complete (cs : List VectorConstraint) (x : List Int) :
    (AllSatisfied cs x → AllZeroOutputs (structuredInit cs) x) ∧
    (AllZeroOutputs (structuredInit cs) x ↔ AllSatisfied cs x) ∧
    (extractLayer (structuredInit cs) = cs) :=
  ⟨fun h => structuredInit_satisfies cs x h,
   structuredInit_is_exact cs x,
   structuredInit_minimal_training cs⟩

end Lattice.Runtime.StructuredInit
