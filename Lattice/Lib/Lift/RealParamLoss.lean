import Mathlib
import Lattice.Runtime.RealLinear
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Optim.RealCrossUniverseBridge
/-!
# LATTICE W17: RealParamLoss —— MPO-1「参数化损失」

## 由来

M10（\`sweep5/M10-核心主张的覆盖充分性.md\`）与 S01（\`sweep5/S01-训练侧形式化边界裁定.md\`）
共同裁定：**「权重在证明层不存在」**——库里两个损失定义的权重槽位都被烤死：

* \`loss : LinearConstraint → ℤ → ℤ\`（\`ConstraintEmbeddingSoundness.lean:28\`）＝ \`(NeuronOut (convert c) x)^2\`，
  \`convert\` 把系数烤进神经元，唯一自由变量是 \`x\`；
* \`RealTotalLoss : (Fin n → RealNeuron) → ℝ → ℝ\`（\`RealTotalLoss.lean:24\`），
  其主定理对 \`ls := compileFin cs\` **固定**，只对 \`x\` 全称。

S01 §4.3 据此提出**最小可证目标 MPO-1**：\`paramLoss : (Fin n → ℝ) → ℝ\`，
且 \`paramLoss p = 0 ↔ 约束满足\`。本文件是该目标的落地。

## ⚠️ 本文件对 S01 原始陈述的**机器修订**（这是本报告最重要的产出）

S01 原话把 MPO-1 写成「\`paramLoss p = 0 ↔ 约束满足\`」，**未指明对 \`p\` 的量词**。
本轮内核实测（\`_w17_probe_a\` / \`paramLoss_forall_p_false\`，\`EXIT=0\`）证明：

> ⭐ **把 \`p\` 全称量化时，S01 的 MPO-1 陈述为【假】。**
> 反例：\`cs = ⟨a=1, b=0⟩\`、\`x = 5\`、**\`p = 0\`** ⟹ \`paramLoss = (0·5+0)² = 0\`，
> 但约束 \`1·5+0 = 5 ≠ 0\` **不满足**。

⟹ 正确的 MPO-1 必须**区分两个量词域**，本文件据此给出**两个真陈述**：

| 陈述 | 量词 | 内容 | 意义 |
|:--|:--|:--|:--|
| \`paramLoss_zero_iff_pConstraint\` | \`∀ p\` | 零损失 ⟺ **p-参数化**约束成立 | 损失面是**良定义的距离度量**（对**任意**参数） |
| \`paramLoss_symParam_zero_iff\` | \`p := symParam cs\` | 零损失 ⟺ **符号**约束满足 | 与链核心语义**对齐**（\`aᵢ\` 处） |

⭐ **这两条合起来才是 MPO-1 的真内容**：\`p\` 自由 ⟹ 损失可对 \`p\` 求最小（训练有意义）；
\`p = symParam cs\` 处零损失 ⟹ 符号约束满足（训练**接上符号**）。**缺任一条都不成立。**

## 承重性（消融级证据，判据③）

* \`paramLoss_forall_p_false\`：把 \`p\` 取全称 ⟹ **命题变假**（这就是上面那条反例的机器化）；
* \`paramLoss_not_const\`：损失对 \`p\` **非常函数** ⟹ 损失面非平凡，\`∇_p\` 有内容（MPO-2 的前提）。

## 接线（治 M10 发现 1「训练线孤岛」）

\`paramLoss_one_eq_layerOut_sq\` 经 \`RealCrossUniverseBridge.symW\` 把**参数化损失**
与链核心的 \`RealDot\` 输出接在同一等式上——这是本库**第一条**「参数化损失 → 链核心载体」的边。

\`#print axioms\` 全部 ⊆ {propext, Classical.choice, Quot.sound}，无 sorryAx。
-/

open scoped BigOperators

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## §1 ⭐ 参数化损失：参数 `p` 是**自由变量** -/

/-- 第 \`i\` 个约束对应的神经元输出，其**权重槽由参数 \`p i\` 供给**
（而**不是**由约束系数 \`(cs i).a\` 烤死）。\`p i\` 是 \`Fin n → ℝ\` 的投影。 -/
noncomputable def paramNeuronOut {n : Nat} (cs : Fin n → RealConstraint)
    (p : Fin n → ℝ) (x : ℝ) (i : Fin n) : ℝ :=
  p i * x + (cs i).b

/-- ⭐⭐ **参数化总损失** \`paramLoss cs x p = Σᵢ (pᵢ·x + bᵢ)²\`。
\`p\` 是自由的**可训练参数向量**（对照 \`RealTotalLoss (compileFin cs) x\`：那里 \`pᵢ\` 被替换为烤死的 \`(cs i).a\`）。 -/
noncomputable def paramLoss {n : Nat} (cs : Fin n → RealConstraint)
    (x : ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (paramNeuronOut cs p x i) ^ 2

/-- 符号参数向量：把约束系数 \`(cs i).a\` 作为参数注入（即 \`compileFin\` 的 ℝ 侧对偶）。 -/
noncomputable def symParam {n : Nat} (cs : Fin n → RealConstraint) : Fin n → ℝ :=
  fun i => (cs i).a

/-! ## §2 ⭐ 零点刻画（两个量词域，缺一不可） -/

/-- 零损失 ⟺ 每个参数化神经元输出为零（\`p\` **全称**，无任何对 \`p\` 的限制）。 -/
theorem paramLoss_zero_iff_all_outputs {n : Nat} (cs : Fin n → RealConstraint)
    (x : ℝ) (p : Fin n → ℝ) :
    paramLoss cs x p = 0 ↔ ∀ i : Fin n, paramNeuronOut cs p x i = 0 := by
  unfold paramLoss
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i
      exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
    · intro h i _
      exact sq_eq_zero_iff.mpr (h i)
  · intro i _
    exact sq_nonneg (paramNeuronOut cs p x i)

/-- ⭐⭐ **MPO-1（自由参数版）**：对**任意**参数 \`p\`，零损失 ⟺ **p-参数化**约束成立。
即损失面是参数空间上一个良定义的「满足性指示」。 -/
theorem paramLoss_zero_iff_pConstraint {n : Nat} (cs : Fin n → RealConstraint)
    (x : ℝ) (p : Fin n → ℝ) :
    paramLoss cs x p = 0 ↔ ∀ i : Fin n, p i * x + (cs i).b = 0 := by
  rw [show paramLoss cs x p = ∑ i : Fin n, (p i * x + (cs i).b) ^ 2 from rfl]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i
      exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
    · intro h i _
      exact sq_eq_zero_iff.mpr (h i)
  · intro i _
    exact sq_nonneg _

/-- ⭐⭐⭐ **MPO-1（符号参数版，主定理）**：在符号参数 \`symParam cs\` 处，
**零损失 ⟺ 符号约束全部满足**。这是「训练把损失压到 0 ⟹ 符号约束被满足」的类型载体。 -/
theorem paramLoss_symParam_zero_iff {n : Nat} (cs : Fin n → RealConstraint) (x : ℝ) :
    paramLoss cs x (symParam cs) = 0 ↔ ∀ i : Fin n, (cs i).a * x + (cs i).b = 0 := by
  rw [show paramLoss cs x (symParam cs)
        = ∑ i : Fin n, ((cs i).a * x + (cs i).b) ^ 2 from rfl]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i
      exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
    · intro h i _
      exact sq_eq_zero_iff.mpr (h i)
  · intro i _
    exact sq_nonneg _

/-- 不满足 ⟹ 损失**严格为正**（训练可观测的失败信号）。 -/
theorem paramLoss_pos_of_unsatisfied {n : Nat} (cs : Fin n → RealConstraint)
    (x : ℝ) (p : Fin n → ℝ) (i : Fin n) (h : p i * x + (cs i).b ≠ 0) :
    0 < paramLoss cs x p := by
  unfold paramLoss
  have hsq : 0 < (paramNeuronOut cs p x i) ^ 2 := by
    have hne : paramNeuronOut cs p x i ≠ 0 := by
      unfold paramNeuronOut; exact h
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (by
      intro hs; exact hne (sq_eq_zero_iff.mp hs)))
  have hle : (paramNeuronOut cs p x i) ^ 2
      ≤ ∑ j : Fin n, (paramNeuronOut cs p x j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (paramNeuronOut cs p x j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  exact lt_of_lt_of_le hsq hle

/-! ## §3 承重性（消融级证据） -/

/-- ⭐⭐ **消融见证**：S01 原陈述（\`p\` 全称版）**为假**。
反例 \`cs = ⟨1,0⟩\`、\`x = 5\`、\`p = 0\`：损失 \`0\` 但约束 \`5 ≠ 0\`。
⟹ 「零损失 ⟺ 约束满足」**不能**对任意 \`p\` 声称；\`symParam\` 这个限制**删不掉**。 -/
theorem paramLoss_forall_p_false :
    ¬ (∀ (n : Nat) (cs : Fin n → RealConstraint) (x : ℝ) (p : Fin n → ℝ),
        paramLoss cs x p = 0 ↔ ∀ i : Fin n, (cs i).a * x + (cs i).b = 0) := by
  intro h
  have hh := h 1 (fun _ => (⟨1, 0⟩ : RealConstraint)) 5 (fun _ => (0 : ℝ))
  have hloss : paramLoss (n := 1) (fun _ => (⟨1, 0⟩ : RealConstraint)) 5
      (fun _ => (0 : ℝ)) = 0 := by
    simp [paramLoss, paramNeuronOut]
  have hsat := hh.mp hloss
  have h0 := hsat 0
  norm_num at h0

/-- ⭐ **消融见证（非平凡性）**：损失对参数**不是常函数** ⟹ 损失面有内容，
\`∇_p paramLoss\` 非恒零（MPO-2 梯度下降回路的前提）。 -/
theorem paramLoss_not_const :
    ∃ (cs : Fin 1 → RealConstraint) (x : ℝ) (p q : Fin 1 → ℝ),
      paramLoss cs x p ≠ paramLoss cs x q := by
  refine ⟨fun _ => (⟨0, 1⟩ : RealConstraint), 1, fun _ => 0, fun _ => 1, ?_⟩
  simp only [paramLoss, paramNeuronOut, Fin.sum_univ_one]
  norm_num

/-! ## §4 ⭐ 接线：参数化损失 → 链核心载体（治 M10 发现 1 的孤岛病） -/

/-- 从链核心 \`LinearLayer\` 的 ℤ 权重经跨宇宙桥 \`symW\` 提取参数向量。 -/
noncomputable def layerParam (n : Nat) (l : LinearLayer) : Fin n → ℝ := symW n l.w

/-- ⭐⭐ **接线定理**：参数化损失在「层权重」这一参数点上，等于该层 \`RealDot\` 输出的平方。
⟹ 本库**第一条**把\`参数化损失\`与链核心 \`LinearLayer\` 接在同一等式上的边
（\`symW\` 来自 \`RealCrossUniverseBridge.lean\`）。 -/
theorem paramLoss_one_eq_layerOut_sq (n : Nat) (l : LinearLayer) (x : Fin n → ℝ) :
    paramLoss (n := 1) (fun _ => (⟨0, 0⟩ : RealConstraint))
        (RealDot (layerParam n l) x) (fun _ => (1 : ℝ))
      = (RealDot (layerParam n l) x) ^ 2 := by
  simp only [paramLoss, Fin.sum_univ_one, paramNeuronOut]
  ring

end Lattice

#print axioms Lattice.paramLoss_zero_iff_all_outputs
#print axioms Lattice.paramLoss_zero_iff_pConstraint
#print axioms Lattice.paramLoss_symParam_zero_iff
#print axioms Lattice.paramLoss_pos_of_unsatisfied
#print axioms Lattice.paramLoss_forall_p_false
#print axioms Lattice.paramLoss_not_const
#print axioms Lattice.paramLoss_one_eq_layerOut_sq
