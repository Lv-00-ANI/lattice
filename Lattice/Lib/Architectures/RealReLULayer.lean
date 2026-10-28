import Mathlib
import Lattice.Runtime.RealLinear
import Lattice.Lift.RealNonlinear
import Lattice.Lib.Architectures.RealLayerPropagation
/-!
# LATTICE: ReLU 层组合传播 —— 非线性层的约束流

把 RealNonlinear（ReLU 编码约束）接入 RealLayerPropagation（层间传播）：
  1. ReLU 层：输出 = relu(线性层输出)，**恒非负**（关键性质）；
  2. 零向量输入：ReLU 层输出 = relu(偏置)（区别于线性层的 = 偏置）；
  3. 约束满足传播（ReLU 版）：第一层约束全满足 → ReLU 层收到零向量
     → 输出 = relu(偏置)；
  4. 非负输出批量判定：Σ ReLU 输出 = 0 ⟺ 各项为零（复用非负和零）。

这给出**带非线性激活的多层网络**的约束传播语义。
-/


namespace Lattice

/-! RealLinear/RealNonlinear/RealLayerPropagation 的内容同在 Lattice 命名空间，无需 open。
注：RealLayerOut/RealVectorSat 需要 [Fintype ι]，此处为缺失的类型类约束补全（最小修正）。-/

/-! ## ReLU 层：线性层输出经 ReLU 激活 -/

def ReLULayerOut {ι : Type} [Fintype ι] (l : RealLinearLayer ι) (x : ι → ℝ) : ℝ :=
  relu (RealLayerOut l x)

/-! ## 定理一：ReLU 层输出恒非负（relu 的关键性质） -/

theorem reluLayer_out_nonneg {ι : Type} [Fintype ι] (l : RealLinearLayer ι) (x : ι → ℝ) :
    0 ≤ ReLULayerOut l x := by
  unfold ReLULayerOut
  exact relu_nonneg _

/-! ## 定理二：ReLU 层收到零向量输出 relu(偏置)
区别于线性层（= 偏置）：ReLU 把负偏置截断为零。 -/

theorem reluLayer_zero_input {ι : Type} [Fintype ι] (l : RealLinearLayer ι) :
    ReLULayerOut l (fun _ => 0) = relu l.b := by
  unfold ReLULayerOut
  rw [realLayerOut_zero_input]

/-! ## 定理三：约束满足的层间传播（ReLU 版）
第一层约束全部满足 → ReLU 层收到零向量 → 输出 = relu(偏置)。-/

theorem relu_propagation {ι : Type} [Fintype ι] (cs : ι → RealVectorConstraint ι) (x : ι → ℝ)
    (l2 : RealLinearLayer ι) (h : ∀ i, RealVectorSat (cs i) x) :
    ReLULayerOut l2 (fun i => RealLayerOut (compileRealVecSeq cs i) x) = relu l2.b := by
  -- 第一层输出零函数
  have hzero : ∀ i, RealLayerOut (compileRealVecSeq cs i) x = 0 :=
    (realLayer_allSatisfied_iff_zero_output cs x).mp h
  have hinput : (fun i => RealLayerOut (compileRealVecSeq cs i) x) = fun _ => 0 := by
    funext i
    exact hzero i
  rw [hinput]
  exact reluLayer_zero_input l2

/-! ## ReLU 层输出和（Fin 索引） -/

def ReLUSum {ι : Type} [Fintype ι] {n : Nat} (ls : Fin n → RealLinearLayer ι) (x : ι → ℝ) : ℝ :=
  ∑ i : Fin n, ReLULayerOut (ls i) x

/-! ## 定理四：ReLU 输出和为零 ⟺ 各项为零
（各输出非负 → Mathlib sum_eq_zero_iff_of_nonneg）。-/

theorem ReLUSum_zero_iff_all {ι : Type} [Fintype ι] {n : Nat} (ls : Fin n → RealLinearLayer ι)
    (x : ι → ℝ) :
    ReLUSum ls x = 0 ↔ ∀ i : Fin n, ReLULayerOut (ls i) x = 0 := by
  unfold ReLUSum
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · intro i hi
    exact reluLayer_out_nonneg (ls i) x

/-! ## 定理五：ReLU 层批量约束判定
多个约束编译的 ReLU 层，输出和为零 ⟺ 全部 ReLU 层输出为零
（结合 relu_preserves 后即"全部不等式满足"）。-/

theorem ReLUSum_iff_all_constraints {ι : Type} [Fintype ι] {n : Nat}
    (as bs : Fin n → ℝ) (x : ι → ℝ) (ls : Fin n → RealLinearLayer ι)
    (hcompile : ∀ i, RealLayerOut (ls i) x =
      RealNeuronOut (convertReal { a := as i, b := bs i }) (RealLayerOut (ls i) x)) :
    ReLUSum ls x = 0 ↔
      ∀ i : Fin n, RealNeuronOut (convertReal { a := as i, b := bs i }) (RealLayerOut (ls i) x) ≤ 0 := by
  rw [ReLUSum_zero_iff_all]
  constructor
  · intro h i
    -- ReLU 输出零 ⟺ 内部线性输出 ≤ 0（relu_eq_zero_iff）
    have hz : relu (RealLayerOut (ls i) x) = 0 := by
      simpa [ReLULayerOut] using h i
    have : RealLayerOut (ls i) x ≤ 0 := (relu_eq_zero_iff _).mp hz
    rw [hcompile i] at this
    exact this
  · intro h i
    -- 内部线性输出 ≤ 0 ⟺ relu 输出零
    have hle : RealLayerOut (ls i) x ≤ 0 := by
      rw [hcompile i]
      exact h i
    have : relu (RealLayerOut (ls i) x) = 0 := (relu_eq_zero_iff _).mpr hle
    simpa [ReLULayerOut] using this

end Lattice
