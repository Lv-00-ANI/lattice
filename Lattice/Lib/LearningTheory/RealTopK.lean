import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: top-k 稀疏路由 —— 子集凸组合界与 argmax 衔接

稀疏注意力/MoE 的路由：分数前 k 的 value 加权输出（稀疏路由）。

  1. 子集凸组合界：选择集 S（权重 w 在 S 上是概率分布）⟹
     ‖Σ_{i∈S} wᵢ·vᵢ‖ ≤ max‖vⱼ‖（凸组合界在子集上——全注意力的推广）；
  2. k=1 衔接：S = {i*}（单元素）⟹ 输出 = vᵢ*（硬注意力/argmax 路由）；
  3. k=n 衔接：S = 全集 ⟹ 全注意力（凸组合界退化）。

模型无关：任意分数/值向量、任意选择集。
-/


noncomputable section

namespace Lattice

variable {ι F : Type*}
  [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定理一：子集凸组合范数界
w 在选择集 S 上是概率分布且 value 有界 ⟹ 稀疏输出 ≤ max‖v‖。-/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem topk_output_bound (S : Finset ι) (w : ι → ℝ) (v : ι → F) (M : ℝ)
    (hw0 : ∀ i, i ∈ S → 0 ≤ w i) (hsum : ∑ i in S, w i = 1)
    (hV : ∀ i, ‖v i‖ ≤ M) :
    ‖∑ i in S, w i • v i‖ ≤ M := by
  calc
    ‖∑ i in S, w i • v i‖ ≤ ∑ i in S, ‖w i • v i‖ := norm_sum_le _ _
    _ = ∑ i in S, w i * ‖v i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hw : ‖w i‖ = w i := by
        rw [Real.norm_eq_abs]
        exact abs_of_nonneg (hw0 i hi)
      rw [norm_smul, hw]
    _ ≤ ∑ i in S, w i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hV i) (hw0 i hi)
    _ = M * (∑ i in S, w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = M := by
      rw [hsum]
      ring

/-! ## 定理二：k=1 衔接（硬路由/argmax）
S = {i}（单元素选择）⟹ 输出 = vᵢ（硬注意力退化）。-/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem top1_output_is_hard (i : ι) (v : ι → F) (w : ι → ℝ)
    (hw : w i = 1) (_hrest : ∀ j, j ≠ i → w j = 0) :
    ∑ j in ({i} : Finset ι), w j • v j = v i := by
  -- 单点求和
  simp [hw]

/-! ## 定理三：k=1 输出被界住（衔接凸组合界）
单点选择的输出 = vᵢ ≤ max‖v‖（硬路由有界）。-/

omit [Fintype ι] [Nonempty ι] [NormedSpace ℝ F] in
theorem top1_output_bound (i : ι) (v : ι → F) (M : ℝ) (hV : ∀ j, ‖v j‖ ≤ M) :
    ‖∑ j in ({i} : Finset ι), (if j = i then 1 else 0) • v j‖ ≤ M := by
  -- one-hot 选择：权重 = if j=i then 1 else 0，和 = v_i
  calc
    ‖∑ j in ({i} : Finset ι), (if j = i then 1 else 0) • v j‖ = ‖v i‖ := by
      -- 单点求和 + if 化简
      simp
    _ ≤ M := hV i

/-! ## 定理四：top-k 是凸组合（良定）
选择权重在 S 上非负且和 1（稀疏路由的良定前提——由 softmax 在 S 上
归一化给出，衔接 softmax 行随机）。-/

omit [DecidableEq ι] in
theorem topk_weights_prob (z : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) :
    (∀ i, i ∈ S → 0 ≤ softmax z i) ∧
    (∑ i in S, softmax z i / ∑ j in S, softmax z j = 1) := by
  constructor
  · -- softmax 非负（全空间非负 ⟹ 子集非负）
    intro i hi
    exact softmax_nonneg z i
  · -- 归一化：Σ(sᵢ/S) = S/S = 1（softmax 分母为正 ⟹ S 上每项正）
    have hpos : ∀ j, 0 < softmax z j := by
      intro j
      unfold softmax
      exact div_pos (Real.exp_pos _) (softmax_denom_pos z)
    have hSpos : 0 < ∑ j in S, softmax z j := by
      exact Finset.sum_pos (fun j hj => hpos j) hS
    calc
      ∑ i in S, softmax z i / ∑ j in S, softmax z j
          = (∑ i in S, softmax z i) / ∑ j in S, softmax z j := by
            rw [← Finset.sum_div]
      _ = 1 := by
            -- A/D = D/D = 1（分子分母同一求和，仅绑定名不同）
            have hA : (∑ i in S, softmax z i) = (∑ j in S, softmax z j) := rfl
            rw [hA]
            exact div_self (ne_of_gt hSpos)

end Lattice
