import Mathlib

/-!
# LATTICE: 注意力结构 —— 凸组合范数界与 √d 缩放（模型无关）

transformer 调研（research/real-world/transformer-semantics.md 的 MHA）核心性质：

  1. 注意力输出是 value 的**凸组合**（权重 = softmax 行，概率分布）：
     ‖Σᵢ wᵢ·Vᵢ‖ ≤ maxᵢ‖Vᵢ‖   （输出范数被最大 value 界住——残差稳定性）
  2. √d 缩放：|⟨q,k⟩/√d| ≤ ‖q‖·‖k‖/√d（Cauchy-Schwarz + 缩放）
  3. softmax 行随机：softmax(z)ᵢ ≥ 0 且 Σᵢ softmax(z)ᵢ = 1（概率分布）

模型无关：任意维度、任意 value 向量、任意 logits。
-/

noncomputable section

namespace Lattice

variable {ι F : Type*}
  [Fintype ι]
  [Nonempty ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 概率分布抽象 -/

def ProbDist (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1)

/-! ## 凸组合 -/

def convComb (w : ι → ℝ) (V : ι → F) : F :=
  ∑ i, w i • V i

/-! ## 定理一：凸组合范数界（注意力输出有界）
w 是概率分布且 ∀i ‖Vᵢ‖ ≤ M ⟹ ‖Σ wᵢ·Vᵢ‖ ≤ M。-/

omit [Nonempty ι] in
theorem convComb_norm_bound (w : ι → ℝ) (V : ι → F) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖convComb w V‖ ≤ M := by
  unfold convComb
  calc
    ‖∑ i, w i • V i‖ ≤ ∑ i, ‖w i • V i‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖V i‖ := by
      -- ‖wᵢ•Vᵢ‖ = wᵢ·‖Vᵢ‖（wᵢ ≥ 0）
      apply Finset.sum_congr rfl
      intro i hi
      have hw : |w i| = w i := abs_of_nonneg (hw0 i)
      rw [norm_smul, Real.norm_eq_abs, hw]
    _ ≤ ∑ i, w i * M := by
      -- 每项 ≤（wᵢ ≥ 0）
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hV i) (hw0 i)
    _ = M * (∑ i, w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = M := by
      rw [hsum]
      ring

/-! ## 定理二：√d 缩放有界（Cauchy-Schwarz）
|⟨q, k⟩ / √d| ≤ ‖q‖·‖k‖ / √d（q、k 内积空间元素，d > 0）。-/

theorem sqrt_d_scale_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (q k : E) (d : ℝ) (hd : 0 < d) :
    |inner q k / Real.sqrt d| ≤ ‖q‖ * ‖k‖ / Real.sqrt d := by
  -- |a/b| = |a|/|b|；|⟨q,k⟩| ≤ ‖q‖‖k‖（C-S）
  have hcs : |inner q k| ≤ ‖q‖ * ‖k‖ := by
    simpa [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) q k)
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hd' : Real.sqrt d ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr hd
  calc
    |inner q k / Real.sqrt d| = |inner q k| / |Real.sqrt d| := abs_div _ _
    _ = |inner q k| / Real.sqrt d := by
      rw [abs_of_nonneg hsq]
    _ ≤ (‖q‖ * ‖k‖) / Real.sqrt d := by
      exact div_le_div_of_nonneg_right hcs hsq

/-! ## softmax（行随机：非负 + 和 1） -/

def softmax (z : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (z i) / ∑ j, Real.exp (z j)

/-! ## 引理：softmax 分母为正（非空指标）
Σ exp(zⱼ) > 0（每项正且指标非空）。-/

lemma softmax_denom_pos (z : ι → ℝ) : 0 < ∑ j, Real.exp (z j) := by
  exact Finset.sum_pos (fun j hj => Real.exp_pos _) Finset.univ_nonempty

/-! ## 定理三：softmax 非负
softmax(z)ᵢ ≥ 0。-/

theorem softmax_nonneg (z : ι → ℝ) : ∀ i, 0 ≤ softmax z i := by
  intro i
  unfold softmax
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (softmax_denom_pos z))

/-! ## 定理四：softmax 行随机（和为 1）
Σᵢ softmax(z)ᵢ = 1（概率分布）。-/

theorem softmax_sum_one (z : ι → ℝ) : ∑ i, softmax z i = 1 := by
  unfold softmax
  -- Σ (exp_i / S) = (Σ exp_i) / S = S / S = 1
  have hS : ∑ j, Real.exp (z j) ≠ 0 := ne_of_gt (softmax_denom_pos z)
  calc
    ∑ i, Real.exp (z i) / ∑ j, Real.exp (z j) = (∑ i, Real.exp (z i)) / ∑ j, Real.exp (z j) := by
      rw [← Finset.sum_div]
    _ = 1 := by
      field_simp [hS]

/-! ## 定理五：注意力输出范数有界（softmax 是概率分布 ⟹ 凸组合界）
把 softmax 与凸组合界连接：注意力输出被最大 value 界住。-/

theorem attention_output_bound (z : ι → ℝ) (V : ι → F) (M : ℝ)
    (hV : ∀ i, ‖V i‖ ≤ M) :
    ‖convComb (softmax z) V‖ ≤ M := by
  exact convComb_norm_bound (softmax z) V M (softmax_nonneg z) (softmax_sum_one z) hV

end Lattice
