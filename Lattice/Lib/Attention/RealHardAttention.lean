import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: 注意力硬路由语义 —— argmax 判定与 softmax 保序

transformer 调研（research/real-world/transformer-semantics.md）的硬注意力：
推理加速用硬路由（argmax 选中最相似 key 的 value）——符号语义：

  1. argmax 定义：IsArgMax s i := ∀j, sⱼ ≤ sᵢ（i 是最大分数）；
  2. 唯一性：分数严格不同（∀j≠i, sⱼ < sᵢ）⟹ argmax 唯一（确定性路由）；
  3. 硬输出：路由到 value vᵢ（被选中 value 直接输出）；
  4. softmax 保序：sⱼ ≤ sᵢ ⟹ softmax(s)ⱼ ≤ softmax(s)ᵢ
     ——硬路由与软注意力的选择一致（软是硬的平滑版）。

模型无关：任意分数函数、任意 value。
-/


namespace Lattice

variable {ι F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## argmax（分数最大者的判定） -/

def IsArgMax (s : ι → ℝ) (i : ι) : Prop :=
  ∀ j : ι, s j ≤ s i

/-! ## 定理一：argmax 唯一性（分数严格不同时）
(∀j≠i, sⱼ < sᵢ) ⟹ argmax 唯一（确定性路由）。-/

omit [Fintype ι] [Nonempty ι] in
theorem argmax_unique (s : ι → ℝ) (i : ι) (hstrict : ∀ j : ι, j ≠ i → s j < s i) :
    ∀ j : ι, IsArgMax s j → j = i := by
  intro j hj
  by_contra hji
  -- j ≠ i：sⱼ < sᵢ（严格）；但 IsArgMax s j 给 sᵢ ≤ sⱼ——矛盾
  have hlt : s j < s i := hstrict j hji
  have hge : s i ≤ s j := hj i
  linarith

/-! ## 定理二：argmax 值是被选中的最大分数
IsArgMax s i 且 j ≠ i ⟹ sⱼ ≤ sᵢ（最大值性质，直接来自定义）。-/

omit [Fintype ι] [Nonempty ι] in
theorem argmax_is_max (s : ι → ℝ) (i j : ι) (hi : IsArgMax s i) (_hji : j ≠ i) :
    s j ≤ s i := hi j

/-! ## 硬注意力输出（路由到被选中的 value）
路由语义：分数 argmax 决定 value 选择，输出 = vᵢ（确定性）。 -/

def hardAttentionOutput (s : ι → ℝ) (v : ι → F) (i : ι) (hi : IsArgMax s i) : F :=
  v i

/-! ## 定理三：硬输出被最大 value 界住（衔接凸组合界）
硬注意力输出（单个 value）≤ 凸组合界（软注意力的退化情形）。-/

omit [Fintype ι] [Nonempty ι] [NormedSpace ℝ F] in
theorem hard_output_norm_bound (s : ι → ℝ) (v : ι → F) (i : ι) (hi : IsArgMax s i)
    (M : ℝ) (hV : ∀ j, ‖v j‖ ≤ M) :
    ‖hardAttentionOutput s v i hi‖ ≤ M := by
  unfold hardAttentionOutput
  exact hV i

/-! ## 定理四：softmax 保序
sⱼ ≤ sᵢ ⟹ softmax(s)ⱼ ≤ softmax(s)ᵢ（exp 单调 + 公共正分母）。
硬路由与软注意力的选择一致（软是硬的平滑版）。-/

theorem softmax_monotone (s : ι → ℝ) (i j : ι) (h : s j ≤ s i) :
    softmax s j ≤ softmax s i := by
  unfold softmax
  -- exp(sⱼ)/S ≤ exp(sᵢ)/S：exp 单调 + 公共正分母
  have he : Real.exp (s j) ≤ Real.exp (s i) := Real.exp_le_exp.mpr h
  have hS : 0 < ∑ k, Real.exp (s k) := softmax_denom_pos s
  exact div_le_div_of_nonneg_right he (le_of_lt hS)

/-! ## 定理五：argmax 处的 softmax 权重最大（路由一致）
若 i 是 argmax，则 softmax 在 i 处取得最大权重（硬路由与软注意一致）。-/

theorem argmax_softmax_weight_max (s : ι → ℝ) (i : ι) (hi : IsArgMax s i) :
    ∀ j : ι, softmax s j ≤ softmax s i := by
  intro j
  exact softmax_monotone s i j (hi j)

end Lattice
