import Mathlib
import Lattice.Runtime.RealNonlinear
/-!
# LATTICE: ReLU 梯度与驻点 —— P2a 正面 + P2b 反例

调研（research/embedding/README.md §4）的 P2 命题：
「ReLU 可分系统的梯度零化 ⟹ 满足」——**本文件证明其不可证（P2b 反例）**，
并给出可证的 P2a 正面（relu 单边平方损失的不满足区非驻点）。

  1. P2a（正面）：relu(x-a)² 在"不满足区"（x > a）导数严格非零——不满足 ⟹ 非驻点；
  2. P2b（反例）：L(x) = relu(x) + relu(1-x) 在 (0,1) 内是常数 1（导数 0），
     但 relu 编码的约束（x ≤ 0 且 1-x ≤ 0）不满足——**虚假驻点**。

结论：ReLU 平方损失（单约束）驻点 ⟺ 满足成立；ReLU 线性损失（约束和）
存在虚假驻点——可微化选型须用平方而非线性 relu 项（或验证器兜底）。

纯 ℝ（Mathlib 微分）。
-/


noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! ## relu 的局部恒等/零化 -/

lemma relu_eq_self_of_nonneg (x : ℝ) (h : 0 ≤ x) : relu x = x := by
  unfold relu
  exact max_eq_left h

lemma relu_eq_zero_of_nonpos (x : ℝ) (h : x ≤ 0) : relu x = 0 := by
  unfold relu
  exact max_eq_right h

/-! ## P2a：relu 单边平方损失的不满足区非驻点
x > a ⟹ deriv (fun y => relu(y-a)²) x = 2(x-a) ≠ 0。
（x > a 邻域内 relu(y-a) = y-a，损失局部 = (y-a)²。） -/

lemma relu_sq_local (a y : ℝ) (h : a < y) : relu (y - a) = y - a := by
  exact relu_eq_self_of_nonneg (y - a) (by linarith)

lemma deriv_relu_sq_gt (a x : ℝ) (h : a < x) :
    deriv (fun y => relu (y - a) ^ 2) x = 2 * (x - a) := by
  -- 局部：relu(y-a) = y-a（x>a 邻域）
  have hloc : ∀ᶠ y in 𝓝 x, relu (y - a) = y - a := by
    -- (a, +∞) 是 x 的邻域（x > a）
    have hmem : x ∈ Set.Ioi a := h
    exact mem_of_superset (isOpen_Ioi.mem_nhds hmem) (fun y hy => relu_sq_local a y hy)
  -- 局部函数 (y-a)² 的导数 = 2(x-a)
  have hder : HasDerivAt (fun y => relu (y - a) ^ 2) (2 * (x - a)) x := by
    have hlin : HasDerivAt (fun y : ℝ => y - a) 1 x := by
      simpa using (hasDerivAt_id x).sub (hasDerivAt_const x a)
    have hpow : HasDerivAt (fun y : ℝ => (y - a) ^ 2) (2 * (x - a)) x := by
      simpa using hlin.pow 2
    -- congr：在邻域内 relu(y-a)² = (y-a)²
    refine hpow.congr_of_eventuallyEq ?_
    filter_upwards [hloc] with y hy
    rw [hy]
  exact hder.deriv

theorem P2a_nonstationary_when_unsatisfied (a x : ℝ) (h : a < x) :
    deriv (fun y => relu (y - a) ^ 2) x ≠ 0 := by
  rw [deriv_relu_sq_gt a x h]
  have hx : x - a ≠ 0 := by linarith
  have h2 : 2 * (x - a) ≠ 0 := by
    intro hz
    exact hx ((mul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℝ) ≠ 0))
  exact h2

/-! ## P2b：ReLU 线性损失存在虚假驻点（反例）
L(y) = relu(y) + relu(1-y) 在 (0,1) 内恒为 1，导数 0；
但约束（y ≤ 0 ∧ 1-y ≤ 0）不满足——梯度零化不蕴含满足。-/

lemma relu_add_complement_const (y : ℝ) (h0 : 0 < y) (h1 : y < 1) :
    relu y + relu (1 - y) = 1 := by
  have hy : relu y = y := relu_eq_self_of_nonneg y (le_of_lt h0)
  have h1y : relu (1 - y) = 1 - y := relu_eq_self_of_nonneg (1 - y) (by linarith)
  rw [hy, h1y]
  ring

def ReLUSumLoss (y : ℝ) : ℝ := relu y + relu (1 - y)

lemma ReLUSumLoss_const_on_open (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    deriv ReLUSumLoss x = 0 := by
  -- (0,1) 内恒为 1 → 局部常数 → 导数 0
  have hloc : ∀ᶠ y in 𝓝 x, ReLUSumLoss y = 1 := by
    have hmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    exact mem_of_superset (isOpen_Ioo.mem_nhds hmem) (fun y hy =>
      congrArg (fun z : ℝ => z) (relu_add_complement_const y hy.1 hy.2))
  have hc : HasDerivAt ReLUSumLoss 0 x := by
    apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
    simpa [ReLUSumLoss] using hloc
  exact hc.deriv

theorem P2b_false_stationarity :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ deriv ReLUSumLoss x = 0 ∧ ¬(x ≤ 0 ∧ 1 - x ≤ 0) := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · exact ReLUSumLoss_const_on_open (1 / 2) (by norm_num) (by norm_num)
  · norm_num

/-! ## 推论：P2a 的完整表述（单约束 relu 平方损失）
不满足（x > a）⟹ 非驻点；满足（x ≤ a）⟹ relu 输出零（损失为零，relu_preserves）。
与 P2b 对比：**平方 relu 项无虚假驻点，线性 relu 项有**。 -/

theorem P2a_relu_sq_summary (a x : ℝ) :
    a < x → deriv (fun y => relu (y - a) ^ 2) x ≠ 0 :=
  P2a_nonstationary_when_unsatisfied a x

end Lattice
