import Mathlib
import Lattice.Runtime.RealNonlinear
import Lattice.Lib.Architectures.RealReLUStationarity
/-!
# LATTICE: ReLU 次梯度 —— 非光滑驻点的次梯度刻画（§5 约束行「次梯度」）

relu 在 0 处不可导（左导 0、右导 1）——经典事实，本文件不重证——
可微驻点分析（RealReLUStationarity）在 0 处失效。本文件从**次梯度**
（凸分析意义）刻画非光滑驻点：

  次梯度定义（一维凸 f : ℝ → ℝ 在 x 处）：
    g ∈ ∂f(x) ⟺ ∀ y, f y ≥ f x + g·(y − x)

  relu 的次梯度（逐点非空，驻点良定）：
    ∂relu(0) = [0,1]；∂relu(x) = {1}（x > 0）；∂relu(x) = {0}（x < 0）

结论（relu_subgradient_nonempty）：relu 处处有次梯度——**非光滑但驻点良定**；
且 0 ∈ ∂relu(0) 给出「0 是全局最小点」（subgradient_minimum_criterion：
g = 0 时次梯度不等式即全局最小性，无需凸性）；
衔接 RealReLUStationarity 的 relu² 驻点线：relu² 在 0 处不可导，
但 0 ∈ ∂(relu²)(0)（reluSq_subgradient_zero_at_zero）——
正是**非光滑驻点**定义（0 在次梯度中 ⟹ 驻点良定）。

诚实边界：
  · 0 处不可导是经典事实（左右导数不同），本文件只说明不证明；
  · mathlib 4.14 **无** `Convex.subderiv`（源码检索确认），次梯度按定义自证；
  · relu 的凸性/次梯度非空此处逐点直接验证，未走一般凸分析定理；
  · relu_mask_decomposition（RealActClass）给出 relu x = s(x)·x、s ∈ [0,1]，
    与 ∂relu(0) = [0,1] 的软掩码直觉一致（仅 docstring 关联，未用于证明）。

mathlib 4.14 说明：relu x = max x 0；0 ≤ x ⟹ relu x = x 用 max_eq_left
（RealReLUStationarity.relu_eq_self_of_nonneg），x ≤ 0 ⟹ relu x = 0 用 max_eq_right。
-/

noncomputable section

namespace Lattice

/-! ## 次梯度定义（subgradient_def）
一维凸 f : ℝ → ℝ 在 x 处：g ∈ ∂f(x) ⟺ ∀ y, f y ≥ f x + g·(y − x)。
mathlib 4.14 无现成 `Convex.subderiv`，按定义自证。-/

def Subgradient (f : ℝ → ℝ) (x g : ℝ) : Prop :=
  ∀ y : ℝ, f y ≥ f x + g * (y - x)

/-! ## 引理：0 处次梯度（核心）—— t ∈ [0,1] ⟹ t ∈ ∂relu(0)
y ≥ 0 时 relu y = y，需 y ≥ t·y ⟸ t ≤ 1；y ≤ 0 时 relu y = 0，需 0 ≥ t·y ⟸ t ≥ 0。 -/

theorem relu_subgradient_zero (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Subgradient relu 0 t := by
  intro y
  by_cases hy : y ≤ 0
  · -- y ≤ 0：relu y = 0，需 0 ≥ t·y
    have hz : relu 0 = 0 := relu_eq_zero_of_nonpos 0 le_rfl
    have hrel : relu y = 0 := relu_eq_zero_of_nonpos y hy
    have hmul : t * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hy
    rw [hz, hrel]
    simpa using hmul
  · -- 0 ≤ y：relu y = y，需 y ≥ t·y（t ≤ 1）
    have hypos : 0 ≤ y := le_of_not_ge hy
    have hz : relu 0 = 0 := relu_eq_zero_of_nonpos 0 le_rfl
    have hrel : relu y = y := relu_eq_self_of_nonneg y hypos
    have hmul : t * y ≤ y := by
      calc
        t * y ≤ 1 * y := mul_le_mul_of_nonneg_right ht1 hypos
        _ = y := by simp
    rw [hz, hrel]
    simpa using hmul

/-! ## 引理：∂relu(0) = [0,1]（完整刻画，定义性刻画）
反向：y = −1 处 relu(−1) = 0 ≥ g·(−1) ⟹ g ≥ 0；y = 1 处 relu 1 = 1 ≥ g ⟹ g ≤ 1。 -/

theorem relu_subgradient_zero_iff (g : ℝ) : Subgradient relu 0 g ↔ 0 ≤ g ∧ g ≤ 1 := by
  constructor
  · intro hg
    have hinst1 := hg (-1)
    rw [relu_eq_zero_of_nonpos (-1) (by norm_num), relu_eq_zero_of_nonpos 0 le_rfl] at hinst1
    have hg0 : 0 ≤ g := by nlinarith
    have hinst2 := hg 1
    rw [relu_eq_self_of_nonneg 1 (by norm_num), relu_eq_zero_of_nonpos 0 le_rfl] at hinst2
    have hg1 : g ≤ 1 := by nlinarith
    exact ⟨hg0, hg1⟩
  · intro h
    exact relu_subgradient_zero g h.1 h.2

/-! ## 引理：x > 0 ⟹ ∂relu(x) = {1}
双向：g ∈ ∂relu(x) ⟺ g = 1。
单边：y = x+1 方向（relu(x+1) = x+1）⟹ g ≤ 1；y = 0 方向（relu 0 = 0）⟹ g ≥ 1（x > 0）。
反向：1 ∈ ∂relu(x) 直接验证（relu y ≥ x + (y − x) = y 恒真，因 relu y = max y 0 ≥ y）。 -/

theorem relu_subgradient_positive (x g : ℝ) (hx : 0 < x) :
    Subgradient relu x g ↔ g = 1 := by
  constructor
  · intro hg
    have hrelx : relu x = x := relu_eq_self_of_nonneg x (le_of_lt hx)
    have hup : g ≤ 1 := by
      -- y = x + 1：relu(x+1) = x+1 ⟹ x+1 ≥ x + g·1 ⟹ g ≤ 1
      have hy : 0 ≤ x + 1 := by linarith
      have hrelp : relu (x + 1) = x + 1 := relu_eq_self_of_nonneg (x + 1) hy
      have hinst := hg (x + 1)
      rw [hrelp, hrelx] at hinst
      nlinarith
    have hlo : 1 ≤ g := by
      -- y = 0：relu 0 = 0 ⟹ 0 ≥ x + g·(0−x) = x − gx ⟹ gx ≥ x ⟹ g ≥ 1（x > 0）
      have hrel0 : relu 0 = 0 := relu_eq_zero_of_nonpos 0 le_rfl
      have hinst := hg 0
      rw [hrel0, hrelx] at hinst
      have hx2 : x * (1 - g) ≤ 0 := by
        nlinarith
      have hng : 1 - g ≤ 0 := by
        by_contra h
        have hpos : 0 < 1 - g := lt_of_not_ge h
        have : 0 < x * (1 - g) := mul_pos hx hpos
        linarith
      linarith
    exact le_antisymm hup hlo
  · intro hg1
    rw [hg1]
    have hrelx : relu x = x := relu_eq_self_of_nonneg x (le_of_lt hx)
    intro y
    by_cases hy : y ≤ 0
    · -- y ≤ 0：relu y = 0，需 0 ≥ x + (y − x) = y（y ≤ 0）
      have hrel : relu y = 0 := relu_eq_zero_of_nonpos y hy
      rw [hrelx, hrel]
      nlinarith [hy]
    · -- 0 ≤ y：relu y = y，需 y ≥ x + (y − x) = y（恒真）
      have hypos : 0 ≤ y := le_of_not_ge hy
      have hrel : relu y = y := relu_eq_self_of_nonneg y hypos
      rw [hrelx, hrel]
      nlinarith

/-! ## 引理：x < 0 ⟹ ∂relu(x) = {0}
双向：g ∈ ∂relu(x) ⟺ g = 0。
单边：y = x−1 方向（relu(x−1) = 0）⟹ 0 ≥ g·(−1) ⟹ g ≥ 0；
y = x/2 方向（x < x/2 < 0，relu(x/2) = 0，x/2 − x > 0）⟹ 0 ≥ g·(x/2 − x) ⟹ g ≤ 0。
反向：0 ∈ ∂relu(x) 直接验证（relu y ≥ 0 = relu_nonneg）。 -/

theorem relu_subgradient_negative (x g : ℝ) (hx : x < 0) :
    Subgradient relu x g ↔ g = 0 := by
  constructor
  · intro hg
    have hrelx : relu x = 0 := relu_eq_zero_of_nonpos x (le_of_lt hx)
    have hlo : 0 ≤ g := by
      -- y = x − 1：relu(x−1) = 0 ⟹ 0 ≥ g·(−1) ⟹ g ≥ 0
      have hrelp : relu (x - 1) = 0 := relu_eq_zero_of_nonpos (x - 1) (by linarith)
      have hinst := hg (x - 1)
      rw [hrelp, hrelx] at hinst
      nlinarith
    have hup : g ≤ 0 := by
      -- y = x/2：x < x/2 < 0，relu(x/2) = 0，x/2 − x > 0 ⟹ 0 ≥ g·(x/2 − x) ⟹ g ≤ 0
      have hrelp : relu (x / 2) = 0 := relu_eq_zero_of_nonpos (x / 2) (by nlinarith)
      have hinst := hg (x / 2)
      rw [hrelp, hrelx] at hinst
      have ha : 0 < x / 2 - x := by nlinarith
      have hmul : g * (x / 2 - x) ≤ 0 := by nlinarith
      by_contra h
      have hgpos : 0 < g := lt_of_not_ge h
      have : 0 < g * (x / 2 - x) := mul_pos hgpos ha
      linarith
    exact le_antisymm hup hlo
  · intro hg0
    rw [hg0]
    have hrelx : relu x = 0 := relu_eq_zero_of_nonpos x (le_of_lt hx)
    intro y
    rw [hrelx]
    simpa using relu_nonneg y

/-! ## 核心结论：次梯度处处非空——非光滑但驻点良定
∀x, ∂relu(x) 非空：x < 0 取 0；x = 0 取 0 ∈ [0,1]；x > 0 取 1。 -/

theorem relu_subgradient_nonempty (x : ℝ) : ∃ g : ℝ, Subgradient relu x g := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact ⟨0, (relu_subgradient_negative x 0 hx).mpr rfl⟩
  · subst hx
    exact ⟨0, relu_subgradient_zero 0 (by norm_num) (by norm_num)⟩
  · exact ⟨1, (relu_subgradient_positive x 1 hx).mpr rfl⟩

/-! ## 定理：0 ∈ ∂f(x*) ⟹ x* 是全局最小点
g = 0 时次梯度不等式就是 ∀y, f x* ≤ f y——**无需凸性**（凸性保证
∂f 非空/定义良定，此处直接由定义得出）。 -/

theorem subgradient_minimum_criterion (f : ℝ → ℝ) (x : ℝ) :
    Subgradient f x 0 → ∀ y : ℝ, f x ≤ f y := by
  intro h y
  have hy := h y
  simpa [Subgradient] using hy

/-! ## 推论：relu 在 0 取全局最小 0（0 ∈ ∂relu(0) 取 t = 0） -/

theorem relu_minimum_at_zero : ∀ y : ℝ, relu 0 ≤ relu y := by
  exact subgradient_minimum_criterion relu 0 (relu_subgradient_zero 0 (by norm_num) (by norm_num))

/-! ## 衔接 ReluStationarity 线：relu² 的非光滑驻点
relu² 在 0 处不可导（relu 0 处不可导），但 **0 ∈ ∂(relu²)(0)**：
∀y, relu(y)² ≥ 0 + 0·y = 0（sq_nonneg）——非光滑驻点定义成立。 -/

theorem reluSq_subgradient_zero_at_zero :
    Subgradient (fun y : ℝ => relu y ^ 2) 0 0 := by
  intro y
  have hz : (fun y : ℝ => relu y ^ 2) 0 = 0 := by
    change relu 0 ^ 2 = 0
    rw [relu_eq_zero_of_nonpos 0 le_rfl]
    norm_num
  rw [hz]
  simpa using sq_nonneg (relu y)

end Lattice
