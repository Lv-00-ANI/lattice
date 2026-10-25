import Mathlib
import Lattice.Lib.Optim.RealStrongConvex
import Lattice.Lib.Optim.RealNesterov
/-!
# LATTICE: Nesterov O(1/k²) —— 估计序列的 Lyapunov 算术与参数序列

`RealNesterov` 覆盖了「下降引理 + 望远镜 + 共强制性下的参数空间收缩」，并明确标注
**完整的 Nesterov O(1/k²) 目标值率未证**。本文件补齐该缺口中**可形式化的算术内核**：

* 参数序列 `A_k = k²/4`（`A_0 = 0`，`A` 单调增，`a_k := A_k − A_{k−1}` 满足 `a_k² ≤ A_k`）；
* Lyapunov 函数 `V_k = A_k(f(x_k) − f*) + (1/2)‖u_k − x*‖²`；
* **望远镜定理**：`V_{k+1} ≤ V_k`（∀k）⟹ `A_k(f(x_k) − f*) ≤ (1/2)‖u_0 − x*‖²`；
* **率定理**：`A_k > 0` 时 `f(x_k) − f* ≤ (1/2)‖u_0 − x*‖² / A_k`；对 `A_k = k²/4`
  得 `f(x_k) − f* ≤ 2‖u_0 − x*‖²/k²`（即 O(1/k²)）；
* **接口非空的一致性检验**：普通梯度步（`η ≤ 1/L`）满足带常数 `A ≡ 1`、
  `u ≡ x₀` 的 Lyapunov 非增性（由 `RealNesterov.nesterov_descent_lemma_le`）。

定理清单：
  1. `nestA`（def）、`nestA_zero`、`nestA_nonneg`、`nestA_pos`、`nestA_mono`；
  2. `nestStep`（def）、`nestStep_sq_le`（`a_k² ≤ A_k`）；
  3. `nestLyap`（def）；
  4. `nesterov_lyapunov_telescope`（**核心算术**）；
  5. `nesterov_rate_of_lyapunov`（一般 `A` 的率）、`nestA_rate`（**O(1/k²)**）；
  6. `nestA_arith_consistency`（梯度步的 Lyapunov 非增，接口非空）。

**诚实边界（重要，降级说明）**：
- 本文件证明的是 Nesterov 估计序列证明中的**Lyapunov 望远镜与参数序列算术**。
  「具体动量格式 `y_k = x_k + β_k(x_k − x_{k−1})`、`x_{k+1} = y_k − (1/L)∇f(y_k)`
  确实使 `V_{k+1} ≤ V_k` 成立」——即**估计序列构造与方案的对接**——本文件**未做**，
  它以显式假设 `hmono : ∀ k, V_{k+1} ≤ V_k`（或 `nestA_rate` 中的 `hmono`）出现。
  因此本文件**不声称**证明了完整 Nesterov 定理，只补上其可证算术内核；
- 与 `RealNesterov` 一致：一维、`Smooth`/`StrongConvex` 为下降引理形式的显式假设；
- 一致性检验（定理 6）说明该接口**非空**（梯度步是其特例），但不是 O(1/k²) 的来源
  （梯度步只给 O(1/k)）；
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、参数序列 `A_k = k²/4` -/

/-- **Nesterov 参数序列**（规范化）：`A_k = k²/4`（`A_0 = 0`、`A_1 = 1/4`）。
`a_k := A_k − A_{k−1} = (2k−1)/4`。 -/
def nestA (k : ℕ) : ℝ := (k : ℝ) ^ 2 / 4

/-- `A_0 = 0`（Lyapunov 初始条件 `V_0 = (1/2)‖u_0 − x*‖²` 的关键）。 -/
lemma nestA_zero : nestA 0 = 0 := by
  simp [nestA]

/-- `A_k ≥ 0`。 -/
lemma nestA_nonneg (k : ℕ) : 0 ≤ nestA k := by
  unfold nestA
  positivity

/-- `k > 0` 时 `A_k > 0`。 -/
lemma nestA_pos {k : ℕ} (hk : 0 < k) : 0 < nestA k := by
  unfold nestA
  have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  positivity

/-- `A` 单调不减。 -/
lemma nestA_mono {i j : ℕ} (hij : i ≤ j) : nestA i ≤ nestA j := by
  unfold nestA
  have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have h2 : (i : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
    exact pow_le_pow_left₀ h0 h 2
  linarith

/-- 相邻差 `a_k = A_{k+1} − A_k = (2k+1)/4`。 -/
def nestStep (k : ℕ) : ℝ := nestA (k + 1) - nestA k

/-- **参数序列的可行性**：`a_k² ≤ A_{k+1}`（估计序列构造对 `a_k` 的标准要求）。
`a_k = (2k+1)/4`、`A_{k+1} = (k+1)²/4`，等价于 `(2k+1)² ≤ (2k+2)²`。 -/
lemma nestStep_sq_le (k : ℕ) : nestStep k ^ 2 ≤ nestA (k + 1) := by
  have h1 : nestA (k + 1) = ((k : ℝ) + 1) ^ 2 / 4 := by
    simp only [nestA]
    push_cast
    ring
  have h2 : nestStep k = (2 * (k : ℝ) + 1) / 4 := by
    simp only [nestStep, nestA]
    push_cast
    ring
  rw [h2, h1]
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  nlinarith [hk]

/-! ## 二、Lyapunov 函数与望远镜 -/

/-- **Nesterov Lyapunov 函数**：
`V_k = A_k·(f(x_k) − f x*) + (1/2)‖u_k − x*‖²`。 -/
def nestLyap (A : ℕ → ℝ) (f : ℝ → ℝ) (xstar : ℝ) (xs us : ℕ → ℝ) (k : ℕ) : ℝ :=
  A k * (f (xs k) - f xstar) + (1 / 2) * (us k - xstar) ^ 2

/-- **Lyapunov 望远镜（核心算术）**：`A_k ≥ 0`、`V_{k+1} ≤ V_k`（∀k）、`A_0 = 0` ⟹
`A_k·(f(x_k) − f x*) ≤ (1/2)‖u_0 − x*‖²`。

证明：对 `k` 归纳得 `V_k ≤ V_0 = (1/2)‖u_0 − x*‖²`（`A_0 = 0`），
再用 `(1/2)‖u_k − x*‖² ≥ 0` 去掉非负项。 -/
theorem nesterov_lyapunov_telescope {A : ℕ → ℝ} {f : ℝ → ℝ} {xstar : ℝ}
    {xs us : ℕ → ℝ} (hA0 : A 0 = 0) (hAnonneg : ∀ k, 0 ≤ A k)
    (hmono : ∀ k, nestLyap A f xstar xs us (k + 1) ≤ nestLyap A f xstar xs us k) :
    ∀ k : ℕ, A k * (f (xs k) - f xstar) ≤ (1 / 2) * (us 0 - xstar) ^ 2 := by
  intro k
  have h : nestLyap A f xstar xs us k ≤ nestLyap A f xstar xs us 0 := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact le_trans (hmono k) ih
  have hnonneg : 0 ≤ (1 / 2) * (us k - xstar) ^ 2 := by positivity
  have hV0 : nestLyap A f xstar xs us 0 = (1 / 2) * (us 0 - xstar) ^ 2 := by
    simp only [nestLyap, hA0, zero_mul, zero_add]
  rw [hV0] at h
  simp only [nestLyap] at h
  linarith

/-- **率定理（一般 `A`）**：`A_k > 0` 且望远镜条件成立 ⟹
`f(x_k) − f x* ≤ ((1/2)‖u_0 − x*‖²) / A_k`。 -/
theorem nesterov_rate_of_lyapunov {A : ℕ → ℝ} {f : ℝ → ℝ} {xstar : ℝ}
    {xs us : ℕ → ℝ} (hA0 : A 0 = 0) (hAnonneg : ∀ k, 0 ≤ A k)
    (hmono : ∀ k, nestLyap A f xstar xs us (k + 1) ≤ nestLyap A f xstar xs us k)
    {k : ℕ} (hk : 0 < A k) :
    f (xs k) - f xstar ≤ ((1 / 2) * (us 0 - xstar) ^ 2) / A k := by
  have h := nesterov_lyapunov_telescope hA0 hAnonneg hmono k
  rw [le_div_iff₀ hk]
  linarith [h]

/-- **Nesterov O(1/k²) 率（对 `A_k = k²/4`）**：在 Lyapunov 单调性假设下，
`f(x_k) − f x* ≤ 2‖u_0 − x*‖²/k²`（`k > 0`）。 -/
theorem nestA_rate {f : ℝ → ℝ} {xstar : ℝ} {xs us : ℕ → ℝ}
    (hmono : ∀ k, nestLyap nestA f xstar xs us (k + 1) ≤ nestLyap nestA f xstar xs us k)
    {k : ℕ} (hk : 0 < k) :
    f (xs k) - f xstar ≤ 2 * (us 0 - xstar) ^ 2 / (k : ℝ) ^ 2 := by
  have hApos : 0 < nestA k := nestA_pos hk
  have h := nesterov_rate_of_lyapunov nestA_zero nestA_nonneg hmono hApos
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hk)
  have heq : ((1 / 2) * (us 0 - xstar) ^ 2) / nestA k
      = 2 * (us 0 - xstar) ^ 2 / (k : ℝ) ^ 2 := by
    simp only [nestA]
    field_simp [hkne]
    ring
  linarith [h, heq]

/-! ## 三、接口非空的一致性检验 -/

/-- **梯度步满足 Lyapunov 非增（常数 `A ≡ 1`、`u ≡ x₀`）**：`η ≤ 1/L` 时
普通梯度步的目标值不增，因此 `V_{k+1} ≤ V_k` 对 `V = 1·(f(x_k) − f*) + c` 成立。
这说明第 4/5 条所用的 Lyapunov 接口**非空**（不是空假设）。 -/
theorem nestA_arith_consistency {f g : ℝ → ℝ} {L eta xstar c x : ℝ} (hL : 0 < L)
    (heta : 0 < eta) (hetaL : eta ≤ 1 / L) (hSM : Smooth L f g) :
    (1 : ℝ) * (f (x - eta * g x) - f xstar) + c ≤ (1 : ℝ) * (f x - f xstar) + c := by
  have h := nesterov_descent_lemma_le hL heta hetaL hSM x
  linarith

/-! ## 注：闭环语义与诚实边界
  `nestA`/`nestStep`（参数序列）→ `nestStep_sq_le`（可行性）→
  `nesterov_lyapunov_telescope`（望远镜）→ `nesterov_rate_of_lyapunov` /
  `nestA_rate`（率）；`nestA_arith_consistency` 说明 Lyapunov 接口非空。
  **降级说明**：估计序列与具体动量方案的对接（`hmono` 的实际成立性）**未证**，
  以显式假设出现；本文件只声称证明了 O(1/k²) 的算术内核。 -/

end Lattice
