import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Convex.RealSubgradientDescent
import Lattice.Lib.Optim.RealConvergence
import Mathlib

/-!
# LATTICE: 梯度压缩 + 误差反馈（分布式训练中的有界误差与平均一致性）

分布式/通信受限训练中，每个 worker 只能发送梯度的**压缩版本** `C(g)`（top-k、量化等）。
直接发送压缩量会让误差逐步累积；**误差反馈（error feedback, EF）** 的标准做法是把上一轮
的残差 `e` 加回本轮梯度再压缩：

    e' = e + g            （累积）
    s  = C(e')            （发送压缩量）
    e'' = e' − C(e')      （新残差）

## 主结果

1. **误差有界**（`errorFeedback_bounded`）：压缩算子满足相对误差界
   `|C x − x| ≤ (1−δ)|x|`（`0 < δ ≤ 1`），且梯度一致有界 `|g_t| ≤ G`，则误差反馈残差
   一致有界：

       |e_t| ≤ G·(1−δ)/δ        （即 O(G/δ)，与步数 T 无关）

2. **精确望远镜恒等式**（`ef_transmit_eq`）：发送量满足

       C(e_t + g_t) = g_t + (e_t − e_{t+1})

   求和后 `Σ C(e_t+g_t) = Σ g_t + e_0 − e_T`，故**压缩流与真实梯度的平均偏差只有 O(1/T)**
   （`errorFeedback_average_consistency` / `errorFeedback_convergence`）：
   误差反馈并不改变 SGD 的**平均前进方向**，只引入一个有界偏移。

3. **框架衔接**（`ef_sgd_rate`）：在「校正后的发送量是无偏次梯度估计」这一标准 EF 假设下，
   直接调用 `RealSGDStochastic.sgd_rate_bound` 得到 `O(D·G'/√T)` 的期望率。该假设本身
   不由压缩算子推出（见下），本文件如实标注。

4. **无反饋的反例**（`noFeedback_divergence`）：若把压缩误差直接丢弃（不做误差反馈），
   在 `C ≡ 0`、`g ≡ 1` 的构造下累积压缩误差 `Σ_{t<T}(g_t − C(g_t)) = T` 无界 ——
   与 1 的有界性形成对照。

## 诚实边界

- 压缩假设只有**相对误差界**（`IsCompressor`）：这是 δ-近似压缩的常用理想化，`E‖C(x)−x‖² ≤ (1−δ)‖x‖²`
  的确定型强化版；不做随机化压缩（无偏 top-k 等）的概率化处理。
- 定理 3 需要「校正后方向是无偏次梯度估计」这一**额外假设**：误差反馈本身不保证无偏
  （压缩是有偏算子），本文件不声称从压缩算子推出它 —— 这是明确标注的降级，不是被掩盖的 gap。
- 残差界 `G(1−δ)/δ` 在 `δ → 0` 时发散，与 4 的反例一致：`δ > 0` 是本质的。
- 定标量 ℝ 一维，与 RealSGDStochastic / RealSubgradientDescent 同口径。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、压缩算子与误差反馈的定义 -/

/-- 压缩算子：δ-近似压缩，`∀ g, |C g − g| ≤ (1−δ)|g|`，`0 < δ ≤ 1`。 -/
def IsCompressor (C : ℝ → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ ∀ g : ℝ, |C g - g| ≤ (1 - δ) * |g|

/-- 压缩：`compress C g = C g`。 -/
def compress (C : ℝ → ℝ) (g : ℝ) : ℝ := C g

/-- 累积：`e + g`。 -/
def efAccumulate (e g : ℝ) : ℝ := e + g

/-- 压缩发送量：`C (e + g)`。 -/
def efTransmit (C : ℝ → ℝ) (e g : ℝ) : ℝ := C (e + g)

/-- 误差反馈的新残差：`e'' = (e + g) − C(e + g)`。 -/
def efNewError (C : ℝ → ℝ) (e g : ℝ) : ℝ := (e + g) - C (e + g)

/-- 误差反馈残差序列：`e_0 = 0`，`e_{t+1} = efNewError C (e_t) (g_t)`。 -/
def efErrorSeq (C : ℝ → ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (t + 1) => efNewError C (efErrorSeq C g t) (g t)

lemma efErrorSeq_zero (C : ℝ → ℝ) (g : ℕ → ℝ) : efErrorSeq C g 0 = 0 := rfl

lemma efErrorSeq_succ (C : ℝ → ℝ) (g : ℕ → ℝ) (t : ℕ) :
    efErrorSeq C g (t + 1) = efNewError C (efErrorSeq C g t) (g t) := rfl

lemma efNewError_eq (C : ℝ → ℝ) (e g : ℝ) : efNewError C e g = (e + g) - C (e + g) := rfl

/-! ## 二、主结果：误差反馈残差一致有界

一般序列形式（便于归纳）：`e_0 = 0`、`e_{t+1} = (e_t + g_t) − C(e_t + g_t)`，
则 `|e_t| ≤ G(1−δ)/δ`。 -/

theorem errorFeedback_bounded_aux (C : ℝ → ℝ) (δ G : ℝ) (g e : ℕ → ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (hg : ∀ t : ℕ, |g t| ≤ G)
    (he0 : e 0 = 0)
    (hrec : ∀ t : ℕ, e (t + 1) = (e t + g t) - C (e t + g t)) :
    ∀ t : ℕ, |e t| ≤ G * (1 - δ) / δ := by
  have hG0 : 0 ≤ G := le_trans (abs_nonneg (g 0)) (hg 0)
  have h1δ : 0 ≤ 1 - δ := by linarith
  have htarget : 0 ≤ G * (1 - δ) / δ :=
    div_nonneg (mul_nonneg hG0 h1δ) (le_of_lt hδ0)
  have hkey : (1 - δ) * (G * (1 - δ) / δ + G) = G * (1 - δ) / δ := by
    field_simp [ne_of_gt hδ0]
    ring
  intro t
  induction t with
  | zero => rw [he0]; simpa using htarget
  | succ t ih =>
      have h1 : |(e t + g t) - C (e t + g t)| ≤ (1 - δ) * |e t + g t| := by
        have h := hC (e t + g t)
        rwa [abs_sub_comm] at h
      have h2 : |e t + g t| ≤ |e t| + |g t| := abs_add _ _
      have h3 : |e t| + |g t| ≤ G * (1 - δ) / δ + G := add_le_add ih (hg t)
      rw [hrec t]
      calc
        |(e t + g t) - C (e t + g t)| ≤ (1 - δ) * |e t + g t| := h1
        _ ≤ (1 - δ) * (|e t| + |g t|) := mul_le_mul_of_nonneg_left h2 h1δ
        _ ≤ (1 - δ) * (G * (1 - δ) / δ + G) := mul_le_mul_of_nonneg_left h3 h1δ
        _ = G * (1 - δ) / δ := hkey

/-- **误差反馈残差一致有界**：δ-近似压缩 + 梯度有界 ⟹ `|e_t| ≤ G(1−δ)/δ`。 -/
theorem errorFeedback_bounded (C : ℝ → ℝ) (δ G : ℝ) (g : ℕ → ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (hg : ∀ t : ℕ, |g t| ≤ G) :
    ∀ t : ℕ, |efErrorSeq C g t| ≤ G * (1 - δ) / δ :=
  errorFeedback_bounded_aux C δ G g (efErrorSeq C g) hδ0 hδ1 hC hg
    (efErrorSeq_zero C g)
    (fun t => by rw [efErrorSeq_succ]; rfl)

/-! ## 三、精确望远镜恒等式：发送量 = 梯度 + 残差差分

`C(e_t + g_t) = g_t + (e_t − e_{t+1})` 由 `e_{t+1} = (e_t + g_t) − C(e_t + g_t)` 直接重排。 -/

theorem ef_transmit_eq (C : ℝ → ℝ) (g e : ℕ → ℝ)
    (hrec : ∀ t : ℕ, e (t + 1) = (e t + g t) - C (e t + g t)) (t : ℕ) :
    C (e t + g t) = g t + (e t - e (t + 1)) := by
  rw [hrec t]
  ring

/-! ## 四、平均一致性：压缩流与真实梯度的总偏差有界

`Σ_{t<T}(C(e_t+g_t) − g_t) = e_0 − e_T`，故总偏差 `≤ 2G(1−δ)/δ`。 -/

theorem errorFeedback_average_consistency (C : ℝ → ℝ) (δ G : ℝ) (g e : ℕ → ℝ) (T : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (hg : ∀ t : ℕ, |g t| ≤ G)
    (he0 : e 0 = 0)
    (hrec : ∀ t : ℕ, e (t + 1) = (e t + g t) - C (e t + g t)) :
    |(∑ t in Finset.range T, C (e t + g t)) - (∑ t in Finset.range T, g t)| ≤
      2 * G * (1 - δ) / δ := by
  have hbound := errorFeedback_bounded_aux C δ G g e hδ0 hδ1 hC hg he0 hrec
  have hsum : (∑ t in Finset.range T, C (e t + g t)) - (∑ t in Finset.range T, g t)
      = ∑ t in Finset.range T, (e t - e (t + 1)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun t _ => by rw [ef_transmit_eq C g e hrec t]; ring)
  have htel : (∑ t in Finset.range T, (e t - e (t + 1))) = e 0 - e T :=
    sum_range_sub_telescoping T
  rw [hsum, htel]
  calc
    |e 0 - e T| ≤ |e 0| + |e T| := by
      have h := abs_add (e 0) (-(e T))
      rw [abs_neg] at h
      simpa using h
    _ ≤ G * (1 - δ) / δ + G * (1 - δ) / δ := add_le_add (hbound 0) (hbound T)
    _ = 2 * G * (1 - δ) / δ := by ring

/-- **平均一致性（O(1/T)）**：压缩流与真实梯度的**平均**偏差满足
`|(1/T)Σ C(e_t+g_t) − (1/T)Σ g_t| ≤ 2G(1−δ)/(δT)`。
即误差反馈下压缩只引入 O(1/T) 的平均方向偏移。 -/
theorem errorFeedback_convergence (C : ℝ → ℝ) (δ G : ℝ) (g e : ℕ → ℝ) (T : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : ∀ x : ℝ, |C x - x| ≤ (1 - δ) * |x|)
    (hg : ∀ t : ℕ, |g t| ≤ G)
    (he0 : e 0 = 0)
    (hrec : ∀ t : ℕ, e (t + 1) = (e t + g t) - C (e t + g t))
    (hT : 0 < T) :
    |(1 / (T : ℝ)) * (∑ t in Finset.range T, C (e t + g t))
        - (1 / (T : ℝ)) * (∑ t in Finset.range T, g t)| ≤
      2 * G * (1 - δ) / (δ * (T : ℝ)) := by
  have h := errorFeedback_average_consistency C δ G g e T hδ0 hδ1 hC hg he0 hrec
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have h1T : 0 ≤ 1 / (T : ℝ) := div_nonneg zero_le_one (le_of_lt hTpos)
  rw [← mul_sub, abs_mul, abs_of_nonneg h1T]
  calc
    (1 / (T : ℝ)) * |(∑ t in Finset.range T, C (e t + g t))
        - (∑ t in Finset.range T, g t)|
        ≤ (1 / (T : ℝ)) * (2 * G * (1 - δ) / δ) :=
          mul_le_mul_of_nonneg_left h h1T
    _ = 2 * G * (1 - δ) / (δ * (T : ℝ)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring

/-! ## 五、框架衔接：EF 校正流的 O(D·G'/√T) 期望率

在「校正后的发送量是无偏次梯度估计、二阶矩 ≤ G'²」这一**标准 EF 假设**下
（以逐步期望收缩 `hstep` 的形式给出），`RealSGDStochastic.sgd_rate_bound` 直接给出
`∃ t < T, E[f(x_t) − f x*] ≤ D·G'/√T`。该假设不由 `IsCompressor` 推出（压缩有偏），
故此处如实作为假设引入。 -/

theorem ef_sgd_rate {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω)
    (f : ℝ → ℝ) (x : ℕ → Ω → ℝ) (xstar G' D η : ℝ) (T : ℕ)
    (hG : 0 < G') (hT : 0 < T) (hD : 0 < D)
    (hD2 : ExpDist p (x 0) xstar = D ^ 2)
    (hη : η = D / (G' * Real.sqrt (T : ℝ)))
    (hstep : ∀ t : ℕ, ExpDist p (x (t + 1)) xstar ≤
      ExpDist p (x t) xstar - 2 * η * ExpGap p f (x t) xstar + η ^ 2 * G' ^ 2) :
    ∃ t : ℕ, t < T ∧ ExpGap p f (x t) xstar ≤ D * G' / Real.sqrt (T : ℝ) :=
  sgd_rate_bound p hp0 f x xstar G' D η T hG hT hD hD2 hη hstep

/-! ## 六、无反饋的反例：压缩误差线性累积

`noFeedbackError C g T = Σ_{t<T}(g_t − C(g_t))`。取 `C ≡ 0`（只满足退化的 δ = 0 相对界
`|C x − x| = |x| ≤ (1−0)|x|`）、`g ≡ 1`：累积误差 = T，随 T 无界。
与 `errorFeedback_bounded` 的 `G(1−δ)/δ` 界对照：δ → 0 时 EF 界也发散，`δ > 0` 是本质的。 -/

def noFeedbackError (C : ℝ → ℝ) (g : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t in Finset.range T, (g t - C (g t))

/-- **无反饋的压缩误差无界**：`C ≡ 0`、`g ≡ 1` 时 `Σ_{t<T}(g_t − C(g_t)) = T`，
故 `∀ B, ∃ T, B < Σ...`。 -/
theorem noFeedback_divergence :
    ∀ B : ℝ, ∃ T : ℕ, B < noFeedbackError (fun _ => 0) (fun _ => 1) T := by
  intro B
  rcases exists_nat_gt B with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have h : noFeedbackError (fun _ => 0) (fun _ => 1) N = (N : ℝ) := by
    simp only [noFeedbackError]
    simp
  rw [h]
  exact hN

/-! ## 注：闭环语义
  压缩算子（IsCompressor）→ 误差反馈递推（efErrorSeq）→
  残差一致有界（errorFeedback_bounded，O(G/δ)）→ 精确望远镜恒等式（ef_transmit_eq）→
  平均一致性 O(1/T)（errorFeedback_convergence）→ 框架衔接 O(D·G'/√T)（ef_sgd_rate）；
  对照：无反饋压缩误差线性发散（noFeedback_divergence）。
  诚实标注：压缩的相对误差界与「校正流无偏」假设均为显式假设。 -/

end Lattice
