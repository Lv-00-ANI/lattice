import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealKLConvexity
/-!
# LATTICE: KL 的联合凸性 —— 逐项 log-sum 不等式、联合凸与有限加权版

RealKLConvexity 用初等方法（只用 `log x ≤ x − 1`）建立了 KL 的**单侧**凸性：
`ce_convex_in_q`、`kl_convex_in_q`、`kl_convex_in_p`（固定一个变量）。
本文件补上信息论中真正的核心：**联合凸**，即 (p, q) ↦ KL(p‖q) 对两个变量同时凸。

关键工具是**逐项 log-sum 不等式**（每条坐标 a）：
对 x, y, s, t > 0、lam ∈ [0,1]，m = lam·x + (1−lam)·y、r = lam·s + (1−lam)·t，

    m·log(m/r) ≤ lam·x·log(x/s) + (1−lam)·y·log(y/t)

证明路线（初等，与 RealKLConvexity.mul_log_convex_two 同型）：
  令 A = x·r/(s·m)、B = y·r/(t·m)，则
    lam·x·log(x/s) + (1−lam)·y·log(y/t) − m·log(m/r) = lam·x·log A + (1−lam)·y·log B
  （用 `Real.log_div`/`Real.log_mul` 把 log 拆开，m = lam·x + (1−lam)·y 消项），
  再用 `Real.one_sub_inv_le_log_of_pos`：log A ≥ 1 − A⁻¹，加权求和恰为
    (lam·x + (1−lam)·y) − (m/r)·(lam·s + (1−lam)·t) = m − m = 0。

本文件建立：

  1. `logsum_two`（核心工具）：上述两点逐项 log-sum 不等式；
  2. `kl_joint_convex`（核心定理）：KL(mix p₁p₂ ‖ mix q₁q₂) ≤ lam·KL(p₁‖q₁) + (1−lam)·KL(p₂‖q₂)
     （p、q 全部分量严格正）；
  3. `kl_convex_in_p_strict_positive`：把 RealKLConvexity.kl_convex_in_p 回收为本文件的特例
     （q₁ = q₂ = q，`mixDist lam q q = q`）；
  4. `logsum_finset`（核心工具）：有限加权 log-sum 不等式
     (Σ wᵢxᵢ)·log((Σ wᵢxᵢ)/(Σ wᵢsᵢ)) ≤ Σ wᵢ·xᵢ·log(xᵢ/sᵢ)（wᵢ ≥ 0、Σwᵢ = 1、xᵢ,sᵢ > 0）；
  5. `kl_joint_convex_sum`（核心定理）：有限加权联合凸
     KL(ΣᵢwᵢPᵢ ‖ ΣᵢwᵢQᵢ) ≤ Σᵢwᵢ·KL(Pᵢ‖Qᵢ)（Σwᵢ = 1、P、Q 分量严格正）。

**诚实边界**（本文件不证 / 不声称的）：

- **[重要] `(p,q) ↦ CE(p,q)` 的联合凸性是假命题**，本文件**不**声称任何 `ce_joint_convex`。
  这是任务稿中的一处数学错误。反例（k = 2，lam = 1/2）：
    p₁ = (1,0)、q₁ = (1,0)；p₂ = (0,1)、q₂ = (0,1)。
  于是 CE(p₁,q₁) = CE(p₂,q₂) = 0（含 0·log 0 项取 0），而混合
    p̄ = (1/2,1/2)、q̄ = (1/2,1/2)，CE(p̄,q̄) = (1/2)·log 2 + (1/2)·log 2 = log 2 > 0，
  即 CE(p̄,q̄) > (1/2)CE(p₁,q₁) + (1/2)CE(p₂,q₂)，凸性失败。
  根本原因：CE(p,q) = KL(p‖q) + H(p)，联合凸的 KL 加上**凹**的 H(p) 不再凸
  （单变量 Hessian 行列式 = −1/q² < 0）。故联合凸是 **KL 特有的**，本文件只对 KL 陈述。
  该反例已在文件尾部形式化为 `ce_not_joint_convex`（k = 2、lam = 1/2，机器验证）。
  RealKLConvexity 中已证的 `ce_convex_in_q`（固定 p、对 q 凸）仍然正确，不受此影响。
- `kl_convex_in_p`（RealKLConvexity）只在 p₁、p₂ 严格正下陈述（log 定义域）；
  本文件的所有凸性同样在严格正假设下陈述，含零分布的边界情形未展开。
- 未做：KL 的算子（Bregman）形式、Fisher 信息、连续分布 KL。

模型无关：任意有限 k（及加权的任意有限 n）。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-! ## 工具引理一：有限加权 log-sum 不等式（**全文件的一般形，权威位置**）

(Σ wᵢxᵢ)·log((Σ wᵢxᵢ)/(Σ wᵢsᵢ)) ≤ Σ wᵢ·xᵢ·log(xᵢ/sᵢ)（wᵢ ≥ 0、Σwᵢ = 1、xᵢ, sᵢ > 0）。
证明：令 m = Σwᵢxᵢ、r = Σwᵢsᵢ、Aᵢ = xᵢ·r/(sᵢ·m)，
差值 = Σwᵢ·xᵢ·log Aᵢ ≥ Σwᵢ·xᵢ·(1 − Aᵢ⁻¹) = m − (m/r)·Σwᵢsᵢ = 0。

**REFACTOR Step 3（v12）**：本引理原位于文件后段（"工具引理二"），与前面的两点版
`logsum_two` 各证一遍同型推理。现将**一般形前移**，`logsum_two` 改为它的 `Fin 2` 实例化
（省去 ~80 行重复证明）——同一原理在全库只证一次。 -/

lemma logsum_finset {ι : Type*} [Fintype ι] (w x s : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) :
    (∑ i, w i * x i) * Real.log ((∑ i, w i * x i) / (∑ i, w i * s i))
      ≤ ∑ i, w i * (x i * Real.log (x i / s i)) := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => h i)
    rw [hws] at hz
    norm_num at hz
  obtain ⟨i0, hi0⟩ := hex
  have hwi0 : 0 < w i0 := lt_of_le_of_ne (hw0 i0) (Ne.symm hi0)
  have hmpos : 0 < ∑ i, w i * x i :=
    lt_of_lt_of_le (mul_pos hwi0 (hx i0))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw0 i) (le_of_lt (hx i)))
        (Finset.mem_univ i0))
  have hrpos : 0 < ∑ i, w i * s i :=
    lt_of_lt_of_le (mul_pos hwi0 (hs i0))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw0 i) (le_of_lt (hs i)))
        (Finset.mem_univ i0))
  set m : ℝ := ∑ i, w i * x i with hm
  set r : ℝ := ∑ i, w i * s i with hr
  set A : ι → ℝ := fun i => x i * r / (s i * m) with hA
  have hApos : ∀ i, 0 < A i :=
    fun i => div_pos (mul_pos (hx i) hrpos) (mul_pos (hs i) hmpos)
  have hlogA : ∀ i, Real.log (A i)
      = (Real.log (x i) - Real.log (s i)) + (Real.log r - Real.log m) := by
    intro i
    have h1 : A i = (x i / s i) * (r / m) := by
      rw [hA]
      exact (div_mul_div_comm (x i) (s i) r m).symm
    rw [h1, Real.log_mul (ne_of_gt (div_pos (hx i) (hs i))) (ne_of_gt (div_pos hrpos hmpos)),
      Real.log_div (ne_of_gt (hx i)) (ne_of_gt (hs i)),
      Real.log_div (ne_of_gt hrpos) (ne_of_gt hmpos)]
  have hsplit : ∑ i, w i * (x i * Real.log (A i))
      = (∑ i, w i * (x i * Real.log (x i / s i))) + m * (Real.log r - Real.log m) := by
    have hterm : ∀ i, w i * (x i * Real.log (A i))
        = w i * (x i * Real.log (x i / s i)) + w i * x i * (Real.log r - Real.log m) := by
      intro i
      rw [hlogA i, Real.log_div (ne_of_gt (hx i)) (ne_of_gt (hs i))]
      ring
    calc ∑ i, w i * (x i * Real.log (A i))
        = ∑ i, (w i * (x i * Real.log (x i / s i))
            + w i * x i * (Real.log r - Real.log m)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, w i * (x i * Real.log (x i / s i)))
            + ∑ i, w i * x i * (Real.log r - Real.log m) := Finset.sum_add_distrib
      _ = (∑ i, w i * (x i * Real.log (x i / s i)))
            + (∑ i, w i * x i) * (Real.log r - Real.log m) := by rw [Finset.sum_mul]
      _ = (∑ i, w i * (x i * Real.log (x i / s i))) + m * (Real.log r - Real.log m) := by
            rw [← hm]
  have hdecomp : (∑ i, w i * (x i * Real.log (x i / s i))) - m * Real.log (m / r)
      = ∑ i, w i * (x i * Real.log (A i)) := by
    rw [hsplit, Real.log_div (ne_of_gt hmpos) (ne_of_gt hrpos)]
    ring
  have hb : ∀ i, w i * (x i * (1 - (A i)⁻¹)) ≤ w i * (x i * Real.log (A i)) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos (hApos i)) (le_of_lt (hx i)))
      (hw0 i)
  have hzero : ∑ i, w i * (x i * (1 - (A i)⁻¹)) = 0 := by
    have hAinv : ∀ i, (A i)⁻¹ = s i * m / (x i * r) := by
      intro i
      rw [hA, inv_div]
    have hterm : ∀ i, w i * (x i * (1 - (A i)⁻¹)) = w i * x i - (m / r) * (w i * s i) := by
      intro i
      rw [hAinv i]
      field_simp [ne_of_gt (hx i), ne_of_gt hrpos]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
    have h1 : (∑ i, w i * x i) = m := hm.symm
    have h2 : (∑ i, (m / r) * (w i * s i)) = m := by
      rw [← Finset.mul_sum]
      rw [show (∑ i, w i * s i) = r from hr.symm, div_mul_cancel₀ m (ne_of_gt hrpos)]
    rw [h1, h2, sub_self]
  have hlow : 0 ≤ ∑ i, w i * (x i * Real.log (A i)) := by
    calc 0 = ∑ i, w i * (x i * (1 - (A i)⁻¹)) := hzero.symm
      _ ≤ ∑ i, w i * (x i * Real.log (A i)) := Finset.sum_le_sum (fun i _ => hb i)
  have hD : 0 ≤ (∑ i, w i * (x i * Real.log (x i / s i))) - m * Real.log (m / r) := by
    rw [hdecomp]
    exact hlow
  linarith

/-! ## 工具引理二：两点逐项 log-sum 不等式（一般形的 `Fin 2` 实例）

**REFACTOR Step 3（v12）**：本引理此前有 ~80 行独立证明（与上面的 `logsum_finset` 同型、
各证一遍）。现收敛为 `logsum_finset` 在 `Fin 2` 上的实例化——**同一原理全库只证一次**。 -/

/-- 两点 log-sum 不等式（逐项形式）：
m = lam·x + (1−lam)·y、r = lam·s + (1−lam)·t ⟹
m·log(m/r) ≤ lam·x·log(x/s) + (1−lam)·y·log(y/t)（x, y, s, t > 0、lam ∈ [0,1]）。
【实现】`logsum_finset` 在 `Fin 2` 上取权重 `(lam, 1−lam)`、点 `(x, y)`、`(s, t)`。 -/
lemma logsum_two {x y s t lam : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (ht : 0 < t)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (lam * x + (1 - lam) * y) * Real.log ((lam * x + (1 - lam) * y) / (lam * s + (1 - lam) * t))
      ≤ lam * (x * Real.log (x / s)) + (1 - lam) * (y * Real.log (y / t)) := by
  have h := logsum_finset (w := ![lam, 1 - lam]) (x := ![x, y]) (s := ![s, t])
    (by intro i; fin_cases i <;> (simp; linarith [hlam0, hlam1]))
    (by simp [Fin.sum_univ_two])
    (by intro i; fin_cases i <;> simp [hx, hy])
    (by intro i; fin_cases i <;> simp [hs, ht])
  simpa [Fin.sum_univ_two] using h

/-! ## 定理一（核心）：KL 的联合凸性

(p, q) ↦ KL(p‖q) 联合凸：逐坐标用 `logsum_two` 相加。
p、q 分量严格正（log 定义域）。 -/

theorem kl_joint_convex (p1 p2 q1 q2 : Fin k → ℝ)
    (hp1 : ∀ a, 0 < p1 a) (hp2 : ∀ a, 0 < p2 a)
    (hq1 : ∀ a, 0 < q1 a) (hq2 : ∀ a, 0 < q2 a)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    kl (mixDist lam p1 p2) (mixDist lam q1 q2)
      ≤ lam * kl p1 q1 + (1 - lam) * kl p2 q2 := by
  have hp : ∀ a, 0 < mixDist lam p1 p2 a := mixDist_pos p1 p2 hp1 hp2 hlam0 hlam1
  have hq : ∀ a, 0 < mixDist lam q1 q2 a := mixDist_pos q1 q2 hq1 hq2 hlam0 hlam1
  rw [kl_as_sum_log_ratio (mixDist lam p1 p2) (mixDist lam q1 q2) hp hq,
    kl_as_sum_log_ratio p1 q1 hp1 hq1, kl_as_sum_log_ratio p2 q2 hp2 hq2]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h := logsum_two (hp1 a) (hp2 a) (hq1 a) (hq2 a) hlam0 hlam1
  simpa only [mixDist] using h

/-! ## 定理二：回收单侧结果（KL 对 p 凸）

取 q₁ = q₂ = q（`mixDist lam q q = q`），`kl_joint_convex` 退化为 RealKLConvexity.kl_convex_in_p 的内容。
命名注明「strict_positive」以区别于既有 `kl_convex_in_p`（陈述相同、路线不同：本证明经联合凸）。 -/

theorem kl_convex_in_p_strict_positive (p1 p2 q : Fin k → ℝ)
    (hp1 : ∀ a, 0 < p1 a) (hp2 : ∀ a, 0 < p2 a) (hq : ∀ a, 0 < q a)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    kl (mixDist lam p1 p2) q ≤ lam * kl p1 q + (1 - lam) * kl p2 q := by
  have h := kl_joint_convex p1 p2 q q hp1 hp2 hq hq hlam0 hlam1
  have hmix : mixDist lam q q = q := by
    funext a
    unfold mixDist
    ring
  rwa [hmix] at h


/-! ## 定理三（核心）：KL 的有限加权联合凸性

KL(ΣᵢwᵢPᵢ ‖ ΣᵢwᵢQᵢ) ≤ Σᵢwᵢ·KL(Pᵢ‖Qᵢ)（wᵢ ≥ 0、Σwᵢ = 1，P、Q 分量严格正）。
逐坐标用 `logsum_finset`，再 `Finset.sum_comm` 换序。 -/

theorem kl_joint_convex_sum {n : ℕ} (w : Fin n → ℝ) (P Q : Fin n → Fin k → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hP : ∀ i a, 0 < P i a) (hQ : ∀ i a, 0 < Q i a) :
    kl (fun a => ∑ i, w i * P i a) (fun a => ∑ i, w i * Q i a)
      ≤ ∑ i, w i * kl (P i) (Q i) := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => h i)
    rw [hws] at hz
    norm_num at hz
  obtain ⟨i0, hi0⟩ := hex
  have hwi0 : 0 < w i0 := lt_of_le_of_ne (hw0 i0) (Ne.symm hi0)
  have hmixP : ∀ a, 0 < ∑ i, w i * P i a := by
    intro a
    exact lt_of_lt_of_le (mul_pos hwi0 (hP i0 a))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw0 i) (le_of_lt (hP i a)))
        (Finset.mem_univ i0))
  have hmixQ : ∀ a, 0 < ∑ i, w i * Q i a := by
    intro a
    exact lt_of_lt_of_le (mul_pos hwi0 (hQ i0 a))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw0 i) (le_of_lt (hQ i a)))
        (Finset.mem_univ i0))
  rw [kl_as_sum_log_ratio _ _ hmixP hmixQ]
  have hR : ∑ i, w i * kl (P i) (Q i)
      = ∑ i, w i * ∑ a, P i a * Real.log (P i a / Q i a) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [kl_as_sum_log_ratio (P i) (Q i) (fun a => hP i a) (fun a => hQ i a)]
  rw [hR]
  calc ∑ a, (∑ i, w i * P i a) * Real.log ((∑ i, w i * P i a) / (∑ i, w i * Q i a))
      ≤ ∑ a, ∑ i, w i * (P i a * Real.log (P i a / Q i a)) :=
        Finset.sum_le_sum (fun a _ =>
          logsum_finset w (fun i => P i a) (fun i => Q i a) hw0 hws
            (fun i => hP i a) (fun i => hQ i a))
    _ = ∑ i, w i * ∑ a, P i a * Real.log (P i a / Q i a) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]

/-! ## 附注（形式化反例）：CE 的联合凸性**不成立**

任务稿建议的 `ce_joint_convex`（(p,q) ↦ CE(p,q) 联合凸）是**假命题**，下面给出机器验证的反例。
取 k = 2、lam = 1/2，两张 one-hot 分布各自混合：

  p₁ = q₁ = e₀、p₂ = q₂ = e₁（eᵢ 为 one-hot），
  CE(p₁,q₁) = CE(p₂,q₂) = 0，而混合 p̄ = q̄ = (1/2,1/2) 给出
  CE(p̄,q̄) = (1/2)·log(1/2) + (1/2)·log(1/2) = −log(1/2) = log 2 > 0，

故 CE(mix p ‖ mix q) > (1/2)·CE(p₁,q₁) + (1/2)·CE(p₂,q₂)，凸性失败。
根因：CE(p,q) = KL(p‖q) + H(p)，联合凸的 KL 加上**凹**的 H(p) 后不再凸
（单变量 Hessian 行列式 = −1/q² < 0）。联合凸是 KL 特有的。 -/

/-- one-hot 向量 eᵢ（k = 2）：eᵢ i = 1，否则 0。 -/
def pt2 (i : Fin 2) : Fin 2 → ℝ := fun a => if a = i then 1 else 0

/-- 形式化反例：CE 不是联合凸的（k = 2、lam = 1/2、两个 one-hot 分布的混合）。 -/
theorem ce_not_joint_convex :
    ¬ ((1 : ℝ) / 2 * crossEntropy (pt2 0) (pt2 0)
        + (1 : ℝ) / 2 * crossEntropy (pt2 1) (pt2 1)
        ≥ crossEntropy (mixDist ((1 : ℝ) / 2) (pt2 0) (pt2 1))
            (mixDist ((1 : ℝ) / 2) (pt2 0) (pt2 1))) := by
  intro h
  have h00 : crossEntropy (pt2 0) (pt2 0) = 0 := by
    simp [crossEntropy, pt2, Fin.sum_univ_two]
  have h11 : crossEntropy (pt2 1) (pt2 1) = 0 := by
    simp [crossEntropy, pt2, Fin.sum_univ_two]
  have hmix : mixDist ((1 : ℝ) / 2) (pt2 0) (pt2 1) = fun _ : Fin 2 => (1 : ℝ) / 2 := by
    funext a
    fin_cases a <;> simp [mixDist, pt2] <;> norm_num
  have hm : crossEntropy (fun _ : Fin 2 => (1 : ℝ) / 2) (fun _ : Fin 2 => (1 : ℝ) / 2)
      = Real.log 2 := by
    unfold crossEntropy
    rw [Fin.sum_univ_two]
    have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hlog]
    ring
  rw [h00, h11, hmix, hm] at h
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end Lattice
