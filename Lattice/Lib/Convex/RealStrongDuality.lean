import Mathlib
import Lattice.Lib.Convex.RealDualTheory
/-!
# LATTICE: 强对偶与 Slater 条件 —— 零间隙判据、紧致支撑下的间隙公式、Slater 边界

RealDualTheory 建立了拉格朗日对偶的**弱**半边：L(x,λ) = f(x) + Σ_i λ_i g_i(x)、
λ ≥ 0、可行 x ⟹ L(x,λ) ≤ f(x)，并把「零间隙」作为**假设**接收
（`strong_duality_convex_case`：零间隙 ⟹ 互补松弛）。本文件补上强对偶一侧的结构：

  1. `SlaterCondition`（def）：∃ x, ∀ i, g_i(x) < 0（严格可行点）；
  2. `slater_implies_feasible`：Slater ⟹ 可行点存在；
  3. `slater_sum_strictly_negative` / `slater_lagrangian_lt`：Slater 点处任何
     **非零**乘子都使 Σ λ_i g_i < 0，故 L(x̄,λ) < f(x̄)（Slater 点是拉格朗日函数的
     严格改进点，间隙不可能在该点由非零乘子关闭）；
  4. `zero_gap_iff_complementary_slackness`（**核心**）：在有限支撑 s 上、x ∈ s、
     λ ≥ 0、x 可行时，
         dualValue(λ) = f(x)  ⟺  (∀i, λ_i g_i(x) = 0)  ∧  x 在 s 上极小化 L(·,λ)。
     前向：由弱对偶与 inf 的极小性夹出等式；后向：互补松弛给出 L(x,λ) = f(x)，
     再由 x 的极小性把 dualValue 夹到 L(x,λ)。
     **诚实修正**：仅有「互补松弛」**不足以**推出零间隙（需同时要求 x 极小化 L——
     否则 ⨅L ≤ L(x,λ) = f(x) 是相反方向），故陈述中包含第二项；
     `zero_gap_implies_complementary_slackness` 给出常用的前向投影。
  5. `strong_duality_under_compactness`（**紧致支撑下的间隙公式**）：有限（紧致）支撑 s
     上 x ∈ s 且 x 极小化 L(·,λ) ⟹ **对偶 inf 可达**且间隙**恰好**为
         dualValue(λ) = f(x) + Σ_i λ_i g_i(x)，
     即 f(x) − dualValue(λ) = −Σ_i λ_i g_i(x)；配合 λ ≥ 0、x 可行即得非负间隙。
     这是「紧致性给可达性、互补松弛项给间隙数值」的精确分解。
  6. `dual_attainment`：零间隙（f(x) ≤ dualValue(λ)）⟹ 对偶值等于原值、互补松弛成立、
     且 x 在 s 上极小化 L(·,λ)——即**对偶最优可达**（λ 是最优乘子）。
  7. `slater_implies_strong_duality`（**Slater 边界情形**）：若证书点 x 本身是 Slater 点
     （∀i, g_i(x) < 0），则零间隙（f(x) ≤ dualValue(λ)）迫使 **λ = 0**，
     且仍有 dualValue(λ) = f(x)。即：Slater 点位于可行域内部时最优乘子必消失
     （乘子只编码**边界**处的约束活性）。
  8. `slater_not_sufficient_discrete`（**反例，诚实边界**）：Slater 条件对**离散支撑**
     不足以保证强对偶。支撑 {−1,1}、约束 g(x) = x（Slater 点 x̄ = −1）、
     f(−1) = 0、f(1) = −100：原问题最优值（唯一可行点 −1 处）= 0，而对偶最优值 = −50，
     且对任意 λ ≥ 0 都有 dualValue(λ) ≤ −50 < 0。故间隙恒 ≥ 50 > 0。

诚实边界：
  · **「凸 + Slater ⟹ 零间隙」的完整强对偶定理在本文件未证明**：其核心是凸集的**分离定理**
    （存在支撑超平面 ⟺ 存在最优乘子）。
    ⚠ **更正（CORRECTIONS B6）**：本文件早期版本在此声称「mathlib 4.14 没有该形式（分离定理）」——
    **该论断为假**。mathlib 4.14 **有**几何 Hahn–Banach 分离定理，位于
    `Mathlib/Analysis/NormedSpace/HahnBanach/Separation.lean`
    （`geometric_hahn_banach_closed_point` 等，签名见 `RealSeparation` 头部 docstring 的
    #check 清单：`geometric_hahn_banach_*` 一族）。
    真正缺的**不是工具**，而是把分离定理**接到拉格朗日对偶的桥**（分离泛函 → 支撑超平面 →
    最优乘子存在性）；该桥已由 `RealSeparation.strong_duality_convex_slater` 补出
    （4.14 的 `geometric_hahn_banach_*` 直接可用），本文件未改动、仍按下述方案呈现。
    （另：下半连续凸函数的次梯度理论仍确有缺口，`Mathlib` 未提供 `Convex.subderiv`。）
    本文件因此给出：(i) 零间隙的**等价刻画**
    （定理 4），(ii) 紧致性单独贡献的**可达性 + 精确间隙公式**（定理 5、6），
    (iii) Slater 条件下的**边界结论**（定理 7），(iv) 显示 Slater 在离散支撑下**不充分**
    的显式反例（定理 8）。此即「保留零间隙 ⟺ 互补松弛 + 条件性陈述」的方案。
  · 定理 5 表明：有限支撑下 ⨅ 总是**被某点达到**（ℝ 上 iInf 的约定值陷阱被 Finset.inf'
    完全规避），因此强对偶在有限支撑下的**唯一障碍**就是互补松弛项 Σ λ_i g_i 是否为零。
  · 反例同时说明：强对偶依赖可行集的**凸性/连续性**（Slater 保证内点），而不仅是 Slater
    条件本身——这是把「凸 + Slater」写成两个独立假设的必要性所在。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## 一、Slater 条件 -/

/-- **Slater 条件**：存在严格可行点 x（∀i, g_i(x) < 0）。 -/
def SlaterCondition (g : Fin n → ℝ → ℝ) : Prop :=
  ∃ x : ℝ, ∀ i, g i x < 0

/-- Slater 条件 ⟹ 可行点存在。 -/
theorem slater_implies_feasible (g : Fin n → ℝ → ℝ) (h : SlaterCondition g) :
    ∃ x : ℝ, ∀ i, g i x ≤ 0 := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun i => le_of_lt (hx i)⟩

/-- **Slater 点的严格负性和**：x̄ 严格可行、λ ≥ 0 且某分量 λ_{i₀} > 0
⟹ Σ_i λ_i g_i(x̄) < 0（逐项 ≤ 0，在 i₀ 处严格负）。 -/
theorem slater_sum_strictly_negative (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hslater : ∀ i, g i x < 0) (hlam : ∀ i, 0 ≤ lam i) (i₀ : Fin n) (hi₀ : 0 < lam i₀) :
    ∑ i, lam i * g i x < 0 := by
  have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin n)), lam i * g i x ≤ (0 : ℝ) :=
    fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (le_of_lt (hslater i))
  have hstrict : ∃ i ∈ (Finset.univ : Finset (Fin n)), lam i * g i x < (0 : ℝ) :=
    ⟨i₀, Finset.mem_univ i₀, mul_neg_of_pos_of_neg hi₀ (hslater i₀)⟩
  have := Finset.sum_lt_sum hnonpos hstrict
  simpa using this

/-- **Slater 点处拉格朗日函数严格低于目标**：非零乘子在严格可行点必使 L(x̄,λ) < f(x̄)。 -/
theorem slater_lagrangian_lt (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hslater : ∀ i, g i x < 0) (hlam : ∀ i, 0 ≤ lam i) (i₀ : Fin n) (hi₀ : 0 < lam i₀) :
    Lagrangian f g x lam < f x := by
  have hsum := slater_sum_strictly_negative g x lam hslater hlam i₀ hi₀
  unfold Lagrangian
  linarith

/-! ## 二、零间隙 ⟺ 互补松弛 + 对偶极小性 -/

/-- **零间隙的完整刻画（有限支撑）**：x ∈ s、λ ≥ 0、x 可行时，
    dualValue(λ) = f(x)  ⟺  (∀i, λ_i g_i(x) = 0) 且 x 在 s 上极小化 L(·,λ)。

说明：两个条件缺一不可。仅有互补松弛只给出 L(x,λ) = f(x) ≥ dualValue(λ)
（因 dualValue 是 inf），要取等必须再要求 L(x,λ) = dualValue(λ)，即 x 极小化 L。 -/
theorem zero_gap_iff_complementary_slackness (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ)
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0) :
    dualValue f g s hs lam = f x ↔
      ((∀ i, lam i * g i x = 0) ∧
        ∀ y ∈ s, Lagrangian f g x lam ≤ Lagrangian f g y lam) := by
  constructor
  · intro h
    have hlow : Lagrangian f g x lam ≤ f x := lagrangian_lower_bound f g x lam hlam hfeas
    have hinf : dualValue f g s hs lam ≤ Lagrangian f g x lam := by
      simp only [dualValue]
      exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hxs
    have hL : Lagrangian f g x lam = f x :=
      le_antisymm hlow (by rw [← h]; exact hinf)
    have hsum : ∑ i, lam i * g i x = 0 := by
      have hh := hL
      unfold Lagrangian at hh
      linarith
    refine ⟨fun i => ?_, fun y hy => ?_⟩
    · exact (Finset.sum_eq_zero_iff_of_nonpos
        (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeas i))).mp hsum i
        (Finset.mem_univ i)
    · rw [hL, ← h]
      simp only [dualValue]
      exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hy
  · rintro ⟨hcs, hmin⟩
    have hsum : ∑ i, lam i * g i x = 0 := Finset.sum_eq_zero fun i _ => hcs i
    have hL : Lagrangian f g x lam = f x := by
      unfold Lagrangian
      rw [hsum]
      ring
    have hinf : dualValue f g s hs lam ≤ Lagrangian f g x lam := by
      simp only [dualValue]
      exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hxs
    have hle : Lagrangian f g x lam ≤ dualValue f g s hs lam := by
      simp only [dualValue]
      exact Finset.le_inf' hs (fun x' => Lagrangian f g x' lam) hmin
    rw [← hL]
    exact le_antisymm hinf hle

/-- 零间隙 ⟹ 互补松弛（定理 4 的前向投影）。 -/
theorem zero_gap_implies_complementary_slackness (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ)
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hgap : dualValue f g s hs lam = f x) :
    ∀ i, lam i * g i x = 0 :=
  ((zero_gap_iff_complementary_slackness f g s hs x hxs lam hlam hfeas).mp hgap).1

/-! ## 三、紧致支撑：对偶可达 + 精确间隙公式 -/

/-- **紧致支撑下的强对偶（间隙公式）**：有限（紧致）支撑 s 上，若 x ∈ s 极小化 L(·,λ)，
则对偶 inf **可达**且间隙有精确表达式

    dualValue(λ) = f(x) + Σ_i λ_i g_i(x)，

即 f(x) − dualValue(λ) = −Σ_i λ_i g_i(x)。配合 λ ≥ 0、x 可行（弱对偶）即得非负间隙；
零间隙当且仅当互补松弛项为零。

证明：`Finset.inf'_le` 给出 dualValue ≤ L(x,λ)，`Finset.le_inf'` 配合极小性给出
L(x,λ) ≤ dualValue，两边夹紧后展开 Lagrangian 的定义。 -/
theorem strong_duality_under_compactness (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ)
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ)
    (hmin : ∀ y ∈ s, Lagrangian f g x lam ≤ Lagrangian f g y lam) :
    dualValue f g s hs lam = f x + ∑ i, lam i * g i x := by
  have hinf : dualValue f g s hs lam ≤ Lagrangian f g x lam := by
    simp only [dualValue]
    exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hxs
  have hle : Lagrangian f g x lam ≤ dualValue f g s hs lam := by
    simp only [dualValue]
    exact Finset.le_inf' hs (fun x' => Lagrangian f g x' lam) hmin
  have hL : dualValue f g s hs lam = Lagrangian f g x lam := le_antisymm hinf hle
  rw [hL, Lagrangian]

/-- **对偶最优可达**：零间隙（f(x) ≤ dualValue(λ)）⟹ 对偶值等于原值、互补松弛成立、
且 x 在 s 上极小化 L(·,λ)——λ 即（有限支撑意义下的）最优乘子。 -/
theorem dual_attainment (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (s : Finset ℝ) (hs : s.Nonempty)
    (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hfeas : ∀ i, g i x ≤ 0) (hgap : f x ≤ dualValue f g s hs lam) :
    dualValue f g s hs lam = f x ∧ (∀ i, lam i * g i x = 0) ∧
      ∀ y ∈ s, Lagrangian f g x lam ≤ Lagrangian f g y lam := by
  have hlow : Lagrangian f g x lam ≤ f x := lagrangian_lower_bound f g x lam hlam hfeas
  have hinf : dualValue f g s hs lam ≤ Lagrangian f g x lam := by
    simp only [dualValue]
    exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hxs
  have hL : Lagrangian f g x lam = f x := le_antisymm hlow (le_trans hgap hinf)
  have hvaleq : dualValue f g s hs lam = f x := le_antisymm (le_trans hinf (le_of_eq hL)) hgap
  have hsum : ∑ i, lam i * g i x = 0 := by
    have hh := hL
    unfold Lagrangian at hh
    linarith
  refine ⟨hvaleq, fun i => ?_, fun y hy => ?_⟩
  · exact (Finset.sum_eq_zero_iff_of_nonpos
      (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeas i))).mp hsum i
      (Finset.mem_univ i)
  · rw [hL, ← hvaleq]
    simp only [dualValue]
    exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hy

/-! ## 四、Slater 边界情形：最优乘子消失 -/

/-- **Slater 边界情形（强对偶 + λ = 0）**：若证书点 x 本身是 **Slater 点**
（∀i, g_i(x) < 0）、λ ≥ 0、x 可行且在该点零间隙成立（f(x) ≤ dualValue(λ)），
则 **λ = 0**，且 dualValue(λ) = f(x)。

意义：Slater 点位于可行域**内部**，零间隙蕴含的互补松弛 λ_i g_i(x) = 0 与
g_i(x) < 0 迫使每个 λ_i = 0——乘子只编码**边界**处的约束活性。这是完整强对偶定理中
「Slater ⟹ 最优乘子存在」一侧所能达到的边界结论。 -/
theorem slater_implies_strong_duality (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ)
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ)
    (hslater : ∀ i, g i x < 0) (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hgap : f x ≤ dualValue f g s hs lam) :
    lam = 0 ∧ dualValue f g s hs lam = f x := by
  obtain ⟨hvaleq, hcs, -⟩ := dual_attainment f g s hs x hxs lam hlam hfeas hgap
  refine ⟨?_, hvaleq⟩
  funext i
  exact (mul_eq_zero.mp (hcs i)).resolve_right (ne_of_lt (hslater i))

/-- Slater 点的**乘子消失**（定理 7 的投影）。 -/
theorem slater_multiplier_vanishes (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ)
    (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ)
    (hslater : ∀ i, g i x < 0) (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hgap : f x ≤ dualValue f g s hs lam) :
    lam = 0 :=
  (slater_implies_strong_duality f g s hs x hxs lam hslater hlam hfeas hgap).1

/-! ## 五、反例：Slater 条件对离散支撑不充分 -/

/-- 反例的目标函数：f(1) = −100，其余点取 0（故 f(−1) = 0）。 -/
def slaterCounterF (x : ℝ) : ℝ := if x = 1 then -100 else 0

/-- 反例的约束族（单约束 g(x) = x ≤ 0）。 -/
def slaterCounterG : Fin 1 → ℝ → ℝ := fun _ x => x

/-- 反例的有限支撑 {−1, 1}。 -/
def slaterCounterSupport : Finset ℝ := {-1, 1}

/-- 支撑非空。 -/
theorem slaterCounterSupport_nonempty : slaterCounterSupport.Nonempty :=
  ⟨-1, by simp [slaterCounterSupport]⟩

/-- 反例中 f(−1) = 0。 -/
theorem slaterCounterF_neg_one : slaterCounterF (-1) = 0 := by
  unfold slaterCounterF
  rw [if_neg (by norm_num : ¬((-1 : ℝ) = 1))]

/-- 反例中 f(1) = −100。 -/
theorem slaterCounterF_one : slaterCounterF 1 = -100 := by
  unfold slaterCounterF
  rw [if_pos rfl]

/-- 反例中 L(y, λ) = f(y) + λ₀·y。 -/
theorem slaterCounter_lagrangian (lam : Fin 1 → ℝ) (y : ℝ) :
    Lagrangian slaterCounterF slaterCounterG y lam = slaterCounterF y + lam 0 * y := by
  simp [Lagrangian, slaterCounterG, Fin.sum_univ_one]

/-- **反例（诚实边界）**：Slater 条件在**离散支撑**下不足以保证强对偶。

支撑 s = {−1, 1}、约束 g(x) = x ≤ 0（Slater 点 x̄ = −1：g(x̄) = −1 < 0）、
f(−1) = 0、f(1) = −100。此时：
  · −1 是支撑内**唯一**可行点（故原问题最优值 = f(−1) = 0）；
  · 对任意 λ ≥ 0，dualValue(λ) = min(−λ, −100 + λ) ≤ −50；
  · 取 λ = 50 时 dualValue = −50（且 −50 是全局最大值）。
所以间隙恒 ≥ 50 > 0——**Slater 条件本身不充分**，强对偶还需可行集的凸性/连续性
（连续凸情形下 Slater 保证内点，支撑的凸包才可能承载分离定理）。 -/
theorem slater_not_sufficient_discrete :
    (∀ i : Fin 1, slaterCounterG i (-1) < 0) ∧
    (∀ x ∈ slaterCounterSupport, (∀ i, slaterCounterG i x ≤ 0) → x = -1) ∧
    (∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam ≤ -50) ∧
    (∃ lam : Fin 1 → ℝ, 0 ≤ lam 0 ∧
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam = -50) ∧
    (∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam < slaterCounterF (-1)) := by
  have hSlater : ∀ i : Fin 1, slaterCounterG i (-1) < 0 := by
    intro i; norm_num [slaterCounterG]
  have hUniq : ∀ x ∈ slaterCounterSupport, (∀ i, slaterCounterG i x ≤ 0) → x = -1 := by
    intro x hx hfeas
    simp only [slaterCounterSupport, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · have h1 : (1 : ℝ) ≤ 0 := by simpa [slaterCounterG] using hfeas 0
      exact absurd h1 (by norm_num)
  have hinf_le : ∀ (lam : Fin 1 → ℝ) (y : ℝ), y ∈ slaterCounterSupport →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam
        ≤ Lagrangian slaterCounterF slaterCounterG y lam := by
    intro lam y hy
    simp only [dualValue]
    exact Finset.inf'_le (s := slaterCounterSupport)
      (fun x' => Lagrangian slaterCounterF slaterCounterG x' lam) hy
  have hBound : ∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam ≤ -50 := by
    intro lam hlam
    have h1 := hinf_le lam (-1) (by simp [slaterCounterSupport])
    have h2 := hinf_le lam 1 (by simp [slaterCounterSupport])
    simp only [slaterCounter_lagrangian, slaterCounterF_neg_one, slaterCounterF_one] at h1 h2
    linarith
  have hAttain : ∃ lam : Fin 1 → ℝ, 0 ≤ lam 0 ∧
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam = -50 := by
    have h50 : Lagrangian slaterCounterF slaterCounterG (-1) (fun _ => 50) = -50 := by
      rw [slaterCounter_lagrangian, slaterCounterF_neg_one]
      norm_num
    refine ⟨fun _ => 50, by norm_num, le_antisymm ?_ ?_⟩
    · have h1 := hinf_le (fun _ => 50) (-1) (by simp [slaterCounterSupport])
      rwa [h50] at h1
    · have hle : Lagrangian slaterCounterF slaterCounterG (-1) (fun _ => 50)
          ≤ dualValue slaterCounterF slaterCounterG slaterCounterSupport
            slaterCounterSupport_nonempty (fun _ => 50) := by
        simp only [dualValue]
        refine Finset.le_inf' slaterCounterSupport_nonempty
          (fun x' => Lagrangian slaterCounterF slaterCounterG x' (fun _ => 50)) ?_
        intro y hy
        show Lagrangian slaterCounterF slaterCounterG (-1) (fun _ => 50)
            ≤ Lagrangian slaterCounterF slaterCounterG y (fun _ => 50)
        have hy' : Lagrangian slaterCounterF slaterCounterG y (fun _ => 50) = -50 := by
          rw [slaterCounter_lagrangian]
          simp only [slaterCounterSupport, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · rw [slaterCounterF_neg_one]; norm_num
          · rw [slaterCounterF_one]; norm_num
        linarith [h50, hy']
      rwa [h50] at hle
  have hStrict : ∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam < slaterCounterF (-1) := by
    intro lam hlam
    have h := hBound lam hlam
    rw [slaterCounterF_neg_one]
    linarith
  exact ⟨hSlater, hUniq, hBound, hAttain, hStrict⟩

/-! ## 注：强对偶的证明义务分解
  完整定理「f、g_i 凸 ∧ Slater 条件 ∧ 适当紧致性 ⟹ 对偶间隙为零」的证明义务可分解为三步：
  (A) **弱对偶**：λ ≥ 0、x 可行 ⟹ L(x,λ) ≤ f(x)（RealDualTheory）；
  (B) **互补松弛 ⟸ 零间隙**：定理 4 与 RealDualTheory 的 `strong_duality_convex_case`；
  (C) **零间隙的构造**：需分离定理给出最优乘子 λ*，使 x* 极小化 L(·,λ*)。本文件**未证** (C)。
      注意 **更正（CORRECTIONS B6）**：此处早期版本写作「mathlib 4.14 缺此工具」——**该论断为假**：
      4.14 **有** `geometric_hahn_banach_closed_point` 等真分离定理（见 `RealSeparation`），
      缺的只是「分离 → 支撑超平面 → 最优乘子」这一步桥接；该桥已由
      `RealSeparation.strong_duality_convex_slater` 在凸 + Slater 假设下补出。
      （真正的缺口是下半连续凸函数的次梯度，见 `RealSubgradient`。）
  本文件把 (A)(B) 补全为等价刻画，并把 (C) 的两种可证替代（紧致支撑下的可达性 + 精确
  间隙公式；Slater 内部点的乘子消失）与「Slater 对离散支撑不充分」的反例一并给出。 -/

end Lattice
