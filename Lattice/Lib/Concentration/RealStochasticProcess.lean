import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: 随机过程基座 —— 有限纤维滤链、条件期望（纤维均值）、塔性质、鞅差

RealHoeffding / RealSamplingBoost 用「有限样本空间 + 均匀概率」处理独立副本，
但没有**滤链与条件期望**的结构。本文件给出随机过程的基座（有限计数 / 纤维版）：

设定：有限样本空间 `α`（`Fintype`），信息由投影 `π : α → β` 给出（σ-代数
σ(π) = π 的纤维分割）；**条件期望 = 纤维均值**
`condExpFiber π X b = (∑ a ∈ fiber π b, X a) / |fiber π b|`（空纤维约定为 0）。

定理链（全部完整证明，无 sorry）：
  1. `card_mul_condExpFiber`（**引擎**）：`|fiber π b| · E[X | π](b) = ∑_{a ∈ fiber π b} X a`
     —— 含空纤维情形（两边皆为 0），它是后面一切求和恒等式的枢纽。
  2. `fiber_sum_eq`：`∑_b ∑_{a ∈ fiber π b} X a = ∑_a X a`（纤维分割的双计数，
     直接调用 `Finset.sum_fiberwise`）。
  3. `sum_card_mul_condExpFiber`：`∑_b |fiber π b| · E[X|π](b) = ∑_a X a`
     —— **全期望公式**（纤维加权平均 = 总平均）。
  4. `condExpFiber_const`：常值函数的条件期望 = 该常数（非空纤维）。
  5. `condExpFiber_add` / `condExpFiber_smul`：**条件期望的线性性**
     （有限情形无需可积性假设）。
  6. `condExpFiber_self_of_adapted`：若 `X` 关于 π 可测（纤维常值，`AdaptedTo`），
     则 `E[X|π](π a) = X a` —— 条件期望保持 σ(π)-可测函数。
  7. `fiber_sum_eq_filtered_fiber_sum`（**塔性质的求和形式**）：细纤维 `π` 与粗纤维
     `g ∘ π`（`g : β → γ`）满足
     `∑_{a ∈ 粗纤维 c} X a = ∑_{b : g b = c} ∑_{a ∈ 细纤维 b} X a`
     （`Finset.sum_fiberwise` + 集合恒等式 `filter_filter_fiber`）。
  8. `tower_property`（**塔性质，核心**）：
     `|粗纤维 c| · E[X | 粗](c) = ∑_{b : g b = c} |细纤维 b| · E[X | 细](b)`，
     即 `E[E[X|F₁]|F₂] = E[X|F₂]`（F₂ ⊆ F₁ 为粗信息）的**精确纤维加权形式**。
     注：粗侧按**纤维大小加权**（这正是均匀测度下条件期望的正确权重）。
  9. `tower_property_div`：除以 `|粗纤维 c|` 的条件期望形式。
 10. `condZeroMean_iff_condExpFiber_eq_zero`：纤维均值为零 ⟺ 条件期望恒零。
 11. `martingale_def_equiv`（**鞅 ⟺ 条件期望保持**）：鞅差 `MartingaleDiff π d`
     ⟺ `E[d|π] = 0` 且对任意 π-可测加项 `Y`，`E[Y + d | π] = E[Y | π]`。

**#check 结果（mathlib 4.14 实测）**：`MeasureTheory.Filtration` / `Adapted` /
`Martingale` / 记号 `μ[f|m]` / `MeasureTheory.condexp_condexp_of_le`（真正测度论语境下的
滤链与塔性质）确实存在（注意它们在 `MeasureTheory` 命名空间，而非 `ProbabilityTheory`）。
本文件**不引用**它们，而给出自足的有限纤维版本——原因见下。

**诚实假设与降级（重要）**：
- 本文件是**有限计数 / 纤维**版本，不是全测度论版本：样本空间有限、概率均匀
  （每个样本点等权），条件期望按纤维**算术平均**定义，而非 mathlib 的
  `MeasureTheory.condexp`（条件是 `L¹` 投影 / a.e. 唯一性）。
- 因此**塔性质在离散均匀测度下严格成立**（定理 8），且不需要可积性 / σ-有限性
  等技术假设；但它**不能直接替代**测度论塔性质的一般情形。
- 塔性质的粗侧权重是**纤维基数**（`|细纤维 b|`），而非条件概率测度下的均匀权重
  ——这是均匀总测度下「先细分再粗化」必须的加权，如实陈述。
- 定理 11 的「鞅」是**鞅差 / 条件均值保持**形式（有限滤链单步），不含多期滤链
  与可选停止等结构。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {α β γ : Type*} [Fintype α] [DecidableEq β]

/-! ## 一、纤维与纤维均值条件期望 -/

/-- **π-纤维**：映射到 `b` 的样本点集合 `{a | π a = b}`（σ(π) 的原子）。 -/
def fiber (π : α → β) (b : β) : Finset α := Finset.univ.filter (fun a => π a = b)

/-- **有限条件期望（纤维均值）**：`E[X | σ(π)](b) = (∑_{a ∈ fiber π b} X a) / |fiber π b|`；
空纤维（`b` 不被 π 命中）约定为 0。 -/
def condExpFiber (π : α → β) (X : α → ℝ) (b : β) : ℝ :=
  if (fiber π b).card = 0 then 0 else (∑ a in fiber π b, X a) / ((fiber π b).card : ℝ)

/-- **引擎恒等式**：`|fiber π b| · E[X|π](b) = ∑_{a ∈ fiber π b} X a`（空纤维时两边为 0）。 -/
theorem card_mul_condExpFiber (π : α → β) (X : α → ℝ) (b : β) :
    ((fiber π b).card : ℝ) * condExpFiber π X b = ∑ a in fiber π b, X a := by
  by_cases h : (fiber π b).card = 0
  · rw [h, Finset.card_eq_zero.mp h]
    simp [condExpFiber]
  · rw [condExpFiber, if_neg h]
    field_simp

/-- **纤维分割双计数**：按 π 的纤维分组求和 = 全空间求和。 -/
theorem fiber_sum_eq [Fintype β] (π : α → β) (X : α → ℝ) :
    ∑ b, ∑ a in fiber π b, X a = ∑ a, X a :=
  Finset.sum_fiberwise (Finset.univ : Finset α) π X

/-- **全期望公式**：`∑_b |fiber π b| · E[X|π](b) = ∑_a X a`。 -/
theorem sum_card_mul_condExpFiber [Fintype β] (π : α → β) (X : α → ℝ) :
    ∑ b, ((fiber π b).card : ℝ) * condExpFiber π X b = ∑ a, X a := by
  simp_rw [card_mul_condExpFiber]
  exact fiber_sum_eq π X

/-! ## 二、条件期望的基本性质 -/

/-- 常值函数的条件期望等于该常数（非空纤维）。 -/
theorem condExpFiber_const (π : α → β) (c : ℝ) (b : β) (h : (fiber π b).card ≠ 0) :
    condExpFiber π (fun _ => c) b = c := by
  have h1 := card_mul_condExpFiber π (fun _ => c) b
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr h) h1

/-- **线性性（加法）**：`E[X + Y | π] = E[X | π] + E[Y | π]`（有限情形无需可积性）。 -/
theorem condExpFiber_add (π : α → β) (X Y : α → ℝ) (b : β) :
    condExpFiber π (fun a => X a + Y a) b = condExpFiber π X b + condExpFiber π Y b := by
  by_cases h : (fiber π b).card = 0
  · simp [condExpFiber, h]
  · rw [condExpFiber, condExpFiber, condExpFiber, if_neg h, if_neg h, if_neg h]
    rw [Finset.sum_add_distrib]
    field_simp

/-- **线性性（数乘）**：`E[c · X | π] = c · E[X | π]`。 -/
theorem condExpFiber_smul (π : α → β) (X : α → ℝ) (c : ℝ) (b : β) :
    condExpFiber π (fun a => c * X a) b = c * condExpFiber π X b := by
  by_cases h : (fiber π b).card = 0
  · simp [condExpFiber, h]
  · rw [condExpFiber, condExpFiber, if_neg h, if_neg h, ← Finset.mul_sum]
    field_simp

/-- **适应性**（σ(π)-可测）：`X` 在 π 的每个纤维上取常值。 -/
def AdaptedTo (π : α → β) (X : α → ℝ) : Prop := ∀ a a', π a = π a' → X a = X a'

/-- **条件期望保持可测函数**：`X` 关于 π 可测 ⟹ `E[X|π](π a) = X a`。 -/
theorem condExpFiber_self_of_adapted (π : α → β) (X : α → ℝ) (hX : AdaptedTo π X) (a : α) :
    condExpFiber π X (π a) = X a := by
  have hmem : a ∈ fiber π (π a) := by simp [fiber]
  have hpos : 0 < (fiber π (π a)).card := Finset.card_pos.mpr ⟨a, hmem⟩
  have hne : (fiber π (π a)).card ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  rw [condExpFiber, if_neg hne]
  have hconst : ∀ b ∈ fiber π (π a), X b = X a := by
    intro b hb
    exact hX b a (by simpa [fiber] using hb)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ## 三、塔性质（细纤维 → 粗纤维） -/

/-- **纤维过滤恒等式**：`(粗纤维 c) ∩ (细纤维 b)` 等于 `细纤维 b`（当 `g b = c`）
否则为空。 -/
lemma filter_filter_fiber (π : α → β) (g : β → γ) [DecidableEq γ] (c : γ) (b : β) :
    (Finset.univ.filter (fun a => g (π a) = c)).filter (fun a => π a = b)
      = if g b = c then fiber π b else ∅ := by
  by_cases hb : g b = c
  · rw [if_pos hb]
    ext a
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; exact hb, h2⟩
  · rw [if_neg hb]
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro a ha
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hb (by rw [← ha.2]; exact ha.1)

/-- **塔性质的求和形式**：粗纤维上的求和 = 按细纤维分组的二重求和。 -/
theorem fiber_sum_eq_filtered_fiber_sum [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ]
    (X : α → ℝ) (c : γ) :
    ∑ a in fiber (fun a => g (π a)) c, X a
      = ∑ b in (Finset.univ : Finset β).filter (fun b : β => g b = c), ∑ a in fiber π b, X a := by
  rw [show fiber (fun a => g (π a)) c = Finset.univ.filter (fun a => g (π a) = c) from rfl]
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun a => g (π a) = c)) π X]
  rw [Finset.sum_filter (s := (Finset.univ : Finset β)) (p := fun b : β => g b = c)
    (f := fun b => ∑ a in fiber π b, X a)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [filter_filter_fiber]
  by_cases hb : g b = c <;> simp [hb]

/-- **加权条件期望**（粗纤维聚合）：`∑_{b : g b = c} |细纤维 b| · E[X | 细](b)`。
定义为独立函数，以避免同一陈述中两种索引类型的 `condExpFiber` 混用。 -/
noncomputable def weightedCondExp [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ]
    (X : α → ℝ) (c : γ) : ℝ :=
  Finset.sum ((Finset.univ : Finset β).filter (fun b : β => g b = c))
    (fun b : β => ((fiber π b).card : ℝ) * condExpFiber π X b)

/-- **塔性质（核心）**：`|粗纤维 c| · E[X | 粗](c) = ∑_{b : g b = c} |细纤维 b| · E[X | 细](b)`，
即 `E[E[X|F₁]|F₂] = E[X|F₂]`（F₂ ⊆ F₁）的纤维加权精确形式。 -/
theorem tower_property [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ] (X : α → ℝ)
    (c : γ) :
    ((fiber (fun a => g (π a)) c).card : ℝ) * condExpFiber (fun a => g (π a)) X c
      = weightedCondExp π g X c := by
  rw [card_mul_condExpFiber]
  rw [weightedCondExp, fiber_sum_eq_filtered_fiber_sum]
  exact Finset.sum_congr rfl (fun b _ => (card_mul_condExpFiber π X b).symm)

/-- **塔性质（条件期望形式）**：除以粗纤维基数后的形式。 -/
theorem tower_property_div [Fintype β] (π : α → β) (g : β → γ) [DecidableEq γ] (X : α → ℝ)
    (c : γ) (h : (fiber (fun a => g (π a)) c).card ≠ 0) :
    condExpFiber (fun a => g (π a)) X c
      = weightedCondExp π g X c / (((fiber (fun a => g (π a)) c).card : ℝ)) := by
  have hc : ((fiber (fun a => g (π a)) c).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [eq_div_iff hc, mul_comm, tower_property]

/-! ## 四、鞅差（条件零均值）与鞅的等价刻画 -/

/-- **条件零均值（鞅差）**：`d` 在每个 π-纤维上的和为零。 -/
def CondZeroMean (π : α → β) (d : α → ℝ) : Prop := ∀ b, ∑ a in fiber π b, d a = 0

/-- **条件零均值 ⟺ 条件期望恒零**。 -/
theorem condZeroMean_iff_condExpFiber_eq_zero (π : α → β) (d : α → ℝ) :
    CondZeroMean π d ↔ ∀ b, condExpFiber π d b = 0 := by
  constructor
  · intro h b
    by_cases hc : (fiber π b).card = 0
    · simp [condExpFiber, hc]
    · have h1 := card_mul_condExpFiber π d b
      rw [h b] at h1
      exact (mul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr hc)
  · intro h b
    rw [← card_mul_condExpFiber π d b, h b, mul_zero]

/-- **鞅差**：条件期望为零的增量（有限滤链单步的鞅差分）。 -/
def MartingaleDiff (π : α → β) (d : α → ℝ) : Prop := CondZeroMean π d

/-- **鞅 ⟺ 条件期望保持（核心）**：`d` 是鞅差 ⟺ `E[d|π] = 0` 且对任意 π-可测
加项 `Y`，添加 `d` 不改变条件期望（`E[Y + d | π] = E[Y | π]`）。 -/
theorem martingale_def_equiv (π : α → β) (d : α → ℝ) :
    MartingaleDiff π d ↔ (∀ b, condExpFiber π d b = 0) ∧
      (∀ Y : α → ℝ, AdaptedTo π Y →
        ∀ b, condExpFiber π (fun a => Y a + d a) b = condExpFiber π Y b) := by
  constructor
  · intro h
    have h1 := (condZeroMean_iff_condExpFiber_eq_zero π d).mp h
    exact ⟨h1, fun Y _ b => by rw [condExpFiber_add, h1 b, add_zero]⟩
  · rintro ⟨h1, _⟩
    exact (condZeroMean_iff_condExpFiber_eq_zero π d).mpr h1

end Lattice
