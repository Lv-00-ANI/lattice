import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealUnionBound
/-!
# LATTICE: Rademacher 复杂度（有限版）与有限假设类泛化界

方向（§5 验证行「泛化 / 学习理论」）：`RealHoeffding` 给出**单个**假设的有界
偏差尾界（Hoeffding），`RealUnionBound` 给出**多个**事件的并集界（Boole）。
本文件把两者拼成学习理论的第一块砖：**有限假设类的泛化界**，并给出
**Rademacher 复杂度**的有限（确定性样本）定义与基本性质。

**设定**：`α` 为有限非空样本空间（`Fintype α`），`n > 0` 为样本量，
`F : Finset (α → ℝ)` 为有限假设类，
`uniformProb` / `uniformExpectation` 沿用 `RealSamplingBoost` / `RealHoeffding`
的有限计数概率空间（每个样本点等概率 `1/|α|`）。

**内容**：
1. `radSign`：Rademacher 符号变量（`Fin 2` 上的 `±1` 零均值函数）及其小引理
   （`radSign_zero` / `radSign_one` / `radSign_abs` / `radSign_sum_zero`）。
2. `radComplexity`：有限确定性样本上的 **Rademacher 复杂度**
   `E_σ sup_{f∈F} |Σᵢ σᵢ fᵢ| / n`；`rad_complexity_nonneg` / `rad_complexity_le`。
3. 核心：`rad_hoeffding_event`（单假设偏差尾界，直接引用 `hoeffding_two_sided`）
   ⟹ `rad_generalization_bound`（并集界形式，引用 `union_bound_finite`）
   ⟹ `rad_generalization_bound_mem`（更友好的「存在某假设」事件形式）。
4. 对称化（symmetrization）：`rad_sup_expectation_le`（上确界之期望 ≤ 期望之上确界）、
   `rad_symmetrization_step`（逐点三角不等式），以及
   `rad_symmetrization`——**把平均步骤归约为一条显式的可交换性假设**
   （`降级`/`未证`：该交换恒等式本身未在此形式化，见下与文末注）。

**诚实标注（downgrades）**：
· 泛化界的常数是 `RealHoeffding` 中**已证**的保守常数：
  `2·|F|·exp(−n t²/8)`，而非教科书的紧常数 `2·|F|·exp(−2 n t²)`；
  要得到 `−2nt²` 需要 `X ∈ [−1,1]` 的**精确** Hoeffding 引理
  （`λ²(b−a)²/8`，`b−a = 2` 给出 `exp(−nt²/2)`；`−2nt²` 还要求 `[0,1]` 归一化），
  本文件不重证该引理，直接复用 `hoeffding_two_sided`。
· `rad_symmetrization` 以**显式假设** `hswap` 的形式给出可交换性
  （交换坐标保持配对空间上的均匀测度），该恒等式本身未证。
· 从 `E_w sup_f (Ef − Êf(w))` 化归到 `E_{w,w'} sup_f (Êf(w') − Êf(w))` 的
  「经验均值无偏」一步（`E_{w'} Êf(w') = Ef`）未做，故 `rad_symmetrization`
  的左侧直接取**已对称化**的形式。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 1. Rademacher 符号变量 -/

/-- Rademacher 符号变量：`Fin 2` 上的 `+1 / −1` 函数（`0 ↦ 1`，`1 ↦ −1`）。
注意：与 `RealBernstein.lean` 中的 `Lattice.rademacher` 同义但**独立定义**，
本文件不重定义既有标识符。 -/
noncomputable def radSign : Fin 2 → ℝ := fun a => if a = 0 then 1 else -1

/-- `radSign 0 = 1`。 -/
lemma radSign_zero : radSign 0 = 1 := by
  unfold radSign
  rw [if_pos rfl]

/-- `radSign 1 = -1`。 -/
lemma radSign_one : radSign 1 = -1 := by
  unfold radSign
  rw [if_neg (by decide)]

/-- 逐点绝对值恒为 1：`|radSign a| = 1`。 -/
lemma radSign_abs (a : Fin 2) : |radSign a| = 1 := by
  have h : ∀ b : Fin 2, radSign b = 1 ∨ radSign b = -1 := by
    intro b
    fin_cases b
    · exact Or.inl (by simpa using radSign_zero)
    · exact Or.inr (by simpa using radSign_one)
  rcases h a with h1 | h1 <;> rw [h1] <;> norm_num

/-- Rademacher 符号的零均值（求和形式）：`∑ a : Fin 2, radSign a = 0`。 -/
lemma radSign_sum_zero : (∑ a : Fin 2, radSign a) = 0 := by
  rw [Fin.sum_univ_two, radSign_zero, radSign_one]
  norm_num

/-- Rademacher 符号的零均值（均匀期望形式）：`uniformExpectation radSign = 0`。 -/
lemma radSign_uniformExpectation_zero : uniformExpectation (radSign : Fin 2 → ℝ) = 0 :=
  uniformExpectation_eq_zero_of_sum_eq_zero radSign_sum_zero

/-! ## 2. 有限均匀期望的辅助性质（本文件内部使用） -/

/-- 有限均匀期望的非负性：逐点非负 ⟹ 期望非负。 -/
lemma rad_uniformExpectation_nonneg {α : Type*} [Fintype α] {X : α → ℝ}
    (hX : ∀ x, 0 ≤ X x) : 0 ≤ uniformExpectation X := by
  unfold uniformExpectation
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hX x)) (Nat.cast_nonneg _)

/-- 有限均匀期望的单调性：逐点 `≤` ⟹ 期望 `≤`（分母 `|α| ≥ 0`）。 -/
lemma rad_uniformExpectation_mono {α : Type*} [Fintype α] {X Y : α → ℝ}
    (hXY : ∀ x, X x ≤ Y x) : uniformExpectation X ≤ uniformExpectation Y := by
  unfold uniformExpectation
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hXY x)) (Nat.cast_nonneg _)

/-- 常函数的均匀期望：`α` 非空时 `E[c] = c`。 -/
lemma rad_uniformExpectation_const {α : Type*} [Fintype α] (hN : 0 < Fintype.card α) (c : ℝ) :
    uniformExpectation (fun _ : α => c) = c := by
  unfold uniformExpectation
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_cancel_left₀ c (ne_of_gt (Nat.cast_pos.mpr hN))]

/-- 有限均匀期望的加性：`E[X + Y] = E[X] + E[Y]`。 -/
lemma rad_uniformExpectation_add {α : Type*} [Fintype α] (X Y : α → ℝ) :
    uniformExpectation (fun x => X x + Y x) = uniformExpectation X + uniformExpectation Y := by
  unfold uniformExpectation
  rw [Finset.sum_add_distrib, add_div]

/-- 有限均匀期望的数乘：`E[c · X] = c · E[X]`。 -/
lemma rad_uniformExpectation_mul_const {α : Type*} [Fintype α] (c : ℝ) (X : α → ℝ) :
    uniformExpectation (fun x => c * X x) = c * uniformExpectation X := by
  unfold uniformExpectation
  rw [← Finset.mul_sum, mul_div_assoc]

/-- 乘积类型上只看第一个坐标的均匀期望：`E_{(a,b)}[X a] = E_a[X a]`
（`β` 非空，保证内层平均不退化）。 -/
lemma rad_uniformExpectation_fst {α β : Type*} [Fintype α] [Fintype β]
    (hβ : 0 < Fintype.card β) (X : α → ℝ) :
    uniformExpectation (fun p : α × β => X p.1) = uniformExpectation X := by
  have hβne : (Fintype.card β : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hβ)
  unfold uniformExpectation
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum,
    mul_comm (Fintype.card β : ℝ) (∑ a, X a)]
  exact mul_div_mul_right _ _ hβne

/-- 乘积类型上只看第二个坐标的均匀期望：`E_{(a,b)}[X b] = E_b[X b]`
（`α` 非空）。 -/
lemma rad_uniformExpectation_snd {α β : Type*} [Fintype α] [Fintype β]
    (hα : 0 < Fintype.card α) (X : β → ℝ) :
    uniformExpectation (fun p : α × β => X p.2) = uniformExpectation X := by
  have hαne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hα)
  unfold uniformExpectation
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_left _ _ hαne

/-! ## 3. 上确界的两个基本引理（绕开 `sup'` 的非空前件相等性问题） -/

/-- 有限集上确界的下界：`b ∈ s ⟹ f b ≤ s.sup' H f`（用 `Finset.sup'_le_iff`
在同一条非空见证 `H` 下取得，避免 `H` 的证明项差异）。 -/
lemma rad_le_sup' {β : Type*} {s : Finset β} (H : s.Nonempty) (f : β → ℝ) {b : β}
    (hb : b ∈ s) : f b ≤ s.sup' H f :=
  (Finset.sup'_le_iff (s := s) (H := H) (f := f)).mp le_rfl b hb

/-- 有限集上确界的上界判据：逐点 `≤ a` ⟹ `s.sup' H f ≤ a`。 -/
lemma rad_sup'_le {β : Type*} {s : Finset β} (H : s.Nonempty) (f : β → ℝ) {a : ℝ}
    (h : ∀ b ∈ s, f b ≤ a) : s.sup' H f ≤ a :=
  (Finset.sup'_le_iff (s := s) (H := H) (f := f)).mpr h

/-! ## 4. Rademacher 复杂度（有限确定性样本版） -/

/-- **Rademacher 复杂度（有限确定性样本版）**：
样本 `F : Finset (Fin n → ℝ)`（假设在 `n` 个样本点上的取值），
`E_σ sup_{f∈F} |Σᵢ σᵢ fᵢ| / n`，其中 `σ` 在符号空间 `Fin n → Fin 2` 上均匀取值。

`hF` 是非空见证（`Finset.sup'` 需要）。 -/
noncomputable def radComplexity (n : ℕ) (F : Finset (Fin n → ℝ)) (hF : F.Nonempty) : ℝ :=
  uniformExpectation (fun σ : Fin n → Fin 2 =>
    F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f i|) / (n : ℝ))

/-- **Rademacher 复杂度非负（一般形式）**：只要每个 `σ` 处的上确界非负
（此处由绝对值保证），平均后仍非负。 -/
lemma rad_complexity_nonneg_of (n : ℕ) (F : Finset (Fin n → ℝ)) (hF : F.Nonempty)
    (hsup : ∀ σ : Fin n → Fin 2,
      0 ≤ F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f i|)) :
    0 ≤ radComplexity n F hF := by
  apply rad_uniformExpectation_nonneg
  intro σ
  exact div_nonneg (hsup σ) (Nat.cast_nonneg n)

/-- **Rademacher 复杂度非负**：`0 ≤ radComplexity n F hF`。
每个 `sup'` 值 ≥ 某个绝对值 ≥ 0，除以 `n ≥ 0` 后仍非负，平均后非负。 -/
theorem rad_complexity_nonneg (n : ℕ) (F : Finset (Fin n → ℝ)) (hF : F.Nonempty) :
    0 ≤ radComplexity n F hF :=
  rad_complexity_nonneg_of n F hF
    (fun σ => le_trans (abs_nonneg _)
      (rad_le_sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f i|) hF.choose_spec))

/-- **Rademacher 复杂度上界（`n > 0`）**：若假设类逐点有 `|f i| ≤ 1`，
则 `radComplexity n F hF ≤ 1`。证明：`|Σᵢ σᵢ fᵢ| ≤ Σᵢ |σᵢ|·|fᵢ| = Σᵢ |fᵢ| ≤ n`，
故每个 `σ` 处 `sup' / n ≤ n/n = 1`，平均后 ≤ 1。 -/
theorem rad_complexity_le (n : ℕ) (hn : 0 < n) (F : Finset (Fin n → ℝ)) (hF : F.Nonempty)
    (hb : ∀ f ∈ F, ∀ i : Fin n, |f i| ≤ 1) :
    radComplexity n F hF ≤ 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  haveI : Nonempty (Fin n → Fin 2) := ⟨fun _ => 0⟩
  have hcardSig : 0 < Fintype.card (Fin n → Fin 2) := Fintype.card_pos_iff.mpr inferInstance
  have hsup : ∀ σ : Fin n → Fin 2,
      F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f i|) ≤ (n : ℝ) := by
    intro σ
    apply rad_sup'_le hF
    intro f hf
    calc
      |∑ i : Fin n, radSign (σ i) * f i| ≤ ∑ i : Fin n, |radSign (σ i) * f i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |f i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, radSign_abs, one_mul]
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hb f hf i)
      _ = (n : ℝ) := by simp
  have hdiv : ∀ σ : Fin n → Fin 2,
      F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f i|) / (n : ℝ) ≤ 1 := by
    intro σ
    have h := div_le_div_of_nonneg_right (hsup σ) (le_of_lt hnpos)
    rwa [div_self hnne] at h
  have hmain : radComplexity n F hF ≤
      uniformExpectation (fun _ : Fin n → Fin 2 => (1 : ℝ)) := by
    unfold radComplexity
    exact rad_uniformExpectation_mono hdiv
  rwa [rad_uniformExpectation_const hcardSig 1] at hmain

/-! ## 5. 核心：有限假设类的泛化界（Hoeffding + 并集界） -/

/-- **单假设的 Hoeffding 事件尾界**：`|f| ≤ 1`、`t > 0` 时，
经验均值偏离均匀期望超过 `t` 的概率 ≤ `2·exp(−n t²/8)`。
直接引用 `RealHoeffding.hoeffding_two_sided`（无需任何新证明）。 -/
theorem rad_hoeffding_event {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hb : ∀ x : α, |f x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|)) ≤
      2 * Real.exp (-(n : ℝ) * t ^ 2 / 8) :=
  hoeffding_two_sided (X := f) (uniformExpectation f) n hn hN rfl hb ht

/-- **有限假设类泛化界（并集界形式）**：有限类 `F` 中每个假设逐点有 `|f| ≤ 1`、
`t > 0` 时，「存在某个假设 `f ∈ F` 使其经验均值偏离期望超过 `t`」的概率
≤ `|F| · 2·exp(−n t²/8)`。证明：对 `f ∈ F` 用 `rad_hoeffding_event`，
再对 `|F|` 个事件用 `RealUnionBound.union_bound_finite`（Bonferroni）。 -/
theorem rad_generalization_bound {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (α → ℝ)) (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hb : ∀ f ∈ F, ∀ x : α, |f x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (F.biUnion (fun f => Finset.univ.filter (fun w : Fin n → α =>
        t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|))) ≤
      (F.card : ℝ) * (2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)) :=
  union_bound_finite F
    (fun f => Finset.univ.filter (fun w : Fin n → α =>
      t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|))
    (fun f hf => rad_hoeffding_event f n hn hN (hb f hf) ht)

/-- **泛化界（「存在」事件形式）**：把事件写成
`{w | ∃ f ∈ F, t ≤ |Êf(w) − Ef|}` 的过滤集，用
`Finset.mem_biUnion` 证明它等于上一条的 `biUnion`，再用 `RealUnionBound`
给出的同一条界。 -/
theorem rad_generalization_bound_mem {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (α → ℝ)) (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hb : ∀ f ∈ F, ∀ x : α, |f x| ≤ 1) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        ∃ f ∈ F, t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|)) ≤
      (F.card : ℝ) * (2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)) := by
  have hset : Finset.univ.filter (fun w : Fin n → α =>
        ∃ f ∈ F, t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|)
      = F.biUnion (fun f => Finset.univ.filter (fun w : Fin n → α =>
          t ≤ |(∑ i : Fin n, f (w i)) / n - uniformExpectation f|)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
  rw [hset]
  exact rad_generalization_bound F n hn hN hb ht

/-! ## 6. 对称化（symmetrization）：上确界-期望交换、三角不等式与交换性归约 -/

/-- **上确界的期望 ≤ 期望的上确界**（有限 `F`，函数 `g : β → α → ℝ`）：
`sup_{f} E[g f] ≤ E[sup_f g f]`。证明：`sup'_le_iff` 归约为逐点
`g f w ≤ sup'_f g f w`（`rad_le_sup'`），再对期望用单调性。 -/
theorem rad_sup_expectation_le {α β : Type*} [Fintype α] (F : Finset β) (hF : F.Nonempty)
    (g : β → α → ℝ) :
    F.sup' hF (fun f => uniformExpectation (g f)) ≤
      uniformExpectation (fun w => F.sup' hF (fun f => g f w)) := by
  apply rad_sup'_le hF
  intro f hf
  exact rad_uniformExpectation_mono (fun w => rad_le_sup' hF (fun f => g f w) hf)

/-- **对称化的逐点三角不等式**：对固定的 `z z' : Fin n → α` 与符号 `σ`，
`sup_{f∈F} Σᵢ σᵢ (f z'ᵢ − f zᵢ) ≤ sup_{f∈F}|Σᵢ σᵢ f z'ᵢ| + sup_{f∈F}|Σᵢ σᵢ f zᵢ|`。
证明：和式拆开为 `A − B`，用 `A − B ≤ |A| + |B|`（`linarith`），
两个绝对值分别被 `sup'` 控制（`rad_le_sup'`）。 -/
theorem rad_symmetrization_step {α : Type*} [Fintype α] (F : Finset (α → ℝ)) (hF : F.Nonempty)
    (n : ℕ) (z z' : Fin n → α) (σ : Fin n → Fin 2) :
    F.sup' hF (fun f => ∑ i : Fin n, radSign (σ i) * (f (z' i) - f (z i))) ≤
      F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z' i)|) +
      F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z i)|) := by
  apply rad_sup'_le hF
  intro f hf
  have hsplit : (∑ i : Fin n, radSign (σ i) * (f (z' i) - f (z i)))
      = (∑ i : Fin n, radSign (σ i) * f (z' i)) -
        (∑ i : Fin n, radSign (σ i) * f (z i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc
    (∑ i : Fin n, radSign (σ i) * (f (z' i) - f (z i)))
        = (∑ i : Fin n, radSign (σ i) * f (z' i)) -
          (∑ i : Fin n, radSign (σ i) * f (z i)) := hsplit
    _ ≤ |∑ i : Fin n, radSign (σ i) * f (z' i)| +
        |∑ i : Fin n, radSign (σ i) * f (z i)| := by
      have h1 : (∑ i : Fin n, radSign (σ i) * f (z' i)) ≤
          |∑ i : Fin n, radSign (σ i) * f (z' i)| := le_abs_self _
      have h2 : -(∑ i : Fin n, radSign (σ i) * f (z i)) ≤
          |∑ i : Fin n, radSign (σ i) * f (z i)| := neg_le_abs _
      linarith
    _ ≤ F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z' i)|) +
        F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z i)|) :=
      add_le_add
        (rad_le_sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z' i)|) hf)
        (rad_le_sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (z i)|) hf)

/-- **交换坐标映射**：对固定符号 `σ`，把配对 `(p.1, p.2)` 在满足 `σ i = -1`
（即 `σ i ≠ 0`）的坐标 `i` 处交换。这是对称化中「交换后重新配对」的显式映射；
其**保持均匀测度**（即它在配对空间上是双射）正是 `rad_symmetrization` 中
显式假设 `hswap` 的内容。 -/
def radSwap {α : Type*} {n : ℕ} (σ : Fin n → Fin 2)
    (p : (Fin n → α) × (Fin n → α)) : (Fin n → α) × (Fin n → α) :=
  (fun i => if σ i = 0 then p.1 i else p.2 i,
   fun i => if σ i = 0 then p.2 i else p.1 i)

/-- **样本上的 Rademacher 复杂度**（含 `n` 归一）：
`E_σ E_w sup_{f∈F} |Σᵢ σᵢ f(wᵢ)| / n`，即 `radComplexity` 的「样本平均」版本
（`w` 在 `Fin n → α` 上均匀取值）。 -/
noncomputable def radComplexitySample {α : Type*} [Fintype α] (n : ℕ)
    (F : Finset (α → ℝ)) (hF : F.Nonempty) : ℝ :=
  uniformExpectation (fun σ : Fin n → Fin 2 =>
    uniformExpectation (fun w : Fin n → α =>
      F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))) / (n : ℝ)

/-- **对称化（symmetrization），`降级`/`未证`**：
在**显式假设** `hswap`（「按 `σ` 交换坐标保持配对空间上的均匀平均」，
即 `radSwap σ` 是保测双射）下，

  `E_{w,w'} sup_{f∈F} (Êf(w') − Êf(w)) ≤ 2 · (1/n) · E_{σ,w} sup_{f∈F} |Σᵢ σᵢ f(wᵢ)|`.

**降级说明**：
· 左侧取的是**已对称化**的经验过程形式 `E_{w,w'} sup_f (Êf(w') − Êf(w))`
  （`Êf(w) = (Σᵢ f(wᵢ))/n`）；从标准形式 `E_w sup_f (Ef − Êf(w))` 到此式
  还需「经验均值无偏」一步（`E_{w'} Êf(w') = Ef`），本文件**未证**。
· `hswap` 本身（交换坐标的保测性）**未在此形式化**：它是本证明中唯一的缺口，
  其余全部（逐点三角不等式 `rad_symmetrization_step`、期望的加性/单调性、
  「只看一个坐标」的乘积平均 `rad_uniformExpectation_fst/snd`）都已给出。
· 该交换恒等式的作用恰是：对每个 `σ` 把 `sup_f (Êf(w') − Êf(w))` 的配对平均
  改写为 `sup_f (Σᵢ σᵢ (f(w'ᵢ) − f(wᵢ)))/n` 的配对平均，于是可在符号上取平均。 -/
theorem rad_symmetrization {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ)
    (hα : 0 < Fintype.card α)
    (F : Finset (α → ℝ)) (hF : F.Nonempty)
    (hswap : ∀ (σ : Fin n → Fin 2) (G : (Fin n → α) × (Fin n → α) → ℝ),
      (∑ p : (Fin n → α) × (Fin n → α), G (radSwap σ p)) = ∑ p, G p) :
    uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i)))) / (n : ℝ)
      ≤ 2 * radComplexitySample n F hF := by
  haveI : Nonempty α := Fintype.card_pos_iff.mp hα
  have hcardW : 0 < Fintype.card (Fin n → α) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Classical.arbitrary α⟩
  -- (i) 交换性：每个 σ 下，配对平均把 `Σ(f(p.2)-f(p.1))` 改为 `Σ σᵢ (f(p.2)-f(p.1))`
  have key : ∀ σ : Fin n → Fin 2,
      uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, radSign (σ i) * (f (p.2 i) - f (p.1 i))))
      = uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i)))) := by
    intro σ
    unfold uniformExpectation
    congr 1
    calc
      (∑ p : (Fin n → α) × (Fin n → α),
          F.sup' hF (fun f => ∑ i : Fin n, radSign (σ i) * (f (p.2 i) - f (p.1 i))))
          = ∑ p : (Fin n → α) × (Fin n → α),
              F.sup' hF (fun f => ∑ i : Fin n,
                (f ((radSwap σ p).2 i) - f ((radSwap σ p).1 i))) := by
            apply Finset.sum_congr rfl
            intro p _
            congr 1
            funext f
            apply Finset.sum_congr rfl
            intro i _
            by_cases h : σ i = 0
            · simp only [radSwap, radSign, if_pos h]; ring
            · simp only [radSwap, radSign, if_neg h]; ring
      _ = ∑ p : (Fin n → α) × (Fin n → α),
            F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))) :=
            hswap σ (fun p =>
              F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))))
  -- (ii) 逐点三角不等式 → 配对平均界
  have hstep : ∀ σ : Fin n → Fin 2,
      uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, radSign (σ i) * (f (p.2 i) - f (p.1 i))))
      ≤ 2 * uniformExpectation (fun w : Fin n → α =>
        F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|)) := by
    intro σ
    have hmono : uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
          F.sup' hF (fun f => ∑ i : Fin n, radSign (σ i) * (f (p.2 i) - f (p.1 i))))
        ≤ uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
          (F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (p.2 i)|) +
           F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (p.1 i)|))) :=
      rad_uniformExpectation_mono
        (fun p => rad_symmetrization_step F hF n p.1 p.2 σ)
    have hlin : uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
          (F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (p.2 i)|) +
           F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (p.1 i)|)))
        = 2 * uniformExpectation (fun w : Fin n → α =>
            F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|)) := by
      rw [rad_uniformExpectation_add,
        rad_uniformExpectation_snd hcardW
          (fun w : Fin n → α => F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|)),
        rad_uniformExpectation_fst hcardW
          (fun w : Fin n → α => F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))]
      ring
    exact hmono.trans (le_of_eq hlin)
  -- (iii) 组合：把 `E_p H` 看成对 σ 的常函数，再对 σ 取平均
  have hcardSig : 0 < Fintype.card (Fin n → Fin 2) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => (0 : Fin 2)⟩
  have hsig : ∀ σ : Fin n → Fin 2,
      uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))))
      ≤ 2 * uniformExpectation (fun w : Fin n → α =>
        F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|)) := by
    intro σ
    rw [← key σ]
    exact hstep σ
  have hbound : uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))))
      ≤ 2 * uniformExpectation (fun σ : Fin n → Fin 2 =>
          uniformExpectation (fun w : Fin n → α =>
            F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))) := by
    calc
      uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
          F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))))
          = uniformExpectation (fun _s : Fin n → Fin 2 =>
              uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
                F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i))))) :=
            (rad_uniformExpectation_const hcardSig _).symm
      _ ≤ uniformExpectation (fun σ : Fin n → Fin 2 =>
            2 * uniformExpectation (fun w : Fin n → α =>
              F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))) :=
            rad_uniformExpectation_mono hsig
      _ = 2 * uniformExpectation (fun σ : Fin n → Fin 2 =>
            uniformExpectation (fun w : Fin n → α =>
              F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))) :=
            rad_uniformExpectation_mul_const 2 _
  calc
    uniformExpectation (fun p : (Fin n → α) × (Fin n → α) =>
        F.sup' hF (fun f => ∑ i : Fin n, (f (p.2 i) - f (p.1 i)))) / (n : ℝ)
        ≤ 2 * uniformExpectation (fun σ : Fin n → Fin 2 =>
              uniformExpectation (fun w : Fin n → α =>
                F.sup' hF (fun f => |∑ i : Fin n, radSign (σ i) * f (w i)|))) / (n : ℝ) :=
          div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)
    _ = 2 * radComplexitySample n F hF := by
          unfold radComplexitySample
          ring

/-! ## 注：与 RealUnionBound / RealHoeffding 的衔接

**两个零件、三个接口。** 本文件是 Concentration ⟶ Learning Theory 的桥：

1. **集中步骤** `rad_hoeffding_event` 直接调用 `RealHoeffding.hoeffding_two_sided`：
   单个假设 `f`（`|f| ≤ 1`）的经验均值 `Êf(w) = (Σᵢ f(wᵢ))/n` 以概率
   `1 − 2·exp(−n t²/8)` 落在 `[Ef − t, Ef + t]` 内。这是「**一个**假设好用」
   的指数型保证（Hoeffding 的 e^{−c n t²} 集中）。
2. **并集步骤** `rad_generalization_bound` 调用
   `RealUnionBound.union_bound_finite`：把 `|F|` 个「坏事件」的并集概率用
   Bonferroni `|F|·ε` 控制住。这是「**所有**假设同时好用」的代价——
   泛化界中的 `|F|` 因子正是样本复杂度 `log |F|` 的来源
   （取 `2|F|exp(−nt²/8) ≤ δ` 即得 `n ≳ (8/t²)·log(2|F|/δ)`）。
3. **对称化** `rad_symmetrization` 把「最坏假设的经验偏差」量化，
   给出与假设类大小无关的 Rademacher 复杂度 `2·(1/n)·E_{σ,w} sup_f |Σσᵢ f(wᵢ)|`；
   它与 `rad_generalization_bound` 的 `|F|` 因子互补：前者对无穷类也有意义，
   后者对有限类给出可直接计算的界。

**由此得到的「桥」**：`RealHoeffding`（单假设指数集中）+ `RealUnionBound`
（多假设并集代价）= 有限假设类的泛化界；再把 sup 从「有限并」换成
「期望的 sup」（Rademacher 复杂度）即从组合界升级为度量熵/复杂度界。
这正是学习理论中「能力（capacity）控制泛化」的最基本形式。

### 全部诚实降级（downgrade）清单

· `rad_hoeffding_event` / `rad_generalization_bound` / `rad_generalization_bound_mem`
  —— **常数降级**：指数为 `exp(−n t²/8)`、系数 `2`；教科书紧常数为
  `2·|F|·exp(−2 n t²)`。原因：`RealHoeffding` 为了保证 `X ∈ [−1,1]` 的
  完整 Hoeffding 引理未重证，用 `|X − μ| ≤ 2` 的保守上界，代价是常数
  `2`（→ `exp(−nt²/8)`）而非 `1/2`（→ `exp(−nt²/2)`）；`−2nt²` 还需要
  `X ∈ [0,1]`（区间宽度 1）的归一化版本。本文件不重证该引理。
· `rad_symmetrization` —— **显式假设降级**：可交换性恒等式 `hswap`
  （「按 `σ` 交换坐标保持配对空间 `(Fin n → α) × (Fin n → α)` 上的均匀平均」）
  以**假设**形式给出，本身**未证**。它的一个充分证明是：
  `radSwap σ` 是 `Fin n → (α × α)` 上的坐标置换（在每个坐标处用
  `Prod.swap` 或恒等），从而是保测双射；本文件只把它写成假设。
· `rad_symmetrization` —— **形式降级**：左侧取已对称化的
  `E_{w,w'} sup_f (Êf(w') − Êf(w))`；从标准的
  `E_w sup_f (Ef − Êf(w))` 到此式所需的「经验均值无偏」
  （`E_{w'} Êf(w') = Ef`）**未做**。
· `rad_complexity_le` 需要 `hn : 0 < n`（`n = 0` 时 `sup'/0 = 0`，
  结论 `≤ 1` 也成立）。**该假设是形式上的**：按题面要求保留；删去后
  `n = 0` 分支无需任何单独处理，既有的 `hnpos` / `hnne` / `hcardSig`
  三个 `have` 只服务于 `n > 0` 的推理。
· 未做：Rademacher 复杂度的有限类界 `R ≤ sqrt(2 log|F|/n)`、
  Dudley 熵积分、VC 维、马尔可夫/切比雪夫版的 Rademacher 界。
-/

end Lattice
