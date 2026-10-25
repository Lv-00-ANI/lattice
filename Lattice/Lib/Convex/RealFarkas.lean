import Mathlib
import Lattice.Lib.Convex.RealConstraintQualification
/-!
# LATTICE: Farkas 引理与 MFCQ 的严格分离部分

本文件补上 `RealConstraintQualification`（221–230 行）显式登记的两处缺口中的
**Farkas 引理 / 有限维分离定理**那一半，并给出 MFCQ 在「无乘子 ⟹ 存在可行下降方向」
这一步中的真实作用。

## 一、任务书原始命题的前提恒假（机器验证）

任务书给出的原始 Farkas 形式是

```
{x | ∀ i, ⟨aᵢ, x⟩ ≤ 0} = ∅ ⟹ ∃ λ ≥ 0, ∑ λᵢ aᵢ = 0 ∧ ∑ λᵢ > 0
```

**其前提恒假**：因为 `0` 永远满足 `dotV (a i) 0 = 0 ≤ 0`。本文件用
`nonpos_set_nonempty` / `nonpos_set_never_empty` **机器验证**了这一点，并用
`farkas_literal_vacuous` 逐字给出该假言命题（空真）。**诚实标注：这不是有内容的 Farkas 引理。**

## 二、正确的 Farkas 引理

1. `farkas_alternative`（抽象内积空间 `H`）：非空闭凸锥 `K`、`b : H`，
   若 `b` 被 `K` 的对偶锥「合法化」，则 `b ∈ K`（即 `K** ⊆ K`，双极定理的 nontrivial 方向）；
2. `farkas_bipolar`：`(K*)* = K`（双极形式，直接回收 mathlib 的
   `ConvexCone.innerDualCone_of_innerDualCone_eq_self`）；
3. `farkas_alternative_dotV` / `farkas_fin_conic`（**有限维 `ℝ^d` 坐标形式**）：
   直接调用几何 Hahn–Banach（`geometric_hahn_banach_closed_point`，在 `Fin d → ℝ` 这个
   有限维局部凸空间上可用），再用标准基把分离泛函写成 `dotV a ·`，从而得到
   `(∀ y, (∀ x ∈ K, 0 ≤ dotV x y) → 0 ≤ dotV b y) ↔ b ∈ K`；
4. `farkas_multiplier_criterion`（**乘子判据**）：
   `HasNonnegCombo grad (-gradF) ↔ (∀ v, (∀ i, dotV (grad i) v ≤ 0) → 0 ≤ dotV gradF v)`。
   前向方向是纯代数；后向方向归约到 `farkas_fin_conic`，需要
   `IsClosed (nonnegComboCone grad)`。

## 三、MFCQ 的作用

5. `mfcq_perturb` / `mfcq_perturb_neg`：MFCQ 方向 `w`（`∀ i, ⟨∇gᵢ, w⟩ < 0`）可以把
   弱方向 `v`（`∀ i, ⟨∇gᵢ, v⟩ ≤ 0`）扰动成**严格**方向（`∀ i, ⟨∇gᵢ, v'⟩ < 0`），
   同时保持目标泛函值的符号不变；
6. `mfcq_strict_separation`：MFCQ + 无乘子 ⟹ 存在**严格**可行下降方向
   （`∀ i, ⟨∇gᵢ, v⟩ < 0` 且 `⟨∇f, v⟩ < 0`）。

## 诚实边界（标注）

- **标注：前提恒假**。任务书原始 Farkas 命题的前提 `{x | ∀ i, ⟨aᵢ,x⟩ ≤ 0} = ∅` 不可满足
  （`0` 恒属于该集合，机器验证于 `nonpos_set_nonempty`），故 `farkas_literal_vacuous`
  是空真命题，**不是有内容的 Farkas 引理**；
- **未证**：有限生成锥 `nonnegComboCone grad = {∑ λᵢ∇gᵢ | λᵢ ≥ 0}` 的**闭性**。
  该事实在数学上成立（有限生成锥都是闭的），但 mathlib 4.14 没有多面体锥 / 有限生成锥
  闭性的 API（无 `Polyhedral`、无 `conicalHull` 的闭性引理），本文件因此把
  `IsClosed (nonnegComboCone grad)` 作为**显式假设**保留（`farkas_multiplier_criterion`、
  `mfcq_strict_separation`），而不是谎称已证。**降级**说明：这是本文件唯一的数学缺口；
  `farkas_alternative_dotV` / `farkas_fin_conic` 对**任意**给定的非空闭凸锥是完整证明；
- **未做**：`MFCQ ⟹ 乘子存在` 的**完整 KKT 定理**。本文件只补上了 Farkas / 严格分离这一半；
  完整的 KKT 还需要 (a) 一阶最优性（「x̄ 最优 ⟹ 不存在可行下降方向」，
  需要 `HasFDerivAt` + 小步长论证）与 (b) 把 `RealConstraintQualification` 的
  `MFCQ` / 活跃约束设定与 `grad` 的对应关系补全。**不谎称已补齐 KKT**；
- **未做**：一般 `m` 的 `LICQ ⟹ MFCQ`（需要转置映射满射 / 正交补维数公式），本文件不涉及；
- **标注：任务书符号不一致**。任务书要求
  `mfcq_strict_separation : ¬ HasNonnegCombo grad (-gradF) → 0 < dotV gradF v`，
  但在本文件的乘子判据 `HasNonnegCombo grad (-gradF) ↔ ∀ v, P v → 0 ≤ dotV gradF v`
  （这是任务书自己给出的判据）下，`¬ HasNonnegCombo grad (-gradF)` 推出的
  **是 `dotV gradF v < 0`**（下降方向），不是 `0 < dotV gradF v`。
  这不是证明能力问题，而是命题本身的**符号不一致**：本文件用
  `mfcq_strict_separation_literal_false` 给出**机器验证的反例**
  （`d = 1`、`∇g = 1`、`∇f = 1` 时该严格不等式不可能成立，因为 `⟨∇g,v⟩ < 0` 与 `0 < ⟨∇f,v⟩` 是同一个不等式 `v < 0` 与 `0 < v`）。本文件因此给出**符号正确**的
  `mfcq_strict_separation`（结论为 `dotV gradF v < 0`）；
- 全程无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open Set

-- `𝓝` / `𝓝[>]` 属于 `Topology` 记法作用域，缺了它 `𝓝` 会是未知标识符
-- （表现为 "unknown identifier '𝓝'" 或解析器读错 `[>]`）；
-- `Tendsto` / `Filter` 相关名字在 `Filter` 命名空间下。
open scoped BigOperators RealInnerProductSpace Topology

open Filter

/-! ## 零、标准基与连续线性泛函的坐标表示

（本文件按任务书只 `import Mathlib` 与 `import RealConstraintQualification`，不依赖
`RealSupportingHyperplane`，故这里自带一份「标准基展开 + 泛函坐标表示」的辅助引理；
声明名与本仓库其它文件不冲突。） -/

/-- `Fin d → ℝ` 的标准基向量 `e_j`（第 `j` 坐标为 `1`，其余 `0`）。 -/
def farkasStdBasisVec {d : ℕ} (j : Fin d) : Fin d → ℝ := fun k => if k = j then 1 else 0

/-- 标准基展开：`y = ∑ j, y j • e_j`。 -/
theorem farkas_sum_stdBasisVec_smul {d : ℕ} (y : Fin d → ℝ) :
    (∑ j : Fin d, y j • farkasStdBasisVec j) = y := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [farkasStdBasisVec]
  · intro j _ hj
    have hkj : k ≠ j := fun h => hj h.symm
    simp [farkasStdBasisVec, hkj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **连续线性泛函的坐标表示**：`(Fin d → ℝ) →L[ℝ] ℝ` 上任意泛函都由坐标内积给出，
`f y = dotV a y`，其中 `a j = f e_j`。这是把抽象分离泛函「向量化」的关键引理。 -/
theorem farkas_continuousLinearMap_eq_dotV {d : ℕ} (f : (Fin d → ℝ) →L[ℝ] ℝ)
    (y : Fin d → ℝ) :
    f y = dotV (fun j => f (farkasStdBasisVec j)) y := by
  calc f y = f (∑ j : Fin d, y j • farkasStdBasisVec j) := by rw [farkas_sum_stdBasisVec_smul]
    _ = ∑ j : Fin d, y j * f (farkasStdBasisVec j) := by
          simp only [map_sum, map_smul, smul_eq_mul]
    _ = dotV (fun j => f (farkasStdBasisVec j)) y := by
          simp only [dotV]
          exact Finset.sum_congr rfl fun j _ => by ring

/-! ## 一、`dotV` 的双线性引理 -/

/-- `dotV` 对**左**变元可加。 -/
lemma dotV_add_left {d : ℕ} (u v w : Fin d → ℝ) :
    dotV (u + v) w = dotV u w + dotV v w := by
  simp only [dotV, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `dotV` 对**左**变元取负。 -/
lemma dotV_neg_left {d : ℕ} (u v : Fin d → ℝ) : dotV (-u) v = -(dotV u v) := by
  simp only [dotV, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- `dotV` 对**右**变元可加。 -/
lemma dotV_add_right {d : ℕ} (u v w : Fin d → ℝ) :
    dotV u (v + w) = dotV u v + dotV u w := by
  simp only [dotV, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- `dotV` 对**右**变元取负。 -/
lemma dotV_neg_right {d : ℕ} (u v : Fin d → ℝ) : dotV u (-v) = -(dotV u v) := by
  simp only [dotV, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- `dotV` 对**左**变元齐次。 -/
lemma dotV_smul_left {d : ℕ} (c : ℝ) (u v : Fin d → ℝ) :
    dotV (c • u) v = c * dotV u v := by
  simp only [dotV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `dotV` 对**右**变元齐次。 -/
lemma dotV_smul_right {d : ℕ} (c : ℝ) (u v : Fin d → ℝ) :
    dotV u (c • v) = c * dotV u v := by
  simp only [dotV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `dotV` 对称。 -/
lemma dotV_comm {d : ℕ} (u v : Fin d → ℝ) : dotV u v = dotV v u := by
  simp only [dotV]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `dotV` 对线性组合的左变元展开：`dotV (∑ λᵢ gᵢ) v = ∑ λᵢ · dotV gᵢ v`。 -/
lemma dotV_sum_smul_left {m d : ℕ} (lam : Fin m → ℝ) (g : Fin m → (Fin d → ℝ))
    (v : Fin d → ℝ) :
    dotV (∑ i, lam i • g i) v = ∑ i, lam i * dotV (g i) v := by
  calc dotV (∑ i, lam i • g i) v
      = ∑ j : Fin d, ∑ i : Fin m, (lam i * g i j) * v j := by
          simp only [dotV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin d, (lam i * g i j) * v j := Finset.sum_comm
    _ = ∑ i : Fin m, lam i * dotV (g i) v := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [dotV, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring

/-! ## 二、非负半空间集合永不空（任务书原始命题前提恒假的机器验证） -/

/-- **机器验证（反例/见证）**：对任意 `a : Fin m → (Fin d → ℝ)`，
非负半空间交 `{x | ∀ i, dotV (a i) x ≤ 0}` **永远包含 `0`**。
这与任务书原始 Farkas 命题的前提 `{x | ∀ i, ⟨aᵢ,x⟩ ≤ 0} = ∅` **直接矛盾**。 -/
theorem nonpos_set_nonempty {m d : ℕ} (a : Fin m → (Fin d → ℝ)) :
    (0 : Fin d → ℝ) ∈ {x : Fin d → ℝ | ∀ i, dotV (a i) x ≤ 0} := by
  intro i
  simp [dotV]

/-- **机器验证**：`{x | ∀ i, dotV (a i) x ≤ 0}` 永不空（`0` 是见证）。 -/
theorem nonpos_set_never_empty {m d : ℕ} (a : Fin m → (Fin d → ℝ)) :
    {x : Fin d → ℝ | ∀ i, dotV (a i) x ≤ 0}.Nonempty :=
  ⟨0, nonpos_set_nonempty a⟩

/-- **任务书原始命题（逐字复现）**：
`{x | ∀ i, dotV (a i) x ≤ 0} = ∅ ⟹ ∃ λ ≥ 0, (∀ j, ∑ i, λᵢ aᵢⱼ = 0) ∧ 0 < ∑ λᵢ`。

**诚实标注：前提不可满足**（`0` 恒在该集合中，见 `nonpos_set_nonempty`），
因此本命题是**空真**的假言命题，**不是有内容的 Farkas 引理**。
其证明只是从前提导出 `False`（`0 ∈ ∅`）。 -/
theorem farkas_literal_vacuous {m d : ℕ} (a : Fin m → (Fin d → ℝ)) :
    ({x : Fin d → ℝ | ∀ i, dotV (a i) x ≤ 0} = ∅ →
      ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧
        (∀ j, (∑ i, lam i * a i j) = 0) ∧ 0 < ∑ i, lam i) := by
  intro h
  have h0 := nonpos_set_nonempty a
  rw [h] at h0
  exact absurd h0 (by simp)

/-! ## 三、非负组合锥 -/

/-- **非负组合**：`b` 是 `grad` 的非负线性组合（坐标形式），即存在 `λ ≥ 0` 使
`∀ j, b j = ∑ i, λᵢ · grad i j`。这正是 KKT 驻点方程 `∇f + ∑ λᵢ ∇gᵢ = 0`
中的向量部分（取 `b = -gradF`）。 -/
def HasNonnegCombo {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (b : Fin d → ℝ) : Prop :=
  ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ ∀ j, b j = ∑ i, lam i * grad i j

/-- **非负组合锥** `cone{∇gᵢ} = {∑ λᵢ ∇gᵢ | λᵢ ≥ 0}`，其载体恰为 `HasNonnegCombo grad`。 -/
def nonnegComboCone {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) : ConvexCone ℝ (Fin d → ℝ) where
  carrier := {b | HasNonnegCombo grad b}
  smul_mem' c hc b hb := by
    obtain ⟨lam, hlam, hb⟩ := hb
    refine ⟨fun i => c * lam i, fun i => mul_nonneg hc.le (hlam i), fun j => ?_⟩
    show c * b j = ∑ i, (c * lam i) * grad i j
    rw [hb j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  add_mem' b hb b' hb' := by
    obtain ⟨lam, hlam, hb⟩ := hb
    obtain ⟨mu, hmu, hb'⟩ := hb'
    refine ⟨fun i => lam i + mu i, fun i => add_nonneg (hlam i) (hmu i), fun j => ?_⟩
    show b j + b' j = ∑ i, (lam i + mu i) * grad i j
    rw [hb j, hb' j, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **坐标形式与「向量和」形式的等价**：
`HasNonnegCombo grad b ↔ ∃ λ ≥ 0, b = ∑ i, λᵢ • grad i`。 -/
theorem hasNonnegCombo_iff_sum {m d : ℕ} {grad : Fin m → (Fin d → ℝ)} {b : Fin d → ℝ} :
    HasNonnegCombo grad b ↔
      ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ b = ∑ i, lam i • grad i := by
  constructor
  · rintro ⟨lam, hlam, hb⟩
    refine ⟨lam, hlam, ?_⟩
    funext j
    rw [hb j, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  · rintro ⟨lam, hlam, hb⟩
    refine ⟨lam, hlam, fun j => ?_⟩
    rw [hb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]

/-- **每个生成元都属于非负组合锥**：`grad i ∈ cone{grad j}`（取 `λ = eᵢ`）。 -/
theorem grad_mem_nonnegComboCone {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (i : Fin m) :
    grad i ∈ nonnegComboCone grad := by
  refine ⟨fun k => if k = i then (1 : ℝ) else 0, fun k => ?_, fun j => ?_⟩
  · by_cases h : k = i
    · simp [h]
    · simp [h]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

/-! ## 四、闭凸锥的 Farkas 引理 -/

/-- **闭非空凸锥含 `0`**：`K` 闭、非空、是凸锥 ⟹ `0 ∈ K`。
证明：取 `x ∈ K`，`t • x → 0`（`t → 0⁺`）且 `t • x ∈ K`（`t > 0`），由闭性得 `0 ∈ K`。 -/
theorem zero_mem_of_closed_convexCone {d : ℕ} (K : ConvexCone ℝ (Fin d → ℝ))
    (hne : (K : Set (Fin d → ℝ)).Nonempty) (hc : IsClosed (K : Set (Fin d → ℝ))) :
    (0 : Fin d → ℝ) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  -- `hc.mem_of_tendsto` 需要 `[NeBot b]`，但 `b` 在调用时仍是元变量，
  -- 实例搜索会卡住。故把 `NeBot` 实例**显式**作为参数传入（`mem_of_tendsto` 的
  -- `[NeBot b]` 是实例隐参，可命名传入）。
  haveI hnb : (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)).NeBot :=
    nhdsWithin_Ioi_neBot' ⟨1, by simp⟩ le_rfl
  refine IsClosed.mem_of_tendsto (f := fun t : ℝ => t • x)
    (b := 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) hc ?_ ?_
  · have htend : Tendsto (fun t : ℝ => t • x) (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 ((0 : ℝ) • x)) :=
      ((continuous_id.smul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using htend
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact K.smul_mem ht hx

/-- **抽象 Farkas 引理（双极的 nontrivial 方向）**：设 `H` 是完备实内积空间，`K` 是非空闭凸锥。
若 `b` 满足「所有 `K` 的对偶锥元素对 `b` 取非负值」，则 `b ∈ K`（即 `K** ⊆ K`）。

证明：反设 `b ∉ K`，用 `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem`
分离出 `y`：`∀ x ∈ K, 0 ≤ ⟪x, y⟫` 且 `⟪y, b⟫ < 0`，与假设给的 `0 ≤ ⟪b, y⟫` 矛盾
（`real_inner_comm`）。 -/
theorem farkas_alternative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (K : ConvexCone ℝ H) (hne : (K : Set H).Nonempty)
    (hc : IsClosed (K : Set H)) {b : H}
    (h : ∀ y : H, (∀ x ∈ K, 0 ≤ ⟪x, y⟫) → 0 ≤ ⟪b, y⟫) : b ∈ K := by
  by_contra hb
  obtain ⟨y, hy, hyb⟩ := K.hyperplane_separation_of_nonempty_of_isClosed_of_nmem hne hc hb
  have h1 := h y hy
  rw [real_inner_comm y b] at h1
  linarith

/-- **Farkas 双极形式**：非空闭凸锥 `K` 满足 `(K*)* = K`，其中 `K* = K.innerDualCone`。
直接回收 mathlib 的 `ConvexCone.innerDualCone_of_innerDualCone_eq_self`。 -/
theorem farkas_bipolar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (K : ConvexCone ℝ H) (hne : (K : Set H).Nonempty)
    (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDualCone : Set H).innerDualCone = K :=
  ConvexCone.innerDualCone_of_innerDualCone_eq_self K hne hc

/-- **有限维坐标形式 Farkas（隐式方向）**：对 `Fin d → ℝ` 上的非空闭凸锥 `K` 与 `b`，
若 `b` 被「`K` 的 `dotV`-对偶锥」合法化，则 `b ∈ K`。

证明：反设 `b ∉ K`，在有限维局部凸空间 `Fin d → ℝ` 上用
`geometric_hahn_banach_closed_point` 得分离泛函 `f`（`u` 满足 `∀ a ∈ K, f a < u < f b`）。
由 `K` 是锥且 `0 ∈ K`（`zero_mem_of_closed_convexCone`）得 `u > 0`；再用 `t • a ∈ K`
（`t > 0`）与 `f a` 无上界推出 `∀ a ∈ K, f a ≤ 0`。取
`y := -(fun j => f (farkasStdBasisVec j))`（`farkasStdBasisVec` 为 `e_j` 标准基，本文件的
`farkas_continuousLinearMap_eq_dotV` 把 `f` 写成 `dotV`），则 `∀ x ∈ K, 0 ≤ dotV x y`，
由假设得 `0 ≤ dotV b y = -f b`，与 `0 < f b` 矛盾。 -/
theorem farkas_alternative_dotV {d : ℕ} (K : ConvexCone ℝ (Fin d → ℝ))
    (hne : (K : Set (Fin d → ℝ)).Nonempty) (hc : IsClosed (K : Set (Fin d → ℝ)))
    {b : Fin d → ℝ} (h : ∀ y : Fin d → ℝ, (∀ x ∈ K, 0 ≤ dotV x y) → 0 ≤ dotV b y) :
    b ∈ K := by
  by_contra hb
  obtain ⟨f, u, hfu, hfb⟩ := geometric_hahn_banach_closed_point K.convex hc hb
  have h0K : (0 : Fin d → ℝ) ∈ K := zero_mem_of_closed_convexCone K hne hc
  have hu : (0 : ℝ) < u := by
    have := hfu 0 h0K
    simpa using this
  have hle : ∀ a ∈ K, f a ≤ 0 := by
    intro a ha
    by_contra hneg
    push_neg at hneg
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u / f a < (n : ℝ) := exists_nat_gt (u / f a)
    have ht : (0 : ℝ) < (n : ℝ) + 1 := by
      -- `Nat.cast_nonneg n` 的目标类型含元变量，须显式给出 `ℝ` 实例。
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      linarith
    have hmem : ((n : ℝ) + 1) • a ∈ K := K.smul_mem ht ha
    have hlt := hfu _ hmem
    rw [map_smul, smul_eq_mul] at hlt
    have h1 : u < (n : ℝ) * f a := by
      rw [div_lt_iff hneg] at hn
      exact hn
    nlinarith [hlt, h1, hneg]
  have hfbpos : (0 : ℝ) < f b := lt_trans hu hfb
  have hkey : ∀ x : Fin d → ℝ, f x = dotV (fun j => f (farkasStdBasisVec j)) x :=
    fun x => farkas_continuousLinearMap_eq_dotV f x
  have hy : ∀ x ∈ K, 0 ≤ dotV x (-(fun j => f (farkasStdBasisVec j))) := by
    intro x hx
    have hx0 : f x ≤ 0 := hle x hx
    rw [dotV_neg_right, dotV_comm, ← hkey x]
    linarith
  have h2 := h (-(fun j => f (farkasStdBasisVec j))) hy
  have h3 : dotV b (-(fun j => f (farkasStdBasisVec j))) = -f b := by
    rw [dotV_neg_right, dotV_comm, ← hkey b]
  linarith

/-- **有限维 Farkas 引理（`ℝ^d` 坐标形式，iff）**：对任意非空闭凸锥
`K ⊆ Fin d → ℝ`，
`(∀ y, (∀ x ∈ K, 0 ≤ dotV x y) → 0 ≤ dotV b y) ↔ b ∈ K`。
正向（`b ∈ K`）平凡；反向即 `farkas_alternative_dotV`。

**诚实标注**：这里 `K` 是**给定的**闭凸锥；把 `K` 具体取成有限生成锥 `cone{∇gᵢ}` 时，
「有限生成锥本身闭」这一事实**未证**（见 `farkas_multiplier_criterion` 的说明）。 -/
theorem farkas_fin_conic {d : ℕ} (K : ConvexCone ℝ (Fin d → ℝ))
    (hne : (K : Set (Fin d → ℝ)).Nonempty) (hc : IsClosed (K : Set (Fin d → ℝ)))
    {b : Fin d → ℝ} :
    (∀ y : Fin d → ℝ, (∀ x ∈ K, 0 ≤ dotV x y) → 0 ≤ dotV b y) ↔ b ∈ K :=
  ⟨fun h => farkas_alternative_dotV K hne hc h, fun hb _ hy => hy b hb⟩

/-! ## 五、乘子判据（Farkas 的可计算形式） -/

/-- **Farkas 乘子判据**：`HasNonnegCombo grad (-gradF)`（即 KKT 驻点方程
`∇f + ∑ λᵢ ∇gᵢ = 0`、`λ ≥ 0` 的可解性）**等价于**
「所有可行方向 `v`（`∀ i, ⟨∇gᵢ, v⟩ ≤ 0`）都满足 `⟨∇f, v⟩ ≥ 0`」
（即可行方向都不下降 `f`）。

- 前向（`⟹`）：纯代数（`dotV_sum_smul_left` + `Finset.sum_nonpos`）；
- 反向（`⟸`）：把 `v` 换成 `-v` 得 `-gradF` 在 `nonnegComboCone grad` 的对偶锥中，
  再调用 `farkas_alternative_dotV`。

**诚实标注（未证/降级）**：反向需要 `IsClosed (nonnegComboCone grad)`。该闭性在数学上
对有限生成锥成立，但 **mathlib 4.14 未提供有限生成锥闭性的引理**（无多面体锥 API），
故此处作为**显式假设** `hc` 保留，不谎称已证。 -/
theorem farkas_multiplier_criterion {m d : ℕ} (grad : Fin m → (Fin d → ℝ))
    (gradF : Fin d → ℝ) (hc : IsClosed (nonnegComboCone grad : Set (Fin d → ℝ))) :
    HasNonnegCombo grad (-gradF) ↔
      (∀ v : Fin d → ℝ, (∀ i, dotV (grad i) v ≤ 0) → 0 ≤ dotV gradF v) := by
  constructor
  · rintro ⟨lam, hlam, hb⟩ v hv
    have hb_eq : (∑ i, lam i • grad i) = -gradF := by
      funext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (hb j).symm
    have h1 : dotV (-gradF) v ≤ 0 := by
      rw [← hb_eq, dotV_sum_smul_left]
      exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hv i)
    have h2 := dotV_neg_left gradF v
    linarith
  · intro h
    refine farkas_alternative_dotV (nonnegComboCone grad) ⟨0, ?_⟩ hc ?_
    · exact ⟨fun _ => 0, fun _ => le_refl 0, fun j => by simp⟩
    · intro y hy
      have h1 : ∀ i, dotV (grad i) (-y) ≤ 0 := by
        intro i
        have hg := hy (grad i) (grad_mem_nonnegComboCone grad i)
        rw [dotV_neg_right]
        linarith
      have h2 := h (-y) h1
      rw [dotV_neg_right] at h2
      rw [dotV_neg_left]
      linarith

/-! ## 六、MFCQ 的扰动与严格分离 -/

/-- **MFCQ 扰动（约束部分的纯代数引理）**：若 `v` 是弱可行方向（`∀ i, ⟨∇gᵢ, v⟩ ≤ 0`），
`w` 是严格方向（`∀ i, ⟨∇gᵢ, w⟩ < 0`），则对任意 `t > 0`，`v + t w` 仍是**严格**方向
（`∀ i, ⟨∇gᵢ, v + t w⟩ < 0`）。 -/
theorem dotV_add_smul_strict {m d : ℕ} {grad : Fin m → (Fin d → ℝ)} {v w : Fin d → ℝ}
    (hv : ∀ i, dotV (grad i) v ≤ 0) (hw : ∀ i, dotV (grad i) w < 0) {t : ℝ} (ht : 0 < t) :
    ∀ i, dotV (grad i) (v + t • w) < 0 := by
  intro i
  rw [dotV_add_right, dotV_smul_right]
  rcases lt_or_eq_of_le (hv i) with hlt | heq
  · have := mul_neg_of_pos_of_neg ht (hw i)
    linarith
  · rw [heq, zero_add]
    exact mul_neg_of_pos_of_neg ht (hw i)

/-- **MFCQ 扰动（目标值取正的情形）**：设 `MFCQ grad`（`∃ w, ∀ i, ⟨∇gᵢ, w⟩ < 0`），
`v` 满足 `∀ i, ⟨∇gᵢ, v⟩ ≤ 0` 且 `0 < ⟨∇f, v⟩`。则存在 `v'` 使
`∀ i, ⟨∇gᵢ, v'⟩ < 0` 且 `0 < ⟨∇f, v'⟩`。

证明：`v' = v + t w`，`t > 0` 取足够小。约束部分对**任意** `t > 0` 自动成立
（`dotV_add_smul_strict`）；目标部分只需 `t · ⟨∇f, w⟩` 不太负：
若 `⟨∇f, w⟩ ≥ 0` 取 `t = 1`，否则取 `t = ⟨∇f, v⟩ / (2·(−⟨∇f, w⟩))`。 -/
theorem mfcq_perturb {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (gradF : Fin d → ℝ)
    (hw : ∃ w : Fin d → ℝ, ∀ i, dotV (grad i) w < 0) {v : Fin d → ℝ}
    (hv : ∀ i, dotV (grad i) v ≤ 0) (hvd : 0 < dotV gradF v) :
    ∃ v' : Fin d → ℝ, (∀ i, dotV (grad i) v' < 0) ∧ 0 < dotV gradF v' := by
  obtain ⟨w, hw⟩ := hw
  by_cases hB : 0 ≤ dotV gradF w
  · refine ⟨v + (1 : ℝ) • w, dotV_add_smul_strict hv hw zero_lt_one, ?_⟩
    rw [dotV_add_right, dotV_smul_right, one_mul]
    linarith
  · push_neg at hB
    refine ⟨v + (dotV gradF v / (2 * (-(dotV gradF w)))) • w, dotV_add_smul_strict hv hw ?_, ?_⟩
    · exact div_pos hvd (by linarith)
    · rw [dotV_add_right, dotV_smul_right]
      have hne : (2 : ℝ) * (-(dotV gradF w)) ≠ 0 := by linarith
      have heq : (dotV gradF v / (2 * (-(dotV gradF w)))) * dotV gradF w
          = -(dotV gradF v / 2) := by
        -- 记 `a = dotV gradF v`、`b = dotV gradF w`。`a / (2 * (-b)) * b = -(a / 2)`
        -- 在 `b ≠ 0` 时成立；`field_simp` 后的环等式交给 `ring`。
        have hb : dotV gradF w ≠ 0 := by
          intro h0
          rw [h0] at hB
          linarith
        field_simp
        ring
      linarith

/-- **MFCQ 扰动（目标值取负的下降方向情形）**：设 `MFCQ grad`，`v` 满足
`∀ i, ⟨∇gᵢ, v⟩ ≤ 0` 且 `⟨∇f, v⟩ < 0`。则存在 `v'` 使
`∀ i, ⟨∇gᵢ, v'⟩ < 0` 且 `⟨∇f, v'⟩ < 0`（**严格可行下降方向**）。
证明结构与 `mfcq_perturb` 对偶（取 `t = −⟨∇f, v⟩ / (2·⟨∇f, w⟩)` 于 `⟨∇f, w⟩ > 0` 的情形）。 -/
theorem mfcq_perturb_neg {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (gradF : Fin d → ℝ)
    (hw : ∃ w : Fin d → ℝ, ∀ i, dotV (grad i) w < 0) {v : Fin d → ℝ}
    (hv : ∀ i, dotV (grad i) v ≤ 0) (hvd : dotV gradF v < 0) :
    ∃ v' : Fin d → ℝ, (∀ i, dotV (grad i) v' < 0) ∧ dotV gradF v' < 0 := by
  obtain ⟨w, hw⟩ := hw
  by_cases hB : dotV gradF w ≤ 0
  · refine ⟨v + (1 : ℝ) • w, dotV_add_smul_strict hv hw zero_lt_one, ?_⟩
    rw [dotV_add_right, dotV_smul_right, one_mul]
    linarith
  · push_neg at hB
    refine ⟨v + (-(dotV gradF v) / (2 * dotV gradF w)) • w,
      dotV_add_smul_strict hv hw ?_, ?_⟩
    · exact div_pos (by linarith) (by linarith)
    · rw [dotV_add_right, dotV_smul_right]
      have hne : (2 : ℝ) * dotV gradF w ≠ 0 := by linarith
      have heq : (-(dotV gradF v) / (2 * dotV gradF w)) * dotV gradF w
          = -(dotV gradF v / 2) := by
        field_simp [hne]
        try ring
      linarith

/-- **MFCQ 严格分离（符号正确版）**：在 `MFCQ grad` 下，若**不存在**非负乘子
（`¬ HasNonnegCombo grad (-gradF)`），则存在**严格可行下降方向** `v`：
`∀ i, ⟨∇gᵢ, v⟩ < 0` 且 `⟨∇f, v⟩ < 0`。

证明：由 `farkas_multiplier_criterion` 的逆否得弱方向 `v`（`∀ i, ≤ 0`、`⟨∇f, v⟩ < 0`），
再用 `mfcq_perturb_neg` 升级为严格方向。

**诚实标注**：`hc`（`nonnegComboCone grad` 闭）是承继自乘子判据的**未证**假设，见文件头。 -/
theorem mfcq_strict_separation {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (gradF : Fin d → ℝ)
    (hc : IsClosed (nonnegComboCone grad : Set (Fin d → ℝ))) (hMFCQ : MFCQ grad)
    (hnc : ¬ HasNonnegCombo grad (-gradF)) :
    ∃ v : Fin d → ℝ, (∀ i, dotV (grad i) v < 0) ∧ dotV gradF v < 0 := by
  have hnot : ¬ (∀ v : Fin d → ℝ, (∀ i, dotV (grad i) v ≤ 0) → 0 ≤ dotV gradF v) :=
    fun h => hnc ((farkas_multiplier_criterion grad gradF hc).mpr h)
  push_neg at hnot
  obtain ⟨v, hv, hvd⟩ := hnot
  exact mfcq_perturb_neg grad gradF hMFCQ hv hvd

/-- **机器验证反例（标注：任务书符号不一致）**：任务书要求的命题
「`MFCQ grad` 且 `¬ HasNonnegCombo grad (-gradF)` ⟹ `∃ v, (∀ i, ⟨∇gᵢ, v⟩ < 0) ∧ 0 < ⟨∇f, v⟩`」
在 `d = 1`、`∇g = 1`、`∇f = 1` 时**为假**：此时 `MFCQ` 成立（`w = -1`），
`¬ HasNonnegCombo grad (-gradF)` 也成立（`-1 = λ · 1` 无 `λ ≥ 0` 解），
但 `⟨∇g, v⟩ = v`、`⟨∇f, v⟩ = v`，故结论要求 `v < 0 ∧ 0 < v`，不可能。

因此 MFCQ 的正确结论是**下降方向**（`⟨∇f, v⟩ < 0`），见 `mfcq_strict_separation`。 -/
theorem mfcq_strict_separation_literal_false :
    ∃ (grad : Fin 1 → (Fin 1 → ℝ)) (gradF : Fin 1 → ℝ),
      MFCQ grad ∧ ¬ HasNonnegCombo grad (-gradF) ∧
        ¬ (∃ v : Fin 1 → ℝ, (∀ i, dotV (grad i) v < 0) ∧ 0 < dotV gradF v) := by
  refine ⟨fun _ => fun _ => (1 : ℝ), fun _ => (1 : ℝ), ?_, ?_, ?_⟩
  · refine ⟨fun _ => (-1 : ℝ), ?_⟩
    intro i
    fin_cases i
    simp [dotV, Fin.sum_univ_one]
  · rintro ⟨lam, hlam, hb⟩
    have h1 := hb 0
    simp only [Pi.neg_apply, Fin.sum_univ_one, mul_one] at h1
    have h0 := hlam 0
    linarith
  · rintro ⟨v, hv, hvd⟩
    have h1 := hv 0
    simp [dotV, Fin.sum_univ_one] at h1 hvd
    linarith

end Lattice
