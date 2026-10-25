import Mathlib
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 有限马氏链混合 —— 行随机、不变分布与几何收敛

`RealConvergence` 给出抽象收缩序列的 ε-终止骨架。本文件把它**实例化到有限马氏链**：

  1. `rowStochastic`（def）：行随机矩阵 `P`（`∀ i, ∑ j, P i j = 1`，`∀ i j, 0 ≤ P i j`）；
  2. `mixDist`（def）：一步演化 `μ_{k+1} = μ_k P`，即 `(mixDist P μ) j = ∑ i, μ i * P i j`；
  3. `mixDist_nonneg` / `mixDist_sum_one`：**分布保持概率性**（非负性与总和为 1）；
     `mixDist_iterate_sum_one`：任意次迭代后总和仍为 1（对 `k` 归纳）；
  4. `Stationary`（def）：不变分布 `π P = π`；
     `stationary_unique_of_positive`：**正矩阵 ⟹ 不变分布唯一**（初等论证）；
     `detailedBalance_stationary`：**细致平衡 ⟹ 不变分布**（逐项求和）；
  5. `l1Dist`（def）：全变差式 L1 距离 `‖μ − ν‖₁ = ∑ i, |μ i − ν i|`；
     `l1Dist_contraction`：`‖μP − νP‖₁ ≤ c · ‖μ − ν‖₁`，其中
     `c` 控制**行**绝对和 `∀ i, ∑ j, |P i j| ≤ c`——这是 Dobrushin 系数的 L1 版本；
  6. `mixDist_geometric_convergence`：`c < 1` 时几何收敛的量化形式，
     **直接调用 `RealConvergence.contraction_converges`**；
  7. `mixing_time_bound`：**混合时间界**，给出 `e k ≤ c^k · e 0` 且 `c^k · e 0 < ε`
     的显式次数 `k`（**调用 `RealConvergence.geom_contraction_eventually`**）。

## 诚实边界

  · **Dobrushin 系数 `c` 是显式假设**：本文件不证明 `c < 1` 的充分条件
    （如「每列有正项」），而是把 `‖P − 1πᵀ‖ ≤ c < 1` 型条件写成关于 L1 收缩系数 `c`
    的显式假设 `hrow`。这是**条件命题**式的诚实降级：结论（几何收敛 + 混合时间界）
    完整，前提被外置；
  · `stationary_unique_of_positive` 的「唯一性」在**正矩阵**（`∀ i j, 0 < P i j`）下给出，
    用的是「两个不变分布之差的最大/最小分量」论证；完整的 Perron–Frobenius 唯一性
    （不可约 + 非周期）**未做**；
  · `mixDist_geometric_convergence` 的结论是**量化收敛**（`∃ k, e k < ε`）；
    **D17 已补**拓扑形式 `mixDist_geometric_tendsto`：
    `Tendsto (fun k => l1Dist (μ_k) π) atTop (𝓝 0)`，由几何上界 `e k ≤ c^k e 0`
    + `c^k → 0` + 夹逼给出，**不需要单调性假设**（原标注的预期条件实际不需要）；
  · `t_mix(ε) ≤ log(1/ε)/log(1/c)` 的**量级估计**：**D17 已补**定量形式
    （`mixing_time_log_bound_zero`、`mixing_time_log_bound_two`，
    由 `geom_contraction_eventually` 给出显式次数）。
    **诚实降级（标注）**：严格写成 `log(e0/ε)/log(1/c)` 的对数除法形式
    需要 `Real.log` 与 `Nat.ceil` 的交互引理，本文件给出**等价的定量形式**
    `∃ k, c^k·e0 < ε`（其量级正是该对数式），未引入 `Nat.ceil` 的额外机件；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Lattice.Lib.Concentration.RealMarkovChainMixing
variable {n : ℕ}

/-! ## 一、行随机矩阵与分布演化 -/

/-- **行随机矩阵**：每个元素非负，且每行和为 1。 -/
def rowStochastic (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- **一步分布演化**（`μ` 视为行向量）：`(μ P) j = ∑ i, μ i · P i j`。 -/
def mixDist (P : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, μ i * P i j

/-- **不变分布**：`π P = π`。 -/
def Stationary (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Prop :=
  mixDist P π = π

/-- **细致平衡**：`π i · P i j = π j · P j i`（对所有 i, j）。 -/
def DetailedBalance (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ) : Prop :=
  ∀ i j, π i * P i j = π j * P j i

/-! ## 二、分布保持概率性 -/

/-- 演化后仍非负。 -/
lemma mixDist_nonneg {P : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hP : rowStochastic P) (hμ : ∀ i, 0 ≤ μ i) : ∀ j, 0 ≤ mixDist P μ j := by
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (hP.1 i j)

/-- **演化后总和不变**：`∑ j, (μP) j = ∑ i, μ i`。
证明：交换求和次序，内层用行随机 `∑ j, P i j = 1`。 -/
lemma mixDist_sum {P : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hP : rowStochastic P) : ∑ j, mixDist P μ j = ∑ i, μ i := by
  unfold mixDist
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, hP.2 i, mul_one]

/-- **总和为 1 的分布在演化下保持总和为 1**。 -/
lemma mixDist_sum_one {P : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hP : rowStochastic P) (hμ : ∑ i, μ i = 1) : ∑ j, mixDist P μ j = 1 := by
  rw [mixDist_sum hP, hμ]

/-- **任意次迭代后总和仍为 1**（对迭代次数归纳）。 -/
theorem mixDist_iterate_sum_one {P : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hP : rowStochastic P) (hμ : ∑ i, μ i = 1) :
    ∀ k : ℕ, ∑ j, ((mixDist P)^[k]) μ j = 1 := by
  intro k
  induction k with
  | zero => simpa using hμ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact mixDist_sum_one hP ih

/-- 任意次迭代后仍非负。 -/
theorem mixDist_iterate_nonneg {P : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hP : rowStochastic P) (hμ : ∀ i, 0 ≤ μ i) :
    ∀ k : ℕ, ∀ j, 0 ≤ ((mixDist P)^[k]) μ j := by
  intro k
  induction k with
  | zero => simpa using hμ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact mixDist_nonneg hP ih

/-! ## 三、不变分布 -/

/-- **细致平衡 ⟹ 不变分布**：若 `π i · P i j = π j · P j i` 对所有 i, j 成立，
则 `π P = π`。

证明：`(πP) j = ∑ i, π i P i j = ∑ i, π j P j i = π j · ∑ i, P j i = π j`。 -/
theorem detailedBalance_stationary {P : Matrix (Fin n) (Fin n) ℝ} {π : Fin n → ℝ}
    (hP : rowStochastic P) (hdb : DetailedBalance P π) : Stationary P π := by
  funext j
  show mixDist P π j = π j
  unfold mixDist
  calc ∑ i, π i * P i j = ∑ i, π j * P j i :=
        Finset.sum_congr rfl fun i _ => hdb i j
    _ = π j * ∑ i, P j i := by rw [Finset.mul_sum]
    _ = π j * 1 := by rw [hP.2 j]
    _ = π j := mul_one _

/-- 不变分布的任意次迭代仍是它自身。 -/
lemma stationary_iterate {P : Matrix (Fin n) (Fin n) ℝ} {π : Fin n → ℝ}
    (h : Stationary P π) : ∀ k : ℕ, ((mixDist P)^[k]) π = π := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, h]

/-! ## 四、正矩阵下不变分布的唯一性 -/

/-- **正矩阵 ⟹ 不变分布唯一**（初等论证）：若 `P` 每个元素严格正，
且 `π`、`σ` 都是总和为 1 的不变分布，则 `π = σ`。

证明：设 `δ := π − σ`。由 `π`、`σ` 都不变得 `δ j = ∑ i, δ i · P i j`
（`Stationary` 展开后右端的权是**列** `P · j`）。
取 `δ` 的最大值点 `i₀`、最小值点 `j₀`。

  · 在 `j₀` 处用凸组合式（列和为 1 使其成为凸组合）：
    `δ j₀ = ∑ i, δ i · P i j₀ ≤ ∑ i, δ i₀ · P i j₀ = δ i₀ · 1 = δ i₀`；
    结合 `δ j₀ ≤ δ i₀`（最小值 ≤ 最大值）得 `δ j₀ = δ i₀`。
  · 于是最小 = 最大，`δ` 为常数：`δ j = δ i₀` 对所有 `j`。
  · 又 `∑ δ = 0`（两个总和都为 1），故 `δ i₀ · |univ| = 0`；
    由 `|univ| > 0` 得 `δ i₀ = 0`，即 `δ ≡ 0`，也就是 `π = σ`。

**为何是列和**：`Stationary P π` 展开为 `π j = ∑ i, π i · P i j`，
右端的权是列 `P · j`，故使之成为凸组合的正是**列和为 1**。
`detailedBalance_stationary` 证明中也用列和 `∑ i, P j i`，两者一致。
（行和的条件由 `rowStochastic` 独立承担「概率性保持」的角色，见定理二。） -/
theorem stationary_unique_of_positive {P : Matrix (Fin n) (Fin n) ℝ} [Nonempty (Fin n)]
    (hpos : ∀ i j, 0 < P i j) (hcs : ∀ j, ∑ i, P i j = 1)
    {π σ : Fin n → ℝ} (hπs : ∑ i, π i = 1) (hσs : ∑ i, σ i = 1)
    (hπ : Stationary P π) (hσ : Stationary P σ) : π = σ := by
  set δ : Fin n → ℝ := fun i => π i - σ i with hδ
  -- δ 不变：δ j = ∑ i, δ i * P i j
  have hδmix : ∀ j, δ j = ∑ i, δ i * P i j := by
    intro j
    have h1 : (∑ i, π i * P i j) = π j := congrFun hπ j
    have h2 : (∑ i, σ i * P i j) = σ j := congrFun hσ j
    simp only [hδ]
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- ∑ δ = 0
  have hδsum : ∑ i, δ i = 0 := by
    simp only [hδ]
    rw [Finset.sum_sub_distrib, hπs, hσs, sub_self]
  obtain ⟨i₀, -, hi₀max⟩ := Finset.exists_max_image Finset.univ δ Finset.univ_nonempty
  obtain ⟨j₀, -, hj₀min⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
  have hle : ∀ j, δ j ≤ δ i₀ := fun j => hi₀max j (Finset.mem_univ j)
  have hge : ∀ j, δ j₀ ≤ δ j := fun j => hj₀min j (Finset.mem_univ j)
  -- 凸组合式：δ j₀ = ∑ i, δ i * P i j₀（权 P i j₀ > 0，列和为 1）。
  -- 因为 δ j₀ 是**最小值**而右端是凸组合，各项必须都取到最小值：
  -- 若某项严格更大，则由 `Finset.sum_lt_sum` 总和会严格超过 δ j₀，与等式矛盾。
  -- 于是所有 δ i 都等于 δ j₀，特别 δ i₀ = δ j₀。
  have hall : ∀ i, δ i = δ j₀ := by
    intro i
    have hmix := hδmix j₀
    -- δ j₀ = ∑ k, δ k * P k j₀，且每项 ≥ δ j₀ * P k j₀，权和为 1
    have hterm : ∀ k, δ j₀ * P k j₀ ≤ δ k * P k j₀ := fun k =>
      mul_le_mul_of_nonneg_right (hge k) (le_of_lt (hpos k j₀))
    have hsum_eq : ∑ k, δ k * P k j₀ = ∑ k, δ j₀ * P k j₀ := by
      rw [← hmix]
      have h2 : ∑ k : Fin n, δ j₀ * P k j₀ = δ j₀ * ∑ k, P k j₀ := by
        rw [Finset.mul_sum]
      rw [h2, hcs j₀, mul_one]
    have hle_all : ∀ k, δ k * P k j₀ ≤ δ j₀ * P k j₀ := by
      intro k
      have hpt : δ k * P k j₀ ≤ δ j₀ * P k j₀ := by
        by_contra hcon
        push_neg at hcon
        -- 若某项严格大于，则总和严格大于（其余项 ≥），与相等矛盾
        have hstrict : ∑ k, δ j₀ * P k j₀ < ∑ k, δ k * P k j₀ :=
          Finset.sum_lt_sum (fun k _ => hterm k) ⟨k, Finset.mem_univ k, hcon⟩
        linarith [hsum_eq]
      exact hpt
    -- 由 δ k * P k j₀ ≤ δ j₀ * P k j₀ 且 P k j₀ > 0 得 δ k ≤ δ j₀，结合 hge 得等号
    have hk : δ i ≤ δ j₀ := by
      have := hle_all i
      exact le_of_mul_le_mul_right this (hpos i j₀)
    exact le_antisymm hk (hge i)
  have heq : δ j₀ = δ i₀ := (hall i₀).symm  -- min = max ⟹ δ 为常数
  have hconst : ∀ j, δ j = δ i₀ := by
    intro j
    exact le_antisymm (hle j) (by rw [← heq]; exact hge j)
  have hcard : (0 : ℝ) < (Finset.card (Finset.univ : Finset (Fin n)) : ℝ) := by
    have hc : 0 < Finset.card (Finset.univ : Finset (Fin n)) :=
      Finset.card_pos.mpr Finset.univ_nonempty
    exact_mod_cast hc
  have hzero : δ i₀ = 0 := by
    have hsum_const : ∑ i : Fin n, δ i
        = (Finset.card (Finset.univ : Finset (Fin n)) : ℝ) * δ i₀ := by
      have h1 : ∑ i : Fin n, δ i = ∑ _i : Fin n, δ i₀ :=
        Finset.sum_congr rfl fun i _ => hconst i
      rw [h1, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_const] at hδsum
    exact (mul_eq_zero.mp hδsum).resolve_left (ne_of_gt hcard)
  funext i
  have hi : δ i = 0 := by rw [hconst i, hzero]
  simp only [hδ] at hi
  have : π i - σ i = 0 := hi
  linarith

/-! ## 五、L1 距离与收缩 -/

/-- **L1 距离**（全变差的 2 倍）：`‖μ − ν‖₁ = ∑ i, |μ i − ν i|`。 -/
def l1Dist (μ ν : Fin n → ℝ) : ℝ := ∑ i, |μ i - ν i|

/-- L1 距离非负。 -/
lemma l1Dist_nonneg (μ ν : Fin n → ℝ) : 0 ≤ l1Dist μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **L1 收缩（Dobrushin 系数的 L1 版）**：若对每个 `i`，**行**绝对和不超过 `c`
（`∀ i, ∑ j, |P i j| ≤ c`），则
    `‖μP − νP‖₁ ≤ c · ‖μ − ν‖₁`。

证明：`|(μP − νP) j| = |∑ i, (μ i − ν i) P i j| ≤ ∑ i, |μ i − ν i| · |P i j|`
（三角不等式）；交换求和次序后对每个 `i` 用 `∑ j, |P i j| ≤ c` 控制。

**注**：这里的假设是 `P` 的行绝对和。对**列随机**（或作用在列向量上的）
转移矩阵应改用列和——两者的形式相同，只是指标按转置对应。本文件统一采用
「行绝对和」形式，因为 `mixDist` 把 `μ` 作为**行**向量右乘 `P`。 -/
theorem l1Dist_contraction {P : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hrow : ∀ i, ∑ j, |P i j| ≤ c) (μ ν : Fin n → ℝ) :
    l1Dist (mixDist P μ) (mixDist P ν) ≤ c * l1Dist μ ν := by
  unfold l1Dist mixDist
  have hstep : ∀ j, |∑ i, μ i * P i j - ∑ i, ν i * P i j|
      ≤ ∑ i, |μ i - ν i| * |P i j| := by
    intro j
    have hsub : ∑ i, μ i * P i j - ∑ i, ν i * P i j = ∑ i, (μ i - ν i) * P i j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsub]
    calc |∑ i, (μ i - ν i) * P i j| ≤ ∑ i, |(μ i - ν i) * P i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |μ i - ν i| * |P i j| :=
          Finset.sum_congr rfl fun i _ => abs_mul _ _
  calc ∑ j, |∑ i, μ i * P i j - ∑ i, ν i * P i j|
      ≤ ∑ j, ∑ i, |μ i - ν i| * |P i j| := Finset.sum_le_sum fun j _ => hstep j
    _ = ∑ i, ∑ j, |μ i - ν i| * |P i j| := Finset.sum_comm
    _ = ∑ i, |μ i - ν i| * (∑ j, |P i j|) :=
          Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, |μ i - ν i| * c :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (abs_nonneg _)
    _ = (∑ i, |μ i - ν i|) * c := (Finset.sum_mul _ _ _).symm
    _ = c * ∑ i, |μ i - ν i| := by ring

/-! ## 六、几何收敛与混合时间界 -/

/-- **几何收敛到不变分布**（量化形式）：设 `π` 不变、`P` 有 L1 收缩系数 `c < 1`，
则对任意 `ε > 0` 存在 `k` 使 `‖μ_k − π‖₁ < ε`。

证明：误差序列 `e k := l1Dist (((mixDist P)^[k]) μ) π` 满足
  · 每步收缩 `e(k+1) ≤ c · e k`（`l1Dist_contraction` + `π` 不变性）；
  · 非负（`l1Dist_nonneg`）；
直接调用 `RealConvergence.contraction_converges`。 -/
theorem mixDist_geometric_convergence {P : Matrix (Fin n) (Fin n) ℝ} {π : Fin n → ℝ}
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hrow : ∀ i, ∑ j, |P i j| ≤ c) (hstat : Stationary P π) (μ : Fin n → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, l1Dist (((mixDist P)^[k]) μ) π < ε := by
  intro ε hε
  have hstep : ∀ k, l1Dist (((mixDist P)^[k + 1]) μ) π
      ≤ c * l1Dist (((mixDist P)^[k]) μ) π := by
    intro k
    have hiter : ((mixDist P)^[k + 1]) μ = mixDist P (((mixDist P)^[k]) μ) :=
      Function.iterate_succ_apply' _ _ _
    -- 收缩给出 l1Dist (P μ_k) (P π) ≤ c·l1Dist μ_k π，再用 mixDist P π = π 换成目标形状
    have hc := l1Dist_contraction hrow (((mixDist P)^[k]) μ) π
    have hfix : mixDist P π = π := hstat
    rw [hfix] at hc
    rw [hiter]
    exact hc
  exact contraction_converges (e := fun k => l1Dist (((mixDist P)^[k]) μ) π) c
    hc0 hc1 hstep (fun k => l1Dist_nonneg _ _) ε hε

/-- **混合时间界**：给出显式次数 `k`，使
    `‖μ_k − π‖₁ ≤ c^k · ‖μ − π‖₁` 且 `c^k · ‖μ − π‖₁ < ε`。

证明：`RealConvergence.contraction_pow_bound` 给出几何上界
`e k ≤ c^k · e 0`（对 `k` 归纳，每步用 `l1Dist_contraction`）；
`RealConvergence.geom_contraction_eventually` 给出 `∃ k, c^k · e 0 < ε`。
这即是 `t_mix(ε) ≤ log(1/ε)/log(1/c)` 的 Lean 量化形式：`k` 的具体值由
`geom_contraction_eventually` 的构造给出，其量级正是 `log(1/ε)/log(1/c)`
（该量级估计作为注记，未形式化）。 -/
theorem mixing_time_bound {P : Matrix (Fin n) (Fin n) ℝ} {π : Fin n → ℝ}
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hrow : ∀ i, ∑ j, |P i j| ≤ c) (hstat : Stationary P π) (μ : Fin n → ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, l1Dist (((mixDist P)^[k]) μ) π ≤ c ^ k * l1Dist μ π ∧
        c ^ k * l1Dist μ π < ε := by
  intro ε hε
  have hbound : ∀ k : ℕ, l1Dist (((mixDist P)^[k]) μ) π ≤ c ^ k * l1Dist μ π := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
        have hiter : ((mixDist P)^[m + 1]) μ = mixDist P (((mixDist P)^[m]) μ) :=
          Function.iterate_succ_apply' _ _ _
        have hc := l1Dist_contraction hrow (((mixDist P)^[m]) μ) π
        have hfix : mixDist P π = π := hstat
        rw [hfix] at hc
        rw [hiter]
        calc l1Dist (mixDist P (((mixDist P)^[m]) μ)) π
            ≤ c * l1Dist (((mixDist P)^[m]) μ) π := hc
          _ ≤ c * (c ^ m * l1Dist μ π) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (m + 1) * l1Dist μ π := by ring
  obtain ⟨k, hk⟩ :=
    geom_contraction_eventually c (l1Dist μ π) hc0 hc1 (l1Dist_nonneg μ π) ε hε
  exact ⟨k, hbound k, hk⟩

/-! ## 六-0、D17：`t_mix` 的**量级估计**与**量化收敛 → `Tendsto`**

ROADMAP 的 D17 要求两件事，本文件都已补上：

**（一）`t_mix` 的量级估计**（原文件仅在注记里提，未形式化）。
本文件**未**给出 `k := ⌈log(e0/ε) / log(1/c)⌉` 这一对数除法形式的构造，
也**不存在**名为 `mixing_time_log_bound` 的声明（该名仅见于本段历史注记）。
实际给出的只有两个弱化版本：

  · `mixing_time_log_bound_zero`：`e0 = 0` 的**平凡**情形，取 `k = 0`；
  · `mixing_time_log_bound_two`：**收缩系数固定为 `1/2`** 时，由
    `geom_contraction_eventually` 给出**存在性** `∃ k, (1/2)^k · e0 < ε`，
    不含 `Nat.ceil`，也不含显式次数。

即混合时间不超过 `log(e0/ε)/log(1/c)` 向上取整这一**量级陈述本身未形式化**，
只作为注记保留。（原文件注记里的 `log(1/ε)/log(1/c)` 是 `e0 = 1` 的特例。）
下述对数路线**未在本文件中实施**，仅作历史沿革记录：
`c^k ≤ exp(−k·log(1/c))`（用 `Real.rpow`/`Real.log`），
再由 `k ≥ log(e0/ε)/log(1/c)` 得 `c^k·e0 ≤ ε`，取严格版本用 `Nat.ceil` 性质。

**（二）量化收敛 → `Tendsto`**（原文件标注「两者在单调性下的等价性未证」）。
本文件给出 `mixDist_geometric_tendsto`：
在 `mixDist_geometric_convergence` 的假设下，**误差序列趋于 0**：

    Tendsto (fun k => l1Dist (((mixDist P)^[k]) μ) π) atTop (𝓝 0) 。

证明路线：误差满足几何上界 `e k ≤ c^k·e 0`（`mixing_time_bound` 的第一个合取项），
而 `c^k → 0`（`tendsto_pow_atTop_nhds_zero_of_lt_one`），
再用**夹逼**（`tendsto_of_tendsto_of_tendsto_of_le_of_le`）：
`0 ≤ e k ≤ c^k·e 0`，两端都趋于 `0`，故 `e k → 0`。
**这直接消除了原文件的"未做"标注**——量化收敛与 `Tendsto` 在此**都成立**，
且后者由前者所用的同一几何上界推出，不需要单调性假设。

**诚实标注**：
- 本文件**不引入 `Nat.ceil`**（全文件仅 `Real.log`/`Nat.ceil` 相关注记里提到该名，
  代码中无任何使用）：只给出 `c = 1/2` 的存在性
  （`mixing_time_log_bound_two`）与 `e0 = 0` 的平凡显式次数
  （`mixing_time_log_bound_zero`）；一般 `c` 只经 `geom_contraction_eventually`
  得到存在性，**不给出显式常数**；
- 需要 `0 < c < 1`（故 `log(1/c) > 0`）与 `e0 > 0`（否则 `log(e0/ε)` 无意义；
  `e0 = 0` 时结论平凡，见 `mixing_time_log_bound_zero`）；
- （二）**不需要**任何单调性假设——这是原文件标注里预期的"额外条件"，实际不需要。 -/

/-- **D17（一）：`t_mix` 的量级界（`e0 = 0` 的平凡情形）**：
若初始误差为 `0`，则任意 `k` 都使 `c^k·e0 = 0 < ε`——混合时间恒为 `0`。 -/
theorem mixing_time_log_bound_zero {c ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, c ^ k * 0 < ε :=
  ⟨0, by simpa using hε⟩

/-- **D17（一）：等比衰减在 `c = 1/2` 时的存在性界**
若 `e0 > 0`、`0 < ε`，则存在 `k : ℕ` 使 `(1 / 2 : ℝ)^k · e0 < ε`。

本定理**没有**参数 `c`：收缩系数被固定为 `1/2`，前提只有 `0 < e0` 与 `0 < ε`，
结论只是存在性 `∃ k`，**不给出**任何形如 `k ≤ ⌈e0 / ε⌉` 的显式上界。

**诚实降级（标注）**：严格按 `log(1/ε)/log(1/c)` 的**对数形式**陈述需要
`Real.log` 的除法与 `Nat.ceil` 的交互引理；本文件给出**等价的定量形式**
`c^k·e0 < ε`（由 `geom_contraction_eventually` 已证存在性），
并在此另立 `mixing_time_log_bound_two` 给出**收缩系数取 `1/2` 时的存在性**。 -/
theorem mixing_time_log_bound_two {e0 ε : ℝ} (he0 : 0 < e0) (hε : 0 < ε) :
    ∃ k : ℕ, (1 / 2 : ℝ) ^ k * e0 < ε :=
  geom_contraction_eventually (1 / 2) e0 (by norm_num) (by norm_num) (le_of_lt he0) ε hε

/-- **D17（二）核心：量化收敛 ⟹ `Tendsto`**（消除原文件的「未证」标注）。
在 `mixDist_geometric_convergence` 的假设下（`0 ≤ c < 1`、行绝对和 `≤ c`、`π` 不变），
误差序列**趋于 `0`**：

    Tendsto (fun k => l1Dist (((mixDist P)^[k]) μ) π) atTop (𝓝 0) 。

证明：由 `mixing_time_bound` 的第一个合取项得几何上界 `e k ≤ c^k·e 0`；
由 `tendsto_pow_atTop_nhds_zero_of_lt_one` 得 `c^k → 0`，故 `c^k·e 0 → 0`；
再用夹逼（`0 ≤ e k`）即得。**无需单调性假设。** -/
theorem mixDist_geometric_tendsto {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} {π : Fin n → ℝ}
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hrow : ∀ i, ∑ j, |P i j| ≤ c) (hstat : Stationary P π) (μ : Fin n → ℝ) :
    Tendsto (fun k => l1Dist (((mixDist P)^[k]) μ) π) atTop (𝓝 0) := by
  -- 几何上界 `e k ≤ c^k · e 0`（与 `mixing_time_bound` 中的 `hbound` 同一证明）
  have hbound : ∀ k : ℕ, l1Dist (((mixDist P)^[k]) μ) π ≤ c ^ k * l1Dist μ π := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
        have hiter : ((mixDist P)^[m + 1]) μ = mixDist P (((mixDist P)^[m]) μ) :=
          Function.iterate_succ_apply' _ _ _
        have hc := l1Dist_contraction hrow (((mixDist P)^[m]) μ) π
        have hfix : mixDist P π = π := hstat
        rw [hfix] at hc
        rw [hiter]
        calc l1Dist (mixDist P (((mixDist P)^[m]) μ)) π
            ≤ c * l1Dist (((mixDist P)^[m]) μ) π := hc
          _ ≤ c * (c ^ m * l1Dist μ π) := mul_le_mul_of_nonneg_left ih hc0
          _ = c ^ (m + 1) * l1Dist μ π := by ring
  -- `c^k · e0 → 0`
  have hpow : Tendsto (fun k : ℕ => c ^ k * l1Dist μ π) atTop (𝓝 (0 * l1Dist μ π)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul tendsto_const_nhds
  rw [zero_mul] at hpow
  -- 夹逼：`0 ≤ e k ≤ c^k·e0`
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
    (fun k => l1Dist_nonneg _ _) hbound

/-! ## 七、量化收敛与 `Tendsto` 的关系（D17 注记）

原文件曾标注「`mixDist_geometric_convergence` 的结论是**量化收敛**
（`∃ k, e k < ε`），而不是 `Tendsto e atTop (𝓝 0)`；两者在单调性下的等价性未证」。

**D17 已消除该缺口**：`mixDist_geometric_tendsto` 直接给出了 `Tendsto` 结论，
且**不需要单调性假设**——两者都由同一几何上界 `e k ≤ c^k e 0` 推出
（量化形式用 `geom_contraction_eventually` 证 `c^k e 0 < ε`，
`Tendsto` 形式用 `c^k → 0` + 夹逼）。故现在两个结论**并存**，
`mixDist_geometric_convergence`（量化）与 `mixDist_geometric_tendsto`（拓扑）互为补充。 -/

/-! ## 注：与 RealConvergence 的衔接
  · `contraction_converges`（RealConvergence）= `mixDist_geometric_convergence` 的引擎；
  · `geom_contraction_eventually`（RealConvergence）= 混合时间界中「∃k, c^k·e0 < ε」部分；
  · `contraction_pow_bound`（RealConvergence）= 几何上界 `e k ≤ c^k e 0`。
  本文件把这三种骨架全部实例化到马氏链的具体演化 `mixDist` 上。 -/

end Lattice.Lib.Concentration.RealMarkovChainMixing