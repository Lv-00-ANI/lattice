import Mathlib

/-!
# LATTICE: dropped-mass 误差界 —— top-k 稀疏近似的理论保证

稀疏路由调研（research/real-world/norm-topk-family.md 新定理）：
top-k 稀疏注意力（保留集 S 上重归一）vs 全注意力的误差被**丢弃质量**界住：

  全输出 A = Σᵢ pᵢ·vᵢ（p 概率分布）
  稀疏 A' = Σ_{i∈S} (pᵢ/Z)·vᵢ（Z = Σ_{i∈S}pᵢ = 保留质量）
  ⟹ ‖A − A'‖ ≤ 2M·(1 − Z)（‖vᵢ‖ ≤ M，丢弃质量 1−Z）

推导：‖Σ_{i∈S}(pᵢ−pᵢ/Z)vᵢ + Σ_{i∉S}pᵢvᵢ‖
  ≤ M·(Σ_{i∈S}pᵢ(1−Z)/Z + (1−Z)) = M·((1−Z)+(1−Z)) = 2M(1−Z)

意义：保留质量 Z 越接近 1，稀疏近似越精确——top-k 路由的质量保证。

模型无关：任意概率分布、任意 value。
-/

noncomputable section

namespace Lattice

variable {ι F : Type*}
  [Fintype ι]
  [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 全注意力与稀疏注意力 -/

def fullAttn (p : ι → ℝ) (v : ι → F) : F :=
  ∑ i, p i • v i

def sparseAttn (p : ι → ℝ) (v : ι → F) (S : Finset ι) (Z : ℝ) : F :=
  ∑ i in S, (p i / Z) • v i

/-! ## 引理一：Finset 分区求和
Σᵢ fᵢ = Σ_{i∈S} fᵢ + Σ_{i∈univ∖S} fᵢ（S 与补集划分全集）。-/

omit [NormedSpace ℝ F] in
lemma sum_partition (f : ι → F) (S : Finset ι) :
    ∑ i, f i = ∑ i in S, f i + ∑ i in Finset.univ \ S, f i := by
  -- univ = S ∪ (univ \ S)，不相交
  have hunion : (Finset.univ : Finset ι) = S ∪ (Finset.univ \ S) := by
    ext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]
  calc
    ∑ i, f i = ∑ i in S ∪ (Finset.univ \ S), f i := by rw [← hunion]
    _ = ∑ i in S, f i + ∑ i in Finset.univ \ S, f i := by
      exact Finset.sum_union disjoint_sdiff_self_right

/-! ## 引理二：重归一差
|pᵢ − pᵢ/Z| = pᵢ·(1−Z)/Z（pᵢ ≥ 0，0 < Z ≤ 1）。-/

lemma renorm_diff (pᵢ Z : ℝ) (hp : 0 ≤ pᵢ) (hZ : 0 < Z) (hZle : Z ≤ 1) :
    |pᵢ - pᵢ / Z| = pᵢ * (1 - Z) / Z := by
  -- pᵢ − pᵢ/Z = −pᵢ·(1−Z)/Z；|−·| = |·|
  have hneg : pᵢ - pᵢ / Z = -(pᵢ * (1 - Z) / Z) := by
    field_simp [ne_of_gt hZ]
    ring
  rw [hneg, abs_neg]
  -- pᵢ·(1−Z)/Z ≥ 0（pᵢ ≥ 0、Z ≤ 1、Z > 0）→ 去绝对值
  have hge : 0 ≤ pᵢ * (1 - Z) / Z := by
    have h1 : 0 ≤ 1 - Z := by linarith
    have hprod : 0 ≤ pᵢ * (1 - Z) := mul_nonneg hp h1
    exact div_nonneg hprod (le_of_lt hZ)
  rw [abs_of_nonneg hge]

/-! ## 定理：dropped-mass 误差界
p 概率分布、Z = Σ_{i∈S}pᵢ（保留质量，0<Z≤1）、‖vᵢ‖≤M
⟹ ‖fullAttn − sparseAttn‖ ≤ 2M·(1−Z)。-/

theorem dropped_mass_bound (p : ι → ℝ) (v : ι → F) (S : Finset ι) (Z M : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hZ : Z = ∑ i in S, p i) (hZ0 : 0 < Z) (hZ1 : Z ≤ 1)
    (hV : ∀ i, ‖v i‖ ≤ M) :
    ‖fullAttn p v - sparseAttn p v S Z‖ ≤ 2 * M * (1 - Z) := by
  -- 展开并分区
  have hdiff : fullAttn p v - sparseAttn p v S Z =
      ∑ i in S, (p i - p i / Z) • v i + ∑ i in Finset.univ \ S, p i • v i := by
    unfold fullAttn sparseAttn
    -- Σᵢ pᵢvᵢ - Σ_{i∈S}(pᵢ/Z)vᵢ = Σ_{i∈S}(pᵢ−pᵢ/Z)vᵢ + Σ_{i∉S}pᵢvᵢ
    calc
      (∑ i, p i • v i) - (∑ i in S, (p i / Z) • v i)
          = (∑ i in S, p i • v i + ∑ i in Finset.univ \ S, p i • v i) - (∑ i in S, (p i / Z) • v i) := by
            -- 全量 = S + 补集
            rw [← sum_partition (fun i => p i • v i) S]
        _ = (∑ i in S, p i • v i - ∑ i in S, (p i / Z) • v i) + ∑ i in Finset.univ \ S, p i • v i := by
            -- 交换减法分组：(A + C) - B = (A - B) + C
            abel
        _ = ∑ i in S, (p i - p i / Z) • v i + ∑ i in Finset.univ \ S, p i • v i := by
            -- 减法逐项并入 S 求和：(pᵢvᵢ) − ((pᵢ/Z)vᵢ) = (pᵢ−pᵢ/Z)vᵢ
            rw [← Finset.sum_sub_distrib]
            apply congrArg (fun x => x + ∑ i in Finset.univ \ S, p i • v i)
            apply Finset.sum_congr rfl
            intro i hi
            rw [← sub_smul]
  rw [hdiff]
  -- 三角 + 范数
  calc
    ‖∑ i in S, (p i - p i / Z) • v i + ∑ i in Finset.univ \ S, p i • v i‖
        ≤ ‖∑ i in S, (p i - p i / Z) • v i‖ + ‖∑ i in Finset.univ \ S, p i • v i‖ := norm_add_le _ _
    _ ≤ (∑ i in S, ‖(p i - p i / Z) • v i‖) + (∑ i in Finset.univ \ S, ‖p i • v i‖) := by
      exact add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ (∑ i in S, p i * (1 - Z) / Z * M) + (∑ i in Finset.univ \ S, p i * M) := by
      -- S 部分：‖(pᵢ−pᵢ/Z)vᵢ‖ = |pᵢ−pᵢ/Z|·‖vᵢ‖ ≤ pᵢ(1−Z)/Z·M
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        calc
          ‖(p i - p i / Z) • v i‖ = |p i - p i / Z| * ‖v i‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ (p i * (1 - Z) / Z) * M := by
            have hd : |p i - p i / Z| = p i * (1 - Z) / Z := renorm_diff (p i) Z (hp0 i) hZ0 hZ1
            rw [hd]
            exact mul_le_mul_of_nonneg_left (hV i) (by
              -- pᵢ(1−Z)/Z ≥ 0
              have h1 : 0 ≤ 1 - Z := by linarith
              have hprod : 0 ≤ p i * (1 - Z) := mul_nonneg (hp0 i) h1
              exact div_nonneg hprod (le_of_lt hZ0))
      · apply Finset.sum_le_sum
        intro i hi
        calc
          ‖p i • v i‖ = |p i| * ‖v i‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = p i * ‖v i‖ := by rw [abs_of_nonneg (hp0 i)]
          _ ≤ p i * M := mul_le_mul_of_nonneg_left (hV i) (hp0 i)
    _ ≤ 2 * M * (1 - Z) := by
      -- Σ_{i∈S} pᵢ(1−Z)/Z·M + Σ_{i∉S} pᵢ·M
      -- = M·((1−Z)/Z·Σ_{i∈S}pᵢ + Σ_{i∉S}pᵢ)
      -- = M·((1−Z) + (1−Z)) = 2M(1−Z)
      have hZS : ∑ i in S, p i = Z := hZ.symm
      have hsumRest : ∑ i in Finset.univ \ S, p i = 1 - Z := by
        -- Σ_{i∉S}pᵢ = 1 − Σ_{i∈S}pᵢ = 1 − Z
        have hpart : (∑ i, p i) = (∑ i in S, p i) + (∑ i in Finset.univ \ S, p i) := by
          exact sum_partition p S
        rw [hsum, ← hZ] at hpart
        linarith
      -- 计算和
      have hsumS : ∑ i in S, p i * (1 - Z) / Z * M = M * (1 - Z) := by
        -- Σ_{i∈S} pᵢ·c·M = c·Σ_{i∈S}pᵢ·M = M·(1−Z)
        calc
          (∑ i in S, p i * (1 - Z) / Z * M) = ∑ i in S, p i * ((1 - Z) / Z * M) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (∑ i in S, p i) * ((1 - Z) / Z * M) := by
            rw [Finset.sum_mul]
          _ = Z * ((1 - Z) / Z * M) := by rw [hZ]
          _ = M * (1 - Z) := by
            have hz0 : Z ≠ 0 := ne_of_gt hZ0
            field_simp [hz0]
            ring
      have hsumRest2 : ∑ i in Finset.univ \ S, p i * M = M * (1 - Z) := by
        calc
          (∑ i in Finset.univ \ S, p i * M) = M * (∑ i in Finset.univ \ S, p i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = M * (1 - Z) := by rw [hsumRest]
      rw [hsumS, hsumRest2]
      nlinarith

end Lattice
