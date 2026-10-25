import Mathlib
import Lattice.Lib.Editing.RealSeparation
/-!
# LATTICE: 多变量 - 多约束 KKT 强对偶（改进集 → 分离 → 乘子 → 零间隙）

`RealSeparation` 给出了**标量单约束**的完整强对偶闭环（改进集 `A ⊆ ℝ²`、支撑超平面、
乘子存在、零间隙）。本文件把它提升到 **`m` 个约束、单目标**的一般情形：

* 改进集 `A = {(u, v) ∈ (Fin m → ℝ) × ℝ | ∃ x, (∀ i, gᵢ x ≤ uᵢ) ∧ f x ≤ v}`；
* `Convex ℝ A`（`f`、各 `gᵢ` 凸）；
* `(interior A).Nonempty`（以 `x` 为见证的 `(g x + 1, f x + 1)` 的半径为 1 的球）；
* `(0, f x̄) ∉ interior A`（`x̄` 可行最优）；
* 由 `RealSeparation.supporting_functional_of_not_mem_interior` 得非零连续线性泛函
  `φ`，`φ(0, f x̄) ≤ φ y`（`y ∈ A`）。把 `φ` 按标准基写成
  `φ(u, v) = ∑ i, uᵢ · aᵢ + v · b`；
* 逐坐标论证 `aᵢ ≥ 0`、`b ≥ 0`；若 `b = 0` 则 Slater 与 `∑ aᵢ gᵢ ≥ 0` 矛盾
  （除非 `φ = 0`），故 `b > 0`；取 `λᵢ = aᵢ / b ≥ 0`；
* **乘子不等式**：`∀ x, f x̄ ≤ f x + ∑ i, λᵢ gᵢ x`；
* **零间隙**：`(⨅ x, f x + ∑ i, λᵢ gᵢ x) = f x̄`。

技术要点：连续线性泛函在 `(Fin m → ℝ) × ℝ` 上的坐标表示
`contLinMap_prod_coords`（用 `Pi.single` 标准基展开，`map_sum`/`map_smul`）。

**诚实边界**：
- 本文件证明的是**有限多个不等式约束**（`Fin m` 索引）的 KKT 强对偶（Slater 严格可行点
  存在）。等式约束、抽象凸集约束、无穷约束族、以及 `x` 属于一般拓扑线性空间的情形
  本文件**未做**；
- 与 `RealSeparation` 一样，改进集 `A` **不要求闭**，分离用的是内点分离
  （`supporting_functional_of_not_mem_interior`）；Slater 提供内点存在性；
- 最优值可达性（紧可行集上取到 `x̄`）在 `RealSeparation.slater_compact_sufficient` 中
  已对单约束给出，本文件的**多约束版本未做**（标注为后续工作）；
- `m = 0`（无约束）退化为 `∀ x, f x̄ ≤ f x`，本文件的一般陈述自动覆盖
  （`Fin 0` 上求和为 0，Slater 条件空真）。

无 sorry / axiom / admit。
-/

noncomputable section

open scoped BigOperators
open Set

namespace Lattice

/-! ## 一、多约束改进集及其凸性 -/

/-- **多约束改进集**：
`A = {(u, v) | ∃ x, (∀ i, gᵢ x ≤ uᵢ) ∧ f x ≤ v}`（同时放松所有约束值与目标值的点集）。
`Fin m` 索引约束族。 -/
def multImprovingSet {m : ℕ} (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ) :
    Set ((Fin m → ℝ) × ℝ) :=
  {p | ∃ x, (∀ i, g i x ≤ p.1 i) ∧ f x ≤ p.2}

/-- **多约束改进集是凸的**：`f`、各 `gᵢ` 凸 ⟹ `A` 凸。
取两见证点凸组合作新见证（`x = a x₁ + b x₂`），逐分量用凸性与线性性。 -/
theorem convex_multImprovingSet {m : ℕ} {f : ℝ → ℝ} {g : Fin m → ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i)) :
    Convex ℝ (multImprovingSet f g) := by
  rw [convex_iff_forall_pos]
  rintro ⟨u₁, v₁⟩ ⟨x₁, hg₁, hf₁⟩ ⟨u₂, v₂⟩ ⟨x₂, hg₂, hf₂⟩ aa bb ha hb hab
  refine ⟨aa * x₁ + bb * x₂, ?_, ?_⟩
  · intro i
    have h := (hg i).2 (Set.mem_univ x₁) (Set.mem_univ x₂) ha.le hb.le hab
    simp only [smul_eq_mul] at h
    have h1 : aa * g i x₁ ≤ aa * u₁ i := mul_le_mul_of_nonneg_left (hg₁ i) ha.le
    have h2 : bb * g i x₂ ≤ bb * u₂ i := mul_le_mul_of_nonneg_left (hg₂ i) hb.le
    show g i (aa * x₁ + bb * x₂) ≤ (aa • u₁ + bb • u₂) i
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linarith
  · have h := hf.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ha.le hb.le hab
    simp only [smul_eq_mul] at h
    have h1 : aa * f x₁ ≤ aa * v₁ := mul_le_mul_of_nonneg_left hf₁ ha.le
    have h2 : bb * f x₂ ≤ bb * v₂ := mul_le_mul_of_nonneg_left hf₂ hb.le
    show f (aa * x₁ + bb * x₂) ≤ aa • v₁ + bb • v₂
    rw [smul_eq_mul, smul_eq_mul]
    linarith

/-- **多约束改进集有内点**：以 `x` 为见证，`(g x + 1, f x + 1)` 的半径为 1 的
球整个落在 `A` 内（用乘积度量的坐标投影 `dist_le_pi_dist`）。 -/
theorem interior_multImprovingSet_nonempty {m : ℕ} (f : ℝ → ℝ) (g : Fin m → ℝ → ℝ)
    (x : ℝ) : (interior (multImprovingSet f g)).Nonempty := by
  refine ⟨(fun i => g i x + 1, f x + 1), ?_⟩
  have hsub : Metric.ball ((fun i => g i x + 1, f x + 1) : (Fin m → ℝ) × ℝ) 1
      ⊆ multImprovingSet f g := by
    rintro ⟨u, v⟩ hq
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] at hq
    have h1 : dist u (fun i => g i x + 1) < 1 := lt_of_le_of_lt (le_max_left _ _) hq
    have h2 : |v - (f x + 1)| < 1 := lt_of_le_of_lt (le_max_right _ _) hq
    rw [abs_lt] at h2
    refine ⟨x, fun i => ?_, by linarith [h2.1, h2.2]⟩
    have hi : |u i - (g i x + 1)| ≤ dist u (fun i => g i x + 1) := by
      have h := dist_le_pi_dist u (fun i => g i x + 1) i
      rwa [Real.dist_eq] at h
    have hi' : |u i - (g i x + 1)| < 1 := lt_of_le_of_lt hi h1
    rw [abs_lt] at hi'
    show g i x ≤ (u, v).1 i
    simp only [Prod.fst]
    linarith [hi'.1, hi'.2]
  exact interior_maximal hsub Metric.isOpen_ball (Metric.mem_ball_self one_pos)

/-- **最优值点不是改进集的内点**：`(0, f x̄)` 若为内点，则存在 `ε > 0` 使
`(0, f x̄ − ε/2) ∈ A`，即存在可行点 `y`（`∀i, gᵢ y ≤ 0`）满足 `f y < f x̄`，
与最优性矛盾。 -/
theorem not_mem_interior_multImprovingSet {m : ℕ} {f : ℝ → ℝ} {g : Fin m → ℝ → ℝ}
    {xbar : ℝ} (hfeas : ∀ i, g i xbar ≤ 0)
    (hopt : ∀ y, (∀ i, g i y ≤ 0) → f xbar ≤ f y) :
    ((0 : Fin m → ℝ), f xbar) ∉ interior (multImprovingSet f g) := by
  intro hcon
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hcon) with ⟨eps, heps, hball⟩
  have hdist : dist (((0 : Fin m → ℝ), f xbar - eps / 2)) (((0 : Fin m → ℝ), f xbar)) < eps := by
    rw [Prod.dist_eq, Real.dist_eq]
    have hzero : dist (0 : Fin m → ℝ) 0 = 0 := dist_self _
    have hval : |f xbar - eps / 2 - f xbar| = eps / 2 := by
      rw [show f xbar - eps / 2 - f xbar = -(eps / 2) by ring, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < eps / 2)]
    rw [hzero, hval, max_eq_right (by linarith : (0 : ℝ) ≤ eps / 2)]
    linarith
  have hmem : ((0 : Fin m → ℝ), f xbar - eps / 2) ∈ multImprovingSet f g :=
    interior_subset (hball hdist)
  obtain ⟨y, hgy, hfy⟩ := hmem
  have h := hopt y hgy
  linarith

/-! ## 二、连续线性泛函的坐标表示 -/

/-- **乘积空间上连续线性泛函的坐标表示**：任何
`φ : ((Fin m → ℝ) × ℝ) →L[ℝ] ℝ` 都可写成
`φ(u, v) = ∑ i, uᵢ · aᵢ + v · b`，其中 `aᵢ = φ(δᵢ, 0)`、`b = φ(0, 1)`
（`δᵢ = Pi.single i 1` 是标准基向量）。

证明：`u = ∑ i, uᵢ • δᵢ`（逐坐标展开），故 `φ(u, 0) = ∑ i, uᵢ · aᵢ`
（`map_sum` + `map_smul`）；`φ(0, v) = v · b`；再用 `map_add` 拆分 `(u,v) = (u,0) + (0,v)`。 -/
theorem contLinMap_prod_coords {m : ℕ} (phi : ((Fin m → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ (a : Fin m → ℝ) (b : ℝ), ∀ (u : Fin m → ℝ) (v : ℝ),
      phi (u, v) = (∑ i, u i * a i) + v * b := by
  refine ⟨fun i => phi (Pi.single i (1 : ℝ), 0), phi (0, 1), ?_⟩
  intro u v
  have h1 : phi (u, (0 : ℝ)) = ∑ i, u i * phi (Pi.single i (1 : ℝ), 0) := by
    have hdecomp : u = ∑ i, u i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
      funext j
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        have hz : (Pi.single i (1 : ℝ) : Fin m → ℝ) j = 0 := by
          simp [Pi.single_eq_of_ne (Ne.symm hij)]
        rw [Pi.smul_apply, hz, smul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hpu : (u, (0 : ℝ)) = ∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ)) := by
      have hfst : (u, (0 : ℝ)).1
          = (∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).1 := by
        show u = (∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).1
        rw [show (∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).1
            = ∑ i, u i • (Pi.single i (1 : ℝ) : Fin m → ℝ) from Prod.fst_sum]
        exact hdecomp
      have hsnd : (u, (0 : ℝ)).2
          = (∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).2 := by
        rw [show (∑ i, u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).2
            = ∑ i, (u i • ((Pi.single i (1 : ℝ) : Fin m → ℝ), (0 : ℝ))).2
            from Prod.snd_sum]
        simp
      exact Prod.ext hfst hsnd
    rw [hpu, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, smul_eq_mul]
  have h2 : phi ((0 : Fin m → ℝ), v) = v * phi (0, (1 : ℝ)) := by
    have hv : ((0 : Fin m → ℝ), v) = v • ((0 : Fin m → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_smul, smul_eq_mul]
  have hsplit : (u, v) = (u, (0 : ℝ)) + ((0 : Fin m → ℝ), v) := by
    ext <;> simp
  rw [hsplit, map_add, h1, h2]

/-- 辅助：`∑ j, (Pi.single i T) j * a j = T * a i`（单点求和）。 -/
lemma sum_pi_single_mul {m : ℕ} (T : ℝ) (a : Fin m → ℝ) (i : Fin m) :
    (∑ j, (Pi.single i T : Fin m → ℝ) j * a j) = T * a i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    rw [Pi.single_eq_of_ne hij, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## 三、Slater 乘子存在（核心） -/

/-- **多变量-多约束 Slater 乘子存在（核心）**：`f`、各 `gᵢ` 凸、`x̄` 可行（`∀i, gᵢ x̄ ≤ 0`）
且最优、Slater（`∃ x₀, ∀ i, gᵢ x₀ < 0`）⟹ 存在乘子 `λ : Fin m → ℝ`，`λᵢ ≥ 0` 且
`∀ x, f x̄ ≤ f x + ∑ i, λᵢ · gᵢ x`。

证明路线：分离（`supporting_functional_of_not_mem_interior`）→ 坐标表示
`φ(u,v) = ∑ uᵢ aᵢ + v b` → `b(f x − f x̄) + ∑ aᵢ gᵢ x ≥ 0` → 逐坐标 `aᵢ ≥ 0`（令
`u = g x̄ + T·δᵢ`，`T → ∞`）与 `b ≥ 0`（令 `v = f x̄ + T`）→ `b ≠ 0`
（否则 `b = 0` 与 Slater 迫使所有 `aᵢ = 0`，即 `φ = 0`，与 `φ ≠ 0` 矛盾）
→ `λᵢ = aᵢ / b`。 -/
theorem mult_slater_multiplier_exists {m : ℕ} {f : ℝ → ℝ} {g : Fin m → ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    {xbar : ℝ} (hfeas : ∀ i, g i xbar ≤ 0)
    (hopt : ∀ y, (∀ i, g i y ≤ 0) → f xbar ≤ f y)
    (hslater : ∃ x₀, ∀ i, g i x₀ < 0) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧
      ∀ x, f xbar ≤ f x + ∑ i, lam i * g i x := by
  obtain ⟨phi, hphi_ne, -, hphi_sup⟩ :=
    supporting_functional_of_not_mem_interior (convex_multImprovingSet hf hg)
      (interior_multImprovingSet_nonempty f g xbar)
      (not_mem_interior_multImprovingSet hfeas hopt)
  obtain ⟨a, b, hcoord⟩ := contLinMap_prod_coords phi
  -- 关键不等式：0 ≤ b(f x − f x̄) + ∑ aᵢ gᵢ x
  have hkey : ∀ x : ℝ, 0 ≤ b * (f x - f xbar) + ∑ i, a i * g i x := by
    intro x
    have hmem : (fun i => g i x, f x) ∈ multImprovingSet f g :=
      ⟨x, fun i => le_rfl, le_rfl⟩
    have h := hphi_sup (fun i => g i x, f x) hmem
    rw [hcoord, hcoord] at h
    have hzero : (∑ i, (0 : Fin m → ℝ) i * a i) = 0 := by simp
    rw [hzero, zero_add] at h
    have hsum_eq : (∑ i, g i x * a i) = ∑ i, a i * g i x :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsum_eq] at h
    linarith
  -- aᵢ ≥ 0
  have haa : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set S : ℝ := ∑ j, g j xbar * a j with hS
    set T : ℝ := (|S| + 1) / (-a i) with hT
    have hai : a i ≠ 0 := ne_of_lt hneg
    have hTpos : 0 < T := by
      rw [hT]
      exact div_pos (by positivity) (by linarith)
    have hmemT : (fun j => g j xbar + (Pi.single i (1 : ℝ) : Fin m → ℝ) j * T, f xbar)
        ∈ multImprovingSet f g := by
      refine ⟨xbar, fun j => ?_, le_rfl⟩
      show g j xbar ≤ g j xbar + (Pi.single i (1 : ℝ) : Fin m → ℝ) j * T
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        linarith [hTpos]
      · rw [Pi.single_eq_of_ne hj, zero_mul, add_zero]
    have h := hphi_sup
      (fun j => g j xbar + (Pi.single i (1 : ℝ) : Fin m → ℝ) j * T, f xbar) hmemT
    rw [hcoord, hcoord] at h
    have hzero : (∑ j, (0 : Fin m → ℝ) j * a j) = 0 := by simp
    rw [hzero, zero_add] at h
    have hsum : (∑ j, (g j xbar + (Pi.single i (1 : ℝ) : Fin m → ℝ) j * T) * a j)
        = S + T * a i := by
      have hsplit : (∑ j, (g j xbar + (Pi.single i (1 : ℝ) : Fin m → ℝ) j * T) * a j)
          = (∑ j, g j xbar * a j)
            + ∑ j, ((Pi.single i (1 : ℝ) : Fin m → ℝ) j * T) * a j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      have hsecond : (∑ j, ((Pi.single i (1 : ℝ) : Fin m → ℝ) j * T) * a j)
          = T * a i := by
        have hcomm : (∑ j, ((Pi.single i (1 : ℝ) : Fin m → ℝ) j * T) * a j)
            = ∑ j, (Pi.single i (1 : ℝ) : Fin m → ℝ) j * (T * a j) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [hcomm, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, zero_mul]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hsplit, hsecond, ← hS]
    rw [hsum] at h
    have hTa : T * a i = -(|S| + 1) := by
      have hane : -a i ≠ 0 := by linarith
      rw [hT, div_mul_eq_mul_div]
      rw [show (|S| + 1) * a i = (-a i) * (-(|S| + 1)) by ring]
      exact mul_div_cancel_left₀ _ hane
    rw [hTa] at h
    have hle : S ≤ |S| := le_abs_self S
    linarith
  -- b ≥ 0
  have hbb : 0 ≤ b := by
    by_contra hneg
    push_neg at hneg
    set S : ℝ := ∑ j, g j xbar * a j with hS
    set T : ℝ := (|S| + 1) / (-b) with hT
    have hbne : b ≠ 0 := ne_of_lt hneg
    have hTpos : 0 < T := by
      rw [hT]
      exact div_pos (by positivity) (by linarith)
    have hmemT : (fun j => g j xbar, f xbar + T) ∈ multImprovingSet f g :=
      ⟨xbar, fun j => le_rfl, by
        show f xbar ≤ f xbar + T
        linarith [hTpos]⟩
    have h := hphi_sup (fun j => g j xbar, f xbar + T) hmemT
    rw [hcoord, hcoord] at h
    have hzero : (∑ j, (0 : Fin m → ℝ) j * a j) = 0 := by simp
    rw [hzero, zero_add] at h
    rw [← hS] at h
    have hTb : T * b = -(|S| + 1) := by
      have hbne' : -b ≠ 0 := by linarith
      rw [hT, div_mul_eq_mul_div]
      rw [show (|S| + 1) * b = (-b) * (-(|S| + 1)) by ring]
      exact mul_div_cancel_left₀ _ hbne'
    have hexp : (f xbar + T) * b = f xbar * b + T * b := by ring
    rw [hexp, hTb] at h
    have hle : S ≤ |S| := le_abs_self S
    linarith
  -- b ≠ 0
  have hbb_ne : b ≠ 0 := by
    intro hb0
    obtain ⟨x₀, hx₀⟩ := hslater
    have hkey0 : 0 ≤ ∑ i, a i * g i x₀ := by
      have h := hkey x₀
      rw [hb0, zero_mul, zero_add] at h
      exact h
    have hnonpos : ∀ i, a i * g i x₀ ≤ 0 :=
      fun i => mul_nonpos_of_nonneg_of_nonpos (haa i) (le_of_lt (hx₀ i))
    have hsum_nonpos : (∑ i, a i * g i x₀) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => hnonpos i)
    have hsum0 : (∑ i, a i * g i x₀) = 0 := le_antisymm hsum_nonpos hkey0
    have hall : ∀ i, a i = 0 := by
      intro i
      by_contra hne
      have hpos : 0 < a i := lt_of_le_of_ne (haa i) (Ne.symm hne)
      have hlt : a i * g i x₀ < 0 := mul_neg_of_pos_of_neg hpos (hx₀ i)
      have hrest : (∑ j in Finset.univ.erase i, a j * g j x₀) ≤ 0 :=
        Finset.sum_nonpos (fun j _ => hnonpos j)
      have hsplit : (∑ j, a j * g j x₀)
          = a i * g i x₀ + ∑ j in Finset.univ.erase i, a j * g j x₀ := by
        rw [add_comm]
        exact (Finset.sum_erase_add Finset.univ (fun j => a j * g j x₀) (Finset.mem_univ i)).symm
      rw [hsum0] at hsplit
      linarith
    apply hphi_ne
    ext q
    · show phi (q, (0 : ℝ)) = 0
      rw [hcoord q 0]
      have hsuma : (∑ i, q i * a i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hall i, mul_zero]
      rw [hsuma, hb0]
      ring
    · show phi ((0 : Fin m → ℝ), _) = 0
      rw [hcoord 0 _]
      have hsuma : (∑ i, (0 : Fin m → ℝ) i * a i) = 0 := by simp
      rw [hsuma, hb0]
      ring
  have hbb_pos : 0 < b := lt_of_le_of_ne hbb (Ne.symm hbb_ne)
  refine ⟨fun i => a i / b, fun i => div_nonneg (haa i) hbb_pos.le, fun x => ?_⟩
  have h := hkey x
  have hdiv : 0 ≤ (f x - f xbar) + (∑ i, a i * g i x) / b := by
    have hd : 0 ≤ (b * (f x - f xbar) + ∑ i, a i * g i x) / b :=
      div_nonneg h hbb_pos.le
    rw [add_div, mul_div_cancel_left₀ _ hbb_ne] at hd
    exact hd
  have hsum_div : (∑ i, (a i / b) * g i x) = (∑ i, a i * g i x) / b := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hsum_div]
  linarith

/-! ## 四、零间隙（强对偶） -/

/-- **多变量-多约束零间隙（强对偶）**：与 `mult_slater_multiplier_exists` 同假设下，
存在 `λᵢ ≥ 0` 使拉格朗日函数的下确界恰等于原问题最优值 `f x̄`，且给出全局下界。

证明：乘子不等式给出 `f x̄ ≤ ⨅ x, L(x, λ)`；另一方面
`⨅ x, L(x, λ) ≤ L(x̄, λ) = f x̄ + ∑ λᵢ gᵢ x̄ ≤ f x̄`（`λᵢ ≥ 0`、`gᵢ x̄ ≤ 0`）两侧夹紧。 -/
theorem mult_strong_duality_convex_slater {m : ℕ} {f : ℝ → ℝ} {g : Fin m → ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    {xbar : ℝ} (hfeas : ∀ i, g i xbar ≤ 0)
    (hopt : ∀ y, (∀ i, g i y ≤ 0) → f xbar ≤ f y)
    (hslater : ∃ x₀, ∀ i, g i x₀ < 0) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧
      (⨅ x, (f x + ∑ i, lam i * g i x)) = f xbar ∧
      ∀ x, f xbar ≤ f x + ∑ i, lam i * g i x := by
  obtain ⟨lam, hlam, hmult⟩ := mult_slater_multiplier_exists hf hg hfeas hopt hslater
  refine ⟨lam, hlam, ?_, hmult⟩
  have hle : f xbar ≤ ⨅ x, (f x + ∑ i, lam i * g i x) := le_ciInf (fun x => hmult x)
  have hbdd : BddBelow (Set.range (fun x : ℝ => f x + ∑ i, lam i * g i x)) :=
    ⟨f xbar, by rintro _ ⟨x, rfl⟩; exact hmult x⟩
  have hge : (⨅ x, (f x + ∑ i, lam i * g i x)) ≤ f xbar := by
    have h1 := ciInf_le hbdd xbar
    have h2 : (∑ i, lam i * g i xbar) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeas i))
    linarith
  exact le_antisymm hge hle

end Lattice
