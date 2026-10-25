import Mathlib
import Lattice.Lib.InfoTheory.RealKL
/-!
# LATTICE: 互信息 —— KL(联合 ‖ 边缘乘积)、非负性与熵分解

信息论线的收官一环（衔接 RealCrossEntropy 的 CE/熵、RealKL 的 KL）：

联合分布 `p : Fin m → Fin n → ℝ` 的行/列边缘 `marginalRow`/`marginalCol`，
边缘乘积（独立联合分布）`prodDist a b = marginalRow p a * marginalCol p b`，
**互信息**定义为联合与边缘乘积之间的 KL 型量：

    MI(p) = Σ_{a,b} p_ab·(log p_ab − log(p_ab 的边缘乘积))

本文件建立：

  1. `mi_as_sum_log_ratio`：显式比值形式 MI(p) = Σ p·log(p/(mr·mc))（log 定义域下）；
  2. `marginalRow_nonneg` / `marginalCol_nonneg`：边缘非负；
  3. `prodDist_sum`：Σ_{a,b} 边缘乘积 = (Σ_a mr_a)·(Σ_b mc_b)（乘积结构）；
  4. `mutual_information_nonneg`（核心）：p ≥ 0、ΣΣ p = 1、边缘严格正 ⟹ MI(p) ≥ 0
     （逐项 Gibbs 下界 `gibbs_term` 给出 p_ab − q_ab ≤ p_ab·(log p_ab − log q_ab)，
      求和后用 ΣΣ(p_ab − q_ab) = 1 − 1 = 0 ⟹ MI ≥ 0）；
  5. `mutual_information_comm`：转置对称性 MI(p) = MI(pᵀ)；
  6. `mi_eq_zero_of_independent`：p = 边缘乘积（独立）⟹ MI = 0；
  7. `gibbs_term`（自足引理）：0 ≤ x、0 < y ⟹ x − y ≤ x·(log x − log y)
     （`Real.one_sub_inv_le_log_of_pos`；与 RealKL.kl_term_ge 同型，此处按联合分量自证）。

**诚实边界**：
- MI 用 `log p − log q` 的**全函数**形式定义（mathlib 的 `Real.log` 在非正处取 0），
  因此定义本身无需任何假设；含比值的等式（`mi_as_sum_log_ratio`）在 0 < p、0 < q 下陈述，
  这是 log 定义域的语义标注。
- 未做：MI = H(X) + H(Y) − H(X,Y) 的熵分解（需联合熵的多重求和代数，
  与 `marginalRow`/`marginalCol` 的 Finset 展开配合，标注为后续）、
  MI = 0 ⟺ 独立的完整反向（需要 Q = P 型的分布乘积刻画，见 RealKL.kl_zero_iff_support 的同类诚实处理）。

模型无关：任意有限 m、n；无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {m n : ℕ}

/-! ## 定义：边缘分布、边缘乘积、互信息 -/

/-- 行边缘（第一分量的边缘分布）：mr_a = Σ_b p_ab。 -/
noncomputable def marginalRow (p : Fin m → Fin n → ℝ) (a : Fin m) : ℝ := ∑ b, p a b

/-- 列边缘（第二分量的边缘分布）：mc_b = Σ_a p_ab。 -/
noncomputable def marginalCol (p : Fin m → Fin n → ℝ) (b : Fin n) : ℝ := ∑ a, p a b

/-- 边缘乘积（独立联合分布）：q_ab = mr_a·mc_b。 -/
noncomputable def prodDist (p : Fin m → Fin n → ℝ) (a : Fin m) (b : Fin n) : ℝ :=
  marginalRow p a * marginalCol p b

/-- 互信息（KL 形式）：MI(p) = Σ_{a,b} p_ab·(log p_ab − log(mr_a·mc_b))。
`log` 为全函数，定义无需假设。 -/
noncomputable def mutualInformation (p : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, p a b * (Real.log (p a b) - Real.log (prodDist p a b))

/-! ## 自足引理：逐项 Gibbs 下界（联合分量版）
0 ≤ x、0 < y ⟹ x − y ≤ x·(log x − log y)

**REFACTOR Step 3（v12）**：原独立证明已收敛到唯一权威位置 `RealConvexToolkit.gibbs_ineq`
（同名兼容接口保留，下游调用点无需改动）。 -/

lemma gibbs_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) :=
  gibbs_ineq hx hy

/-! ## 引理：边缘非负 -/

lemma marginalRow_nonneg (p : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 ≤ p a b) (a : Fin m) :
    0 ≤ marginalRow p a :=
  Finset.sum_nonneg (fun b _ => hp0 a b)

lemma marginalCol_nonneg (p : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 ≤ p a b) (b : Fin n) :
    0 ≤ marginalCol p b :=
  Finset.sum_nonneg (fun a _ => hp0 a b)

/-! ## 引理：边缘乘积严格正（边缘严格正时） -/

lemma prodDist_pos (p : Fin m → Fin n → ℝ) (a : Fin m) (b : Fin n)
    (hr : 0 < marginalRow p a) (hc : 0 < marginalCol p b) : 0 < prodDist p a b :=
  mul_pos hr hc

/-! ## 引理：边缘乘积的双重和 = 边缘和之积
Σ_{a,b} mr_a·mc_b = (Σ_a mr_a)·(Σ_b mc_b)（Finset 乘积结构）。 -/

lemma prodDist_sum (p : Fin m → Fin n → ℝ) :
    (∑ a, ∑ b, prodDist p a b) = (∑ a, marginalRow p a) * (∑ b, marginalCol p b) := by
  unfold prodDist
  calc
    (∑ a, ∑ b, marginalRow p a * marginalCol p b)
        = ∑ a, marginalRow p a * (∑ b, marginalCol p b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = (∑ a, marginalRow p a) * (∑ b, marginalCol p b) := by
          rw [Finset.sum_mul]

/-! ## 定理一：互信息的显式比值形式
MI(p) = Σ_{a,b} p_ab·log(p_ab / q_ab)（0 < p、q > 0：`Real.log_div` 合成）。 -/

theorem mi_as_sum_log_ratio (p : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 < p a b)
    (hr : ∀ a, 0 < marginalRow p a) (hc : ∀ b, 0 < marginalCol p b) :
    mutualInformation p = ∑ a, ∑ b, p a b * Real.log (p a b / prodDist p a b) := by
  unfold mutualInformation
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Real.log_div (ne_of_gt (hp0 a b)) (ne_of_gt (prodDist_pos p a b (hr a) (hc b)))]

/-! ## 定理二（核心）：互信息非负
p ≥ 0、ΣΣ p = 1、边缘严格正 ⟹ MI(p) ≥ 0。
证明：逐项 Gibbs 下界求和，ΣΣ(p_ab − q_ab) = 1 − 1 = 0。 -/

theorem mutual_information_nonneg (p : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 ≤ p a b)
    (hsum : ∑ a, ∑ b, p a b = 1)
    (hr : ∀ a, 0 < marginalRow p a) (hc : ∀ b, 0 < marginalCol p b) :
    0 ≤ mutualInformation p := by
  have hcol : ∑ b, marginalCol p b = 1 := by
    unfold marginalCol
    rw [Finset.sum_comm]
    exact hsum
  have hq : ∑ a, ∑ b, prodDist p a b = 1 := by
    rw [prodDist_sum]
    have hrow : ∑ a, marginalRow p a = 1 := hsum
    rw [hrow, hcol, one_mul]
  have hterm : ∀ a b,
      p a b - prodDist p a b ≤ p a b * (Real.log (p a b) - Real.log (prodDist p a b)) := by
    intro a b
    exact gibbs_term (hp0 a b) (prodDist_pos p a b (hr a) (hc b))
  have hsumdiff : ∑ a, ∑ b, (p a b - prodDist p a b) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [hsum, hq]
    ring
  calc
    0 = ∑ a, ∑ b, (p a b - prodDist p a b) := hsumdiff.symm
    _ ≤ ∑ a, ∑ b, p a b * (Real.log (p a b) - Real.log (prodDist p a b)) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hterm a b))
    _ = mutualInformation p := rfl

/-! ## 定理三：转置对称性
MI(p) = MI(pᵀ)（双重求和换序 + 乘积交换律）。 -/

theorem mutual_information_comm (p : Fin m → Fin n → ℝ) :
    mutualInformation p = mutualInformation (fun (b : Fin n) (a : Fin m) => p a b) := by
  simp only [mutualInformation, prodDist, marginalRow, marginalCol]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [mul_comm]

/-! ## 定理四：独立 ⟹ 互信息为零
p 等于边缘乘积（两个分量独立）⟹ MI(p) = 0（每项 log 1 = 0）。 -/

theorem mi_eq_zero_of_independent (p : Fin m → Fin n → ℝ)
    (h : ∀ a b, p a b = prodDist p a b) : mutualInformation p = 0 := by
  unfold mutualInformation
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [h a b, sub_self, mul_zero]

/-! ## 推论：联合是概率分布（ΣΣ = 1）时边缘和为一
（供后续熵分解与验证线使用） -/

lemma marginalRow_sum_eq_one (p : Fin m → Fin n → ℝ) (hsum : ∑ a, ∑ b, p a b = 1) :
    ∑ a, marginalRow p a = 1 := hsum

lemma marginalCol_sum_eq_one (p : Fin m → Fin n → ℝ) (hsum : ∑ a, ∑ b, p a b = 1) :
    ∑ b, marginalCol p b = 1 := by
  unfold marginalCol
  rw [Finset.sum_comm]
  exact hsum

end Lattice
