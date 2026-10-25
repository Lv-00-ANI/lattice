import Mathlib
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.InfoTheory.RealMutualInformation
import Lattice.Lib.InfoTheory.RealContinuousKL
/-!
# LATTICE: KL 的链式法则与熵分解（有限支撑版）

`RealMutualInformation` 在 docstring 中**明确标注未做**
`MI = H(X) + H(Y) − H(X,Y)` 的熵分解；本文件补齐该缺口，并给出联合 KL 的
**链式法则**（KL 的分解）与联合 KL 非负。

主要结果：

  1. `klJoint` / `klJointMarginal` / `klConditional`（定义）：联合 KL、
     边缘 KL、条件 KL。
  2. `klChainRule`（**核心**）：有限支撑下
     `KL(p(x,y)‖q(x,y)) = KL(p(x)‖q(x)) + Σ_a p(x=a)·KL(p(y|x=a)‖q(y|x=a))`。
     证明：逐点 log 恒等式
     `log(p_b/q_b) = log((p_b/r)/(q_b/r')) + log(r/r')`（`Real.log_mul` 逆用）
     + 纤维求和提出常数（`Finset.sum_mul` / `Finset.mul_sum`）+ 双重求和换序。
  3. `klJoint_nonneg`：联合 KL 的 Gibbs 非负（`ΣΣ p = 1`、`ΣΣ q = 1`、逐项
     `RealContinuousKL.sub_le_mul_log_div`）。
  4. `jointEntropy` / `marginalEntropyRow` / `marginalEntropyCol`（定义）与
     `mutualInformation_eq_entropy_decomposition`（**补齐 RealMutualInformation
     的标注缺口**）：`MI(p) = H(X) + H(Y) − H(X,Y)`。
  5. `mutualInformation_eq_klJoint_prodDist`：`MI(p) = KL(p ‖ p_X ⊗ p_Y)`
     （把互信息接到 `RealKLChainRule.klJoint` 上）。

**诚实边界（标注）**：
- 全部为**有限支撑**（`Fin m → Fin n → ℝ`）的纯代数 + 求和换序；不含测度论版本。
- `klChainRule` 与熵分解明确假设联合/边缘**严格正**（`0 < p`、`0 < mr`、`0 < mc`），
  因为 `Real.log` 在非正处取 0 会破坏 `Real.log_div` / `Real.log_mul` 的代数恒等式。
  这是定义域语义标注，不是证明缺口。
- 未做：测度论（Radon–Nikodym）形式的链式法则；条件 KL 的凸性。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {m n : ℕ}

/-! ## 一、定义：联合 KL、边缘 KL、条件 KL -/

/-- **联合 KL 散度**（有限支撑）：`KL(p‖q) = Σ_{a,b} p_ab·log(p_ab / q_ab)`。 -/
noncomputable def klJoint (p q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, p a b * Real.log (p a b / q a b)

/-- **边缘（行）KL 散度**：`KL(p_X‖q_X) = Σ_a mr_a·log(mr_a / mr'_a)`。 -/
noncomputable def klJointMarginal (p q : Fin m → Fin n → ℝ) : ℝ :=
  ∑ a, marginalRow p a * Real.log (marginalRow p a / marginalRow q a)

/-- **条件 KL 散度**：`KL(p(y|a)‖q(y|a)) = Σ_b (p_ab/mr_a)·log((p_ab/mr_a)/(q_ab/mr'_a))`。 -/
noncomputable def klConditional (p q : Fin m → Fin n → ℝ) (a : Fin m) : ℝ :=
  ∑ b, (p a b / marginalRow p a)
    * Real.log ((p a b / marginalRow p a) / (q a b / marginalRow q a))

/-! ## 二、KL 的链式法则（核心） -/

/-- **逐点 log 恒等式**：`log(p_b/q_b) = log((p_b/r)/(q_b/r')) + log(r/r')`。
由乘法恒等式 `((p/r)/(q/r'))·(r/r') = p/q` 与 `Real.log_mul` 逆用得到。 -/
lemma log_ratio_decomposition {pb qb r r' : ℝ} (hp : pb ≠ 0) (hq : qb ≠ 0)
    (hr : r ≠ 0) (hr' : r' ≠ 0) :
    Real.log (pb / qb)
      = Real.log ((pb / r) / (qb / r')) + Real.log (r / r') := by
  have h1 : (pb / r) / (qb / r') ≠ 0 := div_ne_zero (div_ne_zero hp hr) (div_ne_zero hq hr')
  have h2 : r / r' ≠ 0 := div_ne_zero hr hr'
  have hprod : (pb / r) / (qb / r') * (r / r') = pb / qb := by
    field_simp
    ring
  rw [← hprod, Real.log_mul h1 h2]

/-- **单纤维分解**：固定 `a`，
`Σ_b p_ab·log(p_ab/q_ab) = mr_a·KL(p(y|a)‖q(y|a)) + mr_a·log(mr_a/mr'_a)`。 -/
lemma sum_row_kl_decomposition (p q : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 < p a b)
    (hq0 : ∀ a b, 0 < q a b) (hrp : ∀ a, 0 < marginalRow p a)
    (hrq : ∀ a, 0 < marginalRow q a) (a : Fin m) :
    ∑ b, p a b * Real.log (p a b / q a b)
      = marginalRow p a * klConditional p q a
        + marginalRow p a * Real.log (marginalRow p a / marginalRow q a) := by
  have hrp' : (marginalRow p a) ≠ 0 := ne_of_gt (hrp a)
  have hrq' : (marginalRow q a) ≠ 0 := ne_of_gt (hrq a)
  have hpoint : ∀ b : Fin n, p a b * Real.log (p a b / q a b)
      = p a b * Real.log ((p a b / marginalRow p a) / (q a b / marginalRow q a))
        + p a b * Real.log (marginalRow p a / marginalRow q a) := by
    intro b
    rw [log_ratio_decomposition (ne_of_gt (hp0 a b)) (ne_of_gt (hq0 a b)) hrp' hrq']
    ring
  rw [Finset.sum_congr rfl (fun b _ => hpoint b), Finset.sum_add_distrib]
  congr 1
  · -- Σ_b p_ab·log(A_b/B_b) = mr_a·Σ_b (p_ab/mr_a)·log(A_b/B_b)
    unfold klConditional
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    field_simp
  · -- Σ_b p_ab·C = (Σ_b p_ab)·C = mr_a·C
    rw [← Finset.sum_mul]
    rfl

/-- **KL 的链式法则（核心）**：有限支撑下
`KL(p(x,y)‖q(x,y)) = KL(p(x)‖q(x)) + Σ_a p(x=a)·KL(p(y|x=a)‖q(y|x=a))`。 -/
theorem klChainRule (p q : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 < p a b)
    (hq0 : ∀ a b, 0 < q a b) (hrp : ∀ a, 0 < marginalRow p a)
    (hrq : ∀ a, 0 < marginalRow q a) :
    klJoint p q = klJointMarginal p q
      + ∑ a, marginalRow p a * klConditional p q a := by
  unfold klJoint klJointMarginal
  rw [Finset.sum_congr rfl (fun a _ =>
    sum_row_kl_decomposition p q hp0 hq0 hrp hrq a)]
  rw [Finset.sum_add_distrib]
  ring

/-! ## 三、联合 KL 的 Gibbs 非负 -/

/-- **联合 KL 非负**（Gibbs 不等式）：`p ≥ 0`、`q > 0`、`ΣΣ p = 1`、`ΣΣ q = 1`
⟹ `0 ≤ KL(p‖q)`。证明：逐项 `sub_le_mul_log_div` 求和 + `ΣΣ(p−q) = 1 − 1 = 0`。 -/
theorem klJoint_nonneg (p q : Fin m → Fin n → ℝ) (hp0 : ∀ a b, 0 ≤ p a b)
    (hq0 : ∀ a b, 0 < q a b) (hpsum : ∑ a, ∑ b, p a b = 1)
    (hqsum : ∑ a, ∑ b, q a b = 1) :
    0 ≤ klJoint p q := by
  have hpoint : ∀ a b, p a b - q a b ≤ p a b * Real.log (p a b / q a b) :=
    fun a b => sub_le_mul_log_div (hp0 a b) (hq0 a b)
  have hdiff : ∑ a, ∑ b, (p a b - q a b) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [hpsum, hqsum]
    ring
  calc (0 : ℝ) = ∑ a, ∑ b, (p a b - q a b) := hdiff.symm
    _ ≤ ∑ a, ∑ b, p a b * Real.log (p a b / q a b) :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hpoint a b))
    _ = klJoint p q := rfl

/-! ## 四、互信息 = KL(联合 ‖ 边缘乘积) -/

/-- **互信息 = 联合与边缘乘积之间的 KL**：`MI(p) = KL(p‖p_X⊗p_Y)`
（`RealMutualInformation.mutualInformation` 的 log(p)−log(q) 形式与
`klJoint` 的 log(p/q) 形式经 `Real.log_div` 对齐）。 -/
theorem mutualInformation_eq_klJoint_prodDist (p : Fin m → Fin n → ℝ)
    (hp0 : ∀ a b, 0 < p a b) (hr : ∀ a, 0 < marginalRow p a)
    (hc : ∀ b, 0 < marginalCol p b) :
    mutualInformation p = klJoint p (prodDist p) := by
  unfold mutualInformation klJoint
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Real.log_div (ne_of_gt (hp0 a b)) (ne_of_gt (prodDist_pos p a b (hr a) (hc b)))]

/-! ## 五、熵定义与 MI 的熵分解（补 RealMutualInformation 的标注缺口） -/

/-- **联合熵**：`H(X,Y) = −Σ_{a,b} p_ab·log p_ab`。 -/
noncomputable def jointEntropy (p : Fin m → Fin n → ℝ) : ℝ :=
  -∑ a, ∑ b, p a b * Real.log (p a b)

/-- **行边缘熵**：`H(X) = −Σ_a mr_a·log mr_a`。 -/
noncomputable def marginalEntropyRow (p : Fin m → Fin n → ℝ) : ℝ :=
  -∑ a, marginalRow p a * Real.log (marginalRow p a)

/-- **列边缘熵**：`H(Y) = −Σ_b mc_b·log mc_b`。 -/
noncomputable def marginalEntropyCol (p : Fin m → Fin n → ℝ) : ℝ :=
  -∑ b, marginalCol p b * Real.log (marginalCol p b)

/-- 行内提出常数：`Σ_a Σ_b p_ab·log(mr_a) = Σ_a mr_a·log(mr_a)`。 -/
lemma sum_sum_mul_log_marginalRow (p : Fin m → Fin n → ℝ) :
    (∑ a, ∑ b, p a b * Real.log (marginalRow p a))
      = ∑ a, marginalRow p a * Real.log (marginalRow p a) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul]
  rfl

/-- 列内提出常数（换序后）：`Σ_a Σ_b p_ab·log(mc_b) = Σ_b mc_b·log(mc_b)`。 -/
lemma sum_sum_mul_log_marginalCol (p : Fin m → Fin n → ℝ) :
    (∑ a, ∑ b, p a b * Real.log (marginalCol p b))
      = ∑ b, marginalCol p b * Real.log (marginalCol p b) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul]
  unfold marginalCol
  rfl

/-- **MI 的熵分解**（**补齐 `RealMutualInformation` 明确标注未做的部分**）：
`MI(p) = H(X) + H(Y) − H(X,Y)`。
证明：把 `log(mr_a·mc_b)` 拆成 `log mr_a + log mc_b`（`Real.log_mul`），
分配后分别用行/列提出常数引理提出 `mr_a`、`mc_b`。 -/
theorem mutualInformation_eq_entropy_decomposition (p : Fin m → Fin n → ℝ)
    (hr : ∀ a, 0 < marginalRow p a)
    (hc : ∀ b, 0 < marginalCol p b) :
    mutualInformation p = marginalEntropyRow p + marginalEntropyCol p - jointEntropy p := by
  have hlog : ∀ a b, Real.log (prodDist p a b)
      = Real.log (marginalRow p a) + Real.log (marginalCol p b) := by
    intro a b
    unfold prodDist
    rw [Real.log_mul (ne_of_gt (hr a)) (ne_of_gt (hc b))]
  have hsplit : (∑ a, ∑ b, p a b * (Real.log (p a b)
        - (Real.log (marginalRow p a) + Real.log (marginalCol p b))))
      = (∑ a, ∑ b, p a b * Real.log (p a b))
        - (∑ a, ∑ b, p a b * Real.log (marginalRow p a))
        - (∑ a, ∑ b, p a b * Real.log (marginalCol p b)) := by
    simp_rw [mul_sub, mul_add]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  unfold mutualInformation
  simp_rw [hlog]
  rw [hsplit, sum_sum_mul_log_marginalRow, sum_sum_mul_log_marginalCol]
  unfold marginalEntropyRow marginalEntropyCol jointEntropy
  ring

end Lattice
