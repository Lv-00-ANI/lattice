import Mathlib

/-!
# LATTICE: 凸/对数工具箱 —— 类 Gibbs 不等式与两点凹凸性的**唯一权威位置**

信息论线与收敛线反复使用三个初等内核（此前在 7 个文件中各自独立证明）：

  1. **逐项 Gibbs 下界**：`0 ≤ x`、`0 < y` ⟹ `x − y ≤ x·(log x − log y)`；
  2. **log 的两点凹性**：`λ·log x + (1−λ)·log y ≤ log(λ·x + (1−λ)·y)`；
  3. **`t·log(t/q)` 的两点凸性**：`m·log(m/q) ≤ λ·x·log(x/q) + (1−λ)·y·log(y/q)`，`m = λx + (1−λ)y`。

三者共用同一初等技法：**只用 `log z ≤ z − 1` 与 `1 − z⁻¹ ≤ log z`，加权求和恰为 0**
（不依赖任何 mathlib 凸性引理名，故对 mathlib 版本迁移不敏感）。

## 本文件是"单一权威位置"（single source of truth）

| 权威引理 | 此前分散的同义证明（见 `REFACTOR.md` C-1/C-2） |
|:--|:--|
| `gibbs_ineq` | `RealKL.kl_term_ge`、`RealMutualInformation.gibbs_term` |
| `log_concave_pair` | `RealKLConvexity.log_concave_two` |
| `mul_log_convex_pair` | `RealKLConvexity.mul_log_convex_two` |
| （逐项 log-sum 族） | `RealKLJointConvex.logsum_two/logsum_finset`、`RealDataProcessing.logsum_le`、`RealFDivergence.fdiv_nonneg_of_convex` |

**命名约定**：本文件的引理名**刻意不同于**既有文件中的同义名（`gibbs_ineq` vs `gibbs_term`、
`log_concave_pair` vs `log_concave_two` 等）——避免"同时导入 toolkit 与旧文件"时的命名冲突
（教训见 `NAMING.md`：14 处跨文件同名声明全部藏在不相交 import 闭包中）。
后续**新增**文件应直接引用本文件；**既有**文件按 `REFACTOR.md` §4 的次序逐步迁移为一行别名。

**诚实边界**：
- 全部为初等实分析引理，无额外假设（仅 `log` 定义域正性）；
- 不含 **log-sum 一般形**（`Σ xᵢ·log(xᵢ/yᵢ) ≥ (Σxᵢ)·log(Σxᵢ/Σyᵢ)`）的完整加权版——该形式在各文件以
  "逐项 `gibbs_ineq` + 求和"的方式等价实现，未在此重复抽象（避免引入与 `RealDataProcessing.logsum_le`
  的命名/语义重叠）；
- 模型无关：任意实数，不假设概率归一化（归一化由各使用点自行提供）。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 1. 逐项 Gibbs 不等式族 -/

/-- **对数幂不等式**（`log z ≤ z − 1`，薄封装便于统一调用；`0 < z`）。 -/
lemma log_gibbs_pt {z : ℝ} (hz : 0 < z) : Real.log z ≤ z - 1 :=
  Real.log_le_sub_one_of_pos hz

/-- **加权对数幂不等式**：`0 ≤ w`、`0 < z` ⟹ `w·log z ≤ w·(z − 1)`。 -/
lemma log_gibbs_weighted {w z : ℝ} (hw : 0 ≤ w) (hz : 0 < z) :
    w * Real.log z ≤ w * (z - 1) :=
  mul_le_mul_of_nonneg_left (log_gibbs_pt hz) hw

/-- **逐项 Gibbs 下界（非加权）**：`0 ≤ x`、`0 < y` ⟹ `x − y ≤ x·(log x − log y)`。
权威位置——`RealKL.kl_term_ge`、`RealMutualInformation.gibbs_term` 与此同义。 -/
lemma gibbs_ineq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_mul, zero_sub]
    linarith
  · have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hratio : 0 < x / y := div_pos hx' hy
    have hlog := Real.one_sub_inv_le_log_of_pos hratio
    have hinv : (x / y)⁻¹ = y / x := by simp
    have hlog' : 1 - y / x ≤ Real.log (x / y) := by rwa [hinv] at hlog
    have hsep : Real.log (x / y) = Real.log x - Real.log y :=
      Real.log_div (ne_of_gt hx') (ne_of_gt hy)
    have hmul : x * (1 - y / x) ≤ x * (Real.log x - Real.log y) := by
      rw [← hsep]
      exact mul_le_mul_of_nonneg_left hlog' (le_of_lt hx')
    have heq : x * (1 - y / x) = x - y := by field_simp
    rwa [heq] at hmul

/-- **加权 Gibbs 下界**：`0 ≤ w` ⟹ `w·(x − y) ≤ w·x·(log x − log y)`。
求和形式即"逐项 Gibbs + 求和"，用于 f-散度/熵/KL 的非负性。 -/
lemma gibbs_ineq_weighted {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 < y) :
    w * (x - y) ≤ w * (x * (Real.log x - Real.log y)) :=
  mul_le_mul_of_nonneg_left (gibbs_ineq hx hy) hw

/-- 非负权求和版：`∀a, 0 ≤ w a`、`∀a, 0 < y a` ⟹ `Σ w·(x−y) ≤ Σ w·x·(log x − log y)`。
（对齐 `RealCrossEntropy.ce_nonneg`、`RealKL.kl_nonneg` 的逐项路线。） -/
lemma gibbs_ineq_finset {k : ℕ} (w x y : Fin k → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hx : ∀ a, 0 ≤ x a) (hy : ∀ a, 0 < y a) :
    (∑ a, w a * (x a - y a)) ≤ ∑ a, w a * (x a * (Real.log (x a) - Real.log (y a))) :=
  Finset.sum_le_sum (fun a _ => gibbs_ineq_weighted (hw a) (hx a) (hy a))

/-! ## 2. log 的两点凹性（初等证法） -/

/-- **log 的两点凹性**：`0 < x`、`0 < y`、`λ ∈ [0,1]` ⟹
`λ·log x + (1−λ)·log y ≤ log(λ·x + (1−λ)·y)`。
权威位置——`RealKLConvexity.log_concave_two` 与此同义。 -/
lemma log_concave_pair {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * Real.log x + (1 - lam) * Real.log y ≤ Real.log (lam * x + (1 - lam) * y) := by
  have hm : 0 < lam * x + (1 - lam) * y := by
    rcases eq_or_lt_of_le hlam0 with h0 | h0
    · rw [← h0]
      rw [zero_mul, zero_add, sub_zero, one_mul]
      exact hy
    · have hmul : 0 < lam * x := mul_pos h0 hx
      have hle : 0 ≤ (1 - lam) * y := mul_nonneg (by linarith) (le_of_lt hy)
      linarith
  have hxm : 0 < x / (lam * x + (1 - lam) * y) := div_pos hx hm
  have hym : 0 < y / (lam * x + (1 - lam) * y) := div_pos hy hm
  have hlx : Real.log x
      = Real.log (x / (lam * x + (1 - lam) * y)) + Real.log (lam * x + (1 - lam) * y) := by
    rw [← Real.log_mul (ne_of_gt hxm) (ne_of_gt hm), mul_comm]
    congr 1
    field_simp
  have hly : Real.log y
      = Real.log (y / (lam * x + (1 - lam) * y)) + Real.log (lam * x + (1 - lam) * y) := by
    rw [← Real.log_mul (ne_of_gt hym) (ne_of_gt hm), mul_comm]
    congr 1
    field_simp
  have hbd1 : Real.log (x / (lam * x + (1 - lam) * y))
      ≤ x / (lam * x + (1 - lam) * y) - 1 := Real.log_le_sub_one_of_pos hxm
  have hbd2 : Real.log (y / (lam * x + (1 - lam) * y))
      ≤ y / (lam * x + (1 - lam) * y) - 1 := Real.log_le_sub_one_of_pos hym
  have hw1 : lam * Real.log (x / (lam * x + (1 - lam) * y))
      ≤ lam * (x / (lam * x + (1 - lam) * y) - 1) :=
    mul_le_mul_of_nonneg_left hbd1 hlam0
  have hw2 : (1 - lam) * Real.log (y / (lam * x + (1 - lam) * y))
      ≤ (1 - lam) * (y / (lam * x + (1 - lam) * y) - 1) :=
    mul_le_mul_of_nonneg_left hbd2 (by linarith)
  have hzero : lam * (x / (lam * x + (1 - lam) * y) - 1)
      + (1 - lam) * (y / (lam * x + (1 - lam) * y) - 1) = 0 := by
    field_simp
    ring
  calc
    lam * Real.log x + (1 - lam) * Real.log y
        = lam * (Real.log (x / (lam * x + (1 - lam) * y))
              + Real.log (lam * x + (1 - lam) * y))
          + (1 - lam) * (Real.log (y / (lam * x + (1 - lam) * y))
              + Real.log (lam * x + (1 - lam) * y)) := by rw [hlx, hly]
    _ = (lam * Real.log (x / (lam * x + (1 - lam) * y))
          + (1 - lam) * Real.log (y / (lam * x + (1 - lam) * y)))
        + Real.log (lam * x + (1 - lam) * y) := by ring
    _ ≤ (lam * (x / (lam * x + (1 - lam) * y) - 1)
          + (1 - lam) * (y / (lam * x + (1 - lam) * y) - 1))
        + Real.log (lam * x + (1 - lam) * y) := by linarith
    _ = Real.log (lam * x + (1 - lam) * y) := by rw [hzero]; ring

/-! ## 3. `t·log(t/q)` 的两点凸性（初等证法） -/

/-- **`t·log(t/q)` 的两点凸性**：`0 < x`、`0 < y`、`0 < q`、`λ ∈ [0,1]` 时
`m·log(m/q) ≤ λ·x·log(x/q) + (1−λ)·y·log(y/q)`，其中 `m = λx + (1−λ)y`。
权威位置——`RealKLConvexity.mul_log_convex_two` 与此同义；
是 KL 对 p 凸、`RealKLJointConvex.kl_joint_convex` 的逐项内核。 -/
lemma mul_log_convex_pair {x y q lam : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (lam * x + (1 - lam) * y) * Real.log ((lam * x + (1 - lam) * y) / q)
      ≤ lam * (x * Real.log (x / q)) + (1 - lam) * (y * Real.log (y / q)) := by
  have hm : 0 < lam * x + (1 - lam) * y := by
    rcases eq_or_lt_of_le hlam0 with h0 | h0
    · rw [← h0]
      rw [zero_mul, zero_add, sub_zero, one_mul]
      exact hy
    · have hmul : 0 < lam * x := mul_pos h0 hx
      have hle : 0 ≤ (1 - lam) * y := mul_nonneg (by linarith) (le_of_lt hy)
      linarith
  have hxm : 0 < x / (lam * x + (1 - lam) * y) := div_pos hx hm
  have hym : 0 < y / (lam * x + (1 - lam) * y) := div_pos hy hm
  have hmq : 0 < (lam * x + (1 - lam) * y) / q := div_pos hm hq
  have hlx : Real.log (x / q)
      = Real.log (x / (lam * x + (1 - lam) * y))
        + Real.log ((lam * x + (1 - lam) * y) / q) := by
    have hsplit : x / q = (x / (lam * x + (1 - lam) * y)) * ((lam * x + (1 - lam) * y) / q) := by
      field_simp
    rw [hsplit, Real.log_mul (ne_of_gt hxm) (ne_of_gt hmq)]
  have hly : Real.log (y / q)
      = Real.log (y / (lam * x + (1 - lam) * y))
        + Real.log ((lam * x + (1 - lam) * y) / q) := by
    have hsplit : y / q = (y / (lam * x + (1 - lam) * y)) * ((lam * x + (1 - lam) * y) / q) := by
      field_simp
    rw [hsplit, Real.log_mul (ne_of_gt hym) (ne_of_gt hmq)]
  have hbd1 : x - (lam * x + (1 - lam) * y)
      ≤ x * Real.log (x / (lam * x + (1 - lam) * y)) := by
    have hle := Real.one_sub_inv_le_log_of_pos hxm
    have hinv : (x / (lam * x + (1 - lam) * y))⁻¹ = (lam * x + (1 - lam) * y) / x := by simp
    rw [hinv] at hle
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hx)
    have heq : x * (1 - (lam * x + (1 - lam) * y) / x) = x - (lam * x + (1 - lam) * y) := by
      field_simp
    rwa [heq] at hmul
  have hbd2 : y - (lam * x + (1 - lam) * y)
      ≤ y * Real.log (y / (lam * x + (1 - lam) * y)) := by
    have hle := Real.one_sub_inv_le_log_of_pos hym
    have hinv : (y / (lam * x + (1 - lam) * y))⁻¹ = (lam * x + (1 - lam) * y) / y := by simp
    rw [hinv] at hle
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hy)
    have heq : y * (1 - (lam * x + (1 - lam) * y) / y) = y - (lam * x + (1 - lam) * y) := by
      field_simp
    rwa [heq] at hmul
  have hlow : 0 ≤ lam * (x * Real.log (x / (lam * x + (1 - lam) * y)))
      + (1 - lam) * (y * Real.log (y / (lam * x + (1 - lam) * y))) := by
    have h1 := mul_le_mul_of_nonneg_left hbd1 hlam0
    have h2 := mul_le_mul_of_nonneg_left hbd2 (by linarith : (0 : ℝ) ≤ 1 - lam)
    have hzero : lam * (x - (lam * x + (1 - lam) * y))
        + (1 - lam) * (y - (lam * x + (1 - lam) * y)) = 0 := by ring
    linarith [h1, h2, hzero]
  have key : lam * (x * Real.log (x / q)) + (1 - lam) * (y * Real.log (y / q))
      - (lam * x + (1 - lam) * y) * Real.log ((lam * x + (1 - lam) * y) / q)
      = lam * (x * Real.log (x / (lam * x + (1 - lam) * y)))
        + (1 - lam) * (y * Real.log (y / (lam * x + (1 - lam) * y))) := by
    rw [hlx, hly]
    ring
  linarith [key, hlow]

end Lattice
