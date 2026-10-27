import Mathlib
import Lattice.Lib.Architectures.RealTensorNorm
/-!
# LATTICE: n 维张量 Frobenius 范数（递归收缩 / 2 维回收矩阵版）

把 `RealTensorNorm` 的二维矩阵 Frobenius 范数推广到**任意阶 n** 的张量：
阶为 `n`、指标类型为 `ι` 的张量就是 `(Fin n → ι) → ℝ`（`Matrix (Fin m) (Fin n) ℝ`
本身就是 `Fin m → Fin n → ℝ`，故二维情形是 `n = 2` 的特例）。

本文件建立并**完整证明**（无 sorry/axiom/admit）：

  1. `tensorFrobSq`（`∑ idx : Fin n → ι, T idx ^ 2`）与
     `tensorFrob`（`= Real.sqrt ∘ tensorFrobSq`，本文件直接写成 `Real.sqrt (tensorFrobSq T)`）；
  2. 基本性质：非负性 `tensorFrobSq_nonneg` / `tensorFrob_nonneg`、
     零判定 `tensorFrobSq_zero_iff`（`= 0 ↔ ∀ idx, T idx = 0`）、
     数乘齐次 `tensorFrobSq_smul` / `tensorFrob_smul`（`frob (c • T) = |c| * frob T`）；
  3. 逐元素界 ⟹ 全局界：`tensorFrobSq_le_card_mul`（`≤ card (Fin n → ι) * M`）；
  4. 多指标 Cauchy–Schwarz：`tensorFrobSq_inner_sq_le`
     `(∑ idx, T idx * S idx)^2 ≤ tensorFrobSq T * tensorFrobSq S`；
  5. **2 维回收**：`frobenius_sq_eq_prod_sum`（`ι × κ` 版）与
     `tensorFrobSq_two_matches_matrix`（`Fin 2 → ι` 版，用显式等价
     `piFinTwoEquiv : (Fin 2 → ι) ≃ ι × ι`），把 n 维定义在 n = 2 时回收为
     `RealTensorNorm.frobSq` 的展开式 `∑ i, ∑ j, A i j ^ 2`；
  6. **递归收缩与「算子范数 ≤ Frobenius」**：
     `contract T x idx = ∑ a, T (Fin.cons a idx) * x a`，
     `tensorFrobSq_cons_decomp` 给出关键重组
     `tensorFrobSq T = ∑ a, ∑ idx, T (Fin.cons a idx)^2`
     （用显式等价 `finSuccProdEquiv : (Fin (n+1) → ι) ≃ ι × (Fin n → ι)`），
     由此 `contract_frobSq_le`
     `tensorFrobSq (contract T x) ≤ tensorFrobSq T * ∑ a, x a ^ 2` 对**所有 n** 成立，
     开方得 `contract_frob_le`
     `tensorFrob (contract T x) ≤ tensorFrob T * sqrt (∑ a, x a ^ 2)`。
     即逐层收缩（张量的「矩阵化」）不会增大范数——这是矩阵情形
     `RealTensorNorm.frob_vec_sq_le` / `frob_operator_norm_le` 的任意阶推广。

诚实标注（无 sorry / axiom / admit）：
- 本文件全部条目均已证明，**未证/未做**项为 0；
- 本文件的「算子范数」是最粗的 Frobenius 型上界：`contract` 只收缩一个指标，
  `contract_frobSq_le` 给的是「收缩后 Frobenius 平方 ≤ 原 Frobenius 平方 × 向量平方和」，
  不是 sharp 的谱范数常数（不做奇异值/谱理论）；
- `tensorFrobSq_le_card_mul` 中的 `card (Fin n → ι)` 是 `(card ι)^n` 的隐式写法，
  未另行化简为幂形式；
- 所有张量定义为普通函数类型，不做内存布局/计算复杂度主张。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## 一、n 维张量 Frobenius 范数 -/

/-- n 维张量 Frobenius 范数平方：`∑ idx : Fin n → ι, T idx ^ 2`。
（阶为 n 的张量 = `(Fin n → ι) → ℝ`；n = 2 时回收为矩阵的逐元素平方和。） -/
def tensorFrobSq {n : ℕ} (T : (Fin n → ι) → ℝ) : ℝ := ∑ idx : Fin n → ι, T idx ^ 2

/-- n 维张量 Frobenius 范数：`tensorFrob = Real.sqrt ∘ tensorFrobSq`，即
`Real.sqrt (∑ idx, T idx ^ 2)`。 -/
def tensorFrob {n : ℕ} (T : (Fin n → ι) → ℝ) : ℝ := Real.sqrt (tensorFrobSq T)

theorem tensorFrob_nonneg {n : ℕ} (T : (Fin n → ι) → ℝ) : 0 ≤ tensorFrob T :=
  Real.sqrt_nonneg _

theorem tensorFrobSq_nonneg {n : ℕ} (T : (Fin n → ι) → ℝ) : 0 ≤ tensorFrobSq T := by
  unfold tensorFrobSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- `tensorFrobSq T = 0` 当且仅当张量所有元素为零。 -/
theorem tensorFrobSq_zero_iff {n : ℕ} (T : (Fin n → ι) → ℝ) :
    tensorFrobSq T = 0 ↔ ∀ idx, T idx = 0 := by
  unfold tensorFrobSq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro h idx
    exact sq_eq_zero_iff.mp (h idx (Finset.mem_univ idx))
  · intro h i _
    exact sq_eq_zero_iff.mpr (h i)

/-! ## 二、数乘齐次 -/

theorem tensorFrobSq_smul {n : ℕ} (c : ℝ) (T : (Fin n → ι) → ℝ) :
    tensorFrobSq (c • T) = c ^ 2 * tensorFrobSq T := by
  unfold tensorFrobSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- 数乘齐次：`tensorFrob (c • T) = |c| * tensorFrob T`。 -/
theorem tensorFrob_smul {n : ℕ} (c : ℝ) (T : (Fin n → ι) → ℝ) :
    tensorFrob (c • T) = |c| * tensorFrob T := by
  unfold tensorFrob
  rw [tensorFrobSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-! ## 三、逐元素受控 ⟹ 全局界 -/

/-- 逐元素平方 ≤ M ⟹ `tensorFrobSq T ≤ card (Fin n → ι) * M`。

**第 211 轮删掉了前提 `(_hM : 0 ≤ M)`**（与 `RealTensorNorm.frobSq_le_card_mul_sq` 同一处修正）。
证明是 `Finset.sum_le_sum` 加 `Finset.sum_const`，**从未用到 `M` 的符号**——
加这条非负性是**无依据的收窄**，而原 docstring 还把它写成了必要条件。 -/
theorem tensorFrobSq_le_card_mul {n : ℕ} {T : (Fin n → ι) → ℝ} {M : ℝ}
    (h : ∀ idx, T idx ^ 2 ≤ M) :
    tensorFrobSq T ≤ (Fintype.card (Fin n → ι) : ℝ) * M := by
  unfold tensorFrobSq
  calc ∑ idx : Fin n → ι, T idx ^ 2 ≤ ∑ _idx : Fin n → ι, M :=
        Finset.sum_le_sum (fun i _ => h i)
    _ = (Fintype.card (Fin n → ι) : ℝ) * M := by
        simp [nsmul_eq_mul]

/-! ## 四、多指标 Cauchy–Schwarz -/

/-- **多指标 Cauchy–Schwarz**：`(∑ idx, T idx * S idx)^2 ≤ tensorFrobSq T * tensorFrobSq S`。
（把 `Fin n → ι` 视为单一有限索引，直接用实 CS `Finset.sum_mul_sq_le_sq_mul_sq`。） -/
theorem tensorFrobSq_inner_sq_le {n : ℕ} (T S : (Fin n → ι) → ℝ) :
    (∑ idx, T idx * S idx) ^ 2 ≤ tensorFrobSq T * tensorFrobSq S := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → ι)) T S
  simpa [tensorFrobSq] using h

/-! ## 五、与二维矩阵版本兼容（2 维回收） -/

/-- 乘积型求和的交换：`∑ i, ∑ j, A i j ^ 2 = ∑ p : ι × κ, A p.1 p.2 ^ 2`
（`Fintype.sum_prod_type`）。 -/
theorem frobenius_sq_eq_prod_sum {κ : Type*} [Fintype κ] (A : ι → κ → ℝ) :
    (∑ i : ι, ∑ j : κ, A i j ^ 2) = ∑ p : ι × κ, A p.1 p.2 ^ 2 := by
  rw [Fintype.sum_prod_type]

/-- `Fin 2 → ι` 与 `ι × ι` 的显式等价：`p ↦ (p 0, p 1)`，逆为
`(a, b) ↦ fun k => if k = 0 then a else b`。 -/
def piFinTwoEquiv (ι : Type*) : (Fin 2 → ι) ≃ ι × ι where
  toFun p := (p 0, p 1)
  invFun q := fun k => if k = 0 then q.1 else q.2
  left_inv p := by
    funext k
    fin_cases k <;> simp
  right_inv q := by
    rcases q with ⟨a, b⟩
    simp

omit [Fintype ι] in
/-- `piFinTwoEquiv` 的逆在 `(a, b)` 上的第 0 坐标是 `a`。 -/
theorem piFinTwoEquiv_symm_zero (a b : ι) :
    (piFinTwoEquiv ι).symm (a, b) 0 = a := by
  simp [piFinTwoEquiv]

omit [Fintype ι] in
/-- `piFinTwoEquiv` 的逆在 `(a, b)` 上的第 1 坐标是 `b`。 -/
theorem piFinTwoEquiv_symm_one (a b : ι) :
    (piFinTwoEquiv ι).symm (a, b) 1 = b := by
  simp [piFinTwoEquiv]

/-- **2 维回收（`Fin 2 → ι` 版）**：把 n 维张量 Frobenius 平方限制到 `n = 2`，
得到矩阵的逐元素平方和 `∑ i, ∑ j, A i j ^ 2`（即 `RealTensorNorm.frobSq` 的展开式）。
证明：用显式等价 `piFinTwoEquiv` 做 `Equiv.sum_comp` 重指标，再用
`Fintype.sum_prod_type` 拆成迭代和。 -/
theorem tensorFrobSq_two_matches_matrix (A : ι → ι → ℝ) :
    tensorFrobSq (fun p : Fin 2 → ι => A (p 0) (p 1)) = ∑ i : ι, ∑ j : ι, A i j ^ 2 := by
  unfold tensorFrobSq
  rw [← Equiv.sum_comp (piFinTwoEquiv ι).symm
        (fun p : Fin 2 → ι => A (p 0) (p 1) ^ 2)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [piFinTwoEquiv_symm_zero, piFinTwoEquiv_symm_one]

/-! ## 六、递归收缩：n 维张量的算子范数 ≤ Frobenius 范数 -/

/-- 沿首指标收缩：`contract T x idx = ∑ a, T (Fin.cons a idx) * x a`，
把 (n+1) 阶张量 `T` 与向量 `x` 收缩成 n 阶张量。
（`Fin.cons a idx : Fin (n+1) → ι` 是「首元素为 a、其余为 idx」的序列。） -/
def contract {n : ℕ} (T : (Fin (n + 1) → ι) → ℝ) (x : ι → ℝ) : (Fin n → ι) → ℝ :=
  fun idx => ∑ a : ι, T (Fin.cons a idx) * x a

/-- `Fin (n+1) → ι` 与 `ι × (Fin n → ι)` 的显式等价：
`p ↦ (p 0, Fin.tail p)`，逆为 `(a, idx) ↦ Fin.cons a idx`。 -/
def finSuccProdEquiv (ι : Type*) (n : ℕ) : (Fin (n + 1) → ι) ≃ ι × (Fin n → ι) where
  toFun p := (p 0, Fin.tail p)
  invFun q := Fin.cons q.1 q.2
  left_inv p := by
    funext k
    induction k using Fin.cases with
    | zero => simp
    | succ k => rfl
  right_inv q := by
    rcases q with ⟨a, t⟩
    simp

omit [Fintype ι] in
/-- `finSuccProdEquiv` 的逆在 `(a, idx)` 上等于 `Fin.cons a idx`。 -/
theorem finSuccProdEquiv_symm_apply (a : ι) (idx : Fin n → ι) :
    (finSuccProdEquiv ι n).symm (a, idx) = Fin.cons a idx := by
  simp [finSuccProdEquiv]

/-- **关键重组**：`tensorFrobSq T = ∑ a, ∑ idx, T (Fin.cons a idx)^2`。
即把 `(Fin (n+1) → ι)` 的和按首指标分解为 `ι × (Fin n → ι)` 的迭代和。 -/
theorem tensorFrobSq_cons_decomp {n : ℕ} (T : (Fin (n + 1) → ι) → ℝ) :
    tensorFrobSq T = ∑ a : ι, ∑ idx : Fin n → ι, T (Fin.cons a idx) ^ 2 := by
  unfold tensorFrobSq
  rw [← Equiv.sum_comp (finSuccProdEquiv ι n).symm (fun p : Fin (n + 1) → ι => T p ^ 2)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro idx _
  rw [finSuccProdEquiv_symm_apply]

/-- **递归收缩的算子范数 ≤ Frobenius 范数（平方形式）**：
`tensorFrobSq (contract T x) ≤ tensorFrobSq T * ∑ a, x a ^ 2`。
证明：对每个 `idx` 用 Cauchy–Schwarz 控制 `(∑ a, T (cons a idx) x a)^2`，
外层求和后用 `tensorFrobSq_cons_decomp` 重组回 (n+1) 阶 Frobenius 平方。
这直接给出矩阵情形 `RealTensorNorm.frob_vec_sq_le` 的任意阶推广。 -/
theorem contract_frobSq_le {n : ℕ} (T : (Fin (n + 1) → ι) → ℝ) (x : ι → ℝ) :
    tensorFrobSq (contract T x) ≤ tensorFrobSq T * (∑ a, x a ^ 2) := by
  have hcs : ∀ idx : Fin n → ι,
      (∑ a : ι, T (Fin.cons a idx) * x a) ^ 2 ≤
        (∑ a : ι, T (Fin.cons a idx) ^ 2) * (∑ a : ι, x a ^ 2) :=
    fun idx => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun a => T (Fin.cons a idx)) (fun a => x a)
  calc tensorFrobSq (contract T x)
      = ∑ idx : Fin n → ι, (∑ a : ι, T (Fin.cons a idx) * x a) ^ 2 := by
        simp [tensorFrobSq, contract]
    _ ≤ ∑ idx : Fin n → ι, (∑ a : ι, T (Fin.cons a idx) ^ 2) * (∑ a : ι, x a ^ 2) :=
        Finset.sum_le_sum (fun idx _ => hcs idx)
    _ = (∑ idx : Fin n → ι, ∑ a : ι, T (Fin.cons a idx) ^ 2) * (∑ a : ι, x a ^ 2) := by
        rw [Finset.sum_mul]
    _ = (∑ a : ι, ∑ idx : Fin n → ι, T (Fin.cons a idx) ^ 2) * (∑ a : ι, x a ^ 2) := by
        rw [Finset.sum_comm]
    _ = tensorFrobSq T * (∑ a : ι, x a ^ 2) := by
        rw [← tensorFrobSq_cons_decomp]

/-- **递归收缩的算子范数 ≤ Frobenius 范数（开方形式）**：
`tensorFrob (contract T x) ≤ tensorFrob T * sqrt (∑ a, x a ^ 2)`。 -/
theorem contract_frob_le {n : ℕ} (T : (Fin (n + 1) → ι) → ℝ) (x : ι → ℝ) :
    tensorFrob (contract T x) ≤ tensorFrob T * Real.sqrt (∑ a, x a ^ 2) := by
  unfold tensorFrob
  calc Real.sqrt (tensorFrobSq (contract T x))
      ≤ Real.sqrt (tensorFrobSq T * (∑ a, x a ^ 2)) :=
        Real.sqrt_le_sqrt (contract_frobSq_le T x)
    _ = Real.sqrt (tensorFrobSq T) * Real.sqrt (∑ a, x a ^ 2) :=
        Real.sqrt_mul (tensorFrobSq_nonneg T) _

end Lattice
