import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Quantization.RealQuantizedError
/-!
# LATTICE: 剪枝稀疏化误差界 —— 幅度置零的 Frobenius/算子误差与 n 层前向传播衔接

部署优化线（剪枝/稀疏化）：把权重矩阵中**幅度最小**的分量置零（pruning），
给出由此引入的误差界，并衔接 RealQuantizedError 的 n 层量化传播框架：

  1. `pruneMatrix`/`pruneError`：剪枝模型 A'（被剪集 S 上分量置 0，其余保持
     A 不变）与误差矩阵 B = A − A'（仅在被剪集 S 上非零，值 = A 的分量）；
  2. `prune_magnitude_bound`（核心）：若被剪分量幅度 |Aᵢⱼ| ≤ θ（θ ≥ 0）且
     被剪集大小 |S| ≤ s，则 Frobenius 误差 ‖A − A'‖_F ≤ √s·θ
     （Σ_{p∈S}(Aᵢⱼ)² ≤ |S|·θ² ≤ s·θ²，开方：`frobeniusNorm_sq` + `sq_le_sq`）；
  3. `prune_op_norm_bound`：由 RealMatrixNorm 的 `opNorm_le_frobenius`
     （算子范数 ≤ Frobenius 范数）得算子误差 ‖A − A'‖_op ≤ √s·θ；
  4. `prune_output_bound`：逐点输出误差 ‖(A − A')x‖ ≤ √s·θ·‖x‖
     （`frobenius_bound` / `le_opNorm` 两条路线）；
  5. `prune_threshold_exists` / `prune_threshold_from_kept`：阈值存在性
     —— θ = 被剪集幅度的最大值；若保留集 K 逐点支配被剪集（保留幅度 ≥
     被剪幅度，top-k 保留的排序性质的 honest 抽象），θ = 保留集幅度的
     最小值；衔接 RealTopK 的 top-k 思想（免排序）；
  6. `prune_chain_error` / `prune_chain_error_pruned`：把逐层剪枝误差
     δᵢ = √sᵢ·θᵢ 代入 RealQuantizedError 的 `quantized_chain_error_closed`
     （剪枝 = 量化特例：被剪分量 → 0），得 n 层剪枝模型的端到端前向误差界
     Σ_{i<k} (∏后层范数)·δᵢ·(∏前层范数)·‖x‖；
  7. `prune_zero_keep` / `prune_error_zero_outside`：被保留分量逐点不变，
     误差矩阵在被剪集外为零（剪枝只影响被剪集）。

诚实假设（全部显式标注）：幅度阈值 θ ≥ 0；被剪集大小 |S| ≤ s（s : ℕ）；
被剪分量幅度上界 |Aᵢⱼ| ≤ θ 由"剪小留大"的剪枝策略自然给出（θ = 阈值）；
阈值存在性定理要求被剪集（或保留集）非空（Finset 的 max'/min' 前提）。
其余为范数公理与求和事实（sum_le_sum、sq_le、card）。

模型无关：任意 m×n 维度（Fin 指标）；剪枝集为 `Finset (Fin m × Fin n)`
（行 × 列坐标对）。无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {m n : ℕ}

/-! ## 剪枝与误差矩阵 -/

/-- 剪枝模型 A'：被剪集 S（`Finset (Fin m × Fin n)` 的行列坐标对）上分量置 0，
其余分量保持 A 不变。 -/
def pruneMatrix (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ S then 0 else A i j

/-- 剪枝误差矩阵 B = A − A'：仅在被剪集 S 上非零（值 = A 的分量）。 -/
def pruneError (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if (i, j) ∈ S then A i j else 0

/-- 剪枝模型与被剪前的差恰为误差矩阵：A − A' = B（逐点）。 -/
lemma prune_sub_eq_error (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    A - pruneMatrix A S = pruneError A S := by
  ext i j
  by_cases hij : (i, j) ∈ S <;> simp [pruneMatrix, pruneError, hij]

/-- 剪枝模型的差（A' − A）= 误差矩阵的相反数（衔接 matCLME 线性性）。 -/
lemma pruneMatrix_sub_eq_neg (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    pruneMatrix A S - A = -pruneError A S := by
  ext i j
  by_cases hij : (i, j) ∈ S <;> simp [pruneMatrix, pruneError, hij]

/-- 被保留分量不变：A' 与 A 在 S 的补集上逐点相等（剪枝只影响被剪集）。 -/
lemma prune_zero_keep (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    ∀ i j, (i, j) ∉ S → pruneMatrix A S i j = A i j := by
  intro i j hij
  simp [pruneMatrix, hij]

/-- 误差矩阵在被剪集外为零。 -/
lemma prune_error_zero_outside (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    ∀ i j, (i, j) ∉ S → pruneError A S i j = 0 := by
  intro i j hij
  simp [pruneError, hij]

/-! ## Finset 工具：pair 求和与 ite 消除 -/

/-- 全空间求和消去 ite：Σ_p (if p ∈ S then f p else 0) = Σ_{p∈S} f p。 -/
lemma sum_ite_mem {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    (∑ p : α, if p ∈ S then f p else 0) = ∑ p in S, f p := by
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun p : α => p ∈ S)) = S := by
    ext p
    simp
  rw [hset]

/-- 双重求和（i, j）化为被剪集上的求和：
Σ_i Σ_j (if (i,j) ∈ S then (A i j)² else 0) = Σ_{p∈S} (A p.1 p.2)²。 -/
lemma sum_double_ite (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n)) :
    (∑ i : Fin m, ∑ j : Fin n, (if (i, j) ∈ S then (A i j) ^ 2 else 0))
      = ∑ p in S, (A p.1 p.2) ^ 2 := by
  let g : Fin m × Fin n → ℝ := fun p => if p ∈ S then (A p.1 p.2) ^ 2 else 0
  calc
    (∑ i : Fin m, ∑ j : Fin n, (if (i, j) ∈ S then (A i j) ^ 2 else 0))
        = ∑ i : Fin m, ∑ j : Fin n, g (i, j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          simp [g]
    _ = ∑ p : Fin m × Fin n, g p := (Fintype.sum_prod_type g).symm
    _ = ∑ p in S, (A p.1 p.2) ^ 2 := by
          simp [g]

/-! ## 定理一（核心）：Frobenius 剪枝误差界 -/

/-- 核心剪枝误差界：被剪分量 |Aᵢⱼ| ≤ θ（θ ≥ 0）且被剪集大小 |S| ≤ s
⟹ Frobenius 误差 ‖A − A'‖_F ≤ √s·θ。证明路线：
Σ_{p∈S}(A p.1 p.2)² ≤ |S|·θ² ≤ s·θ²（逐项 sq_le + sum_le_sum + card），
再用 frobeniusNorm_sq + sq_le_sq 开方。 -/
theorem prune_magnitude_bound (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) :
    frobeniusNorm (pruneError A S) ≤ Real.sqrt (s : ℝ) * θ := by
  have hsq : (frobeniusNorm (pruneError A S)) ^ 2 ≤ (Real.sqrt (s : ℝ) * θ) ^ 2 := by
    calc
      (frobeniusNorm (pruneError A S)) ^ 2
          = ∑ i : Fin m, ∑ j : Fin n, (pruneError A S i j) ^ 2 := frobeniusNorm_sq (pruneError A S)
      _ = ∑ i : Fin m, ∑ j : Fin n, (if (i, j) ∈ S then (A i j) ^ 2 else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : (i, j) ∈ S <;> simp [pruneError, hij]
      _ = ∑ p in S, (A p.1 p.2) ^ 2 := sum_double_ite A S
      _ ≤ ∑ p in S, θ ^ 2 := by
            apply Finset.sum_le_sum
            intro p hp
            exact sq_le_sq.mpr (by
              rw [abs_of_nonneg hθ]
              exact hA p hp)
      _ = (S.card : ℝ) * θ ^ 2 := by
            simp [Finset.sum_const]
      _ ≤ (s : ℝ) * θ ^ 2 := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (sq_nonneg θ)
      _ = (Real.sqrt (s : ℝ) * θ) ^ 2 := by
            have hs : 0 ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le s
            rw [mul_pow, Real.sq_sqrt hs]
  have hnonneg : 0 ≤ Real.sqrt (s : ℝ) * θ :=
    mul_nonneg (Real.sqrt_nonneg _) hθ
  have habs : |frobeniusNorm (pruneError A S)| ≤ |Real.sqrt (s : ℝ) * θ| := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (frobeniusNorm_nonneg (pruneError A S)), abs_of_nonneg hnonneg] using habs

/-- Frobenius 误差（直接形式）：‖A − A'‖_F ≤ √s·θ（A' = pruneMatrix A S）。
与 `prune_magnitude_bound` 等价（A − A' = pruneError A S）。 -/
theorem prune_frobenius_error (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) :
    frobeniusNorm (A - pruneMatrix A S) ≤ Real.sqrt (s : ℝ) * θ := by
  rw [prune_sub_eq_error]
  exact prune_magnitude_bound A S s θ hS hθ hA

/-! ## 定理二：算子范数剪枝误差界（opNorm ≤ Frobenius） -/

/-- 算子范数剪枝误差界：‖A − A'‖_op ≤ √s·θ
（衔接 RealMatrixNorm.opNorm_le_frobenius：‖matCLME B‖ ≤ frobeniusNorm B）。 -/
theorem prune_op_norm_bound (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) :
    ‖matCLME (pruneError A S)‖ ≤ Real.sqrt (s : ℝ) * θ := by
  exact le_trans (opNorm_le_frobenius (pruneError A S))
    (prune_magnitude_bound A S s θ hS hθ hA)

/-! ## 定理三：逐点输出误差界 -/

/-- 逐点输出误差界：‖(A − A')x‖ ≤ √s·θ·‖x‖
（衔接 frobenius_bound：‖Ax‖ ≤ ‖A‖_F·‖x‖）。 -/
theorem prune_output_bound (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖matvecE (pruneError A S) x‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  calc
    ‖matvecE (pruneError A S) x‖ ≤ frobeniusNorm (pruneError A S) * ‖x‖ :=
      frobenius_bound (pruneError A S) x
    _ ≤ (Real.sqrt (s : ℝ) * θ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (prune_magnitude_bound A S s θ hS hθ hA) (norm_nonneg x)

/-- 逐点输出误差界（算子版）：‖(A − A')x‖ ≤ √s·θ·‖x‖（衔接 le_opNorm）。 -/
theorem prune_output_bound_clm (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖matCLME (pruneError A S) x‖ ≤ Real.sqrt (s : ℝ) * θ * ‖x‖ := by
  calc
    ‖matCLME (pruneError A S) x‖ ≤ ‖matCLME (pruneError A S)‖ * ‖x‖ :=
      (matCLME (pruneError A S)).le_opNorm x
    _ ≤ (Real.sqrt (s : ℝ) * θ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (prune_op_norm_bound A S s θ hS hθ hA) (norm_nonneg x)

/-! ## matCLME 的线性性（剪枝差 = 误差矩阵的算子化） -/

lemma matvecE_sub (A B : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matvecE (A - B) x = matvecE A x - matvecE B x := by
  ext i
  calc
    (∑ j : Fin n, (A i j - B i j) * x j) = ∑ j : Fin n, (A i j * x j - B i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j : Fin n, A i j * x j) - (∑ j : Fin n, B i j * x j) := by
      rw [Finset.sum_sub_distrib]

lemma matvecE_neg (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    matvecE (-A) x = -matvecE A x := by
  ext i
  calc
    (∑ j : Fin n, (-A i j) * x j) = ∑ j : Fin n, -(A i j * x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = -(∑ j : Fin n, A i j * x j) := by
      rw [Finset.sum_neg_distrib]

lemma matCLME_sub (A B : Matrix (Fin m) (Fin n) ℝ) :
    matCLME (A - B) = matCLME A - matCLME B := by
  apply ContinuousLinearMap.ext
  intro x
  simpa [matCLME_apply] using matvecE_sub A B x

lemma matCLME_neg (A : Matrix (Fin m) (Fin n) ℝ) :
    matCLME (-A) = -matCLME A := by
  apply ContinuousLinearMap.ext
  intro x
  simpa [matCLME_apply] using matvecE_neg A x

/-- 剪枝矩阵差（A' − A）的算子范数 ≤ √s·θ：衔接剪枝误差与逐层 δᵢ。 -/
lemma prune_error_norm (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (θ : ℝ) (hS : S.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ p, p ∈ S → |A p.1 p.2| ≤ θ) :
    ‖matCLME (pruneMatrix A S) - matCLME A‖ ≤ Real.sqrt (s : ℝ) * θ := by
  calc
    ‖matCLME (pruneMatrix A S) - matCLME A‖
        = ‖matCLME (pruneMatrix A S - A)‖ := by rw [matCLME_sub]
    _ = ‖matCLME (-pruneError A S)‖ := by rw [pruneMatrix_sub_eq_neg]
    _ = ‖-matCLME (pruneError A S)‖ := by rw [matCLME_neg]
    _ = ‖matCLME (pruneError A S)‖ := by rw [norm_neg]
    _ ≤ Real.sqrt (s : ℝ) * θ := prune_op_norm_bound A S s θ hS hθ hA

/-! ## 定理四：n 层剪枝模型端到端前向误差（衔接 RealQuantizedError） -/

/-- n 层剪枝模型端到端误差（抽象 δᵢ 版）：每层剪枝算子误差
‖matCLME (Ap i) − matCLME (A i)‖ ≤ δ i（i < k）⟹ 前向误差
‖quantFwd (Ap 层) k x − quantFwd (A 层) k x‖
≤ Σ_{i<k} (∏_{j∈Ioo i k} ‖matCLME (Ap j)‖)·δ i·(∏_{j<i} ‖matCLME (A j)‖)·‖x‖。
直接实例化 RealQuantizedError.quantized_chain_error_closed（剪枝 = 量化特例：
被剪分量 → 0，即量化到零的 Wq = pruneMatrix A S）。 -/
theorem prune_chain_error (A Ap : ℕ → Matrix (Fin n) (Fin n) ℝ) (δ : ℕ → ℝ) (k : ℕ)
    (hδ : ∀ i, i < k → ‖matCLME (Ap i) - matCLME (A i)‖ ≤ δ i) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖quantFwd (fun i => matCLME (Ap i)) k x - quantFwd (fun i => matCLME (A i)) k x‖
        ≤ ∑ i in Finset.range k,
            (∏ j in Finset.Ioo i k, ‖matCLME (Ap j)‖) * δ i
              * (∏ j in Finset.range i, ‖matCLME (A j)‖) * ‖x‖ := by
  intro x
  exact quantized_chain_error_closed (fun i => matCLME (A i)) (fun i => matCLME (Ap i)) δ k hδ x

/-- n 层剪枝模型端到端误差（剪枝参数版）：每层被剪集 S i 大小 ≤ s i、
被剪分量 |A i p.1 p.2| ≤ θ i（θ i ≥ 0）⟹ 前向误差
≤ Σ_{i<k} (∏后层范数)·(√(s i)·θ i)·(∏前层范数)·‖x‖
（δᵢ = √(s i)·θ i 来自 `prune_error_norm`，代入 `prune_chain_error`）。 -/
theorem prune_chain_error_pruned (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (S : ℕ → Finset (Fin n × Fin n)) (s : ℕ → ℕ) (θ : ℕ → ℝ) (k : ℕ)
    (hS : ∀ i, i < k → (S i).card ≤ s i)
    (hθ : ∀ i, i < k → 0 ≤ θ i)
    (hA : ∀ i, i < k → ∀ p, p ∈ S i → |A i p.1 p.2| ≤ θ i) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖quantFwd (fun i => matCLME (pruneMatrix (A i) (S i))) k x
        - quantFwd (fun i => matCLME (A i)) k x‖
        ≤ ∑ i in Finset.range k,
            (∏ j in Finset.Ioo i k, ‖matCLME (pruneMatrix (A j) (S j))‖)
              * (Real.sqrt (s i : ℝ) * θ i)
              * (∏ j in Finset.range i, ‖matCLME (A j)‖) * ‖x‖ := by
  intro x
  refine prune_chain_error A (fun i => pruneMatrix (A i) (S i))
    (fun i => Real.sqrt (s i : ℝ) * θ i) k ?_ x
  intro i hi
  exact prune_error_norm (A i) (S i) (s i) (θ i) (hS i hi) (hθ i hi) (hA i hi)

/-! ## 定理五（加分）：剪枝阈值的存在性 -/

/-- 阈值存在（θ = 被剪集上幅度的最大值）：被剪集 S 非空 ⟹ 存在 θ ≥ 0 使
所有被剪分量 |Aᵢⱼ| ≤ θ（剪枝"剪幅度最小"的诚实前提：阈值即被剪集内幅度上界；
免排序的 max 构造，替代"第 k+1 大幅度"的排序版本）。 -/
theorem prune_threshold_exists (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (hSne : S.Nonempty) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ p, p ∈ S → |A p.1 p.2| ≤ θ := by
  let T : Finset ℝ := S.image (fun p => |A p.1 p.2|)
  have hTne : T.Nonempty := by
    rcases hSne with ⟨p, hp⟩
    refine ⟨|A p.1 p.2|, ?_⟩
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  refine ⟨T.max' hTne, ?_, ?_⟩
  · have hmem : T.max' hTne ∈ T := Finset.max'_mem T hTne
    rcases Finset.mem_image.mp hmem with ⟨p, hp, hval⟩
    rw [← hval]
    exact abs_nonneg _
  · intro p hp
    exact Finset.le_max' T (|A p.1 p.2|) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- 阈值存在（top-k 衔接，θ = 保留集幅度最小值）：若保留集 K 逐点支配被剪集 S
（∀ p∈S, ∀ q∈K, |A p| ≤ |A q| —— 保留幅度 ≥ 被剪幅度的排序性质，top-k 保留的
honest 抽象），则存在 θ ≥ 0（θ = min_{q∈K}|A q|）界住全部被剪分量。
替代"θ = 第 k+1 大幅度"的排序证明（免排序，诚实等价）。 -/
theorem prune_threshold_from_kept (A : Matrix (Fin m) (Fin n) ℝ) (S K : Finset (Fin m × Fin n))
    (hKne : K.Nonempty)
    (hdom : ∀ p, p ∈ S → ∀ q, q ∈ K → |A p.1 p.2| ≤ |A q.1 q.2|) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ p, p ∈ S → |A p.1 p.2| ≤ θ := by
  let T : Finset ℝ := K.image (fun q => |A q.1 q.2|)
  have hTne : T.Nonempty := by
    rcases hKne with ⟨q, hq⟩
    refine ⟨|A q.1 q.2|, ?_⟩
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  refine ⟨T.min' hTne, ?_, ?_⟩
  · have hmem : T.min' hTne ∈ T := Finset.min'_mem T hTne
    rcases Finset.mem_image.mp hmem with ⟨q, hq, hval⟩
    rw [← hval]
    exact abs_nonneg _
  · intro p hp
    exact Finset.le_min' T hTne (|A p.1 p.2|) (by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨q, hq, heq⟩
      rw [← heq]
      exact hdom p hp q hq)

/-- 全局幅度界的直接实例化：若 |Aᵢⱼ| ≤ M 处处成立（M ≥ 0），则任意被剪集
S（|S| ≤ s）的剪枝误差 ≤ √s·M（阈值 M 的平凡存在形式）。 -/
theorem prune_threshold_global (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m × Fin n))
    (s : ℕ) (M : ℝ) (hS : S.card ≤ s) (hM0 : 0 ≤ M) (hM : ∀ i j, |A i j| ≤ M) :
    frobeniusNorm (pruneError A S) ≤ Real.sqrt (s : ℝ) * M := by
  exact prune_magnitude_bound A S s M hS hM0 (fun p hp => hM p.1 p.2)

/-! ## 注：实例化闭环
  单层剪枝误差 δ = √s·θ（`prune_error_norm`，由幅度阈值 θ 与被剪集大小 s
  给出）代入 `prune_chain_error` ⟹ n 层剪枝模型端到端前向误差（定理四）；
  这与 RealQuantizedError 的量化传播同构：剪枝 = 量化到零的特例
  （Wq = pruneMatrix A S ⟹ Wq − W = −pruneError A S），`quantized_chain_error_closed`
  的 δᵢ 处代入剪枝界即可。阈值存在性（定理五）保证"剪幅度最小"策略下
  hA 假设可满足（θ = 被剪集幅度最大值 / 保留集幅度最小值），衔接
  RealTopK 的 top-k 保留思想。与 RealMatrixNorm 的 Frobenius↔算子范数
  （`opNorm_le_frobenius`）及 Frobenius 逐点界（`frobenius_bound`）衔接：
  剪枝误差从 Frobenius 范数传播到算子范数、再到输出范数。-/

end Lattice
