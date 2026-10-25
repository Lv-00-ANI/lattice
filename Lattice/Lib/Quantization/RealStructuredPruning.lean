import Mathlib
import Lattice.Lib.LinearAlgebra.RealSparsity
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Quantization.RealQuantizedError
import Lattice.Lib.Quantization.RealCompressionJoint
/-!
# LATTICE: 结构化剪枝误差界 —— 通道/头/层的整组置零

RealSparsity 处理**非结构化**剪枝（逐分量置零：被剪集 `S : Finset (Fin m × Fin n)`，
界 `‖A − A'‖_F ≤ √s·θ`）。真实部署中更常见的是**结构化剪枝**：以「结构单元」
（输出通道 = 矩阵行、注意力头 = 参数块、层 = 整张矩阵）为单位整组置零，
被剪掉的不是 `s` 个分量，而是 `s` 个**单元**。

本文件把 RealSparsity 的界推广到结构化情形，并保持与非结构化版的一致性：

  1. `structuredSet`/`mem_structuredSet`：被剪单元对应的**分量集合**
     （`T.biUnion (fiber)`），成员判定 `p ∈ structuredSet grp T ↔ grp p ∈ T`；
  2. `structuredMask`/`structuredError`：整组置零的剪枝模型与误差矩阵
     （与 `pruneMatrix`/`pruneError` 在 `structuredSet` 上逐点一致，
     `structuredError_eq_pruneError`/`structuredMask_eq_pruneMatrix`）；
  3. `structuredSet_card_le`（核心计数）：`|structuredSet| ≤ |T|·g`
     ——被剪分量数 ≤ 被剪单元数 × 单元大小（`Finset.card_biUnion_le`）；
  4. `structured_pruning_error`（**核心**）：被剪单元数 `|T| ≤ s`、每单元大小
     `≤ g`、分量幅度 `|Aₚ| ≤ θ` ⟹ `‖A − A'‖_F ≤ √(s·g)·θ`
     ——RealSparsity 非结构化界 `√|S|·θ` 的推广（把 `|S|` 换成 `|T|·g`）；
  5. `structured_op_bound`/`structured_output_bound`：算子范数与逐点输出界
     （衔接 `opNorm_le_frobenius`/`frobenius_bound`）；
  6. `structured_vs_unstructured`：同一逐分量阈值 `θ` 下，结构化界 `√(s·g)·θ`
     不小于非结构化界 `√s·θ`（因数 `√g`）——结构化剪枝的单位更「粗」，
     但其**存储的结构索引数**是 `s`（非结构化需记 `s·g` 个分量坐标），
     这是压缩率与误差界的诚实权衡；
  7. `channel_pruning_bound`：通道剪枝 = 整行置零（`row_fiber_card_le`：
     行 fiber 恰有 `n` 个分量）⟹ `‖·‖_F ≤ √(s·n)·θ`；
  8. `head_pruning_bound`：注意力头剪枝 = 「头 × 头内参数」参数矩阵的行置零
     （行索引即头），同一界的实例化；
  9. `structured_chain_error`（加分）：把逐层 δᵢ = √(sᵢ·gᵢ)·θᵢ 代入
     RealQuantizedError 的 `quantized_chain_error_closed`，得 n 层结构化剪枝
     模型的端到端前向误差界。

诚实假设（全部显式标注）：剪枝分组 `grp : Fin m × Fin n → Fin G` 为给定映射
（分组方式由架构决定，本文件不构造它）；每单元大小上界 `g` 与阈值 `θ ≥ 0`
为显式假设；结构化剪枝在数学上**就是**非结构化剪枝作用在被剪单元的分量并集上
（`structuredError_eq_pruneError` 是定义级等式），因此并无新的范数假设——
所有界都从 RealSparsity/RealMatrixNorm/RealQuantizedError 既有结论推出。

模型无关：任意 m×n 维度与任意分组数 `G`；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

open Matrix

variable {m n : ℕ}

/-! ## 结构分组：被剪单元 → 分量集合 -/

/-- 被剪单元集合 `T` 对应的**分量集合**：`T` 中各单元 fiber 的并集。
`grp : Fin m × Fin n → Fin G` 把每个分量坐标映到它所属的结构单元。 -/
def structuredSet {G : ℕ} (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) :
    Finset (Fin m × Fin n) :=
  T.biUnion (fun t => (Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t))

/-- 成员判定：分量 `p` 属于被剪分量集 ⟺ 它所在的单元被剪
（`Finset.mem_biUnion` + `Finset.mem_filter`）。 -/
lemma mem_structuredSet {G : ℕ} (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G))
    (p : Fin m × Fin n) : p ∈ structuredSet grp T ↔ grp p ∈ T := by
  unfold structuredSet
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨t, _ht, hp⟩
    rw [Finset.mem_filter] at hp
    rwa [hp.2]
  · intro h
    exact ⟨grp p, h, Finset.mem_filter.mpr ⟨Finset.mem_univ p, rfl⟩⟩

/-! ## 结构化剪枝模型与误差矩阵 -/

/-- 结构化剪枝模型 A'：被剪单元 `T`（`Finset (Fin G)`）上的分量整组置 0，
其余单元保持 A 不变。 -/
def structuredMask {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if grp (i, j) ∈ T then 0 else A i j

/-- 结构化剪枝误差矩阵 B = A − A'：仅在被剪单元的分量上非零（值 = A 的分量）。 -/
def structuredError {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if grp (i, j) ∈ T then A i j else 0

/-- 结构化误差 = 非结构化误差（在单元并集 `structuredSet` 上）：
结构化剪枝就是 RealSparsity 的非结构化剪枝作用在被剪单元的分量并集上。 -/
lemma structuredError_eq_pruneError {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) :
    structuredError A grp T = pruneError A (structuredSet grp T) := by
  ext i j
  by_cases h : (i, j) ∈ structuredSet grp T
  · have hT : grp (i, j) ∈ T := (mem_structuredSet grp T (i, j)).mp h
    simp [structuredError, pruneError, hT, h]
  · have hT : grp (i, j) ∉ T := fun hc => h ((mem_structuredSet grp T (i, j)).mpr hc)
    simp [structuredError, pruneError, hT, h]

/-- 结构化剪枝模型 = 非结构化剪枝模型（在单元并集上）。 -/
lemma structuredMask_eq_pruneMatrix {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) :
    structuredMask A grp T = pruneMatrix A (structuredSet grp T) := by
  ext i j
  by_cases h : (i, j) ∈ structuredSet grp T
  · have hT : grp (i, j) ∈ T := (mem_structuredSet grp T (i, j)).mp h
    simp [structuredMask, pruneMatrix, hT, h]
  · have hT : grp (i, j) ∉ T := fun hc => h ((mem_structuredSet grp T (i, j)).mpr hc)
    simp [structuredMask, pruneMatrix, hT, h]

/-- 被保留单元上的分量逐点不变（剪枝只影响被剪单元）。 -/
lemma structured_zero_keep {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) :
    ∀ i j, grp (i, j) ∉ T → structuredMask A grp T i j = A i j := by
  intro i j hij
  simp [structuredMask, hij]

/-! ## 计数引理：被剪分量数 ≤ 被剪单元数 × 单元大小 -/

/-- **核心计数引理**：被剪单元数 `|T|`、每单元大小 `≤ g` ⟹
被剪分量数 `|structuredSet grp T| ≤ |T|·g`
（`Finset.card_biUnion_le`：并集基数 ≤ 各 fiber 基数之和 ≤ `|T|·g`）。 -/
lemma structuredSet_card_le {G : ℕ} (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G))
    (g : ℕ)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g) :
    (structuredSet grp T).card ≤ T.card * g := by
  unfold structuredSet
  calc
    (T.biUnion (fun t => (Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t))).card
        ≤ ∑ t in T,
            ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _t in T, g := Finset.sum_le_sum (fun t ht => hg t ht)
    _ = T.card * g := by
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

/-! ## 定理一（核心）：结构化剪枝的 Frobenius 误差界 -/

/-- **核心结构化剪枝误差界**（RealSparsity `prune_magnitude_bound` 的结构化推广）：
被剪单元数 `|T| ≤ s`、每单元大小 `≤ g`、被剪分量幅度 `|Aₚ| ≤ θ`（`θ ≥ 0`）⟹
Frobenius 误差 `‖A − A'‖_F ≤ √(s·g)·θ`。
证明路线：结构化误差 = 单元并集上的非结构化误差
（`structuredError_eq_pruneError`），并集基数 `≤ s·g`
（`structuredSet_card_le` + `Nat.mul_le_mul_right`），代入 `prune_magnitude_bound`。 -/
theorem structured_pruning_error {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) (s g : ℕ) (θ : ℝ)
    (hT : T.card ≤ s)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g)
    (hθ : 0 ≤ θ) (hA : ∀ p, grp p ∈ T → |A p.1 p.2| ≤ θ) :
    frobeniusNorm (structuredError A grp T) ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ := by
  rw [structuredError_eq_pruneError]
  refine prune_magnitude_bound A (structuredSet grp T) (s * g) θ ?_ hθ ?_
  · calc
      (structuredSet grp T).card ≤ T.card * g := structuredSet_card_le grp T g hg
      _ ≤ s * g := Nat.mul_le_mul_right g hT
  · intro p hp
    exact hA p ((mem_structuredSet grp T p).mp hp)

/-- 直接形式（模型差）：`‖A − A'‖_F ≤ √(s·g)·θ`。 -/
theorem structured_frobenius_error {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) (s g : ℕ) (θ : ℝ)
    (hT : T.card ≤ s)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g)
    (hθ : 0 ≤ θ) (hA : ∀ p, grp p ∈ T → |A p.1 p.2| ≤ θ) :
    frobeniusNorm (A - structuredMask A grp T) ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ := by
  have hsub : A - structuredMask A grp T = structuredError A grp T := by
    rw [structuredError_eq_pruneError]
    have h := prune_sub_eq_error A (structuredSet grp T)
    rwa [← structuredMask_eq_pruneMatrix A grp T] at h
  rw [hsub]
  exact structured_pruning_error A grp T s g θ hT hg hθ hA

/-! ## 定理二：算子范数与逐点输出界 -/

/-- 结构化剪枝的算子范数界：`‖matCLME (structuredError …)‖ ≤ √(s·g)·θ`
（`opNorm_le_frobenius` + 定理一）。 -/
theorem structured_op_bound {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) (s g : ℕ) (θ : ℝ)
    (hT : T.card ≤ s)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g)
    (hθ : 0 ≤ θ) (hA : ∀ p, grp p ∈ T → |A p.1 p.2| ≤ θ) :
    ‖matCLME (structuredError A grp T)‖ ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ :=
  le_trans (opNorm_le_frobenius (structuredError A grp T))
    (structured_pruning_error A grp T s g θ hT hg hθ hA)

/-- 结构化剪枝的逐点输出界：`‖(A − A')x‖ ≤ √(s·g)·θ·‖x‖`
（`frobenius_bound` + 定理一）。 -/
theorem structured_output_bound {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) (s g : ℕ) (θ : ℝ)
    (hT : T.card ≤ s)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g)
    (hθ : 0 ≤ θ) (hA : ∀ p, grp p ∈ T → |A p.1 p.2| ≤ θ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖matvecE (structuredError A grp T) x‖ ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ * ‖x‖ := by
  calc
    ‖matvecE (structuredError A grp T) x‖
        ≤ frobeniusNorm (structuredError A grp T) * ‖x‖ := frobenius_bound _ x
    _ ≤ (Real.sqrt ((s * g : ℕ) : ℝ) * θ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (structured_pruning_error A grp T s g θ hT hg hθ hA)
        (norm_nonneg x)

/-- 结构化剪枝的算子级误差（模型差）：`‖matCLME A' − matCLME A‖ ≤ √(s·g)·θ`。 -/
lemma structured_error_norm {G : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (grp : Fin m × Fin n → Fin G) (T : Finset (Fin G)) (s g : ℕ) (θ : ℝ)
    (hT : T.card ≤ s)
    (hg : ∀ t ∈ T,
      ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => grp p = t)).card ≤ g)
    (hθ : 0 ≤ θ) (hA : ∀ p, grp p ∈ T → |A p.1 p.2| ≤ θ) :
    ‖matCLME (structuredMask A grp T) - matCLME A‖ ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ := by
  calc
    ‖matCLME (structuredMask A grp T) - matCLME A‖
        = ‖matCLME (structuredMask A grp T - A)‖ := by rw [matCLME_sub]
    _ = ‖matCLME (-structuredError A grp T)‖ := by
      have h : structuredMask A grp T - A = -structuredError A grp T := by
        rw [structuredMask_eq_pruneMatrix A grp T, structuredError_eq_pruneError]
        exact pruneMatrix_sub_eq_neg A (structuredSet grp T)
      rw [h]
    _ = ‖matCLME (structuredError A grp T)‖ := by rw [matCLME_neg, norm_neg]
    _ ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ :=
      structured_op_bound A grp T s g θ hT hg hθ hA

/-! ## 定理三：结构化 vs 非结构化（同阈值下的界对比） -/

/-- **结构化 vs 非结构化**：同一逐分量阈值 `θ ≥ 0` 下，单元大小 `g ≥ 1` 时
`√(s·g)·θ ≥ √s·θ`——结构化剪枝的单位更粗（一个单元含 `g` 个分量），
在「被剪单元数 ≤ s」的同一预算下，Frobenius 误差界大 `√g` 倍。
诚实的交换：结构化剪枝只需记录 `s` 个结构索引（非结构化需 `s·g` 个分量坐标），
压缩率更高而误差界更松。 -/
theorem structured_vs_unstructured (s g : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hg : 1 ≤ g) :
    Real.sqrt (s : ℝ) * θ ≤ Real.sqrt ((s * g : ℕ) : ℝ) * θ := by
  have hsg : s ≤ s * g := by
    have h : s * 1 ≤ s * g := Nat.mul_le_mul_left s hg
    simpa using h
  have hcast : (s : ℝ) ≤ ((s * g : ℕ) : ℝ) := by exact_mod_cast hsg
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcast) hθ

/-- 界对比的等价读法：结构化界 = 非结构化界 × `√g`（`g ≥ 1`、`θ ≥ 0`）。 -/
theorem structured_unstructured_ratio (s g : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hg : 1 ≤ g) :
    Real.sqrt (s : ℝ) * θ ≤ Real.sqrt (g : ℝ) * (Real.sqrt (s : ℝ) * θ) := by
  have h1 : (1 : ℝ) ≤ Real.sqrt (g : ℝ) := by
    have hg' : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    have h := Real.sqrt_le_sqrt hg'
    simpa using h
  have hs : 0 ≤ Real.sqrt (s : ℝ) * θ := mul_nonneg (Real.sqrt_nonneg _) hθ
  calc
    Real.sqrt (s : ℝ) * θ ≤ 1 * (Real.sqrt (s : ℝ) * θ) := by rw [one_mul]
    _ ≤ Real.sqrt (g : ℝ) * (Real.sqrt (s : ℝ) * θ) := mul_le_mul_of_nonneg_right h1 hs

/-! ## 定理四：通道剪枝（整行置零） -/

/-- 通道剪枝模型：输出通道集合 `R`（矩阵的**行**）整行置 0。 -/
def channelMask (A : Matrix (Fin m) (Fin n) ℝ) (R : Finset (Fin m)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i ∈ R then 0 else A i j

/-- 通道剪枝误差矩阵：`R` 所在行取 A 的分量，其余为 0。 -/
def channelError (A : Matrix (Fin m) (Fin n) ℝ) (R : Finset (Fin m)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i ∈ R then A i j else 0

/-- 通道剪枝 = 以「行索引」为结构单元的结构化剪枝。 -/
lemma channelError_eq_structured (A : Matrix (Fin m) (Fin n) ℝ) (R : Finset (Fin m)) :
    channelError A R = structuredError A (fun p : Fin m × Fin n => p.1) R := rfl

/-- 行 fiber 恰有 `n` 个分量：`{p | p.1 = t}` 与 `Fin n` 等势（`p ↦ p.2` 单射）。 -/
lemma row_fiber_card_le (t : Fin m) :
    ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => p.1 = t)).card ≤ n := by
  have hsub : (Finset.univ : Finset (Fin m × Fin n)).filter (fun p => p.1 = t)
      ⊆ (Finset.univ : Finset (Fin n)).image (fun j => (t, j)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ p.2, Prod.ext hp.2.symm rfl⟩
  calc
    ((Finset.univ : Finset (Fin m × Fin n)).filter (fun p => p.1 = t)).card
        ≤ ((Finset.univ : Finset (Fin n)).image (fun j => (t, j))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- **通道剪枝误差界**：被剪行数 `|R| ≤ s`、被剪分量幅度 `|Aᵢⱼ| ≤ θ`（`θ ≥ 0`）⟹
`‖A − A'‖_F ≤ √(s·n)·θ`（通道剪枝 = 行结构化剪枝，单元大小 = 列数 `n`）。 -/
theorem channel_pruning_bound (A : Matrix (Fin m) (Fin n) ℝ) (R : Finset (Fin m))
    (s : ℕ) (θ : ℝ) (hR : R.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ i j, i ∈ R → |A i j| ≤ θ) :
    frobeniusNorm (channelError A R) ≤ Real.sqrt ((s * n : ℕ) : ℝ) * θ := by
  rw [channelError_eq_structured]
  refine structured_pruning_error A (fun p : Fin m × Fin n => p.1) R s n θ hR ?_ hθ ?_
  · intro t _ht
    exact row_fiber_card_le t
  · intro p hp
    exact hA p.1 p.2 hp

/-- 通道剪枝的算子范数界：`‖matCLME (channelError A R)‖ ≤ √(s·n)·θ`。 -/
theorem channel_op_bound (A : Matrix (Fin m) (Fin n) ℝ) (R : Finset (Fin m))
    (s : ℕ) (θ : ℝ) (hR : R.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ i j, i ∈ R → |A i j| ≤ θ) :
    ‖matCLME (channelError A R)‖ ≤ Real.sqrt ((s * n : ℕ) : ℝ) * θ :=
  le_trans (opNorm_le_frobenius (channelError A R))
    (channel_pruning_bound A R s θ hR hθ hA)

/-! ## 定理五：注意力头剪枝（头 × 头内参数 的参数矩阵，行 = 头） -/

variable {h d : ℕ}

/-- **注意力头剪枝误差界**：把多头注意力的参数建模为
`Matrix (Fin h) (Fin d) ℝ`（**行 = 头**，列 = 头内参数，`h` 个头、每头 `d` 个参数），
剪掉 `|R| ≤ s` 个头 ⟹ `‖A − A'‖_F ≤ √(s·d)·θ`。
诚实标注：真实 Q/K/V/O 的单头参数是一个 **块**（多张矩阵按头切片后再拼接）；
这里把「头块」压平成一行来建模，正是 `channel_pruning_bound` 在 `m := h`、`n := d`
上的实例化——头剪枝与通道剪枝在「整行置零」这一数学结构上完全一致。 -/
theorem head_pruning_bound (A : Matrix (Fin h) (Fin d) ℝ) (R : Finset (Fin h))
    (s : ℕ) (θ : ℝ) (hR : R.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ i j, i ∈ R → |A i j| ≤ θ) :
    frobeniusNorm (channelError A R) ≤ Real.sqrt ((s * d : ℕ) : ℝ) * θ :=
  channel_pruning_bound A R s θ hR hθ hA

/-- 头剪枝的算子范数界：`‖matCLME (channelError A R)‖ ≤ √(s·d)·θ`。 -/
theorem head_op_bound (A : Matrix (Fin h) (Fin d) ℝ) (R : Finset (Fin h))
    (s : ℕ) (θ : ℝ) (hR : R.card ≤ s) (hθ : 0 ≤ θ)
    (hA : ∀ i j, i ∈ R → |A i j| ≤ θ) :
    ‖matCLME (channelError A R)‖ ≤ Real.sqrt ((s * d : ℕ) : ℝ) * θ :=
  channel_op_bound A R s θ hR hθ hA

/-! ## 定理六（加分）：n 层结构化剪枝模型的端到端误差 -/

/-- **n 层结构化剪枝端到端误差**：每层被剪单元数 `|T i| ≤ s i`、单元大小
`≤ g i`、被剪分量幅度 `≤ θ i`（`θ i ≥ 0`）⟹ 前向误差
`≤ Σ_{i<k} (∏后层范数)·(√(s i·g i)·θ i)·(∏前层范数)·‖x‖`
（逐层 δᵢ 由 `structured_error_norm` 给出，代入
RealQuantizedError `quantized_chain_error_closed`）。 -/
theorem structured_chain_error {G : ℕ} (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (grp : ℕ → Fin n × Fin n → Fin G) (T : ℕ → Finset (Fin G))
    (s g : ℕ → ℕ) (θ : ℕ → ℝ) (k : ℕ)
    (hT : ∀ i, i < k → (T i).card ≤ s i)
    (hg : ∀ i, i < k → ∀ t ∈ T i,
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => grp i p = t)).card ≤ g i)
    (hθ : ∀ i, i < k → 0 ≤ θ i)
    (hA : ∀ i, i < k → ∀ p, grp i p ∈ T i → |A i p.1 p.2| ≤ θ i) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖quantFwd (fun i => matCLME (structuredMask (A i) (grp i) (T i))) k x
        - quantFwd (fun i => matCLME (A i)) k x‖
        ≤ ∑ i in Finset.range k,
            (∏ j in Finset.Ioo i k, ‖matCLME (structuredMask (A j) (grp j) (T j))‖)
              * (Real.sqrt ((s i * g i : ℕ) : ℝ) * θ i)
              * (∏ j in Finset.range i, ‖matCLME (A j)‖) * ‖x‖ := by
  intro x
  refine prune_chain_error A (fun i => structuredMask (A i) (grp i) (T i))
    (fun i => Real.sqrt ((s i * g i : ℕ) : ℝ) * θ i) k ?_ x
  intro i hi
  exact structured_error_norm (A i) (grp i) (T i) (s i) (g i) (θ i)
    (hT i hi) (hg i hi) (hθ i hi) (hA i hi)

/-! ## 注：实例化闭环与诚实边界
  结构化剪枝在数学上 **就是** 非结构化剪枝作用于「被剪单元的分量并集」
  （`structuredError_eq_pruneError` 是定义级等式），所以本文件不引入新假设：
  · 定理一 = `RealSparsity.prune_magnitude_bound` + `structuredSet_card_le`（计数）；
  · 定理二 = RealMatrixNorm 的 `opNorm_le_frobenius`/`frobenius_bound`；
  · 定理六 = RealQuantizedError 的 `prune_chain_error`（其闭式求和）。
  结构化剪枝的**真实代价**在界里可见：同一「单元数预算 s」下，误差界从 `√s·θ`
  膨胀到 `√(s·g)·θ`（定理三），而收益是可存储的索引数从 `s·g` 降到 `s`。
  通道/头/层三种结构分别是 `grp p = p.1`（行）、头参数矩阵的行、以及
  常值分组 `grp p = 0`（整张矩阵为一个单元）的实例——层剪枝即 `T = {0}`
  且 `g = m·n` 的极端情形（界 `≤ √(m·n)·θ`，与 `prune_threshold_global` 一致）。
  与 RealCompressionJoint 衔接：逐层 δᵢ 可直接进入 `jointDelta`，与量化/蒸馏
  误差预算求和后走同一条链式传播。无 sorry/axiom/admit。 -/

end Lattice
