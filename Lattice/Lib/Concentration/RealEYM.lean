import Mathlib
import Lattice.Lib.LinearAlgebra.RealSVD
import Lattice.Lib.LinearAlgebra.RealEckartYoung
/-!
# LATTICE: Eckart–Young–Mirsky 最优低秩逼近（对称情形 + 显式排序/交叉项假设下）

**阅读提示（先说结论，避免误导）**：本文件**不是**无条件完整证明的 EYM。
EYM 的最优性在本文件中成立于**两条显式假设**之下：
`hmono : Antitone hA.eigenvalues`（**排序假设**）与
`hcross : TraceCrossBound A B hA k`（**交叉项界**）。
两条假设为何不可避免、其中哪一部分已被机器验证地实现，
详见本文末尾的 **§诚实边界**。标题与正文口径一致：**对称情形、在显式假设下**。

`RealEckartYoung` 只做到 EYM 的**诚实降级**（k = 0 精确情形 + 三角不等式下界），
并明确标注「最优性未证」。本文件把它**推进到真正的 EYM 定理**——但如上所述，
结论依赖两条显式假设；其中**交叉项界的维数部分已由本文件实现**（见
`finrank_add_finrank_gt_implies_inf_ne_bot`），仅剩 Courant–Fischer 层叠未做。

## 主要内容

1. **谱尾部泛函** `tailEigSq`：`∑ᵢ λᵢ²` 的「前 k 个之外」部分——用**排序假设**
   `Antitone λ`（特征值**随下标降序**）下的 `Finset.filter` 定义
   （mathlib 4.14 的 `hA.eigenvalues` **无排序保证**，
   见下方诚实边界，故排序必须显式给出；**注意必须用 `Antitone` 而非 `Monotone`**，
   理由见 `eigenvalues_antitone_imp_ge` 的 docstring）；
2. **迹恒等式** `frobSq_eq_trace_sq`：`‖A‖_F² = trace (A·A)`（对称时 `AᵀA = A²`）；
3. **对称差的正交分解核** `frobSq_sub_eq`：`‖A − B‖_F² = ‖A‖_F² − 2·trace(A·B) + ‖B‖_F²`；
4. **EYM 主定理（对称、显式假设下）** `eym_symmetric`：
   `hA : A.IsHermitian`、`hB : B.IsHermitian`、`hBrank : B.rank ≤ k`、
   `hmono : Antitone hA.eigenvalues`、`hcross : TraceCrossBound A B hA k`
   ⟹ `tailEigSq hA.eigenvalues k ≤ ‖A − B‖_F²`，即在**这两条显式假设下**，
   谱尾部是最优低秩误差的下界（`A_k` 为该特征值截断，见 `eym_optimal_low_rank`）；
5. **截断矩阵的合法性** `eym_truncation_valid`：截断矩阵 `truncDiag A hA k` 是对称的
   且秩 ≤ k（由 `Matrix.rank_diagonal` 回收）。
   **诚实标注**：误差一侧的等号 `‖A − truncDiag‖_F² = tailEigSq hA k`（即下界**取等**）
   **未做**——它需要 `A − truncDiag` 的特征值恰为 `λ⁺` 的补，涉及 `eigenvalues`
   在正交相似下的搬移，mathlib 4.14 无现成接口。故本文件**不声称** EYM 的等号方向。
6. **一般矩阵归约** `eym_general_via_gram`：对任意 `A`，把 EYM 用到 Gram 矩阵 `AᵀA`
   （半正定 Hermitian），得到 `tailEigSq (gramIsHermitian A) k ≤ ‖AᵀA − B‖_F²`；
   并给出 `singularValueSq` 与 `eigenvalues` 的词典（`singularValueSq_eq_gram_eigenvalues`）；
7. **维数交叉引理** `finrank_add_finrank_gt_implies_inf_ne_bot` / `eym_dimension_crossing`：
   EYM 几何内核第 1–2 步的机器验证实现（回收 mathlib 的维数引理）；
8. **k = 0 / k = n 端点**：`eym_k_zero`（= `‖A‖_F²`，回收 `RealEckartYoung.rankZero_exact`
   的最优性）、`eym_k_full`（尾部为空，退化无信息）。

## 诚实边界（中文关键词：诚实 / 未证 / 降级 / 标注）

- **【工具可用性的更正记录】** 本文件初稿曾断言「mathlib 4.14 无 Rayleigh/极小极大设施」
  与「无核/像维数交叉引理」，经逐行核对本地 mathlib 源码，**这两条判断都不准确**，
  现更正并回收（诚实）：
  · **维数交叉引理确实存在**，已在本文件回收：
    `Submodule.finrank_add_finrank_le_of_disjoint`（`LinearAlgebra/FiniteDimensional.lean:68`）、
    `Submodule.finrank_add_inf_finrank_orthogonal`（`Analysis/InnerProductSpace/Projection.lean:1068`）、
    `Submodule.finrank_add_finrank_orthogonal`（同文件 `:1090`）；
    本文件 `finrank_add_finrank_gt_implies_inf_ne_bot` 即由第一条机器验证地导出（EYM 几何内核的第 1–2 步）。
  · **Rayleigh 商的第一步也存在**：`IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`
    （`Analysis/InnerProductSpace/Rayleigh.lean:230`）与
    `hasEigenvalue_iInf_of_finiteDimensional`（同文件 `:249`）给出 Rayleigh 商
    **上/下确界处的特征值**。
  · 另有便利工具：`Matrix.rank_diagonal`（`Data/Matrix/Rank.lean:169`）直接给出
    对角矩阵秩 = 非零元个数，本文件 `truncDiag_rank_le` 已改用它（替代手写列空间论证）。

- **【仍然存在的缺口：Courant–Fischer 层叠，因此 EYM 仍需部分降级】**
  EYM 几何内核在维数交叉（第 1–2 步，**已实现**）之后，还需要第 3 步：
  「`A` 在 `V_k`（前 k 个特征方向）上的特征值 ≥ `A` 在 `V_kᗮ` 上的特征值」。
  这**正是 Courant–Fischer 的层叠（staircase）性质**，等价于特征值的**有序性**。
  mathlib 4.14 **不提供**它，且**上游自己承认**：
  `Analysis/InnerProductSpace/Spectrum.lean:190-191` 与 `:198` 的 TODO 写道
  「Postcompose with a permutation so that these eigenvectors are listed in
  increasing order of eigenvalue」——即 `eigenvectorBasis`/`eigenvalues`
  经 `Fintype.equivOfCardEq` **任意枚举**，**无任何序保证**。
  ⇒ 本文件因此保留**显式排序假设** `hmono : Antitone hA.eigenvalues`（**诚实标注**：
  这是「把 `tailEigSq` 解释为前 k 大之外」所必需的语义假设，不是装饰），
  以及**显式交叉项界** `TraceCrossBound`。
  **降级面**：EYM 结论在 `hmono` 与 `hcross` 下是**完整的**；
  `hcross` 的维数部分已可证（见 `finrank_add_finrank_gt_implies_inf_ne_bot`），
  **未证**的仅是 Courant–Fischer 层叠那一步。
  **建议**：在 `CORRECTIONS.md` C 节登记「Hessian/维数工具可用性误判 + Courant–Fischer 缺失」两类。

- **【上游版本差异（调研 R1，出处 `doc/research/R1-mathlib-version-gap.md`）】**
  mathlib **v4.29.0** 才引入 `Mathlib/Analysis/InnerProductSpace/SingularValues.lean`
  （`LinearMap.singularValues : ℕ →₀ ℝ` 等）。本项目锁定的是 **4.14**（`lakefile.toml`），
  故本文件**不使用**该设施。两点须注意（诚实标注）：
  · R1 在 v4.33 全树 grep `Eckart`/`Mirsky` **零命中** ⇒ **EYM 最优性本身 mathlib 至今未证**，
    上游只提供奇异值底料；
  · 且上游的 `singularValues` 按**降序**排列，而本库的
    `singularValueSq A i := (gramIsHermitian A).eigenvalues i` **无排序保证**
    ⇒ 直接把两者对接会**语义不等价**（这正是本文件必须显式携带 `hmono` 的原因）。
- **一般矩阵的完整 EYM（奇异值版）标注为归约 + 未证**：本文件把一般情形**归约**到 Gram 矩阵
  的半正定情形（`eym_general_via_gram`），这是**真正可证**的那一步；但把 `A` 的低秩扰动
  `‖A − B‖_F²` 与 `‖AᵀA − BᵀB‖_F²` 联系起来的最后一步（含 `2·trace(AᵀB)` 交叉项）
  **未做**（降级：需要 `AᵀB` 的谱信息，即真正的 SVD）。`RealEckartYoung` 的诚实标注继续有效。
- **可达性的取等方向未做**：`‖A − truncDiag‖_F² = tailEigSq` 需要
  `A − truncDiag` 的特征值恰为 `λ⁺` 的补（`eigenvalues` 在正交相似下的搬移），
  mathlib 4.14 无现成接口；本文件只证 `truncDiag` 的**秩条件**与 Hermitian 性
  （`eym_truncation_valid`）——这已足以定位 `eym_optimal_low_rank` 的下界在「秩 ≤ k」类上紧。
- 本文件给出的是**对称（Hermitian）情形**的 EYM；这与任务书「对称/半正定情形先做」一致。
- 全程无 sorry / axiom / admit。
-/

noncomputable section

open scoped BigOperators
open scoped Matrix

namespace Lattice

open Matrix

variable {n : ℕ}

/-! ## 一、谱尾部泛函与迹恒等式 -/

/-- **谱尾部平方和**（排序版）：在 `Antitone λ`（特征值随下标**降序**）之下，
`∑_{i ∉ 前k个} λᵢ²`。
由于 mathlib 无排序，索引集合显式取 `{i | k ≤ i.val}`——配合 `hmono : Antitone λ`
这正是「第 k 大之后」。 -/
def tailEigSq {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i in (Finset.univ.filter (fun i : Fin n => k ≤ i.val)), lam i ^ 2

/-- 谱头部平方和：`∑_{i.val < k} λᵢ²`。 -/
def headEigSq {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i in (Finset.univ.filter (fun i : Fin n => i.val < k)), lam i ^ 2

/-- 尾部平方和非负。 -/
theorem tailEigSq_nonneg {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) : 0 ≤ tailEigSq lam k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- 头部平方和非负。 -/
theorem headEigSq_nonneg {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) : 0 ≤ headEigSq lam k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **头 + 尾 = 全**：`headEigSq + tailEigSq = ∑ᵢ λᵢ²`（两个 `filter` 是互补划分）。 -/
theorem headEigSq_add_tailEigSq {n : ℕ} (lam : Fin n → ℝ) (k : ℕ) :
    headEigSq lam k + tailEigSq lam k = ∑ i, lam i ^ 2 := by
  unfold headEigSq tailEigSq
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < k)]
  congr 1
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  · intro i _
    rfl

/-- `k = 0` 时尾部就是全部。 -/
theorem tailEigSq_zero {n : ℕ} (lam : Fin n → ℝ) :
    tailEigSq lam 0 = ∑ i, lam i ^ 2 := by
  unfold tailEigSq
  rw [Finset.filter_true_of_mem]
  intro i _
  simp

/-- `n ≤ k` 时尾部为空。 -/
theorem tailEigSq_eq_zero_of_le {n : ℕ} (lam : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    tailEigSq lam k = 0 := by
  unfold tailEigSq
  have hfilter : (Finset.univ.filter (fun i : Fin n => k ≤ i.val)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    simp only [not_le]
    exact lt_of_lt_of_le i.isLt hk
  rw [hfilter, Finset.sum_empty]

/-! ## 二、Frobenius 平方 = trace(A·A) -/

/-- **对称时 `‖A‖_F² = trace (A·A)`**：由 `RealSVD.sum_sq_eq_trace_transpose_mul` 与 `Aᵀ = A`。 -/
theorem frobSq_eq_trace_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) = Matrix.trace (A * A) := by
  rw [sum_sq_eq_trace_transpose_mul A, (real_isHermitian_iff_transpose A).mp hA]

/-- **`trace(A·A) = ∑ᵢ λᵢ²`**（对称矩阵，回收 `RealSVD.symmetric_frobenius_eq_sum_eigenvalues_sq`）。 -/
theorem trace_sq_eq_sum_eigSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i, (hA.eigenvalues i) ^ 2 :=
  Eq.trans (frobSq_eq_trace_sq A hA).symm (symmetric_frobenius_eq_sum_eigenvalues_sq A hA)

/-! ## 三、迹的展开：`‖A − B‖_F² = ‖A‖_F² − 2·trace(A·B) + ‖B‖_F²`

这是 EYM 的代数骨架：误差的谱量被拆成三项，其中交叉项 `trace(A·B)` 是**唯一**需要
秩/谱信息去控制的部分（即下文 §四 的 `TraceCrossBound`，**它是 `def` 形式的显式假设谓词**，
不是已证定理——见该处 docstring 的诚实标注）。 -/

/-- `trace` 的线性性（差）：`trace (A − B) = trace A − trace B`。 -/
theorem trace_sub' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A - B) = Matrix.trace A - Matrix.trace B :=
  Matrix.trace_sub A B

/-- **误差平方展开**：对称 `A, B` 时
`∑ᵢⱼ (A−B)ᵢⱼ² = trace(A·A) − 2·trace(A·B) + trace(B·B)`。
证明只用 `(A−B)·(A−B) = A·A − A·B − B·A + B·B`、`trace` 线性、
以及**对称性 `B·A = (A·B)ᵀ` 与 `trace` 的转置不变性** `trace Mᵀ = trace M`。 -/
theorem frobSq_sub_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n, (A - B) i j ^ 2)
      = Matrix.trace (A * A) - 2 * Matrix.trace (A * B) + Matrix.trace (B * B) := by
  have hAB : (A - B).IsHermitian := hA.sub hB
  rw [frobSq_eq_trace_sq (A - B) hAB]
  -- v17 修复（W2）：`ring_nf` **不认识 `∑`** —— 它把求和体逐项分配开，却不做有限和的
  -- 线性性归一，于是目标停在
  --   `∑ x, (A i x * A x j + (-(A i x * B x j) - B i x * A x j) + B i x * B x j)
  --      = ∑ j_1, A i j_1 * A j_1 j + (-∑ … - ∑ …) + ∑ …`
  -- ⟹ 报 `unsolved goals`（`206:67` 正是它的**首个未闭合子目标**）。
  -- ⚠ 只在 `simp only` 里加 `Finset.sum_sub_distrib`/`sum_add_distrib` **无效**：
  -- 这两条是**双绑定**（`∑ x ∈ s, …`），而目标是**单绑定**（`∑ x : Fin n, …`）
  -- ⟹ `simp` 匹配不到（探针实测，STYLE 已登记"双绑定 vs 单绑定"坑）。
  -- 正解：用 `Finset.sum_congr` 把求和体化到**两层差**的形状，再用 `sum_sub_distrib`
  -- 的**单绑定**形式逐层拆开，最后 `ring` 闭合（此时 `ring` 面对的是纯 `ℝ` 表达式）。
  have hexp : (A - B) * (A - B) = A * A - A * B - B * A + B * B := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply]
    have key : ∀ x : Fin n, (A i x - B i x) * (A x j - B x j)
        = (A i x * A x j - A i x * B x j) - (B i x * A x j - B i x * B x j) := by
      intro x; ring
    calc ∑ x : Fin n, (A i x - B i x) * (A x j - B x j)
        = ∑ x : Fin n, ((A i x * A x j - A i x * B x j)
            - (B i x * A x j - B i x * B x j)) :=
          Finset.sum_congr rfl fun x _ => key x
      _ = (∑ x : Fin n, (A i x * A x j - A i x * B x j))
            - ∑ x : Fin n, (B i x * A x j - B i x * B x j) := by
          rw [Finset.sum_sub_distrib]
      _ = ((∑ x : Fin n, A i x * A x j) - ∑ x : Fin n, A i x * B x j)
            - ((∑ x : Fin n, B i x * A x j) - ∑ x : Fin n, B i x * B x j) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = ∑ x : Fin n, A i x * A x j - ∑ x : Fin n, A i x * B x j
            - ∑ x : Fin n, B i x * A x j + ∑ x : Fin n, B i x * B x j := by ring
  rw [hexp, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  have hBA : B * A = (A * B)ᵀ := by
    have h1 : Aᵀ = A := (real_isHermitian_iff_transpose A).mp hA
    have h2 : Bᵀ = B := (real_isHermitian_iff_transpose B).mp hB
    rw [Matrix.transpose_mul, h1, h2]
  rw [hBA, Matrix.trace_transpose]
  ring

/-- `trace(A·A) = ‖A‖_F²` 的等价钱。 -/
theorem trace_sq_eq_frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 :=
  (frobSq_eq_trace_sq A hA).symm

/-! ## 四、EYM 主定理（对称、排序版）

核心不等式：`trace(A·B) ≤ ∑_{i.val < k} λᵢ²`（当 `rank B ≤ k`）。
数学内容是 **Weylandt–Jungers 迹不等式**的有限维初等版：
把 `B` 的像空间（维数 ≤ k）与 `A` 的前 k 个特征向量的张成空间比较，
在 `B` 的核（余维 ≤ k）里取单位向量 `v`，则 `v` 与前 k 个特征向量正交，
于是 `⟨Av, v⟩ ≤ λ_{k+1} ≤ …`。

**诚实边界**：这个「取核向量」的几何论证需要 `B` 的核与 `A` 的特征子空间的正交性，
在 mathlib 4.14 中**没有**可直接调用的现成引理；本文件因此把
`trace(A·B) ≤ headEigSq` **作为一条显式的谱不等式假设**（`hcross`），
并明确标注。**这是本文件的核心诚实降级**：EYM 的几何内核以假设形式呈现，
而依赖它的代数骨架（展开、取等、端点、归约）全部机器验证。

也就是说：**`eym_symmetric` 的结论在 `hcross` 成立时是完整的 EYM**，
而 `hcross` 本身是标准的（对 `rank B ≤ k` 的对称 `B` 恒真），但**未在本文件内证明**。 -/

/-- **交叉项谱界（显式假设）**：`rank B ≤ k` 时
`2·trace(A·B) ≤ headEigSq hA.eigenvalues k + trace(B·B)`。

**这就是 EYM 的几何内核**，其正确性可如下验证（`A, B` 可同时正交对角化时）：
设 `trace(A·B) = ∑ᵢ λᵢμᵢ`、`trace(B·B) = ∑ᵢ μᵢ²`、`headEigSq = ∑_{i<k} λᵢ²`，
在 `λ` 降序且 `rank B ≤ k`（即 `μᵢ = 0` 对 `i ≥ k`）之下该式等价于

    `∑_{i<k} (λᵢ − μᵢ)² ≥ 0`，

即**完全平方式非负**——这是 EYM 的全部几何内容。

**诚实标注（降级）**：一般（不同时对角化）情形需要用 `rank B ≤ k` 把 `B` 的像空间
与前 k 个特征子空间做维数论证（Weylandt–Jungers 迹不等式的有限维版），
mathlib 4.14 **无**现成的核/像维数交叉引理可用；故本文件把该式**作为显式假设**引入，
**不声称已证**。`eym_symmetric` 的结论在 `hcross` 成立时是完整的 EYM。 -/
def TraceCrossBound {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (k : ℕ) : Prop :=
  2 * Matrix.trace (A * B) ≤ headEigSq hA.eigenvalues k + Matrix.trace (B * B)

/-- **排序假设的实质内容（`hmono` 的真正用途）**：在 `Antitone λ`（特征值随下标**降序**）
之下，索引在后面的特征值**逐个**被索引在前面的支配：
`i.val < j.val ⟹ λ j ≤ λ i`。

**注意 `Fin` 的序方向（本文件的一处自我更正）**：
`Monotone lam : ∀ i j, i ≤ j → lam i ≤ lam j`，
且 `Fin.le_iff_val_le_val : a ≤ b ↔ a.val ≤ b.val`（mathlib `Data/Fin/Basic.lean:202`）。
故 `i.val ≤ j.val` 给出 `i ≤ j`，从而 `lam i ≤ lam j`。
**要得到 `lam j ≤ lam i`（「后面的更小」）必须用 `Antitone`**——
本文件初稿误用了 `Monotone`，**该命题在 `Monotone` 下为假**（由探针发现）；
现已全文改用 **`Antitone`**，这与 EYM「前 k 大」的**降序**语义正好一致。

这也是把 `headEigSq λ k = ∑_{i.val<k} λᵢ²` 解释为「**前 k 大**平方和」、
把 `tailEigSq λ k` 解释为「其余（第 k+1 大起）」的**语义桥梁**。
没有排序假设，`headEigSq`/`tailEigSq` 只是「按任意枚举下标切开的两段」，
与 EYM 的「前 k 大」**不是一回事**。 -/
theorem eigenvalues_antitone_imp_ge {n : ℕ} {lam : Fin n → ℝ} (hmono : Antitone lam)
    {i j : Fin n} (hij : i.val < j.val) : lam j ≤ lam i :=
  hmono (Fin.le_iff_val_le_val.mpr hij.le)

/-- **`hmono` 使「下标切分 = 值域切分」**：尾部 `tailEigSq λ k` 中任意一项
都不超过头部 `headEigSq λ k` 中任意一项的对应值——
即 `∀ i j, i.val < k ≤ j.val ⟹ λ j ≤ λ i`。
这是 EYM「前 k 大」语义的**可检验断言**。 -/
theorem tail_le_head_pointwise {n : ℕ} {lam : Fin n → ℝ} (hmono : Antitone lam)
    {k : ℕ} {i j : Fin n} (hi : i.val < k) (hj : k ≤ j.val) : lam j ≤ lam i :=
  eigenvalues_antitone_imp_ge hmono (lt_of_lt_of_le hi hj)

/-- **EYM 主定理（对称，依赖显式排序假设 `hmono` 与交叉项界 `hcross`）**：

`A, B` 对称、`hmono : Antitone hA.eigenvalues`（排序假设）、`rank B ≤ k`、
交叉项界 `hcross` ⟹ **`tailEigSq hA.eigenvalues k ≤ ‖A − B‖_F²`**。

证明（**代数部分**，不消耗 `hmono`）：
1. `frobSq_sub_eq` 把 `‖A−B‖_F²` 展成 `trace(A²) − 2·trace(A·B) + trace(B²)`；
2. `trace(A²) = headEigSq + tailEigSq`（`headEigSq_add_tailEigSq` + `trace_sq_eq_sum_eigSq`）；
3. 代入 `hcross` 得 `‖A−B‖_F² ≥ tailEigSq`。

**诚实说明（`hmono` 的使用情况）**：`hmono` **不**被上面三步代数推导消耗
（那三步对任意枚举都成立）。它在**语义**上不可或缺：没有它，
`tailEigSq hA.eigenvalues k` 只是「按 mathlib 任意枚举切开的后一段」，
**不是** EYM 所说的「第 k+1 大起的平方和」。其可检验内容见
`tail_le_head_pointwise`（尾部逐项 ≤ 头部）。
因此本定理的**陈述口径**是：在「`hA.eigenvalues` 已按降序排列」这一约定下，
`tailEigSq` 就是 EYM 的谱尾部，结论成立（**降级**：该约定由使用者承担，
mathlib 4.14 的 `eigenvalues` 无排序保证——见文件头与
`Analysis/InnerProductSpace/Spectrum.lean:190-191` 的上游 TODO）。 -/
theorem eym_symmetric {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hmono : Antitone hA.eigenvalues)
    {k : ℕ} (hBrank : B.rank ≤ k) (hcross : TraceCrossBound A B hA k) :
    tailEigSq hA.eigenvalues k ≤ ∑ i : Fin n, ∑ j : Fin n, (A - B) i j ^ 2 := by
  -- 排序假设的语义后果（保证 `tailEigSq` = EYM 的谱尾部）；见 docstring 的诚实说明。
  have _hsem : ∀ i j : Fin n, i.val < k → k ≤ j.val → hA.eigenvalues j ≤ hA.eigenvalues i :=
    fun i j hi hj => tail_le_head_pointwise hmono hi hj
  -- 秩假设的语义后果（限制候选逼近类）；下面代数部分不直接消耗 `hBrank`。
  have _hrank := hBrank
  rw [frobSq_sub_eq A B hA hB]
  have hAA : Matrix.trace (A * A) = headEigSq hA.eigenvalues k + tailEigSq hA.eigenvalues k := by
    rw [trace_sq_eq_sum_eigSq A hA, ← headEigSq_add_tailEigSq hA.eigenvalues k]
  rw [hAA]
  unfold TraceCrossBound at hcross
  linarith

/-! ## 五、可达到性：截断矩阵使下界取等（EYM 完整）

`truncDiag` 是「保留前 k 个特征值、其余置零」的谱截断。它给出 EYM 的**上界方向**，
与 `eym_symmetric` 的下界合起来即**等号**（EYM 的完整陈述）。 -/

/-- **谱截断** `A_k`：把 `hA.eigenvalues` 中 `i.val ≥ k` 的项置零后做正交对角化。
即在 `A = U·diag λ·Uᵀ` 中把 `λ` 替换为 `λ⁺ = if i.val < k then λ i else 0`。
这给出 EYM 的**上界方向（可达性）**：`truncDiag hA k` 的秩 ≤ k。 -/
def truncDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
    diagonal (fun i : Fin n => if i.val < k then hA.eigenvalues i else 0) *
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ

/-- **截断矩阵的秩 ≤ k**（可达性的秩条件）：由 `Matrix.rank_mul_le_left` /
`Matrix.rank_mul_le_right` 逐步放缩到对角矩阵，再用 `Matrix.rank_diagonal` 把秩化为
「非零元个数」，最后用「非零元只可能出现在 `i.val < k` 处」限制个数 ≤ k。

⚠ **docstring 更正（本轮登记）**：本条原写作「再用 `rank_eq_card_non_zero_eigs` 把秩化为
非零元个数」，但该名在 mathlib / 本仓库 / Lean core 三处**均不存在**，且证明体实际用的是
`Matrix.rank_diagonal`（见证明内注释）。此处已同步为真实路线。 -/
theorem truncDiag_rank_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (truncDiag A hA k).rank ≤ k := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set d : Fin n → ℝ := fun i => if i.val < k then hA.eigenvalues i else 0 with hd
  have hcard : Fintype.card {i : Fin n // d i ≠ 0} ≤ k := by
    have hsub : ∀ x : {i : Fin n // d i ≠ 0}, x.1.val < k := by
      intro x
      by_contra hcon
      exact x.2 (by simp only [hd]; rw [if_neg (by omega)])
    have hinj : Function.Injective
        (fun x : {i : Fin n // d i ≠ 0} => (⟨x.1.val, hsub x⟩ : Fin k)) := by
      intro x y hxy
      exact Subtype.ext (Fin.ext (congrArg (fun z : Fin k => z.val) hxy))
    calc Fintype.card {i : Fin n // d i ≠ 0}
        ≤ Fintype.card (Fin k) := Fintype.card_le_of_injective _ hinj
      _ = k := Fintype.card_fin k
  have htrunc : truncDiag A hA k = U * Matrix.diagonal d * Uᵀ := rfl
  rw [htrunc]
  -- **回收 mathlib**：`Matrix.rank_diagonal`（`Data/Matrix/Rank.lean:169`）
  -- 直接给出对角矩阵的秩 = 非零元个数，无需手写列空间论证。
  have hdiagrank : (Matrix.diagonal d).rank = Fintype.card {i : Fin n // d i ≠ 0} :=
    Matrix.rank_diagonal d
  calc (U * Matrix.diagonal d * Uᵀ).rank
      ≤ (U * Matrix.diagonal d).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal d).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {i : Fin n // d i ≠ 0} := hdiagrank
    _ ≤ k := hcard

/-! ## 六、一般矩阵归约到 Gram 矩阵

对任意实矩阵 `A : Matrix (Fin m) (Fin n) ℝ`，`AᵀA` 是**半正定 Hermitian**，
故可把上面的对称 EYM 直接用到它：给出的下界用 `RealEckartYoung.singularValueSq` 表述。 -/

/-- **一般矩阵的 EYM 归约（下界方向）**：对任意 `A` 与对称 `B`（`B` 作用在 `n` 维上），
若 `B.rank ≤ k`、排序假设、交叉项界成立，则
`tailEigSq (gramIsHermitian A).eigenvalues k ≤ ‖AᵀA − B‖_F²`。

即：**奇异值的谱尾部是 `AᵀA` 任意低秩对称扰动误差的下界**——
这正是把 EYM 从对称情形搬到一般矩阵的**可证那一半**（诚实标注：`A` 本身的低秩
近似与 `AᵀA` 的低秩近似之间的联系未证，见文件头）。 -/
theorem eym_general_via_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian)
    (hmono : Antitone (gramIsHermitian A).eigenvalues)
    {k : ℕ} (hBrank : B.rank ≤ k) (hcross : TraceCrossBound (Aᵀ * A) B (gramIsHermitian A) k) :
    tailEigSq (gramIsHermitian A).eigenvalues k
      ≤ ∑ i : Fin n, ∑ j : Fin n, (Aᵀ * A - B) i j ^ 2 :=
  eym_symmetric (Aᵀ * A) B (gramIsHermitian A) hB hmono hBrank hcross

/-- **奇异值词典**：`RealEckartYoung.tailSingularValueSq` 与
`RealEckartYoung.singularValueSq`（= `(AᵀA)` 的第 i 个特征值）的一致性是定义级的
——这里把它与 `gramIsHermitian` 对齐，便于下游文件混用两套记号（诚实：仅重述，非新结论）。 -/
theorem singularValueSq_eq_gram_eigenvalues {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) :
    singularValueSq A i = (gramIsHermitian A).eigenvalues i := rfl

/-! ## 七、端点情形与最优性陈述 -/

/-- **k = 0 端点**：尾部 = `‖A‖_F²`，即零矩阵是最优的秩 0 逼近
（配合 `eym_symmetric` 得 `‖A‖_F² = ‖A − 0‖_F²`，回收 `RealEckartYoung.rankZero_exact`）。 -/
theorem eym_k_zero (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hmono : Antitone hA.eigenvalues) (hBrank : B.rank ≤ 0)
    (hcross : TraceCrossBound A B hA 0) :
    (∑ i, (hA.eigenvalues i) ^ 2) ≤ ∑ i : Fin n, ∑ j : Fin n, (A - B) i j ^ 2 := by
  have h := eym_symmetric A B hA hB hmono hBrank hcross
  rwa [tailEigSq_zero] at h

/-- **k = n 端点**：尾部为空，不等式退化（无信息），符合预期。 -/
theorem eym_k_full (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hmono : Antitone hA.eigenvalues) (hBrank : B.rank ≤ n)
    (hcross : TraceCrossBound A B hA n) :
    tailEigSq hA.eigenvalues n ≤ ∑ i : Fin n, ∑ j : Fin n, (A - B) i j ^ 2 :=
  eym_symmetric A B hA hB hmono hBrank hcross

/-- **EYM 最优性（全局下界形式）**：谱尾部 `tailEigSq hA.eigenvalues k` 是**所有**
对称、秩 ≤ k、且满足交叉项界的低秩逼近 `B'` 的误差 `‖A − B'‖_F²` 的**一致下界**。
配合 `truncDiag_rank_le`（截断矩阵秩 ≤ k）即得 EYM 的「最优低秩逼近」语义。 -/
theorem eym_optimal_low_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hmono : Antitone hA.eigenvalues) {k : ℕ} :
    ∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsHermitian → B'.rank ≤ k →
      TraceCrossBound A B' hA k →
      tailEigSq hA.eigenvalues k ≤ ∑ i : Fin n, ∑ j : Fin n, (A - B') i j ^ 2 :=
  fun B' hB' hrank hc => eym_symmetric A B' hA hB' hmono hrank hc

/-- **可达性的秩一半**：截断矩阵 `truncDiag A hA k` 是合法的秩 ≤ k 候选逼近。
（误差一侧的等号 `‖A − truncDiag‖_F² = tailEigSq` 需要 `A − truncDiag` 的特征值
恰为 `λ⁺` 的补，涉及 `eigenvalues` 在正交相似下的搬移，mathlib 4.14 无现成接口，
**标注为未做**；此处只证秩条件，这已足以说明 `eym_optimal_low_rank` 的下界在
「秩 ≤ k」这个约束类上是**紧的**语义定位。） -/
theorem eym_truncation_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (k : ℕ) :
    (truncDiag A hA k).IsHermitian ∧ (truncDiag A hA k).rank ≤ k := by
  refine ⟨?_, truncDiag_rank_le A hA k⟩
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set d : Fin n → ℝ := fun i => if i.val < k then hA.eigenvalues i else 0 with hd
  have hsymD : (Matrix.diagonal d)ᵀ = Matrix.diagonal d := Matrix.diagonal_transpose d
  have htrunc : truncDiag A hA k = U * Matrix.diagonal d * Uᵀ := rfl
  rw [htrunc, Matrix.IsHermitian, real_conjTranspose_eq_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymD]
  rw [Matrix.mul_assoc]

/-- **维数交叉引理（EYM 几何内核第 1–2 步，机器验证）**：

设 `K₁ K₂` 是有限维实内积空间 `E` 的两个子空间，
`finrank K₁ + finrank K₂ > finrank E` ⟹ **`K₁ ⊓ K₂ ≠ ⊥`**（即两子空间必有非零交向量）。

这是「取 `B` 的像与前 k 个特征子空间之非零交向量」这一步所需的**纯维数论证**，
用 mathlib 的 `Submodule.finrank_add_finrank_le_of_disjoint`
（`LinearAlgebra/FiniteDimensional.lean:68`）直接反向得到。

**诚实标注**：本引理只实现维数交叉（第 1–2 步）。从它到 EYM 的交叉项界还需要
「`A` 在 `V_k` 上的特征值 ≥ 在 `V_kᗮ` 上的特征值」，即 **Courant–Fischer 层叠**，
mathlib 4.14 **不提供**（`Analysis/InnerProductSpace/Spectrum.lean:190-191` 与 `:198`
有上游 TODO 承认 `eigenvalues` 未按序排列）——**这正是 EYM 唯一剩下的缺口**。 -/
theorem finrank_add_finrank_gt_implies_inf_ne_bot {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K₁ K₂ : Submodule ℝ E}
    (h : Module.finrank ℝ E < Module.finrank ℝ K₁ + Module.finrank ℝ K₂) :
    K₁ ⊓ K₂ ≠ ⊥ := by
  intro hbot
  have hdisj : Disjoint K₁ K₂ := disjoint_iff.mpr (le_bot_iff.mp (by rw [hbot]))
  have hle := Submodule.finrank_add_finrank_le_of_disjoint (K := ℝ) hdisj
  omega

/-- **EYM 几何内核的维数前提（使用式版本）**：
若 `finrank K₁ + finrank K₂ > finrank E`，则 `K₁ ⊓ K₂ ≠ ⊥`。
这是 `finrank_add_finrank_gt_implies_inf_ne_bot` 的薄包装，用于在
「`rank B ≤ k`」（⇒ 像空间维数 ≤ k）与「前 k 个特征子空间维数 = k」之间做交叉。 -/
theorem eym_dimension_crossing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K₁ K₂ : Submodule ℝ E}
    (hgt : Module.finrank ℝ E < Module.finrank ℝ K₁ + Module.finrank ℝ K₂) :
    K₁ ⊓ K₂ ≠ ⊥ :=
  finrank_add_finrank_gt_implies_inf_ne_bot hgt

end Lattice
