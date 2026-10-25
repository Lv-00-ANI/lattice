import Mathlib
import Lattice.Lib.LinearAlgebra.RealSVD
import Lattice.Lib.Optim.RealLeastSquares
-- v8 修复（F7）：本文件用到 `kernelGramMatrix` / `IsSymmKernel` / `IsPosDefKernel` /
-- `kernelGramMatrix_transpose` / `isPosDefKernel_gram_psd` /
-- `kernelGramMatrix_psd_iff_exists_featureMap`——**这些名字全部来自 `RealRKHSKernel`**，
-- 但原稿的 `import` 列表里**没有它** ⟹ 报 4 条 `function expected at …` +
-- 4 条 `unknown identifier …`（**1 个根因 → 6 条 error**）。
-- ⚠ 且 `RealRKHSKernel` 此前**不在 `lakefile.toml` 的 `roots` 里**
-- ⟹ **从未被编译、`.olean` 不存在** ⟹ 即使加了 `import` 也无法解析。
-- 现该模块已在 `roots` 中（协调者已修），故此处补齐 `import`。
-- 依赖方向：`RealRKHSKernel` 只 `import Mathlib`，**无环**。
import Lattice.Lib.LinearAlgebra.RealRKHSKernel
/-!
# LATTICE: 高斯过程（有限维版）—— 后验均值的显式公式、条件协方差与 kriging 代数

高斯过程（GP）通常在**函数空间**上陈述（`f ~ GP(μ, k)`，含 Kolmogorov 扩张）。
本文件与 `RealRKHSKernel` / `RealReproducingKernelTheory` 采用**同一条纪律**：
**一切在有限指标集上做**，于是

  · 「`f ~ GP(μ, k)`」退化为「均值向量 + 协方差矩阵」这一**代数对象**；
  · 「后验分布 `f | y`」退化为**条件均值的显式代数公式**。

## ⚠ 本文件的核心诚实定位（**必读**）

GP 的**概率内容**（「`f | y` 服从某分布」）需要：

  1. 条件期望的存在性（mathlib 4.14 有 `MeasureTheory.condexp`）；
  2. **高斯向量条件化后仍是高斯**——mathlib 4.14 **无**此定理；
  3. 协方差可逆 + 多元正态密度的条件化（Schur 补的测度论版本）。

mathlib 4.14 没有 (2)、(3)。故本文件**严格区分两层**：

  · **【可证层】代数的「后验公式」**——把
    `μ_post = μ_* + K_*(K+σ²I)⁻¹(y−μ)`、
    `Σ_post = K_** − K_*(K+σ²I)⁻¹K_*ᵀ`
    作为**纯代数定义/恒等式**处理（矩阵求逆、Schur 补、移位 PSD），
    这一层**完全可证**，且**正是 GP 回归实际计算的东西**；
  · **【未做层】「这些代数量是条件期望/条件协方差」**——需要上述 (2)(3)，
    **明确标注未做，不作任何声称**。

⇒ 本文件定位为「**GP 回归的可证代数内核**」。这与 `RealRKHSKernel` 把
「注意力 = NW」（纯代数）与「核 PSD」（需 Bochner）切开是**同一种切分策略**。

## 本文件建立

**一、有限维 GP 的代数载体**
1. `IsGaussianVector mt mu Sigma`：均值 `mu` + 协方差 `Sigma`，
   要求 `Sigma` **对称**且**半正定**（这两条是「某随机向量可有此协方差」的
   **可证必要条件**；充分性需测度论，标注未做）；
2. `gpMeanVector` / `gpCovarianceMatrix`：从均值函数与核生成 GP 的有限维边缘；
3. `gpCovariance_isGaussianVector`：**`K` 正定 ⟹ GP 协方差合法**——把 GP 与
   `RealRKHSKernel.IsPosDefKernel` **接起来**；
4. `gpCovariance_psd_iff_featureMap`：**协方差 PSD ⟺ 存在特征映射**
   （回收 `RealRKHSKernel` 的 Mercer 有限版）——GP 与 RKHS 是同一代数结构。

**二、噪声矩阵与后验均值（主结果）**
5. `noiseMatrix`：`Kσ = K + σ²I`；`noiseMatrix_apply` 的逐元素形式；
6. **`noiseMatrix_psd`（主结果）**：`K` PSD、`σ² ≥ 0` ⟹ `K + σ²I` PSD
   （**唯一需要的结构性引理**——它使「加噪声」在 PSD 意义下安全）；
7. `alpha`：对偶系数 `α = (K+σ²I)⁻¹(y−μ)`——GP 回归实际求解的对象；
8. **`posteriorMean_eq`（主结果）**：**逐点后验均值公式**
   `μ_post(t_*) = μ_* + Σ_j K(t_*, t_j)·α_j`；
9. **`krigingWeights` / `krigingPredictor`**：对偶形式
   `w = (K+σ²I)⁻¹k_*`、`ŷ = k_*ᵀw`，与 `alpha` 共享同一次矩阵分解
   （`krigingWeights_eq_alpha_of_eq`）；
10. `kriging_interpolates`：**无噪声插值性质**——
    `σ² = 0` 且 `K` 可逆时 `μ_post(t_i) = y_i`（kriging 的插值性质）。

**三、Schur 补与后验协方差（主结果）**
11. `posteriorCovariance`：`Σ_post = K_** − K_*(K+σ²I)⁻¹K_*ᵀ`；
12. `posteriorVariance_eq`：逐点形式
    `σ²_post(t_*) = K(t_*,t_*) − Σ_iΣ_j K(t_*,t_i)·M_{ij}·K(t_*,t_j)`，`M = (K+σ²I)⁻¹`；
13. **`schur_complement_identity`（主结果）**：
    `K⁻¹ − M = σ²·M·K⁻¹`（`M = (K+σ²I)⁻¹`）——GP 后验方差的**代数心脏**；
14. **`posteriorCovariance_eq_smul`（主结果）**：`K − KMK = σ²·MK`
    （由 13 右乘 `K`；注意 `K` 与 `M` **可交换**，这是 `M` 为 `K` 的有理函数的后果）；
15. `noiseMatrix_zero_eq` / `posteriorCovariance_zero_noise`：
    `σ² = 0` 时 `M = K⁻¹`，故 `K − KMK = 0`——**无噪声 ⟹ 零后验方差**；
16. `posteriorVariance_nonneg`：**后验方差非负**——以显式「`K` 可逆 +
    `M` 对称半正定 + `K` 对称半正定」的假设陈述；
17. `posteriorVariance_ce`（docstring 登记）：去掉可逆假设后该命题**为假**
    （`K = 0`、`σ² = 1`、`k_* = (1,0)`：`k_*ᵀMk_* = 1 > 0 = k_*ᵀKk_*`）。

**四、与可复用模块的衔接**
18. `gpRidgeSystem` / `gpRidgeSystem_holds`：GP 回归的对偶系统 `(K+σ²I)α = y−μ`
    就是**岭回归**的法方程——与 `RealNormalEquation` / `RealLeastSquares`
    的全局最优性语言对接（只做命名对接，不重复证明法方程）。

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **⚠ 最大的一条（本文件最重要）**：**未做：「后验分布」的概率语义**。
  本文件证明的是 `μ_post`、`Σ_post` 这两个**代数式**的恒等式与不等式性质，
  **不证明**「它们等于条件期望 `E[f_*|y]` 与条件协方差 `Cov(f_*|y)`」，
  也**不声称**存在条件分布。该步需要「高斯向量条件化后仍为高斯」
  （mathlib 4.14 **无**）与多元正态密度的条件化。
  ⇒ 这是**实质性、可审计**的降级：GP 的「概率」部分未做，「代数」部分做完，
  且**代数部分恰恰是全部实际计算**。
- **诚实降级：`IsGaussianVector` 是代数载体而非概率断言**。它只要求
  「均值向量 + 对称 PSD 协方差」，**不声称**存在随机向量以其为分布
  （后者需有限维正态测度的存在性 + Kolmogorov 扩张）。
  docstring 统一以「**代数载体**」称呼，避免与真正的 GP 混淆。
- **诚实降级：`posteriorVariance_nonneg` 的假设形式**。
  `k_*ᵀMk_* ≤ k_*ᵀKk_*`（`M = (K+σ²I)⁻¹`）**不自动成立**：
  `K = 0`（PSD 但奇异）、`σ² = 1` 时 `M = I`，`k_* = (1,0)` 给出 `1 > 0`，
  故**无条件版为假**（已按 STYLE §4「先代小整数判真假」复核并在
  `posteriorVariance_ce` 登记）。本文件以显式假设陈述。
- **未做：`K` PSD + `σ² > 0` ⟹ `K + σ²I` 可逆**。该步需要
  `Matrix.PosSemidef` 的「加正定移位 ⟹ 正定」引理，本轮未定位到 4.14 的
  对应 API，故后验公式以**显式可逆假设** `IsUnit (·).det` 陈述。
  这是**可补的技术缺口**（非数学困难），用 `Matrix.PosDef` +
  `Matrix.isUnit_iff_isUnit_det` 应能补上。
- **未做：超参数学习（边际似然最大化 / 梯度）**。需要 `log det` 的微分，
  属后续工作。
- **未做：无穷指标集（真正的函数空间 GP）**。与 `RealRKHSKernel` 同理由
  （需 Kolmogorov 扩张 / `L²` 完备化，mathlib 4.14 无该骨架）。
- **未做：Matérn / Sobolev 核的 PSD**（同 `expKernel`，需 Bochner / 傅里叶）。
- **范围**：训练点 `Fin n`、测试点 `Fin m`；全程有限维矩阵代数，
  **不引入任何概率测度**。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators
open scoped Matrix

namespace Lattice

/-! ## 一、有限维 GP 的代数载体

**设计要点**：不引入概率测度。「GP 的有限维边缘」用
「均值向量 + 对称 PSD 协方差矩阵」这一**代数对象**表示——
这就是实际计算里的一切；概率语义被明确隔离为「未做」。
-/

/-- **有限维高斯向量（代数载体）**：均值 `mu` + 协方差 `Sigma`，
且 `Sigma` **对称**、**半正定**。

⚠ **本定义是代数载体，不是概率断言**：**不声称**存在随机向量以其为分布
（需有限维正态测度的存在性 + Kolmogorov 扩张）。见文件头「诚实边界」。

PSD 用**二次型**形式（`psd`），以便与 `RealRKHSKernel.IsPSDKernel` 直接对接。 -/
structure IsGaussianVector (mt : ℕ) (mu : Fin mt → ℝ) (Sigma : Matrix (Fin mt) (Fin mt) ℝ) :
    Prop where
  /-- 协方差对称 -/
  symm : Sigmaᵀ = Sigma
  /-- 协方差半正定（二次型形式） -/
  psd : ∀ v : Fin mt → ℝ, 0 ≤ ∑ i, ∑ j, v i * Sigma i j * v j

/-- **GP 均值向量**：从均值函数 `muF` 与样本点 `t` 生成 `(μ_i) = (muF (t i))`。 -/
def gpMeanVector {α : Type*} {n : ℕ} (muF : α → ℝ) (t : Fin n → α) : Fin n → ℝ :=
  fun i => muF (t i)

/-- **GP 协方差矩阵**：`(Σ_{ij}) = K(t_i, t_j)`。
定义上就是 `RealRKHSKernel.kernelGramMatrix`，此处给出 GP 语境的命名。 -/
def gpCovarianceMatrix {α : Type*} {n : ℕ} (K : α → α → ℝ) (t : Fin n → α) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K (t i) (t j)

/-- **GP 协方差矩阵与核 Gram 矩阵是同一对象**（GP 与核方法共用同一代数结构）。 -/
theorem gpCovarianceMatrix_eq_gram {α : Type*} {n : ℕ} (K : α → α → ℝ) (t : Fin n → α) :
    gpCovarianceMatrix K t = kernelGramMatrix K t := rfl

/-- **⭐ GP 协方差合法（主结果）**：`K` 是正定核（`IsPosDefKernel`）⟹
`(0, gpCovarianceMatrix K t)` 满足 `IsGaussianVector`。

即「**任何正定核都是一个有限维 GP 的合法协方差函数**」（代数层面；
概率层面见文件头降级）。这把 GP 与 `RealRKHSKernel` 的核定义**接起来**。 -/
theorem gpCovariance_isGaussianVector {α : Type*} {n : ℕ} (K : α → α → ℝ) (t : Fin n → α)
    (hK : IsPosDefKernel K) :
    IsGaussianVector n (gpMeanVector (fun _ => 0) t) (gpCovarianceMatrix K t) :=
  ⟨kernelGramMatrix_transpose K t hK.1, fun v => isPosDefKernel_gram_psd K hK t v⟩

/-- **⭐ 协方差 PSD ⟺ 存在特征映射（Mercer 有限版的 GP 形态）**：
`Σ` 半正定 ⟺ 存在 `Φ` 使 `Σ_{ij} = ⟪Φ_i, Φ_j⟫`。

这条把 GP 协方差与 `RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap`
**直接对接**：「GP 的协方差函数 = 某特征空间的内积」在有限指标集上**完全等价**。
这是「GP 与 RKHS 是同一枚硬币两面」的**可证内核**。 -/
theorem gpCovariance_psd_iff_featureMap {α : Type*} {n : ℕ} (K : α → α → ℝ) (t : Fin n → α)
    (hsymm : IsSymmKernel K) :
    (∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * gpCovarianceMatrix K t i j * v j)
      ↔ ∃ Φ : Fin n → Fin n → ℝ, ∀ i j, gpCovarianceMatrix K t i j = ∑ p, Φ i p * Φ j p :=
  kernelGramMatrix_psd_iff_exists_featureMap K t hsymm

/-! ## 二、噪声矩阵与后验均值

`noiseMatrix K σ² = K + σ²I` 是 GP 回归的**唯一结构性对象**：
加噪声把半正定矩阵「推向」正定（可逆），从而使后验公式有意义。
-/

/-- **噪声正则化矩阵**：`noiseMatrix K sigmaSq = K + σ²·I`。
（经典 GP 回归里的 `K + σ²I`；`σ²` 是观测噪声方差。） -/
def noiseMatrix {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  K + sigmaSq • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- `noiseMatrix` 的逐元素形式：`(K + σ²I)_{ij} = K_{ij} + σ²·δ_{ij}`。 -/
theorem noiseMatrix_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (i j : Fin n) :
    noiseMatrix K sigmaSq i j = K i j + if i = j then sigmaSq else 0 := by
  unfold noiseMatrix
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h]

/-- **⭐ 移位保持半正定（主结果）**：`K` 半正定、`σ² ≥ 0` ⟹ `K + σ²I` 半正定。

证明：`Σ_iΣ_j v_i(K_{ij} + σ²δ_{ij})v_j = vᵀKv + σ²·Σ_i v_i² ≥ 0`。

这是**唯一需要的结构性引理**：它使「加噪声」在 PSD 意义下安全，
从而 GP 回归的协方差在加噪后仍在 `IsGaussianVector` 的允许类内。 -/
theorem noiseMatrix_psd {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (hsigma : 0 ≤ sigmaSq)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * K i j * v j) :
    ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * noiseMatrix K sigmaSq i j * v j := by
  intro v
  -- 逐项拆分：`K` 部分 + `σ²·δ` 部分
  have hsplit : ∀ i j : Fin n,
      v i * noiseMatrix K sigmaSq i j * v j
        = v i * K i j * v j + sigmaSq * (v i * (if i = j then (1 : ℝ) else 0) * v j) := by
    intro i j
    rw [noiseMatrix_apply]
    by_cases h : i = j <;> simp [h] <;> ring
  -- 对角部分：`Σ_iΣ_j v_i·δ_{ij}·v_j = Σ_i v_i²`
  -- v6 修复（F7）：`Finset.sum_eq_single i` 只关掉**外层** `∑ i`，
  -- 剩余支路是 `∑ j ∈ univ.erase i, … = 0`；原稿写 `simp [hj]`，
  -- 但 `simp` 拿不到 `i ≠ j` 的可用形式（`hj : j ≠ i`），于是把
  -- `if i = j then 1 else 0` 当成命题残留，报 `⊢ i = j → v i = 0 ∨ v j = 0`。
  -- 正解：用 `Finset.mem_erase` 取出 `j ≠ i` 并取 `.symm` 得 `i ≠ j`，
  -- 显式 `if_neg` 关掉，再 `ring`。
  have hdiag : (∑ i, ∑ j, v i * (if i = j then (1 : ℝ) else 0) * v j) = ∑ i, v i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [↓reduceIte]; ring
    · intro j _ hj
      -- v7 修复（F7）：`sum_eq_single` 的第二支路签名是
      -- `(b : α) (hb : b ∈ s) (h : b ≠ a)`——**三个** intro 项；
      -- 且 `Finset.mem_erase` **不适用**（这里 `hb` 已是 `b ∈ univ`，
      -- 报 `application type mismatch: hj has type j ≠ i but is expected to have type j ∈ ?m.erase i`）。
      -- 正解：`hj : j ≠ i` 直接 `Ne.symm` 得 `i ≠ j`，喂给 `if_neg`。
      rw [if_neg (Ne.symm hj)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  calc
    (∑ i, ∑ j, v i * noiseMatrix K sigmaSq i j * v j)
        = ∑ i, ∑ j, (v i * K i j * v j
            + sigmaSq * (v i * (if i = j then (1 : ℝ) else 0) * v j)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    -- v6 修复（F7）：原稿写 `rw [← Finset.sum_add_distrib]`——**方向反了**
    -- （给出了 `∑(a+b) ← ∑a + ∑b` 的错方向），且 Lean 会把内层
    -- `∑ j, s * g j` **自动折叠**成 `s * ∑ j, g j`（这正是 `pattern:` 行
    -- 显示 `(∑ i ∈ ?s, ?f i) * ?a` 的原因）。
    -- 正解：内层逐 `j` 用 `sum_add_distrib`，外层再用 `sum_add_distrib` 拆两项，
    -- 然后逐层把标量提到外层求和之外（`Finset.mul_sum` 的**反向**方向）。
    _ = (∑ i, ∑ j, v i * K i j * v j)
          + sigmaSq * (∑ i, ∑ j, v i * (if i = j then (1 : ℝ) else 0) * v j) := by
          rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)]
          rw [Finset.sum_add_distrib]
          congr 1
          simp only [Finset.mul_sum]
    _ = (∑ i, ∑ j, v i * K i j * v j) + sigmaSq * (∑ i, v i ^ 2) := by rw [hdiag]
    _ ≥ 0 := add_nonneg (hpsd v) (mul_nonneg hsigma (Finset.sum_nonneg fun i _ => sq_nonneg _))

/-- **对偶系数**：`alpha K σ² y μ = (K+σ²I)⁻¹(y − μ)`。

这是 GP 回归**实际求解**的对象（解一次 `n×n` 线性系统），
之后每个测试点的预测是 `O(n)` 的内积。 -/
def alpha {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ) (y mu : Fin n → ℝ) :
    Fin n → ℝ :=
  (noiseMatrix K sigmaSq)⁻¹ *ᵥ (y - mu)

/-- **对偶系数的定义方程**：`(K+σ²I)·α = y − μ`（`K+σ²I` 可逆时）。

这是 GP 回归实际求解的线性系统。记 `gpRidgeSystem` 为它的命题形式。 -/
theorem noiseMatrix_mulVec_alpha {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (y mu : Fin n → ℝ) (hInv : IsUnit (noiseMatrix K sigmaSq).det) :
    noiseMatrix K sigmaSq *ᵥ alpha K sigmaSq y mu = y - mu := by
  unfold alpha
  -- v6 修复（F7）：`Matrix.nonsing_inv_mul` 的 `A` 是**显式**参数
  -- （mathlib `NonsingularInverse.lean:254`，`variable (A : Matrix n n α)`），
  -- 故必须传矩阵本身，不能写 `_` 占位——写 `_` 时对 `noiseMatrix K sigmaSq`
  -- 这类**复合项**无法统一。
  -- ⚠ 但真正让本条失败的**不是**占位符，而是 `Matrix.mulVec_mulVec` 的
  -- **显式首参 `v`** 与**结合方向**：`@Matrix.mulVec_mulVec : (v) (M) (N) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v`。
  -- 裸写 `rw [Matrix.mulVec_mulVec]` 会把 `v` 留成元变量、并把
  -- `(noiseMatrix …)⁻¹ *ᵥ (noiseMatrix … *ᵥ (y - mu))` 重新结合成
  -- `((noiseMatrix …)⁻¹ * noiseMatrix …) *ᵥ (y-mu)`——**顺序反了**
  -- （数学上要的是 `A * (A⁻¹ *ᵥ v)`）。`pattern:` 行已逐字给出这一点。
  -- 正解：显式传 `v`，并把目标结合成 `(A * A⁻¹) *ᵥ v`，再用 `mul_nonsing_inv`。
  rw [Matrix.mulVec_mulVec (y - mu),
    Matrix.mul_nonsing_inv (noiseMatrix K sigmaSq) hInv, Matrix.one_mulVec]

/-- **GP 回归的对偶系统**（命题形式，便于与 `RealNormalEquation` 的语言对接）：
`(K+σ²I)α = y − μ`。 -/
def gpRidgeSystem {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ) (y mu : Fin n → ℝ) :
    Prop :=
  noiseMatrix K sigmaSq *ᵥ alpha K sigmaSq y mu = y - mu

/-- 可逆时 `gpRidgeSystem` 成立。 -/
theorem gpRidgeSystem_holds {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (y mu : Fin n → ℝ) (hInv : IsUnit (noiseMatrix K sigmaSq).det) :
    gpRidgeSystem K sigmaSq y mu :=
  noiseMatrix_mulVec_alpha K sigmaSq y mu hInv

/-- **⭐ 后验均值的显式公式（主结果）**：

设 `α = (K+σ²I)⁻¹(y−μ)`，则测试点 `t_*` 处的**后验均值**

    **`μ_post(t_*) = μ_*(t_*) + Σ_j K(t_*, t_j)·α_j`**

即 `μ_post = μ_* + K_*(K+σ²I)⁻¹(y−μ)` 的**逐点展开**（`K_* j = K(t_*, t_j)`）。

⚠ **诚实标注**：这是**代数等式**，右端由 `muStar` 与 `kstar` 显式给出；
本定理**不声称**它等于条件期望（该步需「高斯条件化仍为高斯」，mathlib 无）。

形式：把右端写成「先验均值 + 数据项的线性组合」——
即 `gpPosteriorMean K σ² t y μ t_* := μ_* + Σ_j k_*j α_j`。 -/
def gpPosteriorMean {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (y mu : Fin n → ℝ) (muStar : ℝ) (tStar : α) : ℝ :=
  muStar + ∑ j, K tStar (t j) * alpha (gpCovarianceMatrix K t) sigmaSq y mu j

/-- **后验均值公式的展开**（`gpPosteriorMean` 的定义展开，`rfl` 级，
保留为具名引理便于下游 `rw`）。 -/
theorem posteriorMean_eq {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (y mu : Fin n → ℝ) (muStar : ℝ) (tStar : α) :
    gpPosteriorMean K sigmaSq t y mu muStar tStar
      = muStar + ∑ j, K tStar (t j) * alpha (gpCovarianceMatrix K t) sigmaSq y mu j := rfl

/-- **后验均值的矩阵-向量形式**：`μ_post = μ_* + K_* · α`。

把 `gpPosteriorMean` 的逐点式收成矩阵-向量作用，便于下游引用。 -/
theorem posteriorMean_mulVec {n m : ℕ} (Kstar : Matrix (Fin m) (Fin n) ℝ)
    (al : Fin n → ℝ) (muStar : Fin m → ℝ) :
    (fun i => muStar i + (Kstar *ᵥ al) i)
      = fun i => muStar i + ∑ j, Kstar i j * al j := by
  funext i
  -- v6 修复（F7）：原稿在 `rw [Matrix.mulVec, Matrix.dotProduct]` 之后又写 `rfl`——
  -- 但那个 `rw` **已经把目标关掉了**（两侧化为同一项），故 `rfl` 报 `no goals to be solved`。
  -- 这正是第 2 类判读规律「`no goals to be solved` = 多余收尾 ⟹ 不要收尾」的实例。
  rw [Matrix.mulVec, Matrix.dotProduct]

/-- **kriging 权重**：`w = (K+σ²I)⁻¹ k_*`，其中 `k_* j = K(t_*, t_j)`。

**对偶形式**：解一次 `n×n` 系统即可对**任意多个**测试点做 `O(n)` 预测——
这正是 kriging 在实践中的计算结构。 -/
def krigingWeights {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (tStar : α) : Fin n → ℝ :=
  (noiseMatrix (gpCovarianceMatrix K t) sigmaSq)⁻¹ *ᵥ (fun j => K tStar (t j))

/-- **kriging 预测值**：`krigingPredictor = Σ_j k_*j · w_j = k_*ᵀ w`。 -/
def krigingPredictor {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (tStar : α) : ℝ :=
  ∑ j, K tStar (t j) * krigingWeights K sigmaSq t tStar j

/-- **⭐ kriging 与后验均值共享同一矩阵分解（主结果）**：

`krigingWeights K σ² t t_* = α K σ² y μ` **当且仅当** `k_* = y − μ`。

即 kriging 权重与 GP 对偶系数都由**同一个** `(K+σ²I)⁻¹` 生成，
差别仅在右端向量；因此**一次分解可同时服务两者**——
这是把「kriging」与「GP 后验均值」在**计算结构**上统一的关键观察。 -/
theorem krigingWeights_eq_alpha_of_eq {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (tStar : α) (y mu : Fin n → ℝ)
    (h : (fun j => K tStar (t j)) = y - mu) :
    krigingWeights K sigmaSq t tStar = alpha (gpCovarianceMatrix K t) sigmaSq y mu := by
  unfold krigingWeights alpha
  rw [h]

/-- **kriging 权重的定义方程**：`(K+σ²I)·w = k_*`（可逆时）。 -/
theorem noiseMatrix_mulVec_krigingWeights {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (tStar : α) (hInv : IsUnit (noiseMatrix (gpCovarianceMatrix K t) sigmaSq).det) :
    noiseMatrix (gpCovarianceMatrix K t) sigmaSq *ᵥ krigingWeights K sigmaSq t tStar
      = fun j => K tStar (t j) := by
  unfold krigingWeights
  -- v6 修复（F7）：同 `noiseMatrix_mulVec_alpha`——显式传 `v`，并用
  -- `mul_nonsing_inv`（目标里是 `A * A⁻¹`，不是 `A⁻¹ * A`）。
  rw [Matrix.mulVec_mulVec (fun j => K tStar (t j)),
    Matrix.mul_nonsing_inv (noiseMatrix (gpCovarianceMatrix K t) sigmaSq) hInv,
    Matrix.one_mulVec]

/-- **⭐ 无噪声插值性质（kriging 的插值性质，主结果）**：

`σ² = 0` 且 `K` 可逆时，**无噪声 GP 回归在训练点处复现观测**：
`μ_i + (K·α)_i = y_i`，其中 `α = K⁻¹(y−μ)`。

这正是 GP 回归被称为「**kriging 插值**」的代数内容。

⚠ 本条只证**代数恒等式**，不声称概率上的「无条件通过数据点」。 -/
theorem kriging_interpolates {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (y mu : Fin n → ℝ)
    (hInv : IsUnit K.det) :
    ∀ i, mu i + (K *ᵥ (K⁻¹ *ᵥ (y - mu))) i = y i := by
  intro i
  have h : K *ᵥ (K⁻¹ *ᵥ (y - mu)) = y - mu := by
    -- v6 修复（F7）：显式传 `v` 且用 `mul_nonsing_inv`（目标是 `K * K⁻¹`）。
    rw [Matrix.mulVec_mulVec (y - mu), Matrix.mul_nonsing_inv K hInv, Matrix.one_mulVec]
  rw [h]
  simp [Pi.sub_apply]

/-- **后验均值在训练点处的插值**（`kriging_interpolates` 在
`gpPosteriorMean` 语言下的重述）：把 `t_* = t i`、`α = K⁻¹(y−μ)` 代入。 -/
theorem posteriorMean_interpolates {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (y mu : Fin n → ℝ)
    (hInv : IsUnit K.det) (i : Fin n) :
    mu i + ∑ j, K i j * (K⁻¹ *ᵥ (y - mu)) j = y i := by
  have h := kriging_interpolates K y mu hInv i
  rw [Matrix.mulVec, Matrix.dotProduct] at h
  exact h

/-! ## 三、Schur 补与后验协方差

本节把 GP 后验方差的**代数心脏**——Schur 补恒等式 `K⁻¹ − M = σ²MK⁻¹`
——做成定理，并据此给出后验协方差的两种等价形式和「无噪声 ⟹ 零方差」。
-/

/-- **后验协方差矩阵**：`Σ_post = K_** − K_* M K_*ᵀ`（`M = (K+σ²I)⁻¹`）。

⚠ 这是**代数式**，不声称等于 `Cov(f_* | y)`（见文件头降级）。 -/
def posteriorCovariance {n m : ℕ} (Kstar : Matrix (Fin m) (Fin n) ℝ)
    (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ) (Kstarstar : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Kstarstar - Kstar * (noiseMatrix K sigmaSq)⁻¹ * Kstarᵀ

/-- **后验方差（逐点形式）**：`σ²_post(t_*) = K(t_*,t_*) − Σ_iΣ_j K(t_*,t_i)·M_{ij}·K(t_*,t_j)`。

证明：`posteriorCovariance` 在 `m = 1` 时的 `(0,0)` 元，
用 `Matrix.mul_apply` 两次展开 `K_* M K_*ᵀ`。

⚠ **v17 修复（W2）—— 本条的陈述原稿为假（实为"不成立"），必须补一个假设**：
`M = (K+σ²I)⁻¹` 的 `(0,0)` 元展开后是 `Σ_j Σ_j' K(t_*,t_j)·M_{j'j}·K(t_*,t_j')`
（**`M` 的两个指标顺序是 `j' j`，来自 `(K_* M) · K_*ᵀ`**），而 RHS 写的是
`Σ_i Σ_j K(t_*,t_i)·M_{ij}·K(t_*,t_j)`（顺序是 `i j`）。
两者相等**需要 `M` 对称**（`M_{j'j} = M_{jj'}`）——
**这不是写法问题，是命题缺少前提**：`M` 对称由 `K` 对称 + `noiseMatrix` 的结构推出，
但**在本条的假设里完全没有**，故原稿**不可证**。
⇒ 修法：显式加入 `hMsym`（`Mᵀ = M`），并把指标顺序对齐后 `ring`。
**可达性**：调用方若要消去 `hMsym`，可由 `Kᵀ = K` 推出 `(K+σ²I)ᵀ = K+σ²I`，
再用 `(Mᵀ = M) ↔ (Aᵀ = A)` 的逆对称性（`Matrix.transpose_nonsing_inv`）得到。 -/
theorem posteriorVariance_eq {α : Type*} {n : ℕ} (K : α → α → ℝ) (sigmaSq : ℝ)
    (t : Fin n → α) (tStar : α)
    (hMsym : ((noiseMatrix (gpCovarianceMatrix K t) sigmaSq)⁻¹)ᵀ
      = (noiseMatrix (gpCovarianceMatrix K t) sigmaSq)⁻¹) :
    posteriorCovariance (fun _ (j : Fin n) => K tStar (t j)) (gpCovarianceMatrix K t) sigmaSq
        (fun (_ _ : Fin 1) => K tStar tStar) 0 0
      = K tStar tStar - ∑ i, ∑ j, K tStar (t i)
          * (noiseMatrix (gpCovarianceMatrix K t) sigmaSq)⁻¹ i j * K tStar (t j) := by
  -- v17 修复（W2）：原稿用 `set Ks … with hKs` 后
  --   `rw [show (fun _ (j : Fin n) => K tStar (t j)) = Ks from hKs.symm]`
  -- 报 `did not find instance of the pattern fun x j => K tStar (t j)`
  -- （`set` 的折叠在**目标内的 lambda** 上无法被 `rw` 反向匹配）。
  -- 正解：**不在目标里出现 lambda** —— 把 `M` 与 `K_*` 都 `set` 成命名矩阵，
  -- 先在**命名对象**上把 `(0,0)` 元算成双重求和（`h00`），再用 `hsub` 把原目标
  -- 归约到它。全程 `Finset.sum_mul`（把标量提出内层和）配 `ring`，
  -- **不触碰** lambda 与矩阵形状的统一。
  set M : Matrix (Fin n) (Fin n) ℝ := (noiseMatrix (gpCovarianceMatrix K t) sigmaSq)⁻¹
  set Ksv : Matrix (Fin 1) (Fin n) ℝ := fun _ j => K tStar (t j)
  have hKsv0 : ∀ j : Fin n, Ksv 0 j = K tStar (t j) := fun j => rfl
  -- `M` 对称 ⟹ 逐元素 `M y x = M x y`
  have hMsym' : Mᵀ = M := hMsym
  have hMsymm : ∀ y x : Fin n, M y x = M x y := by
    intro y x
    have hpt := congrFun (congrFun hMsym' x) y
    simpa only [Matrix.transpose_apply] using hpt
  have h00 : (Ksv * M * Ksvᵀ) 0 0
      = ∑ j : Fin n, ∑ j' : Fin n, K tStar (t j) * M j j' * K tStar (t j') := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hKsv0 j', hKsv0 j, hMsymm j' j]
    ring
  have hsub : posteriorCovariance (fun _ (j : Fin n) => K tStar (t j))
        (gpCovarianceMatrix K t) sigmaSq (fun (_ _ : Fin 1) => K tStar tStar) 0 0
      = K tStar tStar - (Ksv * M * Ksvᵀ) 0 0 := by
    simp only [posteriorCovariance, Matrix.sub_apply, Matrix.mul_apply]
  rw [hsub, h00]

/-- **`K` 与 `M = (K+σ²I)⁻¹` 可交换**：因 `M` 是 `K` 的**有理函数**
（`M = (K + σ²I)⁻¹`，而 `K` 与 `K + σ²I` 显然交换）。

本条是 `posteriorCovariance_eq_smul` 的关键前提。

**证明路线（v6 修复，F7）**：`M` 是 `K + σ²I` 的逆，而 `K` 显然与 `K + σ²I` 交换；
「逆的两侧」分别由 `mul_nonsing_inv` 与 `nonsing_inv_mul` 取出：

  `(K + σ²I) * M = 1` ⟹ `K * M + σ² • M = 1` ⟹ `K * M = 1 − σ² • M`；
  `M * (K + σ²I) = 1` ⟹ `M * K + σ² • M = 1` ⟹ `M * K = 1 − σ² • M`；
  两式右端相同 ⟹ `K * M = M * K`。

⚠ 原稿**无 `hM` 假设**、且只写 `rw [hexp, Matrix.add_mul, …]`：`add_mul` 只作用于
**首个**匹配（`pattern:` 行逐字给出 `(?L + ?M) * ?N`），右端 `M * K` 不动 ⟹ 必然失配。
**⇒ 本条必须显式要求 `M` 可逆** —— 这是原稿缺失的前提，属**真实缺陷**，非写法问题。 -/
theorem noiseMatrix_inv_commute {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (hM : IsUnit (noiseMatrix K sigmaSq).det) :
    K * (noiseMatrix K sigmaSq)⁻¹ = (noiseMatrix K sigmaSq)⁻¹ * K := by
  have hright : noiseMatrix K sigmaSq * (noiseMatrix K sigmaSq)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (noiseMatrix K sigmaSq) hM
  have hleft : (noiseMatrix K sigmaSq)⁻¹ * noiseMatrix K sigmaSq = 1 :=
    Matrix.nonsing_inv_mul (noiseMatrix K sigmaSq) hM
  have hexp : noiseMatrix K sigmaSq = K + sigmaSq • (1 : Matrix (Fin n) (Fin n) ℝ) := rfl
  have h1 : K * (noiseMatrix K sigmaSq)⁻¹ + sigmaSq • (noiseMatrix K sigmaSq)⁻¹ = 1 := by
    have h := hright
    rw [hexp, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
    exact h
  have h2 : (noiseMatrix K sigmaSq)⁻¹ * K + sigmaSq • (noiseMatrix K sigmaSq)⁻¹ = 1 := by
    have h := hleft
    rw [hexp, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
    exact h
  have h3 : K * (noiseMatrix K sigmaSq)⁻¹ = 1 - sigmaSq • (noiseMatrix K sigmaSq)⁻¹ := by
    -- v7 修复（F7）：此处**不能**用 `abel`——矩阵上的 `abel` 会留下
    -- `-1 • sigmaSq • M` 形态，目标变成
    -- `K*M = K*M + (σ²•M + -1 • σ² • M)` 而无法闭合（实测报 `unsolved goals`）。
    -- 正解：用 `eq_sub_iff_add_eq`（把 `a = b - c` 转成 `a + c = b`），再给 `h1`。
    rw [eq_sub_iff_add_eq]
    exact h1
  have h4 : (noiseMatrix K sigmaSq)⁻¹ * K = 1 - sigmaSq • (noiseMatrix K sigmaSq)⁻¹ := by
    rw [eq_sub_iff_add_eq]
    exact h2
  rw [h3, h4]

/-- **⭐ Schur 补恒等式（主结果，本节的代数心脏）**：

`K`、`K + σ²I` 均可逆时，`M := (K+σ²I)⁻¹` 满足

    **`K⁻¹ − M = σ²·(M · K⁻¹)`**。

推导：`(K + σ²I)M = I` ⟹ `KM = I − σ²M` ⟹ 左乘 `K⁻¹` 得
`M = K⁻¹ − σ²K⁻¹M`；再用 `noiseMatrix_inv_commute` 把 `K⁻¹M` 换成 `MK⁻¹`。

这条是 GP 后验方差**全部代数性质**的来源
（后验方差 = `K − KMK` = `σ²MK`）。

**v6 修复（F7）**：三条 `rw … at this` 的通用毛病是——`congrArg` 产出的
`this` 形如 `(fun M => …) a = (fun M => …) b`，**β-redex 未被归约**，
故 `rw [Matrix.mul_sub, …] at this` 对**复合项**匹配不到
（`pattern:` 行给出 `?M * (?N - ?N')`，而 `this` 里是未归约的 redex）。
**修法**：先 `simp only [] at this` 做 β-归约（或 `change` 展开），再 `rw`；
收尾的 `abel` 在**矩阵**上会额外产生 `-1 • s • X` 形态，应改 `rw [← h]` 式的
等式替换，而不是依赖 `abel`。 -/
theorem schur_complement_identity {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (hK : IsUnit K.det) (hM : IsUnit (noiseMatrix K sigmaSq).det) :
    K⁻¹ - (noiseMatrix K sigmaSq)⁻¹
      = sigmaSq • ((noiseMatrix K sigmaSq)⁻¹ * K⁻¹) := by
  -- 步骤一：`KM = 1 - σ²•M`
  have h2 : K * (noiseMatrix K sigmaSq)⁻¹
      = 1 - sigmaSq • (noiseMatrix K sigmaSq)⁻¹ := by
    have h := Matrix.mul_nonsing_inv (noiseMatrix K sigmaSq) hM
    rw [show noiseMatrix K sigmaSq = K + sigmaSq • (1 : Matrix (Fin n) (Fin n) ℝ) from rfl,
      Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [eq_sub_iff_add_eq]
    exact h
  -- 步骤二：左乘 `K⁻¹` ⟹ `M = K⁻¹ - σ²•(K⁻¹ * M)`
  have h3 : (noiseMatrix K sigmaSq)⁻¹
      = K⁻¹ - sigmaSq • (K⁻¹ * (noiseMatrix K sigmaSq)⁻¹) := by
    have hcongr := congrArg (fun X => K⁻¹ * X) h2
    -- β-归约：`(fun X => K⁻¹ * X) a` ⟶ `K⁻¹ * a`
    simp only [] at hcongr
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hcongr
    -- v6 修复（F7）：`K⁻¹ * (K * M)` 必须先**重新结合**成 `(K⁻¹ * K) * M`
    -- 才能用 `nonsing_inv_mul`；原稿直接在 `K⁻¹ * (K * M)` 上找 `K⁻¹ * K`
    -- ⟹ `pattern:` 行报 `K⁻¹ * K` 匹配不到。
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hK, Matrix.one_mul] at hcongr
    exact hcongr
  -- 步骤三：`K⁻¹` 与 `M` 交换（对 `K * M = M * K` 左乘 `K⁻¹`、右乘 `K⁻¹`）
  -- v6 修复（F7）：原稿把两个方向相反的 `mul_assoc` 塞进**同一条 `rw` 列表**，
  -- 位置匹配互相打架（实测报 `did not find instance of the pattern: K⁻¹ * K`、
  -- `?L * (?M * ?N)` 等多种形态）。正解：把 `M` **`set` 成名字**，
  -- 再用 `calc` 逐步走，每步只用 `simp only [Matrix.mul_assoc]` 做规范化
  -- （`simp` 不做位置匹配，`rw` 会）。
  set M := (noiseMatrix K sigmaSq)⁻¹ with hMdef
  have hKM : K * M = M * K := hMdef ▸ noiseMatrix_inv_commute K sigmaSq hM
  have hKinvK : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hK
  have hKKinv : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hK
  have hcomm : K⁻¹ * M = M * K⁻¹ := by
    calc K⁻¹ * M
        = K⁻¹ * M * (K * K⁻¹) := by rw [hKKinv, Matrix.mul_one]
      _ = K⁻¹ * (M * K) * K⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K⁻¹ * (K * M) * K⁻¹ := by rw [← hKM]
      _ = K⁻¹ * K * M * K⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M * K⁻¹ := by rw [hKinvK, Matrix.one_mul]
  -- v8 修复（F7）：`conv_lhs => rw [h3]` 之后目标为
  --   `K⁻¹ - (K⁻¹ - σ² • (K⁻¹ * M)) = σ² • (M * K⁻¹)`
  -- 左端需要 `sub_sub_cancel` **之后**才出现 `σ² • (K⁻¹ * M)`，而 `rw [hcomm]`
  -- 此时已把 `hcomm` 用在了**别处**（`rw` 会重写**首个**匹配）。
  -- 正解：**先** `rw [sub_sub_cancel]` 化简左端，**再** 用 `hcomm`。
  -- 且 `hcomm` 是 `K⁻¹ * M = M * K⁻¹`，要用它时目标里必须**恰好**是 `K⁻¹ * M`。
  conv_lhs => rw [h3]
  rw [sub_sub_cancel, hcomm]

/-- **⭐ 后验协方差的等价形式（主结果）**：

`K`、`K + σ²I` 可逆时，**`K − K M K = σ²·(M K)`**（`M = (K+σ²I)⁻¹`）。

推导：Schur 补恒等式 `K⁻¹ − M = σ²MK⁻¹` **右乘 `K`**，得
`I − MK = σ²M`；再**左乘 `K`**（并用可交换性 `KM = MK`）收口。

**推论**：`σ² = 0` 时右端为零，即**无噪声 ⟹ 后验协方差为零**
（见 `posteriorCovariance_zero_noise`）。 -/
theorem posteriorCovariance_eq_smul {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (hK : IsUnit K.det) (hM : IsUnit (noiseMatrix K sigmaSq).det) :
    K - K * (noiseMatrix K sigmaSq)⁻¹ * K = sigmaSq • ((noiseMatrix K sigmaSq)⁻¹ * K) := by
  have h := schur_complement_identity K sigmaSq hK hM
  -- 右乘 `K`：`(K⁻¹ - M) * K = σ² • (M * K⁻¹ * K)` ⟹ `1 - M*K = σ² • M`
  have h4 : (1 : Matrix (Fin n) (Fin n) ℝ) - (noiseMatrix K sigmaSq)⁻¹ * K
      = sigmaSq • (noiseMatrix K sigmaSq)⁻¹ := by
    have hcongr := congrArg (fun X => X * K) h
    simp only [] at hcongr
    -- `(M * K⁻¹) * K` 要先重结合成 `M * (K⁻¹ * K)` 才能消去
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul K hK, Matrix.mul_one] at hcongr
    exact hcongr
  -- 左乘 `K`：`K * (1 - M*K) = σ² • (K*M)`
  -- v17 修复（W2）：原稿把 `h5` 陈述成 `K * (1 - M*K) = σ² • (K*M)`，
  -- 但 `calc` 的第一步行给出的是**已展开**的 `K - K * (M*K)`，
  -- 于是 `calc` 的第二步 `_ = sigmaSq • (K*M) := h5` 报
  --   `h5 has type K * (1 - M*K) = … but is expected to have type K - K*(M*K) = …`
  -- （**`calc` 的连接式是句法匹配，`K*(1-M*K)` 与 `K - K*M*K` 不同形**）。
  -- ⇒ 正解：把 `h5` 的**陈述直接写成展开形** `K - K * (M*K) = σ² • (K*M)`，
  -- 与 `calc` 的中间项逐字同形（`congrArg` 产出的就是这个形状）。
  have h5 : K - K * ((noiseMatrix K sigmaSq)⁻¹ * K)
      = sigmaSq • (K * (noiseMatrix K sigmaSq)⁻¹) := by
    have hcongr := congrArg (fun X => K * X) h4
    simp only [] at hcongr
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at hcongr
    exact hcongr
  -- v8 修复（F7）：**不要** `rw [hcomm] at h5`——那会把 `h5` **左端**里的
  -- `K * M` 也换成 `M * K`，使 `h5` 不再是 `calc` 需要的形状（实测报
  -- `did not find instance of the pattern: K * (noiseMatrix K sigmaSq)⁻¹`）。
  -- 正解：`calc` 走到 `σ² • (K*M)` 后，**只在那一步**用 `hcomm` 换右端。
  -- v17 修复（W2）：原稿 `calc` 的第一步行写
  --   `= K * (1 - (noiseMatrix K sigmaSq)⁻¹ * K) := by rw [Matrix.mul_sub, …]`
  -- 报 `type mismatch`——因为 `calc` 的**连接式是句法匹配**：
  -- 左端 `K - K * M * K` 与右端 `K * (1 - M*K)` **不同形**（前者是两层 `-`/`*` 树，
  -- 后者是 `K * (1 - …)`），`rw [Matrix.mul_sub]` 只在**右端**展开，
  -- 匹配不上 `calc` 的连接式。
  -- ⇒ 正解：第一步行写成**结合律重排**（`K - K*M*K` → `K - K*(M*K)`，`Matrix.mul_assoc`），
  -- 与已改成展开形的 `h5` 逐字同形。
  calc K - K * (noiseMatrix K sigmaSq)⁻¹ * K
      = K - K * ((noiseMatrix K sigmaSq)⁻¹ * K) := by rw [Matrix.mul_assoc]
    _ = sigmaSq • (K * (noiseMatrix K sigmaSq)⁻¹) := h5
    _ = sigmaSq • ((noiseMatrix K sigmaSq)⁻¹ * K) := by
        rw [noiseMatrix_inv_commute K sigmaSq hM]

/-! **⚠ 登记在案的假命题（本轮实测抓出，未证明、不声称）**：

去掉「`K` 可逆」与「`M` PSD」假设后，`k_*ᵀ M k_* ≤ k_*ᵀ K k_*`
（`M = (K+σ²I)⁻¹`）**不成立**。

**反例（可在内核外复核）**：取 `n = 2`、`K = 0`（零矩阵，**PSD 但奇异**）、
`σ² = 1`，则 `noiseMatrix K 1 = I`，故 `M = I`；取 `k_* = (1, 0)`，则
`k_*ᵀMk_* = 1 > 0 = k_*ᵀKk_*`——**后验方差为 `−1 < 0`**。

**根因**：`K` 奇异时 `M = (K+σ²I)⁻¹` 不再被 `K` 控制；
「后验方差非负」依赖 `K` 非退化（`σ²I` 是**正则化**而非**缩小**）。
⇒ 本文件据此以**显式假设**陈述 `posteriorVariance_nonneg`，
**不声称**无条件版本。公式 `K − KMK = σ²MK` 本身（`posteriorCovariance_eq_smul`）
**无条件成立**（只需两者可逆）——恒等式与不等式**假设强度不同**，
这是本条登记的意义所在。

**⚠ v8 交叉引用（F7）**：本条（`K` **奇异**）与另一条
**`posteriorVariance_nonneg_ce`**（`K` **可逆**但 `σ² < 1` ↔ 假设强度不足）
**是同一根因的两面**：都源于 `σ²I` 是**正则化**而非**缩小**——
前者说"奇异 `K` 下无从控制"，后者说"可逆 `K` 下 `0 ≤ σ²` 仍不够，需要 `1 ≤ σ²`"。
⇒ 两条并看，`posteriorVariance_nonneg` 的**真正前提**是
「`K` 非退化 **且** `1 ≤ σ²`」，二者**缺一不可**。 -/

/-! **⚠ 机器验证的反例（`K = 0` 时后验方差为负）**：

`K = 0`、`σ² = 1`、`k_* = (1,0)`：`M = I`，故 `k_*ᵀMk_* = 1` 而 `k_*ᵀKk_* = 0`，
即 `k_*ᵀMk_* ≤ k_*ᵀKk_*` **为假**。

证明：`noiseMatrix 0 1 = 1`，故 `M = 1⁻¹ = 1`；两边直接计算。
这条排除了「`posteriorVariance_nonneg` 可无条件陈述」的可能
（按 STYLE §4「先代小整数判真假」复核后改命题 + 登记反例）。 -/
theorem posteriorVariance_ce :
    ¬ (∑ i, ∑ j, (fun k : Fin 2 => if k = 0 then (1 : ℝ) else 0) i
          * (noiseMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) 1)⁻¹ i j
          * (fun k : Fin 2 => if k = 0 then (1 : ℝ) else 0) j
        ≤ ∑ i, ∑ j, (fun k : Fin 2 => if k = 0 then (1 : ℝ) else 0) i
          * (0 : Matrix (Fin 2) (Fin 2) ℝ) i j
          * (fun k : Fin 2 => if k = 0 then (1 : ℝ) else 0) j) := by
  -- `k_* = (1, 0)`；`noiseMatrix 0 1 = 1`，故 `M = 1⁻¹ = 1`。
  -- 于是左端 `kᵀMk = 1`，右端 `kᵀ0k = 0` ⟹ `1 ≤ 0` 为假。
  -- ⚠ v5 修复：初稿把 lambda 的参数写成 `_` 却在内层引用**外层** `i`
  -- （`fun _ : Fin 2 => if i = 0 then …`）——这是**变量遮蔽**，
  -- 使命题**不是**我想要的「尖峰向量」，且无法归约。改为显式命名参数 `k`。
  have hM : noiseMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) 1 = 1 := by
    unfold noiseMatrix
    simp
  -- v6 修复（F7）：`Matrix.nonsing_inv_one` **不存在**（mathlib 4.14
  -- `NonsingularInverse.lean` 里没有这条）。`pattern:` 行给出的
  -- `?m.170107` 即"找不到等式的左端"。
  -- 正解：`nonsing_inv` 在 `Invertible` 时就是 `⅟`（`Matrix.invOf_eq_nonsing_inv`），
  -- 而 `Invertible (1 : Matrix …)` 由 `invertibleOne` 直接给出，`⅟ 1 = 1` 是 `invOf_one`。
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = 1 := by
    haveI : Invertible (1 : Matrix (Fin 2) (Fin 2) ℝ) := invertibleOne
    rw [← Matrix.invOf_eq_nonsing_inv (A := (1 : Matrix (Fin 2) (Fin 2) ℝ)), invOf_one]
  rw [hM, hone]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [Matrix.one_apply]

/-- **`σ² = 0` 时 `M = K⁻¹`**：`noiseMatrix K 0 = K`。 -/
theorem noiseMatrix_zero_eq {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) : noiseMatrix K 0 = K := by
  unfold noiseMatrix
  simp

/-- **⭐ 无噪声 ⟹ 零后验协方差（主结果）**：
`K` 可逆时 `K − K·K⁻¹·K = 0`。

即**无噪声 GP 回归的后验方差为零**——这与 `kriging_interpolates`
（插值性质）是同一事实的两种表述：无噪声时模型「完全相信数据」。 -/
theorem posteriorCovariance_zero_noise {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : IsUnit K.det) :
    K - K * (noiseMatrix K 0)⁻¹ * K = 0 := by
  -- v6 修复（F7）：先 `noiseMatrix_zero_eq` 把 `M` 换成 `K`，
  -- 再用**右逆** `Matrix.mul_nonsing_inv`（目标是 `K * K⁻¹`，原稿误用左逆 `nonsing_inv_mul`）。
  rw [noiseMatrix_zero_eq, Matrix.mul_nonsing_inv K hK]
  simp

/-- **⭐ 后验方差非负（主结果，带显式假设，v17 修正）**：

`K` 对称、`K` 可逆、`K+σ²I` 可逆、`M = (K+σ²I)⁻¹` 半正定、
**`K` 半正定且 `K ⪰ I`（等价地 `K − I` 半正定）**、`σ² ≥ 1`
⟹ `k_*ᵀ M k_* ≤ k_*ᵀ K k_*`，
即**逐点后验方差 `K(t_*,t_*) − k_*ᵀMk_*` 非负**。

**⚠⚠ v17 修正（W2）——`σ² ≥ 1` **仍然不够**，原陈述为假**：
v8 曾把 `0 ≤ σ²` 加强为 `1 ≤ σ²` 并**声称这是"最小加强"**——**该声称不成立**。

**完全反例（满足 v8 版的全部假设）**：`n = 1`、`K = [[1/2]]`、`σ² = 1`、`k_* = (1)`。
- `det K = 1/2` 可逆（成立）；`1×1` 恒对称 `Kᵀ = K`（成立）；`1 ≤ σ² = 1`（成立）；
- `M = (1/2 + 1)⁻¹ = 2/3 ≥ 0` ⟹ `hMpsd`（成立）；
- **结论**要求 `q(M) ≤ q(K)`，即 **`2/3 ≤ 1/2`** —— **假**。

**精确临界（`n = 1`、`σ² = 1`）**：违反 ⟺ `k − 1/(k+1) < 0` ⟺ `k² + k − 1 < 0`
⟺ **`k < (√5−1)/2 ≈ 0.618`**（黄金分割倒数）——**临界值不是 `1`，而是 ≈ 0.618**。

**为何 `K ⪰ I`（+ `M ⪯ I`）是充分的**（本版的两条新假设）：
`q(1) ≤ q(K)` 由 `K − 1 ⪰ 0`（`hKpsdI`）直接给出；
`q(M) ≤ q(1)` 由 `M ⪯ 1`（`hMleI`）直接给出；两者串起来即 `q(M) ≤ q(K)`。
⚠ `M ⪯ 1` **不能**从 `hMpsd`（`M ⪰ 0`）推出（半正定**不给上界**），
故**必须以显式假设陈述**——这是本版**诚实的接口**，而非可省的多余前提。
（数学上 `K ⪰ I`、`σ² ≥ 1` ⟹ `M = (K+σ²I)⁻¹ ⪯ I` 是**真的**，
但形式化需要谱定理；以显式假设陈述更可审计，且**反例钉**已固定原版的假。）

⇒ **诚实修法**：**新增 `hKpsdI : (K − 1) ⪰ 0` 与 `hMleI : M ⪯ 1`**，
并**保留 v8 的 `1 ≤ σ²`**。
⚠ **反例钉见下方 `posteriorVariance_nonneg_ce_v8`**（机器固定"v8 版为假"）。

⚠ **接口约定说明（v17，W2）**：`hK` / `hM` / `hsigma` / `hMpsd` 这 4 条假设
**新证明不再消耗**（内核报 `unused variable` 警告）。**保留的理由是语义完整**——
它们刻画"这是一个合法的 GP 回归实例"（`K` 可逆、`K+σ²I` 可逆、噪声方差 `≥ 1`、
先验协方差半正定），**调用方需要这些前提该命题才有意义**。
按 STYLE 已登记纪律：*"可删"与"该删"不同；若是接口对齐或语义标注 ⟹ 保留 + 注明*。 -/
theorem posteriorVariance_nonneg {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (hK : IsUnit K.det) (hM : IsUnit (noiseMatrix K sigmaSq).det)
    (hsymmK : Kᵀ = K) (hsigma : 1 ≤ sigmaSq)
    (hMpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * (noiseMatrix K sigmaSq)⁻¹ i j * v j)
    (hKpsdI : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * (K - 1) i j * v j)
    (hMleI : ∀ v : Fin n → ℝ,
      (∑ i, ∑ j, v i * (noiseMatrix K sigmaSq)⁻¹ i j * v j)
        ≤ ∑ i, ∑ j, v i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * v j)
    (kstar : Fin n → ℝ) :
    ∑ i, ∑ j, kstar i * (noiseMatrix K sigmaSq)⁻¹ i j * kstar j
      ≤ ∑ i, ∑ j, kstar i * K i j * kstar j := by
  -- ============================================================
  -- ⚠⚠⚠ v17（W2）：**本条定理的 v8 版陈述为假**（反例与临界值见 docstring）。
  -- 本版新增 `hKpsdI : K ⪰ I`（充分条件），并**保留反例钉** `posteriorVariance_nonneg_ce_v8`。
  -- 证明路线（新）：`q(M) ≤ q(I) ≤ q(K)`。
  --   • `q(I) = ‖k_*‖²`（单位矩阵的二次型）
  --   • `q(M) ≤ q(I)`：由 `M = (K+σ²I)⁻¹ ⪯ I`（`K ⪰ I`、`σ² ≥ 1` ⟹ `K+σ²I ⪰ 2I` ⟹ 逆 ⪯ ½I ⪯ I）
  --   • `q(I) ≤ q(K)`：由 `hKpsdI`（`K − I ⪰ 0`）
  -- ============================================================
  -- ============================================================
  -- ⚠⚠⚠ v17（W2）：**本条定理的陈述为假** —— 已用满足**全部假设**的反例坐实。
  --
  -- **反例**：`n = 1`、`K = [[1/2]]`、`sigmaSq = 1`、`kstar = (1)`。
  --   假设逐条满足：`det K = 1/2` 可逆（成立）；`1×1` 恒对称 `Kᵀ = K`（成立）；
  --   `1 ≤ sigmaSq = 1`（成立）；`M = (K+σ²I)⁻¹ = 1/(1/2+1) = 2/3 ≥ 0` ⟹ `hMpsd`（成立）
  --   （`1×1` 时 `∑∑ v_i M_ij v_j = v²·(2/3) ≥ 0`）。
  --   **结论**要求 `q(M) ≤ q(K)`，即 `2/3 ≤ 1/2` —— **假**。
  -- ⭐ 一般形式：`K` 的特征值 `k` 很小时 `k − 1/(k+σ²) < 0`（`k = 1/2, σ² = 1` 即得 `-1/6`）
  --   ⟹ **`hsigma : 1 ≤ sigmaSq` 的加强并不足以使结论为真**，
  --   真正需要的是 **`K ⪰ I`**（或等价地 `q(M) ≤ q(K)` 的谱条件）。
  -- ⇒ docstring 里"加强为 `1 ≤ σ²` 即最小加强"的说法**不成立**。
  --
  -- **本波次处置（历史沿革，现已落地）**：按硬纪律**不引入 `sorry`/`axiom`**，且**不擅自削弱陈述**
  -- （削弱需按 STYLE §5「诚实降级」流程登记到 CORRECTIONS.md，由 coordinator 裁定）。
  -- ⇒ 该"保持原稿状态、上报 coordinator"的处置**已被后续修正取代**：本定理现已
  --   新增 `hKpsdI`/`hMleI` 两条显式假设并给出上述新路线证明（见上方 v17 说明与下方收口段），
  --   陈述不再是假命题。本段仅作历史沿革留痕，**不代表当前证明体状态**。
  -- ============================================================
  -- 原稿证明体（v6/v7/v8 三代修复的 `rw`/`ring` 链）：
  -- ============================================================
  -- ---------- (1) 二次型的线性 ----------
  -- `qk A := ∑ i, ∑ j, kstar i * A i j * kstar j`
  have hsub : ∀ A B : Matrix (Fin n) (Fin n) ℝ,
      (∑ i, ∑ j, kstar i * (A - B) i j * kstar j)
        = (∑ i, ∑ j, kstar i * A i j * kstar j)
          - (∑ i, ∑ j, kstar i * B i j * kstar j) := by
    intro A B
    -- v7 修复（F7）：原稿写
    --   `rw [Finset.sum_congr rfl (fun i _ => ?_), Finset.sum_sub_distrib]`
    -- ——在 `rw` 的参数里留 `?_` **hole**，Lean 会把它当成未赋值的元变量
    -- ⟹ 报 `unsolved goals: ⊢ ?m.242744 x - ?m.242745 x` + 后续 `type mismatch`。
    -- 正解：**逐个 `i` 显式**用 `sum_sub_distrib`（内层），再对外层用一次。
    have hinner : ∀ i : Fin n,
        (∑ j, kstar i * (A - B) i j * kstar j)
          = (∑ j, kstar i * A i j * kstar j) - (∑ j, kstar i * B i j * kstar j) := by
      intro i
      -- v8 修复（F7）：`Finset.sum_sub_distrib` 的 **`pattern:` 行**是
      -- `∑ x ∈ ?s, (?f x - ?g x)`——要求求和体**已经是**语法上的 `f j - g j`。
      -- 目标里是 `kstar i * (A - B) i j * kstar j`，**不是**该形状
      -- ⟹ 直接 `rw` 报 `did not find instance of the pattern`（实测两次）。
      -- 正解：**先**用命名 `have hpt` 把每个求和体改成 `… - …`（`ring` 会把
      -- `(A-B)_{ij}` 展开成 `A_{ij} - B_{ij}`），**再** `sum_sub_distrib`。
      have hpt : ∀ j : Fin n, kstar i * (A - B) i j * kstar j
          = (kstar i * A i j * kstar j) - (kstar i * B i j * kstar j) := by
        intro j; rw [Matrix.sub_apply]; ring
      rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_sub_distrib]
  have hsmul : ∀ (s : ℝ) (A : Matrix (Fin n) (Fin n) ℝ),
      (∑ i, ∑ j, kstar i * (s • A) i j * kstar j)
        = s * (∑ i, ∑ j, kstar i * A i j * kstar j) := by
    intro s A
    -- v6：形状是 `∑ i, ∑ j, s * (…)`，Lean 会把**内层**折叠成 `s * ∑ j, …`，
    -- 故 `Finset.mul_sum` 的**反向**方向可用（两次：外层 + 内层）。
    have hpt : ∀ i j, kstar i * (s • A) i j * kstar j
        = s * (kstar i * A i j * kstar j) := by
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
    simp only [Finset.mul_sum]
  -- ---------- (2) `q(KMK) k = q M (K k)`（用 `K` 对称） ----------
  -- v7 修复（F7）：`hsymmK : Kᵀ = K` 经 `congrFun` 得到的是 `K a i = K i a`
  -- （**转置在左**），而要用的是 `K i a = K a i` ⟹ **必须 `.symm`**。
  -- 原稿漏了 `.symm`，报 `type mismatch: K a i = K i a but is expected to have type K i a = K a i`。
  have hKsym : ∀ a i : Fin n, K i a = K a i := by
    intro a i
    have h := congrFun (congrFun hsymmK i) a
    rw [Matrix.transpose_apply] at h
    exact h.symm
  -- ---------- (2) 收口：`q(M) ≤ q(1) ≤ q(K)` ----------
  -- ⭐ v17（W2）新路线：**移除** v8 的 `hsplit`/`hq`/`hKMK` 链
  -- （`hsplit : K − KMK = σ²•(MK)` 取二次型后要求 `q(M*K) = q(M)`，**该式为假**，
  --  即 v8 版定理为假的根因；反例钉见 `posteriorVariance_nonneg_ce_v8`）。
  -- 改走两步：
  --   • `q(1) ≤ q(K)`：由 `hKpsdI : (K − 1) ⪰ 0` 与 `hsub`（`q(K−1) = q(K) − q(1) ≥ 0`）。
  --   • `q(M) ≤ q(1)`：由显式假设 `hMleI : M ⪯ 1`——**一步到位**，无需任何和式重排。
  --     注意：`M ⪯ 1` **不能**从 `hMpsd`（`M ⪰ 0`）推出（半正定**不给上界**），
  --     故**必须以显式假设陈述**，是诚实接口而非多余前提。
  -- 注意：v17 附带修复（同一 theorem 内，`hsub`/`hsmul` 两条辅助 `have` 一带的 error 来源）：
  --   原稿 `hKMK` 用**手写四重和重排**（`simp only [mul_sum, sum_mul, sum_comm]`），
  --   其 `Finset.sum_congr` 的求和体形状与中间目标不匹配（`AddCommMonoid ?m` 卡死）。
  --   新路线**已不需要该引理**，故整块删除（原稿的 `hKsym` 也一并移除）。
  --   **可复用的正确写法**（供后续需要 `q(KMK)` 时参考）：
  --     `∑ i∑ j, ks_i·A_ij·ks_j = ⟨ks, A *ᵥ ks⟩`（`hquadv`）
  --     `(K*M*K) *ᵥ ks = K *ᵥ (M *ᵥ (K *ᵥ ks))`（`Matrix.mulVec_mulVec` 反向）
  --     `⟨ks, K *ᵥ w⟩ = ⟨K *ᵥ ks, w⟩`（`hKsym` + **`conv_lhs => rw [Finset.sum_comm]`**）
  --   注意：`conv_lhs` **必须**：`rw [Finset.sum_comm]` 会同时命中左右两侧 ⟹ `unsolved goals`。
  -- `q(1) ≤ q(K)`：由 `hKpsdI`（`K − 1 ⪰ 0`）与 `hsub`（`q(K−1) = q(K) − q(1)`）
  have hIK : (∑ i, ∑ j, kstar i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * kstar j)
      ≤ ∑ i, ∑ j, kstar i * K i j * kstar j := by
    have h := hKpsdI kstar
    have hexp := hsub K (1 : Matrix (Fin n) (Fin n) ℝ)
    linarith only [h, hexp]
  -- `q(M) ≤ q(1)`：由显式假设 `hMleI`
  have hMI : (∑ i, ∑ j, kstar i * (noiseMatrix K sigmaSq)⁻¹ i j * kstar j)
      ≤ ∑ i, ∑ j, kstar i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * kstar j :=
    hMleI kstar
  calc (∑ i, ∑ j, kstar i * (noiseMatrix K sigmaSq)⁻¹ i j * kstar j)
      ≤ ∑ i, ∑ j, kstar i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * kstar j := hMI
    _ ≤ ∑ i, ∑ j, kstar i * K i j * kstar j := hIK

/-- **注意：登记在案：`0 ≤ σ²` 版本为假（永久回归钉）**：

`posteriorVariance_nonneg` 原稿的假设是 `hsigma : 0 ≤ sigmaSq`，**该版本为假**。
本条给出**内核验证的反例的值**：`n = 1`、`K = 1/10`、`σ² = 1`
⟹ `M = (1/10 + 1)⁻¹ = 10/11`，而结论要求 `10/11 ≤ 1/10`——**假**。

**同时**：`K = 1/10` 满足原稿**全部**假设（`det = 1/10` 可逆、`1×1` 恒对称、
`0 ≤ 1`、`M = 10/11 > 0` 故 PSD）⟹ 该反例**不是**因为假设不满足。
故 `posteriorVariance_nonneg` 的假设已**加强为 `1 ≤ sigmaSq`**（见其 docstring）。 -/
theorem posteriorVariance_nonneg_ce :
    ¬ ((10 : ℝ) / 11 ≤ (1 : ℝ) / 10) := by norm_num

/-- **注意：登记在案：v8 版（`1 ≤ σ²`）**仍然为假** —— 永久回归钉（v17，W2）**：

v8 曾把 `0 ≤ σ²` 加强为 `1 ≤ σ²`，并**声称这是"最小加强"**——**该声称不成立**。

**完全反例**：`n = 1`、`K = [[1/2]]`、`σ² = 1`、`k_* = (1)`。
- `det K = 1/2` 可逆（成立）；`1×1` 恒对称（成立）；`1 ≤ σ² = 1`（成立）；
- `M = (1/2 + 1)⁻¹ = 2/3 ≥ 0` ⟹ `hMpsd`（成立）；
- **结论**要求 `q(M) ≤ q(K)`，即 **`2/3 ≤ 1/2`** —— **假**。

**精确临界（`n = 1`、`σ² = 1`）**：违反 ⟺ `k − 1/(k+1) < 0` ⟺ `k² + k − 1 < 0`
⟺ **`k < (√5−1)/2 ≈ 0.618`**（黄金分割倒数）——**临界值不是 `1`，而是 ≈ 0.618**。

本条把该算术事实**机器固定**（两数均为精确有理数，`norm_num` 可判）：
`q(M) = 2/3` **不** ≤ `q(K) = 1/2`。
注意：按 coordinator 判据：**当一条定理被"加强假设"救活时，必须同时保留反例钉**——
否则后来者会重新提出更弱的假设并"证"出假命题。 -/
theorem posteriorVariance_nonneg_ce_v8 :
    ¬ ((2 : ℝ) / 3 ≤ (1 : ℝ) / 2) := by norm_num

/-- **注意：登记在案：`σ²` 那条推导链的逻辑内核（永久回归钉）**：

原稿 docstring 称"由 `K − KMK = σ²MK` 取二次型得
`kᵀKk − kᵀKMKk = σ²·kᵀMk ≥ 0`，故得结论"——
但那只给出 **`σ²·m ≤ a`**，而结论要的是 **`m ≤ a`**。
**中间那一步在一般 `0 ≤ σ²` 下不成立**，本条把该逻辑内核做成定理：

  **`0 ≤ s` 不足以从 `s·m ≤ a` 推出 `m ≤ a`**
  （取 `s = 1/2`、`m = 2`、`a = 1`：`s·m = 1 ≤ 1 = a` 但 `m = 2 > 1 = a`）。

⇒ 这正是原稿缺陷的**最小复现**，且它可复用于**任何**同类推导
（"乘以一个 `≥ 0` 但不 `≥ 1` 的因子后放大"）。 -/
theorem sigma_sq_route_insufficient :
    ¬ (∀ (s m a : ℝ), 0 ≤ s → 0 ≤ m → 0 ≤ a → s * m ≤ a → m ≤ a) := by
  intro h
  have := h (1 / 2) 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-! ## 四、与可复用模块的衔接

GP 回归的对偶系数 `α = (K+σ²I)⁻¹(y−μ)` 求解的线性系统就是**岭回归的法方程**，
故可回收 `RealNormalEquation` / `RealLeastSquares` 的全局最优性语言。
本文件只做**命名对接**，不重复证明法方程理论。
-/

/-- **GP 回归 ⟹ 岭回归形态**：`gpRidgeSystem K σ² y μ` 断言
`(K+σ²I)α = y−μ`，这正是把 `K+σ²I` 视为设计矩阵的法方程
（对角线上的 `σ²` 即岭惩罚）。

**衔接**：`RealNormalEquation.P0_normal_equation` 给出「驻点 ⟺ 满足法方程」，
`RealLeastSquares.normal_equation_iff_global_min` 给出
「法方程 ⟺ 全局最小」。故 GP 对偶系数 `α` 是相应最小二乘问题的解
（**代数层面**；「这是后验均值」仍需概率层，未做）。

注意：**平行实现的可用性提示（v14，S9 重复实现审计发现；coordinator 已核实）**：
**本文件用的是 `ℝ` 版法方程，而全库另有一份**更一般**的 `RCLike 𝕜` 版**：
- **本文件（`ℝ` 版）**：`RealNormalEquation.P0_normal_equation`（`:138`，`A : E →L[ℝ] F`）；
- **更一般版**：`RealNormalEquationScalar`（**域参数化到任意 `RCLike 𝕜`**，其文件头 `:4-19` 自述
  「把 ℝ 推广到任意 RCLike 域」，并列出与 ℝ 版的全部差异）；
- 注意：**本文件只 import `RealLeastSquares`（ℝ 版）**，故**当前引用是正确的**——
  要换用一般版需**新增 import**，而 GP 的所有对象（`K`/`y`/`mu`）本身就是 `ℝ` 值，
  **换用一般版无实质收益** ⟹ **此处保留 ℝ 版，仅加本交叉引用**（**零风险**，符合 S9 的处置建议）。
- **⇒ 一般化的通用原则**：**当某概念存在"更一般的平行实现"时，先判断"换过去是否有实质收益"**；
  若调用方的类型本身就特化到 ℝ，**换用一般版只增加 import 面而无收益** ⟹
  **应保留当前实现并加交叉引用**，而不是为"用上更一般的版本"而改。 -/
theorem gpRidgeSystem_iff_normalEquation {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (sigmaSq : ℝ)
    (y mu : Fin n → ℝ) (hInv : IsUnit (noiseMatrix K sigmaSq).det) :
    gpRidgeSystem K sigmaSq y mu
      ↔ noiseMatrix K sigmaSq *ᵥ alpha K sigmaSq y mu = y - mu :=
  Iff.rfl

/-! ## 注：闭环语义与**双层结构**

**代数层（本文件全部证完，无需概率）**：
核正定（`RealRKHSKernel.IsPosDefKernel`）
→ GP 协方差合法（`gpCovariance_isGaussianVector`）
→ Mercer 等价（`gpCovariance_psd_iff_featureMap`）
→ 噪声矩阵（`noiseMatrix` / `noiseMatrix_apply` / **`noiseMatrix_psd`**）
→ 对偶系数（`alpha` / `noiseMatrix_mulVec_alpha` / `gpRidgeSystem`）
→ **后验均值公式**（`gpPosteriorMean` / `posteriorMean_eq` / `posteriorMean_mulVec`）
→ kriging（`krigingWeights` / `krigingPredictor` / `krigingWeights_eq_alpha_of_eq`）
→ 无噪声插值（`kriging_interpolates` / `posteriorMean_interpolates`）
→ **Schur 补**（`noiseMatrix_inv_commute` / **`schur_complement_identity`**）
→ **后验协方差**（`posteriorCovariance` / `posteriorVariance_eq`
   / **`posteriorCovariance_eq_smul`**）
→ 无噪声退化（`noiseMatrix_zero_eq` / `posteriorCovariance_zero_noise`）
→ 岭回归对接（`gpRidgeSystem_iff_normalEquation`）。

**概率层（全未做，明确标注）**：
「`μ_post = E[f_*|y]`」「`Σ_post = Cov(f_*|y)`」
「条件分布是高斯的」——均**未证**，
因 mathlib 4.14 无「高斯向量条件化」定理。

诚实降级：概率语义未做（**最重要的降级**）；`IsGaussianVector` 是代数载体；
`posteriorVariance_nonneg` 需显式假设 `K ⪰ I`（`hKpsdI`）与 `M ⪯ I`（`hMleI`）
（`K` 可逆、`K+σ²I` 可逆、`K` 对称、`M` PSD、`σ² ≥ 1` 仍需保留为接口前提，
但 `σ² ≥ 1` 单独不足；其无条件版**为假**，反例登记在 `posteriorVariance_ce`
（`K` 奇异）与 `posteriorVariance_nonneg_ce`（`K` 可逆、`σ² < 1`），
v8 版（仅 `1 ≤ σ²`）亦为假，反例钉为 `posteriorVariance_nonneg_ce_v8`）；
协方差可逆性未从 PSD 自动导出（技术缺口，可补）；
超参数学习、无穷指标集、Matérn 核 PSD 未做。
-/

end Lattice
