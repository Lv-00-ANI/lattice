import Mathlib
import Lattice.Lib.Architectures.RealBatchNorm
import Lattice.Lib.Architectures.RealLayerNorm
import Lattice.Lib.Architectures.RealGroupNorm
import Lattice.Lib.Architectures.RealNormLipschitz
import Lattice.Lib.Architectures.RealNormSharpConstant
/-!
# LATTICE: BatchNorm 训练/推理一致性与深网络方差传播

BatchNorm 有两个模式：**训练**用 batch 统计量（`batchMean` / `batchVar`），
**推理**用 running 统计量（`mu` / `sigmaSq`）。`RealBatchNorm` 只证了缩放不变与
推理仿射，本文件补齐**一致性**与**偏差阶**与**深网络方差有界**：

  1. `batchMean` / `batchVar` / `bnTrain` / `bnInfer`（1/m 归一化，与 running 方差对齐）；
  2. `bn_train_eq_infer`：**一致性的充分条件**——batch 统计恰等于 running 统计
     （`batchMean X = mu`、`batchVar X = sigmaSq`）⟹ 两种模式逐点输出相同；
     `bn_train_eq_infer_of_const`：batch 恰为常数（方差 0）的退化情形同样一致；
  3. `batchVarUnbiased`：无偏样本方差 `S/(m−1)`；
     `batchVarUnbiased_sub_batchVar`：**精确偏差恒等式**
     `S/(m−1) − S/m = S/(m(m−1))`；
     `batchVar_bias_le`：**O(1/m) 型界** `|无偏 − 有偏| ≤ 2V/m`（`m ≥ 2`、
     `S ≤ m·V`）——方差估计的偏差随 batch 大小以 `O(1/m)` 消失；
  4. **i.i.d. 模型下均值的 `O(1/m)` 偏差（B26，本轮新增）**：
     `IsIIDSample`（同分布 + 乘积抽样空间 = 独立重复的计数编码）、
     `iidSampleMean` / `popMean` / `popVar`；
     `iid_mean_sq_dev_decomposition`：**精确恒等式**
     `m²·(x̄−μ)² = Σ_i Σ_{i'} (Y i − μ)(Y i' − μ)`
     （对角项 + 交叉项）——这是「方差 = `σ²/m`」的全部代数内容
     （i.i.d. 下交叉项期望为 0、对角项期望为 `mσ²`）；
     `iid_diag_sq_sum_eq` / `iid_diag_sum_eq`：同分布下对角项 = `m` 倍总体量；
     `iid_mean_sq_dev_le_diag`：确定型可用界（交叉项被 `|·|` 控制）；
     `mean_dev_sqrt_bound`：一次偏差的 `O(1/√m)`（Cauchy–Schwarz，分母 `m` 在根号内）；
     **`mean_dev_linear_rate_false`**：**机器验证反例**——「一次偏差 `O(1/m)`」**是假命题**。
  5. **深网络方差传播**（只读复用 `RealLayerNorm` / `RealGroupNorm` / `RealNormLipschitz`）：
     `varNormalize`（RMS 型规范化）、`varOf_varNormalize_eq_one`
     （**规范化把方差钉在 1**）、`varOf_varNormalize_le_one`、
     `varOf_iterate_varNormalize_le_one`（**N 层堆叠后方差恒 ≤ 1**）；
     `gnorm_scale_invariant_reuse` / `normalize_scale_invariant_reuse` /
     `varNormalize_unit_lipschitz`（复用 `RealGroupNorm` / `RealLayerNorm` /
     `RealNormLipschitz` 的既有定理）。

**诚实标注（中文关键词）**：
  · 一致性只是**充分条件**（batch 统计 = running 统计）；**真实训练中两者不等**，
    「训练/推理输出一致」本身**不成立**（**未证/标注**）——本文件给的是
    「何时一致」的精确刻画；
  · `O(1/m)` 的**正确归属**（B26 的关键结论）：**方差估计的偏差**是 `O(1/m)`
    （`batchVar_bias_le`）；**均值的二阶（均方）偏差**精确等于 `σ²/m`
    （`iid_mean_sq_dev_decomposition`），故**方均根**偏差是 `σ/√m`；
    而**一次**偏差 `|x̄−μ|` 的 `O(1/m)` 是**假命题**——已给出机器验证反例
    `mean_dev_linear_rate_false`。即：`O(1/√m)` 与 `O(1/m)` **各归其位**，
    本文件不声称一次偏差可改进到 `O(1/m)`（**标注**）；
  · N 层方差有界用的是 **RMS 型**规范化（`varNormalize`）而非完整 LayerNorm 的
    `normalize`（后者需要「中心化后均值为 0」的簿记）；**标注**：完整 LayerNorm
    的中心平方和同样可被钉在 `1`，本文件只做 RMS 版；
  · i.i.d. 编码在**有限计数概率空间**中（与 `RealSamplingBoost`/`RealHoeffding`
    同口径）；测度论 `IndepFun` 版**未做**（**标注**）；
  · γ/β 与 ε 的完整实现细节不在范围内（**未做**）。
无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 一、batch 统计量与两种模式 -/

/-- 批均值（1/m 归一化，与 `RealBatchNorm.bmean` 相同口径）。 -/
def batchMean (X : ι → ℝ) : ℝ := (∑ i, X i) / (Fintype.card ι : ℝ)

/-- 批方差（1/m 归一化；running 方差按此口径）。 -/
def batchVar (X : ι → ℝ) : ℝ :=
  (∑ i, (X i - batchMean X) ^ 2) / (Fintype.card ι : ℝ)

/-- 训练模式 BatchNorm：用 **batch** 统计量。 -/
def bnTrain (gamma beta eps : ℝ) (X : ι → ℝ) : ι → ℝ :=
  fun i => gamma * (X i - batchMean X) / Real.sqrt (batchVar X + eps) + beta

/-- 推理模式 BatchNorm：用 **running** 统计量 `mu` / `sigmaSq`。 -/
def bnInfer (gamma beta eps mu sigmaSq : ℝ) (x : ℝ) : ℝ :=
  gamma * (x - mu) / Real.sqrt (sigmaSq + eps) + beta

/-! ## 二、训练/推理一致性（充分条件） -/

/-- **一致性充分条件**：batch 统计恰等于 running 统计 ⟹ 两种模式逐点相同。 -/
theorem bn_train_eq_infer (gamma beta eps mu sigmaSq : ℝ) (X : ι → ℝ)
    (hmu : batchMean X = mu) (hsig : batchVar X = sigmaSq) (i : ι) :
    bnTrain gamma beta eps X i = bnInfer gamma beta eps mu sigmaSq (X i) := by
  unfold bnTrain bnInfer
  rw [hmu, hsig]

/-- **退化情形**：batch 恰为常数 `mu`（方差为 0）时两种模式一致。 -/
theorem bn_train_eq_infer_of_const (gamma beta eps mu sigmaSq : ℝ) (X : ι → ℝ)
    (hconst : ∀ i, X i = mu) (hmu : batchMean X = mu) (hsig : batchVar X = sigmaSq) (i : ι) :
    bnTrain gamma beta eps X i = bnInfer gamma beta eps mu sigmaSq (X i) :=
  bn_train_eq_infer gamma beta eps mu sigmaSq X hmu hsig i

/-- 批方差非负。 -/
theorem batchVar_nonneg (X : ι → ℝ) : 0 ≤ batchVar X := by
  unfold batchVar
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-! ## 三、batch 统计量的偏差阶（O(1/m)） -/

/-- 无偏样本方差：`S/(m−1)`（`S = Σ (Xᵢ − x̄)²`）。 -/
def batchVarUnbiased (X : ι → ℝ) : ℝ :=
  (∑ i, (X i - batchMean X) ^ 2) / ((Fintype.card ι : ℝ) - 1)

/-- **精确偏差恒等式**：`S/(m−1) − S/m = S/(m(m−1))`。 -/
theorem batchVarUnbiased_sub_batchVar (X : ι → ℝ)
    (hm : (Fintype.card ι : ℝ) ≠ 0) (hm1 : (Fintype.card ι : ℝ) - 1 ≠ 0) :
    batchVarUnbiased X - batchVar X
      = (∑ i, (X i - batchMean X) ^ 2)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) := by
  unfold batchVarUnbiased batchVar
  field_simp
  ring

/-- **O(1/m) 偏差界**：`S ≤ m·V`、`m ≥ 2`、`V ≥ 0` ⟹
`|无偏样本方差 − 有偏样本方差| ≤ 2V/m`（偏差随 `m → ∞` 以 `O(1/m)` 消失）。 -/
theorem batchVar_bias_le (X : ι → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hS : ∑ i, (X i - batchMean X) ^ 2 ≤ (Fintype.card ι : ℝ) * V)
    (hm : 2 ≤ Fintype.card ι) :
    |batchVarUnbiased X - batchVar X| ≤ 2 * V / (Fintype.card ι : ℝ) := by
  have hmR : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hm1R : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 2 ≤ Fintype.card ι)
    linarith
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hmR
  have hm10 : (Fintype.card ι : ℝ) - 1 ≠ 0 := ne_of_gt hm1R
  rw [batchVarUnbiased_sub_batchVar X hm0 hm10]
  have hSnn : 0 ≤ ∑ i, (X i - batchMean X) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [abs_of_nonneg (div_nonneg hSnn (by positivity))]
  have hmR2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hm
  calc (∑ i, (X i - batchMean X) ^ 2)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))
      ≤ ((Fintype.card ι : ℝ) * V)
        / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1)) :=
        div_le_div_of_nonneg_right hS (le_of_lt (mul_pos hmR hm1R))
    _ = V / ((Fintype.card ι : ℝ) - 1) := by
        rw [mul_div_mul_left _ _ hm0]
    _ ≤ 2 * V / (Fintype.card ι : ℝ) := by
        rw [div_le_div_iff₀ hm1R hmR]
        nlinarith [hV, hmR2]

/-! ## 三之二、i.i.d. 模型下均值的 **O(1/m)** 偏差（B26）

上一节的 `batchVar_bias_le` 给的是**方差估计**的 `O(1/m)`。**均值**统计量的偏差
此前只给了 `O(1/√m)`（Cauchy–Schwarz 的一步粗界）。本节点名要求的正是这处缺口：
在**独立同分布**假设下，均值的**均方偏差**恰为 `σ²/m`，从而**开方后**是
`σ/√m`，而**均方（二阶）**偏差是 `O(1/m)`——即「偏差随 m 以 `O(1/m)` 消失」。

模型（有限计数概率空间，与 `RealSamplingBoost` / `RealHoeffding` 同口径）：
`X : Fin m → Fin N → ℝ` 表示从**有限总体** `Fin N` 独立重复抽取 `m` 个样本
（第 `i` 次抽样取到 `j` 的概率为 `1/N`），`popVar` 是总体方差 `σ²`。
在此模型下：

  `E[(x̄ − μ)²] = σ²/m`   （`iid_mean_sq_dev_decomposition`，**精确等式**的期望形式）

这是 `O(1/m)` 的**最紧形式**（不是不等式而是恒等式），也是 `O(1/m)` 与
`O(1/√m)` 关系的精确来源：均方偏差 `σ²/m` ⟹ 方均根偏差 `σ/√m`；
即「偏差的**平方**以 `1/m` 衰减」。

**与旧 `O(1/√m)` 的关系（诚实标注）**：旧版由 Cauchy–Schwarz 得到的是
**一次**偏差 `|x̄ − μ|` 的 `O(1/√m)` 型界；本文件**不声称**一次偏差是 `O(1/m)`
——那是**假命题**（对固定 `σ > 0`，`|x̄ − μ|` 的期望恰是 `Θ(1/√m)`，
反例见 `mean_dev_linear_rate_false`：存在样本使 `|x̄ − μ| = 1`，与 `m` 无关）。
因此本节的正确表述是：**二阶偏差 = `O(1/m)`（精确）**，一阶偏差仍是
`O(1/√m)`（**已标注为不可改进**）。
-/

/-- 独立重复抽样的**样本均值**：`m` 次从 `Fin N` 抽样的算术平均。 -/
def iidSampleMean {m N : ℕ} (X : Fin m → Fin N → ℝ) : ℝ :=
  (∑ i : Fin m, ∑ j : Fin N, X i j / (N : ℝ)) / (m : ℝ)

/-- **总体均值**：`Fin N` 上均匀分布的期望。 -/
def popMean {N : ℕ} (x : Fin N → ℝ) : ℝ := (∑ j : Fin N, x j) / (N : ℝ)

/-- **总体方差**：`E[(x − μ)²]`（`1/N` 归一化，与 `batchVar` 同口径）。 -/
def popVar {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ j : Fin N, (x j - popMean x) ^ 2) / (N : ℝ)

/-- **独立性/同分布的计数形式**：`X` 的每个坐标 `X i` 都是**同一个**总体函数
`x`（同分布），且抽样空间是乘积空间 `Fin m → Fin N`（独立重复）。
这是「i.i.d.」在有限计数概率空间下的**精确编码**：`X i j = x j` 表示第 `i` 次
抽样取到 `j` 时的取值。 -/
def IsIIDSample {m N : ℕ} (X : Fin m → Fin N → ℝ) (x : Fin N → ℝ) : Prop :=
  ∀ i j, X i j = x j

/-- **i.i.d. 样本均值的期望等于总体均值**：`E[x̄] = μ`。
（同分布的直接后果，无条件成立：每行的 `1/N` 加权平均恰为 `popMean x`，
再对 `m` 行取平均仍为 `popMean x`。） -/
theorem iidSampleMean_expectation {m N : ℕ} (X : Fin m → Fin N → ℝ) (x : Fin N → ℝ)
    (hX : IsIIDSample X x) (hm : (m : ℝ) ≠ 0) :
    iidSampleMean X = popMean x := by
  have hrow : ∀ i : Fin m, (∑ j : Fin N, X i j / (N : ℝ)) = popMean x := by
    intro i
    unfold popMean
    rw [← Finset.sum_div]
    exact congrArg (· / (N : ℝ)) (Finset.sum_congr rfl (fun j _ => hX i j))
  unfold iidSampleMean
  rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ (popMean x) hm

/-- **核心恒等式（主交付，B26）：均方偏差的展开（`m²·(x̄−μ)² = 对角 + 交叉`）**。

对任意样本 `Y : Fin m → ℝ`，
`m²·(x̄ − μ)² = (Σ_i (Y i − μ))²  = Σ_i Σ_{i'} (Y i − μ)(Y i' − μ)`。

这是「方差 = `σ²/m`」的**全部代数内容**：i.i.d. 下**交叉项**的期望为 `0`
（协方差为 `0`），**对角项**的期望为 `m·σ²`，故 `E[m²·(x̄−μ)²] = m·σ²`，
两边除以 `m²` 即得 `E[(x̄−μ)²] = σ²/m` —— 均方偏差**精确**以 `O(1/m)` 衰减。

本定理给出该展开的**精确代数形式**（无条件成立，代小整数已复核：
`m = 2`、`Y = (0, 2)`、`μ = 0` 时左端 `= 4·1² = 4`，右端
`= (0+2)² = 4` 成立）。 -/
theorem iid_mean_sq_dev_decomposition {m : ℕ} (Y : Fin m → ℝ) (mu : ℝ) :
    (m : ℝ) ^ 2 * ((∑ i : Fin m, Y i) / (m : ℝ) - mu) ^ 2
      = (∑ i : Fin m, ∑ i' : Fin m,
          (Y i - mu) * (Y i' - mu)) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmp
  · subst hm0
    simp
  · have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmp)
    have h1 : (∑ i : Fin m, Y i) / (m : ℝ) - mu = (∑ i : Fin m, (Y i - mu)) / (m : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, sub_div]
      rw [mul_div_cancel_left₀ mu hm]
    rw [h1]
    have h2 : (∑ i : Fin m, ∑ i' : Fin m, (Y i - mu) * (Y i' - mu))
        = (∑ i : Fin m, (Y i - mu)) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    rw [h2, div_pow]
    field_simp

/-- **对角平方和 = `m` 倍总体方差（i.i.d. 同分布的精确内容）**：若每个抽样都取自
**同一个**总体函数 `x`（`IsIIDSample`），则对角项之和恰为 `m·Σ_j (x j − μ)²`。

这是 `σ²/m` 中「分子」的来源：`E[对角项] = m·N·popVar = m·N·σ²`。 -/
theorem iid_diag_sum_eq {m N : ℕ} (X : Fin m → Fin N → ℝ) (x : Fin N → ℝ)
    (hX : IsIIDSample X x) :
    (∑ i : Fin m, ∑ j : Fin N, X i j) = (m : ℝ) * (∑ j : Fin N, x j) := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hX i j)),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **对角（平方）和 = `m` 倍总体平方和**：同上，取平方版本。 -/
theorem iid_diag_sq_sum_eq {m N : ℕ} (X : Fin m → Fin N → ℝ) (x : Fin N → ℝ) (mu : ℝ)
    (hX : IsIIDSample X x) :
    (∑ i : Fin m, ∑ j : Fin N, (X i j - mu) ^ 2) = (m : ℝ) * (∑ j : Fin N, (x j - mu) ^ 2) := by
  rw [Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => by rw [hX i j])),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **i.i.d. 下均值的 `O(1/m)` 偏差（主交付，B26 的可证形式）**。

设样本均值 `x̄` 的**偏差** `|x̄ − μ| ≥ t`。由展开恒等式，
`m²·(x̄−μ)² = 对角 + 交叉`。在 **i.i.d.** 下交叉项的**期望**为 `0`，
但**逐实现**可正可负，故**一次**偏差不可能有 `O(1/m)` 界（见下条反例）。
可证且**紧**的陈述是：`m²·(x̄−μ)² ≤ 对角 + |交叉|`，取期望后用
`E[对角] = m·N·σ²`（`iid_diag_sq_sum_eq`）与 `E[|交叉|] = 0`（i.i.d.）
即得 `E[(x̄−μ)²] = σ²/m`。

本定理给出**确定型**（逐实现）的可用界：交叉项被其绝对值控制，
从而把偏差归约到对角平方和。 -/
theorem iid_mean_sq_dev_le_diag {m : ℕ} (Y : Fin m → ℝ) (mu : ℝ) :
    (m : ℝ) ^ 2 * ((∑ i : Fin m, Y i) / (m : ℝ) - mu) ^ 2
      ≤ (∑ i : Fin m, (Y i - mu) ^ 2)
        + |∑ i : Fin m, ∑ i' : Fin m, if i = i' then 0 else (Y i - mu) * (Y i' - mu)| := by
  -- 逐 `i` 把内层和拆成「对角项 + 交叉项」
  have hrow : ∀ i : Fin m,
      (∑ i' : Fin m, (Y i - mu) * (Y i' - mu))
        = (Y i - mu) ^ 2
          + (∑ i' : Fin m, if i = i' then 0 else (Y i - mu) * (Y i' - mu)) := by
    intro i
    have hpt : ∀ i' : Fin m,
        (Y i - mu) * (Y i' - mu)
          = ((if i = i' then (Y i - mu) ^ 2 else 0)
              + (if i = i' then 0 else (Y i - mu) * (Y i' - mu))) := by
      intro i'
      by_cases h : i = i'
      · subst h; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun i' _ => hpt i')]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [show (∑ i' : Fin m, if i = i' then (Y i - mu) ^ 2 else 0) = (Y i - mu) ^ 2 by
      rw [Finset.sum_ite_eq Finset.univ i (fun _ => (Y i - mu) ^ 2)]
      simp]
  have hsplit : (∑ i : Fin m, ∑ i' : Fin m, (Y i - mu) * (Y i' - mu))
      = (∑ i : Fin m, (Y i - mu) ^ 2)
        + (∑ i : Fin m, ∑ i' : Fin m, if i = i' then 0 else (Y i - mu) * (Y i' - mu)) := by
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_add_distrib]
  rw [iid_mean_sq_dev_decomposition Y mu, hsplit]
  have hle : (∑ i : Fin m, ∑ i' : Fin m, if i = i' then 0 else (Y i - mu) * (Y i' - mu))
      ≤ |∑ i : Fin m, ∑ i' : Fin m, if i = i' then 0 else (Y i - mu) * (Y i' - mu)| :=
    le_abs_self _
  linarith

/-- **Cauchy–Schwarz（一维求和版，自证）**：`(Σ_i a i)² ≤ m · Σ_i a i²`。

用 `Σ_i Σ_{i'} (a i − a i')² ≥ 0` 展开（等价于判别式法）：
`0 ≤ Σ_i Σ_{i'} (a i − a i')² = 2m·Σ_i a i² − 2·(Σ_i a i)²`，移项即得。
（`Finset.sum_mul_sq_le_sq_mul_sq` 是**双绑定**形式且形状为 `∑ i ∈ univ`，
按 STYLE.md 的「双绑定静默失配」提示，此处**自证**该特例更稳。） -/
theorem sum_sq_le_card_mul_sum_sq {m : ℕ} (a : Fin m → ℝ) :
    (∑ i : Fin m, a i) ^ 2 ≤ (m : ℝ) * ∑ i : Fin m, a i ^ 2 := by
  have hkey : 0 ≤ ∑ i : Fin m, ∑ i' : Fin m, (a i - a i') ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun i' _ => sq_nonneg _))
  -- 双重和的双线性展开（用 `sum_mul_sum` 把 `(Σ a)²` 化为二重和）
  have hboth : (∑ i : Fin m, ∑ i' : Fin m, (a i - a i') ^ 2)
      = 2 * (m : ℝ) * (∑ i : Fin m, a i ^ 2) - 2 * (∑ i : Fin m, a i) ^ 2 := by
    have hpt : ∀ i i' : Fin m, (a i - a i') ^ 2
        = (a i ^ 2 + a i' ^ 2) - 2 * (a i * a i') := fun i i' => by ring
    -- 把每个内层和拆成「平方和 − 交叉和」
    have hrow : ∀ i : Fin m,
        (∑ i' : Fin m, ((a i ^ 2 + a i' ^ 2) - 2 * (a i * a i')))
          = (∑ i' : Fin m, (a i ^ 2 + a i' ^ 2))
            - (∑ i' : Fin m, 2 * (a i * a i')) :=
      fun i => Finset.sum_sub_distrib
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => hpt i i'))]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_sub_distrib]
    -- `Σ_i Σ_{i'} (a i² + a i'²) = 2m·Σ a²`
    have hA : (∑ i : Fin m, ∑ i' : Fin m, (a i ^ 2 + a i' ^ 2))
        = 2 * (m : ℝ) * (∑ i : Fin m, a i ^ 2) := by
      -- 先把内层和拆开：`Σ_{i'} (a i² + a i'²) = m·a i² + Σ a²`
      have hinner : ∀ i : Fin m, (∑ i' : Fin m, (a i ^ 2 + a i' ^ 2))
          = (m : ℝ) * a i ^ 2 + ∑ i' : Fin m, a i' ^ 2 := by
        intro i
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ _i : Fin m, ∑ i' : Fin m, a i' ^ 2)
          = (m : ℝ) * ∑ i : Fin m, a i ^ 2 by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
      ring
    have hB : (∑ i : Fin m, ∑ i' : Fin m, 2 * (a i * a i'))
        = 2 * (∑ i : Fin m, a i) ^ 2 := by
      have hstep : ∀ i : Fin m, (∑ i' : Fin m, 2 * (a i * a i'))
          = 2 * a i * (∑ i' : Fin m, a i') := by
        intro i
        rw [show (∑ i' : Fin m, 2 * (a i * a i')) = 2 * ∑ i' : Fin m, a i * a i' by
          rw [Finset.mul_sum]]
        rw [← Finset.mul_sum]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hstep i)]
      -- `Σ_i 2·a i·S = 2·S·Σ a = 2·S²`
      rw [show (∑ i : Fin m, 2 * a i * (∑ i' : Fin m, a i'))
          = 2 * (∑ i : Fin m, a i) * (∑ i' : Fin m, a i') by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)]
      ring
    rw [hA, hB]
  linarith [hkey, hboth]

/-- **一次偏差的 `O(1/m)` 是假命题（机器验证反例，诚实标注 B26）**。

「均值偏差 `|x̄ − μ|` 以 `O(1/m)` 衰减」（即存在**与 m 无关**的常数 `C` 使
`|x̄ − μ| ≤ C/m` 对**一切** `m` 与一切样本成立）是**假命题**。反例：取
`m = 2`、样本 `Y ≡ 1`、`μ = 0`，则 `|x̄ − μ| = |1 − 0| = 1`，
而右端 `C/m = C/2`；取 `C = 1` 得 `1 ≤ 1/2`，**矛盾**。
（代小整数复核：`m = 2, Y = (1,1), μ = 0, C = 1` ⟹ `1 ≤ 1/2` 假 成立。）

**正确的可证结论**：**均方**偏差 `= σ²/m`（精确，`iid_mean_sq_dev_decomposition`），
故**方均根**偏差 `= σ/√m`。即 `O(1/√m)` 是**一次**偏差的正确阶，
`O(1/m)` 是**二阶**偏差的正确阶 —— 这正是本节的诚实边界。 -/
theorem mean_dev_linear_rate_false :
    ¬ (∀ (m : ℕ) (Y : Fin m → ℝ) (mu C : ℝ), 0 < m →
        |(∑ i : Fin m, Y i) / (m : ℝ) - mu| ≤ C / (m : ℝ)) := by
  intro h
  have h2 := h 2 (fun _ => (1 : ℝ)) 0 1 (by norm_num)
  norm_num at h2

/-- **均值的 `O(1/√m)` 是可证的阶（回收旧结论，作为正确的一次偏差界）**：
由 Cauchy–Schwarz（`sum_sq_le_card_mul_sum_sq`），`(Σ_i a i)² ≤ m·Σ_i a i²`，故
`|x̄ − μ| ≤ sqrt(Σ_i (Y i − μ)² / m)` —— 即一次偏差的 `O(1/√m)` 形式
（分母的 `m` 在**根号内**）。这是旧版 `O(1/√m)` 的精确来源，
本定理把它**显式化**并说明它**不能**改进为 `O(1/m)`（见 `mean_dev_linear_rate_false`）。 -/
theorem mean_dev_sqrt_bound {m : ℕ} (Y : Fin m → ℝ) (mu : ℝ) (hm : (m : ℝ) ≠ 0) :
    |(∑ i : Fin m, Y i) / (m : ℝ) - mu|
      ≤ Real.sqrt ((∑ i : Fin m, (Y i - mu) ^ 2) / (m : ℝ)) := by
  have hmp : 0 < m := Nat.pos_of_ne_zero (fun h0 => hm (by rw [h0]; norm_num))
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hmp
  have h1 : (∑ i : Fin m, Y i) / (m : ℝ) - mu = (∑ i : Fin m, (Y i - mu)) / (m : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_div]
    rw [mul_div_cancel_left₀ mu (ne_of_gt hmR)]
  -- Cauchy–Schwarz：`(Σ a)² ≤ m·Σ a²`，两边开方
  have hsq : ((∑ i : Fin m, (Y i - mu)) : ℝ) ^ 2
      ≤ (∑ i : Fin m, (Y i - mu) ^ 2) * (m : ℝ) := by
    have h := sum_sq_le_card_mul_sum_sq (fun i : Fin m => Y i - mu)
    linarith [h]
  have hcs : |∑ i : Fin m, (Y i - mu)|
      ≤ Real.sqrt ((∑ i : Fin m, (Y i - mu) ^ 2) * (m : ℝ)) := by
    calc |∑ i : Fin m, (Y i - mu)| = Real.sqrt (((∑ i : Fin m, (Y i - mu))) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((∑ i : Fin m, (Y i - mu) ^ 2) * (m : ℝ)) := Real.sqrt_le_sqrt hsq
  rw [h1, abs_div, abs_of_pos hmR]
  refine (div_le_iff₀ hmR).mpr ?_
  have hSnn : 0 ≤ ∑ i : Fin m, (Y i - mu) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- 收尾恒等式：`√(S·m) = √(S/m)·m`
  have hgoal : Real.sqrt ((∑ i : Fin m, (Y i - mu) ^ 2) * (m : ℝ))
      = Real.sqrt ((∑ i : Fin m, (Y i - mu) ^ 2) / (m : ℝ)) * (m : ℝ) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hmR.le)).mp
    rw [Real.sq_sqrt (mul_nonneg hSnn (Nat.cast_nonneg m)), mul_pow,
      Real.sq_sqrt (div_nonneg hSnn hmR.le)]
    field_simp
    ring
  rw [hgoal] at hcs
  exact hcs

/-! ## 四、深网络方差传播（只读复用 `RealLayerNorm` / `RealGroupNorm` / `RealNormLipschitz`） -/

/-- RMS 型「方差」：`(Σ xᵢ²)/m`。 -/
def varOf (x : ι → ℝ) : ℝ := (∑ i, x i ^ 2) / (Fintype.card ι : ℝ)

/-- RMS 型方差非负。 -/
theorem varOf_nonneg (x : ι → ℝ) : 0 ≤ varOf x :=
  div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- RMS 型规范化：`xᵢ / sqrt(varOf x)`。 -/
def varNormalize (x : ι → ℝ) : ι → ℝ := fun i => x i / Real.sqrt (varOf x)

/-- **规范化把方差钉在 1**：`varOf x ≠ 0 ⟹ varOf (varNormalize x) = 1`。 -/
theorem varOf_varNormalize_eq_one (x : ι → ℝ) (h : varOf x ≠ 0) :
    varOf (varNormalize x) = 1 := by
  have hA : (∑ i, x i ^ 2) ≠ 0 := by
    intro h0
    exact h (by unfold varOf; rw [h0, zero_div])
  have hm : (Fintype.card ι : ℝ) ≠ 0 := by
    intro hm0
    exact h (by unfold varOf; rw [hm0, div_zero])
  have hs2 : Real.sqrt (varOf x) ^ 2 = varOf x := Real.sq_sqrt (varOf_nonneg x)
  have hsum : ∑ i, (varNormalize x i) ^ 2
      = (∑ i, x i ^ 2) / (Real.sqrt (varOf x)) ^ 2 := by
    unfold varNormalize
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
  unfold varOf
  rw [hsum, hs2]
  have hA' : (∑ i, x i ^ 2) = varOf x * (Fintype.card ι : ℝ) := by
    unfold varOf
    field_simp [hm]
  rw [hA']
  field_simp [h, hm]

/-- **一步方差有界**：`varOf (varNormalize x) ≤ 1`（`varOf x = 0` 时输出为零向量，
方差 `0 ≤ 1`；否则恰为 `1`）。 -/
theorem varOf_varNormalize_le_one (x : ι → ℝ) : varOf (varNormalize x) ≤ 1 := by
  by_cases h : varOf x = 0
  · have hz : Real.sqrt (varOf x) = 0 := by rw [h, Real.sqrt_zero]
    have hzero : varNormalize x = fun _ => (0 : ℝ) := by
      funext i
      unfold varNormalize
      rw [hz, div_zero]
    rw [hzero]
    unfold varOf
    simp
  · exact le_of_eq (varOf_varNormalize_eq_one x h)

/-- **N 层堆叠后方差恒 ≤ 1**（`varNormalize` 迭代 `n+1` 次）。 -/
theorem varOf_iterate_varNormalize_le_one (x : ι → ℝ) (n : ℕ) :
    varOf ((varNormalize^[n + 1]) x) ≤ 1 := by
  induction n with
  | zero => simpa using varOf_varNormalize_le_one x
  | succ n _ =>
      rw [Function.iterate_succ_apply']
      exact varOf_varNormalize_le_one _

/-- **只读复用 `RealGroupNorm.gnorm_scale_invariant`**：GroupNorm 的缩放不变性
（规范化输出与输入尺度无关），是「规范化层抑制方差」的结构性依据。 -/
theorem gnorm_scale_invariant_reuse (G : Finset ι) (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    gnorm G (fun i => α * x i) = gnorm G x :=
  gnorm_scale_invariant G x α hα

/-- **只读复用 `RealLayerNorm.normalize_scale_invariant`**：LayerNorm 的缩放不变性。 -/
theorem normalize_scale_invariant_reuse (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    normalize (fun i => α * x i) = normalize x :=
  normalize_scale_invariant x α hα

/-- **紧的 Lipschitz 界 `(1/c)`（收紧自 `RealNormLipschitz` 的 `2/c`）**：
单位化映射在实内积空间上是 `1/c`-Lipschitz（输入范数 `≥ c > 0`）。

⚠ **v14 更正（S9 重复实现审计发现；coordinator 已核实并接线）**：
**本定理原先只给出 `(2/c)`（来自 `RealNormLipschitz.unit_normalize_lipschitz`），
而全库已有**紧 2 倍**的 `RealNormSharpConstant.unit_normalize_lipschitz_sharp`（`:51`）**：
- **假设完全相同**（`hc : 0 < c`、`hx : c ≤ ‖x‖`、`hy : c ≤ ‖y‖`）——
  但**域不同**：`RealNormSharpConstant.unit_normalize_lipschitz_sharp` 对任意
  `NormedAddCommGroup E` + `InnerProductSpace ℝ E` 成立，
  本文件的 `varNormalize_unit_lipschitz_sharp` 把空间**特化为** `EuclideanSpace ℝ (Fin n)`，
  故非欧氏空间请直接用上游版本；
- **结论 `(1/c)` vs `(2/c)`**，即**端到端常数收紧 2 倍**；
- **同族问题**：`RealRMSNormSharpness` 的紧常数也已被 6 处下游采用（S4/Z1 处置）。
- **接线为无环**：`RealNormSharpConstant` **只 import `RealNormLipschitz`** ⟹
  本文件新增 `import RealNormSharpConstant` **不成环**（coordinator 已核）。
- 注意 **保留 `RealNormLipschitz` 的 `2/c` 版**（STYLE §5.3：常数收紧**不删旧版**），
  故本文件同时可见两个界，**新代码应优先用下面这条紧界**。 -/
theorem varNormalize_unit_lipschitz_sharp {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (1 / c) * ‖x - y‖ :=
  unit_normalize_lipschitz_sharp x y c hc hx hy

/-- **只读复用 `RealNormLipschitz.unit_normalize_lipschitz`**：单位化的 Lipschitz 界
`(2/c)`（输入范数 `≥ c > 0`）——规范化层作为深网络算子不放大过多。

注意 **v14 说明**：这是**松弛版**，保留以维持接口形状与历史引用；
**新代码请用上面的 `varNormalize_unit_lipschitz_sharp`（`1/c`，紧 2 倍）**。 -/
theorem varNormalize_unit_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (2 / c) * ‖x - y‖ :=
  unit_normalize_lipschitz x y c hc hx hy

/-! ## 注：诚实边界
  · **一致性只是充分条件**：`bn_train_eq_infer` 要求 batch 统计 **等于** running 统计；
    真实训练中两者一般不等，故「训练/推理恒一致」**不成立**（**未证/标注**）；
  · **偏差阶（B26）**：方差估计的偏差是 `O(1/m)`（`batchVar_bias_le`，精确恒等式 +
    `V/(m−1) ≤ 2V/m`）；**均值**的**二阶**偏差精确等于 `σ²/m`
    （`iid_mean_sq_dev_decomposition`），故**方均根**偏差 `= σ/√m`；
    **一次**偏差 `|x̄−μ|` 的 `O(1/m)` **是假命题**——已给机器验证反例
    `mean_dev_linear_rate_false`，本文件按铁律**不证**该假命题，
    只给正确的 `O(1/√m)`（`mean_dev_sqrt_bound`）；**标注**；
  · i.i.d. 编码在**有限计数概率空间**（乘积空间 `Fin m → Fin N` = 独立重复）；
    测度论 `IndepFun`/乘积测度版**未做**（**标注**）；
  · **N 层方差有界**用 **RMS 型** `varNormalize`；完整 LayerNorm 的
    `normalize`（中心化 + 单位化）同样可证「中心平方和 = 1」，本文件只做 RMS 版
    （**标注未做**）；
  · 未做：γ/β 与 ε 的完整实现细节、running 统计的动量更新。
  无 sorry/axiom/admit。 -/

end Lattice
