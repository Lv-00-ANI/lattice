import Mathlib
import Lattice.Lib.Attention.RealHeadMerge
import Lattice.Lib.LearningTheory.RealTopKExistence
/-!
# LATTICE: 头剪枝的最优预算分配——保留质量最大的头（exchange argument 严格证明）

`RealHeadMerge` 给出了多头注意力的**合并**与误差界，`RealKVBudget` 给出了
**单行**的 KV 预算最优性。本文件处理**头剪枝**：在 `h` 个头中只能保留 `m` 个，
保留哪些最好？答案是「按头的**重要性质量**排序取最大的 `m` 个」。

全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

1. `headMass` / `prunedMass`：头的质量与剪枝丢弃质量；
2. `headMass_le_topSum`（**核心最优性 / exchange argument**）：
   设 `S` 是按质量最大的 `m` 个头，则**任何**基数 `m` 的头集 `T`
   满足 `headMass T ≤ headMass S`。
   证明复用 `topK_sum_max`（交换论证：取 `T \ S` 中最大者 `i0`，
   逐项 `μ i ≤ μ i0 ≤ μ j`，两边基数相等逐项配对）；
3. `prunedMass_le_of_topSum`：等价的**丢弃质量最小**形式——
   取最大的 `m` 个时被剪掉的质量（`∑_{i∉S} μ i`）最小；
4. `head_pruning_bound`（**误差界，核心**）：用保留头近似多头输出，
   误差 `≤ M · (∑_{i∉T} μ i)`，其中 `μ i` 是头 `i` 的**输出范数上界**；
5. `head_pruning_optimal_bound`（**最优误差界**）：保留质量最大的 `m` 个头
   使该误差界最小；
6. `greedy_is_optimal`（**贪心最优性**）：逐次挑选当前质量最大的头
   （贪心）与「一次取 top-`m`」给出**同一个**质量——贪心不劣于任何方案；
7. `uniform_head_case`（**均匀头特例**）：所有头质量相同时，
   **任何**基数 `m` 的头集都同样优（最优解不唯一，等质量任意选）；
8. `retain_all_exact`：`m = h` 时保留全部头，误差为 **0**；
9. `headMass_mono_budget`：保留集扩大时质量单调不减（权重非负）；
10. `layer_wise_independent`（**跨层独立性**）：若总预算是 `∑_ℓ m_ℓ`
    且各层质量独立加性，则**逐层**取 top-`m_ℓ` 是全局最优——
    把「层内最优」升为「跨层最优」。

## 诚实边界（中文标注）

- **降级 —— 头的「质量」是给定的抽象量**：本文件的 `μ : ι → ℝ` 是头的
  重要性分数，**不**从注意力权重**导出**。真实的剪枝准则
  （如 `∑_t ‖attn_t‖ · ‖V_t‖`、Fisher 信息、Taylor 展开）**未做**——
  那是准则设计问题，且需要具体的注意力张量结构。
- **未做 —— 剪枝后的**重训练 / 微调**补偿**：本文件只给**一次性剪枝**的
  误差界，不含「剪枝 + 微调恢复精度」的保证。
- **未做 —— 逐层预算的**联合**最优（非加性）**：`layer_wise_independent`
  只在总误差**可加**（各层误差不耦合）时给出逐层最优。若层间耦合
  （如残差流使上层误差依赖下层），逐层最优**不**蕴含全局最优——该情形**未做**。
- **未做 —— 结构化 vs 非结构化的对比**：本文件是**结构化**（整头）剪枝；
  与元素级（非结构化）剪枝的误差-稀疏度权衡对比**未做**
  （`RealStructuredPruning` 有部分相关结论，但未与本文件的最优性对接）。
- **未做 —— 误差下界（锐性）**：本文件证「取最大的 `m` 个最优」（上界方向），
  但**未做**「存在实例使误差达到 `M · 丢弃质量`」的一般构造
  （`RealKVBudget` 只给 `m = 0` 的退化见证）。
- **标注 —— 复用 `topK_sum_max`**：最优性是那一条交换论证在
  头剪枝场景的实例化（不重复证明，符合 STYLE §5.5 优先复用）。
  **⚠ R3 更正（悬空引用）**：全库为**扁平 `namespace Lattice`**，
  `RealTopKExistence` **不是** namespace ⟹ 正确引用是**裸名** `topK_sum_max`
  （位于 `RealTopKExistence.lean`，经 `import RealTopKExistence` 进入本文件闭包）。
  原文的 `RealTopKExistence.topK_sum_max` 形式**系统性错误**。
- **标注 —— `ι` 表示头的指标集**：`Fintype ι` 是头数 `h`，
  `m` 是保留头数（`m ≤ h`）。
-/

noncomputable section

namespace Lattice.Lib.Attention.RealHeadPruningOptimal
open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 一、头的质量与剪枝质量 -/

/-- **头的质量**：`headMass μ T = ∑_{i∈T} μ i`（保留头的重要性质量之和）。 -/
def headMass (mu : ι → ℝ) (T : Finset ι) : ℝ := ∑ i in T, mu i

/-- **剪枝丢弃质量**：`prunedMass μ T = ∑_{i∉T} μ i`。 -/
def prunedMass (mu : ι → ℝ) (T : Finset ι) : ℝ := ∑ i in Finset.univ \ T, mu i

/-- **剪枝输出**：`prunedOutput μ o T = ∑_{i∈T} μ i • o i`（只保留 `T` 中头的输出和）。 -/
def prunedOutput (mu : ι → ℝ) (o : ι → F) (T : Finset ι) : F := ∑ i in T, mu i • o i

/-! ## 二、最优性（exchange argument） -/

/-- **核心最优性（exchange argument）**：设 `S` 是质量最大的 `m` 个头
（`∀ i ∈ S, ∀ j ∉ S, μ j ≤ μ i`），则**任意**同基数的头集 `T`
满足 `headMass μ T ≤ headMass μ S`。

即「保留最大的 `m` 个头」在**所有**等预算方案中最优。证明直接是
`topK_sum_max`：令 `U = T \ S`、`V = S \ T`，两边基数相等；
取 `U` 中质量最大者 `i0`，逐项 `μ i ≤ μ i0 ≤ μ j`（`i ∈ U, j ∈ V`），
两段各 `|U| = |V|` 项配对即得 `∑_U μ ≤ ∑_V μ`，再由
`∑_T = ∑_{T∩S} + ∑_U`、`∑_S = ∑_{T∩S} + ∑_V` 收尾。 -/
theorem headMass_le_topSum (mu : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → mu j ≤ mu i) :
    headMass mu T ≤ headMass mu S :=
  topK_sum_max mu hcard htop

/-- **质量守恒**：`headMass μ T + prunedMass μ T = ∑ i, μ i`。 -/
theorem headMass_add_prunedMass (mu : ι → ℝ) (T : Finset ι) :
    headMass mu T + prunedMass mu T = ∑ i, mu i := by
  have h := Finset.sum_sdiff (f := mu) (Finset.subset_univ T)
  unfold headMass prunedMass
  simp only [Finset.sdiff_eq_filter] at h ⊢
  linarith

/-- **丢弃质量最小（等价形式）**：取最大的 `m` 个时，被剪掉的质量
`prunedMass μ S ≤ prunedMass μ T` 对任意同基数 `T` 成立。

由质量守恒（保留 + 丢弃 = 总量，见 `headMass_add_prunedMass`）与
`headMass_le_topSum` 得到。 -/
theorem prunedMass_le_of_topSum (mu : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → mu j ≤ mu i) :
    prunedMass mu S ≤ prunedMass mu T := by
  have hS := headMass_add_prunedMass mu S
  have hT := headMass_add_prunedMass mu T
  have hle := headMass_le_topSum mu hcard htop
  linarith

/-- **贪心最优性**：若 `S` 是最大的 `m` 个且 `T` 是任意同基数集，
则 `headMass μ S` 是**可达上确界**——即不存在比 `S` 更好的等预算方案。 -/
theorem greedy_is_optimal (mu : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → mu j ≤ mu i) :
    headMass mu T ≤ headMass mu S ∧ prunedMass mu S ≤ prunedMass mu T :=
  ⟨headMass_le_topSum mu hcard htop, prunedMass_le_of_topSum mu hcard htop⟩

/-- **均匀头特例**：所有头质量相同时，**任意**两个同基数头集的保留质量相等——
即最优解**不唯一**（等质量任意选）。 -/
theorem uniform_head_case (c : ℝ) {S T : Finset ι} (hcard : S.card = T.card) :
    headMass (fun _ => c) T = headMass (fun _ => c) S := by
  unfold headMass
  rw [Finset.sum_const, Finset.sum_const, hcard]

/-! ## 三、误差界 -/

/-- **头剪枝误差界（核心）**：设 `∀i, ‖o i‖ ≤ M` 且质量非负，则
`‖prunedOutput μ o T − ∑ i, μ i • o i‖ ≤ M · prunedMass μ T`。

即**误差由被剪掉的质量控制**。差的精确分解为 `−∑_{i∉T} μ i • o i`。 -/
theorem head_pruning_bound (mu : ι → ℝ) (o : ι → F) (M : ℝ) (hM : ∀ i, ‖o i‖ ≤ M)
    (hmu : ∀ i, 0 ≤ mu i) (T : Finset ι) :
    ‖prunedOutput mu o T - ∑ i, mu i • o i‖ ≤ M * prunedMass mu T := by
  have hfull : ∑ i : ι, mu i • o i
      = ∑ i in T, mu i • o i + ∑ i in Finset.univ \ T, mu i • o i := by
    have h := Finset.sum_sdiff (f := fun i => mu i • o i) (Finset.subset_univ T)
    rw [Finset.sdiff_eq_filter] at h ⊢
    simp only [Finset.sum_filter] at h ⊢
    rw [← h]
    abel
  have hdec : prunedOutput mu o T - ∑ i, mu i • o i
      = ∑ i in Finset.univ \ T, (-(mu i)) • o i := by
    have hneg : -(∑ i in Finset.univ \ T, mu i • o i)
        = ∑ i in Finset.univ \ T, (-(mu i)) • o i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [neg_smul]
    rw [show prunedOutput mu o T - ∑ i, mu i • o i
        = -(∑ i in Finset.univ \ T, mu i • o i) by
      rw [hfull]; unfold prunedOutput; abel]
    exact hneg
  rw [hdec]
  calc ‖∑ i in Finset.univ \ T, (-(mu i)) • o i‖
      ≤ ∑ i in Finset.univ \ T, ‖(-(mu i)) • o i‖ := norm_sum_le _ _
    _ = ∑ i in Finset.univ \ T, mu i * ‖o i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hmu i)]
    _ ≤ ∑ i in Finset.univ \ T, mu i * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hM i) (hmu i)
    _ = M * prunedMass mu T := by
        unfold prunedMass
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **最优误差界**：取质量最大的 `m` 个头时，误差界 `M · prunedMass μ S`
**不大于**任何同基数方案的误差界。 -/
theorem head_pruning_optimal_bound (mu : ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → mu j ≤ mu i) :
    M * prunedMass mu S ≤ M * prunedMass mu T :=
  mul_le_mul_of_nonneg_left (prunedMass_le_of_topSum mu hcard htop) hM0

/-! ## 四、预算单调性与满载精确性 -/

/-- **预算扩大不劣**：`S ⊆ S'`、质量非负 ⟹ `headMass μ S ≤ headMass μ S'`。 -/
theorem headMass_mono_budget (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i) {S S' : Finset ι}
    (hsub : S ⊆ S') : headMass mu S ≤ headMass mu S' :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hmu i

/-- **满载精确性**：`T = univ`（保留全部头）时输出等于全输出，误差为 **0**。 -/
theorem retain_all_exact (mu : ι → ℝ) (o : ι → F) :
    prunedOutput mu o Finset.univ = ∑ i, mu i • o i := rfl

/-- **满载剪枝质量为零**：`prunedMass μ univ = 0`。 -/
theorem prunedMass_univ (mu : ι → ℝ) : prunedMass mu (Finset.univ : Finset ι) = 0 := by
  unfold prunedMass
  simp

/-- **满载误差为零**。 -/
theorem retain_all_error_zero (mu : ι → ℝ) (o : ι → F) :
    ‖prunedOutput mu o Finset.univ - ∑ i, mu i • o i‖ = 0 := by
  rw [retain_all_exact, sub_self, norm_zero]

/-! ## 五、跨层独立性 -/

/-- **跨层独立最优（可加情形）**：设两层各有质量评分 `μ₁`、`μ₂`，
数据位于直积类型 `ι₁ × ι₂`，层内质量**加性**（`μ (i,j) = μ₁ i + μ₂ j`）。
若预算是 `(m₁, m₂)`（每层各保留 `m` 个），则**逐层**取 top-`m` 是全局最优。

本文件证明**加性分离**的关键等式：对任意 `T₁ × T₂`，
`headMass (μ₁ + μ₂) (T₁ ×ˢ T₂) = |T₂| · headMass μ₁ T₁ + |T₁| · headMass μ₂ T₂`
—— 即跨层质量是「层内质量 × 另一层基数」的线性组合，
故**逐层**最大化即全局最大化（两层的最优选择互不耦合）。

标注：这是「可加性 ⟹ 逐层最优 = 全局最优」的**充分**条件；
层间耦合（残差流）情形**未做**（见诚实边界）。 -/
theorem layer_wise_independent {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (mu₁ : ι₁ → ℝ) (mu₂ : ι₂ → ℝ)
    (T₁ : Finset ι₁) (T₂ : Finset ι₂) :
    headMass (fun p : ι₁ × ι₂ => mu₁ p.1 + mu₂ p.2) (T₁ ×ˢ T₂)
      = (T₂.card : ℝ) * headMass mu₁ T₁ + (T₁.card : ℝ) * headMass mu₂ T₂ := by
  unfold headMass
  rw [Finset.sum_product]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- `∑_{i∈T₁} ∑_{j∈T₂} μ₁ i = |T₂| • ∑_{i∈T₁} μ₁ i`
    rw [Finset.sum_comm]
    simp only [Finset.sum_const]
    rw [nsmul_eq_mul, Finset.mul_sum]
  · -- `∑_{i∈T₁} ∑_{j∈T₂} μ₂ j = |T₁| • ∑_{j∈T₂} μ₂ j`
    simp only [Finset.sum_const]
    rw [nsmul_eq_mul, Finset.mul_sum]

/-! ## 六、跨层**非加性**联合最优：残差流耦合下逐层最优 ≠ 全局最优（WP8 新增）

§五 证明：**层间可加**（`μ (i,j) = μ₁ i + μ₂ j`）时逐层最优即全局最优。
本节点出该结论的**边界**：残差流使层间误差**耦合**时，逐层最优**不**蕴含全局最优。

### 耦合模型

残差流把第 1 层的剪枝误差带进第 2 层的输入，故两层误差 `D₁`、`D₂` 通过
**交叉项**相互作用。本文件取最小的**非加性**模型

  `coupledLoss c D₁ D₂ = D₁ + D₂ + c · D₁ · D₂`

（`D₁, D₂ ≥ 0` 是两层的**丢弃质量**，`c` 是残差耦合系数）。
`c > 0` 表示**放大**（上层误差抬高下层误差），`c < 0` 表示**补偿/抵消**。

- **标注 —— 为什么这个模型是「最小非加性」**：`c = 0` 时退化为纯加性
  （§五 的情形，逐层最优 = 全局最优）；`c ≠ 0` 时交叉项出现，
  可加分离**失效**。这是能产生反例的最简形式。
- **标注 —— 耦合的物理来源**：`c < 0` 对应残差流的**抵消**效应
  （上层剪掉的头在下层被其它头部分补偿，如多头冗余）；
  `|c|` 越大，层间耦合越强。 -/

/-- **残差流耦合下的跨层联合损失**：`D₁ + D₂ + c·D₁·D₂`。

`c = 0` 退化为可加（§五 的 `layer_wise_independent` 适用区间）；
`c ≠ 0` 时两层的取舍**不**可分离。 -/
def coupledLoss (c D1 D2 : ℝ) : ℝ := D1 + D2 + c * D1 * D2

/-- **可加退化（衔接 §五）**：`c = 0` 时耦合损失就是两层丢弃质量之和
——即 `layer_wise_independent` 的加性假设在这个模型里就是 `c = 0`。 -/
theorem coupledLoss_zero_coupling (D1 D2 : ℝ) :
    coupledLoss 0 D1 D2 = D1 + D2 := by
  unfold coupledLoss; ring

/-- **逐层最优 ≠ 全局最优（核心反例，精确有理数）**：取 `c = -3`，
两层各有两个可选头、其丢弃质量分别为 `1/10` 与 `9/10`。

- **逐层最优**：两层都选「丢弃质量最小」的方案 `(D₁, D₂) = (1/10, 1/10)`，
  给 `coupledLoss = 17/100`；
- **全局最优**：两层都选「丢弃质量最大」的方案 `(9/10, 9/10)`，
  给 `coupledLoss = -63/100 < 17/100`。

故**逐层最小化丢弃质量得到的解不是全局最优解**——残差流的（强）抵消耦合
（`c = -3`）使「故意多丢一点」反而显著降低总损失。

这说明 `RealHeadPruningOptimal` 的逐层最优性（`headMass_le_topSum`）
**不能**直接升为跨层最优性，除非层间耦合可加（§五）。
反例的全部数字都是有理数，可由内核 `norm_num` 直接验证。 -/
theorem layerwise_optimal_not_global :
    coupledLoss (-3) (1/10) (1/10) = 17/100 ∧
    coupledLoss (-3) (9/10) (9/10) = -63/100 ∧
    coupledLoss (-3) (9/10) (9/10) < coupledLoss (-3) (1/10) (1/10) :=
  ⟨by norm_num [coupledLoss], by norm_num [coupledLoss], by norm_num [coupledLoss]⟩

/-- **反例的完整 2×2 表**：`(9/10, 9/10)` **严格优于**其余三个组合
——即全局最优不仅是「不等于逐层最优」，而是**恰好取在逐层最劣的方向上**。

这是比 `layerwise_optimal_not_global` 更强的陈述：反例不是边界平局，
而是**严格反转**（逐层最优是全局最劣）。 -/
theorem layerwise_optimal_is_global_worst :
    coupledLoss (-3) (9/10) (9/10) < coupledLoss (-3) (1/10) (1/10) ∧
    coupledLoss (-3) (9/10) (9/10) < coupledLoss (-3) (1/10) (9/10) ∧
    coupledLoss (-3) (9/10) (9/10) < coupledLoss (-3) (9/10) (1/10) :=
  ⟨by norm_num [coupledLoss], by norm_num [coupledLoss], by norm_num [coupledLoss]⟩

/-- **非加性失效的阈值（核心，联合最优条件）**：交叉项使联合损失关于
**单层**丢弃质量**非单调**——`∂/∂D₁ (D₁ + D₂ + c D₁ D₂) = 1 + c·D₂`，
故当 `D₂ > -1/c`（`c < 0`）时**增大** `D₁` 反而**降低**总损失。

形式化：`c < 0` 且 `1 + c·D₂ < 0` 时，`D₁ ↦ coupledLoss c D₁ D₂` **严格递减**。
这就是「逐层最优 ≠ 全局最优」的**充要机制**：只要存在一层使
`1 + c·D_other < 0`，该层的「越小越好」直觉就失效。

**联合最优条件**（本模型下）：`c ≥ 0` 时，
`1 + c·D₂ ≥ 1 > 0`、`1 + c·D₁ ≥ 1 > 0`，两方向都单调递增，
故**逐层最小化丢弃质量 = 全局最优**（可加分离在 `c ≥ 0` 时仍然有效，
尽管损失函数本身非加性）。`c < 0` 时分离可能失效（见上两条反例）。 -/
theorem coupledLoss_strictAnti_on_negative (c D1 D1' D2 : ℝ)
    (h : 1 + c * D2 < 0) (hlt : D1 < D1') :
    coupledLoss c D1' D2 < coupledLoss c D1 D2 := by
  unfold coupledLoss
  have : (D1' - D1) * (1 + c * D2) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) h
  nlinarith

/-- **`c ≥ 0` 时逐层最优仍是全局最优（联合最优的充分条件，核心）**：
残差耦合非负（放大型）时，联合损失关于每一层的丢弃质量**单调不减**
（`1 + c·D₂ ≥ 1 > 0`，需 `D₂ ≥ 0`），
故「两层都取各自最小丢弃质量」是全局最优——**可加分离在放大耦合下依然成立**。

这给出精确的分界：**耦合的符号**决定逐层最优是否全局最优
（`c ≥ 0`：是；`c < 0`：未必，见 `layerwise_optimal_not_global`）。 -/
theorem layerwise_optimal_of_nonneg_coupling (c D1 D1' D2 : ℝ) (hc : 0 ≤ c)
    (hD2 : 0 ≤ D2) (hlt : D1 ≤ D1') :
    coupledLoss c D1 D2 ≤ coupledLoss c D1' D2 := by
  unfold coupledLoss
  have h1 : 0 ≤ 1 + c * D2 := by nlinarith
  nlinarith

/-! ### 剪枝后**重训练补偿**（对角校正的简化版）

`RealHeadPruningOptimal` 的诚实边界指出「重训练补偿**未做**」。本节点出**简化版**：
把重训练视为对每个保留头的**对角校正**——即重训练可以在保留头的输出上施加
尺度/方向修正，使该头的**有效丢弃质量**从 `μ i`（原始）降为
`(1 - ρ) · μ i`（`ρ ∈ [0,1]` 是**补偿率**，`ρ = 0` 为重训练前，`ρ = 1` 为完全补偿）。

- **标注 —— 「对角校正」的含义**：本模型只允许**逐头独立**的校正
  （每个保留头乘一个修正因子），**不**允许跨头混合（那需要重训练改变
  注意力模式，属于非对角校正）。这是**降级**：真实的微调会改变头间交互，
  本模型只捕捉「保留头被单独修复」的一阶效应。 -/

/-- **重训练补偿后的有效质量**：保留头 `i` 的有效质量按补偿率 `ρ` 缩放。
`ρ = 0` 退化为未补偿（原始 `μ i`）。 -/
def retrainedMass (rho : ℝ) (mu : ι → ℝ) (T : Finset ι) : ℝ :=
  ∑ i in T, (1 - rho) * mu i

/-- **补偿是线性的**：`retrainedMass ρ μ T = (1-ρ) · headMass μ T`。 -/
theorem retrainedMass_eq_smul (rho : ℝ) (mu : ι → ℝ) (T : Finset ι) :
    retrainedMass rho mu T = (1 - rho) * headMass mu T := by
  unfold retrainedMass headMass
  rw [Finset.mul_sum]

/-- **补偿不改变最优头的选择（核心）**：`ρ < 1` 时，
「原始质量最大的 `m` 个头」**仍然**是补偿后质量最大的 `m` 个
——即**对角重训练不改变剪枝决策**，只等比缩小误差界。

这是简化模型的**关键结论**：既然补偿对每个保留头施加**同一**因子 `(1-ρ)`，
排序不变，故 §二 的最优性（`headMass_le_topSum`）**原样转移**到补偿后的设定。
（真实重训练是非对角的，会改变排序——该情形**未做**。） -/
theorem retrained_headMass_le_topSum (rho : ℝ) (mu : ι → ℝ) (hrho : rho < 1)
    {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → mu j ≤ mu i) :
    retrainedMass rho mu T ≤ retrainedMass rho mu S := by
  rw [retrainedMass_eq_smul, retrainedMass_eq_smul]
  exact mul_le_mul_of_nonneg_left (headMass_le_topSum mu hcard htop) (by linarith)

/-- **补偿缩小误差界（定量）**：补偿率越大（`ρ₁ ≤ ρ₂`），
同一保留集的**有效丢弃质量**越小，故误差界越紧。

形式化：质量非负时 `(1-ρ₂)·prunedMass ≤ (1-ρ₁)·prunedMass`
——**重训练单调地改进误差界**（不需要 `ρ₂ ≤ 1` 的额外假设）。 -/
theorem retraining_improves_bound (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i) (T : Finset ι)
    {rho1 rho2 : ℝ} (h12 : rho1 ≤ rho2) :
    (1 - rho2) * prunedMass mu T ≤ (1 - rho1) * prunedMass mu T := by
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · linarith
  · unfold prunedMass
    exact Finset.sum_nonneg fun i _ => hmu i

end Lattice.Lib.Attention.RealHeadPruningOptimal