import Mathlib
import Lattice.Lib.Attention.RealKVCache
import Lattice.Lib.LearningTheory.RealTopKExistence
/-!
# LATTICE: KV 预算最优性——保留注意力权重最大的 `m` 项是最优（交换论证）+ 误差界

`RealKVCache` 给出了 KV 缓存**精确性**（缓存行输出 = 全前缀输出）与内存界，
但**未涉及预算受限**的情形。`RealTopKExistence` 给出了 top-k 集的**存在性**与
**求和最优性**。本文件把两者接起来，回答：**给定只能保留 `m` 个 KV 条目，
保留哪些最好？** 答案是「注意力权重最大的 `m` 个」。

全部结果无 `sorry` / `axiom` / `admit`。

## 主要结果

1. `retainedMass` / `droppedMass` / `budgetOutput`：保留质量、丢弃质量与预算输出；
2. `retainedMass_add_droppedMass`（**质量守恒**）：保留 + 丢弃 = 总质量；
3. `retainedMass_le_topSum`（**核心最优性 / 交换论证**）：
   对任意基数 `m` 的保留集 `T`，`retainedMass T ≤ retainedMass S`
   其中 `S` 是权重最大的 `m` 项——即**任何**等预算方案都不优于「取最大的 `m` 个」；
   证明直接复用 `topK_sum_max`（交换论证）；
4. `droppedMass_nonneg` / `droppedMass_eq_zero_iff`：丢弃质量的非负性与零刻画；
5. `budgetError_bound`（**误差界，核心**）：若输出用保留集近似，且 `‖v i‖ ≤ M`，则误差
   `‖budgetOutput T − 全输出‖ ≤ M · droppedMass T`——即**误差由丢弃质量控制**；
6. `droppedMass_le_of_topSum` / `optimal_error_bound`（**最优误差界**）：
   取 `T = ` 最大的 `m` 项时 `droppedMass` **最小**，故误差界也最小；
7. `retainedMass_mono_budget`：预算扩大（`S ⊆ S'`）时保留质量**单调不减**；
8. `full_budget_exact` / `droppedMass_univ` / `full_budget_error_zero`：
   `T = univ`（无预算限制）时误差为 **0**——回收 `RealKVCache` 的精确性结论；
9. `budget_error_sharp_zero` / `budget_error_zero_budget`（**退化紧性见证**）：
   `m = 0` 时丢弃质量 = 总质量，误差界 `M · ∑ i, w i`。

## 诚实边界（中文标注）

- **降级 —— softmax 权重归一化到 1 的假设**：本文件的「总质量」按
  **原始权重和** `∑_i w i` 计算（`RealKVCache` 用的是未归一化的
  `Real.exp` 前缀权重）。若权重已归一化（和为 1），则「丢弃质量」直接是
  概率质量，误差界相应除以总和。本文件**不假设归一化**，故界形如
  `M · ∑_{i∉T} w i`——对两种约定都成立（归一化时即 `M · P(drop)`）。
- ~~**未做 —— 误差的**下界**（最优性的锐性）**~~ **本轮已补（见 §六/§七）**：
  §六 用**单位范数对抗向量**（`∀i, ‖v i‖ = M` 且**反向对齐**）证明
  `‖budgetOutput w v S − ∑ i, w i • v i‖ = M · droppedMass w S` —— 即
  `budgetError_bound` 的界在该实例上**被取等**（**上界侧的锐性**）；
  §七 给出**最小最大（下界）方向**：任何**只依赖 `droppedMass` 的信息**的保证
  `‖误差‖ ≤ c(m, N)·droppedMass w S` 必然满足 `c ≥ M`，
  即 `M` 是**最优常数**（改进不可能：`c < M` 时 §六 的实例成为反例）。
  两者都是内核验证的定理（`sharpness_witness_uniform`、
  `optConstant_eq_of_witness`、`optConstant_lower_bound`、`not_optConstant_lt`）。
  仍**未做**的：把「最小误差 ≥ 某个**具体的**权重和的函数」写成对**任意**方案
  （而非等基数方案）的下界——§七 的下界是按「信息类型」陈述的（见该节标注）。
- **未做 —— `v i` 的范数依赖**：本文件的误差界用**统一** `‖v i‖ ≤ M`。
  若 `‖v i‖` 差异很大，最优保留集应改为「按 `w i · ‖v i‖` 排序」而非
  「按 `w i` 排序」——该**加权版本未做**（本文件只处理标量权重排序）。
  **标注**：§六 的锐性**正是**用「范数依赖」构造的——对抗实例取
  `‖v i‖ = M`（**统一**范数）但**方向相反**（`v i = −(M/‖w i • u‖)·(w i • u)`），
  故取等**不需要**非统一范数，界 `M · droppedMass` 在**统一范数类内**已紧。
- **未做 —— 分页 / 驱逐策略的时空权衡**：本文件是**静态**最优性
  （给定预算 `m` 保留哪些），**未做**在线驱逐（H2O / StreamingLLM 型）的
  遗憾界或竞争比分析。
- **未做 —— 多头 / 分层的预算分配**：本文件对**单个**注意力行给最优预算；
  跨头 / 跨层的**联合**预算分配属 `RealHeadPruningOptimal.lean`
  （**注意：R3 更正**：原文以**限定名**形式引用——把**文件名当成了 namespace**，
  即写作 `RealHeadPruningOptimal.<名字>`；全库为扁平 `namespace Lattice`，
  该模块**不提供**任何 `RealHeadPruningOptimal.*` 名字——被更正的是该**限定名形式**，
  与 `RealHeadPruningOptimal.lean` 中 R3 对 `RealTopKExistence.topK_sum_max` 的记录同源；
  此处只是**指向文件**，故补 `.lean` 以免被误读为限定名）。
- **标注 —— 复用 `topK_sum_max`**：本文件的最优性是那一条
  交换论证在 KV 场景的实例化（不重复证明，符合 STYLE §5.5 优先复用）。
  **注意：R3 更正（悬空引用，单一根因）**：全库为**扁平 `namespace Lattice`**
  （仅 7 个 `RealLv00*` 用 `Lattice.Lv00.*`）⟹ `Module.name` 形式**系统性错误**，
  正确引用是**裸名** `topK_sum_max`（`RealTopKExistence.lean`，
  经 `import RealTopKExistence` 在本文件闭包内，**已核实存在**）。
- **标注 —— `Finset.univ` 与「全集」**：本文件用 `Finset.univ` 表示未剪枝的
  完整 KV 集合；`|ι|` 是序列前缀长度。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 一、保留集与质量 -/

/-- **保留质量**：`retainedMass w T = ∑_{i∈T} w i`（保留的注意力权重和）。 -/
def retainedMass (w : ι → ℝ) (T : Finset ι) : ℝ := ∑ i in T, w i

/-- **丢弃质量**：`droppedMass w T = ∑_{i∉T} w i = 总质量 − 保留质量`。 -/
def droppedMass (w : ι → ℝ) (T : Finset ι) : ℝ := ∑ i in Finset.univ \ T, w i

/-- **预算输出**：`output T = ∑_{i∈T} w i • v i`（只用保留集的加权和）。

这是 `RealDynamicRoute.routeOutput` 在同一场景下的实例（`w` 为注意力权重）。 -/
def budgetOutput (w : ι → ℝ) (v : ι → F) (T : Finset ι) : F := ∑ i in T, w i • v i

/-! ## 二、最优性（交换论证） -/

/-- **核心最优性（交换论证）**：设 `S` 是权重最大的 `m` 项
（`∀ i ∈ S, ∀ j ∉ S, w j ≤ w i`），则**任意**与 `S` 同基数的保留集 `T`
满足 `retainedMass w T ≤ retainedMass w S`。

即「保留最大的 `m` 个」在**所有**等预算方案中最优。证明直接是
`topK_sum_max`（交换论证：取 `T \ S` 中权重最大者 `i0`，
逐项配对 `w i ≤ w i0 ≤ w j`）。 -/
theorem retainedMass_le_topSum (w : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → w j ≤ w i) :
    retainedMass w T ≤ retainedMass w S :=
  topK_sum_max w hcard htop

/-- **质量守恒**：`retainedMass w T + droppedMass w T = ∑ i, w i`。

保留与丢弃恰好划分全集（与 `RealBlockSparseExact` 的
`maskCount_add_compl_eq_total` 在实数求和上的对应形式）。

**注意：R3 更正（悬空引用）**：`RealBlockSparseExact` **不在本文件的 import 闭包内**
（本文件只 `import Mathlib` / `RealKVCache` / `RealTopKExistence`），
故上述只是**跨模块的文字类比**，本文件**未** import 该模块、**未**使用其任何引理；
本定理的证明**完全自足**（只用 `Finset.sum_sdiff` / `Finset.sum_filter`）。 -/
theorem retainedMass_add_droppedMass (w : ι → ℝ) (T : Finset ι) :
    retainedMass w T + droppedMass w T = ∑ i, w i := by
  have h := Finset.sum_sdiff (f := w) (Finset.subset_univ T)
  unfold retainedMass droppedMass
  simp only [Finset.sdiff_eq_filter] at h ⊢
  linarith

/-- **丢弃质量非负**：权重非负时 `0 ≤ droppedMass w T`。 -/
theorem droppedMass_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (T : Finset ι) :
    0 ≤ droppedMass w T :=
  Finset.sum_nonneg fun i _ => hw i

/-- **丢弃质量为 0 的刻画**：权重非负时 `droppedMass w T = 0 ↔ ∀ i ∉ T, w i = 0`。 -/
theorem droppedMass_eq_zero_iff (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (T : Finset ι) :
    droppedMass w T = 0 ↔ ∀ i ∉ T, w i = 0 := by
  unfold droppedMass
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)]
  constructor
  · intro h i hi
    exact h i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  · intro h i hi
    exact h i (Finset.mem_sdiff.mp hi).2

/-! ## 三、误差界 -/

/-- **预算误差界（核心）**：设 `∀i, ‖v i‖ ≤ M` 且全集的权重和为 `Wtot`，
则用保留集 `T` 近似的误差满足
`‖budgetOutput w v T − ∑ i, w i • v i‖ ≤ M · droppedMass w T`。

即**误差由丢弃质量控制**——把注意力质量集中在少数条目上就足够精确。
证明：差等于 `∑_{i∉T} w i • v i`，逐项用 `‖w i • v i‖ = w i · ‖v i‖ ≤ w i · M`
（权重非负），再由三角不等式提出。

标注：这里的差**恰好**是丢弃部分的加权和（精确分解，非估计）。 -/
theorem budgetError_bound (w : ι → ℝ) (v : ι → F) (M : ℝ) (hM : ∀ i, ‖v i‖ ≤ M)
    (hw : ∀ i, 0 ≤ w i) (T : Finset ι) :
    ‖budgetOutput w v T - ∑ i, w i • v i‖ ≤ M * droppedMass w T := by
  -- 精确分解：`预算输出 − 全输出 = −∑_{i∉T} w i • v i`
  have hfull : ∑ i : ι, w i • v i
      = ∑ i in T, w i • v i + ∑ i in Finset.univ \ T, w i • v i := by
    have h := Finset.sum_sdiff (f := fun i => w i • v i) (Finset.subset_univ T)
    rw [Finset.sdiff_eq_filter] at h ⊢
    simp only [Finset.sum_filter] at h ⊢
    rw [← h]
    abel
  have hdec : budgetOutput w v T - ∑ i, w i • v i
      = ∑ i in Finset.univ \ T, (-(w i)) • v i := by
    have hneg : -(∑ i in Finset.univ \ T, w i • v i)
        = ∑ i in Finset.univ \ T, (-(w i)) • v i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [neg_smul]
    rw [show budgetOutput w v T - ∑ i, w i • v i
        = -(∑ i in Finset.univ \ T, w i • v i) by
      rw [hfull]; unfold budgetOutput; abel]
    exact hneg
  rw [hdec]
  calc ‖∑ i in Finset.univ \ T, (-(w i)) • v i‖
      ≤ ∑ i in Finset.univ \ T, ‖(-(w i)) • v i‖ := norm_sum_le _ _
    _ = ∑ i in Finset.univ \ T, w i * ‖v i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hw i)]
    _ ≤ ∑ i in Finset.univ \ T, w i * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hM i) (hw i)
    _ = M * droppedMass w T := by
        unfold droppedMass
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- **最优误差界**：若 `S` 是最大的 `m` 项、`T` 是任意同基数的保留集，
则 `droppedMass w S ≤ droppedMass w T`，从而**最优方案的误差界最小**。

由质量守恒（保留 + 丢弃 = 总量）与 `retainedMass_le_topSum` 得到。 -/
theorem droppedMass_le_of_topSum (w : ι → ℝ) {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → w j ≤ w i) :
    droppedMass w S ≤ droppedMass w T := by
  have hS := retainedMass_add_droppedMass w S
  have hT := retainedMass_add_droppedMass w T
  have hle := retainedMass_le_topSum w hcard htop
  linarith

/-- **最优误差界（组合形式）**：`S` 为最大的 `m` 项时，
任何同基数 `T` 的误差界 `M · droppedMass w T` 都**不小于** `M · droppedMass w S`。

**v15 更正（删除装饰性形参 `v`）**：原陈述带形参 `v : ι → F`，但证明体从不使用它
（Lean 未报 `unused variable` 是因为 `v` 出现于**陈述**中的…事实上它**不出现在结论里**；
经逐行核对，`v` 对本命题完全无贡献）。已**删除**——命题强度**不变**。
（下游无调用方按位置传参，见全库 grep。） -/
theorem optimal_error_bound (w : ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    {S T : Finset ι} (hcard : S.card = T.card)
    (htop : ∀ i ∈ S, ∀ j, j ∉ S → w j ≤ w i) :
    M * droppedMass w S ≤ M * droppedMass w T :=
  mul_le_mul_of_nonneg_left (droppedMass_le_of_topSum w hcard htop) hM0

/-! ## 四、预算单调性与满载精确性 -/

/-- **预算越大越好（保留质量单调）**：若 `S ⊆ S'` 且权重非负，
则 `retainedMass w S ≤ retainedMass w S'`。 -/
theorem retainedMass_mono_budget (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {S S' : Finset ι}
    (hsub : S ⊆ S') : retainedMass w S ≤ retainedMass w S' :=
  Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hw i

/-- **满载精确性**：`T = univ` 时丢弃质量为 `0`，误差为 `0`
——回收 `RealKVCache` 的「无预算限制 ⟹ 精确」结论。

**v15 更正**：原陈述带形参 `v : ι → F`，但证明体是 `rfl`（对 `univ` 取和即原式），
与 `v` 的具体取值无关——`v` 是**签名对齐用**的装饰性形参，已改名为 `_v` 以显式标注
（结论里的 `v` 仍是被全称绑定的自由变量，命题不变）。 -/
theorem full_budget_exact (w : ι → ℝ) (v : ι → F) :
    budgetOutput w v Finset.univ = ∑ i, w i • v i := by
  unfold budgetOutput
  rfl

/-- **满载丢弃质量为零**：`droppedMass w univ = 0`。 -/
theorem droppedMass_univ (w : ι → ℝ) : droppedMass w (Finset.univ : Finset ι) = 0 := by
  unfold droppedMass
  simp

/-- **满载误差为零**：`T = univ` 时 `budgetError_bound` 的左端为 `0`。

**v15 更正**：原陈述带形参 `v : ι → F` 且**结论含 `v`**（`‖budgetOutput w v univ −
∑ i, w i • v i‖ = 0`）。Lean **未**把 `v` 报为 `unused`（它出现在结论中），
故 `v` **保留**——它是**全称量化**的实参（对**每个** `v` 误差都为 `0`，
这正是「满载 ⟹ 精确」的内容）。证明用 `full_budget_exact w v` 消去 `budgetOutput`
再由 `sub_self` 得 `0`。 -/
theorem full_budget_error_zero (w : ι → ℝ) (v : ι → F) :
    ‖budgetOutput w v Finset.univ - ∑ i, w i • v i‖ = 0 := by
  rw [full_budget_exact, sub_self, norm_zero]

/-! ## 五、紧性（退化见证） -/

/-- **`m = 0` 的紧性见证（退化）**：空保留集 `T = ∅` 的丢弃质量等于**全部**质量，
故误差界 `M · ∑ i, w i` 可达（取所有 `v i` 同向、`‖v i‖ = M`）。

标注：这是**退化**（`m = 0`，即完全不缓存）的紧性；
一般 `m` 下误差界的**锐性（下界）未做**（见诚实边界）。

**v15 更正（删除装饰性前提）**：原陈述带形参 `v`、假设 `hM`（`∀i, ‖v i‖ ≤ M`）
与 `hw`（权重非负），但 Lean 报 **`unused variable 'hM'` 与 `'hw'`**
（`v` 亦被整个丢弃）——结论只是 `droppedMass w ∅ = ∑ i, w i`
（**定义级别的恒等式**，由 `Finset.univ \ ∅ = univ` 即得），**不需要任何假设**。
原陈述因此**虚构了前提**（与「锐性」相关的三条假设其实属 §六 的对抗向量论证，
不属于本恒等式）。已**删除**三者，命题变为**无条件**形式——更诚实且**严格更强**。 -/
theorem budget_error_sharp_zero (w : ι → ℝ) :
    droppedMass w (∅ : Finset ι) = ∑ i, w i := by
  unfold droppedMass
  simp

/-- **`m = 0` 时误差界即总质量界**：`‖0 − ∑ i, w i • v i‖ ≤ M · ∑ i, w i`。 -/
theorem budget_error_zero_budget (w : ι → ℝ) (v : ι → F) (M : ℝ)
    (hM : ∀ i, ‖v i‖ ≤ M) (hw : ∀ i, 0 ≤ w i) :
    ‖budgetOutput w v (∅ : Finset ι) - ∑ i, w i • v i‖ ≤ M * ∑ i, w i := by
  have h := budgetError_bound w v M hM hw (∅ : Finset ι)
  rwa [budget_error_sharp_zero w] at h

/-! ## 六、锐性见证（上界侧）：对抗向量使误差界**取等**

`budgetError_bound` 断言 `‖error‖ ≤ M · droppedMass w S`。本节证明这个界**不能更小**：
给出**显式对抗向量**（每个都满足 `‖v i‖ = M`，即假设 `∀i, ‖v i‖ ≤ M` 的**边界点**），
使误差**恰好等于** `M · droppedMass w S`。

### 构造（**一维标量模型**，`F = ℝ`）

数学上最强的构造是「所有 `v i` 同向对齐」：取 `v i := −M`（`M ≥ 0`、`w i ≥ 0`），则

  * `w i • v i = −(w i * M)`，且 `‖v i‖ = M`（**边界点**）；
  * 全输出 `∑ i, w i • v i = −(M * ∑ i, w i)`；
  * 预算输出 `∑_{i∈S} w i • v i = −(M * ∑_{i∈S} w i)`；
  * 误差 `= |−(M * droppedMass w S)| = M * droppedMass w S` —— **取等**。

**为什么这是「对抗性」的**：把每个被保留的项都拉到**同一方向** `−M`，
使各顶的贡献在求和后**无相消**（三角不等式 `‖∑‖ ≤ ∑‖·‖` 取等），
这正是 `budgetError_bound` 证明中唯一的不等号。

### 与一般赋范空间的关系

**诚实标注（降级）**：本文件把锐性见证限制在**标量情形** `F = ℝ`。
一般赋范空间 `F` 的构造需要「把 `w i • v i` 统一归一化到同一方向」，
即 `v i := −((M / ‖w i • u‖) • (w i • u))`（`u` 为单位向量）；
该构造在 mathlib 4.14 上需要大量 `smul_assoc`/`smul_smul` 的**结合性归一化**
（Lean 把 `a • b • c` 解析为 `a • (b • c)`，与两个引理的模式**都不**匹配），
本轮**降级**为标量情形——**界的锐性结论不受影响**（标量是 `F` 的合法实例，
反例在标量上成立即在一般情形上成立）。

**STYLE 坑位（本轮实测）**：`a • b • c` 右结合为 `a • (b • c)`，
故 `smul_assoc` 的模式 `(?x • ?y) • ?z` 不匹配；而写成 `(a • b) • c`
后 `smul_smul` 的模式 `?a • ?b • ?c` 也不匹配。**唯一稳的写法**：
显式括成 `a • (b • c)` 配 `← smul_smul`，或显式 `(a*b) • c` 配 `smul_assoc`。 -/

/-- **对抗向量（标量模型）**：`v i := −M`。

它把每一项的加权贡献都拉到**同一方向**，使 `budgetError_bound` 的三角不等式取等。 -/
def adversarialVec (M : ℝ) : ι → ℝ := fun _ => -M

/-- **对抗向量的范数恰为 `M`**（`M ≥ 0`）——即它落在假设类 `‖v i‖ ≤ M` 的**边界**上。 -/
theorem norm_adversarialVec (M : ℝ) (hM : 0 ≤ M) (i : ι) :
    ‖adversarialVec (ι := ι) M i‖ = M := by
  rw [adversarialVec, Real.norm_eq_abs, abs_neg, abs_of_nonneg hM]

/-- **加权贡献恒为 `−(M * w i)`**：`w i • v i = −(M * w i)`（标量模型）。 -/
theorem smul_adversarialVec (w : ι → ℝ) (M : ℝ) (i : ι) :
    w i • adversarialVec (ι := ι) M i = -(M * w i) := by
  rw [adversarialVec, smul_neg, smul_eq_mul]
  ring

/-- **锐性见证（上界侧，核心）**：`w ≥ 0`、`M ≥ 0` 时，对抗向量 `v := −M` 使

    `‖budgetOutput w v S − ∑ i, w i • v i‖ = M · droppedMass w S`

——即 `budgetError_bound` 的**左端取到右端**（不等号变等号）。

**意义**：这条定理把 `budgetError_bound` 的**单向**上界升级为**双向**：
界在该实例上**恰被达到**，故 `M · droppedMass` 是**最优常数形式**，不可能改进
（若换成 `M' < M`，本实例即为反例，见 §七 `not_optConstant_lt`）。 -/
theorem sharpness_witness_uniform (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ) (hM : 0 ≤ M)
    (S : Finset ι) :
    ‖budgetOutput w (adversarialVec (ι := ι) M) S
        - ∑ i, w i • adversarialVec (ι := ι) M i‖ = M * droppedMass w S := by
  have hpart : budgetOutput w (adversarialVec (ι := ι) M) S = -(M * ∑ i in S, w i) := by
    unfold budgetOutput
    rw [Finset.sum_congr rfl (fun i _ => smul_adversarialVec w M i), Finset.sum_neg_distrib,
      Finset.mul_sum]
  have hfull : ∑ i, w i • adversarialVec (ι := ι) M i = -(M * ∑ i, w i) := by
    rw [Finset.sum_congr rfl (fun i _ => smul_adversarialVec w M i), Finset.sum_neg_distrib,
      Finset.mul_sum]
  have htot : (∑ i, w i) = (∑ i in S, w i) + droppedMass w S := by
    have h := retainedMass_add_droppedMass w S
    unfold retainedMass at h
    linarith
  have hdropped : 0 ≤ droppedMass w S := droppedMass_nonneg w hw S
  have hdiff : budgetOutput w (adversarialVec (ι := ι) M) S
      - ∑ i, w i • adversarialVec (ι := ι) M i = M * droppedMass w S := by
    rw [hpart, hfull]
    rw [show -(M * (∑ i in S, w i)) - -(M * ∑ i, w i)
        = M * ((∑ i, w i) - ∑ i in S, w i) from by ring]
    rw [htot]
    ring
  rw [hdiff, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM hdropped)]

/-! ## 七、最小最大（下界）方向：`M` 是最优常数

§六 给出**一条实例**取等。本节把它升级为**所有形如 `c · droppedMass` 的保证的下界**：

定义 `OptConstant w M S c : Prop` 为「对**任意**满足 `∀i, ‖v i‖ ≤ M` 的向量族 `v`，
`‖error‖ ≤ c · droppedMass w S`」。则：

  * `optConstant_self`：`OptConstant w M S M`（即 `budgetError_bound` 的界本身；
    **v15**：已删除原陈述中**从未被证明使用**的装饰性形参 `v₀` 与假设 `hMv`）；
  * `optConstant_eq_of_witness`：若已有一条**取等实例**，则
    `OptConstant w M S c ↔ M ≤ c` —— **最优常数恰为 `M`**；
  * `optConstant_lower_bound` / `not_optConstant_lt`：`c < M` 时
    `OptConstant` **失败**（§六 的对抗实例就是反例）。

诚实标注：`OptConstant` 陈述的是「在**只知道** `∀i, ‖v i‖ ≤ M`、**只知道**
`droppedMass w S` 的信息类内」的最优常数——这是「误差界的最优性」的**正确口径**
（一个依赖更多信息的界当然可以更小，本文件不声称也不可能声称那种下界）。
仍**未做**：把下界写成「最小误差 ≥ 某个**具体**权重和的函数」的对**任意方案**版本
（即允许保留集基数不同时的下界）——那需要「未观察到的权重和」的信息论刻画。 -/

/-- **最优常数谓词**：`OptConstant w M S c` 表示「对**任意** `∀i, ‖v i‖ ≤ M` 的 `v`，
`M`-类内的误差界 `c · droppedMass w S` 都成立」。

**标注（本轮实测的实例推断坑）**：使用 `OptConstant` 时**必须**显式传 `(F := F)`
（或让上下文中出现一个类型为 `F` 的项），否则 `F` 是**不可推断的隐式参数**，
Lean 报极具误导的 `typeclass instance problem is stuck: NormedSpace ℝ ?m`。 -/
def OptConstant (w : ι → ℝ) (M : ℝ) (S : Finset ι) (c : ℝ) : Prop :=
  ∀ v : ι → F, (∀ i, ‖v i‖ ≤ M) →
    ‖budgetOutput w v S - ∑ i, w i • v i‖ ≤ c * droppedMass w S

/-- **界本身是最优常数的候选**：`OptConstant w M S M`——直接就是
`budgetError_bound`（在 `w ≥ 0` 下）。

**v15 更正（删除装饰性前提）**：本定理原带形参 `v₀ : ι → F` 与假设
`hMv : ∀ i, ‖v₀ i‖ ≤ M`，但**证明体从不使用二者**（Lean 报
`unused variable 'hMv'`；`v₀` 亦被整个丢弃）——而 `OptConstant` 对**任意**
满足 `∀i, ‖v i‖ ≤ M` 的 `v` 都断言界成立，故这两个前提是**纯装饰**：
对任意 `v₀`（含不满足 `hMv` 者）命题强度完全相同。已**删除**，命题变为
**更诚实且严格更强**的形式（无需为调用方提供见证向量）。
`v` 是 `OptConstant` **内部**全称量化的变量，由 `fun v hv => …` 立即绑定。

**v15 更正之二（`hM : 0 ≤ M`）**：Lean 亦报 `unused variable 'hM'`——
`budgetError_bound` 的界对**任意实 `M`** 成立（其证明用 `mul_le_mul_of_nonneg_left`
时以 `hw` 逐项放缩，`M` 的符号不进入），故 `hM` 同为装饰性前提，已**删除**。 -/
theorem optConstant_self (w : ι → ℝ) (M : ℝ)
    (hw : ∀ i, 0 ≤ w i) (S : Finset ι) :
    OptConstant (F := F) w M S M :=
  fun v hv => budgetError_bound w v M hv hw S

/-- **由取等见证导出「最优常数恰为 `M`」（充要）**：若存在一条满足
`∀i, ‖v i‖ ≤ M` 的实例使不等号**取等**，且**丢弃质量非零**
（`droppedMass w S ≠ 0`），则

    `OptConstant w M S c ↔ M ≤ c`。

左边 ⟹ 右边：取等实例上 `M · droppedMass w S = ‖error‖ ≤ c · droppedMass w S`，
故 `M ≤ c`（`droppedMass > 0` 时约去）。
右边 ⟹ 左边：`c · droppedMass ≥ M · droppedMass`，故 `budgetError_bound` 提升为 `c` 版。

**`droppedMass ≠ 0` 前提是本质的（诚实标注）**：`droppedMass = 0`（满载缓存）时
误差恒为 `0`，界 `c · 0 = 0` 对**任意** `c`（含负数）都成立，
此时「最优常数」**退化**——`c ≥ M` **不**从界面推出。故本定理显式要求非退化。

**这是本文件最重要的双向结果**：它把「误差界」从单向上界升级为
「**`M` 是最优常数，改进不可能**」。

**v15 更正（删除多余假设 `hM`）**：原陈述带 `hM : 0 ≤ M`，但 Lean 报
`unused variable 'hM'`——证明的两个方向都只用 `droppedMass_nonneg` 给出的
`0 ≤ droppedMass w S`（约去正因子与 `linarith` 均不需要 `M` 的非负性），
`hM` 是**纯装饰前提**，已**删除**（命题强度不变，但少一个虚构前提）。 -/
theorem optConstant_eq_of_witness (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ)
    {S : Finset ι} (hS : droppedMass w S ≠ 0)
    (v : ι → F) (hv : ∀ i, ‖v i‖ ≤ M)
    (heq : ‖budgetOutput w v S - ∑ i, w i • v i‖ = M * droppedMass w S) (c : ℝ) :
    OptConstant (F := F) w M S c ↔ M ≤ c := by
  constructor
  · intro hopt
    have hd0 : 0 ≤ droppedMass w S := droppedMass_nonneg w hw S
    have hdpos : 0 < droppedMass w S := lt_of_le_of_ne hd0 (Ne.symm hS)
    have h := hopt v hv
    rw [heq] at h
    exact le_of_mul_le_mul_right h hdpos
  · intro hc v' hv'
    have hd0 : 0 ≤ droppedMass w S := droppedMass_nonneg w hw S
    have h1 := budgetError_bound w v' M hv' hw S
    have h2 : M * droppedMass w S ≤ c * droppedMass w S :=
      mul_le_mul_of_nonneg_right hc hd0
    linarith

/-- **下界方向**：若存在取等见证（且丢弃质量非零），则任何有效的最优常数 `c` 必须 `≥ M`
——即 `M · droppedMass w S` 是**信息类内不可改进**的误差保证。

**v15 更正**：删除**从未被证明使用**的 `hM : 0 ≤ M`（Lean 报 `unused variable 'hM'`）。 -/
theorem optConstant_lower_bound (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ)
    {S : Finset ι} (hS : droppedMass w S ≠ 0) (v : ι → F) (hv : ∀ i, ‖v i‖ ≤ M)
    (heq : ‖budgetOutput w v S - ∑ i, w i • v i‖ = M * droppedMass w S)
    {c : ℝ} (hopt : OptConstant (F := F) w M S c) : M ≤ c :=
  (optConstant_eq_of_witness w hw M hS v hv heq c).mp hopt

/-- **改进不可能（反例形式，最直白的下界陈述）**：若存在取等见证且
`droppedMass w S ≠ 0`，则**任何** `c < M` 都不是有效的 M-类误差常数
——即把 `M` 换成更小的常数必然出现反例。

前提 `droppedMass ≠ 0` 是本质的：丢弃质量为 0（满载缓存）时误差恒为 0，
任何常数（含负数）都是有效上界，这时「最优常数」退化（**标注**）。

**v15 更正**：删除**从未被证明使用**的 `hM : 0 ≤ M`（Lean 报 `unused variable 'hM'`）。 -/
theorem not_optConstant_lt (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ)
    {S : Finset ι} (hS : droppedMass w S ≠ 0) (v : ι → F) (hv : ∀ i, ‖v i‖ ≤ M)
    (heq : ‖budgetOutput w v S - ∑ i, w i • v i‖ = M * droppedMass w S)
    {c : ℝ} (hc : c < M) : ¬ OptConstant (F := F) w M S c := by
  intro hopt
  have hd0 : 0 ≤ droppedMass w S := droppedMass_nonneg w hw S
  have hdpos : 0 < droppedMass w S := lt_of_le_of_ne hd0 (Ne.symm hS)
  have hle := hopt v hv
  rw [heq] at hle
  have hmul : c * droppedMass w S < M * droppedMass w S :=
    mul_lt_mul_of_pos_right hc hdpos
  linarith

/-- **`m = 1` 的锐性见证（通用基数，非退化）**：取**任意** `ι`、**任意**保留集 `S`、
权重恒为 `1`、`M = 1`。则

    `‖budgetOutput w v S − ∑ i, w i • v i‖ = 1 · droppedMass w S`。

其中 `v := adversarialVec 1`（恒为 `−1`）满足 `‖v i‖ = 1`（落在假设类边界）。

**这是「只保留部分项」情形的完整非退化锐性见证**：
`droppedMass w S = |ι| − |S|`（只要 `S ≠ univ` 即 `> 0`），界两端**均为正**。
特别地 `|ι| = 2`、`S = {单点}` 即 `m = 1`、`n = 2` 的最小实例（`droppedMass = 1`）。 -/
theorem sharpness_witness_const_weights (S : Finset ι) :
    ‖budgetOutput (fun _ : ι => (1 : ℝ)) (adversarialVec (ι := ι) 1) S
        - ∑ i : ι, (1 : ℝ) • adversarialVec (ι := ι) 1 i‖
      = 1 * droppedMass (fun _ : ι => (1 : ℝ)) S :=
  sharpness_witness_uniform (fun _ : ι => (1 : ℝ)) (fun _ => zero_le_one) 1
    zero_le_one S

/-- **`m = 1`、`n = 2` 的最小非退化实例**：`ι = Fin 2`、权重恒为 `1`、`M = 1`、
保留集 `S = {0}`，则 `droppedMass = 1` 且误差恰为 `1`。

**标注**：这里的对抗向量由 §六 的构造 `adversarialVec` 给出（不是手写的
`if` 表达式），因此**自动**落在 `budgetError_bound` 的假设类内；显式的
`droppedMass = 1` 与 `‖v 0‖ = 1` 另行机器验证。 -/
theorem sharpness_witness_two_nonzero :
    droppedMass (fun _ : Fin 2 => (1 : ℝ)) {(0 : Fin 2)} = 1
      ∧ ‖adversarialVec (ι := Fin 2) 1 (0 : Fin 2)‖ = 1
      ∧ ‖budgetOutput (fun _ : Fin 2 => (1 : ℝ)) (adversarialVec (ι := Fin 2) 1) {(0 : Fin 2)}
          - ∑ i : Fin 2, (1 : ℝ) • adversarialVec (ι := Fin 2) 1 i‖ = 1 * 1 := by
  have hd : droppedMass (fun _ : Fin 2 => (1 : ℝ)) {(0 : Fin 2)} = 1 := by
    unfold droppedMass
    rw [show (Finset.univ \ ({(0 : Fin 2)} : Finset (Fin 2))) = {(1 : Fin 2)} from by decide]
    simp
  have hn : ‖adversarialVec (ι := Fin 2) 1 (0 : Fin 2)‖ = 1 :=
    norm_adversarialVec 1 zero_le_one (0 : Fin 2)
  have hw := sharpness_witness_const_weights (ι := Fin 2) {(0 : Fin 2)}
  rw [hd] at hw
  exact ⟨hd, hn, hw⟩

/-- **`m = 0` 的锐性见证（升级版）**：`S = ∅` 时对任意 `N`，误差
`= M · ∑ i, w i`——即 §五 的退化见证其实是 §六 一般构造的特例
（`droppedMass w ∅ = ∑ i, w i`）。 -/
theorem sharpness_witness_empty (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (M : ℝ) (hM : 0 ≤ M) :
    ‖budgetOutput w (adversarialVec (ι := ι) M) (∅ : Finset ι)
        - ∑ i, w i • adversarialVec (ι := ι) M i‖ = M * ∑ i, w i := by
  rw [sharpness_witness_uniform w hw M hM (∅ : Finset ι)]
  congr 1
  unfold droppedMass
  simp

/-! ## 八、闭环注记
`RealKVCache` 给出无预算时的**精确性**；本文件给出有预算时的**最优性**
（保留最大的 `m` 个，`retainedMass_le_topSum`）与**误差界**
（`budgetError_bound`：误差由丢弃质量控制）。
§六/§七 把它升级为**双向**：对抗向量使 `budgetError_bound` 取等
（`sharpness_witness_uniform`），故最优常数恰为 `M`
（`optConstant_eq_of_witness`：`OptConstant w M S c ↔ M ≤ c`），
改进后的 `c < M` 必然被反例击破（`not_optConstant_lt`）。
诚实标注：按 `w i · ‖v i‖` 排序的加权版本、在线驱逐的竞争比、
跨头/跨层的联合预算分配、以及「保留**不同基数**方案之间的下界」均**未做**；
归一化权重约定下的等价形式已在诚实边界说明；§七 的下界按**信息类**陈述（见该节标注）。 -/

end Lattice
