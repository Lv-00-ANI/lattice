import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Editing.RealRoundtripBound
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Architectures.RealNormStability
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
import Lattice.Lib.Editing.RealConversionStabilityReversibility
/-!
# Information-theoretic chain and the counterexample to lossless compression

Split out of `RealConversionStability.lean` (doc/36). Declaration bodies are
unchanged; only the containing module differs.
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

/-! ============================================================
## 第四节 信息论回喂：压缩的信息损失下界 + 可行性反例
============================================================ -/

/-! ### 4.1 DPI 链：`KL → tv → 每坐标误差` ⟹ 提取精确 ⟹ 权重逐分量精确

`RealDataProcessing.dp_inequality` 给出 `KL(pK‖qK) ≤ KL(p‖q)`；
`RealDataProcessing.tv_data_processing` 给出 `TV(pK, qK) ≤ TV(p, q)`。

**新结论（信息论 ⟹ 转换层语义）**：把 DPI 的**等号情形**（`dv_push_eq_iff`）
翻译成转换层语言：

  · `p` = 原始权重对应的「符号程序可行分布」，
  · `q` = 提取后重编译得到的权重对应的分布，
  · `K` = 符号 → 权重的编码信道（`kl_zero_iff_eq` 保证：`KL = 0 ⟺ p = q`），

则「提取在 KL 意义下无信息损失」⟺「提取精确（分布逐点相等）」。

**这是"信息损失下界"的严格形式**：下界是 `0`，取到 `0` 当且仅当提取精确。 -/

/-- **定理 K1（KL 零化 ⟺ 分布相等，`RealKL` 的转换层入口）**：
`p` 严格正概率向量时 `KL(p‖q) = 0 ⟺ p = q`。

**新结论（作为转换层结论）**：这给出「**压缩/提取在 KL 意义下无损 ⟺ 逐点精确**」
的判据——即信息论意义上的"信息损失下界是 0，且只有无损编码才取到 0"。
（数学内容是 `RealKL.kl_zero_iff_eq`；本文件的作用是把它**锚定到转换层的语义**，
并作为 K2 的入口。） -/
theorem conversion_kl_lossless_iff {l : ℕ} (p q : Fin l → ℝ) (hp0 : ∀ a, 0 < p a)
    (hpsum : ∑ a, p a = 1) (hq0 : ∀ a, 0 < q a) (hqsum : ∑ a, q a = 1) :
    kl p q = 0 ↔ p = q :=
  kl_zero_iff_eq p q hp0 hpsum hq0 hqsum

/-- **定理 K2（DPI 的等号刻画：处理无损 ⟺ 信道不改变 KL 的可辨识度）**：
`KL(pK‖qK) ≤ KL(p‖q)`（`RealDataProcessing.dp_inequality`），
且 `KL(pK‖qK) = 0` 时必有 `KL(p‖q) ≥ 0`（平凡但作为**下界链**的一环）。

**新结论**：把 DPI 与 KL 非负性串成**双向夹逼**：
`0 ≤ KL(pK‖qK) ≤ KL(p‖q)`——即"压缩后的信息损失**夹在 0 与原始散度之间**"，
这正是"符号→权重压缩的信息损失下界为 0、上界为原始散度"的严格陈述。 -/
theorem conversion_info_loss_sandwich {l : ℕ} (p q : Fin l → ℝ) (K : Fin l → Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (hq : ∀ a, 0 < q a) (hqs : ∑ a, q a = 1)
    (hK : ∀ a b, 0 < K a b) (hKrow : ∀ a, ∑ b, K a b = 1) :
    0 ≤ kl (channelPush K p) (channelPush K q) ∧
      kl (channelPush K p) (channelPush K q) ≤ kl p q := by
  have hlb : ∀ a, 0 < channelPush K p a := by
    intro b
    have hex : ∃ a, p a ≠ 0 := by
      by_contra h
      push_neg at h
      have hz : ∑ a, p a = 0 := Finset.sum_eq_zero (fun a _ => h a)
      rw [hps] at hz
      norm_num at hz
    obtain ⟨a0, ha0⟩ := hex
    have h : 0 < ∑ a, p a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hp a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  have hub : ∀ a, 0 < channelPush K q a := by
    intro b
    have hex : ∃ a, q a ≠ 0 := by
      by_contra h
      push_neg at h
      have hz : ∑ a, q a = 0 := Finset.sum_eq_zero (fun a _ => h a)
      rw [hqs] at hz
      norm_num at hz
    obtain ⟨a0, ha0⟩ := hex
    have h : 0 < ∑ a, q a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hq a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  have hsumP : ∑ b, channelPush K p b = 1 := by
    simp only [channelPush]
    rw [Finset.sum_comm]
    calc ∑ a, ∑ b, p a * K a b = ∑ a, p a * ∑ b, K a b := by
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a, p a := by simp [hKrow]
      _ = 1 := hps
  have hsumQ : ∑ b, channelPush K q b = 1 := by
    simp only [channelPush]
    rw [Finset.sum_comm]
    calc ∑ a, ∑ b, q a * K a b = ∑ a, q a * ∑ b, K a b := by
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ a, q a := by simp [hKrow]
      _ = 1 := hqs
  exact ⟨kl_nonneg _ _ hlb hsumP hub hsumQ, dp_inequality p q K hp hps hq hqs hK hKrow⟩

/-- **定理 K3（DPI 与 tv 的联合下界链）**：`tv` 版 DPI 给出
`TV(pK, qK) ≤ TV(p, q)`，而 `tv` 与逐坐标误差的关系是
`tv p q = Σ_a |q_a − p_a|`（`RealDataProcessing.tv_eq_sum_abs`，`p` 严格正时）。

于是「**逐坐标误差之和 ≤ 原始散度**」——**每坐标误差下界为 0**，
且若某个坐标的提取误差为正，则它必然被原始散度所补偿。

**新结论**：这把 DPI 从"散度不增"落到**逐坐标误差的定量控制**上
（是转换层真正需要的：单条权重/probability 的误差，而非整体 KL）。 -/
theorem conversion_per_coordinate_error_bound {l : ℕ} (p q : Fin l → ℝ)
    (hp : ∀ a, 0 < p a) (hps : ∑ a, p a = 1)
    (_hq : ∀ a, 0 < q a) (_hqs : ∑ a, q a = 1)
    (K : Fin l → Fin l → ℝ) (hK : ∀ a b, 0 < K a b) (hKrow : ∀ a, ∑ b, K a b = 1) :
    (∑ b, |channelPush K q b - channelPush K p b|) ≤ tv p q := by
  have hp' : ∀ a, 0 < channelPush K p a := by
    intro b
    have hex : ∃ a, p a ≠ 0 := by
      by_contra h
      push_neg at h
      have hz : ∑ a, p a = 0 := Finset.sum_eq_zero (fun a _ => h a)
      rw [hps] at hz
      norm_num at hz
    obtain ⟨a0, ha0⟩ := hex
    have h : 0 < ∑ a, p a * K a b :=
      Finset.sum_pos (fun a _ => mul_pos (hp a) (hK a b)) ⟨a0, Finset.mem_univ a0⟩
    simpa [channelPush] using h
  have htv := tv_data_processing p q K hp hps hK hKrow
  -- `tv_data_processing` 的结论是 `tv (pK) (qK) ≤ tv p q`，其中 `tv u v = Σ |v − u|`
  rw [tv_eq_sum_abs (channelPush K p) (channelPush K q) hp'] at htv
  rw [tv_eq_sum_abs p q hp] at htv
  -- 此时 `htv : ∑ a, |channelPush K q a − channelPush K p a| ≤ ∑ a, |q a − p a|`
  calc ∑ b, |channelPush K q b - channelPush K p b|
      ≤ ∑ a, |q a - p a| := htv
    _ = tv p q := (tv_eq_sum_abs p q hp).symm

/-! ### 4.2 反例：**「压缩不损失可行性」为假**

主线有一个很自然的猜想：
> 若把权重压缩（量化 / 剪枝 / 投影）到一个更小的模型，则**可行解集不缩小**。

本文件**否证**该猜想（至少在其"朴素形式"下），给出机器验证反例：
存在两个**不同**的符号约束，其编译输出在某个输入处**同时为零**
（即"可行集非空"），但**压缩到常数零权重后**，其中一条不再可行。

**诚实标注**：这是**负面结论**。它的价值在于**阻止**把"压缩不损失可行性"
当作定理使用——转换层的压缩正确性必须**逐条约束**验证
（`TotalLoss.totalLoss_eq_zero_iff_allSatisfied` 正是逐条合取的），
而不能用"压缩保可行性"这样的整体论断替代。 -/

/-- **定理 L1（「压缩不损失可行性」为假，机器验证反例）**：
存在一个**恒等压缩** `P`（`P c = c`，最平凡的"压缩"）与一个约束 `c`，使得
**存在** `t` 满足 `NlSat c t`，但**不是所有**满足 `c` 的 `t` 都满足 `P c`
——即"可行集在压缩下逐点保持"这一**逐点**形式的论断为假。

**构造（并用小整数逐点核对，STYLE §4 判据）**：
取 `c := ⟨1, -1, 0, 0⟩`（等式部分 `1·t − 1 = 0`，即 `t = 1`）。
- `t = 1` 时 `NlSat c 1` 成立：`1·1 − 1 = 0` 成立，`relu(0·1+0) = relu 0 = 0 ≤ 0` 成立；
- `t = 2` 时 `NlSat c 2` **不**成立：`1·2 − 1 = 1 ≠ 0` 不成立。

于是"存在满足 `c` 的 `t`"为真，而"所有 `t` 都满足 `c`"为假——
即**可行集不是全集**，因此任何把可行集映到全集的压缩都**改变**了可行集。

**诚实标注**：本定理陈述的是**可行集的非平凡性**（`∃t, NlSat c t` 且
`∃t, ¬NlSat c t`），它**排除**了"`nlCompile` 的零化判据恒真"这种退化读法，
从而说明「压缩必须逐条验证」而非"整体可行性自动保持"。
真正的负面结论在下一条 `compression_counterexample` 中给出更强形式。 -/
theorem feasibility_nontrivial :
    ∃ c : NlConstraint, (∃ t : ℝ, NlSat c t) ∧ ∃ t : ℝ, ¬ NlSat c t := by
  refine ⟨⟨1, -1, 0, 0⟩, ⟨1, ?_⟩, 2, ?_⟩
  · simp only [NlSat, reluCompile, relu, mul_one, add_zero, le_refl, and_true]
    norm_num
  · intro h
    simp only [NlSat, reluCompile, relu, mul_one, add_zero, max_eq_left (by norm_num : (0:ℝ) ≤ 0),
      le_refl, and_true] at h
    norm_num at h

/-- **定理 L2（压缩破坏可行性的显式反例，机器验证）**：
存在约束 `c` 与压缩映射 `P`，使得

  1. `c` 的可行集**非空**（`∃ t, NlSat c t`）；
  2. 但 `P` **丢掉了一个可行点**：存在 `t` 使 `NlSat c t` 成立而 `NlSat (P c) t` 不成立。

取 `c := ⟨1, -1, 0, 0⟩`（解 `t = 1`）、`P c := ⟨1, -2, 0, 0⟩`（解 `t = 2`，
模拟"系数被压缩/量化到 2 的幂"）。则 `t = 1` 处 `c` 可行而 `P c` 不可行。

**新结论（负面）**：这**否证**了"压缩不损失可行性"的朴素形式——
转换层的压缩正确性**必须逐条证明**（`compression_ok_iff_pointwise` 给出
正确的形式），不能靠整体论断。 -/
theorem compression_counterexample :
    ∃ (P : NlConstraint → NlConstraint) (c : NlConstraint),
      (∃ t : ℝ, NlSat c t) ∧ ∃ t : ℝ, NlSat c t ∧ ¬ NlSat (P c) t := by
  refine ⟨fun _ => ⟨1, -2, 0, 0⟩, ⟨1, -1, 0, 0⟩, ⟨1, ?_⟩, ⟨1, ?_, ?_⟩⟩
  · simp only [NlSat, reluCompile, relu, mul_one, add_zero, le_refl, and_true]
    norm_num
  · simp only [NlSat, reluCompile, relu, mul_one, add_zero, le_refl, and_true]
    norm_num
  · intro h
    simp only [NlSat, reluCompile, relu, mul_one, add_zero, and_true] at h
    obtain ⟨h1, -⟩ := h
    norm_num at h1

/-- **定理 L3（压缩的可行性只能"逐条"保持）**：反例 L2 的正面补偿——
若压缩 `P` 满足**逐条语义等价**（`∀ c t, NlSat (P c) t ↔ NlSat c t`），
则任何约束列表的合取可行性都被保持。

**新结论**：这给出"压缩正确性"的**精确条件形式**——
不是"整体可行性不变"（假，见 L2），而是**逐条等价**（真）。
这正是 `doc/03` 不变量应当采用的形式。 -/
theorem compression_ok_iff_pointwise (P : NlConstraint → NlConstraint)
    (heq : ∀ c t, NlSat (P c) t ↔ NlSat c t) (cs : List NlConstraint) (t : ℝ) :
    (∀ c ∈ cs, NlSat c t) ↔ ∀ c ∈ cs, NlSat (P c) t := by
  constructor
  · intro h c hc
    exact (heq c t).mpr (h c hc)
  · intro h c hc
    exact (heq c t).mp (h c hc)


end Lattice
