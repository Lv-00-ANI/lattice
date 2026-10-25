import Mathlib
import Lattice.Lib.Quantization.RealQuantizedError
import Lattice.Lib.LinearAlgebra.RealSparsity
import Lattice.Lib.LearningTheory.RealDistill
/-!
# LATTICE: 量化 + 剪枝 + 蒸馏的联合压缩误差界

三种部署期压缩（RealQuantizedError 的权重量化、RealSparsity 的幅度剪枝、
RealDistill 的教师–学生蒸馏）在 n 层线性链上是**同一结构**：

  每层误差 ‖压缩层 − 参考层‖ ≤ δᵢ，经其后各层放大、其前各层放缩输入，
  端到端误差 = Σ_{i<n} (∏后层范数)·δᵢ·(∏前层范数)·‖x‖

（`quantized_chain_error_closed` / `prune_chain_error` / `chain_distill_bound`
三者逐项同构，只是 δᵢ 的来源不同：量化舍入、被剪分量、师生参数差）。
因此三种压缩同时作用时，可以**统一为逐层误差预算**：

  `jointDelta δq δp δd i = δq i + δp i + δd i`

本文件把这一统一框架形式化：

  1. `jointDelta`：逐层联合误差预算（三部分之和）；
  2. `compression_error_budget`（核心）：若参考层 `W i`、量化层 `Wq i`、
     剪枝层 `Wp i`（在量化层之上剪枝）、联合压缩层 `Wc i`（在前两者之上蒸馏）
     满足逐层界 ‖Wq−W‖ ≤ δq、‖Wp−Wq‖ ≤ δp、‖Wc−Wp‖ ≤ δd，则
     ‖Wc − W‖ ≤ δq + δp + δd（逐层三角不等式）；
  3. `joint_chain_error`（核心）：以 `δ_total_i = jointDelta … i` 直接实例化
     `RealQuantizedError.quantized_chain_error_closed`，得联合端到端界
     ——压缩 = 量化特例的统一框架；
  4. `joint_uniform_bound`（加分）：均匀情形（δq=dq、δp=dp、δd=dd、
     各层范数 ≤ L、L ≥ 1）⟹ 端到端 ≤ n·(dq+dp+dd)·Lⁿ·‖x‖
     （实例化 `quantized_uniform_error`）；
  5. `compression_dominance`（加分）：若某一种压缩误差恒为 0（如未剪枝），
     逐层预算退化为其余两部分之和（`jointDelta δq 0 δd = δq + δd`），
     链级界同步退化（`compression_dominance_chain`）。

诚实假设（与 RealQuantizedError 一致，均显式标注）：
  · 链为同维端射 `E →L[ℝ] E`（方阵/同维），层 0..n−1 依次作用；
  · 三个逐层误差界 δq/δp/δd 各自成立（它们分别来自 quantized_uniform /
    prune_magnitude_bound / layer_distill_bound 等既有结论）；
  · 联合链的构造顺序为「参考 → 量化 → 剪枝 → 蒸馏」（`W → Wq → Wp → Wc`），
    这是把三部分误差逐层相加的自然次序；若实际流水线次序不同，只需把
    `compression_error_budget` 中的三角不等式重排（结论形式不变）；
  · 均匀界需要 L ≥ 1（误差随层数扩张）与非负误差（dq,dp,dd ≥ 0）——
    与 `quantized_uniform_error` 的诚实假设相同；L < 1 时误差被收缩层衰减，
    需 Σᵢ d·Lⁱ 形式，此处不展开（与既有文件一致）。
全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 联合逐层误差预算（三部分之和） -/

/-- 联合逐层误差预算：量化误差 `δq` + 剪枝误差 `δp` + 蒸馏误差 `δd`。
三者同层叠加（同一结构：逐层误差 + 链式传播）。 -/
def jointDelta (δq δp δd : ℕ → ℝ) : ℕ → ℝ :=
  fun i => δq i + δp i + δd i

/-! ## 定理一（核心）：逐层总误差 ≤ 三部分之和

参考层 `W`、量化层 `Wq`、剪枝层 `Wp`（量化之上剪枝）、联合压缩层 `Wc`
（蒸馏）满足逐层界 ⟹ 联合层误差被 `jointDelta` 界住（逐层三角不等式：
`‖Wc − W‖ = ‖(Wc − Wp) + (Wp − Wq) + (Wq − W)‖ ≤ δd + δp + δq`）。 -/

theorem compression_error_budget (W Wq Wp Wc : ℕ → E →L[ℝ] E) (δq δp δd : ℕ → ℝ)
    (n : ℕ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δq i)
    (hp : ∀ i, i < n → ‖Wp i - Wq i‖ ≤ δp i)
    (hd : ∀ i, i < n → ‖Wc i - Wp i‖ ≤ δd i) :
    ∀ i, i < n → ‖Wc i - W i‖ ≤ jointDelta δq δp δd i := by
  intro i hi
  have h1 := hd i hi
  have h2 := hp i hi
  have h3 := hq i hi
  calc
    ‖Wc i - W i‖ = ‖(Wc i - Wp i) + (Wp i - Wq i) + (Wq i - W i)‖ := by
      congr 1
      abel
    _ ≤ ‖Wc i - Wp i‖ + ‖Wp i - Wq i‖ + ‖Wq i - W i‖ := by
      calc
        ‖(Wc i - Wp i) + (Wp i - Wq i) + (Wq i - W i)‖
            ≤ ‖(Wc i - Wp i) + (Wp i - Wq i)‖ + ‖Wq i - W i‖ := norm_add_le _ _
        _ ≤ (‖Wc i - Wp i‖ + ‖Wp i - Wq i‖) + ‖Wq i - W i‖ :=
              add_le_add_right (norm_add_le _ _) _
    _ ≤ δd i + δp i + δq i := add_le_add (add_le_add h1 h2) h3
    _ = jointDelta δq δp δd i := by
      unfold jointDelta
      ring

/-! ## 定理二（核心）：联合链端到端误差界（统一框架）

把逐层预算 `jointDelta` 代入 `RealQuantizedError.quantized_chain_error_closed`
——「压缩 = 量化特例」的统一框架：三压缩联合模型的端到端误差

`‖F_c x − F x‖ ≤ Σ_{i<n} (∏_{j∈Ioo i n} ‖Wc_j‖)·(δq_i + δp_i + δd_i)
                        ·(∏_{k<i} ‖W_k‖)·‖x‖`

第 i 层的联合误差（三部分之和）经其后各压缩层范数放大、其前各参考层范数
放缩输入。 -/

theorem joint_chain_error (W Wq Wp Wc : ℕ → E →L[ℝ] E) (δq δp δd : ℕ → ℝ) (n : ℕ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δq i)
    (hp : ∀ i, i < n → ‖Wp i - Wq i‖ ≤ δp i)
    (hd : ∀ i, i < n → ‖Wc i - Wp i‖ ≤ δd i) :
    ∀ x, ‖quantFwd Wc n x - quantFwd W n x‖
      ≤ ∑ i in Finset.range n,
          (∏ j in Finset.Ioo i n, ‖Wc j‖) * jointDelta δq δp δd i
            * (∏ k in Finset.range i, ‖W k‖) * ‖x‖ := by
  intro x
  exact quantized_chain_error_closed W Wc (jointDelta δq δp δd) n
    (fun i hi => compression_error_budget W Wq Wp Wc δq δp δd n hq hp hd i hi) x

/-! ## 定理三（加分）：均匀情形联合界 `n·(dq+dp+dd)·Lⁿ·‖x‖`

所有层量化误差 `δq i = dq`、剪枝误差 `δp i = dp`、蒸馏误差 `δd i = dd`
（三者非负），联合链各层范数 ≤ L、参考链各层范数 ≤ L、L ≥ 1 ⟹
`‖F_c x − F x‖ ≤ n·(dq+dp+dd)·Lⁿ·‖x‖`
（实例化 `quantized_uniform_error`；d = dq+dp+dd 为联合逐层预算上界）。 -/

theorem joint_uniform_bound (W Wq Wp Wc : ℕ → E →L[ℝ] E) (δq δp δd : ℕ → ℝ) (n : ℕ)
    (L dq dp dd : ℝ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δq i)
    (hp : ∀ i, i < n → ‖Wp i - Wq i‖ ≤ δp i)
    (hd : ∀ i, i < n → ‖Wc i - Wp i‖ ≤ δd i)
    (hδq : ∀ i, δq i = dq) (hδp : ∀ i, δp i = dp) (hδd : ∀ i, δd i = dd)
    (hdq : 0 ≤ dq) (hdp : 0 ≤ dp) (hdd : 0 ≤ dd)
    (hWc : ∀ i, ‖Wc i‖ ≤ L) (hW : ∀ i, ‖W i‖ ≤ L) (hL1 : 1 ≤ L) :
    ∀ x, ‖quantFwd Wc n x - quantFwd W n x‖
      ≤ (n : ℝ) * (dq + dp + dd) * L ^ n * ‖x‖ := by
  have hδ : ∀ i, jointDelta δq δp δd i = dq + dp + dd := by
    intro i
    unfold jointDelta
    rw [hδq i, hδp i, hδd i]
  have hd0 : 0 ≤ dq + dp + dd := by linarith
  intro x
  exact quantized_uniform_error W Wc (jointDelta δq δp δd) n L (dq + dp + dd)
    (fun i hi => compression_error_budget W Wq Wp Wc δq δp δd n hq hp hd i hi)
    hδ hd0 hWc hW hL1 x

/-! ## 定理四（加分）：压缩占优 / 退化

若某一种压缩误差恒为 0（如未剪枝：`δp = 0`），联合逐层预算退化为其余两种
之和：`jointDelta δq (fun _ => 0) δd i = δq i + δd i`；链级界同步退化
（`compression_dominance_chain`：未剪枝时联合界 = 量化+蒸馏界）。 -/

theorem compression_dominance (δq δd : ℕ → ℝ) (i : ℕ) :
    jointDelta δq (fun _ => 0) δd i = δq i + δd i := by
  unfold jointDelta
  ring

/-- 定理四'（链级退化）：剪枝误差恒为 0（未剪枝，`Wp = Wq`）时，联合链
端到端界退化为「量化 + 蒸馏」两压缩的界（逐项 δq i + δd i）。 -/
theorem compression_dominance_chain (W Wq Wc : ℕ → E →L[ℝ] E) (δq δd : ℕ → ℝ) (n : ℕ)
    (hq : ∀ i, i < n → ‖Wq i - W i‖ ≤ δq i)
    (hd : ∀ i, i < n → ‖Wc i - Wq i‖ ≤ δd i) :
    ∀ x, ‖quantFwd Wc n x - quantFwd W n x‖
      ≤ ∑ i in Finset.range n,
          (∏ j in Finset.Ioo i n, ‖Wc j‖) * (δq i + δd i)
            * (∏ k in Finset.range i, ‖W k‖) * ‖x‖ := by
  intro x
  have hp : ∀ i, i < n → ‖Wq i - Wq i‖ ≤ (fun _ => (0 : ℝ)) i := by
    intro i hi
    simp
  have h := joint_chain_error W Wq Wq Wc δq (fun _ => 0) δd n hq hp hd x
  simpa [jointDelta] using h

/-! ## 定理五（加分）：联合预算非负（由各分量非负）

`δq i ≥ 0`、`δp i ≥ 0`、`δd i ≥ 0` ⟹ `0 ≤ jointDelta δq δp δd i`——
联合预算的良定性（均匀界 `hd0` 的逐层来源）。 -/

theorem jointDelta_nonneg (δq δp δd : ℕ → ℝ) (i : ℕ)
    (hq : 0 ≤ δq i) (hp : 0 ≤ δp i) (hd : 0 ≤ δd i) :
    0 ≤ jointDelta δq δp δd i := by
  unfold jointDelta
  linarith

end Lattice
