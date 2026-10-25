import Mathlib
import Lattice.Lift.RealLinear
import Lattice.Lib.Optim.RealApprox
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.LinearAlgebra.RealSparsity
/-!
# LATTICE: 编译-提取往返的误差界

`WeightToSymbolEquivalence` 证明了线性子类上「编译 → 提取」的**精确**往返恒等
（`roundtrip_extract` / `roundtrip_extractVec`），`RealApprox` 给出了权重扰动到
输出误差的传播界（`layer_out_error_bound`）。本文件把两者接起来，给出
**带误差的往返**的定量界：

  1. `extractReal` + `extract_compile_identity`：ℝ 版提取器与精确往返恒等
     （整数版 `roundtrip_extract` 由 `extract_compile_identity_int` 原样回收，
     向量版由 `extract_compile_identity_vec` 回收）；`roundtripNeuron_self`
     给出神经元层面的往返恒等；
  2. `roundtrip_error_bound`：提取误差 ≤ `(ε₁, ε₂)` 时的往返输出误差界
     `≤ ε₁·X + ε₂`（直接实例化 `RealApprox.layer_out_error_bound`）；
     `roundtrip_error_bound_exact` 是 ε 全零的退化情形（往返精确）；
  3. `roundtrip_under_quantization`：量化/剪枝扰动 `δ` 下的往返误差界
     `≤ δ·X + δ`（衔接 `RealQuantizedError` 的逐层 δ 与 `RealSparsity` 的
     剪枝误差 `δ = √s·θ`，见 `deltaFromPruning` 与 `roundtrip_under_pruning`）；
  4. `extract_stability`：提取算子的 Lipschitz 稳定性 —— 输入神经元的系数
     `max`-范数扰动 ≤ ε ⟹ 往返输出扰动 ≤ ε·X + ε；
     `extract_stability_isometry` 说明提取在系数范数下是**等距**的
     （Lipschitz 常数恰为 1）。

诚实假设与降级（全部显式标注）：
- 往返误差界是**条件界**：`ε / δ` 由提取器或量化器自身给出，本文件不构造
  具体量化器（那是 `RealQuantizedError` / `RealSparsity` 的工作），只证明
  「扰动有界 ⟹ 往返误差有界」的传播；
- 输入有界 `|x| ≤ X` 是 `RealApprox` 体系的标准前提（线性层误差界的必要条件）；
- 第 1 条是精确恒等，第 2–4 条是近似界，二者互不覆盖（精确性是 ε = 0 的特例）；
- `deltaFromPruning` 的 δ = √s·θ 与 `RealSparsity.prune_magnitude_bound` 中
  被剪集大小 `s` 与幅度阈值 `θ` 的记号一致（标量读数）；
- 不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

/-! ## 一、ℝ 版提取器与精确往返 -/

/-- ℝ 版提取器：从神经元恢复符号约束（系数直接读回）。 -/
def extractReal (n : RealNeuron) : RealConstraint :=
  { a := n.w, b := n.b }

/-- 编译-提取往返在神经元上恒等：`convertReal ∘ extractReal = id`
（结构 eta：`⟨n.w, n.b⟩ = n`）。 -/
def roundtripNeuron (n : RealNeuron) : RealNeuron :=
  convertReal (extractReal n)

/-- **精确往返恒等（约束层）**：`extractReal (convertReal c) = c`
（ℝ 版 `roundtrip_extract`）。 -/
theorem extract_compile_identity (c : RealConstraint) :
    extractReal (convertReal c) = c := by
  cases c
  rfl

/-- **精确往返恒等（神经元层）**：`roundtripNeuron n = n`。 -/
theorem roundtripNeuron_self (n : RealNeuron) : roundtripNeuron n = n := by
  cases n
  rfl

/-- 回收整数版 `WeightToSymbolEquivalence.roundtrip_extract`。 -/
theorem extract_compile_identity_int (c : LinearConstraint) :
    extract (convert c) = c :=
  roundtrip_extract c

/-- 回收向量版 `WeightToSymbolEquivalence.roundtrip_extractVec`。 -/
theorem extract_compile_identity_vec (c : VectorConstraint) :
    extractVec (convertVec c) = c :=
  roundtrip_extractVec c

/-! ## 二、近似往返的误差界 -/

/-- **往返误差界（提取误差 ≤ ε₁/ε₂）**：设提取出的约束 `c'` 与原始神经元 `n`
的系数扰动分别被 `ε₁`（一次系数）与 `ε₂`（常数项）界住，输入满足 `|x| ≤ X`，
则「提取再编译」的输出与原始输出之差 ≤ `ε₁·X + ε₂`。
直接实例化 `RealApprox.layer_out_error_bound`。 -/
theorem roundtrip_error_bound (n : RealNeuron) (c' : RealConstraint) (x X ε₁ ε₂ : ℝ)
    (hx : |x| ≤ X) (ha : |c'.a - n.w| ≤ ε₁) (hb : |c'.b - n.b| ≤ ε₂) :
    |RealNeuronOut (convertReal c') x - RealNeuronOut n x| ≤ ε₁ * X + ε₂ := by
  have h := layer_out_error_bound x n.w n.b c'.a c'.b X ε₁ ε₂ hx ha hb
  simpa [RealNeuronOut, convertReal] using h

/-- 精确提取（`c' = extractReal n`）时往返误差为零 —— 定理二与定理一的接口。 -/
theorem roundtrip_error_bound_exact (n : RealNeuron) (x : ℝ) :
    |RealNeuronOut (roundtripNeuron n) x - RealNeuronOut n x| ≤ 0 := by
  rw [roundtripNeuron_self n]
  simp

/-- 往返误差界的单参数形式：一次系数与常数项扰动同时被 `δ` 界住时误差 ≤ `δ·X + δ`。 -/
theorem roundtrip_error_bound_uniform (n : RealNeuron) (c' : RealConstraint) (x X δ : ℝ)
    (hx : |x| ≤ X) (ha : |c'.a - n.w| ≤ δ) (hb : |c'.b - n.b| ≤ δ) :
    |RealNeuronOut (convertReal c') x - RealNeuronOut n x| ≤ δ * X + δ :=
  roundtrip_error_bound n c' x X δ δ hx ha hb

/-! ## 三、量化 / 剪枝扰动下的往返 -/

/-- 量化扰动假设：被量化神经元 `nq` 的系数在 `δ` 内接近原神经元 `n`
（`RealQuantizedError` 中「逐层算子误差 ≤ δ」的标量读数）。 -/
def QuantizedApprox (n nq : RealNeuron) (δ : ℝ) : Prop :=
  |nq.w - n.w| ≤ δ ∧ |nq.b - n.b| ≤ δ

/-- **量化扰动下的往返误差界**：`quantized` 神经元经「提取 → 重编译」往返后，
输出与原始神经元的差 ≤ `δ·X + δ`。
（往返本身精确，故全部误差来自量化扰动。） -/
theorem roundtrip_under_quantization (n nq : RealNeuron) (x X δ : ℝ)
    (hx : |x| ≤ X) (h : QuantizedApprox n nq δ) :
    |RealNeuronOut (roundtripNeuron nq) x - RealNeuronOut n x| ≤ δ * X + δ := by
  have h' := roundtrip_error_bound n (extractReal nq) x X δ δ hx h.1 h.2
  simpa [roundtripNeuron] using h'

/-- 剪枝/量化误差幅度 δ = √s·θ：`RealSparsity.prune_magnitude_bound` 中
「被剪集大小 ≤ s、被剪分量幅度 ≤ θ（θ ≥ 0）⟹ 误差 ≤ √s·θ」的标量读数。 -/
def deltaFromPruning (s θ : ℝ) : ℝ := Real.sqrt s * θ

/-- `δ = √s·θ` 非负（`s ≥ 0`、`θ ≥ 0`）。 -/
theorem deltaFromPruning_nonneg {s θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ deltaFromPruning s θ :=
  mul_nonneg (Real.sqrt_nonneg s) hθ

/-- **剪枝扰动下的往返误差界**：系数扰动被剪枝误差 `δ = √s·θ` 界住时，
往返输出误差 ≤ `δ·X + δ`（`δ = deltaFromPruning s θ`，衔接 `RealSparsity`）。 -/
theorem roundtrip_under_pruning (n nq : RealNeuron) (x X s θ : ℝ)
    (hx : |x| ≤ X) (ha : |nq.w - n.w| ≤ deltaFromPruning s θ)
    (hb : |nq.b - n.b| ≤ deltaFromPruning s θ) :
    |RealNeuronOut (roundtripNeuron nq) x - RealNeuronOut n x|
      ≤ deltaFromPruning s θ * X + deltaFromPruning s θ :=
  roundtrip_under_quantization n nq x X (deltaFromPruning s θ) hx ⟨ha, hb⟩

/-! ## 四、提取算子的稳定性（Lipschitz / 连续性） -/

/-- 神经元系数上的 `max`-范数（一次系数与常数项的最大绝对扰动）。 -/
def neuronDist (n n' : RealNeuron) : ℝ :=
  max |n'.w - n.w| |n'.b - n.b|

/-- 符号约束系数上的 `max`-范数。 -/
def constrDist (c c' : RealConstraint) : ℝ :=
  max |c'.a - c.a| |c'.b - c.b|

/-- **提取在系数范数下是等距**：`constrDist (extractReal n) (extractReal n') = neuronDist n n'`。
因此提取算子的 Lipschitz 常数恰为 1（无信息放大）。 -/
theorem extract_stability_isometry (n n' : RealNeuron) :
    constrDist (extractReal n) (extractReal n') = neuronDist n n' := by
  unfold constrDist neuronDist extractReal
  rfl

/-- 提取算子的 1-Lipschitz 性（等距的直接推论）。 -/
theorem extract_lipschitz_one (n n' : RealNeuron) (ε : ℝ) (h : neuronDist n n' ≤ ε) :
    constrDist (extractReal n) (extractReal n') ≤ ε := by
  rw [extract_stability_isometry]
  exact h

/-- **提取稳定性（输入小扰动 ⟹ 往返结果小变化）**：
神经元系数扰动在 `max`-范数下 ≤ ε、输入有界 `|x| ≤ X`，
则往返后的输出扰动 ≤ `ε·X + ε`（连续性/Lipschitz 估计）。 -/
theorem extract_stability (n n' : RealNeuron) (x X ε : ℝ)
    (hx : |x| ≤ X) (h : neuronDist n n' ≤ ε) :
    |RealNeuronOut (roundtripNeuron n') x - RealNeuronOut (roundtripNeuron n) x|
      ≤ ε * X + ε := by
  have h' : max |n'.w - n.w| |n'.b - n.b| ≤ ε := by
    simpa [neuronDist] using h
  have h1 : |n'.w - n.w| ≤ ε := le_trans (le_max_left _ _) h'
  have h2 : |n'.b - n.b| ≤ ε := le_trans (le_max_right _ _) h'
  have hq := roundtrip_under_quantization n n' x X ε hx ⟨h1, h2⟩
  rw [roundtripNeuron_self n]
  exact hq

end Lattice
