import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealOperatorNorm
import Lattice.Lib.Optim.RealApprox
import Lattice.Lib.Quantization.RealQuantizedError
/-!
# LATTICE: 知识蒸馏输出对齐界 —— 参数接近的学生输出接近教师输出（Lipschitz 结构保证）

训练线延伸：知识蒸馏（teacher-student）的输出误差界。蒸馏训练中学生的
目标是与教师输出对齐（如 KL/蒸馏损失），本文件证明其**结构保证**：
参数接近的学生模型，输出在算子范数意义下接近教师模型——「学生输出距
教师输出的 Lipschitz 界」。

数学设定：教师层 Wt、学生层 Ws（同为 `E →L[ℝ] F` / `E →L[ℝ] E`），
每层参数差 ‖Wt i − Ws i‖ ≤ δ i。定理链：

  1. `layer_distill_bound`：单层蒸馏界 ‖Wt x − Ws x‖ ≤ ‖Wt − Ws‖·‖x‖
     （算子差 + `le_opNorm`，`RealApprox.layer_out_error_bound` 的算子版）；
  2. `layer_distill_bound_delta`：δ 形式单层界 ‖Wt x − Ws x‖ ≤ δ·‖x‖；
  3. `two_layer_distill_bound`（学生内插值）/ `two_layer_distill_bound_teacher_input`
     （教师内插值）：两层插值展开——在中间态切换师生层，三角不等式链；
     `two_layer_distill_bound_closed`：提取 ‖x‖ 的闭式；
  4. `chain_distill_bound`（核心，n 层）：每层参数差 δ i ⟹ 端到端
     ‖quantFwd Wt n x − quantFwd Ws n x‖
     ≤ Σ_{i<n} (∏_{j∈Ioo i n} ‖Wt j‖)·δ i·(∏_{k<i} ‖Ws k‖)·‖x‖
     —— 第 i 层参数差经其后各**教师**层（‖Wt j‖）放大、经其前各**学生**
     层（‖Ws k‖）放缩输入；`distill_chain_error` 为递归界形式；
     `chain_distill_bound_lipschitz` 为非线性 Lipschitz 层版（块级蒸馏入口）；
  5. `distill_uniform`：均匀特例（δ i = d ≥ 0、师生范数均 ≤ L、L ≥ 1）
     ⟹ 端到端 ≤ n·d·Lⁿ·‖x‖；
  6. `distill_zero_teacher_match` / `distill_zero_output` /
     `distill_zero_from_delta`：学生 = 教师（或 δ = 0）⟹ 输出恒等/误差 0。

**与量化误差的同构（关键洞察）**：权重量化是蒸馏的特例——量化模型 =
「学生」、浮点模型 = 「教师」，每层量化误差界 δ i = 每层师生参数差。
`chain_distill_bound` 与 `RealQuantizedError.quantized_chain_error_closed`
的闭式结构完全相同（∏_{j∈Ioo i n} 放大 + ∏_{k<i} 放缩 + δ i·‖x‖），
区别仅为角色命名（教师 Wt ↔ 原层 W，学生 Ws ↔ 量化层 Wq）。因此 n 层
蒸馏界直接由 `quantized_chain_error_closed` 的**角色互换**实例化得到
（W := Ws、Wq := Wt），无需重新归纳——这正体现「蒸馏误差 = 师生参数差
的传播」与「量化误差 = 量化扰动的传播」是同一数学结构；`distill_chain_error`
/ `distill_uniform` 同理互换 `quantized_chain_error` / `quantized_uniform_error`
的角色。

诚实假设（全部显式标注）：参数差界 δ i ≥ 0（由范数非负 + ‖Wt−Ws‖ ≤ δ
自动推出，见 `distill_delta_nonneg`）；均匀版需师生范数上界 L（L ≥ 1）
与 d ≥ 0；Lipschitz 版需师生层共享 Lipschitz 常数上界 Ls i（若不同取
max 即得）。其余为范数公理（`le_opNorm`、三角不等式）。无 sorry/axiom/admit。

模型无关：任意范数空间 E、F（ℝ 标量）、任意层数 n、任意师生层序列
（线性 CLM 或 Lipschitz 层）；不需要模型具体结构（注意力/FFN 细节）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 单层蒸馏界（教师/学生层 Wt/Ws : E →L[ℝ] F） -/

/-- 参数差界非负：‖Wt − Ws‖ ≤ δ 且范数非负 ⟹ 0 ≤ δ。 -/
lemma distill_delta_nonneg (Wt Ws : E →L[ℝ] F) (δ : ℝ) (hδ : ‖Wt - Ws‖ ≤ δ) : 0 ≤ δ :=
  le_trans (norm_nonneg (Wt - Ws)) hδ

/-- 定理一（单层蒸馏界）：‖Wt x − Ws x‖ ≤ ‖Wt − Ws‖·‖x‖
（算子差 + `le_opNorm`；`RealApprox.layer_out_error_bound` 的算子版：
权重扰动 ‖Wt−Ws‖、输入范数界 ‖x‖）。 -/
theorem layer_distill_bound (Wt Ws : E →L[ℝ] F) (x : E) :
    ‖Wt x - Ws x‖ ≤ ‖Wt - Ws‖ * ‖x‖ := by
  calc
    ‖Wt x - Ws x‖ = ‖(Wt - Ws) x‖ := by rw [← ContinuousLinearMap.sub_apply]
    _ ≤ ‖Wt - Ws‖ * ‖x‖ := (Wt - Ws).le_opNorm x

/-- 定理二（δ 形式单层蒸馏界）：‖Wt − Ws‖ ≤ δ ⟹ ‖Wt x − Ws x‖ ≤ δ·‖x‖。 -/
theorem layer_distill_bound_delta (Wt Ws : E →L[ℝ] F) (δ : ℝ) (hδ : ‖Wt - Ws‖ ≤ δ) (x : E) :
    ‖Wt x - Ws x‖ ≤ δ * ‖x‖ := by
  calc
    ‖Wt x - Ws x‖ ≤ ‖Wt - Ws‖ * ‖x‖ := layer_distill_bound Wt Ws x
    _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg x)

/-! ## 两层蒸馏界（插值展开） -/

/-- 定理三（两层蒸馏界，学生内插值）：‖Wt₂(Wt₁x) − Ws₂(Ws₁x)‖
≤ ‖Wt₂‖·δ₁·‖x‖ + δ₂·‖Ws₁‖·‖x‖。
中间插值态 Wt₂(Ws₁x)（先切换层一为学生，层二保持教师）：
[Wt₂(Wt₁x) − Wt₂(Ws₁x)] + [Wt₂(Ws₁x) − Ws₂(Ws₁x)]；
第一项 ≤ ‖Wt₂‖·δ₁·‖x‖（教师层二 Lipschitz + 层一参数差），
第二项 ≤ δ₂·‖Ws₁ x‖ ≤ δ₂·‖Ws₁‖·‖x‖（层二参数差在学生入口点 +
学生层一范数界）。此即 n 层闭式的两层显式特例（层一误差经教师层二放大、
层二误差在学生层一之后）。 -/
theorem two_layer_distill_bound (Wt₁ Wt₂ Ws₁ Ws₂ : E →L[ℝ] E) (δ₁ δ₂ : ℝ)
    (hδ₁ : ‖Wt₁ - Ws₁‖ ≤ δ₁) (hδ₂ : ‖Wt₂ - Ws₂‖ ≤ δ₂) (x : E) :
    ‖Wt₂ (Wt₁ x) - Ws₂ (Ws₁ x)‖ ≤ ‖Wt₂‖ * δ₁ * ‖x‖ + δ₂ * ‖Ws₁‖ * ‖x‖ := by
  calc
    ‖Wt₂ (Wt₁ x) - Ws₂ (Ws₁ x)‖
        = ‖(Wt₂ (Wt₁ x) - Wt₂ (Ws₁ x)) + (Wt₂ (Ws₁ x) - Ws₂ (Ws₁ x))‖ := by
          congr 1
          abel
    _ ≤ ‖Wt₂ (Wt₁ x) - Wt₂ (Ws₁ x)‖ + ‖Wt₂ (Ws₁ x) - Ws₂ (Ws₁ x)‖ := by
          exact norm_add_le _ _
    _ ≤ ‖Wt₂‖ * ‖Wt₁ x - Ws₁ x‖ + δ₂ * ‖Ws₁ x‖ := by
          exact add_le_add
            (linear_map_lipschitz Wt₂ (Wt₁ x) (Ws₁ x))
            (layer_distill_bound_delta Wt₂ Ws₂ δ₂ hδ₂ (Ws₁ x))
    _ ≤ ‖Wt₂‖ * (δ₁ * ‖x‖) + δ₂ * (‖Ws₁‖ * ‖x‖) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (layer_distill_bound_delta Wt₁ Ws₁ δ₁ hδ₁ x) (norm_nonneg Wt₂))
            (mul_le_mul_of_nonneg_left ((Ws₁).le_opNorm x) (distill_delta_nonneg Wt₂ Ws₂ δ₂ hδ₂))
    _ = ‖Wt₂‖ * δ₁ * ‖x‖ + δ₂ * ‖Ws₁‖ * ‖x‖ := by ring

/-- 定理三'（两层蒸馏界，教师内插值）：‖Wt₂(Wt₁x) − Ws₂(Ws₁x)‖
≤ ‖Ws₂‖·δ₁·‖x‖ + δ₂·‖Wt₁‖·‖x‖。
与定理三互为镜像：中间插值态 Ws₂(Wt₁x)（先切换层二为学生，层一保持
教师）；放大因子归属互换（层一误差经学生层二 ‖Ws₂‖ 放大、层二误差在
教师入口点 ‖Wt₁ x‖ 处）。两条一致插值链均可证；「‖Wt₂‖·δ₁ + δ₂·‖Wt₁‖」
的混合形式不是单一插值链，故不采纳（诚实标注）。 -/
theorem two_layer_distill_bound_teacher_input (Wt₁ Wt₂ Ws₁ Ws₂ : E →L[ℝ] E) (δ₁ δ₂ : ℝ)
    (hδ₁ : ‖Wt₁ - Ws₁‖ ≤ δ₁) (hδ₂ : ‖Wt₂ - Ws₂‖ ≤ δ₂) (x : E) :
    ‖Wt₂ (Wt₁ x) - Ws₂ (Ws₁ x)‖ ≤ ‖Ws₂‖ * δ₁ * ‖x‖ + δ₂ * ‖Wt₁‖ * ‖x‖ := by
  have hq₁ : ‖Ws₁ - Wt₁‖ ≤ δ₁ := by
    rw [norm_sub_rev]
    exact hδ₁
  have hq₂ : ‖Ws₂ - Wt₂‖ ≤ δ₂ := by
    rw [norm_sub_rev]
    exact hδ₂
  have hbound := quantized_two_layer_error Wt₁ Wt₂ Ws₁ Ws₂ δ₁ δ₂ hq₁ hq₂ x
  rw [norm_sub_rev] at hbound
  exact hbound

/-- 定理三''（两层蒸馏界，闭式）：提取 ‖x‖ 因子
‖Wt₂(Wt₁x) − Ws₂(Ws₁x)‖ ≤ (‖Wt₂‖·δ₁ + δ₂·‖Ws₁‖)·‖x‖。 -/
theorem two_layer_distill_bound_closed (Wt₁ Wt₂ Ws₁ Ws₂ : E →L[ℝ] E) (δ₁ δ₂ : ℝ)
    (hδ₁ : ‖Wt₁ - Ws₁‖ ≤ δ₁) (hδ₂ : ‖Wt₂ - Ws₂‖ ≤ δ₂) (x : E) :
    ‖Wt₂ (Wt₁ x) - Ws₂ (Ws₁ x)‖ ≤ (‖Wt₂‖ * δ₁ + δ₂ * ‖Ws₁‖) * ‖x‖ := by
  calc
    ‖Wt₂ (Wt₁ x) - Ws₂ (Ws₁ x)‖ ≤ ‖Wt₂‖ * δ₁ * ‖x‖ + δ₂ * ‖Ws₁‖ * ‖x‖ :=
      two_layer_distill_bound Wt₁ Wt₂ Ws₁ Ws₂ δ₁ δ₂ hδ₁ hδ₂ x
    _ = (‖Wt₂‖ * δ₁ + δ₂ * ‖Ws₁‖) * ‖x‖ := by ring

/-! ## n 层蒸馏界（核心；与量化误差同构） -/

/-- 定理四（n 层端到端，递归界）：每层参数差 ‖Wt i − Ws i‖ ≤ δ i
⟹ ‖quantFwd Wt n x − quantFwd Ws n x‖ ≤ quantErrBound Ws Wt δ x n。
角色互换实例化 `RealQuantizedError.quantized_chain_error`（W := Ws 学生、
Wq := Wt 教师）：第 n 层误差 = 前 n 层误差经教师层 n 放大 + 第 n 层
参数差在本层学生入口点的贡献。 -/
theorem distill_chain_error (Wt Ws : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ)
    (hδ : ∀ i, i < n → ‖Wt i - Ws i‖ ≤ δ i) :
    ∀ x, ‖quantFwd Wt n x - quantFwd Ws n x‖ ≤ quantErrBound Ws Wt δ x n := by
  intro x
  exact quantized_chain_error Ws Wt δ n hδ x

/-- 定理四（n 层端到端，闭式求和，核心）：每层参数差 ‖Wt i − Ws i‖ ≤ δ i
⟹ ‖quantFwd Wt n x − quantFwd Ws n x‖
≤ Σ_{i<n} (∏_{j∈Ioo i n} ‖Wt j‖)·δ i·(∏_{k<i} ‖Ws k‖)·‖x‖。
第 i 层参数差 δ_i 经其后各教师层（‖Wt j‖）放大、经其前各学生层
（‖Ws k‖）放缩输入——与 `RealQuantizedError.quantized_chain_error_closed`
的闭式结构逐项同构（量化版：放大因子为量化层范数、放缩因子为原层范数；
蒸馏版：放大因子为教师范数、放缩因子为学生范数），角色互换
（W := Ws、Wq := Wt）直接实例化即得，无需重新归纳。 -/
theorem chain_distill_bound (Wt Ws : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ)
    (hδ : ∀ i, i < n → ‖Wt i - Ws i‖ ≤ δ i) :
    ∀ x, ‖quantFwd Wt n x - quantFwd Ws n x‖
      ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, ‖Wt j‖) * δ i * (∏ k in Finset.range i, ‖Ws k‖) * ‖x‖ := by
  intro x
  exact quantized_chain_error_closed Ws Wt δ n hδ x

/-- 定理四'（非线性 Lipschitz 层版，块级蒸馏入口）：教师层 Ft 与学生对层
Fs 同为 Ls i-Lipschitz（hLt/hLs），逐层输出对齐误差 ‖Ft i y − Fs i y‖ ≤ ε i
（输入无关）⟹ 端到端 ‖ChainFwd Ft n x − ChainFwd Fs n x‖
≤ Σ_{i<n} (∏_{j∈Ioo i n} Ls j)·ε i。
角色互换实例化 `RealQuantizedError.quantized_chain_error_lipschitz`
（F := Fs、Fq := Ft）：接入块级蒸馏时，单块 Lipschitz 常数（如
RealBlockLipschitz/RealModelChain 的 Lb）代入 Ls i、逐块输出对齐误差
代入 ε i；诚实假设：师生层共享常数上界 Ls i（若不同取 max）。 -/
theorem chain_distill_bound_lipschitz (Ft Fs : ℕ → E → E) (Ls ε : ℕ → ℝ) (n : ℕ)
    (hLt : ∀ i, i < n → ∀ x y, ‖Ft i x - Ft i y‖ ≤ Ls i * ‖x - y‖)
    (hLs : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (hε : ∀ i, i < n → ∀ y, ‖Ft i y - Fs i y‖ ≤ ε i) :
    ∀ x, ‖ChainFwd Ft n x - ChainFwd Fs n x‖
      ≤ ∑ i in Finset.range n, (∏ j in Finset.Ioo i n, Ls j) * ε i := by
  intro x
  exact quantized_chain_error_lipschitz Fs Ft Ls ε n hLs hLt hL0 hε x

/-! ## 均匀蒸馏特例 -/

/-- 定理五（均匀蒸馏特例）：每层参数差 δ i = d（d ≥ 0）、师生范数均
≤ L（L ≥ 1）⟹ 端到端误差 ‖quantFwd Wt n x − quantFwd Ws n x‖ ≤ n·d·Lⁿ·‖x‖。
角色互换实例化 `RealQuantizedError.quantized_uniform_error`（W := Ws、
Wq := Wt）。诚实假设：除 δ i = d、d ≥ 0、L ≥ 1 外，还需学生对层范数
‖Ws i‖ ≤ L（Lipschitz 常数上界须同时覆盖师生；L < 1 时误差被收缩层
衰减，需 Σᵢ d·Lⁱ 形式，诚实标注未在此展开）。 -/
theorem distill_uniform (Wt Ws : ℕ → E →L[ℝ] E) (δ : ℕ → ℝ) (n : ℕ) (L d : ℝ)
    (hδ : ∀ i, i < n → ‖Wt i - Ws i‖ ≤ δ i)
    (hδd : ∀ i, δ i = d) (hd0 : 0 ≤ d)
    (hWt : ∀ i, ‖Wt i‖ ≤ L) (hWs : ∀ i, ‖Ws i‖ ≤ L)
    (hL1 : 1 ≤ L) :
    ∀ x, ‖quantFwd Wt n x - quantFwd Ws n x‖ ≤ (n : ℝ) * d * L ^ n * ‖x‖ := by
  intro x
  exact quantized_uniform_error Ws Wt δ n L d hδ hδd hd0 hWt hWs hL1 x

/-! ## 零参数差 ⟹ 输出恒等（加分） -/

/-- 定理六（学生 = 教师 ⟹ 输出恒等）：每层 Ws i = Wt i（i < n）⟹
quantFwd Wt n x = quantFwd Ws n x（逐层相等 ⟹ 前向输出逐点相等，归纳）。 -/
theorem distill_zero_teacher_match (Wt Ws : ℕ → E →L[ℝ] E) (n : ℕ)
    (h : ∀ i, i < n → Ws i = Wt i) :
    ∀ x, quantFwd Wt n x = quantFwd Ws n x := by
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      have hih : ∀ x, quantFwd Wt n x = quantFwd Ws n x := ih (fun i hi => h i (by omega))
      have hWn : Wt n = Ws n := (h n (by omega)).symm
      calc
        quantFwd Wt (n + 1) x = Wt n (quantFwd Wt n x) := rfl
        _ = Ws n (quantFwd Ws n x) := by rw [hWn, hih x]

/-- 定理六'：学生 = 教师 ⟹ 输出差范数为 0。 -/
theorem distill_zero_output (Wt Ws : ℕ → E →L[ℝ] E) (n : ℕ)
    (h : ∀ i, i < n → Ws i = Wt i) :
    ∀ x, ‖quantFwd Wt n x - quantFwd Ws n x‖ = 0 := by
  intro x
  rw [distill_zero_teacher_match Wt Ws n h x]
  simp

/-- 定理六''（δ = 0 版本）：每层参数差 ‖Wt i − Ws i‖ ≤ 0 ⟹ 输出恒等
（范数非负 + 界 0 ⟹ ‖Wt i − Ws i‖ = 0 ⟹ Wt i = Ws i，归约到定理六）。 -/
theorem distill_zero_from_delta (Wt Ws : ℕ → E →L[ℝ] E) (n : ℕ)
    (hδ : ∀ i, i < n → ‖Wt i - Ws i‖ ≤ 0) :
    ∀ x, quantFwd Wt n x = quantFwd Ws n x := by
  apply distill_zero_teacher_match Wt Ws n
  intro i hi
  have hnorm : ‖Wt i - Ws i‖ = 0 := le_antisymm (hδ i hi) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

/-! ## 注：蒸馏训练的意义
  蒸馏损失（学生对齐教师输出）的收敛目标正是 `distill_zero_teacher_match`
  的极限情形；`chain_distill_bound` 给出任意参数差 δ_i 下的输出对齐误差
  上界——训练过程中 δ_i 单调收缩时，端到端对齐误差随之线性收缩（每层
  权重差按 ∏ 教师范数放大、按 ∏ 学生范数放缩输入）。与 RealQuantizedError
  的同构意味着：量化部署与蒸馏训练共享同一套「逐层扰动传播」证明骨架，
  权重扰动来源（量化舍入 vs 训练未收敛）不影响误差传播结构。 -/

end Lattice
