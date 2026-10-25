import Mathlib
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealGatingGeneral
import Lattice.Lib.Attention.RealRelPosEncoding
import Lattice.Lib.Optim.RealErrorFeedback
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.InfoTheory.RealOptimalTransport
import Lattice.Lib.Convex.RealSupportingHyperplane
import Lattice.Lib.Optim.RealRiemannianGD
-- B374: `⟪x, g⟫` is the explicit-scalar inner-product notation from Mathlib's
-- Basic.lean:90; without this declaration it fails to parse at :368.  The same
-- fix is recorded in RealRiemannianGD:71-72.
open scoped RealInnerProductSpace

/-!
# LATTICE: 能力抽象注册表（元级文件）

本文件是**元级**的：它不引入新的数学对象，而是把 LATTICE 仓库里**散落各处的能力抽象
接口**汇总到一处，并做到「注册表里没有一行是文字描述」——每个抽象的**实例**都由一条
**可编译的实例化定理**给出，每个抽象的**覆盖范围**都由一条**覆盖定理**给出。

## 收录的抽象（5 个）

| # | 抽象 | 定义出处 | 语义 |
|---|------|----------|------|
| 1 | `SoftMasked` | `RealActClass` | `f(x) = s(x)·x`，`s ∈ [0,1]`（软/硬掩码激活类） |
| 2 | `Gated` | `RealGatingGeneral` | `f(x) = g(x)·h(x)`（一般门控族） |
| 3 | `IsTranslationEquivariant` | `RealRelPosEncoding` | `f(i+k, j+k) = f(i,j)`（相对位置性） |
| 4 | `IsCompressor` | `RealErrorFeedback` | `|C x − x| ≤ (1−δ)|x|`（δ-近似压缩） |
| 5 | `RoundOp` | `RealFloatFormat` | 舍入算子（相对误差界 + 幂等） |

## 结构约定

每个抽象一节，含：

* **定义出处**：`import` 哪个模块 + 声明名（docstring 里写明）；
* **实例清单**：`reg_inst_*` 命题，每条都是**可编译的实例化定理**（不是文字）；
* **覆盖定理**：`reg_*_coverage` 等，把该抽象的性质推广到整族（如
  `∀ act mask, SoftMasked act mask → Gated act mask id`）。

## 诚实边界与标注

* 本注册表**只汇总既有接口**，不重复证明任何既有定理——所有实例化定理都是对既有定理的
  **重新陈述（re-export）**，或是对既有抽象的新**具体实例**（`IsCompressor` 的
  `id`/折半压缩、`RoundOp` 的恒等舍入），这些新实例都真证，无 `sorry`/`axiom`/`admit`。
* **未证/未做（标注）**：本文件**不**声称这些抽象构成「范畴论意义上的注册表」，也**不**做
  抽象之间的自动发现或依赖分析；注册表是人工维护的、编译期可检验的定理集合。
* **未做（标注）**：新增方向包里的抽象（如最优传输的计划/对偶结构、SCM 截断语义、
  球面投影梯度）尚未纳入本注册表——它们仍需在各自方向稳定后再登记。
* 覆盖定理刻画的是**语义包含关系**，不是「实例枚举完备性」：例如
  `SoftMasked ⟹ Gated` 是一条真定理，但本文件不声称 `Gated` 的实例清单已穷尽。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice
/-! ## 1. 能力抽象：软掩码激活类 `SoftMasked`

**定义出处**：`import RealActClass` ／ `Lattice.SoftMasked`
（`def SoftMasked (f s : ℝ → ℝ) : Prop := (∀ x, f x = s x * x) ∧ (∀ x, 0 ≤ s x) ∧ (∀ x, s x ≤ 1)`）。

语义：`f` 由「有界掩码 `s ∈ [0,1]`」乘以输入 `x` 构成；ReLU 是硬掩码 `s ∈ {0,1}` 的特例。

**实例清单**（每条是可编译的实例化定理）：

| 实例 | 定理 | 掩码 |
|------|------|------|
| ReLU | `reg_inst_softMasked_relu` | `reluSoftMask`（硬掩码） |
| GELU-tanh | `reg_inst_softMasked_gelu` | `geluSoftMask` |
| SiLU / swish | `reg_inst_softMasked_silu` | `sigmoid` |
| HardSwish | `reg_inst_softMasked_hardSwish` | `hardSigmoid` |
| SwiGLU | `reg_inst_softMasked_swiglu` | `sigmoid` |-/

/-- 实例（ReLU）：`SoftMasked relu reluSoftMask`（硬掩码 `s ∈ {0,1} ⊆ [0,1]`）。 -/
theorem reg_inst_softMasked_relu : SoftMasked relu reluSoftMask := relu_is_soft_masked

/-- 实例（GELU-tanh）：`SoftMasked geluTanh geluSoftMask`。 -/
theorem reg_inst_softMasked_gelu : SoftMasked geluTanh geluSoftMask := gelu_is_soft_masked

/-- 实例（SiLU / swish）：`SoftMasked silu sigmoid`。 -/
theorem reg_inst_softMasked_silu : SoftMasked silu sigmoid := silu_is_soft_masked

/-- 实例（HardSwish）：`SoftMasked hardSwish hardSigmoid`。 -/
theorem reg_inst_softMasked_hardSwish : SoftMasked hardSwish hardSigmoid :=
  hardSwish_is_soft_masked

/-- 实例（SwiGLU）：`SoftMasked swiglu sigmoid`。 -/
theorem reg_inst_softMasked_swiglu : SoftMasked swiglu sigmoid := swiglu_is_soft_masked

/-- **覆盖定理（软掩码 ⟹ 门控）**：任意软掩码激活 `act` 与任意掩码 `mask`，
`SoftMasked act mask` 蕴含 `Gated act mask id`（信号取恒等映射）。

这是「软掩码激活类整体是门控族子类」的精确形式：不是枚举实例，而是对**整族**成立。 -/
theorem reg_softMasked_coverage :
    ∀ (act mask : ℝ → ℝ), SoftMasked act mask → Gated act mask id := by
  intro act mask h
  intro x
  have hx : act x = mask x * x := h.1 x
  simpa using hx

/-! ## 2. 能力抽象：一般门控族 `Gated`

**定义出处**：`import RealGatingGeneral` ／ `Lattice.Gated`
（`def Gated (f g h : ℝ → ℝ) : Prop := ∀ x, f x = g x * h x`）。

语义：输出 = 门 `g` 逐点乘信号 `h`。软掩码激活（信号 = `id`）与 SwiGLU 双支门控
（`swigluPair`）都是它的成员。

**实例清单**：`reg_inst_gated_swiglu`、`reg_inst_gated_silu`、`reg_inst_gated_hardSwish`、
`reg_inst_gated_relu`、`reg_inst_gated_gelu`（均由 `SoftMasked` 实例经
`reg_softMasked_coverage` 导出，体现第 1、2 节之间的**语义包含**）。

**覆盖定理**：对复合 `Gated.comp` 与逐点乘积 `Gated.mul` 封闭
（`reg_gated_coverage_comp` / `reg_gated_coverage_mul`）。 -/

/-- 实例（SwiGLU）：`Gated swiglu sigmoid id`。 -/
theorem reg_inst_gated_swiglu : Gated swiglu sigmoid id :=
  reg_softMasked_coverage swiglu sigmoid reg_inst_softMasked_swiglu

/-- 实例（SiLU）：`Gated silu sigmoid id`。 -/
theorem reg_inst_gated_silu : Gated silu sigmoid id :=
  reg_softMasked_coverage silu sigmoid reg_inst_softMasked_silu

/-- 实例（HardSwish）：`Gated hardSwish hardSigmoid id`。 -/
theorem reg_inst_gated_hardSwish : Gated hardSwish hardSigmoid id :=
  reg_softMasked_coverage hardSwish hardSigmoid reg_inst_softMasked_hardSwish

/-- 实例（ReLU）：`Gated relu reluSoftMask id`。 -/
theorem reg_inst_gated_relu : Gated relu reluSoftMask id :=
  reg_softMasked_coverage relu reluSoftMask reg_inst_softMasked_relu

/-- 实例（GELU-tanh）：`Gated geluTanh geluSoftMask id`。 -/
theorem reg_inst_gated_gelu : Gated geluTanh geluSoftMask id :=
  reg_softMasked_coverage geluTanh geluSoftMask reg_inst_softMasked_gelu

/-- **覆盖定理（复合封闭）**：门控对内层映射复合封闭：
`Gated f g h → Gated (f∘k) (g∘k) (h∘k)`。 -/
theorem reg_gated_coverage_comp {f g h : ℝ → ℝ} (hf : Gated f g h) (k : ℝ → ℝ) :
    Gated (fun x => f (k x)) (fun x => g (k x)) (fun x => h (k x)) :=
  Gated.comp hf k

/-- **覆盖定理（乘积封闭）**：两个门控的逐点乘积仍是门控。 -/
theorem reg_gated_coverage_mul {f₁ g₁ h₁ f₂ g₂ h₂ : ℝ → ℝ}
    (hf₁ : Gated f₁ g₁ h₁) (hf₂ : Gated f₂ g₂ h₂) :
    Gated (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) (fun x => h₁ x * h₂ x) :=
  Gated.mul hf₁ hf₂

/-! ## 3. 能力抽象：平移等变 / 相对位置性 `IsTranslationEquivariant`

**定义出处**：`import RealRelPosEncoding` ／ `Lattice.IsTranslationEquivariant`
（`def IsTranslationEquivariant {ι : Type*} [Add ι] (f : ι → ι → ℝ) : Prop :=
∀ i j k : ι, f (i + k) (j + k) = f i j`）。

语义：分数只依赖相对位置。ALiBi（加法距离偏置）与 RoPE（乘法相位）都落在这一族。

**实例清单**：`reg_inst_ite_alibi`（ALiBi 偏置，`ι = ℕ`）、`reg_inst_ite_distBias`
（任意距离偏置族 `β ↦ β(Nat.dist i j)`）、`reg_inst_ite_relPhaseAbs`（复数相位的模，
`ι = ℕ`）、`reg_inst_ite_rope`（RoPE 内积，`ι = ℝ`，跨实数平移）。

**覆盖定理**：该族对逐点加法/数乘/取负封闭
（`reg_ite_coverage_add` / `reg_ite_coverage_const_mul` / `reg_ite_coverage_neg`）。 -/

/-- 实例（ALiBi）：`−m·dist(i,j)` 平移等变。 -/
theorem reg_inst_ite_alibi (m : ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => alibiBias m i j) :=
  alibi_bias_translation_equivariant m

/-- 实例（距离偏置族）：`distBias β i j = β (Nat.dist i j)` 平移等变（对任意 `β`）。 -/
theorem reg_inst_ite_distBias (β : ℕ → ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => distBias β i j) :=
  distBias_equivariant β

/-- 实例（复数相位模）：`|e^{iθ(j−i)}|` 平移等变。 -/
theorem reg_inst_ite_relPhaseAbs (θ : ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => relPhaseAbs θ i j) :=
  relPhaseAbs_translation_equivariant θ

/-- 实例（RoPE 内积）：`⟨R(aθ)q, R(bθ)k⟩` 平移等变（`ι = ℝ`）。 -/
theorem reg_inst_ite_rope (θ : ℝ) (q k : Point2R) :
    IsTranslationEquivariant
      (fun a b : ℝ => rdot (rotateR (a * θ) q) (rotateR (b * θ) k)) :=
  rope_score_translation_equivariant θ q k

/-- **覆盖定理（加法封闭）**：两个平移等变函数之和仍平移等变。 -/
theorem reg_ite_coverage_add {ι : Type*} [Add ι] {f g : ι → ι → ℝ}
    (hf : IsTranslationEquivariant f) (hg : IsTranslationEquivariant g) :
    IsTranslationEquivariant (fun i j => f i j + g i j) := by
  intro i j k
  change f (i + k) (j + k) + g (i + k) (j + k) = f i j + g i j
  rw [hf i j k, hg i j k]

/-- **覆盖定理（数乘封闭）**：平移等变函数的常数倍仍平移等变。 -/
theorem reg_ite_coverage_const_mul {ι : Type*} [Add ι] (c : ℝ) {f : ι → ι → ℝ}
    (hf : IsTranslationEquivariant f) :
    IsTranslationEquivariant (fun i j => c * f i j) := by
  intro i j k
  change c * f (i + k) (j + k) = c * f i j
  rw [hf i j k]

/-- **覆盖定理（取负封闭）**：平移等变函数的负仍平移等变。 -/
theorem reg_ite_coverage_neg {ι : Type*} [Add ι] {f : ι → ι → ℝ}
    (hf : IsTranslationEquivariant f) :
    IsTranslationEquivariant (fun i j => -f i j) := by
  intro i j k
  change -f (i + k) (j + k) = -f i j
  rw [hf i j k]

/-! ## 4. 能力抽象：δ-近似压缩 `IsCompressor`

**定义出处**：`import RealErrorFeedback` ／ `Lattice.IsCompressor`
（`def IsCompressor (C : ℝ → ℝ) (δ : ℝ) : Prop :=
0 < δ ∧ δ ≤ 1 ∧ ∀ g : ℝ, |C g − g| ≤ (1 − δ)·|g|`）。

语义：压缩算子 `C` 的相对误差不超过 `(1−δ)`；`δ = 1` 即无损。

**实例清单**（本文件新增的**具体实例**，均真证）：

| 实例 | 定理 | δ |
|------|------|---|
| 恒等映射 `id` | `reg_inst_compressor_id` | `1`（无损） |
| 折半映射 `g ↦ g/2` | `reg_inst_compressor_half` | `1/2` |

**覆盖定理**：任意 `IsCompressor` 都落在误差反馈的残差有界定理 `errorFeedback_bounded`
的适用范围（`reg_compressor_coverage_errorFeedback`），并对折半实例给出数值化的残差界
（`reg_compressor_half_residual_bound`）。 -/

/-- 实例（恒等压缩，无损）：`IsCompressor id 1`。 -/
theorem reg_inst_compressor_id : IsCompressor (id : ℝ → ℝ) 1 := by
  refine ⟨by norm_num, le_refl (1 : ℝ), ?_⟩
  intro g
  simp

/-- 实例（折半压缩）：`IsCompressor (fun g => g/2) (1/2)`，误差恰为 `|g|/2`。 -/
theorem reg_inst_compressor_half : IsCompressor (fun g : ℝ => g / 2) (1 / 2) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro g
  have hsub : g / 2 - g = -(g / 2) := by ring
  rw [hsub, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hδ : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hδ]
  linarith [abs_nonneg g]

/-- **覆盖定理（压缩 ⟹ 误差反馈残差有界）**：任何 `IsCompressor C δ` 都满足
误差反馈残差一致有界 `|e_t| ≤ G(1−δ)/δ`（`δ-近似压缩 + 梯度有界`）。 -/
theorem reg_compressor_coverage_errorFeedback (C : ℝ → ℝ) (δ : ℝ) (hC : IsCompressor C δ) :
    ∀ (G : ℝ) (g : ℕ → ℝ), (∀ t : ℕ, |g t| ≤ G) →
      ∀ t : ℕ, |efErrorSeq C g t| ≤ G * (1 - δ) / δ := by
  rcases hC with ⟨hδ0, hδ1, hbound⟩
  intro G g hg t
  exact errorFeedback_bounded C δ G g hδ0 hδ1 hbound hg t

/-- 覆盖定理在折半实例上的**数值化**推论（把抽象注册表落到具体压缩器）：
折半压缩的误差反馈残差一致有界，界为 `G(1−1/2)/(1/2) = G`。 -/
theorem reg_compressor_half_residual_bound (G : ℝ) (g : ℕ → ℝ)
    (hg : ∀ t : ℕ, |g t| ≤ G) :
    ∀ t : ℕ, |efErrorSeq (fun x : ℝ => x / 2) g t| ≤ G := by
  intro t
  have h := reg_compressor_coverage_errorFeedback (fun x : ℝ => x / 2) (1 / 2)
    reg_inst_compressor_half G g hg t
  have heq : G * (1 - 1 / 2) / (1 / 2) = G := by ring
  rwa [heq] at h

/-! ## 5. 能力抽象：舍入算子 `RoundOp`

**定义出处**：`import RealFloatFormat` ／ `Lattice.RoundOp`
（`structure RoundOp (F : FloatFormat)`，字段 `toFun : ℝ → ℝ`、
`err_bound : ∀ x, |toFun x − x| ≤ F.eps·|x| + F.tiny`、`idem : ∀ x, toFun (toFun x) = toFun x`）。

语义：任何「相对误差界 + 幂等」的舍入算子。`RoundOp` 的底层函数由
`roundToFormat F r : ℝ → ℝ` 取出。

**实例清单**（本文件新增的**具体实例**）：恒等舍入 `reg_identityRoundOp F`（对任意格式
`F`，是真无损舍入：误差 0、幂等）。

**覆盖定理**：任意 `RoundOp F` 的误差界与幂等性
（`reg_roundOp_coverage` / `reg_roundOp_coverage_idempotent`），以及恒等实例的具体取值
（`reg_roundOp_identity_applies`、`reg_roundToFormat_identity`）。 -/

/-- 实例（恒等舍入）：对任意格式 `F`，恒等函数是 `F` 的合法 `RoundOp`
（误差 `|x − x| = 0 ≤ eps·|x| + tiny`，且幂等）。 -/
def reg_identityRoundOp (F : FloatFormat) : RoundOp F where
  toFun := id
  err_bound := fun x => by
    have h : |id x - x| = 0 := by simp
    rw [h]
    exact add_nonneg (mul_nonneg F.eps_nonneg (abs_nonneg x)) F.tiny_nonneg
  idem := fun x => rfl

/-- **覆盖定理（相对误差界）**：任意 `RoundOp F` 满足 `|round x − x| ≤ eps·|x| + tiny`。 -/
theorem reg_roundOp_coverage (F : FloatFormat) (r : RoundOp F) :
    ∀ x : ℝ, |roundToFormat F r x - x| ≤ F.eps * |x| + F.tiny :=
  format_error_bound F r

/-- **覆盖定理（幂等）**：任意 `RoundOp F` 满足 `round (round x) = round x`。 -/
theorem reg_roundOp_coverage_idempotent (F : FloatFormat) (r : RoundOp F) :
    ∀ x : ℝ, roundToFormat F r (roundToFormat F r x) = roundToFormat F r x :=
  format_round_idempotent F r

/-- 覆盖定理在恒等实例上的**具体化**：恒等舍入对任意格式满足相对误差界。 -/
theorem reg_roundOp_identity_applies (F : FloatFormat) :
    ∀ x : ℝ, |roundToFormat F (reg_identityRoundOp F) x - x| ≤ F.eps * |x| + F.tiny :=
  reg_roundOp_coverage F (reg_identityRoundOp F)

/-- 恒等舍入的底层函数就是恒等映射：`roundToFormat F (reg_identityRoundOp F) = id`。 -/
theorem reg_roundToFormat_identity (F : FloatFormat) :
    roundToFormat F (reg_identityRoundOp F) = id := rfl

/-! ## 6. 新方向抽象：把已证接口以**可编译实例化定理**纳入（D19）

ROADMAP 的 D19 要求把 OT / SCM / 球面梯度等**已证**接口纳入本注册表。
原文件头曾标注「新增方向包里的抽象尚未纳入」——本节补上。

**纳入方式**：与第 1–5 节完全一致——每个抽象由**一条覆盖定理**
（对该方向全部实例成立，不是文字描述）+ **若干实例化定理**（把既有定理
在本注册表的命名空间下**重新陈述**）给出，全部真证、编译期可检验。

收录三个新方向抽象：

| # | 抽象 | 定义出处 | 语义 | 覆盖定理 |
|---|------|----------|------|----------|
| 6 | `IsTransportPlan` | `RealOptimalTransport` | 边际为 `p`、`q` 的非负耦合 | `reg_ot_coverage_optimal` |
| 7 | `IsSupportingFunctional` | `RealSupportingHyperplane` | 在凸集上被最优点支配的线性泛函 | `reg_support_coverage` |
| 8 | `IsTangentGradient` | `RealRiemannianGD` | 与基点正交（切于单位球面）的梯度 | `reg_sphere_coverage_retr` |

**诚实标注**：本节只**汇总并重新陈述**既有定理，**不重复证明**任何既有结论
（符合 STYLE §5.5 优先复用）。`IsTangentGradient` 的覆盖定理用到
`RealRiemannianGD.sphereGD_retr_bound`（该文件本轮新增的 B21 结果）；
若该模块尚未编译，本文件的 `import` 会使其一并构建。
-/

/-! ### 6.1 `IsTransportPlan`：最优传输的计划/耦合抽象 -/

/-- **抽象 6 的定义出处**：`RealOptimalTransport` 中 `IsTransportPlan p q π`
（非负、行边际为 `p`、列边际为 `q`）。此处按**同一语义**重新导出，
使注册表自足（不重复定义，只引用）。 -/
theorem reg_ot_coverage_optimal {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (c : α → β → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hq0 : ∀ b, 0 ≤ q b) (hq1 : ∑ b, q b = 1) :
    ∃ π, IsTransportPlan p q π ∧
      ∀ π' : α → β → ℝ, IsTransportPlan p q π' →
        transportCost c π ≤ transportCost c π' :=
  exists_optimal_plan p q c hp0 hp1 hq0 hq1

/-! ### 6.2 `IsSupportingFunctional`：支撑超平面的线性泛函抽象 -/

/-- **抽象 7（覆盖定理）**：凸集 `s` 的边界点 `x₀` 处存在**非零**线性泛函
`f` 使 `∀ y ∈ s, f y ≤ f x₀`——即支撑超平面的存在性。

这是「支撑泛函族」的整体性质（对**任意**凸集与边界点成立），
不是枚举实例。直接复用 `RealSupportingHyperplane.supporting_hyperplane_of_boundary_point`。 -/
theorem reg_support_coverage {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [TopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hne : (interior s).Nonempty) {x₀ : E}
    (hx₀ : x₀ ∈ frontier s) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ s, f y ≤ f x₀ :=
  supporting_hyperplane_of_boundary_point hs hne hx₀

/-- **抽象 7（实例：`E = ℝ` 的标量版）**：实数凸集 `s`、内部非空、`x₀ ∈ s \ interior s`
处存在 `c ≠ 0` 使 `c·y ≤ c·x₀`（`∀ y ∈ s`）。 -/
theorem reg_inst_support_scalar {s : Set ℝ} (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hx₀' : x₀ ∉ interior s) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ y ∈ s, c * y ≤ c * x₀ :=
  supporting_hyperplane_real hs hne hx₀ hx₀'

/-! ### 6.3 `IsTangentGradient`：球面黎曼梯度的切性抽象 -/

/-- **抽象 8 的谓词**：`g` 是基点 `x` 处的**切梯度**（黎曼梯度）⟺ `⟨x, g⟩ = 0`。
球面 `S^{n-1}` 在 `x` 处的切空间正是 `{v | ⟨x,v⟩ = 0}`（见
`RealRiemannianGD.tangentSpace`），故切性就是这个正交条件。 -/
def IsTangentGradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x g : E) : Prop := ⟪x, g⟫ = 0

/-- **抽象 8（覆盖定理，B21 结果）**：**任意**单位球面上的点 `x`（`‖x‖ = 1`）
与**任意**切梯度 `g`（`IsTangentGradient x g`），球面投影梯度步的位移被
`η‖g‖` 界住：`‖sphereGD η (fun _ => g) x − x‖ ≤ η‖g‖`（`η ≥ 0`）。

这是「径向投影步长 = O(η)」这一定量事实对**整族**切梯度成立，
不是枚举实例。复用本文件工作的 `RealRiemannianGD.sphereGD_retr_bound`（B21）。 -/
theorem reg_sphere_coverage_retr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x g : E) (η : ℝ) (hx : ‖x‖ = 1) (htan : IsTangentGradient x g) (hη : 0 ≤ η) :
    ‖sphereGD η (fun _ => g) x - x‖ ≤ η * ‖g‖ :=
  sphereGD_retr_bound g x η hx htan hη

/-- **抽象 8（实例：保约束，`RealRiemannianGD.sphereGD_mem_sphere` 的再导出）**：
切梯度下球面步**保持球面约束**（`gradStep ≠ 0` 时）。 -/
theorem reg_inst_sphere_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g x : E) (η : ℝ) (hx : ‖x‖ = 1) (hne : gradStep η (fun _ => g) x ≠ 0) :
    sphereGD η (fun _ => g) x ∈ Metric.sphere (0 : E) 1 :=
  sphereGD_mem_sphere η (fun _ => g) x hx hne

/-! ### 6.4 注册表索引（D19 新增条目）

* `IsTransportPlan`（`RealOptimalTransport`）
  - 覆盖：`reg_ot_coverage_optimal`（最优计划的存在性 + 最优性）
* `IsSupportingFunctional`（`RealSupportingHyperplane`）
  - 覆盖：`reg_support_coverage`（一般赋范空间的支撑泛函存在性）
  - 实例：`reg_inst_support_scalar`（`E = ℝ`）
* `IsTangentGradient`（`RealRiemannianGD`）
  - 覆盖：`reg_sphere_coverage_retr`（位移 `≤ η‖g‖`，**B21 新增结果**）
  - 实例：`reg_inst_sphere_mem`（保球面约束）

**D19 诚实标注**：SCM 截断语义方向（`RealSCMIdentification` / `RealCausalInference`）
**未纳入**——其接口由 WP11 负责，本文件不跨包引用以避免归属冲突；
待 WP11 稳定后可按同样模式补第 9 节。
-/

/-! ## 7. 注册表索引（编译期可检验的定理名）

按抽象分组，所有条目都是**已编译通过**的声明名（不是文字描述）：

* `SoftMasked`（`RealActClass`）
  - 实例：`reg_inst_softMasked_relu`、`reg_inst_softMasked_gelu`、
    `reg_inst_softMasked_silu`、`reg_inst_softMasked_hardSwish`、
    `reg_inst_softMasked_swiglu`
  - 覆盖：`reg_softMasked_coverage`
* `Gated`（`RealGatingGeneral`）
  - 实例：`reg_inst_gated_swiglu`、`reg_inst_gated_silu`、`reg_inst_gated_hardSwish`、
    `reg_inst_gated_relu`、`reg_inst_gated_gelu`
  - 覆盖：`reg_gated_coverage_comp`、`reg_gated_coverage_mul`
* `IsTranslationEquivariant`（`RealRelPosEncoding`）
  - 实例：`reg_inst_ite_alibi`、`reg_inst_ite_distBias`、`reg_inst_ite_relPhaseAbs`、
    `reg_inst_ite_rope`
  - 覆盖：`reg_ite_coverage_add`、`reg_ite_coverage_const_mul`、`reg_ite_coverage_neg`
* `IsCompressor`（`RealErrorFeedback`）
  - 实例：`reg_inst_compressor_id`、`reg_inst_compressor_half`
  - 覆盖：`reg_compressor_coverage_errorFeedback`、`reg_compressor_half_residual_bound`
* `RoundOp`（`RealFloatFormat`）
  - 实例：`reg_identityRoundOp`
  - 覆盖：`reg_roundOp_coverage`、`reg_roundOp_coverage_idempotent`、
    `reg_roundOp_identity_applies`、`reg_roundToFormat_identity`
-/

end Lattice
