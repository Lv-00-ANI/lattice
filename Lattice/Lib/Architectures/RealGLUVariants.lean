import Mathlib
import Lattice.Lib.Architectures.RealGatingGeneral
import Lattice.Lib.Architectures.RealActComplete
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealSwiGLU
/-!
# LATTICE: GLU 变体族 —— ReGLU / GeGLU / SiLU-GLU 的门控统一与界

`RealGatingGeneral` 把"激活"统一为**门控** `f(x) = g(x)·h(x)`（`Gated`），并给出
ReLU / GELU / SiLU / SwiGLU / hard-swish 的实例。本文件把 **GLU 变体族**接入同一框架：

    glu act a b(x) = act(a x) · b(x)      （一般门控线性单元）
    reglu   a b(x) = relu(a x) · b(x)
    geglu   a b(x) = geluTanh(a x) · b(x)
    siluGLU a b(x) = silu(a x) · b(x)

核心观察：**若 `act` 本身是软掩码激活（`SoftMasked act s`），则 GLU 就是门控
`(s∘a)·(a·b)`**——即"GLU = 两次投影 + 一个已在门控类中的激活"，无需新的假设。
于是既有的门控定理（有界、Lipschitz、FFN 有效线性）**对整族成立**。

本文件建立：
  1. `glu_is_gated`（核心）：`SoftMasked act s` ⟹ `glu act a b` 是门控 `(s∘a, a·b)`；
  2. `reglu_is_gated` / `geglu_is_gated` / `siluGLU_is_gated`：三个实例（回收既有软掩码定理）；
  3. `glu_bound`：`|act| ≤ 1` ⟹ `|glu act a b x| ≤ |b x|`（门控不放大信号）；
  4. `reluSoftMask_abs_le_one` / `geluSoftMask_abs_le_one`：掩码的 `|·| ≤ 1`（供 3 使用）；
  5. `reglu_bound` / `geglu_bound` / `siluGLU_bound`：三实例的界；
  6. `glu_ffn_effective`：GLU-FFN 的逐元素形式（对整族成立）；
  7. `glu_vs_swiglu_proj`：**投影计数**：GLU 用 2 个投影、SwiGLU（`a`/`b`/`c`）用 3 个
     （`glu_projCount = 2 < swiglu_projCount = 3`）。

**诚实边界**：
- 投影计数是**工程计数抽象**（不含张量形状/参数量细节），与 `RealWeightSharing` 的同类标注一致；
- 未做 GLU 的训练收敛性（那属训练线，本文件只给结构性质与界）；
- 模型无关：任意投影 `a`、`b : ℝ → ℝ`（可为线性层、可含偏置），不特化具体网络。

无 sorry/axiom/admit。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice

/-! ## 定义：一般 GLU 与三个实例 -/

/-- 一般门控线性单元：`glu act a b x = act (a x) · b x`。 -/
def glu (act : ℝ → ℝ) (a b : ℝ → ℝ) (x : ℝ) : ℝ := act (a x) * b x

/-- ReGLU：门 = ReLU ∘ a，信号 = b。 -/
def reglu (a b : ℝ → ℝ) (x : ℝ) : ℝ := glu relu a b x

/-- GeGLU：门 = GELU-tanh ∘ a，信号 = b。 -/
def geglu (a b : ℝ → ℝ) (x : ℝ) : ℝ := glu geluTanh a b x

/-- SiLU-GLU（= Swish-GLU）：门 = SiLU ∘ a，信号 = b。 -/
def siluGLU (a b : ℝ → ℝ) (x : ℝ) : ℝ := glu silu a b x

/-! ## 定理一（核心）：软掩码激活 ⟹ GLU 是门控 -/

/-- `SoftMasked act s` ⟹ `glu act a b = (s∘a)·(a·b)`，即 GLU 落在 `Gated` 类中。 -/
theorem glu_is_gated {act s : ℝ → ℝ} (hsm : SoftMasked act s) (a b : ℝ → ℝ) :
    Gated (glu act a b) (fun x => s (a x)) (fun x => a x * b x) := by
  intro x
  unfold glu
  rw [hsm.1 (a x)]
  ring

/-! ## 定理二：三个实例 -/

/-- ReGLU 是门控（回收 `relu_is_soft_masked`）。 -/
theorem reglu_is_gated (a b : ℝ → ℝ) :
    Gated (reglu a b) (fun x => reluSoftMask (a x)) (fun x => a x * b x) :=
  glu_is_gated relu_is_soft_masked a b

/-- GeGLU 是门控（回收 `gelu_is_soft_masked`）。 -/
theorem geglu_is_gated (a b : ℝ → ℝ) :
    Gated (geglu a b) (fun x => geluSoftMask (a x)) (fun x => a x * b x) :=
  glu_is_gated gelu_is_soft_masked a b

/-- SiLU-GLU 是门控（回收 `silu_is_soft_masked`）。 -/
theorem siluGLU_is_gated (a b : ℝ → ℝ) :
    Gated (siluGLU a b) (fun x => sigmoid (a x)) (fun x => a x * b x) :=
  glu_is_gated silu_is_soft_masked a b

/-! ## 掩码的绝对值界（供 §四 使用） -/

/-- `reluSoftMask` 取值于 {0,1}，故 `|·| ≤ 1`。 -/
lemma reluSoftMask_abs_le_one (x : ℝ) : |reluSoftMask x| ≤ 1 := by
  unfold reluSoftMask
  split <;> simp

/-- `geluSoftMask ∈ [0,1]`，故 `|·| ≤ 1`（回收 `gelu_soft_mask_bounds`）。 -/
lemma geluSoftMask_abs_le_one (x : ℝ) : |geluSoftMask x| ≤ 1 := by
  have h := gelu_soft_mask_bounds x
  rw [abs_of_nonneg h.1]
  exact h.2

/-- `sigmoid ∈ [0,1]`，故 `|·| ≤ 1`（回收 `sigmoid_bounds`）。 -/
lemma sigmoid_abs_le_one (x : ℝ) : |sigmoid x| ≤ 1 := by
  have h := sigmoid_bounds x
  rw [abs_of_nonneg (le_of_lt h.1)]
  exact le_of_lt h.2

/-! ## 定理三：门控不放大 -/

/-- `|act| ≤ 1` ⟹ `|glu act a b x| ≤ |b x|`（门控只缩放、不放大信号）。 -/
theorem glu_bound {act : ℝ → ℝ} (hact : ∀ y, |act y| ≤ 1) (a b : ℝ → ℝ) (x : ℝ) :
    |glu act a b x| ≤ |b x| := by
  unfold glu
  rw [abs_mul]
  calc |act (a x)| * |b x| ≤ 1 * |b x| :=
        mul_le_mul_of_nonneg_right (hact (a x)) (abs_nonneg _)
    _ = |b x| := one_mul _

/-- 门控型界：`act` 是软掩码 `s` 的激活且 `|s| ≤ 1` ⟹ `|glu act a b x| ≤ |a x · b x|`。 -/
theorem glu_mask_bound {act s : ℝ → ℝ} (hsm : SoftMasked act s) (hs : ∀ y, |s y| ≤ 1)
    (a b : ℝ → ℝ) (x : ℝ) : |glu act a b x| ≤ |a x * b x| :=
  gated_abs_le (glu_is_gated hsm a b) (fun y => hs (a y)) x

/-- ReGLU 的界（门控型）。 -/
theorem reglu_bound (a b : ℝ → ℝ) (x : ℝ) : |reglu a b x| ≤ |a x * b x| :=
  glu_mask_bound relu_is_soft_masked reluSoftMask_abs_le_one a b x

/-- GeGLU 的界（门控型）。 -/
theorem geglu_bound (a b : ℝ → ℝ) (x : ℝ) : |geglu a b x| ≤ |a x * b x| :=
  glu_mask_bound gelu_is_soft_masked geluSoftMask_abs_le_one a b x

/-- SiLU-GLU 的界（门控型）。 -/
theorem siluGLU_bound (a b : ℝ → ℝ) (x : ℝ) : |siluGLU a b x| ≤ |a x * b x| :=
  glu_mask_bound silu_is_soft_masked sigmoid_abs_le_one a b x

/-! ## 定理四：GLU-FFN 的逐元素形式（对整族成立） -/

/-- `Σ Wᵢ·glu act a b (Hᵢ) = Σ Wᵢ·(act(a Hᵢ)·b Hᵢ)`（按定义即证）。 -/
theorem glu_ffn_effective {ι : Type*} [Fintype ι] (act a b : ℝ → ℝ) (W H : ι → ℝ) :
    ∑ i, W i * glu act a b (H i) = ∑ i, W i * (act (a (H i)) * b (H i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- 把上一行与门控形式对齐：`= Σ Wᵢ·((s(a Hᵢ))·(a Hᵢ·b Hᵢ))`（`SoftMasked act s` 时）。 -/
theorem glu_ffn_effective_gated {ι : Type*} [Fintype ι] {act s : ℝ → ℝ}
    (hsm : SoftMasked act s) (a b : ℝ → ℝ) (W H : ι → ℝ) :
    ∑ i, W i * glu act a b (H i) = ∑ i, W i * (s (a (H i)) * (a (H i) * b (H i))) := by
  apply Finset.sum_congr rfl
  intro i _
  unfold glu
  rw [hsm.1 (a (H i))]
  ring

/-! ## 定理五：投影计数（工程抽象） -/

/-- GLU 族的投影数（门投影 + 信号投影）。 -/
def glu_projCount : ℕ := 2

/-- SwiGLU 的投影数（门 + 信号 + 第三个投影，见 `RealGatingGeneral.swigluPair`）。 -/
def swiglu_projCount : ℕ := 3

/-- GLU 族比 SwiGLU 少一个投影（工程计数抽象，不含张量形状细节）。 -/
theorem glu_vs_swiglu_proj : glu_projCount < swiglu_projCount := by
  unfold glu_projCount swiglu_projCount
  norm_num

end Lattice
