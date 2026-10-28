import Mathlib
import Lattice.Runtime.RealNonlinear
import Lattice.Lib.Chain.RealComplex
import Lattice.Lib.Convex.RealSubgradient
import Lattice.Lib.Architectures.RealActClass
/-!
# LATTICE: modReLU —— 复数激活（相位保持、幅度门控）

§5 数域行「ℂ 全链（激活）」的激活组件：复值神经网络的 modReLU
（Arjovsky 等，modReLU b z = relu(|z| + b) · z/|z|，b 为实数偏置）。

数学结构：
  1. **幅度门控**：|modReLU b z| = relu(|z| + b) —— 输出模长 = 幅度 ReLU；
  2. **相位保持**：z ≠ 0 时 modReLU b z = (relu(|z|+b)/|z|) · z —— 与 z 同向，
     标量系数 relu(|z|+b)/|z| ≥ 0（正实数增益，modReLU_gain_nonneg）；
  3. **z = 0 处理**：定义用 `if z = 0 then 0 else ...` 避免 0/0，约定 modReLU b 0 = 0
     （modReLU_zero）；故模长等式在 z ≠ 0 成立（z = 0 时 LHS = 0 而
     relu(|0|+b) = relu b 在 b > 0 时非零——诚实标注）。

ℂ 全链衔接：RealComplex 给出 ℂ 代数基础（normSq/内积恒等式），本文件在其上落地
激活层；与 RealActClass.SoftMasked（实软掩码 s ∈ [0,1]）对照：modReLU 是
「复软掩码」——z ≠ 0 时 modReLU b z = s·z、s ≥ 0（modReLU_nonneg_gain）；
与实软掩码的区别是 s 无上界 1（它还重缩放模长，不是纯门控）。

诚实边界：
  · modReLU b 0 = 0 是约定（if 分支），模长等式需 z ≠ 0（见上）；
  · 1-Lipschitz 的**真实真值已澄清**（见 `RealModReLULipschitz`，CORRECTIONS B15）：
    **`b ≤ 0` 时成立**（`modReLU_lipschitz_of_nonpos`，完整证明——此时 modReLU 是极坐标
    软阈值 `z ↦ max(0,|z|−c)·z/|z|`，`c = −b ≥ 0`）；**`b > 0` 时为假**
    （机器验证反例 `modReLU_not_one_lipschitz_for_pos_bias`：`b = 1, z = 0, w = 1/2`
    给出 `3/2 > 1/2`——偏置 `b > 0` 使 modReLU 在 `0` 处不连续）。
    故本文件早期「1-Lipschitz 未证」的表述**已由 `RealModReLULipschitz` 推进**：
    一般 `b` 的全称命题为假，只有 `b ≤ 0` 半边为真。
    本文件退化为上界 modReLU_bounded：|modReLU b z| ≤ |z| + |b|；
  · 幅度次梯度衔接：|z| + b > 0 时 ∂relu(|z|+b) = {1}
    （modReLU_magnitude_subgradient，复用 RealSubgradient.relu_subgradient_positive）。

mathlib 4.14 说明：**在 ℂ 上**无 `Abs` 实例，故 ℂ 上的 `|z|` 记法不可用，
统一用 `Complex.abs z`（ℝ 上的 `|·|` 记法不受影响，本文件后续 `abs_add` /
`abs_div` / `abs_of_nonneg` 等 ℝ 引理照常使用）
（‖z‖ = Complex.abs z，`Complex.norm_eq_abs` 是 rfl；`Complex.abs` 是
`AbsoluteValue ℂ ℝ`，故 `AbsoluteValue.map_mul` / `AbsoluteValue.nonneg` 可用）。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice

/-! ## modReLU 定义
modReLU b z = relu(|z| + b) · z/|z|（z ≠ 0）；z = 0 时按约定取 0
（if 分支避免 0/0；|z| 在 ℂ 上写作 Complex.abs z）。-/

def modReLU (b : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else ((relu (Complex.abs z + b) : ℝ) : ℂ) * (z / (Complex.abs z : ℂ))

/-! ## 定理一：z = 0 分支（约定）
modReLU b 0 = 0 —— if 分支直接给出（避免 0/0）。-/

@[simp] theorem modReLU_zero (b : ℝ) : modReLU b 0 = 0 := by
  unfold modReLU
  simp

/-! ## 定理二：相位保持（核心）
z ≠ 0 ⟹ modReLU b z = (relu(|z|+b)/|z|) · z——与 z 同方向（标量倍）。
证明：展开定义、if_neg 消掉 z = 0 分支，`Complex.ofReal_div` 把
↑(relu(|z|+b)/|z|) 写成 ↑relu(|z|+b) / ↑|z|，ring 处理域恒等式。-/

theorem modReLU_phase_preserved (b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    modReLU b z = ((relu (Complex.abs z + b) / Complex.abs z : ℝ) : ℂ) * z := by
  unfold modReLU
  rw [if_neg hz]
  rw [Complex.ofReal_div]
  ring

/-! ## 引理：幅度增益非负
系数 relu(|z|+b)/|z| ≥ 0（relu 非负 ÷ 非负）——相位保持的标量是正实数。 -/

lemma modReLU_gain_nonneg (b : ℝ) (z : ℂ) : 0 ≤ relu (Complex.abs z + b) / Complex.abs z := by
  exact div_nonneg (relu_nonneg (Complex.abs z + b)) (Complex.abs.nonneg z)

/-! ## 定理三：复软掩码（与 RealActClass.SoftMasked 对照）
z ≠ 0 ⟹ 存在 s ≥ 0 使 modReLU b z = s·z（相位保持 + 增益非负；
与实软掩码 s ∈ [0,1] 的区别：复数增益无上界 1，因为还重缩放模长）。 -/

theorem modReLU_nonneg_gain (b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    ∃ s : ℝ, 0 ≤ s ∧ modReLU b z = (s : ℂ) * z := by
  refine ⟨relu (Complex.abs z + b) / Complex.abs z, modReLU_gain_nonneg b z, ?_⟩
  exact modReLU_phase_preserved b z hz

/-! ## 定理四：幅度门控（核心）
z ≠ 0 ⟹ |modReLU b z| = relu(|z| + b)——输出模长 = 幅度 ReLU。
证明：相位保持 → |(relu(|z|+b)/|z|)·z| = |relu(|z|+b)/|z||·|z|
（AbsoluteValue.map_mul）→ |r/n|·|z| = |r|/|n|·|z|（abs_div）→
r/n·n = r（abs_of_nonneg 两次 + div_mul_cancel₀）。 -/

theorem modReLU_magnitude (b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    Complex.abs (modReLU b z) = relu (Complex.abs z + b) := by
  rw [modReLU_phase_preserved b z hz]
  rw [AbsoluteValue.map_mul]
  rw [Complex.abs_ofReal]
  rw [abs_div]
  rw [abs_of_nonneg (relu_nonneg (Complex.abs z + b))]
  rw [abs_of_nonneg (Complex.abs.nonneg z)]
  have hzabs : Complex.abs z ≠ 0 := by
    rw [← Complex.norm_eq_abs z]
    exact fun h => hz (norm_eq_zero.mp h)
  rw [div_mul_cancel₀ (relu (Complex.abs z + b)) hzabs]

/-! ## 引理：relu 被绝对值控制
relu x = max x 0 ≤ |x|（x ≤ |x| 且 0 ≤ |x|）——上界定理的部件。 -/

lemma relu_le_abs (x : ℝ) : relu x ≤ |x| := by
  unfold relu
  exact max_le (le_abs_self x) (abs_nonneg x)

/-! ## 定理五：幅度上界（Lipschitz 的诚实退化）
|modReLU b z| ≤ |z| + |b|（对一切 z 成立，含 z = 0）。
z = 0：0 ≤ |b|；z ≠ 0：|modReLU b z| = relu(|z|+b) ≤ ||z|+b| ≤ |z|+|b|。
注：1-Lipschitz `|modReLU b z − modReLU b w| ≤ |z − w|` 的**真值**见
`RealModReLULipschitz`（CORRECTIONS B15）：`b ≤ 0` 时**成立**（完整证明），
`b > 0` 时**为假**（机器验证反例）。故「对一切 b 的 1-Lipschitz」为假命题，
本文件只保留上述幅度上界。 -/

theorem modReLU_bounded (b : ℝ) (z : ℂ) : Complex.abs (modReLU b z) ≤ Complex.abs z + |b| := by
  by_cases hz : z = 0
  · subst hz
    rw [modReLU_zero b]
    rw [← Complex.norm_eq_abs (0 : ℂ)]
    simp
  · rw [modReLU_magnitude b z hz]
    calc
      relu (Complex.abs z + b) ≤ |Complex.abs z + b| := relu_le_abs _
      _ ≤ |Complex.abs z| + |b| := abs_add _ _
      _ = Complex.abs z + |b| := by rw [abs_of_nonneg (Complex.abs.nonneg z)]

/-! ## 定理六：幅度次梯度衔接（复用 RealSubgradient）
|z| + b > 0 ⟹ 1 ∈ ∂relu(|z|+b)——幅度门控在激活区是线性增长
（RealSubgradient.relu_subgradient_positive 的实例化）。 -/

theorem modReLU_magnitude_subgradient (b : ℝ) (z : ℂ) (hz : 0 < Complex.abs z + b) :
    Subgradient relu (Complex.abs z + b) 1 :=
  (relu_subgradient_positive (Complex.abs z + b) 1 hz).mpr rfl

end Lattice
