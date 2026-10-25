import Lattice.Lib.Chain.RealChain
import Mathlib

/-!
# LATTICE: 块级 Lipschitz 组合 —— transformer 块 → n 块端到端误差

RealChain（n 层链骨架）到 **transformer 块**的实例化：把块的
结构组合律（残差/加法/复合）完整化，各组件 Lipschitz 假设 ⟹ 块级
端到端误差：

  1. 加法保持：f、g 分别 Lf/Lg-Lipschitz ⟹ f+g 是 (Lf+Lg)-Lipschitz
     （三角不等式）；
  2. 残差连接：id + f 是 (1+Lf)-Lipschitz（恒等路径 +1）；
  3. 复合（向量版）：f∘g 是 Lf·Lg-Lipschitz（常数相乘）；
  4. 标准块：Block = F ∘ (id + A + G)（LN ∘ 残差注意力FFN）是
     Lf·(1+La+Lg)-Lipschitz；
  5. n 个同构块：端到端误差 ≤ (Lb)ⁿ·‖x−y‖（ChainN 实例化，
     ∏ 常数 = 幂）。

实例化路径（组件常数，各文件已证/可假设）：
  · 注意力：凸组合 + softmax Lipschitz ⟹ La（softmax 的 Lipschitz
    是连续可微的推论，作为块级假设）；
  · FFN：软掩码有效线性 ⟹ Lg ≤ max‖Wᵢ·sᵢ‖（softMask_FFN_effective）；
  · LN/规范化：缩放不变 ⟹ Lf 由数据范围决定；
  · 编辑/量化：Lipschitz 扰动（edit_output_bound_scalar）⟹ 误差经块传播。

模型无关：任意范数空间 X、任意 Lipschitz 组件、任意层数 n。
-/

noncomputable section

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 定理一：加法保持 Lipschitz
f、g 分别 Lf/Lg-Lipschitz ⟹ f+g 是 (Lf+Lg)-Lipschitz。-/

omit [NormedSpace ℝ X] in
theorem lipschitz_add (f g : X → X) (Lf Lg : ℝ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ Lf * ‖x - y‖)
    (hg : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖) :
    ∀ x y, ‖(f x + g x) - (f y + g y)‖ ≤ (Lf + Lg) * ‖x - y‖ := by
  intro x y
  calc
    ‖(f x + g x) - (f y + g y)‖ = ‖(f x - f y) + (g x - g y)‖ := by
      congr 1
      abel
    _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
    _ ≤ Lf * ‖x - y‖ + Lg * ‖x - y‖ := add_le_add (hf x y) (hg x y)
    _ = (Lf + Lg) * ‖x - y‖ := by ring

/-! ## 定理二：残差连接
id + f 是 (1+Lf)-Lipschitz（恒等路径 +1，残差不放大输入差）。-/

theorem lipschitz_residual (f : X → X) (Lf : ℝ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ Lf * ‖x - y‖) :
    ∀ x y, ‖(x + f x) - (y + f y)‖ ≤ (1 + Lf) * ‖x - y‖ := by
  have hid : ∀ x y : X, ‖x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    intro x y
    simp
  simpa using lipschitz_add (fun z => z) f 1 Lf hid hf

/-! ## 定理三：复合（向量版）
f∘g 是 Lf·Lg-Lipschitz（Lipschitz 常数相乘）。-/

omit [NormedSpace ℝ X] in
theorem lipschitz_comp (f g : X → X) (Lf Lg : ℝ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ Lf * ‖x - y‖)
    (hg : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖) (hLf : 0 ≤ Lf) :
    ∀ x y, ‖f (g x) - f (g y)‖ ≤ (Lf * Lg) * ‖x - y‖ := by
  intro x y
  calc
    ‖f (g x) - f (g y)‖ ≤ Lf * ‖g x - g y‖ := hf (g x) (g y)
    _ ≤ Lf * (Lg * ‖x - y‖) := mul_le_mul_of_nonneg_left (hg x y) hLf
    _ = (Lf * Lg) * ‖x - y‖ := by ring

/-! ## 定理四：标准 transformer 块
Block = F ∘ (id + A + G)（LN ∘ 残差注意力FFN）：
Lf·(1+La+Lg)-Lipschitz。-/

theorem block_lipschitz_bound (F A G : X → X) (Lf La Lg : ℝ)
    (hF : ∀ x y, ‖F x - F y‖ ≤ Lf * ‖x - y‖)
    (hA : ∀ x y, ‖A x - A y‖ ≤ La * ‖x - y‖)
    (hG : ∀ x y, ‖G x - G y‖ ≤ Lg * ‖x - y‖)
    (hLf : 0 ≤ Lf) :
    ∀ x y, ‖F (x + A x + G x) - F (y + A y + G y)‖ ≤ (Lf * (1 + La + Lg)) * ‖x - y‖ := by
  -- 内层 id + A + G 是 (1+La+Lg)-Lipschitz
  have hin : ∀ x y : X, ‖(x + A x + G x) - (y + A y + G y)‖ ≤ (1 + La + Lg) * ‖x - y‖ := by
    have hid : ∀ x y : X, ‖x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
      intro x y
      simp
    have hsum1 := lipschitz_add (fun z => z) A 1 La hid hA
    have hsum2 := lipschitz_add (fun z => z + A z) G (1 + La) Lg hsum1 hG
    simpa [add_assoc] using hsum2
  -- 外层 F 复合
  intro x y
  calc
    ‖F (x + A x + G x) - F (y + A y + G y)‖
        ≤ Lf * ‖(x + A x + G x) - (y + A y + G y)‖ := hF _ _
    _ ≤ Lf * ((1 + La + Lg) * ‖x - y‖) := mul_le_mul_of_nonneg_left (hin x y) hLf
    _ = (Lf * (1 + La + Lg)) * ‖x - y‖ := by ring

/-! ## 定理五：n 个同构块（端到端）
每块 Lb-Lipschitz ⟹ n 块链端到端误差 ≤ (Lb)ⁿ·‖x−y‖（ChainN 实例化）。-/

theorem chainN_identical_blocks_bound (B : X → X) (Lb : ℝ) (n : ℕ)
    (hB : ∀ x y, ‖B x - B y‖ ≤ Lb * ‖x - y‖) (hLb : 0 ≤ Lb) :
    ∀ x y, ‖ChainFwd (fun _ : ℕ => B) n x - ChainFwd (fun _ : ℕ => B) n y‖
      ≤ (Lb ^ n) * ‖x - y‖ := by
  intro x y
  have hb := chainN_error_bound (fun _ : ℕ => B) (fun _ : ℕ => Lb) n
    (by intro i hi; exact hB) (by intro i hi; exact hLb) x y
  have hprod : (∏ i in Finset.range n, Lb) = Lb ^ n := by
    rw [Finset.prod_const, Finset.card_range]
  simpa [hprod] using hb

/-! ## 注：实例化闭环
  组件 Lipschitz 常数（La：注意力凸组合+softmax 连续可微；
  Lg：FFN 软掩码有效线性；Lf：LN 数据范围缩放；编辑 Lipschitz
  扰动）代入定理四 ⟹ 单块常数 Lf·(1+La+Lg)；代入定理五 ⟹
  n 块端到端误差 (Lb)ⁿ——「完整模型前向链」（RealChain）的
  块级实例化完成。softmax 的 Lipschitz 常数是连续可微的推论
  （有界导数），留给验证器作为块级假设（模型无关保持）。-/

end Lattice
