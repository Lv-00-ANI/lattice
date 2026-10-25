import Mathlib

/-!
# LATTICE: 算子范数代数 —— 线性层 Lipschitz 与范数运算（维度线完善）

矩阵/算子范数线（RealMatrix matvec 桥）的代数完善：算子范数
‖·‖ 的运算性质，直接服务链 Lipschitz 常数（RealChain/RealBlockLipschitz
的 La/Lg 计算）：

  1. 线性层 Lipschitz：‖W·x − W·y‖ ≤ ‖W‖·‖x−y‖（FFN/线性层 L = ‖W‖）；
  2. 复合范数：‖W∘V‖ ≤ ‖W‖·‖V‖（链常数相乘的算子形式）；
  3. 加法三角：‖W₁+W₂‖ ≤ ‖W₁‖+‖W₂‖（块内线性组合）；
  4. 标量缩放：‖c·W‖ = |c|·‖W‖；
  5. 伴随保范数：‖A†‖ = ‖A‖（ROME/编辑伴随衔接）。

实例化：FFN 层 Lg = ‖W‖（linear_map_lipschitz），注意力投影
La = max‖Vᵢ‖（convComb_lipschitz_prob + 本文件）——代入
block_lipschitz_bound 得完整块常数。

模型无关：任意范数空间（ℝ 标量；伴随部分 ℝ-内积空间）。
-/

noncomputable section

open scoped InnerProduct

namespace Lattice

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ## 定理一：线性层 Lipschitz
‖W·x − W·y‖ ≤ ‖W‖·‖x−y‖（W 是 ‖W‖-Lipschitz）。-/

theorem linear_map_lipschitz (W : E →L[ℝ] F) :
    ∀ x y, ‖W x - W y‖ ≤ ‖W‖ * ‖x - y‖ := by
  intro x y
  have hlin : ‖W x - W y‖ = ‖W (x - y)‖ := by rw [← W.map_sub]
  rw [hlin]
  exact W.le_opNorm (x - y)

/-! ## 定理二：复合算子范数
‖W∘V‖ ≤ ‖W‖·‖V‖（链常数相乘的算子形式）。-/

theorem comp_norm_bound (W : F →L[ℝ] G) (V : E →L[ℝ] F) :
    ‖W ∘L V‖ ≤ ‖W‖ * ‖V‖ :=
  W.opNorm_comp_le V

/-! ## 定理三：加法三角
‖W₁ + W₂‖ ≤ ‖W₁‖ + ‖W₂‖。 -/

theorem add_norm_bound (W₁ W₂ : E →L[ℝ] F) :
    ‖W₁ + W₂‖ ≤ ‖W₁‖ + ‖W₂‖ :=
  norm_add_le _ _

/-! ## 定理四：标量缩放
‖c·W‖ = |c|·‖W‖。 -/

theorem smul_norm_bound (c : ℝ) (W : E →L[ℝ] F) :
    ‖c • W‖ = |c| * ‖W‖ := by
  -- ℝ 的范数即绝对值（Norm ℝ = |·|），norm_smul 直接给出
  exact norm_smul c W

/-! ## 伴随部分：保范数 -/

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-! ## 定理五：伴随保范数
‖A†‖ = ‖A‖（伴随是线性等距）。-/

theorem norm_adjoint_eq (A : H →L[ℝ] K) :
    ‖A†‖ = ‖A‖ :=
  (ContinuousLinearMap.adjoint.norm_map A)

/-! ## 注：链常数服务
  FFN/线性层 Lg = ‖W‖（定理一）；复合层 ‖W₂∘W₁‖ ≤ ‖W₂‖‖W₁‖
  （定理二，链常数相乘的算子形式）；块内线性组合加法（定理三）；
  缩放归一化（定理四）；编辑伴随（定理五）——代入
  RealBlockLipschitz.block_lipschitz_bound 即得完整块 Lipschitz
  常数的闭式计算。维度线（算子范数）完善。-/

end Lattice
