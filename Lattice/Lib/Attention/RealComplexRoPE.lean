import Mathlib
import Lattice.Lib.Attention.RealRoPE
import Lattice.Lib.Chain.RealComplex
import Lattice.Lib.LinearAlgebra.RealInnerScalar
/-!
# LATTICE: 复数 RoPE —— 复数域旋转位置编码（ℂ 全链模块二，与 RealRoPE 互补）

方向：RoPE 的**原始复数形式**。位置 m 的向量 z 乘相位因子 e^{iθm}：

    R_m(z) = z · e^{iθm}      （θ 为基频，m 为位置，e^{iθm} = cos(θm) + i·sin(θm)，Euler）

三个性质（与 RealRoPE 实数 2D 版一一对应）：
  1. **旋转保模**：|R_m(z)| = |z|（|e^{iθm}| = 1）；
  2. **旋转组合**：R_m ∘ R_n = R_{m+n}（e^{iθm}·e^{iθn} = e^{iθ(m+n)}，Complex.exp_add）；
  3. **核心——相对位置只影响相位**：
     ⟨R_m q, R_n k⟩ = ⟨q, k⟩ · e^{iθ(n−m)}，
     于是 |⟨R_m q, R_n k⟩| = |⟨q,k⟩|（相位因子模 1 → 注意力分数在位置编码下模稳定）。

与 RealRoPE 的关系：RealRoPE 是复数版的 2D 实数投影（把 z = x + iy 与点 (x,y) 等同，
乘以 e^{iθ} 即 ℝ² 中角度 θ 的旋转，旋转矩阵 [[cosθ, −sinθ],[sinθ, cosθ]] 正是
`rotateR`）；本文件直接在 ℂ 上陈述，证明只依赖 exp 的加法性（exp_add）与
|e^{ix}| = 1（abs_exp_ofReal_mul_I），不再展开 cos/sin。

ℂ 内积惯例（#check `RCLike.inner_apply` 实测）：
  ⟪x, y⟫ = conj x · y     （共轭线性于第一参数、线性于第二参数）
据此 ⟨R_m q, R_n k⟩ = conj(q·e^{iθm})·(k·e^{iθn}) = conj q · conj(e^{iθm}) · k · e^{iθn}
= ⟨q,k⟩ · e^{iθ(n−m)}——相位因子是 **e^{iθ(n−m)}**（相对位置 n−m；若采用「线性于
第一参数」的另类惯例则相位取 m−n，本文件以 mathlib 惯例为准）。模长形式与相位方向无关。

模型无关性：θ、m、n 是任意实数，q、k 是任意复数——任何基频/位置实例化都成立，
不依赖任何具体模型的维度/基频配置（与 RealRoPE.lean 同一立场）。

证明路线：conj 与 exp 交换（`NormedSpace.map_exp` + `Complex.exp_eq_exp_ℂ` 桥接）
⟹ conj(e^{iθm}) = e^{−iθm}；再以 `Complex.exp_add`、`Complex.abs_exp_ofReal_mul_I`、
`AbsoluteValue.map_mul`（|z·w| = |z|·|w|）与 ring 完成。所有定理只引用 mathlib 4.14
现成引理与本文件内部引理，无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open scoped ComplexConjugate

/-! mathlib 4.14 中 ⟪x, y⟫ 是作用域内记法；本文件在 ℂ 上使用与 RealComplex 一致的
显式本地记法（固定 𝕜 := ℂ）。-/
local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-! ## 定义：复数旋转算子（位置编码 R_m(z) = z·e^{iθm}） -/

def complexRotate (θ m : ℝ) (z : ℂ) : ℂ := z * Complex.exp (((θ * m : ℝ) : ℂ) * Complex.I)

/-! ## 基础恒等式 -/

/-! ℂ 内积惯例：⟪x, y⟫ = conj x · y（mathlib `RCLike.inner_apply` 的 ℂ 实例，
共轭线性于第一参数——本文件全部内积推导以此为准）。-/

theorem complex_inner_apply (x y : ℂ) : ⟪x, y⟫ = conj x * y := by
  simp

/-! conj 与 exp 交换：conj(e^z) = e^(conj z)。
证明：`Complex.exp_eq_exp_ℂ` 把 Complex.exp 桥接到 NormedSpace.exp，
`NormedSpace.map_exp` 对连续环同态（starRingEnd ℂ = conj，`Complex.continuous_conj`）成立。-/

lemma complex_conj_exp (z : ℂ) : conj (Complex.exp z) = Complex.exp (conj z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp ℂ (starRingEnd ℂ) Complex.continuous_conj z

/-! conj(e^{ix}) = e^{−ix}（相位共轭 = 反向旋转；上一条 + conj((x:ℂ)·I) = (−x:ℂ)·I）。-/

lemma complex_conj_exp_mul_I (x : ℝ) :
    conj (Complex.exp (((x : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [complex_conj_exp]
  exact congrArg Complex.exp (by
    calc
      conj (((x : ℝ) : ℂ) * Complex.I) = conj ((x : ℝ) : ℂ) * conj Complex.I := by
        rw [map_mul (starRingEnd ℂ)]
      _ = ((x : ℝ) : ℂ) * (-Complex.I) := by simp [Complex.conj_ofReal, Complex.conj_I]
      _ = ((-x : ℝ) : ℂ) * Complex.I := by
        rw [Complex.ofReal_neg]
        ring)

/-! 相位因子模 1：|e^{iθm}| = 1（mathlib `Complex.abs_exp_ofReal_mul_I`）。-/

theorem complex_phase_abs_one (θ m : ℝ) :
    Complex.abs (Complex.exp (((θ * m : ℝ) : ℂ) * Complex.I)) = 1 :=
  Complex.abs_exp_ofReal_mul_I (θ * m)

/-! 相位相加：(a:ℂ)·I + (b:ℂ)·I = (a+b:ℂ)·I（把 ℝ 加法抬到 exp 的自变量，
配合 Complex.exp_add 得 e^{ia}·e^{ib} = e^{i(a+b)}）。-/

lemma complex_phase_sum (a b : ℝ) :
    (((a : ℝ) : ℂ) * Complex.I) + (((b : ℝ) : ℂ) * Complex.I) =
      (((a + b : ℝ) : ℂ) * Complex.I) := by
  calc
    ((a : ℝ) : ℂ) * Complex.I + ((b : ℝ) : ℂ) * Complex.I
        = (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ)) * Complex.I := by ring
    _ = ((a + b : ℝ) : ℂ) * Complex.I := by rw [← Complex.ofReal_add]

/-! ## 定理一：旋转保模
|R_m(z)| = |z|（|z·e^{iθm}| = |z|·|e^{iθm}| = |z|·1）。-/

theorem complex_rotation_preserves_abs (θ m : ℝ) (z : ℂ) :
    Complex.abs (complexRotate θ m z) = Complex.abs z := by
  unfold complexRotate
  rw [AbsoluteValue.map_mul]
  rw [complex_phase_abs_one θ m]
  ring

/-! ## 定理二：旋转组合
R_m (R_n z) = R_{m+n} z（e^{iθn}·e^{iθm} = e^{iθ(m+n)}，Complex.exp_add）。-/

theorem complex_rotation_compose (θ m n : ℝ) (z : ℂ) :
    complexRotate θ m (complexRotate θ n z) = complexRotate θ (m + n) z := by
  unfold complexRotate
  calc
    (z * Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((θ * m : ℝ) : ℂ) * Complex.I)
        = z * (Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((θ * m : ℝ) : ℂ) * Complex.I)) := by ring
    _ = z * Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I +
        ((θ * m : ℝ) : ℂ) * Complex.I) := by rw [← Complex.exp_add]
    _ = z * Complex.exp (((θ * (m + n) : ℝ) : ℂ) * Complex.I) := by
      exact congrArg (fun r : ℂ => z * Complex.exp r) (by
        calc
          ((θ * n : ℝ) : ℂ) * Complex.I + ((θ * m : ℝ) : ℂ) * Complex.I
              = ((θ * n + θ * m : ℝ) : ℂ) * Complex.I := complex_phase_sum (θ * n) (θ * m)
          _ = ((θ * (m + n) : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun r : ℝ => (r : ℂ) * Complex.I) (by ring))

/-! ## 定理三：相位移动（核心）
⟨R_m q, R_n k⟩ = ⟨q, k⟩ · e^{iθ(n−m)}——相对位置只改变内积的**相位**。
（方向：由 ℂ 内积惯例 ⟪x,y⟫ = conj x·y 推出相位因子为 e^{iθ(n−m)}；见模块 docstring。）
证明路线：⟪q·e^{iθm}, k·e^{iθn}⟫ = conj(q·e^{iθm})·(k·e^{iθn})
= conj q · conj(e^{iθm}) · k · e^{iθn} = conj q · k · e^{iθ(n−m)}。 -/

theorem complex_rope_phase_shift (θ m n : ℝ) (q k : ℂ) :
    ⟪complexRotate θ m q, complexRotate θ n k⟫ =
      ⟪q, k⟫ * Complex.exp (((θ * (n - m) : ℝ) : ℂ) * Complex.I) := by
  unfold complexRotate
  rw [RCLike.inner_apply]
  rw [map_mul (starRingEnd ℂ)]
  rw [complex_conj_exp_mul_I (θ * m)]
  calc
    (conj q * Complex.exp (((-(θ * m) : ℝ) : ℂ) * Complex.I)) *
        (k * Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I))
        = conj q * k * (Complex.exp (((-(θ * m) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((θ * n : ℝ) : ℂ) * Complex.I)) := by ring
    _ = conj q * k * Complex.exp (((-(θ * m) : ℝ) : ℂ) * Complex.I +
        ((θ * n : ℝ) : ℂ) * Complex.I) := by rw [← Complex.exp_add]
    _ = conj q * k * Complex.exp (((θ * (n - m) : ℝ) : ℂ) * Complex.I) := by
      exact congrArg (fun r : ℂ => conj q * k * Complex.exp r) (by
        calc
          ((-(θ * m) : ℝ) : ℂ) * Complex.I + ((θ * n : ℝ) : ℂ) * Complex.I
              = ((-(θ * m) + θ * n : ℝ) : ℂ) * Complex.I := complex_phase_sum (-(θ * m)) (θ * n)
          _ = ((θ * (n - m) : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun r : ℝ => (r : ℂ) * Complex.I) (by ring))

/-! ## 定理四：相对位置 |·| 不变（核心定理）
|⟨R_m q, R_n k⟩| = |⟨q, k⟩|——相对位置只影响相位，**模长不变**
（注意力分数 |⟨q_m, k_n⟩| 在位置编码下稳定）。
由定理三：相位因子 |e^{iθ(n−m)}| = 1 消去。-/

theorem complex_rope_relative_abs (θ m n : ℝ) (q k : ℂ) :
    Complex.abs ⟪complexRotate θ m q, complexRotate θ n k⟫ = Complex.abs ⟪q, k⟫ := by
  rw [complex_rope_phase_shift]
  rw [AbsoluteValue.map_mul]
  rw [complex_phase_abs_one θ (n - m)]
  ring

/-! ## 推论：范数形式
‖R_m z‖ = ‖z‖（|·| 与 ‖·‖ 在 ℂ 上一致：`Complex.norm_eq_abs`；等距的范数层表述）。-/

theorem complex_rotation_preserves_norm (θ m : ℝ) (z : ℂ) :
    ‖complexRotate θ m z‖ = ‖z‖ := by
  rw [Complex.norm_eq_abs]
  exact complex_rotation_preserves_abs θ m z

end Lattice
