import Mathlib
import Lattice.Lift.RealLinear
/-!
# LATTICE: IG 完备性（线性版）—— 差异分解恒等式

提取调研（research/real-world/extraction-math.md §3 性质二）的线性版：
Integrated Gradients 的完备性恒等式（路径积分分解行为差异）在**仿射函数**
（梯度常数）下退化为纯代数差：

  Σᵢ (xᵢ − x'ᵢ)·∫₀¹ ∂ᵢF(γ(t)) dt = F(x) − F(x')   （一般形式）

仿射 F(z) = a·z + b：∂ᵢF = aᵢ（常数），∫₀¹ aᵢ dt = aᵢ，
⟹ Σᵢ (xᵢ−x'ᵢ)·aᵢ = a·(x−x') = F(x) − F(x')。

这给出自编译线性子类的**精确定位记账**：行为差异恰被逐输入特征
的贡献之和（权重·位移）完整分解，无遗漏无重复。
-/


namespace Lattice

/-! ## 仿射函数 -/

def Affine {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ℝ) (x : ι → ℝ) : ℝ :=
  RealDot a x + b

/-! ## 引理：点积线性性（差）
RealDot a (x - x') = RealDot a x - RealDot a x'。-/

lemma RealDot_sub {ι : Type*} [Fintype ι] (a x x' : ι → ℝ) : RealDot a (x - x') = RealDot a x - RealDot a x' := by
  unfold RealDot
  -- Σ aᵢ(xᵢ - x'ᵢ) = Σ aᵢxᵢ - Σ aᵢx'ᵢ
  calc
    ∑ i, a i * (x i - x' i) = ∑ i, (a i * x i - a i * x' i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, a i * x i) - (∑ i, a i * x' i) := by
      rw [Finset.sum_sub_distrib]

/-! ## 定理：IG 完备性（线性版）
仿射函数的差异 = 权重·位移（梯度常数时路径积分的精确记账）。-/

theorem IG_linear_completeness {ι : Type*} [Fintype ι] (a x x' : ι → ℝ) (b : ℝ) :
    Affine a b x - Affine a b x' = RealDot a (x - x') := by
  unfold Affine
  rw [RealDot_sub]
  ring

/-! ## 推论一：逐特征贡献分解
行为差异 = 各输入特征的贡献之和（IG 分配记账的线性形态）。-/

theorem IG_feature_decomposition {ι : Type*} [Fintype ι] (a x x' : ι → ℝ) (b : ℝ) :
    Affine a b x - Affine a b x' = ∑ i, a i * (x i - x' i) := by
  rw [IG_linear_completeness]
  rfl

/-! ## 推论二：单特征扰动归因
只扰动第 i 个特征（x' = x 除 i 外相同）时，差异恰为该特征贡献 aᵢ·Δᵢ。
-/

theorem IG_single_feature {ι : Type*} [Fintype ι] [DecidableEq ι] (a x : ι → ℝ) (b : ℝ) (i : ι) (δ : ℝ)
    (x' : ι → ℝ) (hx' : x' = Function.update x i (x i - δ)) :
    Affine a b x - Affine a b x' = a i * δ := by
  -- 用完备性 + update 展开
  rw [IG_linear_completeness]
  unfold RealDot
  -- Σ aⱼ(xⱼ - x'ⱼ)：仅 j=i 项非零（= aᵢ·δ）
  rw [hx']
  have hupdate : ∀ j : ι, j ≠ i → (Function.update x i (x i - δ)) j = x j := by
    intro j hj
    exact Function.update_noteq hj _ _
  -- 逐项化简：j ≠ i 时差为 0；j = i 时差 = aᵢ·δ
  calc
    ∑ j, a j * (x j - (Function.update x i (x i - δ)) j) =
        ∑ j, a j * (if j = i then δ else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i
          · -- j = i：xᵢ - (xᵢ - δ) = δ
            subst hji
            rw [Function.update_same, if_pos rfl]
            ring
          · -- j ≠ i：xⱼ - xⱼ = 0
            rw [hupdate j hji, if_neg hji]
            ring
    _ = a i * δ := by
      -- ∑ aⱼ·(if j=i then δ else 0) = aᵢ·δ（单点求和）
      calc
        ∑ j, a j * (if j = i then δ else 0)
            = ∑ j, (if j = i then a i * δ else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hji : j = i
              · subst hji
                simp
              · simp [hji]
        _ = a i * δ := by
              rw [Finset.sum_ite_eq']
              simp

end Lattice
