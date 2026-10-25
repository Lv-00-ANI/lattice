import Mathlib

/-!
# LATTICE: 验证器可靠性 —— 采样验证 + Lipschitz + δ-稠密 ⟹ 全域近似

提取调研（research/real-world/extraction-math.md 备选三）：
验证器不必检查定义域每个点——在 δ-稠密采样集上验证 + 两侧 Lipschitz，
即可推得全域 ε 近似：

  f、g 在 Ω 上分别 L/L'-Lipschitz
  S ⊂ Ω 是 δ-稠密（∀x∈Ω, ∃s∈S, |x−s|≤δ）
  S 上验证：∀s∈S, |f s − g s| ≤ ε₀
  ⟹ Ω 上：∀x∈Ω, |f x − g x| ≤ ε₀ + (L + L')·δ

证明：三角不等式（x → s → 采样差 → s → x 的路径分解）。

模型无关：任意函数、任意域、任意 Lipschitz 常数。
这是 ApproxOn（RealApprox）的采样版——提取候选的工程可验证路径。
-/

namespace Lattice

/-! ## Lipschitz（域上） -/

def LipschitzOn (f : ℝ → ℝ) (L : ℝ) (Ω : Set ℝ) : Prop :=
  ∀ x y : ℝ, x ∈ Ω → y ∈ Ω → |f x - f y| ≤ L * |x - y|

/-! ## δ-稠密采样集 -/

def DeltaDense (S : Set ℝ) (δ : ℝ) (Ω : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Ω → ∃ s : ℝ, s ∈ Ω ∧ s ∈ S ∧ |x - s| ≤ δ

/-! ## 采样验证 -/

def SampledVerified (f g : ℝ → ℝ) (ε₀ : ℝ) (S : Set ℝ) : Prop :=
  ∀ s : ℝ, s ∈ S → |f s - g s| ≤ ε₀

/-! ## 定理：验证器可靠性（干净版）
采样验证 + 双侧 Lipschitz（常数非负）+ δ-稠密 ⟹ 全域 ε₀+(L+L')δ 近似。-/

theorem verifier_reliable_clean (f g : ℝ → ℝ) (L L' ε₀ δ : ℝ) (Ω : Set ℝ) (S : Set ℝ)
    (hf : LipschitzOn f L Ω) (hg : LipschitzOn g L' Ω)
    (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hd : DeltaDense S δ Ω) (hv : SampledVerified f g ε₀ S) :
    ∀ x : ℝ, x ∈ Ω → |f x - g x| ≤ ε₀ + (L + L') * δ := by
  intro x hx
  rcases hd x hx with ⟨s, hsΩ, hsS, hxs⟩
  calc
    |f x - g x| = |(f x - f s) + (f s - g s) + (g s - g x)| := by
      have h : f x - g x = (f x - f s) + (f s - g s) + (g s - g x) := by ring
      rw [h]
    _ ≤ |f x - f s| + |(f s - g s) + (g s - g x)| := by
      rw [add_assoc]
      exact abs_add _ _
    _ ≤ |f x - f s| + (|f s - g s| + |g s - g x|) := by
      have hb : |(f s - g s) + (g s - g x)| ≤ |f s - g s| + |g s - g x| := abs_add _ _
      linarith
    _ ≤ L * |x - s| + (ε₀ + L' * |x - s|) := by
      have h1 : |f x - f s| ≤ L * |x - s| := hf x s hx hsΩ
      have h2 : |f s - g s| ≤ ε₀ := hv s hsS
      have h3 : |g s - g x| ≤ L' * |s - x| := hg s x hsΩ hx
      have h4 : |s - x| = |x - s| := by rw [abs_sub_comm]
      nlinarith
    _ = ε₀ + (L + L') * |x - s| := by ring
    _ ≤ ε₀ + (L + L') * δ := by
      -- |x-s| ≤ δ 且 (L+L') ≥ 0
      have hpos : 0 ≤ L + L' := by linarith
      exact add_le_add_left (mul_le_mul_of_nonneg_left hxs hpos) ε₀

/-! ## 推论：零误差 + 零稠密度下的退化情形
当 ε₀ = 0 且 δ = 0 时，采样验证 + δ-稠密退化为全域零误差（`verifier_error_vanishes`）。
这不是收敛率命题——`ε₀`、`δ` 在本文件中是自由参数，未证明它们可任意调小；
故此处不宣称「采样足够密时误差可控」，也不涉及一致连续性（本文件只有 `LipschitzOn`）。 -/

theorem verifier_error_vanishes (f g : ℝ → ℝ) (L L' ε₀ δ : ℝ) (Ω : Set ℝ) (S : Set ℝ)
    (hf : LipschitzOn f L Ω) (hg : LipschitzOn g L' Ω)
    (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hd : DeltaDense S δ Ω) (hv : SampledVerified f g ε₀ S)
    (hε : ε₀ = 0) (hδ : δ = 0) :
    ∀ x : ℝ, x ∈ Ω → |f x - g x| ≤ 0 := by
  intro x hx
  have hb := verifier_reliable_clean f g L L' ε₀ δ Ω S hf hg hL hL' hd hv x hx
  rw [hε, hδ] at hb
  simpa using hb

end Lattice