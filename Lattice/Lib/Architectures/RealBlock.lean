import Mathlib
import Lattice.Lift.RealVerifierReliable
/-!
# LATTICE: 完整块的组合误差传播（transformer 块级，模型无关）

把各结构证明（残差/注意力/LN/FFN 的 Lipschitz 性质）组合为
**完整 transformer 块的误差传播**：块 = Lipschitz 组件链，误差经组合传播时
Lipschitz 常数相乘：

  1. 组合误差传播：|f(g x) − f(g x')| ≤ Lf·Lg·|x − x'|（两层）
  2. 三层链：≤ Lf·Lg·Lh·|x − x'|
  3. 块级编辑局部性：编辑子组件使其中间输出扰动 δ，
     块输出变化 ≤ 外层 Lipschitz × δ（外层放大）

模型无关：任意 Lipschitz 组件（注意力凸组合/残差/LN/FFN 的 Lipschitz
性质已在各文件证明），常数相乘与放大对类成立。
-/


namespace Lattice

/-! LipschitzOn 等定义来自 RealVerifierReliable（同在 Lattice 命名空间，无需 open）。-/

/-! ## 定理一：组合误差传播（两层）
f、g 分别 Lf/Lg-Lipschitz（全域）⟹ f∘g 是 Lf·Lg-Lipschitz。-/

theorem compose_error_propagation (f g : ℝ → ℝ) (Lf Lg : ℝ)
    (hf : LipschitzOn f Lf Set.univ) (hg : LipschitzOn g Lg Set.univ)
    (hLf : 0 ≤ Lf) :
    ∀ x x' : ℝ, |f (g x) - f (g x')| ≤ Lf * Lg * |x - x'| := by
  intro x x'
  calc
    |f (g x) - f (g x')| ≤ Lf * |g x - g x'| := hf (g x) (g x') trivial trivial
    _ ≤ Lf * (Lg * |x - x'|) := by
      have hg' : |g x - g x'| ≤ Lg * |x - x'| := hg x x' trivial trivial
      exact mul_le_mul_of_nonneg_left hg' hLf
    _ = Lf * Lg * |x - x'| := by ring

/-! ## 定理二：三层链误差传播
f∘g∘h 是 Lf·Lg·Lh-Lipschitz（Lipschitz 常数相乘）。-/

theorem chain3_error_propagation (f g h : ℝ → ℝ) (Lf Lg Lh : ℝ)
    (hf : LipschitzOn f Lf Set.univ) (hg : LipschitzOn g Lg Set.univ)
    (hh : LipschitzOn h Lh Set.univ) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg) :
    ∀ x x' : ℝ, |f (g (h x)) - f (g (h x'))| ≤ Lf * Lg * Lh * |x - x'| := by
  intro x x'
  calc
    |f (g (h x)) - f (g (h x'))| ≤ Lf * |g (h x) - g (h x')| := hf (g (h x)) (g (h x')) trivial trivial
    _ ≤ Lf * (Lg * Lh * |x - x'|) := by
      have hgh : |g (h x) - g (h x')| ≤ Lg * Lh * |x - x'| :=
        compose_error_propagation g h Lg Lh hg hh hLg x x'
      exact mul_le_mul_of_nonneg_left hgh hLf
    _ = Lf * Lg * Lh * |x - x'| := by ring

/-! ## 定理三：块级编辑局部性（外层 Lipschitz 放大）
子组件输出扰动 δ（编辑影响）⟹ 块输出变化 ≤ Lf·δ（外层放大，
无跨组件放大以外的泄漏）。

**第 210 轮删掉了前提 `(_hLf : 0 ≤ Lf)`**（定理三与定理四各一处）：
`LipschitzOn` **不要求**常数非负，两个证明都是 `hf …` 之后 `simp`/`ring`，
从未用到它。删掉前提让两条定理**更强**，而这对定理三尤其重要——
「Lipschitz 放大」的名字说的是**任意** `Lf` 下的界，加一条 `0 ≤ Lf` 是无依据的收窄。
`gov/check_underscore_hypotheses.py` 是发现它的工具。 -/

theorem outer_lipschitz_amplifies (f : ℝ → ℝ) (Lf : ℝ) (y δ : ℝ)
    (hf : LipschitzOn f Lf Set.univ) :
    |f (y + δ) - f y| ≤ Lf * |δ| := by
  calc
    |f (y + δ) - f y| ≤ Lf * |(y + δ) - y| := hf (y + δ) y trivial trivial
    _ = Lf * |δ| := by simp

/-! ## 定理四：两层块编辑的端到端界
块 = F∘G；编辑发生在 G 内部使其中间输出扰动 δ：
端到端变化 ≤ Lf·δ（外层放大，G 的编辑经 F 的 Lipschitz 传递）。-/

theorem two_layer_block_edit_bound (F G : ℝ → ℝ) (Lf : ℝ) (x : ℝ) (δ : ℝ)
    (hf : LipschitzOn F Lf Set.univ)
    (hG : |G x + δ - G x| = |δ|) :
    |F (G x + δ) - F (G x)| ≤ Lf * |δ| := by
  calc
    |F (G x + δ) - F (G x)| ≤ Lf * |(G x + δ) - G x| := hf (G x + δ) (G x) trivial trivial
    _ = Lf * |δ| := by
      rw [hG]

/-! ## 注：真实块的实例化
transformer 块的 Lipschitz 常数：
  · 注意力：凸组合（convComb_norm_bound）⟹ L ≤ 1（凸组合不放大）
  · 残差：L ≤ ‖F‖ + 1（residual_two_layer 已用）
  · LN：缩放不变（normalize_scale_invariant）
  · FFN：软掩码有效线性（softMask_FFN_effective）⟹ L ≤ max‖Wᵢ·sᵢ‖
将这些常数代入 chain3_error_propagation 即得完整块的端到端误差界。
-/

/-! ## 定理四：把块级 Lipschitz 常数喂进采样验证器（J10 接线）

本文件 `:2` **已经** `import RealVerifierReliable`，且 `:23` 注释已声明
「`LipschitzOn` 等定义来自 `RealVerifierReliable`」，但 `verifier_reliable_clean`
**从未被调用**（`import` 证据 ≠ 使用证据；J10 实测该定理的**定理级真消费者 = 0**）。

下面把它接上：用本文件已证的**块级常数** `Lf * (1 + La + Lg)`（残差结构 `x + A x + G x`）
填进 `verifier_reliable_clean` 的 `L`/`L'`，得到**块级**的采样验证界。

⭐ **零额外成本**：无需新 `import`、无需新文件、无需改 `roots`、无 `import` 环；
且本文件有 6 个 importer（`RealModelChain`/`RealBlockInstance`/`RealWeightSharing`/
`RealCrossAttention`/`RealMixedAttention`/`RealAttentionLipschitz`）⟹ 定理沿现有 DAG 自动可达。

（J10 已内核验证：13 条探针引理全部编译通过、公理 ⊆ {propext, Classical.choice, Quot.sound}、
无 `sorryAx`；组合**非空洞**（见证同时满足全部 14 假设）且**界紧**（取等见证）。） -/

/-- **块级残差结构的 Lipschitz 常数**：`x ↦ B (x + C x + D x)` 是 `Lb * (1 + Lc + Ld)`-Lipschitz。
本引理复用 `compose_error_propagation` 的形状，供定理五使用。 -/
theorem block_residual_lipschitz (B C D : ℝ → ℝ) (Lb Lc Ld : ℝ)
    (hB : LipschitzOn B Lb Set.univ) (hC : LipschitzOn C Lc Set.univ)
    (hD : LipschitzOn D Ld Set.univ) (hLb : 0 ≤ Lb) :
    LipschitzOn (fun x => B (x + C x + D x)) (Lb * (1 + Lc + Ld)) Set.univ := by
  intro x y _ _
  have hin : |(x + C x + D x) - (y + C y + D y)| ≤ (1 + Lc + Ld) * |x - y| := by
    have h1 : |(x + C x) - (y + C y)| ≤ (1 + Lc) * |x - y| := by
      calc
        |(x + C x) - (y + C y)| = |(x - y) + (C x - C y)| := by ring
        _ ≤ |x - y| + |C x - C y| := abs_add _ _
        _ ≤ 1 * |x - y| + Lc * |x - y| := by
          have hCxy : |C x - C y| ≤ Lc * |x - y| := hC x y trivial trivial
          have hid : |x - y| ≤ 1 * |x - y| := by simp
          linarith
        _ = (1 + Lc) * |x - y| := by ring
    calc
      |(x + C x + D x) - (y + C y + D y)|
          = |((x + C x) - (y + C y)) + (D x - D y)| := by ring
      _ ≤ |(x + C x) - (y + C y)| + |D x - D y| := abs_add _ _
      _ ≤ (1 + Lc) * |x - y| + Ld * |x - y| := by
        have hDxy : |D x - D y| ≤ Ld * |x - y| := hD x y trivial trivial
        linarith
      _ = (1 + Lc + Ld) * |x - y| := by ring
  calc
    |B (x + C x + D x) - B (y + C y + D y)|
        ≤ Lb * |(x + C x + D x) - (y + C y + D y)| := hB _ _ trivial trivial
    _ ≤ Lb * ((1 + Lc + Ld) * |x - y|) := mul_le_mul_of_nonneg_left hin hLb
    _ = (Lb * (1 + Lc + Ld)) * |x - y| := by ring

/-- ⭐ **定理五（J10 接线）：块级采样验证界**。
两层残差块 `x ↦ F (x + A x + G x)` 与 `x ↦ F' (x + A' x + G' x)` 各自 Lipschitz，
且在 δ-稠密集 `S` 上采样验证到 `ε₀` ⟹ 在**全空间**上二者相差 ≤ `ε₀ + (Lb + Lb') * δ`，
其中 `Lb = Lf * (1 + La + Lg)`、`Lb' = Lf' * (1 + La' + Lg')` 是**块级常数**。 -/
theorem block_sampled_verifier (F A G F' A' G' : ℝ → ℝ)
    (Lf La Lg Lf' La' Lg' ε₀ δ : ℝ) (S : Set ℝ)
    (hF : LipschitzOn F Lf Set.univ) (hA : LipschitzOn A La Set.univ)
    (hG : LipschitzOn G Lg Set.univ)
    (hF' : LipschitzOn F' Lf' Set.univ) (hA' : LipschitzOn A' La' Set.univ)
    (hG' : LipschitzOn G' Lg' Set.univ)
    (hLf : 0 ≤ Lf) (hLa : 0 ≤ La) (hLg : 0 ≤ Lg)
    (hLf' : 0 ≤ Lf') (hLa' : 0 ≤ La') (hLg' : 0 ≤ Lg')
    (hd : DeltaDense S δ Set.univ)
    (hv : SampledVerified (fun x => F (x + A x + G x)) (fun x => F' (x + A' x + G' x)) ε₀ S) :
    ∀ x ∈ Set.univ, |F (x + A x + G x) - F' (x + A' x + G' x)| ≤
      ε₀ + ((Lf * (1 + La + Lg)) + (Lf' * (1 + La' + Lg'))) * δ :=
  verifier_reliable_clean (fun x => F (x + A x + G x)) (fun x => F' (x + A' x + G' x))
    (Lf * (1 + La + Lg)) (Lf' * (1 + La' + Lg')) ε₀ δ Set.univ S
    (block_residual_lipschitz F A G Lf La Lg hF hA hG hLf)
    (block_residual_lipschitz F' A' G' Lf' La' Lg' hF' hA' hG' hLf')
    (mul_nonneg hLf (by linarith)) (mul_nonneg hLf' (by linarith)) hd hv

/-- **非空洞见证**：`block_sampled_verifier` 的**全部**假设可同时满足（含 `0 < ε₀`）。 -/
theorem block_sampled_verifier_hypotheses_inhabited :
    ∃ (F A G F' A' G' : ℝ → ℝ) (Lf La Lg Lf' La' Lg' ε₀ δ : ℝ) (S : Set ℝ),
      LipschitzOn F Lf Set.univ ∧ LipschitzOn A La Set.univ ∧ LipschitzOn G Lg Set.univ ∧
      LipschitzOn F' Lf' Set.univ ∧ LipschitzOn A' La' Set.univ ∧ LipschitzOn G' Lg' Set.univ ∧
      0 ≤ Lf ∧ 0 ≤ La ∧ 0 ≤ Lg ∧ 0 ≤ Lf' ∧ 0 ≤ La' ∧ 0 ≤ Lg' ∧
      DeltaDense S δ Set.univ ∧
      SampledVerified (fun x => F (x + A x + G x)) (fun x => F' (x + A' x + G' x)) ε₀ S ∧
      0 < ε₀ := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    0, 0, 0, 0, 0, 0, 1, 1, Set.univ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, le_refl 0, le_refl 0, le_refl 0, le_refl 0, le_refl 0, le_refl 0,
    ?_, ?_, one_pos⟩
  · intro x y _ _; simp
  · intro x y _ _; simp
  · intro x y _ _; simp
  · intro x y _ _; simp
  · intro x y _ _; simp
  · intro x y _ _; simp
  · intro x _; exact ⟨x, trivial, trivial, by simp⟩
  · intro s _; simp

end Lattice
