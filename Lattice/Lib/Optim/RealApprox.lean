import Mathlib

/-!
# LATTICE: 近似等价与误差界 —— 浮点/扰动 ⟷ ℝ 语义的桥

doc/02 §10「离散-连续桥：行为等价的判定标准（带误差界近似）」的落地：

  1. Approx：函数在 ε 内近似等价（|f x - g x| ≤ ε，逐点）；
  2. 线性层权重扰动误差界：权重/偏置扰动 ε₁/ε₂ 且输入有界 X，
     输出误差 ≤ ε₁·X + ε₂（数值稳定性的最小证明）；
  3. 近似传递性；
  4. 应用：浮点舍入权重（|w' - w| ≤ δ）→ 输出误差有界 → 验证器容差判定。

这是 WeightToSymbolEquivalence（提取方向）的误差界扩展：
  提取候选若与原权重在 ε 内近似等价，则可作为近似可用的符号表示。
-/

namespace Lattice

/-! ## 近似等价（全局）：|f x - g x| ≤ ε -/

def Approx (f g : ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ x : ℝ, |f x - g x| ≤ ε

/-! ## 受限域近似：输入有界 |x| ≤ X 时近似 -/

def ApproxOn (f g : ℝ → ℝ) (X ε : ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ X → |f x - g x| ≤ ε

/-! ## 定理一：近似传递性
f ≈ g (ε₁) 且 g ≈ h (ε₂) ⟹ f ≈ h (ε₁ + ε₂)（三角不等式）。-/

theorem approx_trans {f g h : ℝ → ℝ} {ε₁ ε₂ : ℝ} (h1 : Approx f g ε₁) (h2 : Approx g h ε₂) :
    Approx f h (ε₁ + ε₂) := by
  intro x
  calc
    |f x - h x| = |(f x - g x) + (g x - h x)| := by
      have h : f x - h x = (f x - g x) + (g x - h x) := by ring
      rw [h]
    _ ≤ |f x - g x| + |g x - h x| := abs_add _ _
    _ ≤ ε₁ + ε₂ := by
      exact add_le_add (h1 x) (h2 x)

/-! ## 定理二：线性层权重扰动误差界
输出 = a·x + b；权重扰动 a→a'、b→b'（|a'-a|≤ε₁、|b'-b|≤ε₂），
输入有界 |x| ≤ X ⟹ 输出误差 ≤ ε₁·X + ε₂。-/

theorem layer_out_error_bound (x a b a' b' X ε₁ ε₂ : ℝ)
    (hx : |x| ≤ X) (ha : |a' - a| ≤ ε₁) (hb : |b' - b| ≤ ε₂) :
    |(a' * x + b') - (a * x + b)| ≤ ε₁ * X + ε₂ := by
  -- 拆解：(a'x + b') - (ax + b) = (a'-a)x + (b'-b)
  calc
    |(a' * x + b') - (a * x + b)| = |(a' - a) * x + (b' - b)| := by
      have h : (a' * x + b') - (a * x + b) = (a' - a) * x + (b' - b) := by ring
      rw [h]
    _ ≤ |(a' - a) * x| + |b' - b| := abs_add _ _
    _ ≤ ε₁ * X + ε₂ := by
      -- |(a'-a)*x| = |a'-a|·|x| ≤ ε₁·X
      have hprod : |(a' - a) * x| ≤ ε₁ * X := by
        calc
          |(a' - a) * x| = |a' - a| * |x| := by rw [abs_mul]
          _ ≤ ε₁ * X := by
            exact mul_le_mul ha hx (abs_nonneg x) (le_trans (abs_nonneg (a' - a)) ha)
      exact add_le_add hprod hb

/-! ## 定理三：系数扰动 → 受限域函数近似
权重扰动界的函数形式：linear(a',b') ≈ linear(a,b)（在输入域 |x|≤X 内，误差 ≤ ε₁X+ε₂）。-/

theorem layer_approx_on (a b a' b' X ε₁ ε₂ : ℝ)
    (ha : |a' - a| ≤ ε₁) (hb : |b' - b| ≤ ε₂) :
    ApproxOn (fun x => a' * x + b') (fun x => a * x + b) X (ε₁ * X + ε₂) := by
  intro x hx
  exact layer_out_error_bound x a b a' b' X ε₁ ε₂ hx ha hb

/-! ## 定理四：零损失判定在近似下的容差
若提取候选 c' 与原约束 c 的权重扰动有界，则：
  原约束满足 ⟹ 候选的平方损失 ≤ (ε₁X+ε₂)²（可容忍的残余损失）。-/

theorem loss_tolerance_under_perturbation (x a b a' b' X ε₁ ε₂ : ℝ)
    (hx : |x| ≤ X) (ha : |a' - a| ≤ ε₁) (hb : |b' - b| ≤ ε₂)
    (hsat : a * x + b = 0) :
    (a' * x + b') ^ 2 ≤ (ε₁ * X + ε₂) ^ 2 := by
  -- 输出误差 ≤ ε₁X+ε₂，且原输出 = 0 → 新输出误差即 |新输出|
  have herr : |(a' * x + b') - (a * x + b)| ≤ ε₁ * X + ε₂ :=
    layer_out_error_bound x a b a' b' X ε₁ ε₂ hx ha hb
  have hzero : (a' * x + b') - 0 = a' * x + b' := by ring
  have hne : |a' * x + b'| ≤ ε₁ * X + ε₂ := by
    simpa [hsat] using herr
  -- |y| ≤ M → y² ≤ M²（M = ε₁X+ε₂ ≥ 0）
  have hnonneg : 0 ≤ ε₁ * X + ε₂ := by
    have hε₁ : 0 ≤ ε₁ := le_trans (abs_nonneg (a' - a)) ha
    have hε₂ : 0 ≤ ε₂ := le_trans (abs_nonneg (b' - b)) hb
    have hX : 0 ≤ X := le_trans (abs_nonneg x) hx
    nlinarith
  have hneAbs : |a' * x + b'| ≤ |ε₁ * X + ε₂| := by
    rw [abs_of_nonneg hnonneg]
    exact hne
  exact sq_le_sq.mpr hneAbs

/-! ## 定理五：★ **受限域近似的传代（`ApproxOn` 三角不等式）**
`approx_trans`（定理一）只覆盖**全域** `Approx`；而下游真正使用的是**受限域** `ApproxOn`
（`RealNonlinearCompile.nonlinear_soundness_local` 等）。**历史沿革**：在本文件加入 `approxOn_trans`
之前，全库检索（grep）该结论命中数为 0，即「受限域近似不可传代」曾是**真空缺口**；
本文件已补上此缺口，故该命中数=0 的盘点仅描述加入前的状态。下面即该补充。

注意 关键点：`ApproxOn` 的传代**不需要** `X` 相同，但两步的有效域必须**同时满足**。
故正确陈述是「在 `|x| ≤ min X₁ X₂` 上」，而非某一个单独的 `X`。
这也是下一条（定理六）的动机。 -/

theorem approxOn_trans {f g h : ℝ → ℝ} {X₁ X₂ ε₁ ε₂ : ℝ}
    (h1 : ApproxOn f g X₁ ε₁) (h2 : ApproxOn g h X₂ ε₂) :
    ApproxOn f h (min X₁ X₂) (ε₁ + ε₂) := by
  intro x hx
  have hx₁ : |x| ≤ X₁ := le_trans hx (min_le_left _ _)
  have hx₂ : |x| ≤ X₂ := le_trans hx (min_le_right _ _)
  calc
    |f x - h x| = |(f x - g x) + (g x - h x)| := by
      have h : f x - h x = (f x - g x) + (g x - h x) := by ring
      rw [h]
    _ ≤ |f x - g x| + |g x - h x| := abs_add _ _
    _ ≤ ε₁ + ε₂ := add_le_add (h1 x hx₁) (h2 x hx₂)

/-! ## 定理六：**同域受限近似传代**（定理五的常用特例）
当两步共用同一个界 `X` 时，`min X X = X`，结论回到形式最简的 `ApproxOn f h X (ε₁+ε₂)`。
要点 这条才是下游可直接接线的那一条（调用方不需要知道 `min`）。 -/

theorem approxOn_trans_same {f g h : ℝ → ℝ} {X ε₁ ε₂ : ℝ}
    (h1 : ApproxOn f g X ε₁) (h2 : ApproxOn g h X ε₂) :
    ApproxOn f h X (ε₁ + ε₂) := by
  simpa using approxOn_trans (X₁ := X) (X₂ := X) h1 h2

/-! ## 定理七：**全域近似退化为受限域近似**（两侧的桥）
`Approx` 与 `ApproxOn` 之间此前没有任何定理桥接（grep：`approx_to_approxOn` = 0）。
若 `Approx f g ε`，则在**任何**界 `X` 下也成立，**无需** `X` 的任何假设
（包括 `X < 0`，此时该事实是空真的）。这把定理一的结论可直接喂给下游 `ApproxOn` 消费者。 -/

theorem approx_to_approxOn {f g : ℝ → ℝ} {ε X : ℝ}
    (h : Approx f g ε) : ApproxOn f g X ε := by
  intro x _
  exact h x

/-! ## 定理八：**受限域近似限制到更小域**（域单调）
若在 `|x| ≤ X` 上近似成立，则在任何更小的域 `|x| ≤ Y`（`Y ≤ X`）上也成立。
这是传代在**域方向**的对偶，也是唯一不需要三角不等式的一条。 -/

theorem approxOn_mono_domain {f g : ℝ → ℝ} {X Y ε : ℝ}
    (h : ApproxOn f g X ε) (hYX : Y ≤ X) : ApproxOn f g Y ε := by
  intro x hx
  exact h x (le_trans hx hYX)

end Lattice

/-! ## Axiom probe (per-declaration #print axioms; sorryAx must NOT appear)

Every theorem in this module, probed one by one. Expected: [propext, Classical.choice, Quot.sound]
(or a subset). sorryAx must NOT appear.
NOTE: decide can silently introduce sorryAx, so a successful compile alone is NOT sufficient.
-/
#print axioms Lattice.approx_trans
#print axioms Lattice.layer_out_error_bound
#print axioms Lattice.layer_approx_on
#print axioms Lattice.loss_tolerance_under_perturbation
#print axioms Lattice.approxOn_trans
#print axioms Lattice.approxOn_trans_same
#print axioms Lattice.approx_to_approxOn
#print axioms Lattice.approxOn_mono_domain
