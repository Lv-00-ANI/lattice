import Mathlib
import Lattice.Lib.Convex.RealKKT
import Lattice.Lib.Lift.RealWeightedConstraints
/-!
# LATTICE: 拉格朗日对偶理论 —— 弱对偶、对偶凹性与零间隙（互补松弛）

RealKKT 用**增广拉格朗日**（`L_aug = (ax−b)² + λ(ax−b)`）刻画等式约束的驻点，
实为「惩罚 + 乘子」的混合形态。本文件把乘子视角补回**经典拉格朗日对偶**：

    有限不等式约束 g_i(x) ≤ 0（i : Fin n），f 为目标，λ ≥ 0 为乘子，
        L(x, λ) = f(x) + Σ_i λ_i·g_i(x)。

定理清单：
  1. `Lagrangian`（def）：有限约束的拉格朗日函数；
  2. `lagrangian_lower_bound`（**核心，弱对偶的逐点形式**）：λ ≥ 0 且 x 可行
     （∀i, g_i(x) ≤ 0）⟹ L(x, λ) ≤ f(x)。（每项 λ_i·g_i(x) ≤ 0，求和 ≤ 0。）
  3. `lagrangian_affine`：固定 x 时 λ ↦ L(x, λ) 是**仿射**的：
        L(x, aλ + bμ) = a·L(x,λ) + b·L(x,μ)（a + b = 1）；
     由此 `lagrangian_concave_in_lam`：λ ↦ L(x, λ) 凹（对任意 x）。
  4. `dualValue`（def）：**有限支撑对偶**——在有限候选点集 s 上取 inf（s 有限 ⟹ inf 可达，
     避开 ℝ 上 `iInf` 对无下界集合的约定值问题）；
  5. `dual_concave`：s 非空 ⟹ λ ↦ dualValue(λ) 是凹函数（`ConcaveOn ℝ Set.univ`）。
     证明：inf 在 x₀ ∈ s 处达到，逐点用 3 的仿射性 + 两个 inf 下界。
  6. `weak_duality`（**核心**）：λ ≥ 0 ⟹ ⨅_x L(x,λ) ≤ f(x) 对任意可行 x 成立
     （需 `BddBelow` 使 ⨅ 为真实下确界——ℝ 上无下界时 `iInf` 取约定值 0，故必须显式假设）；
     `weak_duality_finset`：有限支撑版的弱对偶（无需下有界性）。
  7. `strong_duality_convex_case`（**凸情形强对偶的零间隙判据**）：若 λ ≥ 0、x 可行，
     且**对偶间隙为零**（f(x) ≤ ⨅_x' L(x',λ)），则
        ∀i, λ_i·g_i(x) = 0（**互补松弛**）且 L(x,λ) = f(x)。
  8. `complementary_slackness_of_zero_gap`：7 的互补松弛部分单独列出。

诚实边界：
  · **强对偶本身（凸 + Slater ⟹ 零间隙）未证明**：需要下半连续凸函数的次梯度/分离定理
    （mathlib 4.14 无 `Convex.subderiv`，见 RealSubgradient），本文件把「零间隙」作为
    **假设**（`hgap`）而不是结论——这正是 `strong_duality_convex_case` 名字中
    "convex case" 的含义：判据成立，Slater 条件的充分性标注为后续工作。
  · 对偶函数用**有限支撑** `Finset.inf'` 定义（避免 ℝ 上 `iInf` 的约定值陷阱）；
    全空间版 `weak_duality` 用 `⨅` + `BddBelow` 显式假设。
  · 不等式约束严格按 `g_i(x) ≤ 0`（mathlib 惯例），乘子 λ ≥ 0。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## 一、拉格朗日函数 -/

/-- **拉格朗日函数**（有限不等式约束）：L(x, λ) = f(x) + Σ_i λ_i·g_i(x)。 -/
def Lagrangian (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ) : ℝ :=
  f x + ∑ i, lam i * g i x

/-- **有限支撑对偶值**：在有限候选点集 s 上取 inf（s 非空 ⟹ inf 可达，`Finset.inf'`）。
这是「inf_x L(x,λ)」在有限点集上的可实现版本，避免 ℝ 上 `iInf` 对无下界集合的约定值。 -/
def dualValue (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (s : Finset ℝ) (hs : s.Nonempty)
    (lam : Fin n → ℝ) : ℝ :=
  s.inf' hs (fun x => Lagrangian f g x lam)

/-! ## 二、弱对偶的逐点形式 -/

/-- **核心引理（弱对偶逐点形式）**：λ ≥ 0、x 可行（∀i, g_i(x) ≤ 0）⟹ L(x, λ) ≤ f(x)。
每项 λ_i·g_i(x) ≤ 0，故 Σ ≤ 0。 -/
theorem lagrangian_lower_bound (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0) :
    Lagrangian f g x lam ≤ f x := by
  have hsum : ∑ i, lam i * g i x ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeas i)
  unfold Lagrangian
  linarith

/-- 等价形式：可行点处拉格朗日值不超过目标值（`lagrangian_lower_bound` 的重述）。 -/
theorem lagrangian_feasible_le (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0) :
    Lagrangian f g x lam - f x ≤ 0 := by
  have := lagrangian_lower_bound f g x lam hlam hfeas
  linarith

/-! ## 三、L(x, ·) 关于乘子仿射（对偶凹性的逐点来源） -/

/-- **仿射性**：a + b = 1 ⟹ L(x, aλ + bμ) = a·L(x,λ) + b·L(x,μ)。
（对 λ 的依赖是线性的，故仿射；取 a, b ≥ 0 即得凹性。） -/
theorem lagrangian_affine (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (a b : ℝ) (hab : a + b = 1)
    (lam mu : Fin n → ℝ) :
    Lagrangian f g x (a • lam + b • mu) = a * Lagrangian f g x lam + b * Lagrangian f g x mu := by
  simp only [Lagrangian, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i, (a * lam i + b * mu i) * g i x)
      = a * (∑ i, lam i * g i x) + b * (∑ i, mu i * g i x) := by
    simp only [add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  -- linarith/nlinarith 不会自动用 `hab : a + b = 1` 归一化 `f x * a + f x * b`，
  -- 故先显式提出公因子。
  have hfab : f x * a + f x * b = f x := by rw [← mul_add, hab, mul_one]
  ring_nf
  linarith [hfab]

/-- **逐点凹性**：固定 x 时 λ ↦ L(x, λ) 凹（仿射的特例，a, b ≥ 0、a + b = 1）。 -/
theorem lagrangian_concave_in_lam (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ)
    (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = 1) (lam mu : Fin n → ℝ) :
    a * Lagrangian f g x lam + b * Lagrangian f g x mu ≤ Lagrangian f g x (a • lam + b • mu) := by
  rw [lagrangian_affine f g x a b hab lam mu]

/-! ## 四、有限支撑对偶函数的凹性 -/

/-- **对偶函数是凹函数**（有限支撑版）：s 非空 ⟹ λ ↦ dualValue(λ) 凹。
证明：inf 于 x₀ ∈ s 处达到；对 λ、μ 的凸组合，用 L 的仿射性与两个 inf 下界即可。 -/
theorem dual_concave (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (s : Finset ℝ) (hs : s.Nonempty) :
    ConcaveOn ℝ Set.univ (fun lam : Fin n → ℝ => dualValue f g s hs lam) := by
  refine ⟨convex_univ, ?_⟩
  intro lam _ mu _ a b ha hb hab
  simp only [smul_eq_mul]
  obtain ⟨x0, hx0s, hx0⟩ :=
    Finset.exists_mem_eq_inf' hs (fun x => Lagrangian f g x (a • lam + b • mu))
  have hR : dualValue f g s hs (a • lam + b • mu) = Lagrangian f g x0 (a • lam + b • mu) := by
    simp only [dualValue]
    exact hx0
  rw [hR, lagrangian_affine f g x0 a b hab lam mu]
  have h1 : dualValue f g s hs lam ≤ Lagrangian f g x0 lam := by
    simp only [dualValue]
    exact Finset.inf'_le (s := s) (fun x => Lagrangian f g x lam) hx0s
  have h2 : dualValue f g s hs mu ≤ Lagrangian f g x0 mu := by
    simp only [dualValue]
    exact Finset.inf'_le (s := s) (fun x => Lagrangian f g x mu) hx0s
  have e1 := mul_le_mul_of_nonneg_left h1 ha
  have e2 := mul_le_mul_of_nonneg_left h2 hb
  linarith

/-! ## 五、弱对偶 -/

/-- **弱对偶（核心）**：λ ≥ 0 ⟹ inf_x L(x, λ) ≤ f(x) 对任意可行 x 成立。
`BddBelow` 是把 `⨅_x` 当作真实下确界的必要假设（ℝ 上无下界时 `iInf` 取约定值 0）。 -/
theorem weak_duality (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hbdd : BddBelow (Set.range (fun x' : ℝ => Lagrangian f g x' lam))) :
    (⨅ x' : ℝ, Lagrangian f g x' lam) ≤ f x :=
  le_trans (ciInf_le hbdd x) (lagrangian_lower_bound f g x lam hlam hfeas)

/-- **弱对偶（有限支撑版）**：x 是候选点集 s 中的可行点 ⟹ dualValue(λ) ≤ f(x)
（无需下有界性，因为有限 inf 总是可达）。 -/
theorem weak_duality_finset (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (s : Finset ℝ) (hs : s.Nonempty)
    (x : ℝ) (hxs : x ∈ s) (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hfeas : ∀ i, g i x ≤ 0) : dualValue f g s hs lam ≤ f x := by
  refine le_trans ?_ (lagrangian_lower_bound f g x lam hlam hfeas)
  simp only [dualValue]
  exact Finset.inf'_le (s := s) (fun x' => Lagrangian f g x' lam) hxs

/-! ## 六、凸情形强对偶：零间隙 ⟹ 互补松弛 -/

/-- **强对偶（凸情形，零间隙判据）**：λ ≥ 0、x 可行，且对偶间隙为零
（f(x) ≤ inf_x' L(x',λ)）⟹ ∀i, λ_i·g_i(x) = 0（互补松弛）且 L(x,λ) = f(x)。

证明：弱对偶给出 L(x,λ) ≤ f(x) ≤ ⨅ L ≤ L(x,λ)，故全部取等；
此时 Σ λ_i g_i(x) = 0，而每一项 ≤ 0，故每项为 0。
"凸 + Slater ⟹ 零间隙" 的充分性（需分离定理/次梯度）标注为后续工作。 -/
theorem strong_duality_convex_case (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hbdd : BddBelow (Set.range (fun x' : ℝ => Lagrangian f g x' lam)))
    (hgap : f x ≤ ⨅ x' : ℝ, Lagrangian f g x' lam) :
    (∀ i, lam i * g i x = 0) ∧ Lagrangian f g x lam = f x := by
  have hlow : Lagrangian f g x lam ≤ f x := lagrangian_lower_bound f g x lam hlam hfeas
  have hinf : (⨅ x' : ℝ, Lagrangian f g x' lam) ≤ Lagrangian f g x lam := ciInf_le hbdd x
  have hL : Lagrangian f g x lam = f x := le_antisymm hlow (le_trans hgap hinf)
  have hsum : ∑ i, lam i * g i x = 0 := by
    have h := hL
    unfold Lagrangian at h
    linarith
  refine ⟨fun i => ?_, hL⟩
  exact (Finset.sum_eq_zero_iff_of_nonpos
    (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hfeas i))).mp hsum i (Finset.mem_univ i)

/-- 零间隙时的**互补松弛**：λ_i·g_i(x) = 0（`strong_duality_convex_case` 的投影）。 -/
theorem complementary_slackness_of_zero_gap (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hbdd : BddBelow (Set.range (fun x' : ℝ => Lagrangian f g x' lam)))
    (hgap : f x ≤ ⨅ x' : ℝ, Lagrangian f g x' lam) :
    ∀ i, lam i * g i x = 0 :=
  (strong_duality_convex_case f g x lam hlam hfeas hbdd hgap).1

/-- 零间隙时的**无间隙等式**：L(x,λ) = f(x)（乘子不再惩罚）。 -/
theorem zero_gap_lagrangian_eq (f : ℝ → ℝ) (g : Fin n → ℝ → ℝ) (x : ℝ)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hfeas : ∀ i, g i x ≤ 0)
    (hbdd : BddBelow (Set.range (fun x' : ℝ => Lagrangian f g x' lam)))
    (hgap : f x ≤ ⨅ x' : ℝ, Lagrangian f g x' lam) :
    Lagrangian f g x lam = f x :=
  (strong_duality_convex_case f g x lam hlam hfeas hbdd hgap).2

/-! ## 注：与 KKT / 增广拉格朗日的衔接
  · RealKKT 的增广拉格朗日 L_aug = (ax−b)² + λ(ax−b) 是「目标 + 乘子·约束违背」；
    本文件的 L(x,λ) = f(x) + Σλ_i g_i(x) 把该形态推广到有限不等式约束组。
  · 弱对偶（`lagrangian_lower_bound` / `weak_duality`）说明：任意 λ ≥ 0 给出原问题的
    下界，这正是对偶上升（dual ascent）与增广拉格朗日方法（RealPMix）的合法性来源。
  · 零间隙时的互补松弛（`strong_duality_convex_case`）即 KKT 的「乘子 × 约束 = 0」条件，
    与 RealKKT 的「约束满足 ⟹ 乘子归零」是同一现象的对偶陈述。
  · 诚实边界：凸 + Slater ⟹ 零间隙（强对偶）未证，见文件头说明。 -/

end Lattice
