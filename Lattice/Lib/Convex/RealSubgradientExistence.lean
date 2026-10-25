import Mathlib
import Lattice.Lib.Convex.RealSubgradient
/-!
# LATTICE: 下半连续凸函数次微分非空（**一维版**）

凸分析的核心存在性定理之一：凸函数在每一点都有次梯度（仿射支撑下界）：

  f 凸 ⟹ ∀ x, ∃ g, ∀ y, f y ≥ f x + g·(y − x)

mathlib 4.14 **没有** `subderiv` / 次梯度非空性的现成结果
（源码检索确认），本文件按定义自证一维情形。

本文件建立：

  1. `subdifferential`（定义）：∂f(x) = {g | Subgradient f x g}；
  2. `subgradient_exists_of_convex`（**核心**）：`ConvexOn ℝ Set.univ f` ⟹ 处处存在次梯度。
     证明路线：取左侧割线斜率集合
       S = { (f x − f a) / (x − a) | a < x }，
     用 `ConvexOn.slope_mono_adjacent`（割线斜率单调性）证明 S 有上界，
     取 `g := sSup S`，再用 `csSup_le` / `le_csSup` 分别处理 y > x 与 y < x 两种情形；
  3. `subdifferential_nonempty`：次微分非空（上一引理的集合形式）；
  4. `subgradient_convex_combo` / `subdifferential_convex`：∂f(x) 是凸集；
  5. `subgradient_monotone`：次梯度算子单调——x < y ⟹ ∂f(x) 中的 g ≤ ∂f(y) 中的 h
     （把 g、h 的两条次梯度不等式在对方处相加即得）；
  6. `convexOn_iff_subgradient_support`：**凸 ⟺ 处处存在仿射支撑下界**
     （正向为核心引理，反向由支撑下界的凸组合直接穿针）。

**诚实边界**（本文件不证 / 不声称的）：

- 本文件只证**一维**（定义域 = ℝ）。在一维情形定义域 ℝ 自动是开集，
  且 `f : ℝ → ℝ` 处处有限，所以次微分**处处**非空 ——
  甚至连 f 的下半连续性都不需要。这是真实的一般结论，不是技术性缩水。
- 有限维 `(Fin d → ℝ) → ℝ` 的次梯度非空性**未做**：它需要 epigraph 的
  支撑超平面定理 + 凸函数在开集上局部有界（mathlib 的
  `ConvexOn.continuousOn` / 内点理论），标注为后续。
- `convexOn_iff_subgradient_support` 的「凸 ⟹ 支撑」方向要求定义域为 Set.univ
  （全空间），因为一维的次梯度非空性正是在全空间上证的。
- 未做：次梯度与方向导数 `f'⁺(x; d)` 的关系、次梯度集是闭集、
  次微分的最优性条件（已在 RealSubgradient 的 `subgradient_minimum_criterion` 中给出 g = 0 的版本）。
- 无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

/-! ## 定义：次微分 ∂f(x) -/

/-- 次微分（一维）：∂f(x) = {g : ℝ | ∀ y, f y ≥ f x + g·(y − x)}。 -/
def subdifferential (f : ℝ → ℝ) (x : ℝ) : Set ℝ := {g | Subgradient f x g}

/-! ## 核心定理：凸函数处处有次梯度（一维）

构造左侧割线斜率集 S = {(f x − f a)/(x − a) | a < x}，取 g = sSup S。
割线斜率单调性（`ConvexOn.slope_mono_adjacent`）保证 S 被右侧割线斜率界住。
关键事实：
  · a < x < y ⟹ (f x − f a)/(x − a) ≤ (f y − f x)/(y − x)（右边是 S 的上界）；
  · (f x − f y)/(x − y) ∈ S（见证 a := y），故它 ≤ sSup S。
两种情形分别乘正的分母后 `linarith` 收尾。 -/

/-- **下半连续凸函数次微分非空（一维）**：
`f` 在 ℝ 上凸 ⟹ 每个 `x` 处存在 `g` 使 `f y ≥ f x + g·(y − x)`（∀ y）。
证明见文件头 docstring；核心是左侧割线斜率集的上确界给出仿射支撑。 -/
theorem subgradient_exists_of_convex (f : ℝ → ℝ) (x : ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ∃ g : ℝ, Subgradient f x g := by
  let S : Set ℝ := {c : ℝ | ∃ a : ℝ, a < x ∧ c = (f x - f a) / (x - a)}
  have hne : S.Nonempty :=
    ⟨(f x - f (x - 1)) / (x - (x - 1)), ⟨x - 1, by linarith, rfl⟩⟩
  have hbdd : BddAbove S := by
    refine ⟨(f (x + 1) - f x) / ((x + 1) - x), fun c hc => ?_⟩
    obtain ⟨a, hax, rfl⟩ := hc
    exact ConvexOn.slope_mono_adjacent hf (Set.mem_univ a) (Set.mem_univ (x + 1)) hax
      (by linarith)
  have hright : ∀ y : ℝ, x < y → sSup S ≤ (f y - f x) / (y - x) := by
    intro y hy
    apply csSup_le hne
    intro c hc
    obtain ⟨a, hax, rfl⟩ := hc
    exact ConvexOn.slope_mono_adjacent hf (Set.mem_univ a) (Set.mem_univ y) hax hy
  have hleft : ∀ y : ℝ, y < x → (f x - f y) / (x - y) ≤ sSup S := by
    intro y hy
    exact le_csSup hbdd ⟨y, hy, rfl⟩
  refine ⟨sSup S, fun y => ?_⟩
  rcases lt_trichotomy y x with hyx | hyx | hxy
  · -- y < x：由 (f x − f y)/(x − y) ≤ g 乘以 (x − y) > 0
    have h := hleft y hyx
    have hpos : 0 < x - y := by linarith
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    have hcancel : (f x - f y) / (x - y) * (x - y) = f x - f y :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    rw [hcancel] at hmul
    nlinarith
  · -- y = x：两边相等
    subst hyx
    simp
  · -- x < y：由 g ≤ (f y − f x)/(y − x) 乘以 (y − x) > 0
    have h := hright y hxy
    have hpos : 0 < y - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    have hcancel : (f y - f x) / (y - x) * (y - x) = f y - f x :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    rw [hcancel] at hmul
    nlinarith

/-- 次微分非空（`subgradient_exists_of_convex` 的集合形式）：
凸函数的 ∂f(x) 在每个 x 处非空。 -/
theorem subdifferential_nonempty (f : ℝ → ℝ) (x : ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (subdifferential f x).Nonempty :=
  subgradient_exists_of_convex f x hf

/-! ## 次微分的凸性 -/

/-- 次梯度的凸组合仍是次梯度：g₁, g₂ ∈ ∂f(x)、a, b ≥ 0、a + b = 1 ⟹
a·g₁ + b·g₂ ∈ ∂f(x)。逐点把两条次梯度不等式分别乘 a、b 后相加。 -/
theorem subgradient_convex_combo (f : ℝ → ℝ) (x g₁ g₂ a b : ℝ)
    (h₁ : Subgradient f x g₁) (h₂ : Subgradient f x g₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Subgradient f x (a * g₁ + b * g₂) := by
  intro y
  have h1 : f x + g₁ * (y - x) ≤ f y := h₁ y
  have h2 : f x + g₂ * (y - x) ≤ f y := h₂ y
  have hx' := mul_le_mul_of_nonneg_left h1 ha
  have hy' := mul_le_mul_of_nonneg_left h2 hb
  have hlev : a * (f x + g₁ * (y - x)) + b * (f x + g₂ * (y - x))
      = f x + (a * g₁ + b * g₂) * (y - x) := by
    have h1e : a * (f x + g₁ * (y - x)) + b * (f x + g₂ * (y - x))
        = (a + b) * f x + (a * g₁ + b * g₂) * (y - x) := by ring
    rw [h1e, hab, one_mul]
  rw [← hlev]
  calc a * (f x + g₁ * (y - x)) + b * (f x + g₂ * (y - x))
      ≤ a * f y + b * f y := add_le_add hx' hy'
    _ = f y := by rw [← add_mul, hab, one_mul]

/-- 次微分是凸集：∂f(x) 对凸组合封闭。 -/
theorem subdifferential_convex (f : ℝ → ℝ) (x : ℝ) : Convex ℝ (subdifferential f x) := by
  intro g₁ h₁ g₂ h₂ a b ha hb hab
  simpa only [smul_eq_mul] using subgradient_convex_combo f x g₁ g₂ a b h₁ h₂ ha hb hab

/-! ## 次梯度算子的单调性 -/

/-- 次梯度算子单调：g ∈ ∂f(x)、h ∈ ∂f(y)、x < y ⟹ g ≤ h。
证明：把 g 的次梯度不等式用在 y 处、h 的用在 x 处相加，
得 (g − h)·(y − x) ≤ 0，再除以 y − x > 0。 -/
theorem subgradient_monotone (f : ℝ → ℝ) (x y g h : ℝ)
    (hg : Subgradient f x g) (hh : Subgradient f y h) (hxy : x < y) : g ≤ h := by
  have h1 := hg y
  have h2 := hh x
  nlinarith

/-! ## 凸性 ⟺ 仿射支撑下界处处存在 -/

/-- **凸 ⟺ 处处存在仿射支撑下界**：
`f` 在 ℝ 上凸当且仅当每个 `x` 处存在 `g` 使 `∀ y, f y ≥ f x + g·(y − x)`。
正向：`subgradient_exists_of_convex`。
反向：给定支撑 `g` 在 `z = a·x + b·y` 处，把 `g` 的两条不等式在 x、y 处
分别乘 a、b 相加，中间项 g·(a·x + b·y − (a+b)·z) 消为 0。 -/
theorem convexOn_iff_subgradient_support (f : ℝ → ℝ) :
    ConvexOn ℝ Set.univ f ↔ ∀ x : ℝ, ∃ g : ℝ, Subgradient f x g := by
  constructor
  · intro hf x
    exact subgradient_exists_of_convex f x hf
  · intro h
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    obtain ⟨g, hg⟩ := h (a * x + b * y)
    have hx : f (a * x + b * y) + g * (x - (a * x + b * y)) ≤ f x := hg x
    have hy : f (a * x + b * y) + g * (y - (a * x + b * y)) ≤ f y := hg y
    have hx' := mul_le_mul_of_nonneg_left hx ha
    have hy' := mul_le_mul_of_nonneg_left hy hb
    have hz0 : a * (x - (a * x + b * y)) + b * (y - (a * x + b * y)) = 0 := by
      have h1 : a * (x - (a * x + b * y)) + b * (y - (a * x + b * y))
          = (a * x + b * y) - (a + b) * (a * x + b * y) := by ring
      rw [h1, hab, one_mul, sub_self]
    have hlev : a * (f (a * x + b * y) + g * (x - (a * x + b * y)))
        + b * (f (a * x + b * y) + g * (y - (a * x + b * y))) = f (a * x + b * y) := by
      have h1 : a * (f (a * x + b * y) + g * (x - (a * x + b * y)))
          + b * (f (a * x + b * y) + g * (y - (a * x + b * y)))
          = (a + b) * f (a * x + b * y)
            + g * (a * (x - (a * x + b * y)) + b * (y - (a * x + b * y))) := by ring
      rw [h1, hab, one_mul, hz0, mul_zero, add_zero]
    show f (a * x + b * y) ≤ a * f x + b * f y
    rw [← hlev]
    exact add_le_add hx' hy'

end Lattice
