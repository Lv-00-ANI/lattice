import Mathlib
import Lattice.Lib.Convex.RealFenchel
import Lattice.Lib.Convex.RealSubgradientExistence
/-!
# LATTICE: Fenchel–Moreau **等号方向** f** = f（一维凸函数）

凸共轭线的对偶一环，衔接 `RealFenchel`（有限支撑 f* / f** ≤ f 的弱方向）
与 `RealSubgradientExistence`（一维凸函数次梯度非空）：

  凸共轭（Fenchel 共轭）：f*(y) = sup_z (z·y − f(z))；
  二次共轭：f**(x) = sup_y (y·x − f*(y))。

本文件在**全 ℝ** 上实现 f* 与 f**，并证明 **Fenchel–Moreau 等号方向**：

  f : ℝ → ℝ 凸 ⟹ f**(x) = f(x)（∀ x）

一维情形**不需要** f 的闭性/下半连续性 ——
因为 `f : ℝ → ℝ` 的定义域就是全空间，处处有限，
`RealSubgradientExistence.subgradient_exists_of_convex` 已给出处处次梯度，
它正是 f** = f 的等号方向所需的全部设施。

本文件建立：

  1. `fenchelConjAll`（定义）：f*(y) = sSup_{z ∈ ℝ} (z·y − f z)；
  2. `le_fenchelConjAll` / `fenchelConjAll_le`：`sSup` 的两条基本性质；
  3. `fenchel_ineq_all`：Fenchel 不等式 z·y ≤ f z + f*(y)；
  4. `fenchelConjAll_subgradient`（**核心**）：g ∈ ∂f(x) ⟹ f*(g) = g·x − f(x)；
  5. `subgradient_iff_fenchelConj_eq`（**有价值的 iff**）：在 f*(g) 有限的前提下，
     g ∈ ∂f(x) ⟺ f*(g) = g·x − f(x)（该 iff 本身**不需要凸性**）；
  6. `fenchel_biconj_eq_self`（**主定理**）：凸 f 的 f** = f（全空间等号方向）；
  7. `fenchel_biconj_le_self`：f** ≤ f（弱的半边，不需要凸性，但需要 f** 的
     sSup 集合非空——见下方诚实标注）；
  8. `finite_support_le_all`（**桥接**）：`RealFenchel` 的有限支撑共轭
     `fenchelConjugate f xs y` 不超过全空间共轭 `fenchelConjAll f y`。

**诚实边界**（本文件不证 / 不声称的）：

- 本文件只处理**一维**（定义域 = ℝ）。f* 与 f** 都用 `sSup` 而非扩展实数：
  一般 f 的 f*(y) = sup_z (z·y − f z) 可能为 +∞，而 mathlib 的 `sSup`
  在集合无上界时取 **junk 值 0**（`Real` 不是 `WithTop ℝ`）。因此
  `fenchelBiconjAll` 的定义显式限制到 f* 真正有限（`BddAbove`）的 y 上，
  `subgradient_iff_fenchelConj_eq` 与 `finite_support_le_all` 也带显式
  `BddAbove` 假设。否则「f*(y) 有限」「f* = g·x − f x」这类命题为假/无意义。
  这一 `BddAbove` 不是可省的技术条件，是 `Real` 值 `sSup` 的真实语义。
- **未做**：一般有限维 `ℝ^d` 闭凸函数的 Fenchel–Moreau 等号方向
  （需要 epigraph 的支撑超平面 + f 的下半连续/闭性，见 RealSupportingHyperplane 线）；
- **未做**：把 f* 做成扩展实数（`EReal` / `WithTop ℝ`）以免上述 junk 值，
  从而取消所有 `BddAbove` 假设；
- 桥接说明：`RealFenchel.fenchel_biconjugate_le` 是**有限支撑**（`Fin n`）的
  **弱方向** f** ≤ f，对任意 f 成立；本文件的 `fenchel_biconj_eq_self` 是
  **一维全空间**的**等号方向**，需要凸性。二者互补：
  `finite_support_le_all` 给出有限支撑 f* ≤ 全空间 f*。
- 无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

/-! ## 定义：全空间 Fenchel 共轭与其基本性质 -/

/-- 全空间 Fenchel 共轭（一维）：f*(y) = sup_{z ∈ ℝ} (z·y − f z)。
注意取的是 `Real` 值的 `sSup`：当集合无上界时 mathlib 返回 junk 值 0，
故使用该定义时须显式假设 `BddAbove {v | ∃ z, v = z * y − f z}`。 -/
noncomputable def fenchelConjAll (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ z : ℝ, v = z * y - f z}

/-- sSup 的上界性质：每个 z·y − f z 都不超过 f*(y)（需 f*(y) 有限，即 BddAbove）。 -/
lemma le_fenchelConjAll (f : ℝ → ℝ) (y z : ℝ)
    (hb : BddAbove {v : ℝ | ∃ w : ℝ, v = w * y - f w}) :
    z * y - f z ≤ fenchelConjAll f y :=
  le_csSup hb ⟨z, rfl⟩

/-- sSup 的最小上界性质：若非空且每个 z·y − f z ≤ C，则 f*(y) ≤ C。 -/
lemma fenchelConjAll_le (f : ℝ → ℝ) (y C : ℝ)
    (hne : ({v : ℝ | ∃ w : ℝ, v = w * y - f w}).Nonempty)
    (h : ∀ w : ℝ, w * y - f w ≤ C) : fenchelConjAll f y ≤ C :=
  csSup_le hne fun v hv => by
    obtain ⟨w, rfl⟩ := hv
    exact h w

/-- Fenchel 不等式（一维全空间）：z·y ≤ f z + f*(y)（需 f*(y) 有限）。 -/
lemma fenchel_ineq_all (f : ℝ → ℝ) (z y : ℝ)
    (hb : BddAbove {v : ℝ | ∃ w : ℝ, v = w * y - f w}) :
    z * y ≤ f z + fenchelConjAll f y := by
  have h := le_fenchelConjAll f y z hb
  linarith

/-! ## 核心引理：次梯度处共轭被取到 -/

/-- **核心**：若 g ∈ ∂f(x)（即 ∀ z, f z ≥ f x + g·(z − x)），则
f*(g) = g·x − f(x)：上确界在 z = x 处被取到。
（这里只需次梯度不等式，`hf` 未用到；保留它以对齐任务接口。） -/
theorem fenchelConjAll_subgradient (f : ℝ → ℝ) (x g : ℝ)
    (_hf : ConvexOn ℝ Set.univ f) (hg : Subgradient f x g) :
    fenchelConjAll f g = g * x - f x := by
  have hb : BddAbove {v : ℝ | ∃ z : ℝ, v = z * g - f z} := by
    refine ⟨g * x - f x, ?_⟩
    rintro v ⟨z, rfl⟩
    have h := hg z
    linarith
  apply le_antisymm
  · -- 集合元素形如 `z * y - f z`（`z` 在左、`y` 在右），取 `z := x` 时是 `x * g - f x`，
    -- 故必须写成 `x * g - f x`（写成 `g * x - f x` 会因 `rfl` 不成立而报类型不匹配）。
    apply fenchelConjAll_le f g (g * x - f x) ⟨x * g - f x, x, by ring⟩
    intro z
    have h := hg z
    linarith
  · simpa [mul_comm] using le_fenchelConjAll f g x hb

/-! ## 次梯度 ⟺ 共轭在 g 处被取到 -/

/-- **次梯度 ⟺ 共轭等式**：在 f*(g) 有限（`BddAbove`）的前提下，
g ∈ ∂f(x) ⟺ f*(g) = g·x − f(x)。
正向：次梯度不等式界住集合，等式由 `le_antisymm` 得到（与核心引理同构，但此处不必假设凸性）；
反向：`le_fenchelConjAll` 在 z 处给出 z·g − f z ≤ g·x − f x，整理即次梯度不等式。
**注意**：该 iff 的两个方向都不需要 f 的凸性；`BddAbove` 不可省（见文件头诚实标注）。 -/
theorem subgradient_iff_fenchelConj_eq (f : ℝ → ℝ) (x g : ℝ)
    (hb : BddAbove {v : ℝ | ∃ z : ℝ, v = z * g - f z}) :
    Subgradient f x g ↔ fenchelConjAll f g = g * x - f x := by
  constructor
  · intro hg
    apply le_antisymm
    · -- 同 `fenchelConjAll_subgradient`：取 `z := x` 时集合元素是 `x * g - f x`。
      apply fenchelConjAll_le f g (g * x - f x) ⟨x * g - f x, x, by ring⟩
      intro z
      have h := hg z
      linarith
    · simpa [mul_comm] using le_fenchelConjAll f g x hb
  · intro heq z
    have h := le_fenchelConjAll f g z hb
    rw [heq] at h
    linarith

/-! ## 定义：全空间二次共轭 -/

/-- 全空间二次共轭（一维）：f**(x) = sup over y（f*(y) 有限）的 (y·x − f*(y))。
**诚实标注**：sup 显式限制到 `BddAbove {w | ∃ z, w = z·y − f z}`（即 f*(y) 真正有限）的 y；
因为 `Real` 值的 `sSup` 在集合无上界时取 junk 值 0，不限制则命题为假/无意义。 -/
noncomputable def fenchelBiconjAll (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ y : ℝ,
    BddAbove {w : ℝ | ∃ z : ℝ, w = z * y - f z} ∧ v = y * x - fenchelConjAll f y}

/-! ## 弱方向：f** ≤ f -/

/-- f** ≤ f（Fenchel–Moreau 的弱半边，**不需要凸性**）：
集合 {y·x − f*(y)} 的每个元素 ≤ f(x)，由 `le_fenchelConjAll` 在 z := x 处给出。
**诚实标注**：需显式假设该 sSup 集合非空——否则 `sSup` 返回 junk 值 0，
结论可能为假。凸性可保证非空（见 `fenchel_biconj_eq_self`），此处不假设凸性。 -/
theorem fenchel_biconj_le_self (f : ℝ → ℝ) (x : ℝ)
    (hne : ({v : ℝ | ∃ y : ℝ,
      BddAbove {w : ℝ | ∃ z : ℝ, w = z * y - f z} ∧
        v = y * x - fenchelConjAll f y}).Nonempty) :
    fenchelBiconjAll f x ≤ f x := by
  apply csSup_le hne
  intro v hv
  obtain ⟨y, hyb, rfl⟩ := hv
  have h := le_fenchelConjAll f y x hyb
  linarith

/-! ## 主定理：Fenchel–Moreau 等号方向 f** = f（一维凸） -/

/-- **Fenchel–Moreau 等号方向（一维）**：凸 f : ℝ → ℝ 的二次共轭等于自身，f**(x) = f(x)。

证明：
  · ≥ 方向（`f x ≤ f** x`）：取次梯度 g ∈ ∂f(x)（`subgradient_exists_of_convex`），
    其对应的元素 `g·x − f*(g) = g·x − (g·x − f x) = f x` 落在 f** 的 sSup 集合中，
    `le_csSup` 给出；
  · ≤ 方向（`f** x ≤ f x`）：集合非空（同上元素），且每个元素
    `y·x − f*(y) ≤ f x`，由 `le_fenchelConjAll` 在 z := x 处给出，`csSup_le` 收尾。

一维下**不需要** f 的闭性/下半连续性：定义域 = ℝ 保证处处有限、处处有次梯度。 -/
theorem fenchel_biconj_eq_self (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (x : ℝ) :
    fenchelBiconjAll f x = f x := by
  let T : Set ℝ := {v : ℝ | ∃ y : ℝ,
    BddAbove {w : ℝ | ∃ z : ℝ, w = z * y - f z} ∧ v = y * x - fenchelConjAll f y}
  obtain ⟨g, hg⟩ := subgradient_exists_of_convex f x hf
  have hgBdd : BddAbove {w : ℝ | ∃ z : ℝ, w = z * g - f z} := by
    refine ⟨g * x - f x, ?_⟩
    rintro v ⟨z, rfl⟩
    have h := hg z
    linarith
  have hmem : f x ∈ T := by
    refine ⟨g, hgBdd, ?_⟩
    rw [fenchelConjAll_subgradient f x g hf hg]
    ring
  have hbdd : BddAbove T := by
    refine ⟨f x, ?_⟩
    rintro v ⟨y, hyb, rfl⟩
    have h := le_fenchelConjAll f y x hyb
    linarith
  apply le_antisymm
  · show sSup T ≤ f x
    apply csSup_le ⟨f x, hmem⟩
    intro v hv
    obtain ⟨y, hyb, rfl⟩ := hv
    have h := le_fenchelConjAll f y x hyb
    linarith
  · show f x ≤ sSup T
    exact le_csSup hbdd hmem

/-! ## 桥接：有限支撑共轭 ≤ 全空间共轭 -/

/-- **桥接** `RealFenchel` 的有限支撑共轭与全空间共轭：
`fenchelConjugate f xs y ≤ fenchelConjAll f y`
（有限支撑的 sup 不超过全空间的 sup；需 f*(y) 有限）。
`RealFenchel.fenchel_biconjugate_le` 是有限支撑的弱方向 f** ≤ f，
本文件的 `fenchel_biconj_eq_self` 是一维全空间的等号方向，二者互补。 -/
theorem finite_support_le_all (f : ℝ → ℝ) {n : ℕ} [Nonempty (Fin n)]
    (xs : Fin n → ℝ) (y : ℝ)
    (hb : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y - f z}) :
    fenchelConjugate f xs y ≤ fenchelConjAll f y := by
  apply fenchelConjugate_le
  intro i
  exact le_fenchelConjAll f y (xs i) hb

end Lattice
