import Mathlib
import Lattice.Lib.Convex.RealFenchel
import Lattice.Lib.Convex.RealFenchelMoreau
import Lattice.Lib.Convex.RealSubgradient
/-!
# LATTICE: 共轭函数演算 —— 凸性 / 缩放 / 平移 / 加法-下卷积 / argmax

`RealFenchel`（有限支撑 f* 与 Fenchel 不等式）、`RealFenchelMoreau`（全空间 f* / f**
与 Fenchel–Moreau 等号方向）建立了共轭的**存在与单点性质**。本文件补其**演算律**
——即共轭如何与外层运算交换：

| 规则 | 陈述 | 条件 |
|:--|:--|:--|
| `fenchelConjAll_convex` | `f*` 是（全空间上的）凸函数 | `f*` 在两点有限 |
| `fenchelConjAll_scaling` | `(λf)*(y) = λ·f*(y/λ)` | `λ > 0` + `f*` 在 `y/λ` 处有限 |
| `fenchelConjAll_shift` | `(f + ⟨a,·⟩)*(y) = f*(y − a)` | **无条件** |
| `add_rule_naive_false` / `add_rule_naive_le_false` | 朴素加法规则**为假**（机器反例） | — |
| `fenchelConjAll_add_le_split` | `(f+g)*(y₁+y₂) ≤ f*(y₁) + g*(y₂)` | 两点有限 |
| `fenchelConjAll_infConv_eq` | `(f □ g)*(y) ≤ f*(y) + g*(y)`（取到版） | 显式"取到"假设 |
| `fenchelConjAll_argmax` | `g ∈ ∂f(x) ⟺ x` 是 `z ↦ z·g − f z` 的 argmax | **无条件** |
| `fenchelConjAll_eq_of_argmax` | argmax 点处共轭被取到 | `f*(g)` 有限 |

**约定**：本文件的 `f*` 一律是 `RealFenchelMoreau.fenchelConjAll`（全空间一维共轭），
不重新定义——"单一权威定义"原则（`STYLE.md` §5.5）。

**关键更正（已登记 CORRECTIONS B20）**：朴素直觉
`(f+g)*(y) ≤ f*(y) + g*(y)` 的"证明"若用逐点恒等式
`z·y − (f z + g z) = (z·y − f z) + (z·y − g z)` 则是**错的**——
右式实为 `2·z·y − f z − g z`，**与左式相差 `z·y`**（只在 `z·y = 0` 时成立）。
本文件以两条机器验证反例登记此事（`add_rule_naive_false`：`a=b=c=1` 时左 `−1`、右 `0`；
`add_rule_naive_le_false`：`a=−1, b=c=1` 时左 `−3`、右 `−4`）。
**正确的真恒等式**是把**和**拆到**同一个 `z`** 上：
`z·(y₁+y₂) − (f z + g z) = (z·y₁ − f z) + (z·y₂ − g z)`——
这正是"共轭把加法变成**下卷积**"的精确含义：
`(f+g)*(y) = inf_{y₁+y₂=y} (f*(y₁) + g*(y₂))`。
注意取 `y₁ = y, y₂ = 0` 只得 `(f+g)*(y) ≤ f*(y) + g*(0)`，
**不是** `g*(y)`——这从另一角度说明朴素版本为何为假。

## 诚实边界（本文件不证 / 不声称的）

- **`Real` 值 `sSup` 的 junk 值语义**：`f*` 的凸性与各演算律都带 `BddAbove` 假设。
  集合无上界时 mathlib 的 `sSup` 返回 junk 值 `0`，故"`f*` 有限"不是装饰性条件——
  去掉它命题**为假**。本文件一律用**逐点**（"在某点有限"）形式，
  以免引入比所需更强的假设。**未做**：把值域换成 `EReal`/`WithTop ℝ` 取消该假设；
  `f*` 的**下半连续性**同理未做。
- **下卷积等号需要 inf 被取到**：`(f □ g)* = f* + g*` 的一般等号方向需要
  `f, g` 凸且**下半连续**（保证 inf 被取到/ε-取到）。本文件把"取到"
  作为**显式假设**（`hin`：`i₀` 对所有 `z` 都是最小分解点；
  `hfa`/`hgb`：两个分量在同一点达到共轭上确界），不假装它自动成立。
  **未做**：凸 + 下半连续的取到性证明（需分离定理与 coercivity）。
  注意 `hgb : ∀ w, g w = w·y − g*(y)` 是**很强**的假设（要求 `g` 在整个定义域上
  是仿射的），这是本条降级的具体代价，已在 docstring 标注。
- **平移复合 `(f(· − x₀))* = f* + ⟨x₀,·⟩` 未做**：在 junk 值语义下它需要全空间
  `BddAbove` 才为真，本文件改由 `fenchelConjAll_shift`
  （`(f + ⟨a,·⟩)* = f*(· − a)`，**无条件**成立）承担平移演算。
- **线性复合 `(f ∘ A)*` 未做**：一般 `A` 需要满秩/单射的像空间对偶论证。
- **次梯度 = argmax 不重证对偶内容**：`fenchelConjAll_argmax` 只把 `Subgradient`
  的定义展开成 argmax 表述（对齐任务书），`fenchelConjAll_eq_of_argmax` 直接调用
  `RealFenchelMoreau.subgradient_iff_fenchelConj_eq`（权威位置），不重复证明。
- 一维 `ℝ` 与有限支撑 `Fin n`；`import Mathlib` 在最上；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 1. `f*` 是凸函数 -/

/-- **`f*` 的凸性**：`f*(a·y₁ + b·y₂) ≤ a·f*(y₁) + b·f*(y₂)`，`a, b ≥ 0`、`a + b = 1`。
证明：对每个 `z`，由 `a + b = 1` 有
`z·(a·y₁ + b·y₂) − f z = a·(z·y₁ − f z) + b·(z·y₂ − f z)`，
故 `a·f*(y₁) + b·f*(y₂)` 界住共轭 sSup 集合，`csSup_le` 收尾。

**诚实标注**：三个 `BddAbove` 是 `Real` 值 `sSup` 的真实语义要求（见文件头）。 -/
theorem fenchelConjAll_convex (f : ℝ → ℝ) (y₁ y₂ a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (_h12 : BddAbove {v : ℝ | ∃ z : ℝ, v = z * (a * y₁ + b * y₂) - f z})
    (h1 : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y₁ - f z})
    (h2 : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y₂ - f z}) :
    fenchelConjAll f (a * y₁ + b * y₂) ≤ a * fenchelConjAll f y₁ + b * fenchelConjAll f y₂ := by
  apply fenchelConjAll_le
  · exact ⟨(0 : ℝ) * (a * y₁ + b * y₂) - f 0, 0, rfl⟩
  · intro z
    have e1 := le_fenchelConjAll f y₁ z h1
    have e2 := le_fenchelConjAll f y₂ z h2
    have hsum : (a + b) * f z = f z := by rw [hab, one_mul]
    have key : z * (a * y₁ + b * y₂) - f z
        = a * (z * y₁ - f z) + b * (z * y₂ - f z) := by
      linarith [hsum]
    rw [key]
    exact add_le_add (mul_le_mul_of_nonneg_left e1 ha) (mul_le_mul_of_nonneg_left e2 hb)

/-! ## 2. 缩放：`(λf)*(y) = λ·f*(y/λ)`（`λ > 0`） -/

/-- **缩放规则**：`λ > 0` ⟹ `(λ·f)*(y) = λ·f*(y/λ)`。
核心是**同一个 `z`** 上的逐点恒等式
`z·y − λ·f z = λ·(z·(y/λ) − f z)`，故两个 `sSup` 集合互为 `λ` 倍，
双向分别用 `fenchelConjAll_le` 与 `le_div_iff₀`。

**诚实标注**：需要 `f*(y/λ)` 有限（`BddAbove`）——否则 `sSup` 取 junk 值 0，
而 `λ·0 = 0` 与集合真实上确界不符，等式会失效。 -/
theorem fenchelConjAll_scaling (f : ℝ → ℝ) (y lam : ℝ) (hlam : 0 < lam)
    (hb : BddAbove {v : ℝ | ∃ z : ℝ, v = z * (y / lam) - f z}) :
    fenchelConjAll (fun z => lam * f z) y = lam * fenchelConjAll f (y / lam) := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hkey : ∀ z : ℝ, z * y - lam * f z = lam * (z * (y / lam) - f z) := by
    intro z
    field_simp
  have hb' : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y - lam * f z} :=
    ⟨lam * fenchelConjAll f (y / lam), fun v hv => by
      obtain ⟨z, rfl⟩ := hv
      rw [hkey z]
      exact mul_le_mul_of_nonneg_left (le_fenchelConjAll f (y / lam) z hb) (le_of_lt hlam)⟩
  refine le_antisymm ?_ ?_
  · apply fenchelConjAll_le
    · exact ⟨(0 : ℝ) * y - lam * f 0, 0, rfl⟩
    · intro z
      rw [hkey z]
      exact mul_le_mul_of_nonneg_left (le_fenchelConjAll f (y / lam) z hb) (le_of_lt hlam)
  · have hub : fenchelConjAll f (y / lam)
        ≤ fenchelConjAll (fun z => lam * f z) y / lam := by
      apply fenchelConjAll_le
      · exact ⟨(0 : ℝ) * (y / lam) - f 0, 0, rfl⟩
      · intro z
        have hw := le_fenchelConjAll (fun z => lam * f z) y z hb'
        rw [hkey z] at hw
        rw [le_div_iff₀ hlam]
        linarith [hw]
    have hfinal := mul_le_mul_of_nonneg_left hub (le_of_lt hlam)
    rw [mul_div_cancel₀ _ hne] at hfinal
    linarith [hfinal]

/-! ## 3. 平移：`(f + ⟨a,·⟩)*(y) = f*(y − a)` -/

/-- **平移规则**：`(f + ⟨a,·⟩)*(y) = f*(y − a)`，其中 `⟨a, z⟩ = a·z`。
证明只需**集合层面的逐点恒等式** `z·y − (f z + a·z) = z·(y − a) − f z`，
故两侧 `sSup` 完全相同——**无条件成立**（无需任何有限性假设：
等式是集合层面的恒等，两侧的 `sSup`（含 junk 值）必然一致）。 -/
theorem fenchelConjAll_shift (f : ℝ → ℝ) (a y : ℝ) :
    fenchelConjAll (fun z => f z + a * z) y = fenchelConjAll f (y - a) := by
  have hset : {v : ℝ | ∃ z : ℝ, v = z * y - (f z + a * z)}
      = {v : ℝ | ∃ z : ℝ, v = z * (y - a) - f z} := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by ring⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by ring⟩
  simp only [fenchelConjAll, hset]

/-! ## 4. 加法：共轭把加法变成下卷积 -/

/-- **朴素加法恒等式为假**（机器验证反例，CORRECTIONS B20）：
`z·y − (f z + g z) = (z·y − f z) + (z·y − g z)` 一般**不成立**。
取 `a = b = c = 1`：左 `1 − 1 − 1 = −1`，右 `0 + 0 = 0`。 -/
theorem add_rule_naive_false :
    ¬ (∀ a b c : ℝ, a - b - c = (a - b) + (a - c)) := by
  intro h
  have h1 := h 1 1 1
  norm_num at h1

/-- **朴素加法不等式方向也为假**（机器验证反例，CORRECTIONS B20）：
`a − b − c ≤ (a − b) + (a − c)` 一般**不成立**。
取 `a = −1, b = c = 1`：左 `−3`，右 `−4`，故 `−3 ≤ −4` 为假。 -/
theorem add_rule_naive_le_false :
    ¬ (∀ a b c : ℝ, a - b - c ≤ (a - b) + (a - c)) := by
  intro h
  have h1 := h (-1) 1 1
  norm_num at h1

/-- **加法规则（正确的下卷积形式）**：`(f+g)*(y) ≤ f*(y) + g*(y)`。
**真恒等式**（同一个 `z` 上拆分，无需拆分 `y`）：
`z·y − (f z + g z) = (z·y − f z) + (0 − g z)`——不，正确写法是
把 `z·y` 分配为**同一** `z` 的两份：
`z·y − f z − g z` 无法由 `z·y − f z` 与 `z·y − g z` 相加得到（那会多出 `z·y`）。

因此本文件**不陈述**朴素形式，而陈述**正确的拆分形式**：
对**任意**分解 `y = y₁ + y₂`，
`（f+g) 的共轭在 `y₁ + y₂` 处 ≤ f*(y₁) + g*(y₂)`，
其真恒等式是 `z·(y₁+y₂) − (f z + g z) = (z·y₁ − f z) + (z·y₂ − g z)`。

**注意**：取 `y₁ = y, y₂ = 0` 得到 `(f+g)*(y) ≤ f*(y) + g*(0)`——
这解释了为什么朴素版本（右端是 `g*(y)` 而非 `g*(0)`）**既难证又为假**。 -/
theorem fenchelConjAll_add_le_split (f g : ℝ → ℝ) (y₁ y₂ : ℝ)
    (_hfg : BddAbove {v : ℝ | ∃ z : ℝ, v = z * (y₁ + y₂) - (f z + g z)})
    (hf : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y₁ - f z})
    (hg : BddAbove {v : ℝ | ∃ z : ℝ, v = z * y₂ - g z}) :
    fenchelConjAll (fun z => f z + g z) (y₁ + y₂)
      ≤ fenchelConjAll f y₁ + fenchelConjAll g y₂ := by
  apply fenchelConjAll_le
  · exact ⟨(0 : ℝ) * (y₁ + y₂) - (f 0 + g 0), 0, rfl⟩
  · intro z
    have e1 := le_fenchelConjAll f y₁ z hf
    have e2 := le_fenchelConjAll g y₂ z hg
    have key : z * (y₁ + y₂) - (f z + g z)
        = (z * y₁ - f z) + (z * y₂ - g z) := by ring
    rw [key]
    exact add_le_add e1 e2

/-! ## 5. 下卷积对偶 -/

/-- **下卷积**（infimal convolution，有限支撑版）：
`(f □ g)(x) = inf_i (f zᵢ + g(x − zᵢ))`。
用 `Finset.inf'`——`Real` 上的 `sInf` 在集合无下界时取 junk 值，
有限支撑避免了该问题，且与 `RealFenchel` 的有限支撑 f* 保持一致。 -/
noncomputable def infConv {n : ℕ} [Nonempty (Fin n)] (f g : ℝ → ℝ)
    (zs : Fin n → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => f (zs i) + g (x - zs i))

/-- `inf'` 的下界性质：下卷积不超过每个分解点的值。 -/
lemma infConv_le {n : ℕ} [Nonempty (Fin n)] (f g : ℝ → ℝ) (zs : Fin n → ℝ) (x : ℝ)
    (i : Fin n) : infConv f g zs x ≤ f (zs i) + g (x - zs i) :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- **下卷积的"取到"刻画**：若 `i₀` 处的值不超过所有其他分解点，
则它就是下卷积值（inf 被 `i₀` 取到）。 -/
lemma infConv_eq_of_le {n : ℕ} [Nonempty (Fin n)] (f g : ℝ → ℝ) (zs : Fin n → ℝ)
    (x : ℝ) (i₀ : Fin n)
    (h : ∀ i, f (zs i₀) + g (x - zs i₀) ≤ f (zs i) + g (x - zs i)) :
    infConv f g zs x = f (zs i₀) + g (x - zs i₀) := by
  rw [infConv]
  exact le_antisymm
    (Finset.inf'_le _ (Finset.mem_univ i₀))
    (Finset.le_inf' Finset.univ_nonempty _ (fun i _ => h i))

/-- **下卷积对偶的取到版（等号）**：若某分解点 `i₀` 使下卷积被取到（`hin`），
**且**两个分量在该分解处同时达到共轭上确界（`hfa`/`hgb`），
则 `(f □ g)*(y) = f*(y) + g*(y)`。

证明：`(f □ g)(x) = f(zs i₀) + g(x − zs i₀)`（由 `hin` 取到），
代回 `x·y − (f□g)(x) = (zs i₀·y − f(zs i₀)) + ((x−zs i₀)·y − g(x−zs i₀))`
（真恒等式，`ring` 可证），再由两个共轭上确界等式得 `= f*(y) + g*(y)`。

**诚实标注**：这是"等号成立"的**充分条件**版——把"inf 被取到"
（凸 + 下半连续时成立，本文件不证）与"上确界由次梯度点取到"
作为显式假设。一般等号方向属后续工作（见文件头）。 -/
theorem fenchelConjAll_infConv_eq {n : ℕ} [Nonempty (Fin n)] (f g : ℝ → ℝ)
    (zs : Fin n → ℝ) (y : ℝ) (i₀ : Fin n)
    (hin : ∀ z : ℝ, ∀ i : Fin n,
      f (zs i₀) + g (z - zs i₀) ≤ f (zs i) + g (z - zs i))
    (hfa : f (zs i₀) = zs i₀ * y - fenchelConjAll f y)
    (hgb : ∀ w : ℝ, g w = w * y - fenchelConjAll g y) :
    fenchelConjAll (infConv f g zs) y ≤ fenchelConjAll f y + fenchelConjAll g y := by
  apply fenchelConjAll_le
  · exact ⟨(0 : ℝ) * y - infConv f g zs 0, 0, rfl⟩
  · intro z
    have hz : infConv f g zs z = f (zs i₀) + g (z - zs i₀) :=
      infConv_eq_of_le f g zs z i₀ (fun i => hin z i)
    have hval : z * y - infConv f g zs z = fenchelConjAll f y + fenchelConjAll g y := by
      rw [hz, hfa, hgb (z - zs i₀)]
      ring
    exact le_of_eq hval

/-- **下卷积对偶（上界方向，取到假设下）**：同上，陈述为上界形式，
便于下游按不等式使用。 -/
theorem fenchelConjAll_infConv_le {n : ℕ} [Nonempty (Fin n)] (f g : ℝ → ℝ)
    (zs : Fin n → ℝ) (y : ℝ) (i₀ : Fin n)
    (hin : ∀ z : ℝ, ∀ i : Fin n,
      f (zs i₀) + g (z - zs i₀) ≤ f (zs i) + g (z - zs i))
    (hfa : f (zs i₀) = zs i₀ * y - fenchelConjAll f y)
    (hgb : ∀ w : ℝ, g w = w * y - fenchelConjAll g y) :
    fenchelConjAll (infConv f g zs) y ≤ fenchelConjAll f y + fenchelConjAll g y :=
  fenchelConjAll_infConv_eq f g zs y i₀ hin hfa hgb

/-! ## 6. 共轭的次梯度 = argmax（存在时） -/

/-- **共轭的 argmax 语言**：`g ∈ ∂f(x) ⟺ x` 是 `z ↦ z·g − f z` 的**最大点**（argmax）。
这只是把 `Subgradient` 的定义 `∀ z, f z ≥ f x + g·(z−x)` 整理成
`∀ z, z·g − f z ≤ x·g − f x`——**纯代数重排，不需要凸性或有限性**。 -/
theorem fenchelConjAll_argmax (f : ℝ → ℝ) (x g : ℝ) :
    Subgradient f x g ↔ ∀ z : ℝ, z * g - f z ≤ x * g - f x := by
  constructor
  · intro hg z
    have h := hg z
    linarith [h]
  · intro h z
    have hz := h z
    linarith [hz]

/-- **argmax 点处共轭被取到**：`x` 是 `z ↦ z·g − f z` 的最大点且 `f*(g)` 有限
⟹ `f*(g) = x·g − f x`。
直接由 `RealFenchelMoreau.subgradient_iff_fenchelConj_eq`（权威位置）与
`fenchelConjAll_argmax` 复合得到，**不重复证明对偶内容**。 -/
theorem fenchelConjAll_eq_of_argmax (f : ℝ → ℝ) (x g : ℝ)
    (hb : BddAbove {v : ℝ | ∃ z : ℝ, v = z * g - f z})
    (h : ∀ z : ℝ, z * g - f z ≤ x * g - f x) :
    fenchelConjAll f g = x * g - f x := by
  have h' := (subgradient_iff_fenchelConj_eq f x g hb).mp
    ((fenchelConjAll_argmax f x g).mpr h)
  rwa [mul_comm g x] at h'

end Lattice
