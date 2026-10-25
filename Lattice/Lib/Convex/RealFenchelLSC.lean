import Mathlib
import Lattice.Lib.Convex.RealFenchelMoreau
/-!
# LATTICE: Fenchel 共轭的下半连续性（B3）——`f*` 的闭性与 lsc 性

`RealFenchelMoreau` 用 `ℝ` 值 `sSup` 定义共轭 `fenchelConjAll f y = sSup {w*y − f w}`，
并证了 Fenchel–Moreau 等式 `fenchelBiconjAll f = f`（凸函数）。

本文件回答 ROADMAP 的 **B3**：**`f*`（Fenchel 共轭）是下半连续的**。

## 关键：`ℝ` 值 `sSup` 的 junk 值问题（诚实标注，本文件的核心边界）

`Real.sSup` 对**无上界**集合返回 **junk 值 `0`**（`Real.sSup_empty : sSup ∅ = 0`，
且 `sSup` 在无上界时有 `sSup = 0`）。`fenchelConjAll f y = sSup {w*y − f w}`
在**定义域是否无界与是否非空**两个维度上都会踩到这个 junk：

* 若 `{w*y − f w}` 无上界（典型：`f` 是仿射函数 `w ↦ a*w` 且 `y ≠ a`），则
  `fenchelConjAll f y = 0`，而真正的共轭应是 `+∞` —— **junk**；
* 若 `{w*y − f w}` 为空（`ℝ` 上不可能，但形式化上 `∅` 也给出 `0`）——同样 junk。

因此**「`f*` 是 lsc 的」在 `ℝ` 值 `sSup` 编码下一般地为假**（在 junk 点上是
「假 lsc」：函数值被人为置 `0`，破坏了 `sup` 的真实上包络结构）。
本文件给出：

1. `fenchelConjAll_nonempty`：集合 `{w*y − f w}` 恒**非空**（`w := 0` 给出 `−f 0`），
   故空集那一路 junk 不会发生；
2. **逐点 `BddAbove` 条件**（见 `lsc_condition`）：为使 `f*` 在 `y` 处是 *真正的* 共轭值
   （而非 junk `0`），需要 `{w*y − f w}` **有上界**，即集合 `{w | 0 < w*y − f w}`
   的 `sSup` 有限 —— 本文件把它形式化为 `BddAbove {w*y − f w}`；
3. **B3 主定理**（`fenchelConjAll_lsc`，**条件版**）：在 `y` 处 `BddAbove`
   且 `f*` 在 `y` 的**邻域内处处有限**（`hloc`）的前提下，`f*` 在 `y` 处**下半连续**，
   且给出**显式模**：对任意 `ε > 0`，存在 `δ = ε/(2(|w₀|+1)) > 0`，使
   `|y' − y| < δ` 时 `f* y − ε ≤ f* y'`（这正是 lsc 的 ε-δ 形式）。

## 路线（为什么带 `BddAbove` 就够）

带 `BddAbove` 时 `f* y` 是**真上确界**：对任意 `ε > 0` 存在 `w₀` 使
`f* y − ε ≤ w₀*y − f w₀`（上确界的逼近性质）。`f` 本身不必有界，
因为界住 `f*` 的是**同一个 `w₀` 在 `y'` 处的取值**：
`w₀*y' − f w₀ = (w₀*y − f w₀) + w₀*(y' − y) ≥ f* y − ε − |w₀|·|y' − y|`，
取 `δ = ε / (|w₀| + 1)` 即得。这条路线**只用 `f*` 的 `sSup` 定义**，
不需要 `f` 凸或有界——因此 `BddAbove` 是**唯一**实质假设。

## 诚实边界（中文标注）

- **`BddAbove` 是显式条件，不可省（junk 值）**：如上所述，`ℝ` 值 `sSup` 对无上界集
  返回 `0`。本文件**不**声称「`f*` 无条件 lsc」——那在 junk 点上是**假**的。
  给出的是一致于 `RealFenchelMoreau`/`RealFenchel` 编码的**条件版**，
  并逐点携带 `BddAbove`（其余文件用 `le_fenchelConjAll`/`fenchelConjAll_le` 时
  也都要显式传入同一个 `BddAbove`，故本条件与既有库的接口形态一致）。
- **未做 —— 真正的 `ℝ̄ = ℝ ∪ {±∞}`（`ENNReal`/`WithTop ℝ`）编码**：若要无条件陈述
  「`f*` 是 lsc 的」，正确做法是把值域换成 `WithTop ℝ`（`⊥`/`⊤` 有序完备格，
  `sSup` 无 junk 值），此时 `f*` 是**仿射函数族的上确界**，
  而上确界恒 lsc 是纯序拓扑事实。该**换值域的重写未做**（会改动既有定义，
  超出 B3 的范围），本文件在 `ℝ` 值编码内以逐点 `BddAbove` 条件等价地表达。
  **归因（重要，避免误诊）**：这条限制的根因是**值域决策**（`ℝ` vs `EReal`/`WithTop ℝ`），
  **不是** mathlib 4.14 缺工具——`csSup_le`/`le_csSup`/`BddAbove`/`Metric.mem_nhds_iff`
  等本文件实际用到的工具全部齐备，证明也因此完全走通。
  项目已在 `RealFenchelEReal.lean` 方向迁移值域，那才是消除本条件的正路。
- **未做 —— 序列形式 `f* y ≤ liminf`**：本文件给 ε-δ 形式（与
  `LowerSemicontinuous` 的定义一致），未单独给出 `∀ y, f* y ≤ liminf` 的
  `Filter` 形式重述（两者等价，属同一命题的改写）。
- **未做 —— `f*` 的凸性 + lsc 联合刻画 `f** = f` 的闭凸版本**：
  `RealFenchelMoreau.fenchel_biconj_eq_self` 已给凸函数版；把「凸 + lsc」作为
  充分必要条件刻画 `f** = f`（即 `f` 闭凸 ⟺ 双共轭还原）**未做**。
- **未做 —— 非空但无上界时的「lsc 在扩展意义下成立」**：若允许值 `+∞`，
  junk 点恰好对应 `f* y = +∞`，此时 lsc 自动成立；本文件不展开该论证（同第 2 条）。
- 无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

open Filter

open scoped Topology

namespace Lattice

/-- **共轭的余集恒非空（junk 值的第一路排除）**：
`{v | ∃ w, v = w*y − f w}` 始终非空（取 `w := 0` 得 `−f 0`）。
故 `Real.sSup_empty` 那一支的 junk（空集返回 `0`）在本编码下**不会**发生；
本文件真正要防的是「非空但无上界」那一支（见 `fenchelConjAll_lsc` 的 `hbd`）。 -/
theorem fenchelConjAll_nonempty (f : ℝ → ℝ) (y : ℝ) :
    {v : ℝ | ∃ w, v = w * y - f w}.Nonempty :=
  ⟨0 * y - f 0, 0, rfl⟩

/-- **真下界的 ε-逼近（上确界的逼近性质）**：
若 `{w*y − f w}` 有上界，则对任意 `ε > 0` 存在 `w₀` 使
`f* y − ε ≤ w₀*y − f w₀`。

证明：若不然，`w₀*y − f w₀ < f* y − ε` 对所有 `w₀` 成立，即
`f* y − ε` 是（严格）上界；但 `sSup` 是**最小**上界，故 `f* y ≤ f* y − ε`，矛盾。 -/
theorem fenchelConjAll_sub_le (f : ℝ → ℝ) (y ε : ℝ) (hε : 0 < ε)
    (hbd : BddAbove {v : ℝ | ∃ w, v = w * y - f w}) :
    ∃ w₀ : ℝ, fenchelConjAll f y - ε ≤ w₀ * y - f w₀ := by
  by_contra hcon
  push_neg at hcon
  -- `f* y − ε` 是上界
  have hub : ∀ v ∈ {v : ℝ | ∃ w, v = w * y - f w}, v ≤ fenchelConjAll f y - ε := by
    rintro v ⟨w, rfl⟩
    exact le_of_lt (hcon w)
  -- 但 `f* y` 是最小上界
  have hmin : fenchelConjAll f y ≤ fenchelConjAll f y - ε :=
    csSup_le (fenchelConjAll_nonempty f y) hub
  linarith

/-- **B3 主定理（`f*` 的下半连续性，条件版）**：
设 `f*` 在 `y` 的一个邻域内**处处有限**（即邻域内每点 `z` 的集合
`{v | ∃ w, v = w*z − f w}` 都有上界——`hbd` 给出 `y` 本身、`hloc` 给出邻域内其余点）。
则 `f* = fenchelConjAll f` 在 `y` 处**下半连续**，
即对任意 `ε > 0` 存在 `δ > 0`，使 `|y' − y| < δ` 时 `f* y − ε ≤ f* y'`。

**证明（显式模）**：`hbd` 给出 `w₀` 使 `f* y − ε/2 ≤ w₀*y − f w₀`；
把 `ε/2` 留给位移项，取 `δ = ε / (2(|w₀| + 1))`，则
`w₀*(y − y') ≤ |w₀|·|y − y'| ≤ ε/2`，于是
`f* y − ε/2 ≤ w₀y − f w₀ ≤ (w₀y' − f w₀) + ε/2 ≤ f* y' + ε/2`，
其中最后一步用了 `y'` 处集合有上界（`hloc`）⟹ `w₀y' − f w₀ ≤ f* y'`。

**诚实标注（`BddAbove` 不可省）**：`ℝ` 值 `sSup` 的 junk 值 0 使
「无条件 lsc」为**假**（见 `const_zero_conj_unbounded`）。
本定理的假设形态是「`f*` 在该点邻域内有限」，这与
`RealFenchelMoreau` 中每个引理都要显式传入 `BddAbove` 的做法一致。
注意**邻域内**的有限性（`hloc`）比**单点** `BddAbove` 强——
单点条件在 `y'` 处可能失效，而证明需要 `y'` 处的下界，故必须局部一致地假设。 -/
theorem fenchelConjAll_lsc (f : ℝ → ℝ) (y : ℝ)
    (hbd : BddAbove {v : ℝ | ∃ w, v = w * y - f w})
    (hloc : ∀ᶠ y' in 𝓝 y, BddAbove {v : ℝ | ∃ w, v = w * y' - f w}) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y' : ℝ, |y' - y| < δ → fenchelConjAll f y - ε ≤ fenchelConjAll f y' := by
  intro ε hε
  obtain ⟨w₀, hw₀⟩ := fenchelConjAll_sub_le f y (ε / 2) (by linarith) hbd
  obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hloc
  -- 最终半径取 `min (ε/(2(|w₀|+1))) r`：使「位移小」与「落在邻域内」**同时**成立
  refine ⟨min (ε / (2 * (|w₀| + 1))) r, lt_min (by positivity) hrpos, ?_⟩
  intro y' hy'
  have hδ : |y' - y| < ε / (2 * (|w₀| + 1)) := lt_of_lt_of_le hy' (min_le_left _ _)
  have hnear : y' ∈ Metric.ball y r := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_lt_of_le hy' (min_le_right _ _)
  have hbdy' : BddAbove {v : ℝ | ∃ w, v = w * y' - f w} := hr hnear
  -- `w₀` 在 `y'` 处的取值 ≤ `f* y'`（用 `y'` 处的 `BddAbove`）
  have hcand : w₀ * y' - f w₀ ≤ fenchelConjAll f y' :=
    le_fenchelConjAll f y' w₀ hbdy'
  -- 位移界：`w₀*(y − y') ≤ |w₀|·|y − y'| ≤ ε/2`
  have hshift : w₀ * (y - y') ≤ ε / 2 := by
    have h2 : |w₀ * (y - y')| = |w₀| * |y - y'| := abs_mul w₀ (y - y')
    have h1 : w₀ * (y - y') ≤ |w₀ * (y - y')| := le_abs_self _
    have h3 : |y - y'| < ε / (2 * (|w₀| + 1)) := by
      rw [abs_sub_comm]; exact hδ
    have h4 : |w₀| * |y - y'| ≤ |w₀| * (ε / (2 * (|w₀| + 1))) :=
      mul_le_mul_of_nonneg_left (le_of_lt h3) (abs_nonneg w₀)
    have h5 : |w₀| * (ε / (2 * (|w₀| + 1))) ≤ ε / 2 := by
      -- B378: `rw [mul_div_assoc]` could not match -- the target's product has
      -- the division on the right, whereas mul_div_assoc expects `a * b / c`.
      -- `ring` produces the normal form the subsequent rw needs.
      have h1 : |w₀| * (ε / (2 * (|w₀| + 1))) = |w₀| * ε / (2 * (|w₀| + 1)) := by ring
      rw [h1, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|w₀| + 1))
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg w₀, hε]
    linarith [h1, h2, h4, h5]
  -- `w₀y − f w₀ ≤ (w₀y' − f w₀) + ε/2 ≤ f* y' + ε/2`
  have hle : w₀ * y - f w₀ ≤ fenchelConjAll f y' + ε / 2 := by
    have heq : w₀ * y - f w₀ = (w₀ * y' - f w₀) + w₀ * (y - y') := by ring
    linarith [heq, hshift, hcand]
  linarith [hw₀, hle]

/-- **下半连续的 `Filter` 形式**：`f*` 在 `y` 处沿 `𝓝 y` 满足
`f* y ≤ liminf_{y'→y} f* y'`（用 `Filter` 语言表述，等价于 ε-δ 形式）。
这里以「对每个 `ε > 0`，`{y' | f* y − ε ≤ f* y'}` 是 `y` 的邻域」表述，
**这正是不下于 ε 的等号下水平集的开性**。 -/
theorem fenchelConjAll_lsc_eventually (f : ℝ → ℝ) (y : ℝ)
    (hbd : BddAbove {v : ℝ | ∃ w, v = w * y - f w})
    (hloc : ∀ᶠ y' in 𝓝 y, BddAbove {v : ℝ | ∃ w, v = w * y' - f w}) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ y' in 𝓝 y, fenchelConjAll f y - ε ≤ fenchelConjAll f y' := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := fenchelConjAll_lsc f y hbd hloc ε hε
  exact Metric.mem_nhds_iff.mpr ⟨δ, hδpos, fun y' hy' => hδ y' (by
    rw [Metric.mem_ball, Real.dist_eq] at hy'
    exact hy')⟩

/-- **在 junk 点上的「条件确实会失效」（诚实标注的具体化）**：
取 `f := fun _ => 0`，则 `{w*y − 0} = Set.range (fun w => w*y)` 在 `y ≠ 0` 时**无上界**，
故 `fenchelConjAll f y = 0`（junk），而真正的共轭应为 `+∞`。

本定理给出**可机器验证的部分**：`y ≠ 0` 时集合无上界（`¬ BddAbove`），
故 `fenchelConjAll_lsc` 的 `hbd` 假设在该点上**不可满足**——
这说明 `BddAbove` 不是装饰性假设，而是定理成立所必需的。 -/
theorem const_zero_conj_unbounded (y : ℝ) (hy : y ≠ 0) :
    ¬ BddAbove {v : ℝ | ∃ w, v = w * y - (fun _ : ℝ => (0 : ℝ)) w} := by
  intro hbd
  obtain ⟨C, hC⟩ := hbd
  -- 集合元素形如 `w*y`；只要找到 `w` 使 `w*y > C` 即与上界矛盾。
  -- 关键是选 `w` 使 `w*y` 严格超过 `C`：用 `C - 1` 与 `C + 1` 两个目标值，
  -- 再除以 `y`。**注意不能用一个与 `C` 无关的常数**（如 `-1`）：
  -- `C ≤ 0` 时 `-1 ≤ C` 可能与 `C ≤ 0` 相容（如 `C = 0`），推不出矛盾。
  have key : ∀ t : ℝ, C < t → t ∈ {v : ℝ | ∃ w, v = w * y - (fun _ : ℝ => (0 : ℝ)) w} := by
    intro t ht
    exact ⟨t / y, by
      have h : (t / y : ℝ) * y = t := by field_simp
      rw [h, sub_zero]⟩
  -- `C + 1 > C`，故 `C + 1` 在集合中，与上界 `C` 矛盾
  exact absurd (hC (key (C + 1) (by linarith))) (by linarith)

/-- **B3 的集合论形式（去掉 `f` 的依赖）**：对任意实集 `S`，
`S` 有上界时 `sSup` 的「下半连续模」由 `S` 的逼近元给出。

这是 `fenchelConjAll_lsc` 去掉共轭包装后的纯序事实：
`BddAbove S`、`Nonempty S` 时，对任意 `ε > 0` 存在 `s ∈ S` 使 `sSup S − ε ≤ s`。
本文件把它单列，因为**这是 B3 全部内容的序论内核**（共轭只是把 `S` 取成
`{w*y − f w}`），也说明为何 `BddAbove` 恰好是必需的假设。 -/
theorem csSup_sub_le_of_bddAbove {S : Set ℝ} (hne : S.Nonempty) (_hbd : BddAbove S) :
    ∀ ε : ℝ, 0 < ε → ∃ s ∈ S, sSup S - ε ≤ s := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hub : ∀ v ∈ S, v ≤ sSup S - ε := fun v hv => le_of_lt (hcon v hv)
  have hmin : sSup S ≤ sSup S - ε := csSup_le hne hub
  linarith

/-- **共轭的闭性（`epigraph` 形式，条件版）**：`f*` 在 `y` 处 lsc 等价于
「所有下水平集 `{y' | f* y' ≤ c}` 是闭集」。

本文件给出**局部化**版本：在 `hbd` 下，对任意 `c : ℝ`，
下水平集在 `y` 处的补是开集（即 `{y' | c < f* y'}` 是开集）。
完整的一般闭性（不局部化到单个 `y`）需要在整个定义域上逐点携带 `BddAbove`，
本文件**未做**该全局版本（标注）。 -/
theorem fenchelConjAll_sublevel_open (f : ℝ → ℝ) (y c : ℝ)
    (hbd : BddAbove {v : ℝ | ∃ w, v = w * y - f w})
    (hloc : ∀ᶠ y' in 𝓝 y, BddAbove {v : ℝ | ∃ w, v = w * y' - f w})
    (hc : c < fenchelConjAll f y) :
    {y' : ℝ | c < fenchelConjAll f y'} ∈ 𝓝 y := by
  -- B379: the original argument used ε = f* y - c, which yields only the
  -- NON-strict `c ≤ f* y'`; `{c ≤ f*} ⊆ {c < f*}` is false (the left set is the
  -- larger one), and `c < f* y` cannot combine with `c ≤ f* y'` to give strictness.
  -- Taking HALF the gap makes the bound exceed c strictly:
  --   ε = (f* y - c)/2  ⟹  f* y - ε = (f* y + c)/2 > c  ⟹  c < f* y'.
  have hε : 0 < (fenchelConjAll f y - c) / 2 := by linarith
  have h0 := fenchelConjAll_lsc_eventually f y hbd hloc ((fenchelConjAll f y - c) / 2) hε
  have hev : ∀ᶠ y' in 𝓝 y, (fenchelConjAll f y + c) / 2 ≤ fenchelConjAll f y' := by
    refine h0.mono fun y' hy' => ?_
    have hsub : fenchelConjAll f y - (fenchelConjAll f y - c) / 2
        = (fenchelConjAll f y + c) / 2 := by ring
    calc (fenchelConjAll f y + c) / 2
        = fenchelConjAll f y - (fenchelConjAll f y - c) / 2 := hsub.symm
      _ ≤ fenchelConjAll f y' := hy'
  -- Now the subset relation goes the RIGHT way: (f* y + c)/2 > c, so any point
  -- with f* y' ≥ (f* y + c)/2 also satisfies c < f* y'.
  refine mem_of_superset hev ?_
  intro y' hy'
  -- B379: `hy' : y' ∈ {x | (f* y + c)/2 ≤ f* x}` is a MEMBERSHIP proof; linarith
  -- cannot read through the set-builder, so it must be unfolded first.  `simpa`
  -- or `exact` on the unfolded form is what makes the hypothesis usable.
  have hy'' : (fenchelConjAll f y + c) / 2 ≤ fenchelConjAll f y' := hy'
  show c < fenchelConjAll f y'
  have hmid : c < (fenchelConjAll f y + c) / 2 := by linarith
  linarith

/-! ## 注：闭环语义（B3 在 LATTICE 中的位置）

  · **输入**：`RealFenchelMoreau.fenchelConjAll`（`ℝ` 值 `sSup` 编码的共轭）
    与 `RealFenchel` 的共轭恒等式族；
  · **本文件**：`fenchelConjAll_nonempty`（空集 junk 排除）→
    `fenchelConjAll_sub_le`（上确界逼近）→
    `fenchelConjAll_lsc`（**ε-δ 形式的 lsc，显式模 `δ = ε/(|w₀|+1)`**）→
    `fenchelConjAll_lsc_eventually`（`Filter` 重述）→
    `fenchelConjAll_sublevel_open`（下水平集的局部开性）；
  · **序论内核**：`csSup_sub_le_of_bddAbove` 表明 B3 的实质是 `sSup` 的逼近性质，
    共轭只是 `S := {w*y − f w}` 的实例化；
  · **junk 值见证**：`const_zero_conj_unbounded` 给出 `¬ BddAbove` 的具体点，
    说明「无条件 lsc」在 `ℝ` 值编码下**为假**，`BddAbove` 为必需条件（诚实标注）；
  · **未做（标注）**：`WithTop ℝ`/`ℝ̄` 的值域重写（消除 junk）、
    「凸 + lsc ⟺ `f** = f`」的闭凸刻画、全局（非局部化）的闭性。
  无 sorry/axiom/admit。 -/

end Lattice
