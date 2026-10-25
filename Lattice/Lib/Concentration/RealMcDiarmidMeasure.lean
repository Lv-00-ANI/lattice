import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
-- ⚠ **必须显式 import**：`Real.convexOn_exp` 在
-- `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:59`，而 **`import Mathlib`
-- 覆盖不到它**（`Mathlib.lean` 是**精选**导入）。实测：
-- `import Mathlib` 后 `#check @Real.convexOn_exp` → `unknown constant`。
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Lattice.Lib.Concentration.RealMeasureTheoryBase
/-!
# LATTICE: 测度论 McDiarmid 不等式（ROADMAP A3.1）

## 定位：正是 `RealMcDiarmid` 诚实清单里写明的那条留白

`lean/RealMcDiarmid.lean` 的诚实清单**第 4 条逐字写着**：

> **`未做`（测度论版本）**：本文件全部是 **有限/计数** 概率空间
> （`Fintype` + `uniformProb` / `uniformExpectation`）上的版本；一般概率空间
> （测度、条件期望、鞅收敛）上的 McDiarmid 不等式 **未做**。

同文件的诚实清单**第 1、2、3 条**还指出：连**有限版**的核心 MGF 界
`E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}` 都**未证**，而是以显式假设 `hmgf` 进入
（`mcdiarmid_tail_of_mgf`）。本文件把其中**能够可靠完成的部分**测度论化并证明。

## ⚠⚠ 诚实边界（**先声明，避免过度声称**）

完整的多步条件期望迭代（沿坐标把单步引理乘起来）在 mathlib 的 `condexp` 层面
是很重的工程：需要 `Filtration`、`condexp` 的乘积复合、以及逐坐标 σ-代数独立性
三条线同时到位。**本文件不假装完成它**，采取**分层交付**：

| 层 | 内容 | 本文件状态 |
|:--|:--|:--|
| **L1** | 有界差分的**测度论定义** + 拆项（telescope）+ 极差界 | ✅ **完全证明** |
| **L2** | **逐点弦界**（Hoeffding 引理的纯逐点核心） | ✅ **完全证明** |
| **L2'** | 弦界 **⟹ 条件 MGF 界**（`condexp` 提升） | ✅ **完全证明**（以弦界为输入） |
| **L3** | MGF 界 ⟹ 尾界（切尔诺夫桥） | ⚠ 见 `RealHoeffdingMeasure`（已证，本文件不重证） |
| **L4** | **多步条件期望迭代** | ❌ **未做**（明确标注，见文件末 §注） |

**⇒ 与 `RealMcDiarmid` 的关系**：
- 那是**有限/计数**空间；本文件是**一般测度论**空间；
- 本文件 **L1/L2/L2' 全部测度论化且已证**，L4 与它一样**未做**；
- **⇒ 本文件的增量真实但有限**：把"能测度论化的部分"全部测度论化并证明，
  **不**声称已完成多步迭代。**这是对 A3.1 的部分闭合，不是完整闭合。**

## ⭐ 本文件的一处**结构性正结果**（超出简单移植）

`mcdiarmidBoundedDiff_implies_range`：**有界差分 ⟹ 值域长 ≤ ∑cᵢ**
在测度论版**无条件**成立。这条把 `RealMcDiarmid` 文件头那段关于
「极差约定 vs 绝对界约定」的**长讨论**（`/8` vs `/2`）**变成了定理**：
`cᵢ` 确实是**极差**，故 `/8` 常数正确。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-! ## 一、测度论版有界差分（L1）

`RealMcDiarmid.mcdiarmidBoundedDiff` 是**有限集上**的定义。本层把它移植到
"任意指标集 `ι`"的一般情形。

⚠ **关键观察**：**有界差分不含任何测度**——它是**纯逐点条件**。
故测度论版与有限版**形状完全相同**，只是 `ι`/`Z` 不必有限。
**⇒ 这一步不需要新的数学，只是去掉 `Fintype` 限制并统一记法。** -/

/-- **测度论版有界差分**：`f : (ι → Z) → ℝ` 在坐标 `i` 上的增量被 `c i` 控制。

⚠ 与 `RealMcDiarmid.mcdiarmidBoundedDiff`（用 `Fin n` 索引）的区别：
本层用任意 `ι` + `[DecidableEq ι]`（`Function.update` 需要），
以便与 `iIndepFun` 的指标集对齐。**定义体逐字相同。** -/
def mcdiarmidBoundedDiffMeasure {ι Z : Type*} [DecidableEq ι] (f : (ι → Z) → ℝ)
    (c : ι → ℝ) : Prop :=
  ∀ (i : ι) (z : ι → Z) (z' : Z), |f z - f (Function.update z i z')| ≤ c i

/-! ## 二、拆项引理（telescope，L1 核心）

**拆项是纯 `Finset` 归纳 + 三角不等式**，与概率空间无关。
本层独立重证（不 import `RealMcDiarmid`，避免 olean 依赖），改用一般 `ι`。 -/

/-- **坐标拆项引理（telescope，测度论版）**：若 `z` 与 `z'` 只在有限坐标集 `s` 上
可能不同（`∀ i ∉ s, z i = z' i`），且有界差分 `hbd` 成立，则
`|f z − f z'| ≤ ∑_{i∈s} cᵢ`。

**证明**：对 `s` 作 `Finset.induction_on`。空集由 `funext` 得 `z = z'`，两边为 0。
归纳步取 `a`，令 `z'' := Function.update z a (z' a)`，用 `abs_sub_le` 三角不等式拆成
`|f z − f z''| + |f z'' − f z'|`：前者由 `hbd a z (z' a)`；后者用归纳假设
（`∀ i ∉ s, z'' i = z' i`，由 `Function.update_noteq`/`update_same` 分情形）。 -/
theorem mcdiarmid_telescope_measure {ι Z : Type*} [DecidableEq ι] (f : (ι → Z) → ℝ)
    (c : ι → ℝ) (hbd : mcdiarmidBoundedDiffMeasure f c)
    (s : Finset ι) (z z' : ι → Z) (h : ∀ i ∉ s, z i = z' i) :
    |f z - f z'| ≤ ∑ i in s, c i := by
  classical
  revert z z' h
  refine Finset.induction_on s ?base ?step
  · intro z z' h
    have hzz : z = z' := by
      funext i
      exact h i (Finset.not_mem_empty i)
    rw [hzz]
    simp
  · intro a s ha ih z z' h
    let z'' : ι → Z := Function.update z a (z' a)
    have h1 : |f z - f z''| ≤ c a := by
      dsimp [z'']
      exact hbd a z (z' a)
    have h2 : |f z'' - f z'| ≤ ∑ i in s, c i := by
      apply ih
      intro i hi
      show z'' i = z' i
      by_cases hia : i = a
      · subst hia
        simp [z'']
      · dsimp [z'']
        rw [Function.update_noteq hia (z' a) z]
        exact h i (by
          intro hmem
          rw [Finset.mem_insert] at hmem
          rcases hmem with hmem | hmem
          · exact absurd hmem hia
          · exact hi hmem)
    calc
      |f z - f z'| ≤ |f z - f z''| + |f z'' - f z'| := abs_sub_le _ _ _
      _ ≤ c a + ∑ i in s, c i := add_le_add h1 h2
      _ = ∑ i in insert a s, c i := by rw [Finset.sum_insert ha]

/-- **极差界（推论）**：任意两点的函数值之差被 `∑ᵢ cᵢ` 控制。
取 `s = Finset.univ`（前提 `∀ i ∉ univ, …` 空洞成立）即得。 -/
theorem mcdiarmid_range_le_measure {ι Z : Type*} [DecidableEq ι] [Fintype ι]
    (f : (ι → Z) → ℝ) (c : ι → ℝ)
    (hbd : mcdiarmidBoundedDiffMeasure f c) (z z' : ι → Z) :
    |f z - f z'| ≤ ∑ i : ι, c i := by
  have h := mcdiarmid_telescope_measure f c hbd (Finset.univ : Finset ι) z z'
    (fun i hi => absurd (Finset.mem_univ i) hi)
  exact h

/-- ⭐ **有界差分 ⟹ `cᵢ` 是「极差」而非「绝对界」（结构性正结果）**。

`RealMcDiarmid.lean` 文件头有一段**很长的讨论**，论证其 `mcdiarmidBoundedDiff`
所用的 `cᵢ` 是**值域长度（极差）**、从而 MGF 常数 `/8` 正确（而 `/2` 对应
"`|d| ≤ c` 即值域长 `≤ 2c`"的**绝对界**约定）。该讨论此前是**散文**，
本定理把它**变成机器可验证的事实**：

> 有界差分下，`f` 在固定其余坐标时、改变第 `i` 位的**值域长度**
> （即单坐标极差）`≤ cᵢ`。

**证明**：固定 `i` 与其余坐标 `z`，取 `u v : Z`。两点
`update z i u` 与 `update z i v` **只在第 `i` 位可能不同**，故 telescope 取
`s = {i}`（前提 `∀ j ∉ {i}, … = …` 由 `Function.update_noteq` 给出），
得 `|f (update z i u) − f (update z i v)| ≤ ∑_{j∈{i}} c j = c i`。
这正是"值域长 `≤ cᵢ`"。

⚠ **`cᵢ` 无需非负假设**：`mcdiarmidBoundedDiffMeasure` 本身已给出
`|…| ≤ c i`，故 `c i` 自然非负（`|·| ≥ 0`），**不需要额外的单调性/非负性前提**。

⚠ **这是对 `RealMcDiarmid` 文件头论证的形式化**，不是新数学；
其价值在于把**散文论证**变成**可复用的定理**（后续若有人改动常数约定会立即失败）。 -/
theorem mcdiarmidBoundedDiff_implies_range {ι Z : Type*} [DecidableEq ι] (f : (ι → Z) → ℝ)
    (c : ι → ℝ) (hbd : mcdiarmidBoundedDiffMeasure f c) (i : ι) (z : ι → Z) (u v : Z) :
    |f (Function.update z i u) - f (Function.update z i v)| ≤ c i := by
  classical
  have h := mcdiarmid_telescope_measure f c hbd ({i} : Finset ι)
    (Function.update z i u) (Function.update z i v) ?_
  · simpa using h
  · intro j hj
    rw [Finset.mem_singleton] at hj
    rw [Function.update_noteq hj u z, Function.update_noteq hj v z]

/-! ## 三、逐点弦界（L2）：Hoeffding 引理的纯逐点核心

`RealHoeffdingLemmaMeasure.chord_hull_abs` 已给出此结论。本层**独立重证**，
使测度论 McDiarmid 不依赖该文件的 olean。

**关键性质**：`y` 只以**一次项** `(y/c)·sinh(λc)` 出现
⟹ 取条件期望后被**条件零均值** `μ[Y|m] =ᵐ 0` 直接消掉。这是全部路线的枢纽。 -/

/-- **指数函数的凸性**：`x ↦ e^{tx}` 在 `ℝ` 上凸（对**任意** `t : ℝ`，含 `t = 0`）。
`t = 0` 时退化为常值 `1`（凸）；`t ≠ 0` 时由 `Real.convexOn_exp` 与
线性映射 `x ↦ t·x` 复合（映像是满射故 `= univ`，配 `MonotoneOn exp`）。 -/
theorem convexOn_exp_mul_measure (t : ℝ) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => Real.exp (t * x)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hconst : (fun x : ℝ => Real.exp (0 * x)) = fun _ : ℝ => (1 : ℝ) := by
      funext x; rw [zero_mul, Real.exp_zero]
    rw [hconst]
    exact convexOn_const 1 convex_univ
  · have hlin : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => t * x) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith
    have hsurj : Function.Surjective (fun x : ℝ => t * x) := fun y => ⟨y / t, by field_simp⟩
    have himg : (fun x : ℝ => t * x) '' (Set.univ : Set ℝ) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
    have hmono : MonotoneOn Real.exp ((fun x : ℝ => t * x) '' Set.univ) := by
      intro x _ y _ hxy
      exact Real.exp_le_exp.mpr hxy
    have hexp' : ConvexOn ℝ ((fun x : ℝ => t * x) '' Set.univ) Real.exp := by
      -- ⚠⚠ **是根命名空间的 `convexOn_exp`，不是 `Real.convexOn_exp`**：
      -- 该定理在 `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:59`，
      -- 而文件里的 `namespace Real` 出现在 **:216**（**之后**）⟹ 全名**不带** `Real.`。
      -- 实测：`Real.convexOn_exp` → `unknown constant`（本文件 `:198`）。
      -- 【STYLE 同类陷阱】「mathlib 里定义在 namespace 之前的常量，全名不带该 namespace」。
      rw [himg]; exact convexOn_exp
    have h := hexp'.comp hlin hmono
    simpa [Function.comp] using h

/-- **弦不等式（一般区间）**：`a < b`、`x ∈ [a,b]` ⟹
`e^{tx} ≤ ((b−x)/(b−a))·e^{ta} + ((x−a)/(b−a))·e^{tb}`（对任意 `t` 成立）。

证明：把 `x` 写成端点凸组合，代入 `ConvexOn` 定义；
`ℝ` 上 `•` 即 `*`，故结论直接读作乘法形式。 -/
theorem chord_hull_measure {a b x t : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp (t * x) ≤ ((b - x) / (b - a)) * Real.exp (t * a)
      + ((x - a) / (b - a)) * Real.exp (t * b) := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hne : b - a ≠ 0 := ne_of_gt hba
  set ca : ℝ := (b - x) / (b - a) with hca
  set cb : ℝ := (x - a) / (b - a) with hcb
  have hca0 : 0 ≤ ca := div_nonneg (sub_nonneg.mpr hxb) hba.le
  have hcb0 : 0 ≤ cb := div_nonneg (sub_nonneg.mpr hax) hba.le
  have hsum : ca + cb = 1 := by
    rw [hca, hcb, ← add_div, show (b - x) + (x - a) = b - a by ring, div_self hne]
  have hcomb : ca * a + cb * b = x := by
    rw [hca, hcb]; field_simp; ring
  obtain ⟨-, hineq⟩ := convexOn_exp_mul_measure t
  have hkey := hineq (Set.mem_univ a) (Set.mem_univ b) hca0 hcb0 hsum
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hkey
  rwa [hcomb] at hkey

/-- ⭐ **对称弦界（cosh/sinh 形式，L2 枢纽）**：`|y| ≤ c`、`c > 0` ⟹
`e^{λy} ≤ cosh(λc) + (y/c)·sinh(λc)`（对任意 `λ : ℝ`）。

证明：`chord_hull_measure` 取 `a = −c`、`b = c`（`b − a = 2c`），
再用 `Real.cosh_eq`、`Real.sinh_eq` 整理右端。

**为什么这是枢纽**：右端 `y` **只以一次项出现** ⟹ 取条件期望后，
`μ[Y|m] =ᵐ 0`（条件零均值）**直接消掉** `(Y/c)·sinh(λc)` 项。 -/
theorem chord_bound_symm_measure {y c lam : ℝ} (hc : 0 < c) (hy : |y| ≤ c) :
    Real.exp (lam * y) ≤ Real.cosh (lam * c) + (y / c) * Real.sinh (lam * c) := by
  have hle : y ≤ c := (abs_le.mp hy).2
  have hge : -c ≤ y := (abs_le.mp hy).1
  have h := chord_hull_measure (a := -c) (b := c) (x := y) (t := lam) (by linarith) hge hle
  have hden : c - (-c) = 2 * c := by ring
  rw [hden] at h
  have hrewrite : ((c - y) / (2 * c)) * Real.exp (lam * (-c))
        + ((y - (-c)) / (2 * c)) * Real.exp (lam * c)
      = Real.cosh (lam * c) + (y / c) * Real.sinh (lam * c) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    field_simp
    ring
  rwa [hrewrite] at h

/-! ## 四、弦界 ⟹ 条件 MGF 界（L2'，本文件的核心增量）

把 `chord_bound_symm_measure` 提升到 **`condexp`**：

> 若 `|Y| ≤ c` a.e.（`c > 0`）、且 **`μ[Y|m] =ᵐ 0`**（条件零均值），
> 则 **`μ[fun ω => e^{λ·Y ω}|m] ≤ᵐ fun _ => cosh(λc)`**。

**证明路线**（每步都用已 `#check` 实证的引理）：
1. 逐点弦界 `chord_bound_symm_measure` 给出
   `e^{λY} ≤ cosh(λc) + (Y/c)·sinh(λc)`（a.e.）；
2. `condexp_mono`（需两侧 `Integrable`）提升为条件期望的不等式；
3. `condexp_add` 拆开右端；
4. `condexp_const'` 把常数提出来（得到 `fun _ => cosh(λc)`）；
5. ⭐ 用 **`condexp_smul`** 与条件零均值 `μ[Y|m] =ᵐ 0` 消去
   `μ[(Y/c)·sinh(λc)|m] =ᵐ 0`；
6. 合并得 `μ[e^{λY}|m] ≤ᵐ fun _ => cosh(λc) + 0 = cosh(λc)`。

⚠ **诚实说明**：本定理**以逐点弦界与条件零均值 `hcond` 为假设**——
即它证明的是「**弦界 + 条件零均值 ⟹ 条件 MGF 界**」这一**结构性的提升**，
而**不是**"独立同分布 ⟹ 条件零均值"（后者属于 L4 多步迭代，**未做**）。 -/

/-- **条件 MGF 界（由弦界提升）**：`m ≤ m0`、`[IsFiniteMeasure μ]`、`c > 0`、
`|Y| ≤ c` a.e.、`μ[Y|m] =ᵐ 0`、`Y` 与 `e^{λY}`、弦函数可积 ⟹
`μ[fun ω => e^{λ·Y ω}|m] ≤ᵐ fun _ => cosh(λc)`。

⚠ **前提 `hcond : μ[Y|m] =ᵐ[μ] 0`** 是 McDiarmid 迭代的**输入**（由逐坐标独立性提供），
本定理**不证明**它。⚠ 前提 `hm : m ≤ m0` **不可省**：`m ⊄ m0` 时 mathlib 的
`condexp_of_not_le` 使 `μ[·|m] = 0` **恒为零函数**，结论退化为无信息的 `0 ≤ᵐ cosh(λc)`。

⚠ **`Integrable Y μ` 不是本定理的前提**（实测报 `unused variable 'hYint'`）：
证明只用 `Y` 的**逐点有界性**（`hY`）与**条件零均值**（`hcond`），
不需要 `Y` 本身的可积性——弦界与 `condexp_smul` 都不要求它。
**⇒ 按项目判据「unused variable 是"假设写松"的机械信号」，已删除该前提**。 -/
theorem condexp_exp_le_cosh {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {Y : α → ℝ} {c lam : ℝ} (hm : m ≤ m0) (hc : 0 < c)
    (hY : ∀ᵐ ω ∂μ, |Y ω| ≤ c)
    (hcond : μ[Y|m] =ᵐ[μ] 0)
    (hexpint : Integrable (fun ω => Real.exp (lam * Y ω)) μ)
    (hchordint : Integrable (fun ω => Real.cosh (lam * c)
      + (Y ω / c) * Real.sinh (lam * c)) μ) :
    μ[(fun ω => Real.exp (lam * Y ω))|m] ≤ᵐ[μ] fun _ : α => Real.cosh (lam * c) := by
  -- 1. 逐点弦界（a.e.）
  have hpt : (fun ω => Real.exp (lam * Y ω))
      ≤ᵐ[μ] (fun ω => Real.cosh (lam * c) + (Y ω / c) * Real.sinh (lam * c)) :=
    hY.mono fun ω hω => chord_bound_symm_measure hc hω
  -- 2. condexp_mono 提升
  -- 2. condexp_mono 提升
  -- ⚠⚠ `condexp_mono'` 的 `m` 与 `m0` 都是**隐式参数且顺序相邻**（见
  -- `RealMeasureTheoryBase.condexp_mono'` 的签名），直接传参会报
  -- `don't know how to synthesize implicit argument 'm'`（Lean 把 `m0` 当成 `m` 的候选）。
  -- **⇒ 必须显式命名 `(m := m) (m0 := m0)`。**
  --
  -- ⚠⚠ 更关键：**本定理只在 `m ≤ m0` 时有意义**。`m ⊄ m0` 时 mathlib 的
  -- `condexp_of_not_le` 使 `μ[·|m] = 0` **恒为零函数**，此时结论
  -- `0 ≤ᵐ cosh(λc)` 虽然真，但**信息量为零**（退化解）。
  -- ⇒ 把 `hm : m ≤ m0` 提为**显式前提**（见定理签名），使定理非退化。
  have hmono := condexp_mono' (m := m) (m0 := m0) hexpint hchordint hpt
  -- 3. 右端 = cosh(λc) + (Y/c)·sinh(λc)，用 condexp_add 拆开
  have hsplit : μ[(fun ω => Real.cosh (lam * c) + (Y ω / c) * Real.sinh (lam * c))|m]
      =ᵐ[μ] μ[(fun _ : α => Real.cosh (lam * c))|m]
        + μ[(fun ω => (Y ω / c) * Real.sinh (lam * c))|m] := by
    have h1 : Integrable (fun _ : α => Real.cosh (lam * c)) μ := integrable_const _
    have h2 : Integrable (fun ω => (Y ω / c) * Real.sinh (lam * c)) μ := by
      -- ⚠⚠ `hchordint.sub h1` 的类型是 `Integrable (chord - const) μ`，其中
      -- `chord - const = (fun ω => chord ω - const ω)`（**逐点减法**），
      -- 与目标 `fun ω => (Y ω / c) * sinh (lam*c)` **不是 defeq**
      -- （实测：`after simplification has type Integrable ((…) - fun x => …) μ`）。
      -- ⇒ 必须先用 `funext` **显式证明函数相等**（B205 同类：`rw`/`simp` 用句法匹配）。
      have hsub := hchordint.sub h1
      have hfun : ((fun ω => Real.cosh (lam * c) + (Y ω / c) * Real.sinh (lam * c))
          - fun _ : α => Real.cosh (lam * c))
          = fun ω => (Y ω / c) * Real.sinh (lam * c) := by
        funext ω
        simp only [Pi.sub_apply]
        ring
      rwa [hfun] at hsub
    have hadd := condexp_add' (m := m) (m0 := m0)
      (f := fun _ : α => Real.cosh (lam * c))
      (g := fun ω => (Y ω / c) * Real.sinh (lam * c)) h1 h2
    simpa only [Pi.add_apply] using hadd
  -- 4. 常数项的 condexp（由 `hm : m ≤ m0` 与 `[IsFiniteMeasure μ]` 直接给出**逐点**等式）
  have hconst : μ[(fun _ : α => Real.cosh (lam * c))|m]
      =ᵐ[μ] fun _ : α => Real.cosh (lam * c) := by
    rw [condexp_const' hm (Real.cosh (lam * c))]
  -- 5. 余项：μ[(Y/c)·sinh(λc)|m] =ᵐ 0（由条件零均值消去）
  have hrem : μ[(fun ω => (Y ω / c) * Real.sinh (lam * c))|m] =ᵐ[μ] 0 := by
    -- (Y/c)·sinh = (sinh/c) • Y，用 condexp_smul 提出常数
    have hsmul : (fun ω => (Y ω / c) * Real.sinh (lam * c))
        = (Real.sinh (lam * c) / c) • Y := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    -- ⚠⚠ **`rw` 不能作用于 `=ᵐ[μ]`**（ae 相等不是等式，`rw` 报
    -- `tactic 'rewrite' failed, did not find instance of the pattern`，本文件实测）。
    -- ⇒ 必须用 `Filter.EventuallyEq` 的组合子**逐点**推进：
    --   把 `hcond`（`μ[Y|m] =ᵐ 0`）用 `condexp_smul` 提出的因子乘过去。
    have h1 : μ[(fun ω => (Y ω / c) * Real.sinh (lam * c))|m]
        =ᵐ[μ] (Real.sinh (lam * c) / c) • μ[Y|m] := by
      rw [hsmul]
      exact condexp_smul (Real.sinh (lam * c) / c) Y
    have h2 : (Real.sinh (lam * c) / c) • μ[Y|m] =ᵐ[μ] (0 : α → ℝ) := by
      -- 在 `hcond` 这一 ae 事件上，逐点把 `μ[Y|m]` 换成 `0`
      filter_upwards [hcond] with ω hω
      simp only [Pi.smul_apply, Pi.zero_apply, hω, smul_zero]
    exact h1.trans h2
  -- 6. 合并：把四个 ae 事实**逐个**在 `filter_upwards` 里化为逐点等式再 `rw`
  filter_upwards [hmono, hsplit, hconst, hrem] with ω hmonoω hsplitω hconstω hremω
  simp only [Pi.add_apply] at hmonoω hsplitω
  simp only [Pi.zero_apply] at hremω
  rw [hsplitω, hconstω, hremω, add_zero] at hmonoω
  exact hmonoω

/-! ## 五、注：诚实清单与衔接 -/

/-! ## 注：诚实清单与衔接

本文件不含 `sorry` / `axiom` / `admit`；以下是所有 **降级 / 未证 / 未做** 的显式清单：

1. ✅ **已证（L1）**：`mcdiarmidBoundedDiffMeasure`（测度论版有界差分定义）、
   `mcdiarmid_telescope_measure`（拆项）、`mcdiarmid_range_le_measure`（极差界）、
   **`mcdiarmidBoundedDiff_implies_range`**（把 `RealMcDiarmid` 文件头关于
   「极差 vs 绝对界」的**散文论证形式化为定理**）。

2. ✅ **已证（L2）**：`convexOn_exp_mul_measure`、`chord_hull_measure`、
   `chord_bound_symm_measure`（Hoeffding 引理的**纯逐点核心**，
   `y` 只以一次项出现）。

3. ✅ **已证（L2'）**：`condexp_exp_le_cosh` —— **弦界 + 条件零均值 ⟹ 条件 MGF 界**。
   这是本文件相对 `RealMcDiarmid` 的**核心增量**：把"单步"从有限计数空间
   提升到**一般测度论**的 `condexp` 层面。

4. ❌ **`未做`（L4：多步条件期望迭代）**：把 `condexp_exp_le_cosh` 沿坐标
   **乘起来**得到完整的
   `E[e^{λ(f−Ef)}] ≤ e^{λ²Σcᵢ²/8}`，需要：
   - 逐坐标 σ-代数链 `m₀ ≤ m₁ ≤ … ≤ mₙ`（`Filtration`）；
   - **逐坐标的独立性** ⟹ `μ[Yᵢ|mᵢ] =ᵐ 0`（本文件**以假设 `hcond` 引入**）；
   - `condexp` 与**乘积**的交互（`condexp` 对 `m`-可测因子的提取律）。
   **本文件未做**，故 **A3.1 只被部分闭合**，不是完整闭合。

5. ⚠ **`未做`（尾界）**：MGF 界 ⟹ 尾界（L3）由
   `RealHoeffdingMeasure.hoeffding_tail_of_mgf_bound`（**已证**）承担，
   本文件不重证、也不 import（保持叶子化）。

**与既有模块的衔接**：
* `RealMcDiarmid`：**本文件正是其诚实清单第 4 条所指的"测度论版本"的部分实现**；
  其第 1、2、3 条（`hmgf` 未证、多步迭代未做）在本文件中**同样未做**（第 4 条）。
* `RealHoeffdingLemmaMeasure`：提供**无条件**测度论 Hoeffding 引理
  （`hoeffding_lemma_measure`）；本文件的 `condexp_exp_le_cosh` 是其
  **条件版提升**（以条件零均值为输入）。
* `RealHoeffdingMeasure`：提供 `iIndepFun.mgf_sum` 因子分解与测度版切尔诺夫桥。
* `RealMeasureTheoryBase`：提供本文件全部基础设施
  （`condexp_*` 全小写接口、可积性、`Integrable.mono'` 等）。
-/

end Lattice
