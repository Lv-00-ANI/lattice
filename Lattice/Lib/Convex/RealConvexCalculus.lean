import Mathlib
import Lattice.Lib.Convex.RealConvexToolkit
/-!
# LATTICE: 凸性保持运算律库（统一入口 + 补齐缺口）

本模块是 LATTICE 凸性运算律的**统一入口**：绝大多数保持律 mathlib 已经具备
（`ConvexOn.add` / `smul` / `sup` / `add_const` / `comp_affineMap` / `convex_epigraph` /
`continuousOn` / `convexOn_mul_log` …），本文件**不重证**，只做 `ccx_` 前缀的薄封装，
并补齐三处 mathlib 缺口：

  1. `ccx_nonneg_combo`：**任意 `Fintype` 上的非负线性组合**
     `Σᵢ cᵢ · fᵢ`（`cᵢ ≥ 0`、每个 `fᵢ` 凸）仍是凸函数；mathlib 只有二元 `add`/一元 `smul`；
  2. `ccx_finset_sup`：**有限族的逐点上确界** `x ↦ sup'ᵢ (fᵢ x)` 仍是凸函数；
     mathlib 只有二元 `ConvexOn.sup`，`Finset` 层面的归纳缺口在此补上；
  3. `ccx_epigraph_iff`：**epigraph 桥** `ConvexOn ℝ univ f ↔ Convex ℝ (ccxEpigraph f)`，
     把「函数凸」与「上镜集凸」在 `ℝ × ℝ` 上双向对齐。

## 诚实边界

- 本文件是**统一入口 + 缺口补齐**，绝大部分凸性保持律在 mathlib 已有
  （`ConvexOn.add/smul/sup/comp_affineMap/...`），本文件的价值是 LATTICE 统一命名
  （`ccx_`）、`Finset` 层面的 `sup` / 非负组合缺口、以及 epigraph 桥。
- **未做**：多变量（`Fin d → ℝ`）版本的完整运算律；`ConvexOn.mul` 的一般条件整理
  （mathlib 已有 `ConvexOn.mul`，但需 `MonovaryOn`，本文件不重新陈述）；
  下半连续性的保持（需要 epigraph 的 `IsClosed` 刻画，见后续模块）。
- **标注（与原始任务描述的修正）**：任务描述曾要求给 `x ↦ f (a·x + b)` 加假设 `a ≥ 0`，
  并称 `a < 0` 时变凹。该说法**不正确**：仿射复合 `f ∘ (x ↦ a·x+b)` 对任意实数 `a`
  都保凸（`f(-x)` 同样凸），故 `ccx_affine_comp` **不带**符号假设（更强的真命题），
  同时另给带 `0 ≤ a` 的弱化别名 `ccx_affine_comp_of_nonneg` 以兼容下游调用。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

/-! ## 1. 薄封装：加法 / 数乘 / 常数平移 -/

/-- **凸函数相加**（`ConvexOn.add` 的统一入口）：`f`、`g` 在 `s` 上凸 ⟹ `x ↦ f x + g x` 在 `s` 上凸。 -/
theorem ccx_add {s : Set ℝ} {f g : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun x => f x + g x) := by
  simpa using hf.add hg

/-- **凸函数非负数乘**（`ConvexOn.smul` 的统一入口）：`0 ≤ c`、`f` 在 `s` 上凸 ⟹
`x ↦ c * f x` 在 `s` 上凸。

注意 `mathlib` 的 `ConvexOn.smul` 中 `c` 是**隐式**参数，故此处用 `ConvexOn.smul hc hf` 形式。 -/
theorem ccx_smul {s : Set ℝ} {f : ℝ → ℝ} (c : ℝ) (hc : 0 ≤ c) (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ s (fun x => c * f x) := by
  simpa [smul_eq_mul] using ConvexOn.smul hc hf

/-- **凸函数加常数**（`ConvexOn.add_const` 的统一入口）：`x ↦ f x + c` 保凸。 -/
theorem ccx_add_const {s : Set ℝ} {f : ℝ → ℝ} (c : ℝ) (hf : ConvexOn ℝ s f) :
    ConvexOn ℝ s (fun x => f x + c) := by
  simpa using hf.add_const c

/-! ## 2. 非负线性组合（核心缺口） -/

/-- **非负线性组合保持凸性（核心缺口）**：`Fintype ι` 上，若每个 `f i` 在 `Set.univ` 上凸、
且系数 `c i ≥ 0`，则 `x ↦ Σᵢ cᵢ · fᵢ x` 在 `Set.univ` 上凸。

证明：对 `Finset` 归纳——`∅` 时是常函数 `0`（`convexOn_const`），
`insert a t` 时用 `ConvexOn.add` 把单项 `c a • f a`（由 `ccx_smul`）与归纳结果相加。 -/
theorem ccx_nonneg_combo {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun x => ∑ i, c i * f i x) := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, 0 ≤ c i) →
      (∀ i ∈ t, ConvexOn ℝ Set.univ (f i)) →
      ConvexOn ℝ Set.univ (fun x => ∑ i in t, c i * f i x) := by
    intro t
    -- 用 `Finset.induction_on`（显式绑定 `a t ha ih`）而非 `induction ... with`：
    -- 后者由方程编译器生成名字，`insert` 分支只接受 2 个显式名。
    refine Finset.induction_on t ?_ ?_
    · intro _ _
      simpa using convexOn_const (0 : ℝ) convex_univ
    · intro a t ha ih hc' hf'
      have ha_mem : a ∈ insert a t := Finset.mem_insert_self a t
      have h1 : ConvexOn ℝ Set.univ (fun x => c a * f a x) :=
        ccx_smul (c a) (hc' a ha_mem) (hf' a ha_mem)
      have h2 : ConvexOn ℝ Set.univ (fun x => ∑ i in t, c i * f i x) :=
        ih (fun i hi => hc' i (Finset.mem_insert_of_mem hi))
           (fun i hi => hf' i (Finset.mem_insert_of_mem hi))
      rw [show (fun x => ∑ i in insert a t, c i * f i x)
            = fun x => c a * f a x + ∑ i in t, c i * f i x from by
            funext x; rw [Finset.sum_insert ha]]
      simpa using h1.add h2
  have := key Finset.univ (fun i _ => hc i) (fun i _ => hf i)
  simpa using this

/-! ## 3. 仿射复合（保留凸性，无符号假设） -/

/-- **仿射复合保凸（核心缺口；无符号假设）**：若 `f` 在 `Set.univ` 上凸，则对**任意**
`a b : ℝ`，`x ↦ f (a · x + b)` 在 `Set.univ` 上凸。

理由：`x ↦ a·x + b` 把线段映为线段，故 `f` 沿映射后的线段仍满足凸性不等式：
`a·(c·x + d·y) + b = c·(a·x + b) + d·(a·y + b)`（用 `c + d = 1`）。

**标注**：与原始任务描述不同，这里**不需要** `0 ≤ a`（`a < 0` 时仍保凸，例如 `f(-x)`）；
原描述「`a < 0` 变凹」不成立。 -/
theorem ccx_affine_comp {f : ℝ → ℝ} {a b : ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (a * x + b)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c d hc hd hcd
  have hkey : a * (c * x + d * y) + b = c * (a * x + b) + d * (a * y + b) := by
    -- 显式展开：右端 = `c*(a*x) + d*(a*y) + (c*b + d*b)`，
    -- 中间项用 `← add_mul` 合并为 `(c+d)*b`，再用 `hcd` 化掉。
    have hb : c * b + d * b = b := by rw [← add_mul, hcd, one_mul]
    ring_nf
    linarith [hb]
  have h' : f (a * (c * x + d * y) + b) ≤ c * f (a * x + b) + d * f (a * y + b) := by
    -- `ConvexOn` 是 `def` 别名（`Convex 𝕜 s ∧ ...`），点号 `.2` 取不到第二分量，
    -- 须先 `obtain` 拆开合取。
    obtain ⟨-, hconv⟩ := hf
    have h := hconv (Set.mem_univ (a * x + b)) (Set.mem_univ (a * y + b)) hc hd hcd
    have heq : c • (a * x + b) + d • (a * y + b) = a * (c * x + d * y) + b := by
      rw [smul_eq_mul, smul_eq_mul]
      exact hkey.symm
    rw [heq] at h
    simpa [smul_eq_mul] using h
  simpa [smul_eq_mul] using h'

/-- **仿射复合保凸（带 `0 ≤ a` 的弱化别名）**：`ccx_affine_comp` 的特例，
保留 `0 ≤ a` 假设以兼容按原始任务描述书写的下游调用。 -/
theorem ccx_affine_comp_of_nonneg {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (a * x + b)) :=
  ccx_affine_comp hf

/-! ## 4. 上确界运算 -/

/-- **逐点最大值保凸**：`f`、`g` 在 `s` 上凸 ⟹ `x ↦ max (f x) (g x)` 在 `s` 上凸。

复用 `ConvexOn.sup`（给出 `f ⊔ g`），并用 `Pi.sup_apply` / `sup_eq_max` 桥接到 `max`。 -/
theorem ccx_sup {s : Set ℝ} {f g : ℝ → ℝ} (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun x => max (f x) (g x)) := by
  have h := ConvexOn.sup hf hg
  simpa only [Pi.sup_apply, sup_eq_max] using h

/-- **有限族逐点上确界保凸（补齐缺口）**：`ι` 非空有限，每个 `f i` 在 `s` 上凸 ⟹
`x ↦ Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)` 在 `s` 上凸。

证明不走 `Finset` 归纳，而是直接用 `Finset.sup'_le` + `Finset.le_sup'` 逐点验证凸性不等式：
对每个 `i` 有 `f i (c•x+d•y) ≤ c•f i x + d•f i y`，再用 `f i x ≤ sup'`、`f i y ≤ sup'`
与 `c, d ≥ 0` 放大。 -/
theorem ccx_finset_sup {ι : Type*} [Fintype ι] [Nonempty ι] {s : Set ℝ} {f : ι → ℝ → ℝ}
    (hf : ∀ i, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => f i x)) := by
  classical
  obtain ⟨hconv_univ, -⟩ := hf (Classical.arbitrary ι)
  refine ⟨hconv_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  apply Finset.sup'_le
  intro i _
  obtain ⟨-, hpoint⟩ := hf i
  -- `a b` 是隐式绑定 `⦃a b⦄`，须显式给出。
  have hpoint' := hpoint (x := x) (y := y) (a := c) (b := d) hx hy hc hd hcd
  have hu : f i x ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => f j x) :=
    Finset.le_sup' (fun j => f j x) (Finset.mem_univ i)
  have hv : f i y ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => f j y) :=
    Finset.le_sup' (fun j => f j y) (Finset.mem_univ i)
  calc f i (c • x + d • y) ≤ c • f i x + d • f i y := hpoint'
    _ ≤ c • Finset.univ.sup' Finset.univ_nonempty (fun j => f j x)
          + d • Finset.univ.sup' Finset.univ_nonempty (fun j => f j y) := by
        refine add_le_add ?_ ?_
        · simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hu hc
        · simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hv hd

/-! ## 5. epigraph 桥 -/

/-- **上镜集（epigraph）**：`ccxEpigraph f := {(x, y) | f x ≤ y} ⊂ ℝ × ℝ`。 -/
def ccxEpigraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | f p.1 ≤ p.2}

/-- **epigraph 桥（双向）**：`f` 在 `Set.univ` 上凸 ⟺ 其上镜集 `ccxEpigraph f` 是 `ℝ × ℝ` 中的凸集。

- `→`：由 `ConvexOn.convex_epigraph` 得到 `{p | p.1 ∈ univ ∧ f p.1 ≤ p.2}` 凸，
  再用 `ccxEpigraph` 的定义化去 `p.1 ∈ univ`。
- `←`：对凸性定义逐点展开，取点 `(x, f x)`、`(y, f y)`（都在 epigraph 内），
  用 `c + d = 1` 把 `c • (x, f x) + d • (y, f y)` 化为 `(c•x + d•y, c•f x + d•f y)`。 -/
theorem ccx_epigraph_iff {f : ℝ → ℝ} :
    ConvexOn ℝ Set.univ f ↔ Convex ℝ (ccxEpigraph f) := by
  constructor
  · intro hf
    have h := hf.convex_epigraph
    simpa [ccxEpigraph] using h
  · intro hf
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ c d hc hd hcd
    -- `(x, f x) ∈ ccxEpigraph f` 是 `f x ≤ f x` 的定义展开，`le_refl _` 不会自动
    -- 展开 `ccxEpigraph`，必须显式 `show` 或 `simp`。
    have hx : (x, f x) ∈ ccxEpigraph f := by
      show f x ≤ f x
      exact le_refl _
    have hy : (y, f y) ∈ ccxEpigraph f := by
      show f y ≤ f y
      exact le_refl _
    have h := hf hx hy hc hd hcd
    have hcomp : c • (x, f x) + d • (y, f y)
        = ((c * x + d * y, c * f x + d * f y) : ℝ × ℝ) := by
      ext <;> simp [smul_eq_mul]
    rw [hcomp] at h
    simpa [ccxEpigraph, smul_eq_mul] using h

/-! ## 6. 开集上的连续性 -/

/-- **开凸集上的凸函数连续**（`ConvexOn.continuousOn` 的统一入口，`E = ℝ`）：
`C` 开、`f` 在 `C` 上凸 ⟹ `f` 在 `C` 上连续。 -/
theorem ccx_continuousOn_open {C : Set ℝ} (hC : IsOpen C) {f : ℝ → ℝ}
    (hf : ConvexOn ℝ C f) : ContinuousOn f C :=
  ConvexOn.continuousOn hC hf

/-! ## 7. 衔接信息论线：`x·log x` 的凸性 -/

/-- **`x ↦ x · log x` 在 `[0, ∞)` 上凸**（回收 `Real.convexOn_mul_log`）。

该函数是 KL / 熵 / `f`-散度一族的核心凸核；`RealConvexToolkit` 用初等 `log` 不等式
给出的是**两点**版本 `mul_log_convex_pair`，本声明给出 mathlib 的**全局**凸性入口。 -/
theorem ccx_mul_log : ConvexOn ℝ (Set.Ici 0) (fun x => x * Real.log x) :=
  Real.convexOn_mul_log

end Lattice
