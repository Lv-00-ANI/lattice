import Mathlib

/-!
# LATTICE: Jensen 不等式的一般形式（有限凸组合 / 等号刻画 / 离散条件期望）

本模块把 mathlib 的 `ConvexOn.map_sum_le` / `ConcaveOn.le_map_sum` /
`StrictConvexOn.eq_of_le_map_sum` 等**一般凸组合**引理，包装成 LATTICE 下游可直接调用的
`jensen_` 前缀 API，并补齐三个缺口：

  1. `jensen_finset`：**有限凸组合 Jensen** 的 `Fin k` 权重主入口；
  2. `jensen_eq_of_strictConvexOn`：**严格凸的等号刻画**（等号成立 ⟹ 所有点相同），
     由 `StrictConvexOn.eq_of_le_map_sum` 直接给出，无假设降级；
  3. `jensen_cond_exp`：**离散条件期望（塔性质）形式**的双层和 Jensen，
     即 `f (Σⱼ wⱼ Σᵢ vⱼᵢ pⱼᵢ) ≤ Σⱼ wⱼ Σᵢ vⱼᵢ f (pⱼᵢ)`。

## 诚实边界

- **只做实数一维**：`f : ℝ → ℝ`、权重与点均为 `ℝ`。向量值（`E`/`β` 为一般有序模）版本
  mathlib 已有，本文件**未**重复抽象（`未做`）。
- **未做**：Hölder / Jensen 的向量值版本；连续概率（测度）版
  （mathlib 有 `ConvexOn.map_integral_le`，本文件**未做**重复抽象）；
  含 `0` 权重的精细等号刻画——`jensen_eq_of_strictConvexOn` 要求 `∀ i, 0 < w i`，
  权重可为零时的刻画需要逐点追踪 `w i = 0` 的分量，本文件**未做**，
  也**未提供**该情形的降级版本（两点版 `jensen_two_eq_of_strictConvexOn` 的假设是
  `0 < lam` 与 `lam < 1`，权重严格为正且严格小于 `1`，同样不覆盖零权重）；
  本文件只写出两点、严格权重的特例，含零权重的一般刻画需径用
  mathlib 的 `StrictConvexOn.map_sum_eq_iff`（其对零权重的形式见其文档）。
- 声明名统一 `jensen_` 前缀，避免与 mathlib / 其它 LATTICE 模块撞名。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

/-! ## 1. 有限凸组合 Jensen（主入口） -/

/-- **有限凸组合 Jensen 不等式（`Fin k` 权重版，主入口）**：
凸函数 `f`、权重 `w ≥ 0` 且 `Σ wᵢ = 1`、点 `p i` 任意，则
`f (Σᵢ wᵢ · pᵢ) ≤ Σᵢ wᵢ · f (pᵢ)`。

直接复用 `ConvexOn.map_sum_le`（`t := Finset.univ`，点全在 `Set.univ` 中），
`•` 在 `ℝ` 上由 `smul_eq_mul` 化为 `*`。 -/
theorem jensen_finset {k : ℕ} [Nonempty (Fin k)] {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (w p : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) :
    f (∑ i, w i * p i) ≤ ∑ i, w i * f (p i) := by
  have h := ConvexOn.map_sum_le (t := Finset.univ) (w := w) (p := p) hf
    (fun i _ => hw i) (by simpa using hws) (fun i _ => Set.mem_univ _)
  simpa [smul_eq_mul] using h

/-- **两点 Jensen 不等式**：`0 ≤ lam ≤ 1` 时
`f (lam·x + (1−lam)·y) ≤ lam·f x + (1−lam)·f y`。

取 `ConvexOn` 定义的第二个分量（`hf.2`）直接实例化，比经 `jensen_finset` 的 `Fin 2`
实例化更直接。 -/
theorem jensen_two {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {lam x y : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    f (lam * x + (1 - lam) * y) ≤ lam * f x + (1 - lam) * f y := by
  -- `ConvexOn` 是 `def` 别名（`Convex 𝕜 s ∧ ...`），且 `a b` 是隐式绑定 `⦃a b⦄`；
  -- 目标里出现的是 `1 - lam` 而非独立变量，故先 `obtain` 拆开合取再显式给出 `a`/`b`。
  obtain ⟨-, hconv⟩ := hf
  have h := hconv (x := x) (y := y) (a := lam) (b := 1 - lam)
    (Set.mem_univ x) (Set.mem_univ y) hlam0 (by linarith) (by ring)
  simpa [smul_eq_mul] using h

/-- **两点严格 Jensen 不等式**：`0 < lam < 1` 且 `x ≠ y` 时
`f (lam·x + (1−lam)·y) < lam·f x + (1−lam)·f y`。

取 `StrictConvexOn` 定义的第二个分量直接实例化。 -/
theorem jensen_two_strict {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f)
    {lam x y : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hxy : x ≠ y) :
    f (lam * x + (1 - lam) * y) < lam * f x + (1 - lam) * f y := by
  obtain ⟨-, hconv⟩ := hf
  have h := hconv (x := x) (y := y) (a := lam) (b := 1 - lam)
    (Set.mem_univ x) (Set.mem_univ y) hxy hlam0 (by linarith) (by ring)
  simpa [smul_eq_mul] using h

/-! ## 2. 严格凸的等号刻画 -/

/-- **严格凸 Jensen 的等号刻画（一般 `k` 版，等号 ⟹ 所有点相同）**：
设 `f` 严格凸、权重**严格为正** `w i > 0` 且 `Σ wᵢ = 1`。若 Jensen 取等号
`f (Σᵢ wᵢ·pᵢ) = Σᵢ wᵢ·f (pᵢ)`，则 `∀ i j, p i = p j`。

路线：由 `heq` 反向得到 `Σ wᵢ • f (pᵢ) ≤ f (Σ wᵢ • pᵢ)`，直接喂给 mathlib 的
`StrictConvexOn.eq_of_le_map_sum`（其假设正是 `∀ i ∈ t, 0 < w i`，与 `hw` 精确对齐）。
**未降级**。 -/
theorem jensen_eq_of_strictConvexOn {k : ℕ} [Nonempty (Fin k)] {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ Set.univ f) (w p : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) (hws : ∑ i, w i = 1)
    (heq : f (∑ i, w i * p i) = ∑ i, w i * f (p i)) : ∀ i j, p i = p j := by
  have h' : ∑ i ∈ (Finset.univ : Finset (Fin k)), w i • f (p i)
      ≤ f (∑ i ∈ (Finset.univ : Finset (Fin k)), w i • p i) := by
    simpa [smul_eq_mul] using (le_of_eq heq.symm :
      (∑ i, w i * f (p i)) ≤ f (∑ i, w i * p i))
  exact fun i j => hf.eq_of_le_map_sum (t := Finset.univ) (w := w) (p := p)
    (fun i _ => hw i) (by simpa using hws) (fun i _ => Set.mem_univ _) h'
    (Finset.mem_univ i) (Finset.mem_univ j)

/-- **两点严格凸等号刻画（`jensen_eq_of_strictConvexOn` 的 `k = 2` 特例）**：
`0 < lam < 1` 且 `f (lam·x + (1−lam)·y) = lam·f x + (1−lam)·f y` ⟹ `x = y`。

证明是严格凸定义的直接反证：若 `x ≠ y`，严格凸给出严格 `<`，与等号矛盾。 -/
theorem jensen_two_eq_of_strictConvexOn {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f)
    {lam x y : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (heq : f (lam * x + (1 - lam) * y) = lam * f x + (1 - lam) * f y) : x = y := by
  by_contra hne
  have hlt := jensen_two_strict hf hlam0 hlam1 hne
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## 3. 凹版 Jensen -/

/-- **有限凹组合 Jensen 不等式（一般集合版）**：
凹函数 `f` 在凸集 `s` 上，权重 `w ≥ 0` 且 `Σ wᵢ = 1`，点 `p i ∈ s`，则
`Σᵢ wᵢ · f (pᵢ) ≤ f (Σᵢ wᵢ · pᵢ)`。

复用 `ConcaveOn.le_map_sum`；保留 `hmem` 是为了让 `Real.log`（仅在 `Set.Ioi 0` 上凹）
也能直接使用。 -/
theorem jensen_concave_finset_of_mem {k : ℕ} [Nonempty (Fin k)] {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) (w p : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) (hmem : ∀ i, p i ∈ s) :
    ∑ i, w i * f (p i) ≤ f (∑ i, w i * p i) := by
  have h := ConcaveOn.le_map_sum (t := Finset.univ) (w := w) (p := p) hf
    (fun i _ => hw i) (by simpa using hws) (fun i _ => hmem i)
  simpa [smul_eq_mul] using h

/-- **有限凹组合 Jensen 不等式（`Set.univ` 版）**：`jensen_finset` 的对偶，
与 `jensen_concave_finset_of_mem` 在 `s = Set.univ` 时的特例一致。 -/
theorem jensen_concave_finset {k : ℕ} [Nonempty (Fin k)] {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ Set.univ f) (w p : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) :
    ∑ i, w i * f (p i) ≤ f (∑ i, w i * p i) :=
  jensen_concave_finset_of_mem hf w p hw hws (fun _ => Set.mem_univ _)

/-! ## 4. 离散条件期望（塔性质）形式 -/

/-- **离散条件期望（塔性质）Jensen**：两层有限凸组合
`f (Σⱼ wⱼ · (Σᵢ vⱼᵢ · pⱼᵢ)) ≤ Σⱼ wⱼ · (Σᵢ vⱼᵢ · f (pⱼᵢ))`。

证明分两步：内层对每个 `j` 用 `jensen_finset` 得
`f (Σᵢ vⱼᵢ·pⱼᵢ) ≤ Σᵢ vⱼᵢ·f (pⱼᵢ)`；再以权重 `wⱼ`、点 `qⱼ := Σᵢ vⱼᵢ·pⱼᵢ` 对
`f` 用一次外层 `jensen_finset`，最后逐项乘 `wⱼ ≥ 0` 求和。

这正是「条件期望的凸性」的离散骨架：外层是边缘分布 `w`，内层是条件分布 `v j`。 -/
theorem jensen_cond_exp {kl : ℕ} [Nonempty (Fin kl)] {k : ℕ} [Nonempty (Fin k)]
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (w : Fin kl → ℝ) (hw : ∀ j, 0 ≤ w j) (hws : ∑ j, w j = 1)
    (v : Fin kl → Fin k → ℝ) (hv : ∀ j i, 0 ≤ v j i) (hvs : ∀ j, ∑ i, v j i = 1)
    (p : Fin kl → Fin k → ℝ) :
    f (∑ j, w j * (∑ i, v j i * p j i)) ≤ ∑ j, w j * (∑ i, v j i * f (p j i)) := by
  have hinner : ∀ j, f (∑ i, v j i * p j i) ≤ ∑ i, v j i * f (p j i) :=
    fun j => jensen_finset hf (v j) (p j) (hv j) (hvs j)
  have houter : f (∑ j, w j * (∑ i, v j i * p j i))
      ≤ ∑ j, w j * f (∑ i, v j i * p j i) :=
    jensen_finset hf w (fun j => ∑ i, v j i * p j i) hw hws
  calc f (∑ j, w j * (∑ i, v j i * p j i))
      ≤ ∑ j, w j * f (∑ i, v j i * p j i) := houter
    _ ≤ ∑ j, w j * (∑ i, v j i * f (p j i)) := by
        refine Finset.sum_le_sum ?_
        intro j _
        exact mul_le_mul_of_nonneg_left (hinner j) (hw j)

/-! ## 5. 实例：`log` 的凹性（信息论线衔接） -/

/-- **对数 Jensen（凹版实例）**：权重 `w ≥ 0`、`Σ wᵢ = 1`、`p i > 0` 时
`Σᵢ wᵢ · log (pᵢ) ≤ log (Σᵢ wᵢ · pᵢ)`（即加权几何平均 ≤ 加权算术平均）。

复用 mathlib 的 `strictConcaveOn_log_Ioi`（`Real.log` 在 `Set.Ioi 0` 上严格凹），
经 `jensen_concave_finset_of_mem` 实例化；**未**重复 `RealConvexToolkit` 的初等证法。 -/
theorem jensen_log {k : ℕ} [Nonempty (Fin k)] (w p : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) (hp : ∀ i, 0 < p i) :
    ∑ i, w i * Real.log (p i) ≤ Real.log (∑ i, w i * p i) :=
  jensen_concave_finset_of_mem (strictConcaveOn_log_Ioi.concaveOn) w p hw hws
    (fun i => hp i)

end Lattice
