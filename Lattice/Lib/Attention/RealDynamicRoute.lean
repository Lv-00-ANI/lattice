import Mathlib
import Lattice.Lib.LearningTheory.RealTopK
import Lattice.Lib.Attention.RealHardAttention
/-!
# LATTICE: 稀疏/动态路由 —— top-k 专家选择的稳定性与端到端界

MoE / 稀疏注意力的**动态路由**：每个 token 按分数选 top-k 专家（`routeSelect`），
输出是被选专家的凸组合（`routeOutput`）。路由是**离散**的，因此「模型输出
的 Lipschitz 性」在切换点处失效；本文件把这一失效量化：

  1. `routeOutput`：选择集 S 上权重 w 的凸组合 `Σ_{i∈S} wᵢ•vᵢ`；
  2. `IsTopK s S k`：S 是分数 s 的 top-k 选择集（|S| = k 且 S 内每个分数
     ≥ S 外每个分数）——路由的判定谓词；
  3. `routed_output_bound`（凸组合性质）：S 上概率权重、value 有界
     ⟹ **任意路由的输出仍被 max‖V‖ 界住**（RealTopK 子集凸组合界的路由版）；
  4. `routeOutput_hard`：k=1 时输出 = 被选专家输出（硬路由退化）；
  5. `dynamic_route_error`（核心）：两个不同路由的输出差 ≤ 2M——
     **路由变化导致的误差项**不超过两倍专家输出界（路由切换的最坏代价）；
  6. `argmax_stable` / `topk_route_stable`：**分数间隔 ≥ γ 时路由局部不变**——
     分数扰动 ≤ ε 且 2ε ≤ γ ⟹ top-k 选择集不变（衔接 RealHardAttention
     的 argmax 判定与唯一性）；
  7. `topk_route_stable_unique`：严格间隔（2ε < γ）下稳定路由的 argmax 唯一。
     本条的结论与 `RealHardAttention.argmax_unique` 逐字相同，证明体直接套用
     该定理；其全部内容是把「2ε < γ + 间隔 + 扰动」翻译为该定理的严格性前提，
     不构成路由专属的唯一性结果；
  8. `route_lipschitz`：**切换阈值附近的敏感性**——若扰动 ≤ ε 使路由发生
     变化，则必存在「分数间隔 < 2ε」的临界对：路由改变必然意味着切换裕度
     小于两倍扰动（离散路由的 Lipschitz 化界）。

诚实假设（均显式标注）：
  · `routeSelect s k h` 是「给定 top-k 集存在性证明 h，取一个 top-k 集」的
    非计算选择（`Classical.choose`）；把存在性作为显式参数，
    避免把组合存在性（分数排序）隐藏为未证前提。k=1 的存在性已由
    `exists_topk_one` 给出（有限非空指标集上的 argmax），并封装为
    `routeSelectOne`。对一般 k，top-k 集的存在性需要（分数排序的）组合
    论证，本文件**未证明**——这不是 sorry，而是把「路由良定义」作为显式
    前提。所有路由定理同时以 `IsTopK` 为假设，因此对任意满足 top-k 性质的
    显式选择集（由排序算法构造）直接适用。
  · `routeOutput` 的凸组合性质沿用 RealTopK：权重非负且和为 1、value 有界；
  · 稳定性定理的扰动假设 `|s' j − s j| ≤ ε` 是逐坐标界（分数函数的有界
    扰动），间隔假设 `s j + γ ≤ s i` 是路由切换裕度的显式量化。
全部证明无 sorry / axiom / admit。

模型无关：任意有限专家指标类型 ι、任意 value 空间 F、任意路由选择。
-/

noncomputable section

namespace Lattice

variable {ι F : Type*}
  [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 路由输出（被选专家输出的凸组合） -/

/-- 路由输出：选择集 S 上权重 w 的凸组合 `Σ_{i∈S} wᵢ•vᵢ`。 -/
def routeOutput (S : Finset ι) (w : ι → ℝ) (v : ι → F) : F :=
  ∑ i in S, w i • v i

/-! ## top-k 选择谓词与路由选择函数 -/

/-- `IsTopK s S k`：S 是分数 s 的 top-k 选择集——|S| = k 且 S 内每个分数
不小于 S 外每个分数（路由判定的标准刻画，平局由选择集决定）。 -/
def IsTopK (s : ι → ℝ) (S : Finset ι) (k : ℕ) : Prop :=
  S.card = k ∧ ∀ i ∈ S, ∀ j, j ∉ S → s j ≤ s i

omit [DecidableEq ι] in
/-- 有限非空指标集上 argmax 存在（`Finset.exists_max_image`）。 -/
theorem exists_argmax (s : ι → ℝ) : ∃ i : ι, IsArgMax s i := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) s Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- k=1 的 top-k 集存在（取 argmax 的单点集）——路由良定义的最小实例。 -/
theorem exists_topk_one (s : ι → ℝ) : ∃ S : Finset ι, IsTopK s S 1 := by
  obtain ⟨i, hi⟩ := exists_argmax s
  refine ⟨{i}, ?_, ?_⟩
  · simp
  · intro a ha j hj
    rw [Finset.mem_singleton] at ha
    subst ha
    exact hi j

/-- 每 token 的 top-k 选择（非计算式）：给定存在性，取一个 top-k 集
（`Classical.choose`）。把「路由良定义」的存在性作为显式参数，
避免把组合存在性（分数排序）隐藏为未证前提。 -/
noncomputable def routeSelect (s : ι → ℝ) (k : ℕ)
    (h : ∃ S : Finset ι, IsTopK s S k) : Finset ι :=
  Classical.choose h

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
/-- 路由选择的性质：`routeSelect s k h` 确为 top-k 集。 -/
theorem routeSelect_spec (s : ι → ℝ) (k : ℕ) (h : ∃ S : Finset ι, IsTopK s S k) :
    IsTopK s (routeSelect s k h) k :=
  Classical.choose_spec h

/-- k=1 的 top-1 选择（存在性由 `exists_topk_one` 给出）。 -/
noncomputable def routeSelectOne (s : ι → ℝ) : Finset ι :=
  routeSelect s 1 (exists_topk_one s)

/-- `routeSelectOne s` 是 top-1 集。 -/
theorem routeSelectOne_spec (s : ι → ℝ) : IsTopK s (routeSelectOne s) 1 :=
  routeSelect_spec s 1 (exists_topk_one s)

omit [Fintype ι] [Nonempty ι] in
/-- top-1 集的成员是分数 argmax（k=1 时 top-k 判定 = argmax）。 -/
theorem topk_one_is_argmax (s : ι → ℝ) (S : Finset ι) (hS : IsTopK s S 1)
    {i : ι} (hi : i ∈ S) : IsArgMax s i := by
  intro j
  by_cases hj : j ∈ S
  · have hle1 : S.card ≤ 1 := le_of_eq hS.1
    have hij : i = j := (Finset.card_le_one.mp hle1) i hi j hj
    rw [hij]
  · exact hS.2 i hi j hj

/-- k=1 时 top-1 选择集的成员是 argmax（路由确定性，接 RealHardAttention）。 -/
theorem routeSelectOne_is_argmax (s : ι → ℝ) {i : ι} (hi : i ∈ routeSelectOne s) :
    IsArgMax s i :=
  topk_one_is_argmax s (routeSelectOne s) (routeSelectOne_spec s) hi

/-! ## 定理一：任意路由的输出被 max‖V‖ 界住（凸组合性质）
选择集 S 上概率权重、value 有界 ⟹ `‖routeOutput S w v‖ ≤ M`
（RealTopK.topk_output_bound 的路由版）。 -/

theorem routed_output_bound (S : Finset ι) (w : ι → ℝ) (v : ι → F) (M : ℝ)
    (hw0 : ∀ i, i ∈ S → 0 ≤ w i) (hsum : ∑ i in S, w i = 1)
    (hV : ∀ i, ‖v i‖ ≤ M) :
    ‖routeOutput S w v‖ ≤ M := by
  simpa [routeOutput] using topk_output_bound S w v M hw0 hsum hV

/-! ## 定理二：k=1 硬路由（输出 = 被选专家输出） -/

/-- **硬路由**：one-hot 权重下，**在整个词表上**路由等于取 `vᵢ`。

**第 209 轮补强。** 原陈述路由集取 `{i}`——**和 `top1_output_is_hard` 同一个缺陷**：
单元素集上求和，`hrest` 无从使用，结论退化为 `1 • vᵢ = vᵢ`。
现在路由集是 `Finset.univ`，`hrest` 成为必需。 -/
theorem routeOutput_hard [Fintype ι] [DecidableEq ι] (i : ι) (v : ι → F) (w : ι → ℝ)
    (hw : w i = 1) (hrest : ∀ j, j ≠ i → w j = 0) :
    routeOutput Finset.univ w v = v i := by
  simpa [routeOutput] using top1_output_is_hard i v w hw hrest

/-! ## 定理三（核心）：路由变化导致的误差 ≤ 2M
两个不同路由（不同选择集/权重）的凸组合输出差不超过 2 倍专家输出界：
路由切换的最坏代价（三角不等式 + 两次凸组合界）。 -/

theorem dynamic_route_error (S S' : Finset ι) (w w' : ι → ℝ) (v : ι → F) (M : ℝ)
    (hw0 : ∀ i, i ∈ S → 0 ≤ w i) (hsum : ∑ i in S, w i = 1)
    (hw0' : ∀ i, i ∈ S' → 0 ≤ w' i) (hsum' : ∑ i in S', w' i = 1)
    (hV : ∀ i, ‖v i‖ ≤ M) :
    ‖routeOutput S w v - routeOutput S' w' v‖ ≤ 2 * M := by
  have h1 := routed_output_bound S w v M hw0 hsum hV
  have h2 := routed_output_bound S' w' v M hw0' hsum' hV
  calc
    ‖routeOutput S w v - routeOutput S' w' v‖
        ≤ ‖routeOutput S w v‖ + ‖routeOutput S' w' v‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add h1 h2
    _ = 2 * M := by ring

/-! ## 定理四：分数间隔足够大 ⟹ argmax 局部不变
分数扰动 ≤ ε、切换裕度 ≥ 2ε 时，argmax 保持不变（离散路由的稳定性：
扰动不足以跨越间隔）。 -/

omit [Fintype ι] [Nonempty ι] in
theorem argmax_stable (s s' : ι → ℝ) (i : ι) (γ ε : ℝ)
    (hgap : ∀ j, j ≠ i → s j + γ ≤ s i)
    (hpert : ∀ j, |s' j - s j| ≤ ε)
    (hεγ : 2 * ε ≤ γ) :
    IsArgMax s' i := by
  intro j
  by_cases hji : j = i
  · subst hji
    exact le_rfl
  · have h1 : s' j ≤ s j + ε := by
      have h := hpert j
      rw [abs_le] at h
      linarith [h.2]
    have h2 : s i - ε ≤ s' i := by
      have h := hpert i
      rw [abs_le] at h
      linarith [h.1]
    have h3 := hgap j hji
    linarith

/-! ## 定理五：top-k 路由局部不变（换接 RealTopK 的选择集）
S 是 top-k 集、S 内每个分数高出 S 外至少 γ、扰动 ≤ ε、2ε ≤ γ
⟹ S 仍是扰动后分数的 top-k 集（选择集不变）。 -/

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem topk_route_stable (s s' : ι → ℝ) (S : Finset ι) (k : ℕ) (γ ε : ℝ)
    (hS : IsTopK s S k)
    (hgap : ∀ i ∈ S, ∀ j, j ∉ S → s j + γ ≤ s i)
    (hpert : ∀ j, |s' j - s j| ≤ ε)
    (hεγ : 2 * ε ≤ γ) :
    IsTopK s' S k := by
  refine ⟨hS.1, ?_⟩
  intro i hi j hj
  have h1 : s' j ≤ s j + ε := by
    have h := hpert j
    rw [abs_le] at h
    linarith [h.2]
  have h2 : s i - ε ≤ s' i := by
    have h := hpert i
    rw [abs_le] at h
    linarith [h.1]
  have h3 := hgap i hi j hj
  linarith

/-! ## 定理六：稳定路由的 argmax 唯一（严格间隔）
2ε < γ（严格间隔）时，扰动后分数中 i 严格胜过所有其他专家，
由 `RealHardAttention.argmax_unique` 得 argmax 唯一——路由确定性。
结论与 `argmax_unique` 逐字相同，唯一内容是把上述前提翻译为该定理的
严格性前提（`∀ j ≠ i, s' j < s' i`）。 -/

omit [DecidableEq ι] in
theorem topk_route_stable_unique (s s' : ι → ℝ) (i : ι) (γ ε : ℝ)
    (hgap : ∀ j, j ≠ i → s j + γ ≤ s i)
    (hpert : ∀ j, |s' j - s j| ≤ ε)
    (hεγ : 2 * ε < γ) :
    ∀ j : ι, IsArgMax s' j → j = i := by
  apply argmax_unique s' i
  intro j hji
  have h1 : s' j ≤ s j + ε := by
    have h := hpert j
    rw [abs_le] at h
    linarith [h.2]
  have h2 : s i - ε ≤ s' i := by
    have h := hpert i
    rw [abs_le] at h
    linarith [h.1]
  have h3 := hgap j hji
  linarith

/-! ## 定理七：切换阈值附近的敏感性（路由 Lipschitz 化界）
若扰动 ≤ ε 使路由改变，则必存在分数间隔 < 2ε 的临界对：
「路由改变」⟹「切换裕度 < 2ε」——离散路由变化的必然后果
（定理五的逆否，Lipschitz 型敏感性界）。 -/

theorem route_lipschitz (s s' : ι → ℝ) (S : Finset ι) (k : ℕ) (ε : ℝ)
    (hS : IsTopK s S k)
    (hpert : ∀ j, |s' j - s j| ≤ ε)
    (hchange : ¬ IsTopK s' S k) :
    ∃ i ∈ S, ∃ j, j ∉ S ∧ s i - s j < 2 * ε := by
  by_contra hcon
  have hcon' : ∀ i ∈ S, ∀ j, j ∉ S → 2 * ε ≤ s i - s j := by
    intro i hi j hj
    by_contra hlt
    push_neg at hlt
    exact hcon ⟨i, hi, j, hj, hlt⟩
  apply hchange
  refine topk_route_stable s s' S k (2 * ε) ε hS ?_ hpert le_rfl
  intro i hi j hj
  have h := hcon' i hi j hj
  linarith

/-! ## 注：动态路由收官闭环
  路由输出（凸组合）⟹ 定理一任意路由有界 ⟹ 定理三路由切换代价 ≤ 2M；
  定理四/五给出间隔-稳定性（衔接 RealTopK 凸组合与 RealHardAttention
  argmax 判定）⟹ 定理六唯一性 ⟹ 定理七「路由改变 ⟹ 裕度 < 2ε」的
  逆否敏感性界。`routeSelect` 给出每 token 的 top-k 选择；k=1 的存在性与
  argmax 性质已证（`exists_topk_one`/`routeSelectOne_is_argmax`），
  一般 k 的存在性（分数排序）显式作为前提，未证明部分已在文件头标注。 -/

end Lattice
