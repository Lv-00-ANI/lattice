/-
Copyright: LATTICE

# 扁平参数上的损失：逆向回路的权重侧入口

## 为什么这个文件在 `Domains` 而不是 `Core`

**`flatChainAct`（`Core/VariableDerivative.lean`，第 174 轮）给出任意深度的链作用。
而损失函数 `penaltyLoss`／`Holds` 住在 `Domains/Constraints`（第 101 轮起）。**

**⇒ 把两者接起来只能在 `Domains` 层做**：
**`Core` 不知道 `penaltyLoss` 的存在，反过来 `Domains` 可以依赖 `Core`。
这就是分层门禁 I4 的要求，也是这个文件存在的理由。**

## 本文件证明什么

1. `flatPoints`——扁平参数 → 输出点列（与第 138 轮 `netPoints` 同形状）；
2. `flatPoints_eq_trunc`——与 `trunc` 的定义级等式（那条桥）；
3. `flatLoss`——扁平参数上的总损失；
4. ⭐⭐ `flatLoss_eq_zero_iff`——**损失为零 ⟺ 全部（安全）约束被输出点列满足**。

**第 4 条是逆向回路的核心**：它把「训练把损失压到零」与「网络输出满足符号约束」等同起来，
**而这里的网络是【任意深度、宽度可变】的扁平参数栈。**
-/
import Mathlib
import Lattice.Plugins.Extractors.ChainSlot.VariableDerivative
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative
open Lattice.Core

namespace Lattice.Geo

open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss

/-- **扁平参数 → 输出点列**——**与第 138 轮 `netPoints` 同形状**：

`if h : j < K then 第 j 个输入经链作用 else 0`

**⚠ 越界补零与 `trunc` 一致**（第 122 轮），所以后续所有「`trunc` 与损失」的引理都能直接用。** -/
noncomputable def flatPoints {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (g : Fin N → ℝ) (p : Fin K → Pt n) : ℕ → Pt n :=
  fun j => if h : j < K then flatChainAct (N := N) ch off g (p ⟨j, h⟩) else 0

/-- ⭐⭐ **`flatPoints` 就是 `trunc` 作用在逐点链作用上**——**定义级等式，是通往既有损失引理的桥。** -/
theorem flatPoints_eq_trunc {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (g : Fin N → ℝ) (p : Fin K → Pt n) :
    flatPoints (N := N) ch off g p
      = trunc (n := n) (fun i : Fin K => flatChainAct (N := N) ch off g (p i)) := by
  funext j
  simp only [flatPoints, trunc]

/-- **扁平参数上的总损失**。 -/
noncomputable def flatLoss {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (g : Fin N → ℝ) (p : Fin K → Pt n) : ℝ :=
  (cs.map (fun c => penaltyLoss c (flatPoints (N := N) ch off g p))).sum

/-- ⭐⭐ **`flatLoss` 就是 `lossOfActivations` 与逐点链作用的复合**——**通往第 154 轮双条件的桥。** -/
theorem flatLoss_eq_comp {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (g : Fin N → ℝ) (p : Fin K → Pt n) :
    flatLoss ch off cs g p
      = lossOfActivations cs
          (fun i : Fin K => flatChainAct (N := N) ch off g (p i)) := by
  simp only [flatLoss, lossOfActivations, flatPoints_eq_trunc]

/-- ⭐⭐⭐ **扁平参数上的损失为零 ⟺ 全部（安全）约束被输出点列满足**——**逆向回路的核心。**

**与第 155 轮的 `netLossOn_eq_zero_iff` 逐字同构**：
**`list_sum_eq_zero_of_nonneg`（非负性来自第 101 轮）+ `List.forall_mem_map_iff` + 逐条双条件。** -/
theorem flatLoss_eq_zero_iff {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (g : Fin N → ℝ) (p : Fin K → Pt n)
    (hs : ∀ c ∈ cs, SafeBranch c) :
    flatLoss ch off cs g p = 0
      ↔ ∀ c ∈ cs, Holds c (flatPoints (N := N) ch off g p) := by
  have hnonneg : ∀ x ∈ cs.map (fun c => penaltyLoss c (flatPoints (N := N) ch off g p)), 0 ≤ x := by
    intro x hx
    obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
    exact penaltyLoss_nonneg c' _
  have hsum : flatLoss ch off cs g p
      = (cs.map (fun c => penaltyLoss c (flatPoints (N := N) ch off g p))).sum := by
    simp only [flatLoss]
  rw [hsum, list_sum_eq_zero_of_nonneg hnonneg, List.forall_mem_map_iff]
  exact forall_congr' (fun c => forall_congr' (fun _ =>
    penaltyLoss_eq_zero_iff_holds_of_safe c (hs c ‹c ∈ cs›) _))

/-! ## `flatLoss` 对参数可微

## 结构

**`flatLoss = lossOfActivations ∘ 逐点链作用`（`flatLoss_eq_comp`），而**
**`lossOfActivations` 对激活点列可微是第 136 轮已有的（`_nonKink` 版本，第 148 轮）。**

**⇒ 只需要「逐点链作用对参数 `g` 可微」，而那一步与第 139 轮的
`differentiableAt_pointwiseNetActN_params` 逐字同构。** -/

/-- ⭐⭐ **逐点链作用对参数可微**——**`differentiableAt_pi` 逐坐标，
每个坐标用 `flatChainAct_differentiableAt_joint` 与 `h ↦ (h, p i)` 复合。** -/
theorem flatPoints_differentiableAt_params {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (p : Fin K → Pt n) (g : Fin N → ℝ) :
    DifferentiableAt ℝ
      (fun h : Fin N → ℝ => fun i : Fin K => flatChainAct (N := N) ch off h (p i)) g := by
  rw [show (fun h : Fin N → ℝ => fun i : Fin K => flatChainAct (N := N) ch off h (p i))
      = fun h : Fin N → ℝ =>
          fun i : Fin K => flatChainAct (N := N) ch off h (p i) from rfl]
  exact differentiableAt_pi.2 (fun i => by
    have hpair : DifferentiableAt ℝ
        (fun h : Fin N → ℝ => (h, p i)) g :=
      DifferentiableAt.prod differentiableAt_id (differentiableAt_const (p i))
    exact (flatChainAct_differentiableAt_joint ch off g (p i)).comp g hpair)

/-- ⭐⭐⭐ **`flatLoss` 对参数可微**——**把第 174 轮（链作用可微）与第 175 轮（损失＝复合）接起来。**

**⚠ 前提是 `NonKink`（第 147 轮），而不是 `KinkPositive`**：
**`lossOfActivations_differentiableAt_nonKink` 覆盖 `max` 族的正负两侧。** -/
theorem flatLoss_differentiableAt_params {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (p : Fin K → Pt n) (g : Fin N → ℝ)
    (hK : ∀ c ∈ cs, ConstraintIndicesBelow c K)
    (hk : ∀ c ∈ cs, NonKink c K (fun i : Fin K => flatChainAct (N := N) ch off g (p i))) :
    DifferentiableAt ℝ (fun h : Fin N → ℝ => flatLoss ch off cs h p) g := by
  have hcomp : (fun h : Fin N → ℝ => flatLoss ch off cs h p)
      = (fun a : Fin K → Pt n => lossOfActivations cs a)
        ∘ (fun h : Fin N → ℝ =>
            fun i : Fin K => flatChainAct (N := N) ch off h (p i)) := by
    funext h
    exact flatLoss_eq_comp ch off cs h p
  rw [hcomp]
  exact (lossOfActivations_differentiableAt_nonKink cs
    (fun i : Fin K => flatChainAct (N := N) ch off g (p i)) hK hk).comp g
    (flatPoints_differentiableAt_params ch off p g)

/-- ⭐⭐ **逐点链作用对【输入点列】可微**——**由第 159／177 轮的 `differentiableAt_chainAct`。**

**⚠ 这条在第 176 轮曾因 `unknown identifier 'differentiableAt_chainAct'` 失败**——
**排查发现该定理在第 161 轮丢失（第 177 轮恢复），但本节最终【不】依赖它：
输入侧可微性由 `flatChainAct_differentiableAt_joint` 与 `x ↦ (g, x)` 复合得到，更短。** -/
theorem flatPoints_differentiableAt_input {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (g : Fin N → ℝ) (p : Fin K → Pt n) :
    DifferentiableAt ℝ
      (fun r : Fin K → Pt n => fun i : Fin K => flatChainAct (N := N) ch off g (r i)) p := by
  exact differentiableAt_pi.2 (fun i => by
    have hproj : DifferentiableAt ℝ (fun r : Fin K → Pt n => r i) p := by fun_prop
    exact (flatChainAct_differentiableAt_input ch off g (p i)).comp p hproj)

/-- ⭐⭐⭐ **`flatLoss` 对【输入点列】可微**——**与 `_params` 版对称，两边都有了。** -/
theorem flatLoss_differentiableAt_input {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (g : Fin N → ℝ) (p : Fin K → Pt n)
    (hK : ∀ c ∈ cs, ConstraintIndicesBelow c K)
    (hk : ∀ c ∈ cs, NonKink c K (fun i : Fin K => flatChainAct (N := N) ch off g (p i))) :
    DifferentiableAt ℝ (fun r : Fin K → Pt n => flatLoss ch off cs g r) p := by
  have hcomp : (fun r : Fin K → Pt n => flatLoss ch off cs g r)
      = (fun a : Fin K → Pt n => lossOfActivations cs a)
        ∘ (fun r : Fin K → Pt n =>
            fun i : Fin K => flatChainAct (N := N) ch off g (r i)) := by
    funext r
    exact flatLoss_eq_comp ch off cs g r
  rw [hcomp]
  exact (lossOfActivations_differentiableAt_nonKink cs
    (fun i : Fin K => flatChainAct (N := N) ch off g (p i)) hK hk).comp p
    (flatPoints_differentiableAt_input ch off g p)

/-! ## 可实现性（基线情形）：零层链

## 为什么先做零层

**第 178 轮确定了逆向方向不能从损失反推约束，存活的两个候选之一是
「可实现性」：`∃ g, flatLoss ch off cs g p = 0`。**

**⚠ 一般情形【不成立**：`flatChainAct` 是仿射的（每层都是 `flatParamActSafe` 的复合，
而后者对激活是仿射的），所以输出点列落在输入点列的仿射像里；
而符号侧可满足的配置未必在那个像里。**

**⇒ 先从【零层链】做起**：`ch = Chain.idf n` 时作用是恒等，
**所以损失与 `g` 完全无关，可实现性退化为「约束在输入点上成立」。** -/

/-- ⭐⭐ **零层链的作用是恒等**——**定义级。** -/
theorem flatChainAct_idf_simp {N n : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : Fin n → ℝ) :
    flatChainAct (N := N) (Chain.idf n) off g x = x :=
  rfl

/-- ⭐⭐ **零层链的输出点列就是 `trunc` 作用在输入上**——**与 `g` 无关。** -/
theorem flatPoints_idf {N K n : ℕ} (off : ℕ) (g : Fin N → ℝ) (p : Fin K → Pt n) :
    flatPoints (N := N) (Chain.idf n) off g p = trunc (n := n) p := by
  funext j
  simp only [flatPoints, trunc, flatChainAct_idf_simp]

/-- ⭐⭐⭐ **零层链上的损失与参数无关**——**所以「可实现」等价于「输入点列本身满足约束」。** -/
theorem flatLoss_idf_eq {N K n : ℕ} (off : ℕ) (cs : List (GeoConstraint n))
    (g : Fin N → ℝ) (p : Fin K → Pt n) :
    flatLoss (Chain.idf n) off cs g p
      = (cs.map (fun c => penaltyLoss c (trunc p))).sum := by
  simp only [flatLoss, flatPoints_idf]

/-- ⭐⭐⭐ **零层链上的可实现性**——**存在参数使损失为零 ⟺ 输入点列满足全部（安全）约束。**

**这是候选 1 的基线情形，而且它不带任何仿射像的假设**：
**零层链的作用是恒等，所以每一层都没「挡路」。** -/
theorem flatLoss_idf_achievable {N K n : ℕ} (off : ℕ) (cs : List (GeoConstraint n))
    (p : Fin K → Pt n) (hs : ∀ c ∈ cs, SafeBranch c) :
    (∃ g : Fin N → ℝ, flatLoss (Chain.idf n) off cs g p = 0)
      ↔ ∀ c ∈ cs, Holds c (trunc p) := by
  constructor
  · rintro ⟨g, hg⟩
    have h : (cs.map (fun c => penaltyLoss c (trunc p))).sum = 0 := by
      rw [← flatLoss_idf_eq off cs g p]
      exact hg
    have hnonneg : ∀ x ∈ cs.map (fun c => penaltyLoss c (trunc p)), 0 ≤ x := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      exact penaltyLoss_nonneg c' _
    rw [list_sum_eq_zero_of_nonneg hnonneg, List.forall_mem_map_iff] at h
    intro c hc
    exact (penaltyLoss_eq_zero_iff_holds_of_safe c (hs c hc) (trunc p)).mp (h c hc)
  · intro hall
    refine ⟨0, ?_⟩
    rw [flatLoss_idf_eq]
    have hnonneg : ∀ x ∈ cs.map (fun c => penaltyLoss c (trunc p)), 0 ≤ x := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      exact penaltyLoss_nonneg c' _
    rw [list_sum_eq_zero_of_nonneg hnonneg, List.forall_mem_map_iff]
    intro c hc
    exact (penaltyLoss_eq_zero_iff_holds_of_safe c (hs c hc) (trunc p)).mpr (hall c hc)


/-! ## 深度 1 的逆向刻画：存在参数 ⟺ 存在参数使约束成立

## 为什么这一节

**第 175 轮给了 `flatLoss = 0 ↔ 全部约束在输出点列上成立`，
第 178 轮证明【约束本身】不可从损失恢复（`leZero` 与 `ltZero` 共享损失），
第 185–187 轮证明【仿射像】路线在深度 ≥ 2 上不成立。**

**⇒ 深度 1 是唯一还站得住的易情形（第 186 轮的 `flatChainAct_oneLayer_affine`）。
本节把那个情形上的逆向刻画写全。**

## 三条并立

1. **损失为零**：`∃ g, flatLoss … g p = 0`；
2. **约束成立**：`∃ g, ∀ c ∈ cs, Holds c (flatPoints … g p)`；
3. **落在可行集里**：`∃ g, flatPoints … g p ∈ {Φ | ∀ c ∈ cs, Holds c Φ}`。

**三条【等价】。而 1 ↔ 2 是第 175 轮的逐点双条件在存在量词下提升，
2 ↔ 3 只是 `Set` 成员记法的展开。**

**⚠ 这不是新数学，而是把已有的两块【并列】起来——
但并列本身是必要的：它说明「训练把损失压到零」与「存在一个实现符号约束的配置」
在深度 1 上是同一件事，而那正是逆向回路能运行的前提。** -/

/-- ⭐⭐⭐ **深度 1 的可实现性**：**存在参数使损失为零 ⟺ 存在参数使全部（安全）约束在输出点列上成立。**

**由第 175 轮的 `flatLoss_eq_zero_iff` 在存在量词下提升。** -/
theorem flatLoss_achievable_iff {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (p : Fin K → Pt n)
    (hs : ∀ c ∈ cs, SafeBranch c) :
    (∃ g : Fin N → ℝ, flatLoss ch off cs g p = 0)
      ↔ ∃ g : Fin N → ℝ, ∀ c ∈ cs, Holds c (flatPoints (N := N) ch off g p) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (flatLoss_eq_zero_iff ch off cs g p hs).mp hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (flatLoss_eq_zero_iff ch off cs g p hs).mpr hg⟩

/-- ⭐⭐⭐ **同一件事的【集合】形式**：**存在参数使损失为零 ⟺ 存在参数使输出点列落在可行集里。**

**⚠ 这一条把「可实现」写成「输出落在 `{Φ | ∀ c ∈ cs, Holds c Φ}` 里」——
而那正是第 178 轮指出的正确对象（约束列表不可恢复，可行集可以）。** -/
theorem flatLoss_achievable_iff_mem {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (p : Fin K → Pt n)
    (hs : ∀ c ∈ cs, SafeBranch c) :
    (∃ g : Fin N → ℝ, flatLoss ch off cs g p = 0)
      ↔ ∃ g : Fin N → ℝ,
          flatPoints (N := N) ch off g p ∈ {Φ : ℕ → Pt n | ∀ c ∈ cs, Holds c Φ} := by
  rw [flatLoss_achievable_iff ch off cs p hs]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hg⟩

/-- ⭐⭐⭐ **深度 1 的逆向刻画（合并陈述）**——**三条等价并列。**

**「损失为零」「约束成立」「落在可行集里」在深度 1 上是同一件事。** -/
theorem oneLayer_reverse_equivalence {N K n : ℕ} (ch : Chain n n) (off : ℕ)
    (cs : List (GeoConstraint n)) (p : Fin K → Pt n)
    (hs : ∀ c ∈ cs, SafeBranch c) :
    (∃ g : Fin N → ℝ, flatLoss ch off cs g p = 0)
      ↔ (∃ g : Fin N → ℝ, ∀ c ∈ cs, Holds c (flatPoints (N := N) ch off g p))
      ∧ (∃ g : Fin N → ℝ,
          flatPoints (N := N) ch off g p ∈ {Φ : ℕ → Pt n | ∀ c ∈ cs, Holds c Φ}) := by
  constructor
  · intro h
    exact ⟨(flatLoss_achievable_iff ch off cs p hs).mp h,
      (flatLoss_achievable_iff_mem ch off cs p hs).mp h⟩
  · rintro ⟨h, _⟩
    exact (flatLoss_achievable_iff ch off cs p hs).mpr h


/-! ## ⭐⭐⭐ 可达集【严格小于】配置空间：宽度 1 的三点反例

## 问题

**第 194 轮证了「损失为零 ⟺ 全部约束成立」对任意深度成立。
但那是【容易的一半**。难的一半是：**

**一个符号上可满足的配置 `Φ`，是否总能被某个参数向量【实现**（`∃ g, flatPoints … g p = Φ`）？

**⇒ 本节的答案：在最简情形下【不能】。**

## 最简情形：宽度 1、深度 1

**宽度 1、深度 1 时，一层的作用是 `Φ j = w · (p j) + b`——
即 `Φ` 必须是 `p` 的【仿射函数**。】

**⇒ 取三个输入点 `p j = j`（`j = 0,1,2`）与目标 `Φ j = j²`：
由 `j=0` 得 `b = 0`、由 `j=1` 得 `w = 1`、而 `j=2` 要求 `4 = 2`——矛盾。**

**⇒ `Φ j = j²` 是【符号上完全合法**的配置，**但没有任何宽度 1、深度 1 的网络能实现它。**

**⚠ 这正是「符号 ⇄ 权重」困难的【最简精确形式**：
**配置空间比可达集【大**，缺口由网络结构（此处是仿射性）决定。

**⚠ 与第 194 轮的对照**：
**第 194 轮说「损失为零 ⟺ 约束成立」；本节说「约束成立【不】保证可达」。
两者【不矛盾**：前者关于「给定 `g` 时损失与约束的关系」，
后者关于「哪些 `Φ` 有 `g` 与之对应」。

**⚠ 位置说明**：**本节在 `Domains` 而非 `Core`**，
**因为 `Pt` 是 `Domains` 的定义（`Expr.lean` 的 `abbrev Pt n := Lattice.Core.Point ℝ n`），
而 `Core` 不能引用它——这是分层约束，不是选择。** -/

/-- **三个输入点 `p j = j`**（宽度 1）。 -/
def reachThreePoints : Fin 3 → Pt 1 := fun j => fun _ => (j : ℝ)

/-- **目标配置 `Φ j = j²`**——**符号上完全合法，但不是 `p` 的仿射函数。** -/
def reachSquares : ℕ → Pt 1 := fun j => fun _ => (j : ℝ) ^ 2

/-- ⭐⭐ **数学核心：三个点上没有仿射函数匹配平方。** -/
theorem no_affine_fit_squares :
    ¬ ∃ (w b : ℝ), ∀ j : Fin 3, w * (j : ℝ) + b = (j : ℝ) ^ 2 := by
  rintro ⟨w, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num at h0 h1 h2
  linarith

/-- ⭐⭐⭐ **宽度 1、深度 1 的可达集【严格小于】配置空间。**

**`Φ j = j²` 是符号上合法的配置，但没有宽度 1、深度 1 的网络实现它。** -/
theorem not_reachable_width_one :
    ¬ ∃ (N : ℕ) (g : Fin N → ℝ),
        ∀ j : Fin 3,
          flatPoints (N := N) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
            reachThreePoints j
            = reachSquares (j : ℕ) := by
  rintro ⟨N, g, h⟩
  have key : ∀ j : Fin 3, readSlot g 0 * (j : ℝ) + readSlot g 1 = (j : ℝ) ^ 2 := by
    intro j
    have hpt := congrFun (h j) 0
    simp only [flatPoints, flatChainAct, flatChainAct_idf, flatParamActSafe_width_one,
      reachThreePoints, reachSquares, Fin.is_lt, dif_pos] at hpt
    simpa using hpt
  exact no_affine_fit_squares ⟨readSlot g 0, readSlot g 1, key⟩


/-! ## ⭐⭐⭐ 可达集的【正向】下界：任意两个点的配置都可达

## 为什么这一节与第 195 轮互补

**第 195 轮给出否定结果**：**`Φ j = j²` 在三个点上不可达（宽度 1、深度 1）。**

**⇒ 可达集严格小于配置空间。但那不告诉你可达集【有多大】。**

**本节给出第一个下界**：**若输入只有【两个】点，则【任意】目标配置都可达。**

## 宽度 1 的构造

**宽度 1、深度 1 时一层的作用是 `Φ j = w · (p j) + b`。两个点给出两个方程：
`Φ 0 = w p 0 + b`、`Φ 1 = w p 1 + b`。**

**⇒ 只要 `p 0 ≠ p 1`，解是唯一的：`w = (Φ 1 - Φ 0) / (p 1 - p 0)`、`b = Φ 0 - w · p 0`。**

**⇒ 任意两个点的配置都可达——【只要两点不同**。

**⚠ 而 `p 0 = p 1` 时不可达（除 `Φ 0 = Φ 1` 外）：
同一输入不能有两个输出。那是可达性的【第二个**约束，与第 195 轮的仿射性约束不同。** -/

/-- **两个不同输入点、宽度 1** 的显式参数构造。

**`w = (Φ₁ - Φ₀)/(p₁ - p₀)`、`b = Φ₀ - w·p₀`，放进 `g 0`、`g 1`。**

**⚠ 显式给出 `g` 的类型为 `Fin 2 → ℝ`**：`![…]` 的 `Fin` 下标必须能推断，
否则 `readSlot_of_lt` 的 `N` 与 `k` 都无法归一。** -/
theorem two_points_reachable_width_one
    (p₀ p₁ Φ₀ Φ₁ : ℝ) (hp : p₀ ≠ p₁) :
    ∃ (g : Fin 2 → ℝ),
      readSlot g 0 * p₀ + readSlot g 1 = Φ₀
        ∧ readSlot g 0 * p₁ + readSlot g 1 = Φ₁ := by
  have hd : p₁ - p₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  refine ⟨(![(Φ₁ - Φ₀) / (p₁ - p₀), Φ₀ - (Φ₁ - Φ₀) / (p₁ - p₀) * p₀] : Fin 2 → ℝ), ?_, ?_⟩
  · rw [readSlot_of_lt (N := 2) (k := 0) _ (by norm_num),
      readSlot_of_lt (N := 2) (k := 1) _ (by norm_num)]
    norm_num
  · rw [readSlot_of_lt (N := 2) (k := 0) _ (by norm_num),
      readSlot_of_lt (N := 2) (k := 1) _ (by norm_num)]
    norm_num
    field_simp
    ring


/-! ## ⭐⭐⭐ 可达集必须满足输入点之间的仿射关系

## 这是可达性的普遍必要条件

**第 195／196 轮在宽度 1 上给出了可达集的上下界，但那两条都是特例。
正确的刻画应当从【仿射映射的结构】出发。**

**⇒ 关键观察**：**宽 `n`、深 1 的一层实现的是 `Φ j = W · p j + b`。
于是对任何系数 `c` 满足**

    Σ c j = 0   且   Σ c j · p j = 0

**必有**

    Σ c j · Φ j = W (Σ c j · p j) + (Σ c j) · b = 0

**⇒ 输入点之间的【仿射关系】被输出原样继承。这是可达性的必要条件，
而且它【与宽度无关**——宽度不能突破它。**

## 它如何推出第 195 轮的反例

**取 `p = (0, 1, 2)`（宽 1，即 `Pt 1` 的标量部分）与 `c = (1, -2, 1)`：**

- **`Σ c j = 1 - 2 + 1 = 0`** ✓
- **`Σ c j · p j = 0 - 2·1 + 1·2 = 0`** ✓
- **但 `Σ c j · Φ j = 0 - 2·1 + 1·4 = 2 ≠ 0`**

**⇒ `Φ j = j²` 违反了这个必要条件，因此不可达——与第 195 轮的直接论证一致，
但这里是它的【一般形式**。**

## 为什么按坐标陈述

**`Pt n` 是 `Fin n → ℝ`，其模结构需要实例解析；
按坐标陈述可以完全避开它，而信息量相同。** -/

/-- ⭐⭐⭐ **可达集的仿射关系障碍**——**单层、任意宽度、任意点数。**

**若系数 `c` 同时消掉常数与全部输入点，则它也消掉【任何】可达的输出点列。** -/
theorem oneLayer_respects_affine_relations {N K n : ℕ} (off : ℕ) (g : Fin N → ℝ)
    (p : Fin K → Pt n) (c : Fin K → ℝ)
    (hc : (∑ j, c j) = 0)
    (hp : ∀ i : Fin n, (∑ j, c j * p j i) = 0) :
    ∀ i : Fin n,
      (∑ j, c j * flatParamActSafe (N := N) (a := n) (b := n) off g (p j) i) = 0 := by
  intro i
  simp only [flatParamActSafe]
  have h1 : ∀ j : Fin K,
      c j * ((∑ k : Fin n, readSlot g (slotOf off n k.val i.val) * p j k)
        + readSlot g (off + n * n + i.val))
      = (∑ k : Fin n, c j * readSlot g (slotOf off n k.val i.val) * p j k)
        + c j * readSlot g (off + n * n + i.val) := by
    intro j
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [h1]
  rw [Finset.sum_add_distrib]
  have h2 : (∑ j : Fin K, ∑ k : Fin n,
        c j * readSlot g (slotOf off n k.val i.val) * p j k)
      = ∑ k : Fin n,
          readSlot g (slotOf off n k.val i.val) * (∑ j : Fin K, c j * p j k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h2]
  simp only [hp, mul_zero, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_mul, hc, zero_mul]


/-! ## ⭐⭐⭐ 深度 1 的可达集【精确】刻画：可达 ⟺ 仿射

## 收束第 197／198 轮

**第 197 轮**：**可达的输出继承输入点之间的全部仿射关系**（必要条件）。
**第 198 轮**：**每个 `W, b` 都被某组参数实现**（充分性的根源）。

**⇒ 本节把两者收成一个 `↔`：**

    （存在参数实现 Φ）⟺ （存在仿射映射 W, b 使 Φ j = W · p j + b）

**⚠ 量词的处理**：**结论里出现 `∃ g : Fin (n*n+n) → ℝ` 而非任意 `Fin N → ℝ`。
这不是弱化——`affine_map_realisable` 恰好给出那个宽度，
而「更宽的 `N` 也是可达的」由 `readSlot` 越界读零的性质单独成立（不在此节）。** -/

/-- ⭐⭐⭐ **深度 1 的可达集恰好是仿射映射的限制。**

**这是本路线在深度 1 上的最终形态**：**左边是「参数存在」，右边是「仿射」，
两者等价——所以「符号可满足但不可达」的现象【完全】由仿射性解释。** -/
theorem oneLayer_reachable_exact {K n : ℕ} (hn : 0 < n)
    (p : Fin K → Pt n) (Φ : Fin K → Pt n) :
    (∃ (g : Fin (n * n + n) → ℝ), ∀ j : Fin K,
        flatParamActSafe (N := n * n + n) (a := n) (b := n) 0 g (p j) = Φ j)
      ↔ ∃ (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ), ∀ (j : Fin K) (i : Fin n),
          Φ j i = (∑ k : Fin n, W k i * p j k) + b i := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun k i => readSlot g (k.val * n + i.val),
      fun i => readSlot g (n * n + i.val), ?_⟩
    intro j i
    have := congrFun (hg j) i
    simp only [flatParamActSafe, slotOf, Nat.zero_add] at this
    exact this.symm
  · rintro ⟨W, b, hW⟩
    obtain ⟨g, hg⟩ := affine_map_realisable n hn W b
    refine ⟨g, ?_⟩
    intro j
    funext i
    rw [hg (p j) i, ← hW j i]

end Lattice.Geo
