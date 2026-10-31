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
import Lattice.Core.VariableDerivative
import Lattice.Domains.Constraints.NetLossDerivative

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

end Lattice.Geo
