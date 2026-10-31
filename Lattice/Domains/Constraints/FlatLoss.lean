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

end Lattice.Geo
