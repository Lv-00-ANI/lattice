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

end Lattice.Geo
