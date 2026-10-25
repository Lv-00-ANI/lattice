/-
# LATTICE: RealLimitDiscrete — T2 极限离散等效

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）
> 注意：上述分支归属为**不可核对**陈述：文件内无分支标识或提交哈希可验，`git` 历史亦不含原始提交；
> 该分支名仅作为**血缘标注**保留。可核对的落点在 `lean/RealOperatorSplitBridge.lean` 的归属段（同题）。
> U ≡lim Uₙ：dist(U x, Uₙ x) ≤ εₙ 且 εₙ → 0。
> 不是有限域抽样。光滑 U 的 Taylor 形态以显式余项假设接入。

## 诚实边界（**标注**）

1. ⭐ 「一切非线性皆 T2」是**用户公理**，本文件**不证**普适性。
2. ⭐ **`taylor_limit_discrete` 是假设式（余项假设）** —— 它把假设原样还回，
   **未证**任何 Taylor 余项本身；真正的 n 阶余项界由 mathlib
   `taylor_mean_remainder_bound`（`Analysis/Calculus/Taylor.lean:299`）提供，**留待**接线。
3. ⭐ **只有加法组合性（`add_congr`），没有乘法组合性（`mul_congr`）** ——
   **未做**。层与层之间是乘法/复合，故**超出**本文件的组合能力；
   没有它，T2 无法从单层传到多层（多层正是 main 的核心交付）。
-/

import Mathlib.Data.Real.Basic
import Lattice.Lib.Editing.RealOperatorSplit
namespace RealLimitDiscrete

open RealOperatorSplit

/-- 极限离散等效（显式距离，无拓扑依赖）。 -/
structure LimitDiscrete {α β : Type _} (dist : β → β → ℝ) (u : α → β)
    (approx : Nat → α → β) (X : α → Prop) (eps : Nat → ℝ) : Prop where
  bound : ∀ n x, X x → dist (u x) (approx n x) ≤ eps n
  eps_tendsto_zero : ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n < ε

/-- 两个极限离散可加。 -/
theorem add_congr {α β : Type _} [Add β] (dist : β → β → ℝ)
    (hu hv : α → β) (au av : Nat → α → β)
    (X : α → Prop) (eu ev : Nat → ℝ)
    (huL : LimitDiscrete dist hu au X eu)
    (hvL : LimitDiscrete dist hv av X ev)
    (hdist_add : ∀ a b a' b' : β, dist (a + b) (a' + b') ≤ dist a a' + dist b b') :
    LimitDiscrete dist (fun x => hu x + hv x)
      (fun n x => au n x + av n x) X (fun n => eu n + ev n) := by
  refine ⟨?_, ?_⟩
  · intro n x hx
    calc dist (hu x + hv x) (au n x + av n x)
          ≤ dist (hu x) (au n x) + dist (hv x) (av n x) := hdist_add _ _ _ _
        _ ≤ eu n + ev n := add_le_add (huL.bound n x hx) (hvL.bound n x hx)
  · intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨N₁, h₁⟩ := huL.eps_tendsto_zero (ε / 2) hε2
    obtain ⟨N₂, h₂⟩ := hvL.eps_tendsto_zero (ε / 2) hε2
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have e₁ : eu n < ε / 2 := h₁ n (le_trans (le_max_left N₁ N₂) hn)
    have e₂ : ev n < ε / 2 := h₂ n (le_trans (le_max_right N₁ N₂) hn)
    calc eu n + ev n < ε / 2 + ε / 2 := add_lt_add e₁ e₂
      _ = ε := add_halves ε

/-- T1↔T2 桥：已知 D 精确，`D+U ≡lim D+Uₙ`。 -/
theorem t1_t2_bridge {α β : Type _} [Add β] (dist : β → β → ℝ)
    (D U : α → β) (Un : Nat → α → β) (X : α → Prop) (e : Nat → ℝ)
    (hU : LimitDiscrete dist U Un X e)
    (hdist_add : ∀ a b a' b' : β, dist (a + b) (a' + b') ≤ dist a a' + dist b b')
    (hD : ∀ x, dist (D x) (D x) = 0) :
    LimitDiscrete dist (fun x => D x + U x)
      (fun n x => D x + Un n x) X e := by
  refine ⟨?_, hU.eps_tendsto_zero⟩
  intro n x hx
  have h0 : dist (D x + U x) (D x + Un n x)
      ≤ dist (D x) (D x) + dist (U x) (Un n x) := hdist_add _ _ _ _
  rw [hD x, zero_add] at h0
  exact le_trans h0 (hU.bound n x hx)

/-- Taylor 形态（余项假设式，对接 RealTaylorMultivariate）：无 sorry。 -/
theorem taylor_limit_discrete
    (g T : ℝ → ℝ) (eps : Nat → ℝ) (X : ℝ → Prop)
    (hbound : ∀ n t, X t → abs (g t - T t) ≤ eps n)
    (hto : ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n < ε) :
    LimitDiscrete (fun a b : ℝ => abs (a - b)) g (fun _n t => T t) X eps :=
  ⟨hbound, hto⟩

/-! 诚实边界：T2 是分析陈述；「一切非线性皆 T2」是**用户公理**，本文件**不证**普适性。
本文件的 `eps` 为**显式假设**（**标注**）；`taylor_limit_discrete` 的 `hbound` **未证**，
真正的 n 阶余项界**留待**接线 mathlib（见文件头）。 -/

end RealLimitDiscrete
