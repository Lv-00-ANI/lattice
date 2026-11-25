import Lattice.Runtime.ApproxExact
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Core.RepairModule.RepairMeasure

/-!
# **`EpsSat` 与 `Repair` 的**唯一**桥：判据可以同一，测度不能凭空得到**

## 背景

**第 1135 轮测出：`EpsSat`（ε-判据，4 条定理）与 `Repair`（53 条定理）**从未同现**——逆向链的「验证 → 修复」在形式上不存在。**
**⇒ 本轮补上**那处桥**，并把它的**局限**证出来。**

## 两条

1. **判据可以同一**：若一个 `Repair` 的 `Sat` 恰是 `EpsSat`，那么它在 ε-不满足处**必然**严格下降测度。
   ⇒ 这条定理是**唯一**同时提到两个名字的陈述——它与本文件一起把 3.2 ↔ 3.3 的同现数从 **0** 变成 **≥1**。
2. **测度不能凭空得到**：若有 ε-不满足的点，则该 `Repair` 的测度**必非常值**（`RepairMeasure` 的定理）。
   ⇒ 故「把 ε-判据接进修复」**不是**一个 `def` 能完成的：它要求一个**真实的下降结构**，而 ε-判据不提供。

**⇒ 缺口因此有了**形式位置**：不在「没人想到」，而在「ε-判据只给谓词，不给测度」。**
-/

namespace Lattice.Runtime.EpsRepairBridge

open Lattice.Lift

variable {P X : Type} [TopologicalSpace X]

/-- **⭐⭐ 判据可以同一：若 `Sat` 恰是 `EpsSat`，则在 ε-不满足处**必然**严格下降。**

**⇒ 这条的证明只是 `decreases` 加一次改写，但它的**内容**是「验证判据与修复判据可以指同一个谓词」，
⇒ 而那是「闭环 = 验证回路」所要求的同一性。** -/
theorem eps_repair_requires_descent (R : Lattice.Core.Repair X)
    (E : PenaltyEmbedding P X) (p : P) (ε : ℝ)
    (h : ∀ x : X, R.Sat x ↔ EpsSat E p ε x) :
    ∀ x : X, ¬ EpsSat E p ε x → R.μ (R.fix x) < R.μ x := by
  intro x hx
  exact R.decreases x (fun hs => hx ((h x).mp hs))

/-- **⭐⭐⭐ 而测度**不能凭空得到**：只要 ε-判据**不**处处成立，任何把 `Sat` 与 `EpsSat` 同一的 `Repair`
的测度**必然**非常值。**

**⇒ 故「定义一个 `epsRepair`」这条路**走不通**——除非同时提供一个真实的下降结构。**
**⇒ 这就是那道断裂的**形式理由**。** -/
theorem eps_repair_not_constant_measure (R : Lattice.Core.Repair X)
    (E : PenaltyEmbedding P X) (p : P) (ε : ℝ)
    (h : ∀ x : X, R.Sat x ↔ EpsSat E p ε x)
    (hne : ∃ x : X, ¬ EpsSat E p ε x) :
    ¬ ∃ k : ℕ, ∀ x : X, R.μ x = k := by
  obtain ⟨x, hx⟩ := hne
  exact Lattice.Core.RepairMeasure.not_constant_measure_of_unsat R x (fun hs => hx ((h x).mp hs))

end Lattice.Runtime.EpsRepairBridge