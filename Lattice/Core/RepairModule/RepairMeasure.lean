import Lattice.Core.RepairModule.Repair

/-!
# **`Repair` **必须**有一个非常值的测度**

## 这条为什么存在

**第 1135 轮测出一处真实断裂：`EpsSat`（验证的 ε-判据）与 `Repair`（修复）在全树**从未同现**。**
**⇒ 当时的修法是「定义一个 `Repair`，其 `Sat` 就是 `EpsSat`」。**

**⇒ 那条修法**不能只靠定义**：`Repair` 的 `decreases` 字段要求「不满足时测度严格下降」。**
**⇒ 而若测度是**常数**，`decreases` 就**不可能**成立——除非**没有任何**不满足的点。**
**⇒ 故本节把这件事证出来：它是「ε-世界与修复世界之间为何有断裂」的**形式理由**，**
**⇒ 而不只是一句观察。**

**⇒ 结论：任何真正有修复动作的 `Repair` 都带一个**非常值**的测度；
⇒ 而 ε-判据**自身不提供**测度——它只给出一个谓词。⇒ 缺口就在这里。**
-/

namespace Lattice.Core.RepairMeasure

variable {α : Type}

/-- **⭐⭐ 若测度是常数，则**没有**不满足的点。**

**⇒ 证明：设 `μ x = k`。若 `¬ Sat x`，`decreases` 给出 `μ (fix x) < μ x = k`，
⇒ 而 `μ (fix x) = k`，矛盾。** -/
theorem sat_of_constant_measure (R : Lattice.Core.Repair α) (k : ℕ)
    (h : ∀ x : α, R.μ x = k) (x : α) : R.Sat x := by
  by_contra hns
  have hdec := R.decreases x hns
  rw [h x] at hdec
  rw [h (R.fix x)] at hdec
  exact Nat.lt_irrefl k hdec

/-- **⭐⭐ 故：只要有**一个**不满足的点，测度就**不是**常数。**

**⇒ 这是上一条的逆否形式，也是「修复必须带测度」的精确陈述。** -/
theorem not_constant_measure_of_unsat (R : Lattice.Core.Repair α) (x : α) (hns : ¬ R.Sat x) :
    ¬ ∃ k : ℕ, ∀ y : α, R.μ y = k := by
  rintro ⟨k, hk⟩
  exact hns (sat_of_constant_measure R k hk x)

end Lattice.Core.RepairMeasure