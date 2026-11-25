import Lattice.Runtime.ApproxExact
import Lattice.Runtime.PenaltyEmbedding

/-!
# **Lean 保证（健全但不精确）与验证（ε-判据）之间的那个缺口**

## 背景

**第 1143 轮的两口径测量里，`8 Lean 保证 ↔ 3.2 验证` 是**唯一**一对在两种词表下都为空的条款：
⇒ 接缝工具按概念词计，它也看不见；条款工具按载体名计，它也看不见。
⇒ 即「正确性由 Lean 保证」与「验证回路」在形式上**是两句话**。**

## 这一条补的

**⇒ 缺口不是修辞，而是**可构造**的：`sound_not_exact` 的 witness `constEmbedding`（`loss ≡ 1`、`Sat ≡ False`）
⇒ **在 `ε = 1` 时满足 `EpsSat`，而其约束**不成立**。**

**⇒ 故「ε-验证通过」**不蕴含**「约束成立」——这正是「健全（sound）但不精确（exact）」在验证词汇里的样子。**

**⇒ 这不是缺陷，而是**为什么需要 ε** 的理由本身：一个精确的判据会要求 `PenaltyExact`，而 `sound_not_exact` 证明了
它不可得；于是验证只能在容差里说话——**而容差一旦说话，就必须知道它不蕴含精确。****
-/

namespace Lattice.Runtime.EpsGap

open Lattice.Lift

/-- **⭐⭐⭐ 缺口定理：那个「健全但不精确」的见证，恰好是一个 ε-验证通过而约束失败的例子。**

**⇒ 三个合取项：**
1. `sound_not_exact`（条款 8 的载体）——**同一个**见证；
2. `EpsSat constEmbedding () 1 ()`（条款 3.2 的载体）——能力容差内通过；
3. `¬ constEmbedding.Sat () ()`——而约束**不成立**。

**⇒ 故本条同时命名两个世界：它就是 `8 ↔ 3.2` 的桥。** -/
theorem sound_not_exact_gives_epsilon_gap :
    (Lattice.Lift.PenaltySound Lattice.Lift.constEmbedding ∧
        ¬ Lattice.Lift.PenaltyExact Lattice.Lift.constEmbedding) ∧
      EpsSat Lattice.Lift.constEmbedding () (1 : ℝ) () ∧
      ¬ Lattice.Lift.constEmbedding.Sat () () := by
  refine ⟨Lattice.Lift.sound_not_exact, ?_, ?_⟩
  · show |Lattice.Lift.constEmbedding.loss () ()| ≤ (1 : ℝ)
    norm_num [Lattice.Lift.constEmbedding]
  · simp [Lattice.Lift.constEmbedding]

/-- **⭐⭐ 推论（可直接引用的形式）：存在一个 ε-判据通过而其约束不成立的设计。**

**⇒ 即「ε-验证通过」**不蕴含**「约束成立」——`EpsSat` 是**必要**的判据，不是**充分**的正确性断言。** -/
theorem epsSat_passing_is_not_correctness :
    ∃ (E : PenaltyEmbedding Unit Unit) (p x : Unit) (ε : ℝ),
      0 ≤ ε ∧ EpsSat E p ε x ∧ ¬ E.Sat p x :=
  ⟨Lattice.Lift.constEmbedding, (), (), 1, by norm_num,
   (sound_not_exact_gives_epsilon_gap).2.1,
   (sound_not_exact_gives_epsilon_gap).2.2⟩

end Lattice.Runtime.EpsGap