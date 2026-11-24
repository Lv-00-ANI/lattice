import Lattice.Lib.Compiler.LoopInstance
import Lattice.Lib.Compiler.Chain

/-!
# **逆向链在产物层闭合：修复 → 写回 → 提取 → 验证 + 可观察变化**

## 规划要求什么

**规划 §3.3 的四项（改到的部分 / 保留的部分 / 到达方式 / 失败分支）在第 1047 轮已经交付。
本轮补的是**逆向方向**的闭合（规划 §1.4 / 3.1：权重 → 符号，用于验证、修正、再注入）：**

**⇒ 一条把**产物**放在中间的陈述：把修好的载荷**写回**成产物，再**提取**回来，得到的是**修好的载荷本身**；
它满足约束；而它的**可观察值确实变了**。**

## 为什么这些不是三条平行的事实

**三条事实各自是既有的：**
- 提取忠实：`decodedFamily_ofSegments`（第 1044 轮）；
- 修好者达标：`slopeFix_sat`（第 1047 轮）；
- 可观察变化：`write_back_verifies_and_changes`（第 1047 轮）。

**⇒ 但它们**从未被放在同一条陈述里**，而调用者需要的正是「**同一个**产物同时满足这三件事」。
⇒ 本文件把那一次选择显式化：所有合取项都关于**同一个** `writeBack` 调用。**
-/

namespace Lattice.Lib.Compiler.ReverseChain

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.Chain
open Lattice.Lib.Compiler.WriteBack
open Lattice.Lib.Compiler.RepairPair
open Lattice.Lib.Compiler

/-- **⭐⭐⭐ 两段斜率上的完整逆向链：提取忠实 ∧ 判据成立 ∧ 可观察量改变。**

**⇒ 五个合取项全部关于**同一次**写回：`writeBack (slopeFix a …) dom₁ r` 与
`writeBack (slopeFix b …) dom₂ r`。**
**⇒ 前两项是**提取**（产物 → 载荷），中间两项是**验证**（修好的载荷满足斜率判据），
后两项是**可观察变化**（写回后的产物在该点的求值与原产物不同）。**

**⇒ 这正是「验证、修正、再注入」三件事在同一对象上的**合取**，而不只是三次分别成立。** -/
theorem reverse_chain_twoSlope (a b b₁ c₁ b₂ c₂ : ℝ)
    (hba₁ : b₁ ≠ a) (hba₂ : b₂ ≠ b)
    (dom₁ dom₂ : Lattice.Lib.Compiler.SemDomain) (r : Lattice.Lib.Compiler.CompileRecipe)
    (x₁ x₂ : ℝ) (hx₁ : x₁ ≠ 0) (hidx₁ : segmentIndex r.n x₁ = 0)
    (hx₂ : x₂ ≠ 0) (hidx₂ : segmentIndex r.n x₂ = 0) :
    -- **提取忠实：写回后的产物解回就是修好的载荷。**
    (writeBack (slopeFix a (constFamily b₁ c₁)) dom₁ r).decodedFamily
        = some (slopeFix a (constFamily b₁ c₁))
      ∧ (writeBack (slopeFix b (constFamily b₂ c₂)) dom₂ r).decodedFamily
        = some (slopeFix b (constFamily b₂ c₂))
      -- **判据成立：两侧斜率各自等于目标。**
      ∧ slopeSat a (slopeFix a (constFamily b₁ c₁))
      ∧ slopeSat b (slopeFix b (constFamily b₂ c₂))
      -- **可观察变化：写回后的两个产物在各自的见证点上求值不同。**
      ∧ (writeBack (slopeFix a (constFamily b₁ c₁)) dom₁ r).evalAt x₁
        ≠ (writeBack (constFamily b₁ c₁) dom₁ r).evalAt x₁
      ∧ (writeBack (slopeFix b (constFamily b₂ c₂)) dom₂ r).evalAt x₂
        ≠ (writeBack (constFamily b₂ c₂) dom₂ r).evalAt x₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact decodedFamily_ofSegments (slopeFix a (constFamily b₁ c₁)) dom₁ r
  · exact decodedFamily_ofSegments (slopeFix b (constFamily b₂ c₂)) dom₂ r
  · exact slopeFix_sat a (constFamily b₁ c₁)
  · exact slopeFix_sat b (constFamily b₂ c₂)
  · exact (write_back_verifies_and_changes a b₁ c₁ hba₁ dom₁ r x₁ hx₁ hidx₁).2
  · exact (write_back_verifies_and_changes b b₂ c₂ hba₂ dom₂ r x₂ hx₂ hidx₂).2

end Lattice.Lib.Compiler.ReverseChain