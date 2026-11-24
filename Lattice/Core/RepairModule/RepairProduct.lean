import Lattice.Core.RepairModule.Repair

/-!
# **两个修复实例的乘积：两侧同时检查、同时修复、测度相加**

## 为什么需要它（本轮是**测量驱动**的，不是猜的）

**第 1081 轮的桥只覆盖标量仿射。本轮先测量了 `Runtime/RepairClosure.lean` 与
`Lib/Compiler/WriteBack.lean` 的两个修复实例能否对齐：**

| 实例 | 载体 | 判据 |
|:--|:--|:--|
| `Runtime/RepairClosure.lean` 里的 `R : Repair Layer` | `Layer = List LinearLayer`（`ℤ`） | 提取后的符号满足约束 |
| `Lib/Compiler/WriteBack.lean::slopeRepair` | `ℕ → Segment`（`ℝ`） | 第 0 段斜率等于目标 |

**⇒ 载体不同、判据不同，**没有可证的交换律**。⇒ 因此不硬做「合成一条链」。**

**⇒ 但两者都是 `Repair` 的实例，而 `Repair` 是一个**接口**。⇒ 接口层有一条真正可推广的事：**
**两个修复可以**并行**运行，只要状态是它们的**积**。**

**⇒ 这条不是类比：它让「符号侧的修复」与「权重侧的修复」可以**同时**进行，而总测度严格下降。
⇒ 而这正是规划 §3.3「验证、修正、再注入」在多约束情形下需要的东西。**
-/

namespace Lattice.Core.RepairModule.RepairProduct

open Lattice.Core

/-- **⭐⭐⭐ 两个修复实例的**乘积**。**

**⇒ `Sat` 要求两侧都满足；`fix` 同时修两侧；`μ` 是两侧测度之和。**
**⇒ 三条义务的可证性依赖一个细节：**当只有一侧失败时**，另一侧由 `absorbs` 保持不变，
故总和仍然严格下降——这正是「并行修复不会因为另一侧的不动而失效」的算术根据。** -/
def repairProd {α β : Type} (R : Repair α) (S : Repair β) : Repair (α × β) where
  Sat p := R.Sat p.1 ∧ S.Sat p.2
  fix p := (R.fix p.1, S.fix p.2)
  μ p := R.μ p.1 + S.μ p.2
  absorbs := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    show (R.fix p.1, S.fix p.2) = (p.1, p.2)
    rw [R.absorbs p.1 hp1, S.absorbs p.2 hp2]
  decreases := by
    intro p hp
    by_cases h1 : R.Sat p.1
    · -- **\u53ea\u6709\u53f3\u4fa7\u5931\u8d25\uff1a\u5de6\u4fa7\u88ab\u5438\u6536\uff0c\u6545\u603b\u548c\u4e0b\u964d\u6765\u81ea\u53f3\u4fa7\u3002**
      have h2 : ¬ S.Sat p.2 := fun h2 => hp ⟨h1, h2⟩
      have hfix1 : R.fix p.1 = p.1 := R.absorbs p.1 h1
      have hdec := S.decreases p.2 h2
      show R.μ (R.fix p.1) + S.μ (S.fix p.2) < R.μ p.1 + S.μ p.2
      rw [hfix1]
      omega
    · by_cases h2 : S.Sat p.2
      · -- **\u53ea\u6709\u5de6\u4fa7\u5931\u8d25\uff1a\u53f3\u4fa7\u88ab\u5438\u6536\u3002**
        have hfix2 : S.fix p.2 = p.2 := S.absorbs p.2 h2
        have hdec := R.decreases p.1 h1
        show R.μ (R.fix p.1) + S.μ (S.fix p.2) < R.μ p.1 + S.μ p.2
        rw [hfix2]
        omega
      · -- **\u4e24\u4fa7\u90fd\u5931\u8d25\uff1a\u4e24\u4e2a\u4e25\u683c\u4e0b\u964d\u76f8\u52a0\u3002**
        have hd1 := R.decreases p.1 h1
        have hd2 := S.decreases p.2 h2
        show R.μ (R.fix p.1) + S.μ (S.fix p.2) < R.μ p.1 + S.μ p.2
        omega
  atomic := by
    intro p hzero
    -- **\u548c\u4e3a\u96f6 \u21d2 \u4e24\u4fa7\u5404\u81ea\u4e3a\u96f6 \u21d2 \u4e24\u4fa7\u90fd\u6ee1\u8db3\u3002**
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp hzero
    exact ⟨R.atomic p.1 h1, S.atomic p.2 h2⟩

/-- **⭐ 乘积的修复是**逐分量**的。** -/
theorem repairProd_fix (R : Repair α) (S : Repair β) (p : α × β) :
    (repairProd R S).fix p = (R.fix p.1, S.fix p.2) := rfl

/-- **⭐⭐ 乘积的测度是**相加**的。** -/
theorem repairProd_measure (R : Repair α) (S : Repair β) (p : α × β) :
    (repairProd R S).μ p = R.μ p.1 + S.μ p.2 := rfl

/-- **⭐⭐ 乘积的判据是**两侧的合取**。** -/
theorem repairProd_sat (R : Repair α) (S : Repair β) (p : α × β) :
    (repairProd R S).Sat p ↔ R.Sat p.1 ∧ S.Sat p.2 := Iff.rfl

/-- **⭐⭐⭐ 乘积修复在 `n` 步之后**仍然是逐分量的**（两侧同步推进）。**

**⇒ 这条说明并行修复**不是「先修一边再修另一边」**，而是同步：每一轮两侧各走一步。
⇒ 而总测度仍然单调下降（由 `decreases` 逐步累积），故两侧**同时**收敛，不需要交替。** -/
theorem repairProd_iterate (R : Repair α) (S : Repair β) (n : ℕ) (p : α × β) :
    (repairProd R S).fix^[n] p = (R.fix^[n] p.1, S.fix^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ k ih =>
      -- **先展开左侧的外层迭代，再用归纳假设，最后展开右侧。**
      rw [Function.iterate_succ_apply', ih p]
      simp only [repairProd]
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

end Lattice.Core.RepairModule.RepairProduct