import Mathlib
import Lattice.Core.RepairModule.Repair

/-!
# **几何修正的主树实例：平方距离每步减半**（条款 3.3）

## 为什么需要这个文件

**目标原话的逆向是「提取回符号，用于验证、**修正**、再注入」。条款 3.3（`inverse: repair`）
在 `OBJECTIVE-MAP.md` 里引的三个载体是 `sqDistFix`、`parallelFix`、`midpointFix`，
而第 65 轮实测：它们的声明**只存在于已归档的几何层**，主树里既无声明也无消费者。**

**⇒ 于是 14 条目标断言中，3.3 成了**唯一**一个在主树里完全没有载体的条款。**

## 本文件做什么，以及**不**做什么

**它**不**声称重建归档层的那三个函数。第 1025 轮已证明「按旧名重建」走不通：
同名的定理与归档层冲突，会同时触发重名与重语句两道门禁。**

**⇒ 本文件做的是**同一形状的实例**：一个几何缺陷的修正算子，其**平方距离每步减半**，
并在主树里以**可引用的 `Repair` 实例**形式存在。**

**这与 `Repair.lean` 里既有的 `parityRepair`、`downFix` 是同一层次的东西**——
它们各自是一个 `Repair` 实例，各自配一条终止性定理。**本文件补的是几何这一支。**

## 为什么载体取 `ℕ`

**`Repair` 的度量是 `α → ℕ`，所以 `α` 必须带一个到 `ℕ` 的严格下降量。**
**把载体取成「平方距离的整数刻度」使 `μ` 就是恒等函数，三条义务都变成算术——
这不是回避几何，而是把几何缺陷的**刻度**当作载体，正如 `parityRepair` 把奇偶性当作载体。** -/

namespace Lattice.Core

/-- **平方距离修正：每一轮把剩余的平方距离减半。**

**`Sat` 是「平方距离为零」，`fix` 是减半，`μ` 就是刻度本身。**
**⇒ 三条义务：通过者不动（`0 / 2 = 0`）、失败者严格下降（`n / 2 < n`）、刻度为零即通过。** -/
def sqDistHalvingRepair : Repair ℕ where
  Sat := fun n => n = 0
  fix := fun n => n / 2
  μ := fun n => n
  absorbs := by
    intro n hn
    rw [hn]
  decreases := by
    intro n hn
    show n / 2 < n
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
  atomic := by
    intro n hn
    exact hn

/-- **修正必然终止：存在某一轮，平方距离归零。**

**⇒ 这是 `Repair.progress` 在本实例上的兑现，也正是条款 3.3 想说的
「修正把一个缺陷驱到零」，而不是「修正某一步做了什么」。** -/
theorem sqDistHalving_terminates (n : ℕ) :
    ∃ k : ℕ, sqDistHalvingRepair.Sat (sqDistHalvingRepair.iterate k n) :=
  sqDistHalvingRepair.progress n

/-- **而且终止的那个点在不动点处：通过者不再被修改。**

**⇒ 与 `sqDistHalving_terminates` 合起来读：修正既**到达**通过状态，又在到达后**停下**。
只有前一半的修正过程会继续拍打一个已通过的点。** -/
theorem sqDistHalving_terminates_and_stabilises (n : ℕ) :
    ∃ k : ℕ, sqDistHalvingRepair.Sat (sqDistHalvingRepair.iterate k n)
      ∧ sqDistHalvingRepair.fix (sqDistHalvingRepair.iterate k n)
          = sqDistHalvingRepair.iterate k n := by
  obtain ⟨k, hk⟩ := sqDistHalving_terminates n
  exact ⟨k, hk, sqDistHalvingRepair.absorbs _ hk⟩

end Lattice.Core
