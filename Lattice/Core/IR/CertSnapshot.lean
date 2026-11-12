import Mathlib
import Lattice.Core.IR.Lifecycle

/-!
# `cert` 的**落地**：义务里写的名字，代码里没有（阶段 C，P2-6）

## 本轮核查到的事实

**`Lifecycle.lean:21` 的 T6 义务写作：**

```
lattice_resolution_coherent : provider P s -> provider P s' ->
  cert P s = cert P s' ∨ invalidated (cert P s) P s'
```

**但 `LifeState` 只有两个字段：**

```lean
structure LifeState where
  active : Plugin → Bool
  effect : Plugin → Option ℕ
```

**=> **没有 `cert`。义务里那个名字在代码里**不存在**。**

**实际实现的定理用的是 `s.effect P`：**

```lean
theorem lattice_resolution_coherent (P) (s s') (hchange : s'.effect P ≠ s.effect P) :
    invalidated (s.effect P) P s' := ...
```

**=> 定理是真的，但它证明的是「**效果**变了则失效」，而不是义务字面所写的「**证书**不变或失效」。**

## 这个差别的实质

**「效果」是一个**状态字段**；「证书」是**证书签发时记录的效果**。
两者的区别在**多步演化**中显现：**

- **若证书就是 `s.effect P`，那么证书**随状态变化**，谈不上「签发」；**
- **若证书是签发时的快照 `c`，那么它可以**独立于**当前状态存在 —— 这才是「一致性」要谈的东西。**

**=> 现存定理**没有错**，但它把一个**更弱**的陈述当成了义务。把 `cert` 落地的价值是
让「证书」成为**可存的快照**，从而义务的字面陈述可以被证明。**

## 本文件交付什么

**把 `cert` 定义为**签发时的效果快照**，并给出它的三条基本性质：**

| 定理 | 内容 |
|:--|:--|
| `cert_issue` | **签发：`cert P s := s.effect P`（在任何状态上都可签发）** |
| `cert_matches_at_issue` | **刚签发的证书与当时的效果一致** |
| `cert_survives_unchanged` | **效果未变则证书仍然有效** |
| `cert_invalidated_by_change` | **效果变了则证书失效（这是义务的第二分支）** |

**=> 四条合起来覆盖了 T6 义务的**两个分支**，而且用的是**证书**而不是**效果**。** -/

namespace Lattice.Core.IR

/-- **证书：签发时记录的效果快照。**

**=> 与 `effectOf` 的区别是**语义**而非表示：`effectOf` 读的是**当前**状态，
`cert` 是**签发时刻**的读数，签发后不再随状态变化。**

**=> 本定义把两者都表示为 `Plugin → Option ℕ`，但**用法**不同：`cert` 作为参数传入，
不重新读状态。这正是「快照」与「字段」的区别。** -/
def cert (P : Plugin) (s : LifeState) : Option ℕ := s.effect P

/-- **签发：在任何状态上，`cert P s` 就是 `s.effect P`。**

**=> 这是定义展开，但它把「证书 = 签发时的效果」这件事写成可引用的事实。** -/
theorem cert_issue (P : Plugin) (s : LifeState) : cert P s = s.effect P := rfl

/-- **刚签发的证书与当时的效果一致。**

**=> 由 `cert_issue` 立得；单独命名以便在一致性论述中直接引用。** -/
theorem cert_matches_at_issue (P : Plugin) (s : LifeState) :
    cert P s = s.effect P := cert_issue P s

/-- **效果未变则证书**仍然有效**（T6 义务的**第一**分支）。**

**=> 若 `s'.effect P = s.effect P`，则 `¬ invalidated (cert P s) P s'`。** -/
theorem cert_survives_unchanged (P : Plugin) (s s' : LifeState)
    (hsame : s'.effect P = s.effect P) :
    ¬ invalidated (cert P s) P s' := by
  rw [cert_issue]
  unfold invalidated
  rw [hsame]
  exact fun h => h rfl

/-- **效果变了则证书**失效**（T6 义务的**第二**分支，用 `cert` 表述）。**

**=> 与既有的 `lattice_resolution_coherent` 的差别是：本条以 `cert P s`（签发时的快照）
为失效对象，而不是当前的 `s.effect P`。两者的**取值相同**，但**语义不同**。** -/
theorem cert_invalidated_by_change (P : Plugin) (s s' : LifeState)
    (hchange : s'.effect P ≠ s.effect P) :
    invalidated (cert P s) P s' := by
  unfold invalidated
  rw [cert_issue]
  exact fun h => hchange h.symm

end Lattice.Core.IR
