import Mathlib
import Lattice.Core.CIC.ParSubstOneDim
import Lattice.Core.CIC.ShiftSubstJointBounded
import Lattice.Core.CIC.ParallelReductionVarying

/-!
# 第 1 层的真正障碍：`shift 0 d` 下的联合律**为假**（阶段 5，第九次否证）

## 第 848 轮标出「层 1 缺失」，本轮查明它为什么不是简单补一条引理

**第 848 轮说 `par-subst` 的绑定层需要 `ParRedV E (shift 0 1 s) (shift 0 1 s')`，
即 `ParRedV` 在 `shift 0 1` 下的闭合性。**

**本轮去证它，`beta` 构造子挡住了：它的结论是 `subst 0 a' b'`，
所以要先证 `shift c d (subst 0 a' b')` 与 `shift c d (subst 0 a'' b'')` 的关系。**

**而这里出现了一个**根本性**的问题：**

## 联合律在 `shift 0 d` 处**为假**

```lean
shift 0 1 (subst 0 (var 5) (lam (var 0) (var 1)))
  =?= subst 1 (shift 0 1 (var 5)) (shift 1 1 (lam (var 0) (var 1)))
-- decide: FALSE
```

**=> 第 847 轮的联合律要求左边用 `shift (c+1) d`，**不能**降到 `shift c d`。
而 `ParRedV` 的 `beta` 需要的恰恰是**从 `c = 0` 开始**的位移。**

**=> 所以「`ParRedV` 在 `shift` 下闭合」这条陈述**不能**通过联合律得到，
而它是否**本身**成立也还不清楚 —— 但本轮的否证表明：**不能靠位移-替换交换来证它**。**

## 这解释了为什么第 826 轮的 `parRedVStruct_shift` 是针对 `ParRedVStruct` 的

**`ParRedVStruct` 是 `Rewritable` 包装，它的结构可能不含 `beta` 那样的 `subst` 结论。
对 `ParRedV` 本身，`beta` 的结论削弱了可交换性。**

## 本文件记录什么

**一条定理：`shift 0 d` 下的联合律为假，带具体见证。**

**=> 这使「`par-subst` 走位移-替换交换」这条路线**彻底关闭**，
并指向两个替代：**

1. **对 `ParRedV` 直接作结构归纳，把 `beta` 情形用 `ParRedV.beta` 的**构造子**处理
   （即证明 `shift` 后的项仍在 `ParRedV` 里，而不要求等式）；**
2. **接受 `beta` 的特殊性：`subst 0 a' b'` 在 `shift 0 d` 下需要 `subst d`，
   这是「位移与替换的**偏移量**不同」，可以写成一个专门的引理。**

**=> 第 2 条是标准 de Bruijn 发展里 `subst` 与 `shift` 的「偏移」关系
（`shift d (subst 0 s t)` 与 `subst d (shift s) (shift t)` 之间差一个偏移），
它比联合律弱，但**没有 cutoff 限制**。** -/

namespace Lattice.Core.CIC

/-- **联合律在 `shift 0 d` 处为假。**

**=> 见证：`shift 0 1 (subst 0 (var 5) (lam (var 0) (var 1)))` 与
`subst 1 (shift 0 1 (var 5)) (shift 1 1 (lam (var 0) (var 1)))` 不等。**

**=> 第 847 轮的联合律左边必须是 `shift (c+1) d`，降到 `c` 就失效。
而 `ParRedV.beta` 需要从 `0` 起的位移，所以交换路线在 `beta` 处断开。** -/
theorem shift_zero_joint_fails :
    (shift 0 1 (subst 0 (.var 5) (.lam (.var 0) (.var 1)))
      ≠ subst 1 (shift 0 1 (.var 5)) (shift 1 1 (.lam (.var 0) (.var 1)))) := by
  decide

end Lattice.Core.CIC
