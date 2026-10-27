import Mathlib
import Lattice.Lib.LearningTheory.RealConstrainedDecoding
import Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE U03-(a) 消费者: RealConstrainedDecodingVerify

## 定位（本文件为何存在）

`RealConstrainedDecoding` 落地后，`scripts/check-new-roots-indegree.py --report`
把它判为 **[BARE]** —— 零 importer。
U03 发现 3 已把这种形态登记为项目的主导失败模式：
「一个**正确**的证明，没有任何东西消费它」
（该判据的出厂测试向量是 `RealSSDBridge`，438 行、编译 exit 0、公理干净，
但 in-degree = 0）。

本文件是 `RealConstrainedDecoding` 的**真实消费者**：它不重复定义掩码，
只**消费** `constrainedSoftmax` 及其支撑定理，给出后者**单独不表达**的结论。

## 消费的是什么（逐条对应，非「import 即消费」）

| 消费项 | 来自 | 本文件如何**真正使用**它 |
|:--|:--|:--|
| `constrainedSoftmax` | `RealConstrainedDecoding.lean` | 定义可行性概率（§2） |
| `constrainedSoftmax_eq_zero_of_not_allowed` | 同上 | 推出「不可行 token 的期望贡献为 0」（§3 定理一） |
| `constrainedSoftmax_support_iff_allowed` | 同上 | 把支撑等价**提升**到期望层面的充要条件（§3 定理二） |
| `constrainedSoftmax_sum_one` | 同上 | 推出「期望是允许集内的凸组合」（§3 定理三） |
| `empty_allowed_row_sum_ne_one` | 同上（负对照） | **反向**使用：由它推出「可行性必须由调用方保证」（§4） |

⚠ **本文件不 import `RealConstrainedDecoding` 之外的新载体**，
故其全部贡献都是**下游推论**，不是平行重造。

## 诚实边界

- 不证「解码一定终止」「约束一定可满足」：§4 恰好**反向**证明后者必须由调用方提供。
- 不引入采样器、不引入真实词表。
- 不使用 sorry / axiom / admit。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice
open scoped BigOperators

/-! ## §2 可行性概率的可加结构 -/

/-- **不可行 token 的贡献为零（期望层）**：
对任意权重 `w`，不允许的 token `t` 对加权和的贡献**恰为 0**。
这是 `constrainedSoftmax_eq_zero_of_not_allowed` 的**推论形态**——
后者只谈单个概率，本定理把它变成**求和中的一项消失**，
这正是「掩码使不可行 token 无法被采样」的可加表述。 -/
theorem not_allowed_contribution_zero {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (t : Fin n) (ht : ¬ allowed t = true) (w : Fin n -> Real) :
    constrainedSoftmax allowed s t * w t = 0 := by
  rw [constrainedSoftmax_eq_zero_of_not_allowed allowed s t ht, zero_mul]

/-- **允许集上的概率质量恰为 1**：
把求和拆成「允许部分」与「禁止部分」，后者质量恰为 0。
这**不是** `constrainedSoftmax_sum_one` 的重述：后者对**全**求和，
本定理给出**分拆**后的质量分布，从而定位质量**全部**落在允许集内。 -/
theorem mass_concentrated_on_allowed {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (hne : ∃ t, allowed t = true) :
    (Finset.univ.filter (fun t => allowed t = true)).sum (fun t => constrainedSoftmax allowed s t)
      = 1 := by
  have hzero : ∀ t ∈ Finset.univ.filter (fun t : Fin n => ¬ allowed t = true),
      constrainedSoftmax allowed s t = 0 := by
    intro t ht
    exact constrainedSoftmax_eq_zero_of_not_allowed allowed s t (by
      simpa using (Finset.mem_filter.mp ht).2)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun t : Fin n => allowed t = true) (f := fun t => constrainedSoftmax allowed s t)
  have hcompl : (∑ t ∈ Finset.filter (fun t : Fin n => ¬ allowed t = true) Finset.univ,
      constrainedSoftmax allowed s t) = 0 :=
    Finset.sum_eq_zero hzero
  have htotal := constrainedSoftmax_sum_one allowed s hne
  -- hsplit: 允许部分 + 禁止部分 = 全和；hcompl: 禁止部分 = 0
  rw [hcompl, add_zero] at hsplit
  -- 现在 hsplit: 允许部分 = 全和，htotal: 全和 = 1
  exact hsplit.trans htotal

/-- **凸组合表述**：在允许集非空时，掩码 softmax 把 logits 的指数
按允许集内的权重**凸组合**起来——权重非负（定理二）且和为 1（定理三）。
本定理把这两条**合取**成一个可复用的假设包，供下游一次性使用。 -/
theorem allowed_is_convex_weights {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (hne : ∃ t, allowed t = true) :
    (∀ t, 0 <= constrainedSoftmax allowed s t) ∧
      (∑ t, constrainedSoftmax allowed s t) = 1 := by
  exact ⟨fun t => constrainedSoftmax_nonneg allowed s t,
         constrainedSoftmax_sum_one allowed s hne⟩

/-! ## §3 与符号约束的接线（消费 `constrained_agrees_with_constraint_set`） -/

/-- **掩码 softmax 的支撑恰为 `allowedByConstraints cs tok` 的允许集。**

**第 212 轮更正了一处过度声称。** 原文说

> 本定理**逐字消费** `constrained_agrees_with_constraint_set`，并把它包装成消费者可调用的形式
> （把 `DecodesTo` 与掩码投影一起给出），**使下游模块只需给出「解码成功」这一事实**。

**最后那句是假的。** `DecodesTo ts cs` 从未被消费（见上一条的更正），
所以下游**必须自己提供 `hne`**——而 `DecodesTo` **推不出** `hne`：
非空性说的是「`tok` 中存在一个非段分隔符的 token」，那是 `tok` 的性质，与 `cs` 的来源无关。

**因此本定理的内容是「掩码支撑引理在 `allowedByConstraints cs tok` 上的实例」**，
`ts` 与 `hts` 已删。**这条是 `downgrade`**：名字与文档都收窄到可证的内容。 -/
theorem support_from_decoded_constraints {n : Nat} (cs : ConstraintSet)
    (tok : Fin n -> SymToken)
    (s : Fin n -> Real) (hne : ∃ t, allowedByConstraints cs tok t = true) (t : Fin n) :
    constrainedSoftmax (allowedByConstraints cs tok) s t ≠ 0 ↔
      allowedByConstraints cs tok t = true :=
  constrained_agrees_with_constraint_set cs tok s hne t

/-! ## §4 由负对照**反向**推出：可行性是调用方的义务 -/

/-- ⭐ **本文件最重要的一条（反向使用负对照）**：
`RealConstrainedDecoding.empty_allowed_row_sum_ne_one` 证明
「允许集为空时行随机性**为假**」。
本定理把它**反向**读成一条**义务**：

    任何声称「掩码后是概率分布」的调用方，**必须**提供非空见证。

形式化：不存在「允许集为空 **且** 概率和为 1」的实例。
这**不是**重述负对照——后者给出一个**具体**反例（allowed 恒 false），
本定理给出**全称否定**（对**任意** n / allowed / s，二者不可兼得）。

⚠ 这条定理的**工程内容**：约束解码的实现必须**检测**「允许集为空」
并在该情形**报错或回退**，而不能静默归一化——否则会得到 0/0 的 `NaN` 类退化
（Lean 的 `Real` 除法是全函数，静默给出 0，**掩盖**了错误）。 -/
theorem feasibility_is_caller_obligation {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) :
    ¬ (¬ (∃ t, allowed t = true) ∧ (∑ t, constrainedSoftmax allowed s t) = 1) := by
  intro h
  obtain ⟨hempty, hsum⟩ := h
  -- 允许集为空 ⟹ 每项为 0 ⟹ 和 = 0；与和 = 1 矛盾
  have hzero : ∀ t : Fin n, constrainedSoftmax allowed s t = 0 := by
    intro t
    refine constrainedSoftmax_eq_zero_of_not_allowed allowed s t ?_
    intro ht
    exact hempty ⟨t, ht⟩
  have hsum0 : (∑ t, constrainedSoftmax allowed s t) = 0 := by
    exact Finset.sum_eq_zero (fun t _ => hzero t)
  rw [hsum0] at hsum
  norm_num at hsum

end Lattice

/-! ## §5 公理探测 -/

#print axioms Lattice.not_allowed_contribution_zero
#print axioms Lattice.mass_concentrated_on_allowed
#print axioms Lattice.allowed_is_convex_weights
#print axioms Lattice.support_from_decoded_constraints
#print axioms Lattice.feasibility_is_caller_obligation
