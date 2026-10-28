import Mathlib
import Lattice.Lib.Attention.RealMaskFamily
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.RealTokenSymbolLink
/-!
# LATTICE U03-(a): RealConstrainedDecoding —— 约束解码的可行性掩码（L2⇄L3 的运行时落点）

## 0. 为什么需要本文件（判据来自项目自己的文本）

`doc/02:90` 逐字把 L2⇄L3 的编译方向列为「★唯一难点（本项目核心）」；
`README.md:13` 的链路声明是 数据 ⇄ token ⇄ 符号模型 ⇄ 权重。

**约束解码（constrained decoding）** 是该编译方向在【推理时刻】的唯一形态：

    allowed_t = { t | prefix ++ t 仍可满足符号约束 }      <- 符号侧（L2）
    p'_t     = exp(s_t) if allowed t else 0 / Sigma ...   <- 权重侧（L3，logits 掩码）

若本文件不存在，则编译方向只有训练期落点（损失项/初始化），没有推理期落点。

## 1. 本文件必须钉死的高危误判点（用机器判据坐实）

全库 mask 命中 217 处，100% 是注意力掩码，其类型一律是

    mask : Fin n -> Fin n -> Prop      -- 位置 x 位置（RealMaskFamily.lean:14）

而约束解码需要的是 **logit 掩码**：

    allowed : Fin n -> Bool            -- **词表 token 维度、单下标**

二者定义域/维度/更新语义全不同：前者是二维位置关系且每步重算（随 KV 增长），
后者是一维 token 集合且逐步收窄（约束累积）。本文件把这一区别做成**类型级**事实。

## 2. 与 RealMaskFamily 的关系（复用而非重造）

RealMaskFamily.maskedSoftmax（RealMaskFamily.lean:46-48）的形状是

    maskedSoftmax mask s i j := (if mask i j then exp (s j) else 0) / maskedDenom mask s i

把 mask : Fin n -> Fin n -> Prop（二维，带行指标 i）换成 allowed : Fin n -> Bool
（一维，无行指标）即得本文件的 constrainedSoftmax。证明逐行可搬：
maskedDenom_nonneg(:52)、maskedDenom_pos(:65)、maskedSoftmax_nonneg(:80)、
maskedSoftmax_sum_one(:95)、maskedSoftmax_pos_of_mask(:126)、
maskedSoftmax_eq_zero_of_not_mask(:133)。

诚实标注：本文件不是 RealMaskFamily 的实例化——maskedSoftmax 的第二个下标 i
在约束解码里没有对应物（解码时没有「行」）。把它硬套成 mask := fun _ j => allowed j
会引入一个虚假的行参数，并使 maskedSoftmax_sum_one 的行非空假设
变成对一个与约束无关的哑变量的量化。故本文件独立定义，并另外证明
与 RealMaskFamily 的**显式对应定理**（S4 constrained_via_maskedSoftmax），
把「同构搬运」做成机器可验证的等式，而非注释里的声称。

## 3. 词表抽象

真实约束解码在有限词表上做，且分母是有限和（mathlib 的 Finset.sum 需要 Fintype）。
取 Fin n 使 Fintype/Decidable 自动可用，且与 RealMaskFamily 的 Fin n -> Fin n 同源。
这不声称覆盖「无限词表」（不存在）。

## 4. 与符号侧（L2）的接线：ConstraintSet 是唯一权威类型

本文件只使用 SymbolToWeightCorrectness.lean:27 的
abbrev ConstraintSet := List VectorConstraint。
全库另有 8 个文件各自重定义了同名 structure VectorConstraint
（RealExtractCanonical.lean:45、RealExtractNonInjective.lean:25、
RealHypothesisAudit.lean:42、RealLayerSemanticQuotient.lean:42、
RealRflAudit.lean:42、RealRoundtripNontrivial.lean:35、_D2-3.lean:73、_G-02.lean:42）。
若本文件 import 了其中任何一个，ConstraintSet 的含义会被静默换掉。
故 import 列表只含 SymbolToWeightCorrectness（与 RealTokenSymbolLink，后者亦 import 前者）。

符号侧接口用 RealTokenSymbolLink.decode : List SymToken -> Option ConstraintSet（:170）。

## 5. 诚实边界（本文件不证 / 不声称的）

- 不证「采样出的 token 一定满足约束」。本文件证的是**概率支撑**：掩码外概率恰为 0，
  而「实际生成满足约束」还需采样器正确性 + 每步 allowed 由真约束集算出，二者均不在本文件内。
- 不证约束集的可满足性。若约束本身矛盾，则 allowed 全假、分母为 0，掩码 softmax 未定义
  —— 这是数学事实，故行随机定理带**显式非空假设**（见负对照 empty_allowed_row_sum_ne_one）。
- 不证「解码前缀的增量更新正确」。本文件只证：给定每步的 allowed，掩码 softmax 是概率分布。
  前缀累积是**未落地的缺口**。
- 不接 GPU / 推理引擎 / 真实分词器。Fin n 是抽象词表，SymToken 是抽象 token。
- 不使用 sorry / axiom / admit。
-/

noncomputable section

-- i 是哑行指标（见 §2 诚实标注）：它在若干定理中仅用于传递二维提升，
-- 语义上不携带信息，故关闭该项 linter 噪声。
set_option linter.unusedVariables false

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

open scoped BigOperators

/-! ## S1 可行性掩码：**一维** token 掩码（与二维位置掩码类型级区分） -/

/-- **可行性掩码**：allowed t = true 当且仅当 token t 在当前前缀下仍可满足符号约束。

类型要点：这是 Fin n -> Bool（单下标、词表维度），
不是 RealMaskFamily.lean:14 的 Fin n -> Fin n -> Prop（双下标、位置 x 位置）。
二者不可互相赋值——这是编译期事实，不是注释约定（负对照见 S6）。 -/
abbrev FeasibleMask (n : Nat) := Fin n -> Bool

/-- 掩码的**允许集**（外延形式）。这是「掩码」作为**集合**的规范读法。 -/
def allowedSet {n : Nat} (allowed : FeasibleMask n) : Finset (Fin n) :=
  Finset.univ.filter (fun t => allowed t = true)

/-- **掩码分母**：Sigma_t (if allowed t then exp (s_t) else 0)。
与 RealMaskFamily.maskedDenom（:40-42）同形，但**无行指标**。 -/
def constrainedDenom {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real) : Real :=
  Finset.sum Finset.univ (fun t => (if allowed t = true then Real.exp (s t) else 0))

/-- **约束 softmax（核心定义）**：允许集内归一化的、支撑被限制在 allowed 上的分布：

    p_t = (if allowed t then exp(s_t) else 0) / Sigma_u (if allowed u then exp(s_u) else 0)

用 if 分支避免负无穷（与 RealMaskFamily 同一处置）。 -/
def constrainedSoftmax {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real) :
    Fin n -> Real :=
  fun t => (if allowed t = true then Real.exp (s t) else 0) / constrainedDenom allowed s

/-! ## S2 分母引理（逐行对应 RealMaskFamily 的同名引理） -/

/-- 分母非负 —— **无需任何假设**。（对应 maskedDenom_nonneg:52） -/
lemma constrainedDenom_nonneg {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real) :
    0 <= constrainedDenom allowed s := by
  unfold constrainedDenom
  exact Finset.sum_nonneg (fun t _ => by
    by_cases h : allowed t = true
    · rw [if_pos h]
      exact le_of_lt (Real.exp_pos (s t))
    · rw [if_neg h])

/-- 允许集非空则分母**为正**。（对应 maskedDenom_pos:65） -/
lemma constrainedDenom_pos {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (hne : ∃ t, allowed t = true) : 0 < constrainedDenom allowed s := by
  obtain ⟨t0, ht0⟩ := hne
  unfold constrainedDenom
  refine Finset.sum_pos' (fun t _ => ?_) ⟨t0, Finset.mem_univ t0, ?_⟩
  · by_cases h : allowed t = true
    · rw [if_pos h]
      exact le_of_lt (Real.exp_pos (s t))
    · rw [if_neg h]
  · rw [if_pos ht0]
    exact Real.exp_pos (s t0)

/-! ## S3 核心定理 -/

/-- **定理一（支撑）**：掩码外的 token 概率**恰为 0**。
这是约束解码的定义性内容：不可行 token 的生成概率被精确清零。
（对应 maskedSoftmax_eq_zero_of_not_mask:133） -/
theorem constrainedSoftmax_eq_zero_of_not_allowed {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (t : Fin n) (ht : ¬ allowed t = true) :
    constrainedSoftmax allowed s t = 0 := by
  unfold constrainedSoftmax
  rw [if_neg ht, zero_div]

/-- **定理一'（对偶：允许则严格正）**：允许集内概率**严格为正**（分母为正时）。
于是掩码**没有误杀**可行 token（不是「一律清零」的平凡掩码）。
（对应 maskedSoftmax_pos_of_mask:126） -/
theorem constrainedSoftmax_pos_of_allowed {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (t : Fin n) (hne : ∃ u, allowed u = true) (ht : allowed t = true) :
    0 < constrainedSoftmax allowed s t := by
  unfold constrainedSoftmax
  rw [if_pos ht]
  exact div_pos (Real.exp_pos (s t)) (constrainedDenom_pos allowed s hne)

/-- **定理二（非负）**：任意掩码则概率非负。**无需任何假设**。
（对应 maskedSoftmax_nonneg:80） -/
theorem constrainedSoftmax_nonneg {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (t : Fin n) : 0 <= constrainedSoftmax allowed s t := by
  unfold constrainedSoftmax
  exact div_nonneg
    (by
      by_cases h : allowed t = true
      · rw [if_pos h]
        exact le_of_lt (Real.exp_pos (s t))
      · rw [if_neg h])
    (constrainedDenom_nonneg allowed s)

/-- **定理三（行随机 / 归一化）**：允许集非空则 Sigma_t p_t = 1。
这是「掩码后的 logits 仍是一个概率分布」——约束解码**不破坏**归一化。
（对应 maskedSoftmax_sum_one:95） -/
theorem constrainedSoftmax_sum_one {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (hne : ∃ t, allowed t = true) : (∑ t, constrainedSoftmax allowed s t) = 1 := by
  unfold constrainedSoftmax constrainedDenom
  have hD : (∑ u : Fin n, (if allowed u = true then Real.exp (s u) else 0)) ≠ 0 :=
    ne_of_gt (constrainedDenom_pos allowed s hne)
  calc
    (∑ t : Fin n, (if allowed t = true then Real.exp (s t) else 0) /
        (∑ u : Fin n, (if allowed u = true then Real.exp (s u) else 0)))
        = (∑ t : Fin n, (if allowed t = true then Real.exp (s t) else 0)) /
          (∑ u : Fin n, (if allowed u = true then Real.exp (s u) else 0)) := by
          rw [Finset.sum_div]
    _ = 1 := div_self hD

/-- **支撑-允许集一致性（结构定理）**：概率的**支撑**恰等于允许集。
把定理一（正向）与定理一'（反向）合成**充要条件**，
这排除了「掩码只清 0 但允许集是空的」这类退化读法。 -/
theorem constrainedSoftmax_support_iff_allowed {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (hne : ∃ u, allowed u = true) (t : Fin n) :
    constrainedSoftmax allowed s t ≠ 0 ↔ allowed t = true := by
  constructor
  · intro h
    by_contra ht
    exact h (constrainedSoftmax_eq_zero_of_not_allowed allowed s t ht)
  · intro ht
    exact ne_of_gt (constrainedSoftmax_pos_of_allowed allowed s t hne ht)

/-! ## S4 与 RealMaskFamily 的**显式对应定理** -/

/-- 一维允许掩码到二维（位置 x 位置）掩码的**哑提升**：行指标被忽略。 -/
def liftToPosMask {n : Nat} (allowed : FeasibleMask n) : Fin n -> Fin n -> Prop :=
  fun _ j => allowed j = true

instance {n : Nat} (allowed : FeasibleMask n) : DecidableRel (liftToPosMask allowed) :=
  fun i j => inferInstanceAs (Decidable (allowed j = true))

/-- **对应定理**：constrainedSoftmax = RealMaskFamily.maskedSoftmax 在哑提升下。
两侧定义域不同（一维 vs 二维），本定理是它们**唯一**的合法桥。 -/
theorem constrained_via_maskedSoftmax {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (i t : Fin n) :
    constrainedSoftmax allowed s t = maskedSoftmax (liftToPosMask allowed) s i t := by
  unfold constrainedSoftmax constrainedDenom maskedSoftmax maskedDenom liftToPosMask
  rfl

/-- **复用确认（非重造）**：把对应定理与 RealMaskFamily 的**已证**行随机定理复合，
重新得到本文件定理三。这证明 S3 的四条**确实**是模板定理的特例。 -/
theorem constrained_sum_one_via_realMaskFamily {n : Nat} (allowed : FeasibleMask n)
    (s : Fin n -> Real) (i : Fin n) (hne : ∃ t, allowed t = true) :
    (∑ t, constrainedSoftmax allowed s t) = 1 := by
  have hne' : ∃ j, liftToPosMask allowed i j := by
    obtain ⟨t0, ht0⟩ := hne
    exact ⟨t0, ht0⟩
  calc (∑ t, constrainedSoftmax allowed s t)
      = ∑ t, maskedSoftmax (liftToPosMask allowed) s i t := by
        exact Finset.sum_congr rfl (fun t _ => constrained_via_maskedSoftmax allowed s i t)
    _ = 1 := maskedSoftmax_sum_one (liftToPosMask allowed) s i hne'

/-! ## S5 与符号侧（L2）的接线：ConstraintSet 必须**同时出现** -/

/-- **解码-约束相容性**：token 序列 ts 经 RealTokenSymbolLink.decode 得到的约束集恰为 cs。
这是 L1->L2 方向的既有权威函数，本文件不重新定义解码，只**消费**它（:170）。

decode ts = some cs 才是「成功」；none 分支在既有实现中构造性地不出现
（该文件 :167-169 自陈「失败体现在段被丢弃」），
故本谓词显式取 some cs 分支，**不**把 none 静默当作空约束集。 -/
def DecodesTo (ts : List SymToken) (cs : ConstraintSet) : Prop :=
  decode ts = some cs

/-- **约束集到掩码的规范投影**：允许 token t 当且仅当 decode 出的约束集非空
且 t 的符号内容不是段分隔符（即 t 可作为一个约束项被追加）。

诚实标注：这是**接口**——其右端是可判定的具体条件，**不是**对「任意前缀可满足性」
的完整建模（后者需要完整增量语义，**未落地**）。本文件固定接口形状，
使后续替换为真实语义时**定理陈述不变**。 -/
def allowedByConstraints {n : Nat} (cs : ConstraintSet) (tok : Fin n -> SymToken) :
    FeasibleMask n :=
  fun t => decide (cs.isEmpty = false ∧ tok t ≠ SymToken.sep)

/-- **核心接线定理**：陈述中**同时出现** ConstraintSet 与 logit 掩码。

内容：对掩码 `allowed := allowedByConstraints cs tok`，掩码 softmax 的**支撑**
（非零概率的 token 集）**恰为** allowed 的允许集。 -/
theorem constrained_agrees_with_constraint_set {n : Nat} (cs : ConstraintSet)
    (tok : Fin n -> SymToken) (s : Fin n -> Real)
    (hne : ∃ t, allowedByConstraints cs tok t = true) (t : Fin n) :
    constrainedSoftmax (allowedByConstraints cs tok) s t ≠ 0 ↔
      allowedByConstraints cs tok t = true :=
  constrainedSoftmax_support_iff_allowed (allowedByConstraints cs tok) s hne t

/-! ### ⚠ 这条**没有**把 L2 接到 L3，尽管它的名字这么说

**第 212 轮审计的更正，写在这里而不是留在债务表里。** 原陈述带一个前提

```lean
(_hts : DecodesTo ts cs)
```

**它从未被使用**，因为 `allowedByConstraints cs tok` **是 `cs` 与 `tok` 的函数，不含 `ts`**：
`DecodesTo ts cs` 说的是 `decode ts = some cs`，而 `allowedByConstraints` 只看 `cs` 是否非空、
`tok` 是否是段分隔符。**所以这条定理对任何掩码都成立**，`cs`、`ts` 都是装饰。

**它没有建立「符号约束决定采样支撑」。** 那个连接是 `allowedByConstraints` 的**定义**携带的，
不是这条定理证的；而「`cs` 非空」这一半由**调用方**以 `hne` 提供，
**`DecodesTo` 给不出来**——非空性是 `tok` 的性质（存在一个非分隔符 token），不是 `cs` 的性质。

**所以本条的判定是 `downgrade`（声称过强），不是 `strengthen`**：
名字已收窄到 `constrained_agrees_with_constraint_set` 的**可行含义**，前提已删。 -/

/-! ## S6 真实负对照（任务书判据 5） -/

/-- **负对照 1（消融：非空假设是承重的）**：允许集**空**时，
constrainedSoftmax_sum_one 的结论**为假**——即定理三的非空假设**不可去掉**。

见证：n = 2、allowed 恒 false、s 恒 0。此时分母 = 0，每个概率 = 0/0 = 0
（Lean 的 Real 除法是全函数），故 Sigma p = 0 ≠ 1。
这不是「证明失败」，是**数学事实**：全假掩码下根本没有概率分布。 -/
theorem empty_allowed_row_sum_ne_one :
    ∃ (allowed : FeasibleMask 2) (s : Fin 2 -> Real),
      (¬ (∃ t, allowed t = true)) ∧ (∑ t, constrainedSoftmax allowed s t) ≠ 1 := by
  refine ⟨fun _ => false, fun _ => 0, ?_, ?_⟩
  · intro h
    obtain ⟨t, ht⟩ := h
    exact Bool.noConfusion ht
  · intro hsum
    have hzero : ∀ t : Fin 2,
        constrainedSoftmax (fun _ : Fin 2 => false) (fun _ => 0) t = 0 := by
      intro t
      unfold constrainedSoftmax constrainedDenom
      simp only [if_false, Bool.false_eq_true]
      simp
    have hsum0 : (∑ t : Fin 2,
        constrainedSoftmax (fun _ : Fin 2 => false) (fun _ => 0) t) = 0 := by
      simp only [hzero, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [hsum0] at hsum
    norm_num at hsum

/-- **负对照 2（不可替代性：位置掩码的行指标是哑的）**：
liftToPosMask 的**行指标确实被消掉**：任意两行给出**同一个** softmax。

即：若有人声称「直接用 RealMaskFamily 的 mask 就是约束解码」，
则他必须解释**为什么行指标 i 不携带信息**。本定理把这个「解释」变成机器事实：
它不携带信息，于是二维掩码的额外结构在约束解码中是无用的，
故正确做法是**一维** FeasibleMask（S1），而不是复用二维类型。 -/
theorem posMask_row_is_dummy {n : Nat} (allowed : FeasibleMask n) (s : Fin n -> Real)
    (i i' t : Fin n) :
    maskedSoftmax (liftToPosMask allowed) s i t
      = maskedSoftmax (liftToPosMask allowed) s i' t := by
  rw [← constrained_via_maskedSoftmax allowed s i t,
      ← constrained_via_maskedSoftmax allowed s i' t]

/-- **负对照 3（反驳可能：掩码确实改变分布，不是恒等）**：
存在**具体数值**见证：同一 logits，掩码与非掩码给出**不同的概率**。

若掩码 softmax 恒等于普通 softmax，则本文件的全部定理**空洞**
（「约束解码」什么都没做）。本定理用显式数值排除该退化。

见证：n = 2、s = (0,0)（两点等概率 1/2）、allowed = (true,false)。
掩码后 p_0 = 1、p_1 = 0，与未掩码的 1/2 **不等**。 -/
theorem mask_actually_changes_distribution :
    ∃ (allowed : FeasibleMask 2) (s : Fin 2 -> Real) (t : Fin 2),
      constrainedSoftmax allowed s t
        ≠ Real.exp (s t) / (∑ u : Fin 2, Real.exp (s u)) := by
  refine ⟨fun t => if t = 0 then true else false, fun _ => 0, 0, ?_⟩
  have hmask : constrainedSoftmax (fun t : Fin 2 => if t = 0 then true else false)
      (fun _ : Fin 2 => 0) 0 = 1 := by
    unfold constrainedSoftmax constrainedDenom
    rw [if_pos (by simp : (if (0 : Fin 2) = 0 then true else false) = true)]
    have hdenom : (∑ u : Fin 2, (if (if u = 0 then true else false) = true
        then Real.exp ((fun _ : Fin 2 => 0) u) else 0)) = 1 := by
      rw [Fin.sum_univ_two]
      norm_num
    rw [hdenom]
    norm_num
  have hplain : Real.exp ((fun _ : Fin 2 => 0) 0) /
      (∑ u : Fin 2, Real.exp ((fun _ : Fin 2 => 0) u)) = 1 / 2 := by
    rw [Fin.sum_univ_two]
    norm_num
  rw [hmask, hplain]
  norm_num

/-- **负对照 4（掩码非平凡：存在允许集非空的实例）**：
给出**具体见证** allowed = (true,false)、s = (0,0)，
满足非空假设且行随机性**真的成立**（Sigma p = 1）。
于是定理三**不是**空泛的：它的假设可满足、结论可用。 -/
theorem nonempty_allowed_row_sum_eq_one_witness :
    ∃ (allowed : FeasibleMask 2) (s : Fin 2 -> Real),
      (∃ t, allowed t = true) ∧ (∑ t, constrainedSoftmax allowed s t) = 1 := by
  refine ⟨fun t => if t = 0 then true else false, fun _ => 0, ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · have hne : ∃ t : Fin 2, (fun t : Fin 2 => if t = 0 then true else false) t = true := by
      exact ⟨0, by simp⟩
    exact constrainedSoftmax_sum_one _ _ hne

end Lattice

/-! ## S7 公理探测（守项目纪律：交付模块自证无 sorryAx） -/

#print axioms Lattice.constrainedDenom_nonneg
#print axioms Lattice.constrainedDenom_pos
#print axioms Lattice.constrainedSoftmax_eq_zero_of_not_allowed
#print axioms Lattice.constrainedSoftmax_pos_of_allowed
#print axioms Lattice.constrainedSoftmax_nonneg
#print axioms Lattice.constrainedSoftmax_sum_one
#print axioms Lattice.constrainedSoftmax_support_iff_allowed
#print axioms Lattice.constrained_via_maskedSoftmax
#print axioms Lattice.constrained_sum_one_via_realMaskFamily
#print axioms Lattice.posMask_row_is_dummy
#print axioms Lattice.empty_allowed_row_sum_ne_one
#print axioms Lattice.mask_actually_changes_distribution
#print axioms Lattice.nonempty_allowed_row_sum_eq_one_witness
#print axioms Lattice.constrained_agrees_with_constraint_set
