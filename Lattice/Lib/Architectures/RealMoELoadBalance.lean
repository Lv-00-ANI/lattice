/-
# LATTICE: MoE 负载均衡 —— 专家容量、溢出丢弃与均衡判据

稀疏门控网络的**负载均衡/容量**侧（W11 2.E / W24 二.3 判定的真缺口）：
MoE 之所以是 MoE 的核心机制之一是「每个专家有容量上限 capacity，
超出容量的 token 被**丢弃**（token dropping），并靠辅助损失 auxLoss
把负载推向均匀」。**本文件是该语义的唯一载体** ——
RealMoE / RealDynamicRoute 只做**保序选择与路由稳定性**，
与负载量、容量、丢弃**零交集**（见 RealMoE.lean 文件头）。

形式化对象（模型无关：任意有限专家指标集 iota、任意每专家容量）：

  1. expertLoad e：路由到专家 e 的 token 数（由分配矩阵计数得到）；
  2. capacity : iota -> Nat：每专家容量上限（capacity factor x 平均负载的抽象）；
  3. droppedAt e := max 0 (expertLoad e - capacity e)：专家 e 的溢出丢弃数；
  4. droppedCount := Sum_e droppedAt e：全模型丢弃 token 数（**核心量**）。

定理（每条都是**定量**陈述，无 vacuous 恒等式）：

  1. droppedCount_eq_zero_iff：**无丢弃 <-> 每个专家都不超容**（刻画）；
  2. balanced_no_drop：**均衡 => 零丢弃**；
  3. imbalance_forces_drop *：**不均衡 => 丢弃 > 0** —— 这是
     「负载均衡」在本形式化中**唯一的可证内容**；
  4. drop_lower_bound *：**丢弃数的显式下界** Sum load - Sum cap <= droppedCount；
  5. drop_of_total_exceeds_capacity：总 token 数 > 总容量 => 必有丢弃（鸽笼）；
  6. uniform_capacity_forces_drop：均一容量 c 下 c*|iota| < Sum load => 丢弃 > 0。

* **强制负对照**（对应判据 13「负对照必须断言自己触发的那个 finding 的身份」）：

  · witness_imbalanced_drops：具体反例 load=(4,0), capacity=(2,2) => 丢弃=2>0；
  · witness_balanced_no_drop：**同一 load**、容量放宽 => 丢弃=0；
  · witness_flip：把两条并置，断言**同一 load 下结论翻转** ——
    这是「droppedCount 可失败」的身份证明。
  · 若 droppedCount 恒为 0（定义写错成常数），第一条**不可证**；
    若 droppedCount 忽略 capacity（只数 load），第二条**不可证**。

真实性声明：auxLoss 只作为**语义注释**登记（训练动力学不在本离散计数模型内）；
本文件**不**声称形式化了「辅助损失梯度如何使负载均匀」。

全部证明无 sorry / axiom / admit。
-/

import Mathlib

noncomputable section

namespace Lattice

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## 负载、容量与丢弃的载体 -/

/-- 每专家负载：路由到专家 e 的 token 数。抽象为任意 Nat 值函数，
对应「分配矩阵按专家列计数」。 -/
def expertLoad (iota : Type*) := iota → Nat

/-- 专家 e 的溢出丢弃数 max 0 (load e - capacity e)。 -/
def droppedAt (load capacity : iota → Nat) (e : iota) : Nat :=
  max 0 (load e - capacity e)

/-- 全模型丢弃 token 数：各专家溢出之和。 -/
def droppedCount (load capacity : iota → Nat) : Nat :=
  ∑ e, droppedAt load capacity e

/-- 均衡谓词：每个专家的负载都不超过容量（该专家无溢出）。 -/
def Balanced (load capacity : iota → Nat) : Prop :=
  ∀ e, load e ≤ capacity e

/-! ## 定理 1：无丢弃 <-> 逐专家不超容（刻画） -/

/-- 单专家丢弃为 0 <-> 该专家不超容。 -/
theorem droppedAt_eq_zero_iff (load capacity : iota → Nat) (e : iota) :
    droppedAt load capacity e = 0 ↔ load e ≤ capacity e := by
  unfold droppedAt
  omega

/-- * **刻画**：droppedCount = 0 <-> Balanced。 -/
theorem droppedCount_eq_zero_iff (load capacity : iota → Nat) :
    droppedCount load capacity = 0 ↔ Balanced load capacity := by
  unfold droppedCount Balanced
  constructor
  · intro h e
    have h0 : droppedAt load capacity e = 0 := by
      have hz : ∀ x ∈ (Finset.univ : Finset iota), droppedAt load capacity x = 0 :=
        Finset.sum_eq_zero_iff.mp h
      exact hz e (Finset.mem_univ e)
    exact (droppedAt_eq_zero_iff load capacity e).mp h0
  · intro h
    refine Finset.sum_eq_zero fun e _ => ?_
    exact (droppedAt_eq_zero_iff load capacity e).mpr (h e)

/-! ## 定理 2：均衡 => 零丢弃 -/

/-- **均衡 => 无丢弃**。 -/
theorem balanced_no_drop (load capacity : iota → Nat) (h : Balanced load capacity) :
    droppedCount load capacity = 0 :=
  (droppedCount_eq_zero_iff load capacity).mpr h

/-! ## 定理 3（核心）：不均衡 => 丢弃 > 0 -/

/-- * **不均衡 => 丢弃 > 0**。 -/
theorem imbalance_forces_drop (load capacity : iota → Nat)
    (h : ∃ e, capacity e < load e) : 0 < droppedCount load capacity := by
  obtain ⟨e, he⟩ := h
  have hpos : 0 < droppedAt load capacity e := by
    unfold droppedAt
    omega
  have hle : droppedAt load capacity e ≤ droppedCount load capacity :=
    Finset.single_le_sum (f := fun e => droppedAt load capacity e)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
  omega

/-- 逆否形式。 -/
theorem no_drop_forces_no_overflow (load capacity : iota → Nat)
    (h : droppedCount load capacity = 0) : ¬ (∃ e, capacity e < load e) := by
  intro hc
  have := imbalance_forces_drop load capacity hc
  omega

/-! ## 定理 4：丢弃数的显式下界 -/

/-- * **下界**：Sum load - Sum cap <= droppedCount。 -/
theorem drop_lower_bound (load capacity : iota → Nat) :
    (∑ e, load e) - (∑ e, capacity e) ≤ droppedCount load capacity := by
  unfold droppedCount droppedAt
  -- 逐专家：Σ load - Σ cap ≤ Σ max 0 (load - cap)
  -- 用逐点不等式 + Finset.sum_le_sum 的两侧比较
  have key : ∀ e : iota, load e - capacity e ≤ max 0 (load e - capacity e) := by
    intro e; omega
  -- 先证 Σ load - Σ cap = Σ (load - cap)（Nat 截断版，用逐点 + 双边）
  have hsub : (∑ e, (load e - capacity e)) ≤ ∑ e, max 0 (load e - capacity e) :=
    Finset.sum_le_sum fun e _ => key e
  -- Σ load - Σ cap ≤ Σ (load - cap) 由 Finset.sum_sub_distrib 的 Nat 版
  have hsplit : (∑ e, load e) - (∑ e, capacity e) ≤ ∑ e, (load e - capacity e) := by
    have : ∑ e, (load e - capacity e) + ∑ e, capacity e ≥ ∑ e, load e := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun e _ => by omega
    omega
  omega

/-- **总需求超总容量 => 必有丢弃**（鸽笼定量版）。 -/
theorem drop_of_total_exceeds_capacity (load capacity : iota → Nat)
    (h : (∑ e, capacity e) < ∑ e, load e) : 0 < droppedCount load capacity := by
  have hb := drop_lower_bound load capacity
  omega

/-! ## 定理 5：均一容量的尖锐计数 -/

/-- 均一容量 c 下丢弃数 <= 总负载。 -/
theorem uniform_drop_le_total (load : iota → Nat) (c : Nat) :
    droppedCount load (fun _ => c) ≤ ∑ e, load e := by
  unfold droppedCount droppedAt
  exact Finset.sum_le_sum fun e _ => by omega

/-- * **均一容量下的可失败性**：c*|iota| < Sum load => 丢弃 > 0。 -/
theorem uniform_capacity_forces_drop (load : iota → Nat) (c : Nat) [Nonempty iota]
    (h : c * Fintype.card iota < ∑ e, load e) :
    0 < droppedCount load (fun _ => c) := by
  apply drop_of_total_exceeds_capacity
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
  exact h

/-! ## * 强制负对照（NEGATIVE CONTROL） -/

/-- 不均衡见证：2 专家，负载 (4,0)，容量 (2,2) => 丢弃 = 2。 -/
theorem witness_imbalanced_drops :
    droppedCount (fun i : Fin 2 => if i = 0 then 4 else 0) (fun _ : Fin 2 => 2) = 2 := by
  norm_num [droppedCount, droppedAt, Fin.sum_univ_two]

/-- 均衡见证：**同一负载** (4,0)，容量放宽为 (4,0) => 丢弃 = 0。 -/
theorem witness_balanced_no_drop :
    droppedCount (fun i : Fin 2 => if i = 0 then 4 else 0)
      (fun i : Fin 2 => if i = 0 then 4 else 0) = 0 := by
  norm_num [droppedCount, droppedAt, Fin.sum_univ_two]

/-- * **身份断言**：同一 load 在容量 A 下丢弃 > 0、在容量 B 下丢弃 = 0。 -/
theorem witness_flip :
    ∃ (load capacity capacity' : Fin 2 → Nat),
      droppedCount load capacity = 2 ∧ droppedCount load capacity' = 0 := by
  refine ⟨fun i : Fin 2 => if i = 0 then 4 else 0,
          fun _ : Fin 2 => 2, fun i : Fin 2 => if i = 0 then 4 else 0, ?_, ?_⟩
  · exact witness_imbalanced_drops
  · exact witness_balanced_no_drop

/-- 核心定理在**该实例上触发**的独立复核（非空洞假设）。 -/
theorem witness_core_fires :
    0 < droppedCount (fun i : Fin 2 => if i = 0 then 4 else 0) (fun _ : Fin 2 => 2) := by
  apply imbalance_forces_drop
  exact ⟨0, by decide⟩

/-- 均衡侧核心定理的独立复核。 -/
theorem witness_core_quiet :
    droppedCount (fun i : Fin 2 => if i = 0 then 4 else 0)
      (fun i : Fin 2 => if i = 0 then 4 else 0) = 0 := by
  apply balanced_no_drop
  intro e
  fin_cases e <;> decide

/-! ## 注：与 RealDynamicRoute 的衔接契约（只读，不重复形式化） -/

end Lattice