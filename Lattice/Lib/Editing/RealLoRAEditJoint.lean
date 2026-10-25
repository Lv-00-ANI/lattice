import Lattice.Lib.Quantization.RealLoRA
import Lattice.Lib.Editing.RealEditRollback
import Lattice.Lib.Architectures.RealResidual
import Mathlib

/-!
# LATTICE: LoRA 与权重编辑的联合 —— 低秩补丁 + rank-one 补丁的加法代数

权重编辑线的**联合编辑**维度：LoRA 低秩补丁（`RealLoRA.LoRAEdit`
= c·(B∘A)，低秩中间空间 H）与 ROME/MEMIT 的 rank-one 编辑
（`RealBatchEditClosed.RankOnePatch` / `RealEditRollback.rankOneEdit`
= Δ⊗k）在同一次编辑中叠加：

    loraPlusEdit W A B c Δ k
      : x ↦ W·x + c·(B∘A)·x + ⟨k,x⟩·Δ
      = W·x + (LoRAEdit A B c)·x + rankOneFun k Δ x

两个补丁都是**加法**的，故联合编辑继承加法代数的全部好性质：

  1. `lora_edit_additive`（核心）：两个联合补丁之和 = 系数相加的联合补丁
     （`LoRAEdit A B (c₁+c₂) = LoRAEdit A B c₁ + LoRAEdit A B c₂` 与
     rank-one 加法合并，实数加法交换/结合）；
  2. `lora_edit_joint_bound`（核心界，回收 RealLoRA.lora_edit_bound）：
     `|联合编辑输出 − W·x| ≤ (|c|·‖B‖·‖A‖ + |Δ|·‖k‖)·‖x‖`
     —— LoRA 项用既有 `lora_edit_bound`（smul 范数 + 两次 opNorm），
     rank-one 项用 Cauchy–Schwarz `|⟨k,x⟩| ≤ ‖k‖‖x‖`，最后三角不等式 + 提公因子；
  3. `lora_edit_constraint_drift`（核心推论）：原标量约束 `W·x + b = 0` 在联合编辑后
     漂移 `≤ (|c|‖B‖‖A‖ + |Δ|‖k‖)·‖x‖`（原约束 = 0，故漂移即补丁输出）；
  4. `edit_rollback_with_lora`（核心，衔接 RealEditRollback）：LoRA 存在时编辑**仍精确
     可回滚**——联合补丁的加法逆元是系数取负 `(−c, −Δ)`：
     `loraPlusEdit (loraPlusEdit W A B c Δ k) A B (−c) (−Δ) k = W`。

**诚实标注**：`lora_edit_bound` 这个名字已被 RealLoRA 占用（同 namespace Lattice），
故联合界命名为 `lora_edit_joint_bound`（陈述即任务要求的
`‖(LoRA+Edit)x − Wx‖ ≤ (‖c‖‖B‖‖A‖ + ‖Δ‖)‖x‖`，其中 rank-one 方向的 `‖Δ‖`
在标量行语义下展开为 `|Δ|·‖k‖`：本文件用 Cauchy–Schwarz `|⟨k,x⟩| ≤ ‖k‖‖x‖`
直接给出 |Δ|·‖k‖·‖x‖ 的界）。
`loraPlusEdit` 取**函数级** W : E → ℝ（与 RealEditRollback.rankOneEdit、
RealBatchEditClosed.BatchEditClosed 一致），LoRA 项经 `RealLoRA.LoRAEdit` 的
CLM 逐点求值接入。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ## Δ⊗k 的标量行（函数级）实现与联合编辑定义 -/

/-- rank-one 补丁 Δ⊗k 的标量行语义（函数级）：`x ↦ ⟨k,x⟩·Δ`。
与 `RealEditRollback.rankOneEdit F Δ k x = F x + ⟨k,x⟩·Δ` 的补丁项一致。 -/
def rankOneFun (k : E) (Δ : ℝ) (x : E) : ℝ := inner k x * Δ

omit [CompleteSpace E] in
/-- `rankOneEdit` 即"基函数 + 本文件的 rank-one 补丁项"（rfl 桥）。 -/
lemma rankOneEdit_eq_add_rankOneFun (F : E → ℝ) (Δ : ℝ) (k : E) :
    rankOneEdit F Δ k = fun x => F x + rankOneFun k Δ x := by
  funext x
  rfl

/-- **联合编辑**：`loraPlusEdit W A B c Δ k = W + c·(B∘A) + Δ⊗k`
（在 x 处逐点展开为 `W·x + (LoRAEdit A B c)·x + ⟨k,x⟩·Δ`）。 -/
def loraPlusEdit (W : E → ℝ) (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ) (c Δ : ℝ) (k : E)
    (x : E) : ℝ :=
  W x + LoRAEdit A B c x + rankOneFun k Δ x

/-! ## 辅助：LoRA 缩放的加法性 -/

omit [CompleteSpace E] in
/-- `LoRAEdit A B (c₁+c₂) x = LoRAEdit A B c₁ x + LoRAEdit A B c₂ x`
（`c • X` 的 `add_smul`，逐点）。 -/
lemma LoRAEdit_add_apply (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ) (c₁ c₂ : ℝ) (x : E) :
    LoRAEdit A B (c₁ + c₂) x = LoRAEdit A B c₁ x + LoRAEdit A B c₂ x := by
  simp only [LoRAEdit, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  exact add_smul c₁ c₂ (B (A x))

/-! ## 定理一（核心）：联合补丁的加法性 -/

/-- **联合编辑加法性**：两个联合补丁之和是系数相加的联合补丁——
`loraPlusEdit (loraPlusEdit W … c₁ Δ₁ k) … c₂ Δ₂ k = loraPlusEdit W … (c₁+c₂) (Δ₁+Δ₂) k`。
LoRA 部分用 `LoRAEdit_add_apply`（线性缩放），rank-one 部分用实数分配律。 -/
theorem lora_edit_additive (W : E → ℝ) (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ)
    (c₁ c₂ Δ₁ Δ₂ : ℝ) (k : E) :
    loraPlusEdit (loraPlusEdit W A B c₁ Δ₁ k) A B c₂ Δ₂ k
      = loraPlusEdit W A B (c₁ + c₂) (Δ₁ + Δ₂) k := by
  funext x
  unfold loraPlusEdit rankOneFun
  ring_nf
  rw [LoRAEdit_add_apply A B c₁ c₂ x]
  ring

/-! ## 定理二（核心界）：联合编辑输出变化界（回收 RealLoRA.lora_edit_bound） -/

omit [CompleteSpace E] in
/-- **联合误差界**：`|(LoRA+Edit)x − W·x| ≤ (|c|·‖B‖·‖A‖ + |Δ|·‖k‖)·‖x‖`。
LoRA 项由 `RealLoRA.lora_edit_bound` 给出（`|c|‖B‖‖A‖‖x‖`，需 `‖·‖` 与 `|·|`
在 ℝ 上的换算），rank-one 项由 Cauchy–Schwarz `|⟨k,x⟩| ≤ ‖k‖‖x‖` 给出，
三角不等式后提取公因子 `‖x‖`。 -/
theorem lora_edit_joint_bound (W : E → ℝ) (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ)
    (c Δ : ℝ) (k : E) (x : E) :
    |loraPlusEdit W A B c Δ k x - W x| ≤ (|c| * ‖B‖ * ‖A‖ + |Δ| * ‖k‖) * ‖x‖ := by
  have hlo : |LoRAEdit A B c x| ≤ |c| * ‖B‖ * ‖A‖ * ‖x‖ := by
    have h := lora_edit_bound A B c x
    rw [show ‖LoRAEdit A B c x‖ = |LoRAEdit A B c x| from Real.norm_eq_abs _] at h
    exact h
  have hrank : |rankOneFun k Δ x| ≤ |Δ| * ‖k‖ * ‖x‖ := by
    unfold rankOneFun
    rw [abs_mul]
    calc
      |inner k x| * |Δ| ≤ (‖k‖ * ‖x‖) * |Δ| :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm k x) (abs_nonneg _)
      _ = |Δ| * ‖k‖ * ‖x‖ := by ring
  have hdiff : loraPlusEdit W A B c Δ k x - W x
      = LoRAEdit A B c x + rankOneFun k Δ x := by
    unfold loraPlusEdit
    ring
  rw [hdiff]
  calc
    |LoRAEdit A B c x + rankOneFun k Δ x|
        ≤ |LoRAEdit A B c x| + |rankOneFun k Δ x| := abs_add _ _
    _ ≤ |c| * ‖B‖ * ‖A‖ * ‖x‖ + |Δ| * ‖k‖ * ‖x‖ := add_le_add hlo hrank
    _ = (|c| * ‖B‖ * ‖A‖ + |Δ| * ‖k‖) * ‖x‖ := by ring

/-! ## 定理三（核心推论）：联合编辑后的约束漂移界 -/

/-- **约束漂移界**：原标量约束 `W·x + b = 0` 满足时，联合编辑后的漂移
`|loraPlusEdit … x + b| ≤ (|c|‖B‖‖A‖ + |Δ|‖k‖)·‖x‖`。
证明：`b = −W·x`（由原约束），故漂移 = 补丁输出，直接取 `lora_edit_joint_bound`。 -/
theorem lora_edit_constraint_drift (W : E → ℝ) (b : ℝ) (x : E)
    (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ) (c Δ : ℝ) (k : E)
    (h0 : W x + b = 0) :
    |loraPlusEdit W A B c Δ k x + b| ≤ (|c| * ‖B‖ * ‖A‖ + |Δ| * ‖k‖) * ‖x‖ := by
  have hb : b = -W x := by linarith
  rw [hb]
  rw [show loraPlusEdit W A B c Δ k x + -W x
        = loraPlusEdit W A B c Δ k x - W x by ring]
  exact lora_edit_joint_bound W A B c Δ k x

/-! ## 定理四（核心，衔接 RealEditRollback）：LoRA 存在时编辑仍精确可回滚 -/

omit [CompleteSpace E] in
/-- rank-one 项取负后精确抵消（与 `RealEditRollback.rollback_edit` 同一代数：
`⟨k,x⟩·Δ + ⟨k,x⟩·(−Δ) = 0`）。 -/
theorem rankOneFun_add_neg (F : E → ℝ) (Δ : ℝ) (k : E) :
    (fun x => F x + rankOneFun k Δ x + rankOneFun k (-Δ) x) = F := by
  funext x
  unfold rankOneFun
  ring

/-- **带 LoRA 的精确回滚**：联合补丁 `(c, Δ)` 的加法逆元是 `(−c, −Δ)`——
`loraPlusEdit (loraPlusEdit W A B c Δ k) A B (−c) (−Δ) k = W`。
LoRA 项由 `LoRAEdit A B c + LoRAEdit A B (−c) = LoRAEdit A B 0 = 0` 抵消
（`LoRAEdit_add_apply`），rank-one 项由 Δ 与 −Δ 抵消；即 RealEditRollback
的加法逆元回滚在 LoRA 联合编辑下**依然精确**。 -/
theorem edit_rollback_with_lora (W : E → ℝ) (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ)
    (c Δ : ℝ) (k : E) :
    loraPlusEdit (loraPlusEdit W A B c Δ k) A B (-c) (-Δ) k = W := by
  funext x
  have hc : LoRAEdit A B c x + LoRAEdit A B (-c) x = 0 := by
    rw [← LoRAEdit_add_apply A B c (-c) x, show c + (-c) = (0 : ℝ) by ring]
    simp only [LoRAEdit, zero_smul, ContinuousLinearMap.zero_apply]
  unfold loraPlusEdit
  rw [show (W x + LoRAEdit A B c x + rankOneFun k Δ x) + LoRAEdit A B (-c) x
        + rankOneFun k (-Δ) x
      = W x + (LoRAEdit A B c x + LoRAEdit A B (-c) x)
          + (rankOneFun k Δ x + rankOneFun k (-Δ) x) by ring]
  rw [hc]
  unfold rankOneFun
  ring

/-! ## 注：联合编辑的闭环语义
  低秩补丁（LoRA，`RealLoRA.LoRAEdit` = c·(B∘A)）与 rank-one 补丁
  （ROME/MEMIT，`RealEditRollback.rankOneEdit` = Δ⊗k）都是**加法**补丁，
  故联合编辑（本文件 loraPlusEdit）：加法性（lora_edit_additive）⟹
  误差界（lora_edit_joint_bound，复用 RealLoRA.lora_edit_bound）⟹
  约束漂移界（lora_edit_constraint_drift）⟹ 加法逆元回滚
  （edit_rollback_with_lora，衔接 RealEditRollback.rollback_edit）。
  与 RealResidual 的编辑局部性（残差支路编辑 ΔF 恰好泄漏 ‖ΔF‖）同一框架：
  联合补丁即残差支路的 ΔF = LoRA + Edit。 -/

end Lattice
