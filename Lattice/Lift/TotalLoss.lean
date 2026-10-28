import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lift.ConstraintEmbeddingSoundness
/-!
# LATTICE: 总损失版本 —— Σ(out_i)² = 0 ⟺ 全部约束满足

把 ConstraintEmbeddingSoundness（单约束）与 SymbolToWeightCorrectness（编译）
连接成训练视角的完整链：
  符号程序（约束集合）编译为单层网络后，**总平方损失** Σ(output_i)² 为零
  ⟺ 全部约束满足。

意义：训练中把总损失降到 0 的权重/输入，恰好满足全部符号约束——
多约束嵌入的"零损失点 = 满足点"。

注意 **订正 B400**：此处原写「纯 Std」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层与数学内容确实只用 Std/core 层的东西**——损失与约束都建立在
`List Int` 与 `Int` 之上（`sqSum` 用 `List.foldr`，输出用 `LayerOut`），不依赖 mathlib 的专用结构；
平方非负用 `Int.mul_nonneg` 手工证（`Int.sq_nonneg` 是 Mathlib 提供的，故不调用它），
但**文件整体 import 了 Mathlib**（零化判据的推导用到 `omega` 等 Mathlib tactic）。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」，且把 Mathlib 提供的定理误称 core。订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 引理一：整数平方非负（手工证，core 无此定理） -/

lemma int_sq_nonneg (a : Int) : 0 ≤ a ^ 2 := by
  rcases le_total a 0 with ha | ha
  · -- a ≤ 0：-a ≥ 0，(-a)² = a²
    have hna : 0 ≤ -a := by omega
    have hprod : 0 ≤ (-a) * (-a) := Int.mul_nonneg hna hna
    have hmul : (-a) * (-a) = a * a := by rw [neg_mul_neg]
    rw [pow_two]
    exact hmul ▸ hprod
  · -- 0 ≤ a
    have hprod : 0 ≤ a * a := Int.mul_nonneg ha ha
    rw [pow_two]
    exact hprod

/-! ## 平方和（foldr，便于归纳） -/

def sqSum (xs : List Int) : Int :=
  (xs.map (fun v => v ^ 2)).foldr (fun a b => a + b) 0

/-! ## 引理二：平方和非负 -/

lemma sqSum_nonneg (xs : List Int) : 0 ≤ sqSum xs := by
  unfold sqSum
  induction xs with
  | nil => simp
  | cons h t ih =>
      simp [List.foldr, pow_two]
      have hh : 0 ≤ h * h := by
        rcases le_total h 0 with hh1 | hh2
        · have hna : 0 ≤ -h := by omega
          have : 0 ≤ (-h) * (-h) := Int.mul_nonneg hna hna
          rw [neg_mul_neg] at this
          exact this
        · exact Int.mul_nonneg hh2 hh2
      unfold sqSum at ih
      simp [pow_two] at ih
      omega

/-! ## 引理三：平方和为零 ⟺ 每项为零 -/

lemma sqSum_eq_zero_iff (xs : List Int) : sqSum xs = 0 ↔ ∀ v ∈ xs, v = 0 := by
  unfold sqSum
  induction xs with
  | nil => simp
  | cons h t ih =>
      constructor
      · intro hsum v hv
        simp [List.foldr] at hsum
        rcases (List.mem_cons.mp hv) with hv' | ht
        · -- hv' : v = h：h² + rest = 0，h² ≥ 0，rest ≥ 0 ⟹ h² = 0 ⟹ h = 0
          rw [hv']
          have hrest_nonneg : 0 ≤ (t.map (fun x => x ^ 2)).foldr (fun a b => a + b) 0 := by
            exact sqSum_nonneg t
          have hh2le : h ^ 2 ≤ 0 := by omega
          have hh2 : h ^ 2 = 0 := le_antisymm hh2le (int_sq_nonneg h)
          exact (int_sq_eq_zero_iff h).mp hh2
        · -- v ∈ t
          have hrest_nonneg : 0 ≤ (t.map (fun x => x ^ 2)).foldr (fun a b => a + b) 0 := by
            exact sqSum_nonneg t
          have hsq : 0 ≤ h ^ 2 := int_sq_nonneg h
          have hrest : (t.map (fun x => x ^ 2)).foldr (fun a b => a + b) 0 = 0 := by omega
          exact (ih.mp hrest) v ht
      · intro hall
        have hh : h = 0 := hall h (by simp)
        have ht : ∀ v ∈ t, v = 0 := fun v hv => hall v (by simp [hv])
        have hrest : (t.map (fun x => x ^ 2)).foldr (fun a b => a + b) 0 = 0 := ih.mpr ht
        simp [List.foldr, hh, hrest]

/-! ## 总损失：网络输出平方和 -/

def totalLoss (cs : ConstraintSet) (x : List Int) : Int :=
  sqSum ((compileToLayer cs).map (fun l => LayerOut l x))

/-! ## 定理：总损失零化 ⟺ 全部约束满足 -/

theorem totalLoss_eq_zero_iff_allSatisfied (cs : ConstraintSet) (x : List Int) :
    totalLoss cs x = 0 ↔ AllSatisfied cs x := by
  unfold totalLoss
  -- sqSum (outputs) = 0 ↔ ∀ out ∈ outputs, out = 0
  have hsq : sqSum ((compileToLayer cs).map (fun l => LayerOut l x)) = 0 ↔
      ∀ v ∈ (compileToLayer cs).map (fun l => LayerOut l x), v = 0 :=
    sqSum_eq_zero_iff ((compileToLayer cs).map (fun l => LayerOut l x))
  -- 输出全零 ⟺ 全部约束满足（symbolToWeight_correct 的 AllZeroOutputs 展开）
  have hall : (∀ v ∈ (compileToLayer cs).map (fun l => LayerOut l x), v = 0) ↔ AllSatisfied cs x := by
    constructor
    · intro h
      exact (symbolToWeight_correct cs x).mpr (fun l hl => h (LayerOut l x) (List.mem_map.mpr ⟨l, hl, rfl⟩))
    · intro hsat v hv
      rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
      exact (symbolToWeight_correct cs x).mp hsat l hl
  exact hsq.trans hall

/-! ## 推论：训练验证信号
总损失为零 ⟹ 全部约束满足（训练完成后可直接用损失判满足）。-/

theorem totalLoss_verify (cs : ConstraintSet) (x : List Int)
    (h : totalLoss cs x = 0) : AllSatisfied cs x :=
  (totalLoss_eq_zero_iff_allSatisfied cs x).mp h

end Lattice
