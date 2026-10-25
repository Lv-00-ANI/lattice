import Mathlib
import Lattice.Lift.ConvertLinear
/-!
# LATTICE: 析取组合律架桥 —— OR ⟺ 乘积为零

doc/01 组合律架桥（难点 4）的另一半：之前已完成合取（AND ⟺ 和为零，
见 ComboN/TotalLoss），本文件完成**析取**（OR ⟺ 乘积为零）。

符号侧：约束 c₁ 或 c₂ 满足（∨）
权重侧：两个神经元输出的**乘积**为零（Int 零因子：a*b=0 ⟺ a=0 ∨ b=0）

意义：
- 析取嵌入网络的"或门"子结构 = 输出相乘（0 吸收律）；
- 任意有限个约束的析取 → 输出乘积为零（∃i 满足 ⟺ 乘积零，归纳）。

**注意** **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的数学内容只用到 `Int`/`List` 等核心类型与零因子性质**
（`Int.mul_eq_zero`、列表 `foldr` 归纳，不依赖 mathlib 的专用代数结构），
但**文件整体 import 了 Mathlib**（所 import 的 `ConvertLinear` 亦然）。
⇒ 原措辞把「数学内容的选型」误写成了「依赖的选型」。订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice

-- LinearConstraint/ConstraintSat/NeuronOut/convert/convert_preserves_semantics 来自 ConvertLinear（同在 Lattice 命名空间）。

/-! ## 二元析取：OR ⟺ 乘积为零 -/

theorem disj_embedding (c₁ c₂ : LinearConstraint) (x : Int) :
    ConstraintSat c₁ x ∨ ConstraintSat c₂ x ↔
      NeuronOut (convert c₁) x * NeuronOut (convert c₂) x = 0 := by
  constructor
  · intro h
    rcases h with h₁ | h₂
    · have z₁ : NeuronOut (convert c₁) x = 0 := (convert_preserves_semantics c₁ x).mp h₁
      simp [z₁]
    · have z₂ : NeuronOut (convert c₂) x = 0 := (convert_preserves_semantics c₂ x).mp h₂
      simp [z₂]
  · intro h
    -- Int 零因子：a*b = 0 → a = 0 ∨ b = 0
    rcases Int.mul_eq_zero.mp h with h₁ | h₂
    · left
      exact (convert_preserves_semantics c₁ x).mpr h₁
    · right
      exact (convert_preserves_semantics c₂ x).mpr h₂

/-! ## 有限析取：输出乘积为零 ⟺ 存在一个满足
对约束列表，编译为神经元列表，乘积 ∏ out_i = 0 ⟺ ∃ i, out_i = 0（零因子归纳）。-/

def prodOuts (ls : List LinearNeuron) (x : Int) : Int :=
  (ls.map (fun l => NeuronOut l x)).foldr (fun a b => a * b) 1

/-! 引理：整数乘积为零 ⟺ 存在因子为零 -/

lemma prod_eq_zero_iff_exists (xs : List Int) :
    xs.foldr (fun a b => a * b) 1 = 0 ↔ ∃ v ∈ xs, v = 0 := by
  induction xs with
  | nil =>
      simp
  | cons h t ih =>
      constructor
      · intro hz
        -- h * (foldr t) = 0 → h = 0 ∨ foldr t = 0
        rcases Int.mul_eq_zero.mp hz with hh | ht
        · exact ⟨h, by simp, hh⟩
        · rcases ih.mp ht with ⟨v, hv, hz⟩
          exact ⟨v, by simp [hv], hz⟩
      · intro hv
        rcases hv with ⟨v, hv, hz⟩
        simp at hv
        rcases hv with hvhead | hvtail
        · -- hvhead : v = h，hz : v = 0 ⟹ h = 0
          have hh : h = 0 := by simpa [hvhead] using hz
          simp [hh]
        · have ht : t.foldr (fun a b => a * b) 1 = 0 := ih.mpr ⟨v, hvtail, hz⟩
          simp [ht]

/-! ## 定理：N 元析取保语义
∃ 约束满足 ⟺ 输出乘积为零（批量"或门"判定）。-/

theorem disjN_preserves (cs : List LinearConstraint) (x : Int) :
    (∃ c ∈ cs, ConstraintSat c x) ↔ prodOuts (cs.map convert) x = 0 := by
  unfold prodOuts
  -- 把 (∃ c ∈ cs, P c) 转换为 (∃ out ∈ outputs, out = 0)（保语义逐元素）
  constructor
  · intro hprod
    rcases hprod with ⟨c, hc, hsat⟩
    -- 输出列表中存在对应 out = 0
    rw [prod_eq_zero_iff_exists]
    refine ⟨NeuronOut (convert c) x, ?_, ?_⟩
    · -- 证明 NeuronOut (convert c) x 在 outputs 列表里：由 hc : c ∈ cs 给出
      apply List.mem_map.mpr
      refine ⟨convert c, ?_, rfl⟩
      apply List.mem_map.mpr
      exact ⟨c, hc, rfl⟩
    · exact (convert_preserves_semantics c x).mp hsat
  · intro hprod
    -- 输出乘积为零 → 存在输出为零 → 存在约束满足
    rw [prod_eq_zero_iff_exists] at hprod
    rcases hprod with ⟨out, hout, hzero⟩
    rcases List.mem_map.mp hout with ⟨l, hl, rfl⟩
    rcases List.mem_map.mp hl with ⟨c, hc, rfl⟩
    exact ⟨c, hc, (convert_preserves_semantics c x).mpr hzero⟩

end Lattice
