import Mathlib

/-!
# LATTICE: ℝ 非线性激活 —— ReLU/sign 编码约束（突破线性子类）

此前证明限于线性层（输出 = 加权和）。本文件引入**非线性激活**：
  1. ReLU 编码不等式约束：x ≤ a ⟺ relu(x - a) = 0（relu 输出为零即满足）；
  2. sign 编码等式约束：x = a ⟺ sign(x - a) = 0（Real.sign 零化）；
  3. 合取：多个不等式 ⟺ 各 relu 输出和为零（relu 非负 → 和零 ⟺ 各项零）。

这是非线性子结构保语义的最小实例：约束经激活函数嵌入网络后，
零激活点恰好是约束满足点——把「硬约束解嵌入软约束驻点」推广到带激活的层。
-/

namespace Lattice

/-! ## ReLU（max x 0）与零化性质 -/

/-- ReLU：`max x 0`。

⚠ **平行定义提示（v14，S9 重复实现审计发现；coordinator 已核实）**：
本文件 **62 个传递 importer**（**全库 14.8%**），是**最高爆炸半径**的定义之一。
全库另有**同名 `relu`** 出现在 `RealExtractInvertibility`（及 `RealNonlinearFidelity` 相关链）；
`Lattice.sigmoid` 在 `RealSwiGLU:23` 与 `RealExtractInvertibility:122` **各定义一次**，
`Lattice.geluTanh` 在 `RealActClass:74` 与 `RealExtractInvertibility:148` **各定义一次**。

- **合一物理不可行**：同时 `import` 两者会**报 `environment already contains 'Lattice.sigmoid'`**
  （`RealNonlinearFidelity.lean:25` **逐字记录了该真实报错**）；
- ⇒ **处置：不合一**（与"同一概念但不同名"的孪生对不同——那些是可以安全收敛的）；
  **仅在**声明端**加本标注**，因为**原先的登记只写在消费端**（`RealNonlinearFidelity.lean:28-36`），
  而**声明端**（本文件、`RealSwiGLU:23`、`RealActClass:74`）**零标注**。
- ⚠ **为何声明端也必须标注**：`CORRECTIONS.md:874-876` 已确立先例 ——
  **"不标注就会被下一轮扫描当活缺陷重报"**；扫描器读的是**声明处**，不是消费处。
- **⇒ 一般纪律：重复定义的登记应写在**声明端**（那里是扫描器与被引用者的交汇点）。** -/
def relu (x : ℝ) : ℝ := max x 0

lemma relu_nonneg (x : ℝ) : 0 ≤ relu x := by
  unfold relu
  exact le_max_right x 0

lemma relu_eq_zero_iff (x : ℝ) : relu x = 0 ↔ x ≤ 0 := by
  unfold relu
  constructor
  · intro h
    by_contra hnot
    have hpos : 0 < x := lt_of_not_ge hnot
    have hmax : max x 0 = x := max_eq_left (le_of_lt hpos)
    have : x = 0 := by simpa [hmax] using h
    linarith
  · intro h
    exact max_eq_right h

/-! ## 不等式约束（符号侧）与 relu 神经元（权重侧） -/

def LeConstrR (x a : ℝ) : Prop := x ≤ a

def ReluOut (x a : ℝ) : ℝ := relu (x - a)

/-! ## 定理一：ReLU 编码不等式约束（保语义）
x ≤ a ⟺ relu(x - a) = 0。—— 不等式约束经 ReLU 非线性激活嵌入网络。-/

theorem relu_preserves (x a : ℝ) : LeConstrR x a ↔ ReluOut x a = 0 := by
  unfold LeConstrR ReluOut
  rw [relu_eq_zero_iff]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! ## 定理二：sign 编码等式约束（保语义）
x = a ⟺ sign(x - a) = 0（Real.sign 零化 ⟺ 底数为零）。-/

theorem sign_preserves (x a : ℝ) : x = a ↔ Real.sign (x - a) = 0 := by
  rw [Real.sign_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-! ## 合取：Σ relu 输出 = 0 ⟺ 全部不等式满足 -/

def SumRelu (xs : List (ℝ × ℝ)) : ℝ :=
  (xs.map (fun p => relu (p.1 - p.2))).foldr (fun a b => a + b) 0

lemma sumRelu_nonneg (xs : List (ℝ × ℝ)) : 0 ≤ SumRelu xs := by
  unfold SumRelu
  induction xs with
  | nil => simp
  | cons h t ih =>
      have : 0 ≤ relu (h.1 - h.2) := relu_nonneg _
      change 0 ≤ relu (h.1 - h.2) +
        (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0
      nlinarith

/-! ## 定理三：Σ relu 输出 = 0 ⟺ 每项为零（relu 非负 → 和零 ⟺ 各项零） -/

lemma sumRelu_eq_zero_iff_each (xs : List (ℝ × ℝ)) :
    SumRelu xs = 0 ↔ ∀ p ∈ xs, ReluOut p.1 p.2 = 0 := by
  unfold SumRelu
  induction xs with
  | nil => simp
  | cons h t ih =>
      constructor
      · intro hsum p hp
        simp at hp
        rcases hp with rfl | ht
        · -- p = h：和为零 ⟹ 首项 relu 为零（rfl 已把 h 换成 p）
          have hsum' : relu (p.1 - p.2) +
              (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 = 0 := by
            simpa using hsum
          have hrestNonneg : 0 ≤
              (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 := by
            simpa [SumRelu] using sumRelu_nonneg t
          have hh : relu (p.1 - p.2) = 0 := by
            nlinarith [relu_nonneg (p.1 - p.2), hrestNonneg]
          exact hh
        · -- p ∈ t：和为零 ⟹ 余项和为零
          have hsum' : relu (h.1 - h.2) +
              (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 = 0 := by
            simpa using hsum
          have hrestNonneg : 0 ≤
              (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 := by
            simpa [SumRelu] using sumRelu_nonneg t
          have hrest : (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 = 0 := by
            nlinarith [relu_nonneg (h.1 - h.2), hrestNonneg]
          exact (ih.mp hrest) p ht
      · intro hall
        have hh : relu (h.1 - h.2) = 0 := hall h (by simp)
        have ht : ∀ p ∈ t, ReluOut p.1 p.2 = 0 := fun p hp => hall p (by simp [hp])
        have hrest : (t.map (fun p => relu (p.1 - p.2))).foldr (fun a b => a + b) 0 = 0 := ih.mpr ht
        simp [hh, hrest]

/-! ## 定理四：多个不等式的合取 ⟺ relu 输出和为零
批量不等式验证：和为零 ⟺ 全部满足（非线性激活下的批量判定）。-/

theorem sumRelu_all_constraints (xs : List (ℝ × ℝ)) :
    (∀ p ∈ xs, LeConstrR p.1 p.2) ↔ SumRelu xs = 0 := by
  constructor
  · intro h
    have hout : ∀ p ∈ xs, ReluOut p.1 p.2 = 0 := fun p hp => (relu_preserves p.1 p.2).mp (h p hp)
    exact (sumRelu_eq_zero_iff_each xs).mpr hout
  · intro h p hp
    exact (relu_preserves p.1 p.2).mpr ((sumRelu_eq_zero_iff_each xs).mp h p hp)

/-! ## 定理五：非满足 ⟹ 损失严格为正（relu 版）
存在不满足的不等式 ⟹ Σ relu 输出 > 0（训练失败信号，非线性版）。-/

theorem sumRelu_pos_of_unsatisfied (xs : List (ℝ × ℝ)) (p : ℝ × ℝ) (hp : p ∈ xs)
    (h : ¬ LeConstrR p.1 p.2) : 0 < SumRelu xs := by
  have hout : ReluOut p.1 p.2 ≠ 0 := by
    intro hz
    exact h ((relu_preserves p.1 p.2).mpr hz)
  -- relu 输出 > 0（非零非负）
  have hpos : 0 < relu (p.1 - p.2) := lt_of_le_of_ne (relu_nonneg (p.1 - p.2)) (by intro hz; exact hout (by simpa [ReluOut, hz]))
  -- 单项 ≤ 总和
  have hle : relu (p.1 - p.2) ≤ SumRelu xs := by
    unfold SumRelu
    -- 单项是列表中一项，其余非负 → 单项 ≤ 和
    induction xs with
    | nil => simp at hp
    | cons h2 t ih =>
        simp at hp
        rcases hp with rfl | ht
        · -- p = h2：首项 relu ≤ 总和（其余项非负；rfl 已把 h2 换成 p）
          have hrest : 0 ≤ (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 := by
            exact sumRelu_nonneg t
          change relu (p.1 - p.2) ≤
            relu (p.1 - p.2) + (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0
          nlinarith
        · -- p ∈ t：归纳假设 + 首项非负
          have : relu (p.1 - p.2) ≤ (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0 := ih ht
          have h2nonneg : 0 ≤ relu (h2.1 - h2.2) := relu_nonneg _
          change relu (p.1 - p.2) ≤
            relu (h2.1 - h2.2) + (t.map (fun q => relu (q.1 - q.2))).foldr (fun a b => a + b) 0
          nlinarith
  exact lt_of_lt_of_le hpos hle

end Lattice
