import Mathlib

/-!
# LATTICE: ℝ 版 —— 实数域线性约束的保语义与平方损失

纯 Std 证明（Int 离散域）升级到 **ℝ（连续域，Mathlib）**：
  1. 实数线性约束 → 实数神经元，编译保语义；
  2. 实数平方损失：L = out²，ℝ 上 零损失 ⟺ 满足（sq_eq_zero_iff）；
  3. 实数平方和为零 ⟺ 各项为零（sq_nonneg + nlinarith）；
  4. 向量版：ℝ 有限维点积（Finset 求和）保语义 + 缩放不变性。

Mathlib 提供的代数（sq_eq_zero_iff、sq_nonneg、Finset 求和）使
证明比 Std 手工版（int_sq_nonneg 等）简洁得多，且贴近真实训练语义。

注意：**订正 B400**：此处原写「纯 Std 手工版」，易被读成**本文件不依赖 mathlib** —— 与事实不符。
真实情况是：**上述 Int 离散域的手工版证明才只用 Std 层的东西**（`Int` 及其引理，如 int_sq_nonneg），
**本文件则整体 `import Mathlib`**：`ℝ` 类型、`sq_eq_zero_iff`、`sq_nonneg`、`Finset` 求和，
以及证明中使用的 `ring`/`nlinarith` 等 tactic 均由 Mathlib 提供，并非 Lean core 内置。
⇒ 原措辞把「被对比的那个手工版」误写成了「本文件」。**以本段为准。**
-/

namespace Lattice

/-! ## ℝ 线性约束（符号侧） -/

structure RealConstraint where
  a : ℝ
  b : ℝ

def RealConstraintSat (c : RealConstraint) (x : ℝ) : Prop :=
  c.a * x + c.b = 0

/-! ## ℝ 神经元（权重侧） -/

structure RealNeuron where
  w : ℝ
  b : ℝ

def RealNeuronOut (n : RealNeuron) (x : ℝ) : ℝ :=
  n.w * x + n.b

/-! ## 转换：系数拷贝 -/

def convertReal (c : RealConstraint) : RealNeuron :=
  { w := c.a, b := c.b }

/-! ## 定理一：ℝ 编译保语义 -/

theorem convertReal_preserves (c : RealConstraint) (x : ℝ) :
    RealConstraintSat c x ↔ RealNeuronOut (convertReal c) x = 0 := by
  simp [RealConstraintSat, RealNeuronOut, convertReal]

/-! ## 平方损失 -/

def realLoss (c : RealConstraint) (x : ℝ) : ℝ :=
  (RealNeuronOut (convertReal c) x) ^ 2

/-! ## 定理二：ℝ 平方损失零化 ⟺ 满足
ℝ 上 out² = 0 ⟺ out = 0（Mathlib sq_eq_zero_iff）。-/

theorem realLoss_soundness (c : RealConstraint) (x : ℝ) :
    realLoss c x = 0 ↔ RealConstraintSat c x := by
  unfold realLoss
  rw [sq_eq_zero_iff]
  exact (convertReal_preserves c x).symm

/-! ## 定理三：ℝ 平方和为零 ⟺ 各项为零 -/

theorem real_sq_sum_zero_iff (a b : ℝ) : a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha2 : a ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb2 : b ^ 2 = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    exact ⟨sq_eq_zero_iff.mp ha2, sq_eq_zero_iff.mp hb2⟩
  · intro h
    rcases h with ⟨ha, hb⟩
    simp [ha, hb]

/-! ## 定理四：ℝ 缩放不变性
约束整体缩放 λ ≠ 0 不改变满足语义（实数乘法消去）。-/

theorem real_scale_preserves (c : RealConstraint) (x lam : ℝ) (hlam : lam ≠ 0) :
    RealConstraintSat c x ↔ RealConstraintSat { a := c.a * lam, b := c.b * lam } x := by
  unfold RealConstraintSat
  constructor
  · intro h
    calc
      (c.a * lam) * x + (c.b * lam) = (c.a * x + c.b) * lam := by ring
      _ = 0 * lam := by rw [h]
      _ = 0 := by simp
  · intro h
    -- 反向：两边乘 lam⁻¹
    have hinv : (c.a * x + c.b) * lam = 0 := by
      calc
        (c.a * x + c.b) * lam = (c.a * lam) * x + (c.b * lam) := by ring
        _ = 0 := h
    -- 实数消去：lam ≠ 0
    exact (mul_eq_zero.mp hinv).resolve_right hlam

/-! ## ℝ 向量约束（有限维点积，Finset 求和） -/

def RealDot {ι : Type*} [Fintype ι] (a x : ι → ℝ) : ℝ := ∑ i, a i * x i

structure RealVectorConstraint (ι : Type) where
  a : ι → ℝ
  b : ℝ

def RealVectorSat {ι : Type} [Fintype ι] (c : RealVectorConstraint ι) (x : ι → ℝ) : Prop :=
  RealDot c.a x + c.b = 0

structure RealLinearLayer (ι : Type) where
  w : ι → ℝ
  b : ℝ

def RealLayerOut {ι : Type} [Fintype ι] (l : RealLinearLayer ι) (x : ι → ℝ) : ℝ :=
  RealDot l.w x + l.b

def convertRealVec {ι : Type} [Fintype ι] (c : RealVectorConstraint ι) : RealLinearLayer ι :=
  { w := c.a, b := c.b }

/-! ## 定理五：ℝ 向量约束保语义 -/

theorem convertRealVec_preserves {ι : Type} [Fintype ι] (c : RealVectorConstraint ι) (x : ι → ℝ) :
    RealVectorSat c x ↔ RealLayerOut (convertRealVec c) x = 0 := by
  simp [RealVectorSat, RealLayerOut, convertRealVec, RealDot]

/-! ## 定理六：ℝ 点积缩放线性性
dot (a·λ) x = (dot a x) · λ（Finset 求和线性性）。-/

theorem realDot_scale {ι : Type*} [Fintype ι] (a x : ι → ℝ) (lam : ℝ) :
    RealDot (fun i => a i * lam) x = (RealDot a x) * lam := by
  unfold RealDot
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## 定理七：ℝ 向量约束缩放不变性 -/

theorem realVec_scale_preserves {ι : Type} [Fintype ι] (c : RealVectorConstraint ι) (x : ι → ℝ)
    (lam : ℝ) (hlam : lam ≠ 0) :
    RealVectorSat c x ↔ RealVectorSat { a := fun i => c.a i * lam, b := c.b * lam } x := by
  unfold RealVectorSat
  rw [realDot_scale]
  constructor
  · intro h
    calc
      (RealDot c.a x) * lam + c.b * lam = (RealDot c.a x + c.b) * lam := by ring
      _ = 0 * lam := by rw [h]
      _ = 0 := by simp
  · intro h
    have hsum : (RealDot c.a x + c.b) * lam = 0 := by
      calc
        (RealDot c.a x + c.b) * lam = (RealDot c.a x) * lam + c.b * lam := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp hsum).resolve_right hlam

end Lattice