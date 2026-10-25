import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE: 符号 → 权重转换层推广到非线性

`SymbolToWeightCorrectness`（线性层）证明「全部约束满足 ⟺ 所有神经元输出为零」。
本文件把它推广到**带逐神经元激活**的层 `x ↦ σ (W x + b)`，并给出：

  1. `NonlinearLayerOut act l x := act (LayerOut l x)`：带激活的神经元输出；
  2. `ZeroFixing act := ∀ y, act y = 0 ↔ y = 0`：激活的零集结构假设；
  3. **主定理 `symbolToWeight_nonlinear_correct`**：在零集假设下
     「全部约束满足 ⟺ 所有带激活神经元输出为零」；
     `nonlinear_layer_zero_iff`：单约束版本；
  4. **反例（一般非线性下断言为假）**：`reluZ`（整数 ReLU）**不满足**零集假设
     （`reluZ_not_zeroFixing`），并给出**机器验证的约束级反例**
     `reluZ_counterexample`：约束 `cEx := {a = [1], b = 1}` 在 `x = [-5]` 上
     `reluZ (LayerOut (convertVec cEx) [-5]) = 0` 但 `¬ VectorConstraintSat cEx [-5]`；
     `reluZ_not_strictMono`：`reluZ` 也不严格单调；
  5. **保证成立的附加条件**：`zeroFixing_of_strictMono`：`σ` 严格单调且 `σ 0 = 0`
     ⟹ `ZeroFixing σ`（从而主定理对该类激活适用）。

诚实标注（无 sorry / axiom / admit）：
- 一般非线性下「输出为零 ⟹ 约束满足」**为假**：本文件用 `reluZ` 的负半轴给出
  **机器验证反例**（`reluZ_counterexample`），不证该假命题。
- 主定理的成立**依赖零集假设** `ZeroFixing σ`（等价于零集恰为 `{0}`）；
  严格单调 + `σ 0 = 0` 是其充分条件（`zeroFixing_of_strictMono`）。
  对不满足该条件的激活（如 ReLU），结论**降级**为反例见证。
- 本文件只做单层逐神经元激活的推广；多层复合的逐层推广是直接的列表归纳，本文件
  以 `nonlinear_layer_zero_iff` + 列表全称结构覆盖。不引入任何未证假设。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、带激活的层与零集假设 -/

/-- 带激活的神经元输出：先线性层再激活 `act (LayerOut l x)`。 -/
def NonlinearLayerOut (act : ℤ → ℤ) (l : LinearLayer) (x : List Int) : ℤ :=
  act (LayerOut l x)

/-- 整数 ReLU：`reluZ n = max n 0`。 -/
def reluZ (n : ℤ) : ℤ := max n 0

/-- `ZeroFixing act`：激活的零集恰为 `{0}`（输出为零 ⟺ 线性前置为零）。 -/
def ZeroFixing (act : ℤ → ℤ) : Prop := ∀ y, act y = 0 ↔ y = 0

/-! ## 二、主定理：零集假设下的保语义 -/

/-- **单约束版本**：零集假设下，带激活层输出为零 ⟺ 约束满足。 -/
theorem nonlinear_layer_zero_iff (act : ℤ → ℤ) (hσ : ZeroFixing act)
    (c : VectorConstraint) (x : List Int) :
    act (LayerOut (convertVec c) x) = 0 ↔ VectorConstraintSat c x := by
  rw [hσ]
  exact (convertVec_preserves_semantics c x).symm

/-- **主定理（列表版本）**：零集假设下，
「全部约束满足 ⟺ 所有带激活层的输出为零」。 -/
theorem symbolToWeight_nonlinear_correct (act : ℤ → ℤ) (hσ : ZeroFixing act)
    (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ ∀ c ∈ cs, NonlinearLayerOut act (convertVec c) x = 0 := by
  unfold AllSatisfied
  constructor
  · intro h c hc
    unfold NonlinearLayerOut
    rw [hσ]
    exact (convertVec_preserves_semantics c x).mp (h c hc)
  · intro h c hc
    have hc' : NonlinearLayerOut act (convertVec c) x = 0 := h c hc
    unfold NonlinearLayerOut at hc'
    rw [hσ] at hc'
    exact (convertVec_preserves_semantics c x).mpr hc'

/-! ## 三、一般非线性下的反例（命题为假） -/

/-- **反例**：`reluZ` 不满足零集假设（负半轴被映到 0）。 -/
theorem reluZ_not_zeroFixing : ¬ ZeroFixing reluZ := by
  intro h
  have h0 : reluZ (-4) = 0 := by norm_num [reluZ]
  have hneg : (-4 : ℤ) = 0 := (h (-4)).1 h0
  norm_num at hneg

/-- 具体约束：系数 `[1]`、常数 `1`，即 `x₀ + 1 = 0`。 -/
def cEx : VectorConstraint := { a := [1], b := 1 }

/-- **机器验证的约束级反例**：`reluZ` 层在 `x = [-5]` 上输出为零，
但约束 `x₀ + 1 = 0` 并不满足（`-5 + 1 = -4 ≠ 0`）。
（`VectorConstraintSat` 是 `def` 别名，其 `Prop` 体不透明，
`decide` 无法直接合成 `Decidable` 实例（报
`failed to synthesize Decidable ¬VectorConstraintSat cEx [-5]`），
故先 `unfold VectorConstraintSat` 把 `dot` 计算暴露出来再 `decide`。） -/
theorem reluZ_counterexample :
    NonlinearLayerOut reluZ (convertVec cEx) [-5] = 0 ∧ ¬ VectorConstraintSat cEx [-5] := by
  constructor
  · decide
  · unfold VectorConstraintSat
    decide

/-- **反例**：`reluZ` 不是严格单调（`-1 < 0` 但 `reluZ (-1) = reluZ 0`）。 -/
theorem reluZ_not_strictMono : ¬ StrictMono reluZ := by
  intro h
  have hlt : reluZ (-1) < reluZ 0 := h (by norm_num)
  norm_num [reluZ] at hlt

/-! ## 四、保证成立的附加条件 -/

/-- **充分条件**：`σ` 严格单调且 `σ 0 = 0` ⟹ `σ` 满足零集假设。 -/
theorem zeroFixing_of_strictMono (act : ℤ → ℤ) (h0 : act 0 = 0) (hmono : StrictMono act) :
    ZeroFixing act := by
  intro y
  constructor
  · intro hy
    rcases lt_trichotomy y 0 with hlt | heq | hgt
    · have hlt' : act y < act 0 := hmono hlt
      rw [h0] at hlt'
      omega
    · exact heq
    · have hgt' : act 0 < act y := hmono hgt
      rw [h0] at hgt'
      omega
  · intro hy0
    rw [hy0]
    exact h0

end Lattice
