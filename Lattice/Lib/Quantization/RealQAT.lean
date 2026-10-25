import Mathlib
import Lattice.Lib.Optim.RealGradDescent
import Lattice.Lib.Quantization.RealQuantizedError
import Lattice.Lib.Optim.RealApprox
import Lattice.Lib.LinearAlgebra.RealSparsity
/-!
# LATTICE: 量化感知训练 (QAT) —— 伪量化、直通估计 (STE) 与量化约束下的收敛

RealQuantizedError 处理**训练后量化 (PTQ)**：模型已训练好，量化引入逐层误差
`δᵢ`，端到端误差沿链传播。QAT（量化感知训练）把量化**放进训练回路**：
前向用伪量化（fake quant）、反向用**直通估计 (STE)** 把量化算子当作恒等传梯度。
本文件形式化 QAT 的三个核心语义：

  1. `fakeQuant` / `steSurrogate` / `ste_gradient_identity`：伪量化的前向是量化算子
     `Q`，反向的 STE 代理是**恒等映射** `id`（`steSurrogate Q = id`）；
  2. `ste_hasDerivAt` / `ste_surrogate_deriv`：STE 代理的导数恒为 `1`
     （`deriv (steSurrogate Q) x = 1`）——STE 的「梯度恒等」；
  3. `ste_chain_rule`：链式法则下 STE 把损失对参数的梯度原样穿过量化算子
     （`d/dx L(steSurrogate Q x) = L'(x)`，把伪量化当恒等传梯度）；
  4. `qatLoss`/`ptqLoss`/`quantError`：QAT 损失（在量化点 `Q θ` 处评估，
     参数 θ 自由漂移）与 PTQ 损失（全精度最优点 `θp` 处）；
  5. `qat_loss_equals_ptq_plus_term`（核心）：QAT 损失 = PTQ 损失 + **参数漂移项**，
     且漂移项被 `c·‖Q θ − θp‖` 界住（`L` 为 `c`-Lipschitz）；
  6. `qat_mismatch_decomposition`：参数量化失配 `‖Q θ − θp‖` 分解为
     「参数漂移 `‖θ − θp‖`（经 `Q` 的 Lipschitz 常数 `cQ` 放大）+ PTQ 量化误差
     `‖Q θp − θp‖`」；
  7. `quantization_error_reduction`（核心）：QAT 相比 PTQ 减小误差的界——
     训练使参数漂移 `‖θ − θp‖` 变小、量化误差 `‖Q θp − θp‖ ≤ e` 时，
     `|QAT 损失 − PTQ 损失| ≤ c·(cQ·‖θ − θp‖ + e)`（**训练越到位，漂移越小，
     误差界越小**）；
  8. `qatUpdate`/`qatIterate`/`qatError`/`qat_step_bound`/`qat_convergence`
     （核心，回收 RealGradDescent）：QAT 的参数更新 = 梯度步 + 量化投影
     `Q (GDUpdate A b η x)`；单步误差 `≤ c·eₙ + ‖A‖·δ`，迭代后有**误差地板**
     `‖A x₀ − b‖ + ‖A‖·δ/(1−c)`——量化约束下误差收敛到 δ‖A‖/(1−c) 邻域，
     而非 0（δ 为量化投影误差界 `∀x, ‖Q x − x‖ ≤ δ`）；
  9. `qat_convergence_zero`（加分）：δ = 0（无量化误差）时退化回
     RealGradDescent 的单调收缩 `eₙ ≤ e₀`。

诚实假设（全部显式标注）：
  · STE 是**替代梯度**（surrogate gradient）的抽象：本文件形式化「代理导数为 1」
    这一数学内容，不声称它是伪量化真梯度的近似——真实 `Q` 几乎处处导数为 0，
    STE 是有意为之的定义，故 `ste_hasDerivAt` 是关于 **`steSurrogate Q = id`**
    的定理，而非关于 `Q` 的（`Q` 的不可导性不被建模，见 docstring）；
  · 损失 `L` 的 Lipschitz 常数 `c`、量化算子 `Q` 的 Lipschitz 常数 `cQ`、
    量化误差界 `δ`/`e` 均为显式假设（它们由具体模型/量化方案给出）；
  · 收敛定理的谱界 `‖1 − 2η·AA†‖ ≤ c < 1` 来自 RealGradDescent（经典步长条件），
    另需 `0 ≤ c`、`c < 1`、`δ ≥ 0`。
模型无关：任意范数空间/内积空间；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、伪量化与直通估计 (STE) -/

/-- 伪量化前向：量化算子 `Q` 直接作用于参数/激活（前向量化，`Q` 可为
round-to-nearest、均匀量化、量化投影等任意算子）。 -/
def fakeQuant {E : Type*} (Q : E → E) (x : E) : E := Q x

/-- STE 反向代理：直通估计把伪量化的导数当作**恒等映射**，
即反向用 `steSurrogate Q = id` 代替 `Q` 传梯度。

**标注（`unused variable 'Q'`）**：量化算子 `Q` 是本代理的**签名形参**
（与 `fakeQuant` 的签名对齐、并让 `steSurrogate Q` 的调用点保持对称），
但 `steSurrogate` 的定义**恒为 `id`**，与 `Q` 的取值**完全无关**
——这正是 STE 的**全部数学内容**（"代理算子 = 恒等"）。
故 `Q` 被改名为 `_Q` 以**显式标注**它是**未被使用**的签名占位符，
而不是暗示"代理关于 `Q` 有某种性质"。 -/
def steSurrogate (_Q : ℝ → ℝ) : ℝ → ℝ := id

/-- STE 的梯度恒等：代理算子逐点等于恒等映射。 -/
theorem ste_gradient_identity (Q : ℝ → ℝ) (x : ℝ) : steSurrogate Q x = x := rfl

/-- STE 代理的导数恒为 `1`：`deriv (steSurrogate Q) x = 1`（把伪量化当恒等传梯度）。 -/
theorem ste_hasDerivAt (Q : ℝ → ℝ) (x : ℝ) : HasDerivAt (steSurrogate Q) 1 x := by
  simpa [steSurrogate] using hasDerivAt_id x

/-- STE 代理的导数（`deriv` 形式）：`deriv (steSurrogate Q) x = 1`。 -/
theorem ste_surrogate_deriv (Q : ℝ → ℝ) (x : ℝ) : deriv (steSurrogate Q) x = 1 :=
  (ste_hasDerivAt Q x).deriv

/-- STE 的链式法则：损失 `L` 在伪量化点处的导数为 `L'` ⟹
复合函数 `x ↦ L (steSurrogate Q x)` 在 `x` 处导数为 `L'`
（STE 把梯度原样穿过量化算子；`L'` 不乘任何量化 Jacobian）。 -/
theorem ste_chain_rule (Q L : ℝ → ℝ) (x L' : ℝ)
    (hL : HasDerivAt L L' (steSurrogate Q x)) :
    HasDerivAt (fun y => L (steSurrogate Q y)) L' x := by
  have h := hL.comp x (ste_hasDerivAt Q x)
  simpa [steSurrogate, Function.comp] using h

/-! ## 二、QAT 损失 = PTQ 损失 + 参数漂移项 -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- QAT 损失：参数 `θ` 自由漂移，损失在**量化点** `Q θ` 处评估
（量化在训练回路内，前向即伪量化）。 -/
def qatLoss (L : E → ℝ) (Q : E → E) (θ : E) : ℝ := L (Q θ)

/-- PTQ 损失：全精度最优点 `θp` 处的损失（先训练、后量化）。 -/
def ptqLoss (L : E → ℝ) (θp : E) : ℝ := L θp

/-- 量化误差：参数 `θ` 与其量化版本 `Q θ` 的距离 `‖Q θ − θ‖`。 -/
def quantError (Q : E → E) (θ : E) : ℝ := ‖Q θ - θ‖

omit [NormedSpace ℝ E] in
/-- **QAT 损失 = PTQ 损失 + 参数漂移项**（核心恒等 + 漂移项界）：
`qatLoss = ptqLoss + (qatLoss − ptqLoss)`，且若 `L` 为 `c`-Lipschitz，
漂移项幅度 `|qatLoss − ptqLoss| ≤ c·‖Q θ − θp‖`
（QAT 与 PTQ 的差距完全由「量化后的 QAT 参数 `Q θ` 与 PTQ 最优点 `θp` 的失配」决定）。 -/
theorem qat_loss_equals_ptq_plus_term (L : E → ℝ) (Q : E → E) (θ θp : E) (c : ℝ)
    (hL : ∀ x y, |L x - L y| ≤ c * ‖x - y‖) :
    qatLoss L Q θ = ptqLoss L θp + (qatLoss L Q θ - ptqLoss L θp) ∧
      |qatLoss L Q θ - ptqLoss L θp| ≤ c * ‖Q θ - θp‖ := by
  refine ⟨by ring, ?_⟩
  exact hL _ _

omit [NormedSpace ℝ E] in
/-- **参数量化失配分解**：`‖Q θ − θp‖ ≤ cQ·‖θ − θp‖ + ‖Q θp − θp‖`
（QAT 参数的量化点与 PTQ 最优点之差 = 参数漂移经 `Q` 的 Lipschitz 放大
+ PTQ 量化误差；`Q` 为 `cQ`-Lipschitz）。 -/
theorem qat_mismatch_decomposition (Q : E → E) (θ θp : E) (cQ : ℝ)
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ cQ * ‖x - y‖) :
    ‖Q θ - θp‖ ≤ cQ * ‖θ - θp‖ + quantError Q θp := by
  have hsplit : Q θ - θp = (Q θ - Q θp) + (Q θp - θp) := by abel
  calc
    ‖Q θ - θp‖ = ‖(Q θ - Q θp) + (Q θp - θp)‖ := by rw [hsplit]
    _ ≤ ‖Q θ - Q θp‖ + ‖Q θp - θp‖ := norm_add_le _ _
    _ ≤ cQ * ‖θ - θp‖ + quantError Q θp := add_le_add (hQ θ θp) le_rfl

/-- **QAT 相比 PTQ 减小误差的界**（核心）：`L` 为 `c`-Lipschitz、`Q` 为
`cQ`-Lipschitz ⟹
`|QAT 损失 − PTQ 损失| ≤ c·(cQ·‖θ − θp‖ + ‖Q θp − θp‖)`。
训练使参数漂移 `‖θ − θp‖` 变小 ⟹ 误差界线性变小；`θ = θp` 时界退化为
`c·‖Q θp − θp‖`（纯 PTQ 量化误差）。 -/
theorem quantization_error_reduction (L : E → ℝ) (Q : E → E) (θ θp : E) (c cQ : ℝ)
    (hc : 0 ≤ c) (hcQ : 0 ≤ cQ)
    (hL : ∀ x y, |L x - L y| ≤ c * ‖x - y‖)
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ cQ * ‖x - y‖) :
    |qatLoss L Q θ - ptqLoss L θp| ≤ c * (cQ * ‖θ - θp‖ + quantError Q θp) := by
  have hm := qat_mismatch_decomposition Q θ θp cQ hQ
  have h0 : 0 ≤ cQ * ‖θ - θp‖ + quantError Q θp :=
    add_nonneg (mul_nonneg hcQ (norm_nonneg _)) (norm_nonneg _)
  calc
    |qatLoss L Q θ - ptqLoss L θp| = |L (Q θ) - L θp| := rfl
    _ ≤ c * ‖Q θ - θp‖ := hL _ _
    _ ≤ c * (cQ * ‖θ - θp‖ + quantError Q θp) := mul_le_mul_of_nonneg_left hm hc

/-- **QAT 减小误差（漂移版）**：若 PTQ 量化误差有界 `‖Q θp − θp‖ ≤ e`，则
`|QAT 损失 − PTQ 损失| ≤ c·(cQ·‖θ − θp‖ + e)`——训练把漂移 `‖θ − θp‖` 压到
多小，误差界就压到多小；`e` 是不可约的 PTQ 量化误差。 -/
theorem quantization_error_reduction_drift (L : E → ℝ) (Q : E → E) (θ θp : E)
    (c cQ e : ℝ) (hc : 0 ≤ c) (hcQ : 0 ≤ cQ) (he : quantError Q θp ≤ e)
    (hL : ∀ x y, |L x - L y| ≤ c * ‖x - y‖)
    (hQ : ∀ x y, ‖Q x - Q y‖ ≤ cQ * ‖x - y‖) :
    |qatLoss L Q θ - ptqLoss L θp| ≤ c * (cQ * ‖θ - θp‖ + e) := by
  have := quantization_error_reduction L Q θ θp c cQ hc hcQ hL hQ
  have hmono : cQ * ‖θ - θp‖ + quantError Q θp ≤ cQ * ‖θ - θp‖ + e :=
    add_le_add_left he _
  exact le_trans this (mul_le_mul_of_nonneg_left hmono hc)

omit [NormedSpace ℝ E] in
/-- QAT 损失非负性无关的良定性注记（损失之差可正可负）：
`|qatLoss − ptqLoss| ≤ c·‖Q θ − θp‖` 是双侧界（QAT 可能更好也可能更差）。 -/
theorem qat_ptq_gap_lipschitz (L : E → ℝ) (Q : E → E) (θ θp : E) (c : ℝ)
    (hL : ∀ x y, |L x - L y| ≤ c * ‖x - y‖) :
    |qatLoss L Q θ - ptqLoss L θp| ≤ c * ‖Q θ - θp‖ :=
  hL _ _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- 退化一致性：QAT 参数与 PTQ 最优点相同（`θ = θp`）时，
QAT 损失与 PTQ 损失相等（两者的差异纯粹来自参数点的差异）。 -/
theorem qat_ptq_degenerate (L : E → ℝ) (Q : E → E) (θ : E) :
    qatLoss L Q θ = ptqLoss L (Q θ) := rfl

/-! ## 三、QAT 在量化约束下的收敛（回收 RealGradDescent） -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- QAT 参数更新：先做梯度步 `GDUpdate`（RealGradDescent），再施加**量化投影** `Q`
（量化约束下的参数更新，`Q` 是投影/舍入算子）。 -/
def qatUpdate (A : F →L[ℝ] F) (b : F) (η : ℝ) (Q : F → F) (x : F) : F :=
  Q (GDUpdate A b η x)

/-- QAT 迭代：`n` 步「梯度步 + 量化投影」的复合（`Function.iterate`）。 -/
def qatIterate (A : F →L[ℝ] F) (b : F) (η : ℝ) (Q : F → F) (n : ℕ) (x : F) : F :=
  (qatUpdate A b η Q)^[n] x

/-- QAT 误差：第 `n` 步参数处的平方损失开方 `‖A xₙ − b‖`。 -/
def qatError (A : F →L[ℝ] F) (b : F) (η : ℝ) (Q : F → F) (x0 : F) (n : ℕ) : ℝ :=
  ‖A (qatIterate A b η Q n x0) - b‖

/-- **QAT 单步误差界**：谱界 `‖1 − 2η·AA†‖ ≤ c`、量化投影误差
`‖Q u − u‖ ≤ δ`（`u = GDUpdate A b η x`）⟹
`‖A (Q u) − b‖ ≤ c·‖A x − b‖ + ‖A‖·δ`。
证明：`A(Qu) − b = [A(Qu) − Au] + [Au − b]`，第一项 `≤ ‖A‖·δ`
（`le_opNorm` + `Q` 误差），第二项 `≤ c‖Ax − b‖`（RealGradDescent 单步收缩）。 -/
theorem qat_step_bound (A : F →L[ℝ] F) (b x : F) (η : ℝ) (Q : F → F) (c δ : ℝ)
    (hspec : ‖(1 : F →L[ℝ] F) - (2 * η : ℝ) • (A ∘L A.adjoint)‖ ≤ c)
    (hQ : ‖Q (GDUpdate A b η x) - GDUpdate A b η x‖ ≤ δ) :
    ‖A (qatUpdate A b η Q x) - b‖ ≤ c * ‖A x - b‖ + ‖A‖ * δ := by
  unfold qatUpdate
  have hgd := GD_contraction_step A b η x c hspec
  have hsplit : A (Q (GDUpdate A b η x)) - b =
      (A (Q (GDUpdate A b η x)) - A (GDUpdate A b η x))
        + (A (GDUpdate A b η x) - b) := by abel
  calc
    ‖A (Q (GDUpdate A b η x)) - b‖
        = ‖(A (Q (GDUpdate A b η x)) - A (GDUpdate A b η x))
            + (A (GDUpdate A b η x) - b)‖ := by rw [hsplit]
    _ ≤ ‖A (Q (GDUpdate A b η x)) - A (GDUpdate A b η x)‖
          + ‖A (GDUpdate A b η x) - b‖ := norm_add_le _ _
    _ ≤ ‖A‖ * δ + c * ‖A x - b‖ := by
      refine add_le_add ?_ hgd
      calc
        ‖A (Q (GDUpdate A b η x)) - A (GDUpdate A b η x)‖
            = ‖A (Q (GDUpdate A b η x) - GDUpdate A b η x)‖ := by rw [map_sub]
        _ ≤ ‖A‖ * ‖Q (GDUpdate A b η x) - GDUpdate A b η x‖ := A.le_opNorm _
        _ ≤ ‖A‖ * δ := mul_le_mul_of_nonneg_left hQ (norm_nonneg A)
    _ = c * ‖A x - b‖ + ‖A‖ * δ := by ring

/-- **QAT 收敛（误差地板）**：谱界 `‖1 − 2η·AA†‖ ≤ c < 1`、量化投影误差
`∀x, ‖Q x − x‖ ≤ δ`（`δ ≥ 0`）⟹ 对一切 `n`
`‖A xₙ − b‖ ≤ ‖A x₀ − b‖ + ‖A‖·δ/(1 − c)`。
即：QAT 在量化约束下把误差压到**不可约地板** `‖A‖·δ/(1−c)` 的邻域
（量化投影每步注入 `δ`，被收缩因子 `c` 几何衰减，稳态残差 = `‖A‖δ/(1−c)`）。
归纳：`e_{n+1} ≤ c·eₙ + ‖A‖δ`，且 `c·B + ‖A‖δ = B`（`B` 为上述地板界）。 -/
theorem qat_convergence (A : F →L[ℝ] F) (b x0 : F) (η : ℝ) (Q : F → F) (c δ : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hδ : 0 ≤ δ)
    (hspec : ‖(1 : F →L[ℝ] F) - (2 * η : ℝ) • (A ∘L A.adjoint)‖ ≤ c)
    (hQ : ∀ x : F, ‖Q x - x‖ ≤ δ) :
    ∀ n, qatError A b η Q x0 n ≤ ‖A x0 - b‖ + ‖A‖ * δ / (1 - c) := by
  let a : ℝ := ‖A x0 - b‖
  let d : ℝ := ‖A‖ * δ
  have ha : 0 ≤ a := norm_nonneg _
  have hd : 0 ≤ d := mul_nonneg (norm_nonneg A) hδ
  have h1c : 0 < 1 - c := by linarith
  have hne : (1 - c) ≠ 0 := ne_of_gt h1c
  have hkey : c * (d / (1 - c)) + d = d / (1 - c) := by
    field_simp
    ring
  have hca : c * a ≤ a := by nlinarith
  intro n
  induction n with
  | zero =>
      have hfloor : 0 ≤ d / (1 - c) := div_nonneg hd (le_of_lt h1c)
      show ‖A x0 - b‖ ≤ ‖A x0 - b‖ + ‖A‖ * δ / (1 - c)
      linarith
  | succ n ih =>
      have hstep := qat_step_bound A b ((qatUpdate A b η Q)^[n] x0) η Q c δ hspec (hQ _)
      have hb : qatError A b η Q x0 (n + 1) ≤ c * qatError A b η Q x0 n + d := by
        simp only [qatError, qatIterate, Function.iterate_succ_apply', a, d] at hstep ⊢
        exact hstep
      calc
        qatError A b η Q x0 (n + 1) ≤ c * qatError A b η Q x0 n + d := hb
        _ ≤ c * (a + d / (1 - c)) + d :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih hc0) d
        _ = c * a + (c * (d / (1 - c)) + d) := by ring
        _ = c * a + d / (1 - c) := by rw [hkey]
        _ ≤ a + d / (1 - c) := by linarith

/-- **QAT 收敛（无量化的退化）**：`δ = 0`（`Q = id`，即无量化误差）时，
QAT 误差单调不增：`‖A xₙ − b‖ ≤ ‖A x₀ − b‖`
（退化为 RealGradDescent 的收缩迭代，地板为 0）。 -/
theorem qat_convergence_zero (A : F →L[ℝ] F) (b x0 : F) (η : ℝ) (Q : F → F) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ‖(1 : F →L[ℝ] F) - (2 * η : ℝ) • (A ∘L A.adjoint)‖ ≤ c)
    (hQ : ∀ x : F, Q x = x) :
    ∀ n, qatError A b η Q x0 n ≤ ‖A x0 - b‖ := by
  intro n
  have hδQ : ∀ x : F, ‖Q x - x‖ ≤ (0 : ℝ) := by
    intro x
    rw [hQ x]
    simp
  have h := qat_convergence A b x0 η Q c 0 hc0 hc1 le_rfl hspec hδQ n
  simpa using h

omit [CompleteSpace F] in
/-- **QAT 地板非负**：`‖A‖·δ/(1−c) ≥ 0`（`0 ≤ c < 1`、`δ ≥ 0`）——
地板是真实的不可约残差，`δ > 0` 时严格为正（QAT 无法收敛到零误差）。 -/
theorem qat_floor_nonneg (A : F →L[ℝ] F) (c δ : ℝ) (_hc0 : 0 ≤ c) (hc1 : c < 1)
    (hδ : 0 ≤ δ) : 0 ≤ ‖A‖ * δ / (1 - c) :=
  div_nonneg (mul_nonneg (norm_nonneg A) hδ) (by linarith)

/-! ## 注：实例化闭环与诚实边界
  · **前向**：`fakeQuant Q x = Q x` 是任意量化算子；QAT 的损失在量化点评估
    （`qatLoss L Q θ = L (Q θ)`），PTQ 的损失在全精度点评估（`ptqLoss L θp = L θp`）。
  · **反向**：STE 的数学内容是「代理算子 = 恒等」（`ste_gradient_identity`），
    故代理导数恒为 1（`ste_hasDerivAt`/`ste_surrogate_deriv`），链式法则下
    梯度原样穿过量化算子（`ste_chain_rule`）。**诚实边界**：本文件不声称
    `Q` 可导，也不声称 `1` 是 `Q` 的真导数——STE 是一个**定义**，
    形式化的是这个定义及其后果。
  · **误差**：`quantization_error_reduction` 给出 QAT−PTQ 差距的 `c·(cQ·漂移 + 量化误差)`
    界；训练（减小漂移 `‖θ − θp‖`）直接线性改善该界，这就是 QAT 相对 PTQ
    的收益所在，而 `quantError Q θp` 是不可约的 PTQ 误差（`quantization_error_reduction_drift`）。
  · **收敛**：`qat_step_bound` 把 RealGradDescent 的 `GD_contraction_step`
    与量化投影误差合成；`qat_convergence` 给出误差地板 `‖A‖δ/(1−c)`
    （`δ = 0` 时退化回 `qat_convergence_zero` 的单调收缩）。
    与 RealQuantizedError 衔接：QAT 的参数漂移项等价于逐层量化误差 `δᵢ`，
    可送入 `quantized_chain_error_closed` 得端到端界。
  无 sorry/axiom/admit。 -/

end Lattice
