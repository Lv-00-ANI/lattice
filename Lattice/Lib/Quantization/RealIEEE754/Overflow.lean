import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Quantization.RealIEEE754.Basic

/-!
# LATTICE: IEEE-754 的语义化建模 —— 舍入模式、相对误差界与边界行为

`RealFloatFormat` 给出抽象浮点格式 `FloatFormat`（`eps`/`tiny`）与**两条公理的舍入算子**
`RoundOp`（`err_bound` + `idem`）。本文件把它**语义化**：补齐 IEEE-754 的可见结构，并把
原有的两条公理收敛为「最近偶数舍入」这一模式下的**一个字段**，其余性质（幂等、单调、
符号保持、次正规界）以字段/定理形式给出。

  1. `RoundMode`（inductive）：round-to-nearest-even / toward-zero / toward-up / toward-down
     四种舍入模式，以及 `isDirected`/`isNearest` 的判定与 `isDirected_iff`；
  2. `IEEERound`（structure）：带模式的舍入算子 ——
     · `err_bound`：`|round x − x| ≤ eps·|x| + tiny`（**最近偶数/正规范围**语义；作为字段）
     · `idem`：幂等 `round (round x) = round x`
     · `monotone`：单调性（舍入保序）
     · `sign_preserve_pos`/`sign_preserve_neg`：符号保持（非负数舍入非负、非正数舍入非正）
     · `subnormal_bound`：**次正规区**「`tiny` 以下绝对值不增」（`|x| ≤ tiny ⟹ |round x| ≤ tiny`）
  3. 基本性质定理：`ieee_round_idempotent`（幂等）、`ieee_round_mono`（单调）、
     `ieee_round_sign_pos`/`ieee_round_sign_neg`（符号保持）、`ieee_round_zero`（`round 0 = 0`，
     由双侧符号保持夹出）；
  4. **相对误差界**：`InNormalRange F x`（即 `tiny ≤ eps·|x|`，绝对底被相对项支配的「正规范围」）
     下 `ieee_relative_error_bound`：`|round x − x| ≤ 2·eps·|x|`
     ——纯相对形式（常数 2 来自把 `tiny` 吸收进相对项，诚实标注）；
  5. 次正规边界：`ieee_subnormal_abs_bound`（绝对值不增）、`ieee_subnormal_error_le`
     （`|round x − x| ≤ 2·tiny`，相对界失效、只剩绝对底）；
  6. **指数范围与溢出约定**：`fpOverflow M x`（`M < |x|`）、`OverflowConv`（`toInfinity` /
     `saturate` 两种约定）、`clampTo M x`（饱和函数 `max (−M) (min M x)`），以及
     `clampTo_abs_le`/`clampTo_eq_self`/`clampTo_idem`/`clampTo_mono`/`clampTo_no_overflow`/
     `clampTo_error_le`（`|clamp x − x| ≤ max 0 (|x| − M)`）；
  7. **与既有 `RealFloatFormat.RoundOp` 的兼容定理（本文件的桥）**：`ieeeToRoundOp` 把
     `IEEERound` 的算子提升为 `RoundOp`，`ieee_satisfies_roundOp` 逐条证明 `RoundOp` 的
     **两条字段**均被满足；`ieee_format_error_bound`/`ieee_op_error_propagation` 直接调用
     `RealFloatFormat` 的既有定理，说明既有抽象层的全部结论在 IEEE 语义下**原样可用**。

诚实标注（关键边界，均为显式假设的数据而非 Lean `axiom`）：
  · 本文件**不建模位模式**（不建模符号位/尾数位/指数偏置的具体布局、不建模 NaN/Inf 的位表示）；
  · `err_bound` 是「最近偶数 + 正规范围」的语义假设（`RoundMode` 只标记模式，不参与推导）；
  · `monotone`/`sign_preserve_*`/`subnormal_bound` 是舍入函数的**附加语义假设**（结构字段），
    它们不是从 `err_bound` 推出的定理；
  · `±∞` 约定在 `ℝ` 中**不可表示**（诚实降级：只用 `fpOverflow` 谓词标记「已溢出」，
    饱和约定则由 `clampTo` 具体建模）；
  · **B16-1 已补（定向单侧误差，见 §八）**：原标注「定向舍入的真实误差是单侧的，
    本文件用同一个双侧界覆盖，故常数可能偏保守」——现以 `IEEEDirected` 补上**单侧**语义
    （`towardDown` 的 `round x ≤ x`、`towardUp` 的 `x ≤ round x`、
    `towardZero` 的 `|round x| ≤ |x|`）与单侧误差界
    （`ieee_directed_down_error`/`ieee_directed_up_error`/`ieee_directed_zero`/
    `ieee_directed_down_relative`）。这些单侧性是**结构字段**（显式语义假设），
    **不**从 `err_bound` 推出（`RoundMode` 是纯枚举，不携带符号信息）；
    **未做**：从位模式构造出满足它们的舍入函数。
  · **B16-2 已补（`eps`/`tiny` 从位宽推导，见 §九）**：原标注「`eps`/`tiny` 仍来自
    `FloatFormat`，本文件不从位宽推导它们」——现以 `BinaryFormat p emax` 用
    `eps = 2^(1−p)`、`tiny = 2^(1−emax)` **计算**这两个参数，并给出
    `binary32`（`p=24` → `eps=2^(−23)`）与 `binary64`（`p=53` → `eps=2^(−52)`）
    的实例与数值验证，以及到抽象 `FloatFormat` 的桥 `BinaryFormat.toFloatFormat`。
    **未做**：从位模式构造舍入函数（本节是参数换算的算术）。
无 sorry/axiom/admit；模型无关（任意实数函数与任意维数）。
-/

noncomputable section

namespace Lattice


/-! ## 六、指数范围的溢出与两种溢出约定 -/

/-- **溢出谓词**：`M < |x|`（超过最大有限值 `M`）。
`±∞` 约定下结果不再是有限实数；本文件在 `ℝ` 中只保留该谓词（诚实降级）。 -/
def fpOverflow (M x : ℝ) : Prop := M < |x|

/-- 溢出谓词的展开形式。 -/
theorem fpOverflow_iff (M x : ℝ) : fpOverflow M x ↔ M < |x| := Iff.rfl

/-- **溢出约定**：IEEE 默认溢出到 `±∞`；训练/推理中常用「饱和」约定钳到最大有限值。 -/
inductive OverflowConv where
  /-- 溢出到 ±∞（在 ℝ 上不可表示，仅以 `fpOverflow` 标记） -/
  | toInfinity : OverflowConv
  /-- 饱和：钳到 `±M` -/
  | saturate : OverflowConv
  deriving DecidableEq, Repr

/-- 两种溢出约定穷尽。 -/
theorem overflowConv_exhaustive (c : OverflowConv) : c = .toInfinity ∨ c = .saturate := by
  cases c <;> simp

/-- **饱和函数**（saturate 约定）：`max (−M) (min M x)`，把 `x` 钳到 `[−M, M]`。 -/
def clampTo (M x : ℝ) : ℝ := max (-M) (min M x)

/-- 饱和结果的绝对值不超过 `M`（`M ≥ 0`）。 -/
theorem clampTo_abs_le (M x : ℝ) (hM : 0 ≤ M) : |clampTo M x| ≤ M := by
  rw [abs_le]
  constructor
  · simp only [clampTo]
    exact le_max_left _ _
  · simp only [clampTo]
    exact max_le (by linarith) (min_le_left _ _)

/-- 未溢出（`|x| ≤ M`）时饱和不改变输入。 -/
theorem clampTo_eq_self (M x : ℝ) (_hM : 0 ≤ M) (hx : |x| ≤ M) : clampTo M x = x := by
  have h1 : -M ≤ x := (abs_le.mp hx).1
  have h2 : x ≤ M := (abs_le.mp hx).2
  simp only [clampTo]
  rw [min_eq_right h2, max_eq_right h1]

/-- 饱和幂等：`clamp (clamp x) = clamp x`。 -/
theorem clampTo_idem (M x : ℝ) (hM : 0 ≤ M) : clampTo M (clampTo M x) = clampTo M x :=
  clampTo_eq_self M (clampTo M x) hM (clampTo_abs_le M x hM)

/-- 饱和单调。 -/
theorem clampTo_mono (M : ℝ) : Monotone (clampTo M) := by
  intro a b hab
  simp only [clampTo]
  exact max_le (le_max_left _ _) (le_trans (min_le_min le_rfl hab) (le_max_right _ _))

/-- **饱和不溢出的充分必要条件**：`|clamp x| ≤ M`，故 `¬ fpOverflow M (clamp x)`。 -/
theorem clampTo_no_overflow (M x : ℝ) (hM : 0 ≤ M) : ¬ fpOverflow M (clampTo M x) :=
  not_lt.mpr (clampTo_abs_le M x hM)

/-- **饱和误差**：`|clamp x − x| ≤ max 0 (|x| − M)`
——未溢出时为 0，溢出时恰为超出量（`M ≥ 0`）。 -/
theorem clampTo_error_le (M x : ℝ) (hM : 0 ≤ M) :
    |clampTo M x - x| ≤ max 0 (|x| - M) := by
  by_cases hx : |x| ≤ M
  · rw [clampTo_eq_self M x hM hx, sub_self, abs_zero]
    exact le_max_left _ _
  · rw [not_le] at hx
    rcases lt_abs.mp hx with h | h
    · have hx0 : 0 ≤ x := by linarith
      have hclamp : clampTo M x = M := by
        simp only [clampTo]
        rw [min_eq_left (le_of_lt h), max_eq_right (by linarith)]
      rw [hclamp]
      have hval : |M - x| = |x| - M := by
        rw [abs_of_nonpos (by linarith : M - x ≤ 0), abs_of_nonneg hx0]
        ring
      rw [hval]
      exact le_max_right _ _
    · have hxneg : x < 0 := by linarith
      have hclamp : clampTo M x = -M := by
        simp only [clampTo]
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (by linarith : x ≤ -M)]
      rw [hclamp]
      have hval : |-M - x| = |x| - M := by
        rw [abs_of_nonneg (by linarith : 0 ≤ -M - x), abs_of_neg hxneg]
        ring
      rw [hval]
      exact le_max_right _ _

/-- 溢出输入在饱和约定下严格被改变（`clamp x ≠ x`）。 -/
theorem clampTo_ne_self_of_overflow (M x : ℝ) (hM : 0 ≤ M) (h : fpOverflow M x) :
    clampTo M x ≠ x := by
  intro hc
  have hb : |clampTo M x| ≤ M := clampTo_abs_le M x hM
  rw [hc] at hb
  exact absurd hb (not_le.mpr h)

/-!
# `RealIEEE754` 的第 指数范围的溢出与两种溢出约定。 部分

指数范围的溢出与两种溢出约定。

由 `RealIEEE754.lean` 按原有语义分节拆分而来；节标题与内容未改动。
-/
