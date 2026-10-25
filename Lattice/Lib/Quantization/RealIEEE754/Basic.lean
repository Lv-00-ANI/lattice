import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat

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


/-! ## 一、IEEE-754 舍入模式 -/

/-- IEEE-754 的四种舍入模式：最近偶数（默认）、朝零、朝上（+∞ 方向）、朝下（−∞ 方向）。 -/
inductive RoundMode where
  /-- round-to-nearest, ties-to-even -/
  | nearestEven : RoundMode
  /-- round-toward-zero（截断） -/
  | towardZero : RoundMode
  /-- round-toward-+∞（向上） -/
  | towardUp : RoundMode
  /-- round-toward-−∞（向下） -/
  | towardDown : RoundMode
  deriving DecidableEq, Repr

/-- 定向舍入（朝零/朝上/朝下）；最近偶数不是定向舍入。 -/
def RoundMode.isDirected : RoundMode → Prop
  | .nearestEven => False
  | .towardZero => True
  | .towardUp => True
  | .towardDown => True

/-- 是最近舍入（nearest-even）吗？ -/
def RoundMode.isNearest (m : RoundMode) : Prop := m = .nearestEven

/-- **定向模式的刻画**：`isDirected` 恰为三种定向模式之一。 -/
theorem RoundMode.isDirected_iff (m : RoundMode) :
    m.isDirected ↔ (m = .towardZero ∨ m = .towardUp ∨ m = .towardDown) := by
  cases m <;> simp [RoundMode.isDirected]

/-- 最近偶数模式不是定向舍入。 -/
theorem RoundMode.nearestEven_not_directed : ¬ RoundMode.nearestEven.isDirected := by
  simp [RoundMode.isDirected]

/-- 最近偶数模式是最近舍入。 -/
theorem RoundMode.nearestEven_isNearest : RoundMode.nearestEven.isNearest := rfl


/-! ## 二、正规范围与次正规区（指数范围的语义刻画） -/

/-- **正规范围**：`tiny ≤ eps·|x|`，即绝对误差底被相对项支配（此时纯相对界成立）。 -/
def InNormalRange (F : FloatFormat) (x : ℝ) : Prop := F.tiny ≤ F.eps * |x|

/-- **次正规 / 下溢区**：`|x| ≤ tiny`（相对精度失效，只剩绝对底）。 -/
def BelowTiny (F : FloatFormat) (x : ℝ) : Prop := |x| ≤ F.tiny

/-- 正规范围是一个「大输入」性质：它只依赖幅度 `|x|`。 -/
theorem inNormalRange_iff (F : FloatFormat) (x : ℝ) :
    InNormalRange F x ↔ F.tiny ≤ F.eps * |x| := Iff.rfl


/-! ## 三、带模式的舍入算子（IEEE-754 语义） -/

/-- IEEE-754 风格的舍入算子：一个函数加四条**语义假设**
（最近偶数的相对误差界、幂等、单调、符号保持）与一条**次正规区假设**。
**诚实标注**：这些性质是结构字段（显式数据），本文件不建模位模式、不建模 NaN/Inf；
`m : RoundMode` 只标记模式身份，`err_bound` 对四种模式统一给出双侧界。 -/
structure IEEERound (F : FloatFormat) (m : RoundMode) where
  /-- 舍入函数 -/
  toFun : ℝ → ℝ
  /-- 相对误差界（最近偶数 + 正规范围语义）：`|round x − x| ≤ eps·|x| + tiny` -/
  err_bound : ∀ x : ℝ, |toFun x - x| ≤ F.eps * |x| + F.tiny
  /-- 幂等性：`round (round x) = round x` -/
  idem : ∀ x : ℝ, toFun (toFun x) = toFun x
  /-- 单调性：舍入保序 -/
  monotone : Monotone toFun
  /-- 符号保持（非负）：`0 ≤ x ⟹ 0 ≤ round x` -/
  sign_preserve_pos : ∀ x : ℝ, 0 ≤ x → 0 ≤ toFun x
  /-- 符号保持（非正）：`x ≤ 0 ⟹ round x ≤ 0` -/
  sign_preserve_neg : ∀ x : ℝ, x ≤ 0 → toFun x ≤ 0
  /-- **次正规区**：`|x| ≤ tiny ⟹ |round x| ≤ tiny`（`tiny` 以下绝对值不增） -/
  subnormal_bound : ∀ x : ℝ, |x| ≤ F.tiny → |toFun x| ≤ F.tiny


/-! ## 四、基本性质 -/

/-- **幂等**：`round (round x) = round x`。 -/
theorem ieee_round_idempotent (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) (x : ℝ) :
    R.toFun (R.toFun x) = R.toFun x := R.idem x

/-- **单调**：`a ≤ b ⟹ round a ≤ round b`。 -/
theorem ieee_round_mono (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {a b : ℝ}
    (h : a ≤ b) : R.toFun a ≤ R.toFun b := R.monotone h

/-- **符号保持（非负）**。 -/
theorem ieee_round_sign_pos (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x : ℝ}
    (h : 0 ≤ x) : 0 ≤ R.toFun x := R.sign_preserve_pos x h

/-- **符号保持（非正）**。 -/
theorem ieee_round_sign_neg (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x : ℝ}
    (h : x ≤ 0) : R.toFun x ≤ 0 := R.sign_preserve_neg x h

/-- **零的舍入**：`round 0 = 0`（由两侧符号保持夹出）。 -/
theorem ieee_round_zero (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) :
    R.toFun 0 = 0 :=
  le_antisymm (R.sign_preserve_neg 0 le_rfl) (R.sign_preserve_pos 0 le_rfl)

/-- **幂等是单调意义下的「落在格点上」**：舍入结果的再舍入不变。 -/
theorem ieee_round_fixed_point (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) (x : ℝ) :
    R.toFun (R.toFun x) = R.toFun x := R.idem x


/-! ## 五、相对误差界（正规范围）与次正规边界 -/

/-- **相对误差界**：在正规范围（`tiny ≤ eps·|x|`）且 `0 < |x|` 时，
`|round x − x| ≤ 2·eps·|x|`。
**诚实标注**：常数 `2` 而非 `1`，因为本文件把绝对底 `tiny` 直接吸收进相对项
（`tiny ≤ eps·|x|` 时 `eps|x| + tiny ≤ 2·eps|x|`）；若要常数 1 需更强的「最近偶数」语义。 -/
theorem ieee_relative_error_bound (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x : ℝ}
    (_hx : 0 < |x|) (hr : InNormalRange F x) :
    |R.toFun x - x| ≤ 2 * F.eps * |x| := by
  have h1 : |R.toFun x - x| ≤ F.eps * |x| + F.tiny := R.err_bound x
  have h2 : F.tiny ≤ F.eps * |x| := hr
  calc
    |R.toFun x - x| ≤ F.eps * |x| + F.tiny := h1
    _ ≤ F.eps * |x| + F.eps * |x| := by linarith
    _ = 2 * F.eps * |x| := by ring

/-- 有界输入的舍入误差界：`|x| ≤ Mn ⟹ |round x − x| ≤ eps·Mn + tiny`
（与 `RealFloatFormat.format_error_bound_of_le` 同形，此处经 IEEE 语义表述）。 -/
theorem ieee_error_bound_of_le (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x Mn : ℝ}
    (hx : |x| ≤ Mn) : |R.toFun x - x| ≤ F.eps * Mn + F.tiny := by
  refine le_trans (R.err_bound x) ?_
  exact add_le_add_right (mul_le_mul_of_nonneg_left hx F.eps_nonneg) F.tiny

/-- **次正规区绝对值不增**：`|x| ≤ tiny ⟹ |round x| ≤ tiny`。 -/
theorem ieee_subnormal_abs_bound (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x : ℝ}
    (h : BelowTiny F x) : |R.toFun x| ≤ F.tiny := R.subnormal_bound x h

/-- **次正规区误差被绝对底支配**：`|x| ≤ tiny ⟹ |round x − x| ≤ 2·tiny`
（相对界在此失效，只剩不可约的绝对底）。 -/
theorem ieee_subnormal_error_le (F : FloatFormat) (m : RoundMode) (R : IEEERound F m) {x : ℝ}
    (h : BelowTiny F x) : |R.toFun x - x| ≤ 2 * F.tiny := by
  have hA : |R.toFun x| ≤ F.tiny := R.subnormal_bound x h
  have hB : |x| ≤ F.tiny := h
  have key : |R.toFun x - x| ≤ |R.toFun x| + |x| := by
    have hsplit : R.toFun x - x = R.toFun x + -x := by ring
    rw [hsplit]
    simpa using abs_add (R.toFun x) (-x)
  calc
    |R.toFun x - x| ≤ |R.toFun x| + |x| := key
    _ ≤ F.tiny + F.tiny := add_le_add hA hB
    _ = 2 * F.tiny := by ring

/-- 次正规区与正规范围的互补刻画（按幅度划分输入）：`|x| ≤ tiny` 或 `tiny < |x|`。 -/
theorem belowTiny_or_not (F : FloatFormat) (x : ℝ) : BelowTiny F x ∨ ¬ BelowTiny F x :=
  em _

/-!
# `RealIEEE754` 的第 基础 部分

基础：舍入模式、指数范围、带模式的算子、基本性质、相对误差界。

由 `RealIEEE754.lean` 按原有语义分节拆分而来；节标题与内容未改动。
-/
