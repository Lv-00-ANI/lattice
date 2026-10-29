

import Lattice.Lib.Quantization.RealIEEE754.Basic
import Lattice.Lib.Quantization.RealIEEE754.Nonvacuous
import Lattice.Lib.Quantization.RealIEEE754.Overflow
import Lattice.Lib.Quantization.RealIEEE754.BitWidth
import Lattice.Lib.Quantization.RealIEEE754.Compat

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


/-! ## 注：本文件的定位、诚实边界与后续文件
  · **定位**：`RealFloatFormat` 用两条公理刻画舍入；本文件把公理**语义化**为
    「最近偶数 + 正规范围」的 `IEEERound`（多出单调、符号保持、次正规界三条语义字段），
    并用 `ieeeToRoundOp`/`ieee_satisfies_roundOp` 证明它与原抽象**兼容**：
    `RoundOp` 的两条字段均成立，故 `RealFloatFormat` 的全部定理在 IEEE 语义下原样可用。
  · **相对误差界**：`ieee_relative_error_bound` 在正规范围 `tiny ≤ eps·|x|` 下给出
    `≤ 2·eps·|x|`；常数 2 是诚实标注（把 `tiny` 吸收进相对项），不是「最近偶数」的紧界。
  · **边界行为**：次正规区 `|x| ≤ tiny` 时 `|round x| ≤ tiny`（绝对值不增，
    `ieee_subnormal_abs_bound`）且误差 `≤ 2·tiny`（`ieee_subnormal_error_le`）；
    溢出侧给出两种约定：`OverflowConv.toInfinity`（ℝ 中不可表示，仅谓词）与
    `OverflowConv.saturate`（`clampTo`，误差 `≤ max 0 (|x| − M)`）。
  · **未做/降级**：不建模位模式与 NaN/Inf；`toInfinity` 约定未数值化；
    定向舍入的真实单侧误差未单独建模（统一用双侧界覆盖，故偏保守）。
  · **后续**：`RealMixedPrecisionRounding` 在本文件的舍入语义下重推混合精度的
    单次误差、k 次累加误差与饱和误差；`RealEvalBridge` 给出可执行实现与数值自检。
  无 sorry/axiom/admit。 -/

end Lattice
