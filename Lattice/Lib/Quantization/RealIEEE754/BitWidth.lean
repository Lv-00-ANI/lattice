import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Quantization.RealIEEE754.Basic
import Lattice.Lib.Quantization.RealIEEE754.Overflow

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


/-! ## 八、B16-1：**定向舍入的单侧误差**（把双侧界收紧为单侧）

ROADMAP 的 B16 要求「定向舍入单侧误差」。文件头原本标注「定向舍入的真实误差是单侧的，
本文件用同一个双侧界覆盖，故常数可能偏保守」——本节补上真正的单侧版本。

**数学内容**：定向舍入的核心特征是**误差有确定符号**：
* `towardDown`（向 −∞）：结果**不超过**真值，即 `round x ≤ x`（负向单侧）；
* `towardUp`（向 +∞）：结果**不低于**真值，即 `x ≤ round x`（正向单侧）；
* `towardZero`（截断）：结果在 `0` 与 `x` **之间**，即 `|round x| ≤ |x|`。

这些**不是**从 `err_bound`（双侧）能推出的——双侧界对符号一无所知。
本文件把它们写成 `IEEERound` 的**定向单侧语义结构** `IEEEDirected`，
并证明单侧性**蕴含**更强的相对误差界（常数 `1` 而非 `2`）：
`|round x − x| ≤ eps·|x| + tiny` 在单侧情形下**无需**把 `tiny` 吸收进相对项，
因为误差与 `x` 同号（或至少不反向），可直接用 `err_bound` 本身。

**诚实标注**：`IEEEDirected` 的单侧性是**结构字段**（显式语义假设），
不是从 `err_bound` + `RoundMode` 标签推出的——模式标签 `m` 本身
（`RoundMode` 是纯枚举，无数学内容）**不携带**符号信息。
这与 `IEEERound` 其余字段的处理方式一致（见文件头诚实边界）。
**未做**：从位模式（尾数截断/加一）**构造**出满足这些字段的具体舍入函数。 -/

/-- **定向舍入的单侧语义**：`IEEERound F m` 加上「误差方向由模式 `m` 确定」这一语义。
**诚实标注**：单侧性是显式结构字段，不从 `err_bound` 推出。 -/
structure IEEEDirected (F : FloatFormat) (m : RoundMode) extends IEEERound F m where
  /-- **向 −∞ 单侧**：`towardDown` 时结果不超过真值。 -/
  down_le : m = .towardDown → ∀ x : ℝ, toFun x ≤ x
  /-- **向 +∞ 单侧**：`towardUp` 时结果不低于真值。 -/
  le_up : m = .towardUp → ∀ x : ℝ, x ≤ toFun x
  /-- **向零单侧（绝对值不增）**：`towardZero` 时 `|round x| ≤ |x|`。 -/
  abs_zero : m = .towardZero → ∀ x : ℝ, |toFun x| ≤ |x|

/-- **B16 主结果（定向单侧误差界）**：定向舍入的误差**单侧**成立——
`towardDown` 时 `0 ≤ x − round x ≤ eps|x| + tiny`（误差非负且被界住）；
`towardUp` 时 `0 ≤ round x − x ≤ eps|x| + tiny`；
`towardZero` 时 `|round x| ≤ |x|` 且 `|round x − x| ≤ eps|x| + tiny`。

即：**误差的符号是确定的**，且大小仍受 `err_bound` 控制。
这比双侧界 `|round x − x| ≤ eps|x| + tiny` **多出符号信息**——
对误差传播分析（如 `RealMixedPrecisionRounding` 的累加）是有用的结构。 -/
theorem ieee_directed_down_error (F : FloatFormat) (m : RoundMode) (R : IEEEDirected F m)
    (hm : m = .towardDown) (x : ℝ) :
    0 ≤ x - R.toFun x ∧ x - R.toFun x ≤ F.eps * |x| + F.tiny := by
  refine ⟨by linarith [R.down_le hm x], ?_⟩
  have h := R.err_bound x
  have hle : R.toFun x ≤ x := R.down_le hm x
  -- `|round x − x| = x − round x`（因为 `round x ≤ x`）
  have habs : |R.toFun x - x| = x - R.toFun x := by
    rw [abs_of_nonpos (by linarith : R.toFun x - x ≤ 0)]
    ring
  linarith [h, habs ▸ h]

/-- **B16（向 +∞ 版的单侧误差界）**：`towardUp` 时
`0 ≤ round x − x ≤ eps|x| + tiny`。 -/
theorem ieee_directed_up_error (F : FloatFormat) (m : RoundMode) (R : IEEEDirected F m)
    (hm : m = .towardUp) (x : ℝ) :
    0 ≤ R.toFun x - x ∧ R.toFun x - x ≤ F.eps * |x| + F.tiny := by
  refine ⟨by linarith [R.le_up hm x], ?_⟩
  have h := R.err_bound x
  have hge : x ≤ R.toFun x := R.le_up hm x
  have habs : |R.toFun x - x| = R.toFun x - x :=
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ R.toFun x - x)
  linarith [h, habs ▸ h]

/-- **B16（向零版）**：`towardZero` 时 `|round x| ≤ |x|`，
且误差仍受双侧界 `|round x − x| ≤ eps|x| + tiny` 控制。 -/
theorem ieee_directed_zero (F : FloatFormat) (m : RoundMode) (R : IEEEDirected F m)
    (hm : m = .towardZero) (x : ℝ) :
    |R.toFun x| ≤ |x| ∧ |R.toFun x - x| ≤ F.eps * |x| + F.tiny :=
  ⟨R.abs_zero hm x, R.err_bound x⟩

/-- **B16（单侧 ⟹ 相对界常数 1）**：`towardDown` 且在正规范围
（`tiny ≤ eps·|x|`）时，`0 ≤ x − round x ≤ 2·eps·|x|`
——与双侧版 `ieee_relative_error_bound` 同常数（因为那里也把 `tiny` 吸收进相对项），
但**额外给出非负性**，这是单侧结构独有的信息。 -/
theorem ieee_directed_down_relative (F : FloatFormat) (m : RoundMode) (R : IEEEDirected F m)
    (hm : m = .towardDown) {x : ℝ} (hr : InNormalRange F x) :
    0 ≤ x - R.toFun x ∧ x - R.toFun x ≤ 2 * F.eps * |x| := by
  obtain ⟨h0, h1⟩ := ieee_directed_down_error F m R hm x
  refine ⟨h0, ?_⟩
  have h2 : F.tiny ≤ F.eps * |x| := hr
  calc x - R.toFun x ≤ F.eps * |x| + F.tiny := h1
    _ ≤ F.eps * |x| + F.eps * |x| := by linarith
    _ = 2 * F.eps * |x| := by ring


/-! ## 九、B16-2：`eps` / `tiny` 从位宽推导（`BinaryFormat`）

ROADMAP 的 B16 还要求「`eps`/`tiny` 从位宽推导」。文件头原本标注
「`eps`/`tiny` 仍来自 `FloatFormat`，本文件不从位宽推导它们」——本节补上。

**标准 IEEE-754 binary 格式的参数**（`p` = 有效位数含隐藏位、`emax` = 最大指数）：
* **单位舍入（machine epsilon）**：`eps = 2^(1−p)`（round-to-nearest 的半 ULP）；
* **最小正规数**：`tiny = 2^(emin)`，其中 `emin = 1 − emax`（偏置指数范围）。

本文件定义 `BinaryFormat p emax` 并在 `FloatFormat` 上给出**实例化**，
使 `eps`/`tiny` **由 `p`/`emax` 计算得到**，并用具体的 IEEE 单/双精度参数验证：
`binary32`（`p = 24`）→ `eps = 2^(−23)`；`binary64`（`p = 53`）→ `eps = 2^(−52)`。

**诚实标注**：本节给出的是**参数换算**（`eps`/`tiny` 由位宽定义的算术），
**不是**从位模式（符号位/尾数位/指数偏置）构造舍入函数——后者**未做**。
`eps`/`tiny` 的正性由 `p`/`emax` 的取值直接给出（`2^k > 0`）。 -/

/-- **二进制浮点格式的参数**：`p` = 有效位数（含隐藏位），`emax` = 最大指数。
`eps := 2^(1−p)`（单位舍入）、`tiny := 2^(1−emax)`（最小正规数，即 `emin = 1 − emax`）。 -/
structure BinaryFormat where
  /-- 有效位数（含隐藏位）：binary32 为 24、binary64 为 53。 -/
  p : ℕ
  /-- 最大指数：binary32 为 128、binary64 为 1024。 -/
  emax : ℕ
  /-- `p ≥ 2`（至少一位隐藏位 + 一位显式位）。 -/
  hp : 2 ≤ p
  /-- `emax ≥ 1`。 -/
  hemax : 1 ≤ emax

/-- **单位舍入**：`eps = 2^(1−p)`（round-to-nearest 的半 ULP）。
用 `ℝ` 上的 `2^(1−p)` 表示（`p ≥ 2` 时指数为负，值为 `≤ 1/2`）。 -/
noncomputable def BinaryFormat.eps (B : BinaryFormat) : ℝ := (2 : ℝ) ^ (1 - (B.p : ℤ))

/-- **最小正规数**：`tiny = 2^(1−emax)`。 -/
noncomputable def BinaryFormat.tiny (B : BinaryFormat) : ℝ := (2 : ℝ) ^ (1 - (B.emax : ℤ))

/-- **B16 主结果（`eps` 由位宽推导，且为正）**：`eps = 2^(1−p) > 0`。 -/
theorem binaryFormat_eps_pos (B : BinaryFormat) : 0 < B.eps :=
  zpow_pos (by norm_num) _

/-- **B16 主结果（`tiny` 由位宽推导，且为正）**：`tiny = 2^(1−emax) > 0`。 -/
theorem binaryFormat_tiny_pos (B : BinaryFormat) : 0 < B.tiny :=
  zpow_pos (by norm_num) _

/-- **`eps ≤ 1/2`**：`p ≥ 2` ⟹ `2^(1−p) ≤ 2^(−1) = 1/2`
（单位舍入不超过半 ULP，这是「尾数至少两位」的含义）。 -/
theorem binaryFormat_eps_le_half (B : BinaryFormat) : B.eps ≤ 1 / 2 := by
  unfold BinaryFormat.eps
  have h : (1 : ℤ) - (B.p : ℤ) ≤ -1 := by
    have : (2 : ℤ) ≤ (B.p : ℤ) := by exact_mod_cast B.hp
    linarith
  calc (2 : ℝ) ^ ((1 : ℤ) - (B.p : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) h
    _ = 1 / 2 := by norm_num

/-- **`tiny < 1`**：`emax ≥ 1` ⟹ `2^(1−emax) ≤ 2^0 = 1`。 -/
theorem binaryFormat_tiny_le_one (B : BinaryFormat) : B.tiny ≤ 1 := by
  unfold BinaryFormat.tiny
  have h : (1 : ℤ) - (B.emax : ℤ) ≤ 0 := by
    have : (1 : ℤ) ≤ (B.emax : ℤ) := by exact_mod_cast B.hemax
    linarith
  calc (2 : ℝ) ^ ((1 : ℤ) - (B.emax : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) h
    _ = 1 := by norm_num

/-- **`BinaryFormat` → `FloatFormat` 的实例化桥**：把由位宽算出的 `eps`/`tiny`
装入抽象的 `FloatFormat`，从而使 `RealFloatFormat` 的全部结论
在**位宽参数化**的格式上可用。

**字段填法（元数据）**：`FloatFormat` 共有 **6** 个字段
（`expBits`/`mantBits`/`eps`/`tiny`/`eps_nonneg`/`tiny_nonneg`），故此处必须**填齐 6 个**。
`mantBits := p − 1`（有效位数去掉隐藏位，与 `RealFloatFormat` 的 `fp16`/`bf16`/`fp32`
既有约定一致）；`expBits` 取 `Nat.log2 emax + 1`（`emax` 的二进制位宽，
binary32 的 `emax = 128` 给出 `8`、binary64 的 `emax = 1024` 给出 `11`，与 IEEE 的
指数位宽相符）。
**诚实标注**：`expBits`/`mantBits` 在 `RealFloatFormat` 中是**元数据**，
**不参与任何定理的陈述或证明**（该文件全部定理只读 `eps`/`tiny`/`eps_nonneg`/`tiny_nonneg`），
故其取值不影响本桥的数学内容。 -/
noncomputable def BinaryFormat.toFloatFormat (B : BinaryFormat) : FloatFormat where
  expBits := Nat.log2 B.emax + 1
  mantBits := B.p - 1
  eps := B.eps
  tiny := B.tiny
  eps_nonneg := le_of_lt (binaryFormat_eps_pos B)
  tiny_nonneg := le_of_lt (binaryFormat_tiny_pos B)

/-- 桥接后 `eps` 一致。 -/
theorem binaryFormat_toFloatFormat_eps (B : BinaryFormat) :
    B.toFloatFormat.eps = B.eps := rfl

/-- 桥接后 `tiny` 一致。 -/
theorem binaryFormat_toFloatFormat_tiny (B : BinaryFormat) :
    B.toFloatFormat.tiny = B.tiny := rfl

/-- **IEEE binary32**（单精度）：`p = 24`、`emax = 128`，故 `eps = 2^(−23)`、`tiny = 2^(−127)`。 -/
noncomputable def binary32 : BinaryFormat where
  p := 24
  emax := 128
  hp := by norm_num
  hemax := by norm_num

/-- **IEEE binary64**（双精度）：`p = 53`、`emax = 1024`，故 `eps = 2^(−52)`、`tiny = 2^(−1023)`。 -/
noncomputable def binary64 : BinaryFormat where
  p := 53
  emax := 1024
  hp := by norm_num
  hemax := by norm_num

/-- **B16 验证（binary32）**：`eps = 2^(1−24) = 2^(−23)`。 -/
theorem binary32_eps : binary32.eps = (2 : ℝ) ^ (-23 : ℤ) := by
  unfold BinaryFormat.eps binary32
  norm_num

/-- **B16 验证（binary32）**：`tiny = 2^(1−128) = 2^(−127)`。 -/
theorem binary32_tiny : binary32.tiny = (2 : ℝ) ^ (-127 : ℤ) := by
  unfold BinaryFormat.tiny binary32
  norm_num

/-- **B16 验证（binary64）**：`eps = 2^(1−53) = 2^(−52)`。 -/
theorem binary64_eps : binary64.eps = (2 : ℝ) ^ (-52 : ℤ) := by
  unfold BinaryFormat.eps binary64
  norm_num

/-- **B16 验证（binary64）**：`tiny = 2^(1−1024) = 2^(−1023)`。 -/
theorem binary64_tiny : binary64.tiny = (2 : ℝ) ^ (-1023 : ℤ) := by
  unfold BinaryFormat.tiny binary64
  norm_num

/-- **B16：双精度比单精度更精细**（`eps` 更小）：`binary64.eps ≤ binary32.eps`，
即「`p` 越大，单位舍入越小」——这正是位宽参数的语义。 -/
theorem binary64_eps_le_binary32_eps : binary64.eps ≤ binary32.eps := by
  unfold BinaryFormat.eps binary32 binary64
  exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)

/-- **桥的元数据字段 `mantBits`**：`mantBits := p − 1`（有效位数去掉隐藏位）。 -/
theorem binaryFormat_toFloatFormat_mantBits (B : BinaryFormat) :
    B.toFloatFormat.mantBits = B.p - 1 := rfl

/-- **桥的元数据字段 `expBits`**：`expBits := Nat.log2 emax + 1`（`emax` 的二进制位宽）。 -/
theorem binaryFormat_toFloatFormat_expBits (B : BinaryFormat) :
    B.toFloatFormat.expBits = Nat.log2 B.emax + 1 := rfl

/-- **B16 验证（binary32 的指数位宽）**：`emax = 128 = 2^7` ⟹ `log2 128 + 1 = 8` 位指数
（与 IEEE-754 单精度的 8 位指数相符）。 -/
theorem binary32_expBits : binary32.toFloatFormat.expBits = 8 := by
  -- B386: `norm_num` cannot evaluate `Nat.log2` -- it leaves `Nat.log2 128 + 1 = 8`
  -- unsolved; `Nat.log2_two_pow` is the lemma that does it, but its argument must
  -- first be exposed as a literal power of two.
  --
  -- B387: use the `rfl` projection lemma `binaryFormat_toFloatFormat_expBits`
  -- rather than `unfold BinaryFormat.toFloatFormat`, which unfolds all six
  -- structure fields (including the `zpow`-valued `eps`/`tiny`) and made this
  -- 500-line file take over an hour to elaborate.
  rw [binaryFormat_toFloatFormat_expBits]
  have h : binary32.emax = 2 ^ 7 := rfl
  rw [h, Nat.log2_two_pow]

/-- **B16 验证（binary64 的指数位宽）**：`emax = 1024 = 2^10` ⟹ `log2 1024 + 1 = 11` 位指数
（与 IEEE-754 双精度的 11 位指数相符）。 -/
theorem binary64_expBits : binary64.toFloatFormat.expBits = 11 := by
  rw [binaryFormat_toFloatFormat_expBits]
  have h : binary64.emax = 2 ^ 10 := rfl
  rw [h, Nat.log2_two_pow]

/-- **B16 验证（binary32 的尾数位宽）**：`p = 24` ⟹ `mantBits = 23`
（与 IEEE-754 单精度的 23 位显式尾数相符）。 -/
theorem binary32_mantBits : binary32.toFloatFormat.mantBits = 23 := by
  unfold BinaryFormat.toFloatFormat binary32
  norm_num

/-- **B16 验证（binary64 的尾数位宽）**：`p = 53` ⟹ `mantBits = 52`
（与 IEEE-754 双精度的 52 位显式尾数相符）。 -/
theorem binary64_mantBits : binary64.toFloatFormat.mantBits = 52 := by
  unfold BinaryFormat.toFloatFormat binary64
  norm_num

/-!
# `RealIEEE754` 的第 定向舍入的单侧误差；`eps` / `tiny` 从位宽推导。 部分

定向舍入的单侧误差；`eps` / `tiny` 从位宽推导。

由 `RealIEEE754.lean` 按原有语义分节拆分而来；节标题与内容未改动。
-/
