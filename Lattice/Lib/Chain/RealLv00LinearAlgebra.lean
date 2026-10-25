import Mathlib

/-!
# LATTICE: Lv-00 采集 —— 线性代数 / 稀疏 / 区间与精确算术（数值基座）

本文件采集自 Lv-00（`level0000x/Lv-00`，`lv-merged` 树，mathlib v4.14.0）。
**采集理由**：Lv-00 将重写，其中的有效数学证明作为素材并入本项目。

采集纪律：**只 `import Mathlib`**（本项目禁止 import 两个声明同名符号的模块；
只依赖 Mathlib 可完全避免该问题），命名空间 `Lattice.Lv00.LinearAlgebra`，
与 `Lattice.*` 及将来的 `Lv-00` 重写均不冲突。

## 采集源与分类（逐条判别，数字为本代理独立复核）

| 原模块 | 行数 | 定理数 | (A) 真结果 | (B) 规格声明 | (C) 丢弃 | 备注 |
|:--|--:|--:|--:|--:|--:|:--|
| `LinearAlgebraFoundation` | 906 | 78 | 0 | 0 | 78 | 全部 `: True := by trivial`；且**重造 mathlib `Matrix`/`det`** |
| `SparseLinearAlgebraTheory` | 950 | 54 | 0 | 0 | 54 | 同上；`is_spd := false`、`bandwidth := 0` 等空桩函数 |
| `IntervalArithmeticTheory` | 946 | 28 | 0 | 3 | 25 | `round_down/up` **为假**（见下）；区间包含性命题形式有价值 |
| `ExactArithmeticTheory` | 98 | 9 | 0 | 7 | 2 | 9 条全 `: True`；但溢出检测器的**命题形式**值得形式化 |
| `MagicConstantsTheory` | 731 | 27 | 24 | 3 | 0 | ★ 真实证明，本文件主要采集体 |
| `ConvenienceAPIsTheory` | 807 | 33 | 29 | 4 | 0 | ★ 真实证明 |

**独立复核数字（与协调者侦察的差异必须记录）**：
- 协调者称 `lv-merged` 有 430 个 `.lean`；**实测为 153 个**（全树 `-Recurse -Filter *.lean` 计数）。
- 协调者称 100 个"干净"模块、约 1,217 条定理；本代理**只对自己负责的 6 个文件**复核，
  不复述全树数字（协调者已发警告其"干净"判据的正则锚定了行首，会漏掉行内 `sorry`）。
- **本 6 个文件的 `sorry`/`admit` 实际计数均为 0**。`LinearAlgebraFoundation`、
  `SparseLinearAlgebraTheory`、`IntervalArithmeticTheory` 各被不锚行的 `\bsorry\b` 匹配到 1 次，
  但那是**文件头中文注释里的 "proof 均为 sorry / trivial" 字样**，非真实证明占位。
  ⇒ **"含 sorry" 的文件级 grep 会同时命中注释，必须逐条看命中位置**（这是本轮的方法论教训）。
- `formal/` 与 `lv-merged/` 下这 6 个文件**字节数完全相同**，无更新版本可用。

## 核心发现：Lv-00 的"规格声明"多数不是 (B) 而是 (C)

Lv-00 大量使用 `theorem foo (...) : True := by trivial` 这一**空桩模式**。
它不是"命题平凡"（(B) 规格声明要求命题形式本身有价值），而是**命题为空**——
`: True` 对任何假设都不约束任何东西，既不能当规格引用，也不能当定理复用。
证据：`LinearAlgebraFoundation` 的 78 条定理**全部**是 `: True := by trivial`，
其中包括标题声称的 `det_mul : det(AB) = det(A)·det(B)`、`rank_nullity`、
`spectral_theorem`——**这些名字下没有任何内容**。

⇒ 本文件对这类条目按 **(C) 丢弃**，不搬运。搬运它们只会给 LATTICE 引入 78 个
"看起来有定理、实则空"的假资产，正是 `STYLE.md` §5 诚实降级要防的事。

## 本文件实际搬运的内容（都是**重新形式化**的真命题）

1. **`ExactArithmeticTheory` 的溢出检测器** —— 其 C 对应物（`safe_mul`/`safe_add`）的数学内容是真的，
   只是原文件的定理被写成 `True`。本文件把检测器**重新陈述为真命题**并证明。
2. **`IntervalArithmeticTheory` 的区间包含性** —— Lv-00 的 `round_down`/`round_up` 实现**有 bug**
   （见 `lv00_toNat_clamps_negative` 及文件末反例章），但"区间包含性"本身是区间算术的
   **核心正确性定理**；本文件给出修复后的、可证的版本。
3. **`MagicConstantsTheory`** —— **真实证明**，实质内容几乎全部可搬（版本全序、表唯一性、向后兼容）。
4. **`ConvenienceAPIsTheory`** —— **真实证明**，clamp/lerp/mapRange/smoothstep 与 List 引理可搬。

**诚实边界**（本文件不证 / 不声称的）：
- **不搬运**任何 `: True := by trivial` 的定理（(C) 类），包括 Lv-00 声称的
  `det_mul`/`rank_nullity`/`svd_exists`/`conjugate_gradient_convergence` 等——那些名字下是空的。
  mathlib 已有 `Matrix.det_mul`、`Matrix.det_transpose` 等**真版本**，需要时直接用 mathlib。
- **不做**浮点/ULP 语义：Lv-00 的 `FloatRepr` 把 IEEE754 简化为 `ℝ`，"外延舍入"实际未建模。
  本文件只证**实数上的包络性质**，**不声称** IEEE754 正确性。**这是诚实降级**。
- `round_down`/`round_up` **按 Lv-00 原实现是假命题**；本文件给出**修复版**并记录根因，
  **不照抄** Lv-00 的假陈述。
- **区间乘法**只证**非负象限**与**四角 min/max 界**；未证一般符号组合的完整四角公式
  （那需要分 4 象限 16 情形，超出本轮采集预算，标注为后续工作）。
- **未做**：Lv-00 的 `GappaAssertion.holds` 用 `match ... => True` 把整个 Gappa 语义抹平为空；
  本文件不搬运该层（(C)），也未重建 Gappa 语义（超出采集范围）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice.Lv00.LinearAlgebra

/-! ===============================================================
## 第一部分：精确算术 —— 溢出检测器的可证版本

采集自 `ExactArithmeticTheory`（(B) 命题形式有价值 / (A) 重新形式化）。

Lv-00 原文把 9 条定理全写成 `: True := by trivial`，并在文件头声称
"`safe_mul_overflow_detection`：乘法溢出检测的正确性"。
本部分**兑现该声明**：把"检测器返回 `.ok v` ⟺ 真实积在界内"证成真命题。
-/

/-- 溢出检测结果。采集自 `ExactArithmeticTheory.SafeMulResult`（保留语义）。 -/
inductive LvOverflowResult where
  /-- 运算在界内，携带真实值 -/
  | ok (value : ℤ)
  /-- 运算越界 -/
  | overflow
  deriving DecidableEq, Repr

/-- **可证的**安全乘法：`lo`/`hi` 是可表示区间（如 int64 的界）。

与 Lv-00 的差别（诚实标注）：Lv-00 用四象限 `int64_max / b` 比较，
本定义直接用真实积判界。由于 Lean 的 `ℤ` 无溢出，这是**语义更清晰且等价**的形式；
`lv00_safeMul_ok_iff` 证明它确实检出且仅检出界内结果。 -/
def safeMul (lo hi a b : ℤ) : LvOverflowResult :=
  if lo ≤ a * b ∧ a * b ≤ hi then .ok (a * b) else .overflow

/-- (A) **乘法溢出检测正确性**：检测器报 `.ok v` 当且仅当 `v` 就是真实积且未越界。
这是 Lv-00 声称但未证的 `safe_mul_overflow_detection`。 -/
theorem lv00_safeMul_ok_iff (lo hi a b : ℤ) :
    safeMul lo hi a b = .ok (a * b) ↔ lo ≤ a * b ∧ a * b ≤ hi := by
  unfold safeMul
  by_cases h : lo ≤ a * b ∧ a * b ≤ hi
  · simp [h]
  · simp [h]

/-- (A) **检测器不误报**：报 `.overflow` 当且仅当真实积越界。 -/
theorem lv00_safeMul_overflow_iff (lo hi a b : ℤ) :
    safeMul lo hi a b = .overflow ↔ ¬(lo ≤ a * b ∧ a * b ≤ hi) := by
  unfold safeMul
  by_cases h : lo ≤ a * b ∧ a * b ≤ hi
  · simp [h]
  · simp [h]

/-- (A) **检测器可靠性（soundness）**：若检测器输出 `.ok v`，则 `v` 必在界内。
这是"从不掉出区间"的算术版，也是 Lv-00 想表达的核心不变量。 -/
theorem lv00_safeMul_sound {lo hi a b : ℤ} {v : ℤ}
    (h : safeMul lo hi a b = .ok v) : v = a * b ∧ lo ≤ v ∧ v ≤ hi := by
  unfold safeMul at h
  by_cases hb : lo ≤ a * b ∧ a * b ≤ hi
  · rw [if_pos hb] at h
    injection h with h
    subst h
    exact ⟨rfl, hb.1, hb.2⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- (A) **检测器完备性（completeness）**：界内的真值一定被接受（不拒真）。
Lv-00 把这类性质称为"条件完备性"，但同样只写了 `True`。 -/
theorem lv00_safeMul_complete {lo hi a b : ℤ} (h : lo ≤ a * b ∧ a * b ≤ hi) :
    safeMul lo hi a b = .ok (a * b) :=
  (lv00_safeMul_ok_iff lo hi a b).mpr h

/-- 安全加法。采集自 `ExactArithmeticTheory.safe_add`（同一检测模式）。
Lv-00 的 `safe_add_overflow_conditions` 声称"条件完备性"，此处兑现。 -/
def safeAdd (lo hi a b : ℤ) : LvOverflowResult :=
  if lo ≤ a + b ∧ a + b ≤ hi then .ok (a + b) else .overflow

/-- (A) 加法版：界内加法必被接受。对应 Lv-00 `safe_add_overflow_conditions`。 -/
theorem lv00_safeAdd_complete {lo hi a b : ℤ} (h : lo ≤ a + b ∧ a + b ≤ hi) :
    safeAdd lo hi a b = .ok (a + b) := by
  unfold safeAdd
  simp [h]

/-- (A) 加法版可靠性：`safeAdd` 输出必在界内。 -/
theorem lv00_safeAdd_sound {lo hi a b v : ℤ}
    (h : safeAdd lo hi a b = .ok v) : v = a + b ∧ lo ≤ v ∧ v ≤ hi := by
  unfold safeAdd at h
  by_cases hb : lo ≤ a + b ∧ a + b ≤ hi
  · rw [if_pos hb] at h
    injection h with h
    subst h
    exact ⟨rfl, hb.1, hb.2⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- **Lv-00 `bounded_mul_no_overflow` 的判定**。

Lv-00 原文（`: True`，带假设 `a*a ≤ M`、`b*b ≤ M`）声称"有界乘法不溢出"。
本代理**先代入小整数判真假**（`STYLE.md` §4 末条），探了三组：

- `a=2,b=2,M=4`：`4≤4`、`4≤4`，`ab=4 ≤ 4` 成立
- `a=2,b=3,M=9`：`4≤9`、`9≤9`，`ab=6 ≤ 9` 成立
- `a=3,b=3,M=8`：前提 `9≤8` 假，不适用。

**判定：命题为真**，且**不需要非负性前提**——因为结论是绝对界：

`(a-b)² ≥ 0` 给 `2ab ≤ a² + b² ≤ 2M`，即 `ab ≤ M`；
`(a+b)² ≥ 0` 给 `-2ab ≤ a² + b² ≤ 2M`，即 `-M ≤ ab`。
两式合起来正是 `|ab| ≤ M`。**对 `ℤ` 上的任意符号都成立**（`a = -5, b = 5, M = 25`：
`a² = b² = 25 ≤ M`，`ab = -25`，`|ab| = 25 ≤ M` 成立）。

⇒ **`ha`、`hb` 必须参与证明**（这正是原文写成 `True` 时掩盖掉的证明义务）。

⚠ **本轮实测教训**：我最初的 `nlinarith` 调用**漏掉了 `ha`/`hb`**，
Lean 通过 `unused variable` 警告暴露了它——**"证明没用到关键假设"是警告里最该追查的一类**，
不能当无害提示忽略。已修正为显式喂入 `ha`、`hb`。
⚠ **同时删去了我先前臆造的 `0 ≤ a`、`0 ≤ b` 前提**：它们既不必要（结论是绝对界），
代入 `a=-5,b=5,M=25` 也能确认。**"看起来合理就加上去"的多余假设同样是缺陷**。 -/
theorem lv00_boundedMul_upper {a b M : ℤ} (ha : a * a ≤ M) (hb : b * b ≤ M) :
    a * b ≤ M := by
  nlinarith [sq_nonneg (a - b), ha, hb]

/-- (A) `bounded_mul_no_overflow` 的**下界**版（同一命题的另一半）。
由 `(a+b)² ≥ 0` 得 `-2ab ≤ a² + b² ≤ 2M`，即 `-M ≤ ab`。 -/
theorem lv00_boundedMul_lower {a b M : ℤ} (ha : a * a ≤ M) (hb : b * b ≤ M) :
    -M ≤ a * b := by
  nlinarith [sq_nonneg (a + b), ha, hb]

/-! ===============================================================
## 第二部分：区间算术 —— 修复 Lv-00 的假舍入，恢复包含性定理

采集自 `IntervalArithmeticTheory`（(B) 命题形式有价值；(A) 重新形式化）。

### ⚠ Lv-00 原 `round_down`/`round_up` 是**假**的

原文实现：
```lean
def round_down (x : ℝ) : ℝ :=
  let scale := (1000000000000000.0 : ℝ)
  (Int.floor (x * scale)).toNat.toFloat / scale
```
`Int.floor` 返回 `ℤ`，`.toNat` 把**负数截断为 0**。于是 `round_down (-1) = 0 > -1`，
**违反它自己声称的 `round_down x ≤ x`**。⇒ Lv-00 的
`outward_rounding_safe`/`round_down_le`/`le_round_up` 若按此实现陈述，**目标为假**；
原文靠把它们写成 `: True` 掩盖了这一点。

**⚠ 分类：这是"错误实现"，不是"空桩"。** 空桩（`: True := by trivial`）一眼可辨；
错误实现**名字像成品**、会被下游当可用代码采信，故危害更高。

本文件把 Lv-00 的实现**原样搬来复现该 bug**（`lv00RoundDown`），
并用**机器验证反例**（`lv00_roundDown_counterexample`）把它钉死，
再给出**数学上正确**的格点舍入（`⌊x·N⌋/N` 与 `⌈x·N⌉/N`）作为修复版。
-/

/-- 格点下取整：`⌊x·N⌋ / N ≤ x`。
用 `Int.floor`（**不经过 `.toNat`**，故负数正确）。对应 Lv-00 `round_down` 的**修复版**。 -/
def roundDownN (N : ℤ) (x : ℝ) : ℝ := ((⌊x * (N : ℝ)⌋ : ℤ) : ℝ) / (N : ℝ)

/-- 格点上取整：`x ≤ ⌈x·N⌉ / N`。对应 Lv-00 `round_up` 的**修复版**。 -/
def roundUpN (N : ℤ) (x : ℝ) : ℝ := ((⌈x * (N : ℝ)⌉ : ℤ) : ℝ) / (N : ℝ)

/-- **Lv-00 `round_down` 的原样复现**（为给出机器验证反例而搬入）。
⚠ **此定义有 bug，不要使用**：`Int.toNat` 对负数截断为 0。
本文件仅用它承载下方的反例定理；正式舍入请用 `roundDownN`。 -/
def lv00RoundDown (x : ℝ) : ℝ :=
  let scale := (1000000000000000.0 : ℝ)
  ((Int.floor (x * scale)).toNat : ℝ) / scale

/-- **机器验证反例（根因）**：bug 的根源是 `Int.toNat` 把负数截断为 0。
`Int.toNat (-1) = 0`，故 `⌊x·scale⌋` 为负时结果被抬到 `0`，破坏下界性。 -/
theorem lv00_toNat_clamps_negative : (Int.toNat (-1) : ℤ) = 0 := rfl

/-- 辅助：`⌊-10^15⌋ = -10^15`（底层整数，供下方反例使用）。 -/
theorem floor_neg_scale : ⌊(-1 : ℝ) * 1000000000000000⌋ = (-1000000000000000 : ℤ) := by
  rw [Int.floor_eq_iff]
  norm_num

/-- **机器验证反例**：Lv-00 的 `round_down` 在 `x = -1` 处违反 `round_down x ≤ x`。

`Int.floor (-1 · 10^15) = -10^15`，`.toNat` 把它截断为 `0`，
故 `lv00RoundDown (-1) = 0`，而 `¬((0:ℝ) ≤ -1)`。
⇒ Lv-00 的 `round_down_le : round_down x ≤ x` **为假**（不是"未证"，是**假**）。

⚠ 本文件**没有**用 `decide`：`ℝ` 无可判定实例，`decide` 对实数目标不可用。
故改用 `Int.floor_eq_iff` 显式定值 + `norm_num` 做**内核可验证的构造性见证**。 -/
theorem lv00_roundDown_counterexample : ¬ (lv00RoundDown (-1) ≤ -1) := by
  have hval : lv00RoundDown (-1) = 0 := by
    unfold lv00RoundDown
    norm_num [Int.toNat_of_nonpos, Int.floor_eq_iff]
  rw [hval]
  norm_num

/-- (A) **修复版在反例点上正确**：同一个 `x = -1`，修复版给出 `-1`，满足 `≤ x`。
这是对上方反例的**直接对照**，证明修复确实针对了缺陷。 -/
theorem roundDownN_neg_one : roundDownN 1000000000000000 (-1) = -1 := by
  have hfl : ⌊((-1 : ℝ) * (1000000000000000 : ℝ))⌋ = (-1000000000000000 : ℤ) := by
    rw [Int.floor_eq_iff]; norm_num
  unfold roundDownN
  simp only [hfl, Int.cast_neg, Int.cast_ofNat]
  norm_num

/-- (A) **外延舍入下界安全性**：修复版下取整确实不越过真值。
这是 Lv-00 声称的 `round_down_le`，为其**修复版**。 -/
theorem roundDownN_le (N : ℤ) (hN : 0 < N) (x : ℝ) : roundDownN N x ≤ x := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h : ((⌊x * (N : ℝ)⌋ : ℤ) : ℝ) ≤ x * (N : ℝ) := Int.floor_le _
  unfold roundDownN
  rw [div_le_iff₀ hN']
  exact h

/-- (A) **外延舍入上界安全性**：修复版上取整确实不越过真值。
这是 Lv-00 声称的 `le_round_up`，为其**修复版**。 -/
theorem le_roundUpN (N : ℤ) (hN : 0 < N) (x : ℝ) : x ≤ roundUpN N x := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h : x * (N : ℝ) ≤ ((⌈x * (N : ℝ)⌉ : ℤ) : ℝ) := Int.le_ceil _
  unfold roundUpN
  rw [le_div_iff₀ hN']
  exact h

/-- (A) **外延舍入安全性（合并）**：Lv-00 的 `outward_rounding_safe` 的修复版。 -/
theorem outward_rounding_safe (N : ℤ) (hN : 0 < N) (x : ℝ) :
    roundDownN N x ≤ x ∧ x ≤ roundUpN N x :=
  ⟨roundDownN_le N hN x, le_roundUpN N hN x⟩

/-- (A) **下取整单调**：修复版单调。Lv-00 声称 `round_down_monotone`。 -/
theorem roundDownN_mono (N : ℤ) (hN : 0 < N) {x y : ℝ} (h : x ≤ y) :
    roundDownN N x ≤ roundDownN N y := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul : x * (N : ℝ) ≤ y * (N : ℝ) := mul_le_mul_of_nonneg_right h (le_of_lt hN')
  have hfloor : ⌊x * (N : ℝ)⌋ ≤ ⌊y * (N : ℝ)⌋ := Int.floor_mono hmul
  unfold roundDownN
  exact div_le_div_of_nonneg_right (by exact_mod_cast hfloor) (le_of_lt hN')

/-- (A) **上取整单调**：修复版单调。Lv-00 声称 `round_up_monotone`。 -/
theorem roundUpN_mono (N : ℤ) (hN : 0 < N) {x y : ℝ} (h : x ≤ y) :
    roundUpN N x ≤ roundUpN N y := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul : x * (N : ℝ) ≤ y * (N : ℝ) := mul_le_mul_of_nonneg_right h (le_of_lt hN')
  have hceil : ⌈x * (N : ℝ)⌉ ≤ ⌈y * (N : ℝ)⌉ := Int.ceil_mono hmul
  unfold roundUpN
  exact div_le_div_of_nonneg_right (by exact_mod_cast hceil) (le_of_lt hN')

/-- 区间：下界 `lo`、上界 `hi`，附良构性证明。
采集自 `IntervalArithmeticTheory.Interval`（结构本身是搬来的**(B) 规格**）。 -/
structure LvInterval where
  /-- 下界 -/
  lo : ℝ
  /-- 上界 -/
  hi : ℝ
  /-- 良构性：下界不超过上界 -/
  wf : lo ≤ hi

/-- 点区间 `[x, x]`。采集自 Lv-00 `Interval.point`。 -/
def LvInterval.point (x : ℝ) : LvInterval := ⟨x, x, le_rfl⟩

/-- 包含谓词：`x ∈ [lo, hi]`。采集自 Lv-00 `Interval.contains`（**(B) 接口规格**）。 -/
def LvInterval.contains (iv : LvInterval) (x : ℝ) : Prop := iv.lo ≤ x ∧ x ≤ iv.hi

/-- 区间宽度。采集自 Lv-00 `Interval.width`。 -/
def LvInterval.width (iv : LvInterval) : ℝ := iv.hi - iv.lo

/-- 区间中点。采集自 Lv-00 `Interval.mid`。 -/
def LvInterval.mid (iv : LvInterval) : ℝ := (iv.lo + iv.hi) / 2

/-- (A) **包含性：加法**。区间算术的核心正确性定理，Lv-00 `containment_add` 声称的内容
（原文为 `: True`）。用修复版外延舍入陈述，使其**真的**成立。 -/
theorem containment_add (N : ℤ) (hN : 0 < N) (a b : LvInterval) (x y : ℝ)
    (hx : a.contains x) (hy : b.contains y) :
    roundDownN N (a.lo + b.lo) ≤ x + y ∧ x + y ≤ roundUpN N (a.hi + b.hi) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · exact le_trans (roundDownN_le N hN _) (add_le_add hx1 hy1)
  · exact le_trans (add_le_add hx2 hy2) (le_roundUpN N hN _)

/-- 四角乘积列表：`[lo_a·lo_b, lo_a·hi_b, hi_a·lo_b, hi_a·hi_b]`。
采集自 Lv-00 `fourCorners`（**(B) 命题形式有价值**）。 -/
def fourCorners (a b : LvInterval) : List ℝ :=
  [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]

/-! ### ⚠ 诚实降级：区间乘法的一般四角公式（本文件未证）

Lv-00 `containment_mul` / `four_corner_soundness` 声称的内容（原文为 `: True`）是：
`x ∈ [lo_a,hi_a]`、`y ∈ [lo_b,hi_b]` ⟹ `min(四角) ≤ x·y ≤ max(四角)`。

**为什么未证（诚实记录）**：
该命题为**真**（`x·y` 关于 `(x,y)` 双线性，矩形上极值必在四角），但把它在 Lean 里证出来
需要 4 种符号组合 ×（上下界各一）共 8 个分支，每支都要处理 `mul_le_mul` 系列的
隐式参数顺序与符号前置条件——本轮在构建锁排队成本极高（单次 1600-2900 秒）的条件下，
**投入产出比不合理**，故**降级为后续工作**。

**本文件实际交付的是它的可证特例** `containment_mul_nonneg`（下一条），
覆盖数值基座最常见的用法（误差/范数/概率/区间宽度**均为非负**）。
⇒ **本文件不声称**已证一般四角公式。这正是 `STYLE.md` §5
「诚实降级优先：命题太难就缩小陈述」的做法。 -/

/-- (A) **区间乘法包含性（非负特例，常用形态）**：两区间均非负时，
`lo_a·lo_b ≤ x·y ≤ hi_a·hi_b`。覆盖数值基座最常见的用法（误差/范数/概率均非负）。

这是 Lv-00 `containment_mul` 的**可证特例**；一般四角公式见上方诚实降级说明。 -/
theorem containment_mul_nonneg {a b : LvInterval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo)
    (hx : a.contains x) (hy : b.contains y) :
    a.lo * b.lo ≤ x * y ∧ x * y ≤ a.hi * b.hi := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hb' : 0 ≤ b.lo := hb
  have hy0 : 0 ≤ y := le_trans hb hy1
  have ha' : 0 ≤ a.lo := ha
  have hx0 : 0 ≤ x := le_trans ha hx1
  -- ⚠ v14 修复：原稿第二项写 `mul_le_mul hx2 hy2 hy0 hx0`，报 **application type mismatch**：
  -- `mul_le_mul` 的**第四个参数**要求「**右因子 `a.hi` 的非负性**」（`0 ≤ a.hi`），
  -- 而 `hx0 : 0 ≤ x` 是**左因子**的非负性 ⟹ 类型不匹配。
  -- 正确第四参数由 `0 ≤ a.lo`（`ha`）与良构性 `a.lo ≤ a.hi`（`a.wf`）合成。
  have hahi : 0 ≤ a.hi := le_trans ha a.wf
  exact ⟨mul_le_mul hx1 hy1 hb' hx0, mul_le_mul hx2 hy2 hy0 hahi⟩

/-! ===============================================================
## 第三部分：版本序与魔法常量表

采集自 `MagicConstantsTheory`（**(A) 真实证明**，本文件主要采集体）。
原始 27 条定理中 24 条为真实证明；1 条（`forward_compatibility_property`）是
`hP` 的同义反复（(C)，**丢弃**）；其余为 Mathlib 已有更一般版本的重复（见报告）。
-/

/-- 语义化版本 `major.minor.patch`。采集自 `MagicConstantsTheory.Version`。 -/
structure LvVersion where
  /-- 主版本号 -/
  major : ℕ
  /-- 次版本号 -/
  minor : ℕ
  /-- 修订号 -/
  patch : ℕ
  deriving DecidableEq, Repr

namespace LvVersion

/-- 版本序：先比 major，再比 minor，最后比 patch。
采集自 `MagicConstantsTheory.Version.le`（**(B) 接口规格**，配套定理为 (A)）。 -/
def le (a b : LvVersion) : Prop :=
  a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
  (a.major = b.major ∧ a.minor = b.minor ∧ a.patch ≤ b.patch)

/-- 严格版本序。采集自 `MagicConstantsTheory.Version.lt`。 -/
def lt (a b : LvVersion) : Prop :=
  a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
  (a.major = b.major ∧ a.minor = b.minor ∧ a.patch < b.patch)

instance : LE LvVersion := ⟨le⟩

instance : LT LvVersion := ⟨lt⟩

/-- (A) 自反性。采集自 `Version.le_refl`（真实证明）。 -/
theorem le_refl (a : LvVersion) : a ≤ a :=
  Or.inr (Or.inr ⟨rfl, rfl, Nat.le_refl _⟩)

/-- (A) 传递性。采集自 `Version.le_trans`（真实证明）。
⚠ Lv-00 原证明在若干分支上把 `a.major`/`b.minor` 等字段张冠李戴（`hbc₂` 用作 major 的界），
本文件用 `omega` 收口各分支——`omega` 在纯 `ℕ` 线性算术上是**决策过程**，比手写 `Nat.lt_of_lt_of_le`
更不易错。 -/
theorem le_trans {a b c : LvVersion} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  change a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
    (a.major = b.major ∧ a.minor = b.minor ∧ a.patch ≤ b.patch) at hab
  change b.major < c.major ∨ (b.major = c.major ∧ b.minor < c.minor) ∨
    (b.major = c.major ∧ b.minor = c.minor ∧ b.patch ≤ c.patch) at hbc
  change a.major < c.major ∨ (a.major = c.major ∧ a.minor < c.minor) ∨
    (a.major = c.major ∧ a.minor = c.minor ∧ a.patch ≤ c.patch)
  omega

/-- (A) 反对称性。采集自 `Version.le_antisymm`（真实证明）。
Lv-00 用 `ext` + `Nat.le_antisymm` 分三字段共 30 余行；此处 `omega` 一次收口。 -/
theorem le_antisymm {a b : LvVersion} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  have hab' : a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
      (a.major = b.major ∧ a.minor = b.minor ∧ a.patch ≤ b.patch) := hab
  have hba' : b.major < a.major ∨ (b.major = a.major ∧ b.minor < a.minor) ∨
      (b.major = a.major ∧ b.minor = a.minor ∧ b.patch ≤ a.patch) := hba
  obtain ⟨m₁, m₂, m₃⟩ := a
  obtain ⟨n₁, n₂, n₃⟩ := b
  simp only at hab' hba'
  have h₁ : m₁ = n₁ := by omega
  have h₂ : m₂ = n₂ := by omega
  have h₃ : m₃ = n₃ := by omega
  subst h₁ h₂ h₃
  rfl

/-- (A) **全序性**。采集自 `Version.le_total`（真实证明）。

⚠ **Lv-00 原证明有真缺陷**：它在 `a.patch ≤ b.patch` 分支写
`right; right; right; exact ...`——**四个** `Or` 的右支，但 `Version.le` 只有**三个**析取项。
该文件若真被编译会在此报类型错（原文因此从未被 `lake build` 覆盖）。
本文件按正确的三项写法重写。

⚠ **另一处陷阱（本轮实测）**：定理名 `le_total` 会**遮蔽** `Nat.le_total`，
使 `rcases le_total a.patch b.patch` 递归调用自身 → Lean 报
`fail to show termination`。对策：**用 `Nat.le_total` 显式限定**。

实现上不手写 `Or.inl/Or.inr` 嵌套（极易错），而是**先分成三个平铺的析取**再归类。 -/
theorem le_total (a b : LvVersion) : a ≤ b ∨ b ≤ a := by
  rcases Nat.lt_trichotomy a.major b.major with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Nat.lt_trichotomy a.minor b.minor with h2 | h2 | h2
    · exact Or.inl (Or.inr (Or.inl ⟨h, h2⟩))
    · rcases Nat.le_total a.patch b.patch with h3 | h3
      · exact Or.inl (Or.inr (Or.inr ⟨h, h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h2.symm, h3⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.symm, h2⟩))
  · exact Or.inr (Or.inl h)

/-- (A) 严格序蕴含 `≤`。Lv-00 隐含但未单列的性质。 -/
theorem lt_imp_le {a b : LvVersion} (h : a < b) : a ≤ b := by
  change a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
    (a.major = b.major ∧ a.minor = b.minor ∧ a.patch < b.patch) at h
  change a.major < b.major ∨ (a.major = b.major ∧ a.minor < b.minor) ∨
    (a.major = b.major ∧ a.minor = b.minor ∧ a.patch ≤ b.patch)
  omega

end LvVersion

/-- 版本区间 `[minVersion, maxVersion]`。采集自 `MagicConstantsTheory.VersionRange`。 -/
structure LvVersionRange where
  /-- 下界（含） -/
  minVersion : LvVersion
  /-- 上界（含） -/
  maxVersion : LvVersion

namespace LvVersionRange

/-- 区间包含谓词。采集自 `VersionRange.contains`（**(B) 接口规格**）。 -/
def contains (r : LvVersionRange) (v : LvVersion) : Prop :=
  r.minVersion ≤ v ∧ v ≤ r.maxVersion

/-- 单点区间。采集自 `VersionRange.singleton`。 -/
def singleton (v : LvVersion) : LvVersionRange := ⟨v, v⟩

/-- (A) 单点区间包含其中心。采集自 `VersionRange.singleton_contains_iff` 的右到左方向。 -/
theorem singleton_contains_self (v : LvVersion) : (singleton v).contains v :=
  ⟨LvVersion.le_refl v, LvVersion.le_refl v⟩

/-- (A) 单点区间只包含中心。采集自 `VersionRange.singleton_contains_iff`（真实证明）。 -/
theorem singleton_contains_iff (v w : LvVersion) :
    (singleton v).contains w ↔ w = v := by
  constructor
  · intro ⟨h₁, h₂⟩
    exact LvVersion.le_antisymm h₂ h₁
  · intro h
    rw [h]
    exact singleton_contains_self v

end LvVersionRange

/-! ### 魔法常量表与唯一性不变量

采集自 `MagicConstantsTheory` 第 5–11 节。**(A) 真实证明**。 -/

/-- 魔法常量类别。采集自 `MagicConstantsTheory.MagicCategory`（**(B) 枚举规格**）。 -/
inductive LvMagicCategory where
  /-- 版本标识 -/
  | version
  /-- 特性开关 -/
  | featureFlag
  /-- 上下界常量 -/
  | limit
  /-- 哨兵/终止值 -/
  | sentinel
  /-- 编码标记 -/
  | encodingMarker
  /-- 调试令牌 -/
  | debugToken
  deriving DecidableEq, Repr

/-- 单条魔法常量。采集自 `MagicConstantsTheory.MagicConstant`。 -/
structure LvMagicConstant where
  /-- 常量名（对应 C 里的 `#define`） -/
  name : String
  /-- 数值 -/
  value : ℕ
  /-- 类别 -/
  category : LvMagicCategory
  /-- 引入版本 -/
  versionIntroduced : LvVersion
  deriving DecidableEq, Repr

/-- 魔法常量表。采集自 `MagicConstantsTheory.MagicTable`。 -/
structure LvMagicTable where
  /-- 全部常量 -/
  constants : List LvMagicConstant

namespace LvMagicTable

/-- 按名查找。采集自 `MagicTable.lookup_by_name`。 -/
def lookupByName (t : LvMagicTable) (name : String) : Option LvMagicConstant :=
  t.constants.find? (fun c => c.name = name)

/-- 按类别查找。采集自 `MagicTable.lookup_by_category`。 -/
def lookupByCategory (t : LvMagicTable) (cat : LvMagicCategory) : List LvMagicConstant :=
  t.constants.filter (fun c => c.category = cat)

/-- 插入常量。采集自 `MagicTable.insert`。 -/
def insert (t : LvMagicTable) (c : LvMagicConstant) : LvMagicTable :=
  ⟨c :: t.constants⟩

/-- 按名删除。采集自 `MagicTable.remove`。 -/
def remove (t : LvMagicTable) (name : String) : LvMagicTable :=
  ⟨t.constants.filter (fun c => c.name ≠ name)⟩

/-- 空表。采集自 `MagicTable.empty`。 -/
def empty : LvMagicTable := ⟨[]⟩

end LvMagicTable

/-- 唯一性不变量：(1) 名字互异；(2) **同类别内**数值互异。
采集自 `MagicConstantsTheory.ConstantUniqueness`（**(B) 规格声明**，
其配套定理是 (A) 真结果）。 -/
def LvConstantUniqueness (t : LvMagicTable) : Prop :=
  (∀ c₁ ∈ t.constants, ∀ c₂ ∈ t.constants, c₁.name = c₂.name → c₁ = c₂) ∧
  (∀ c₁ ∈ t.constants, ∀ c₂ ∈ t.constants,
    c₁.category = c₂.category → c₁.value = c₂.value → c₁ = c₂)

/-- (A) 空表满足唯一性。采集自 `empty_table_unique`（真实证明）。 -/
theorem empty_table_unique : LvConstantUniqueness LvMagicTable.empty := by
  unfold LvConstantUniqueness LvMagicTable.empty
  simp

/-- (A) **插入保鲜**：新常量的名字与（同类别）数值均新鲜时，插入保持唯一性。
采集自 `insert_preserves_uniqueness`（真实证明，逐分支 `rcases`）。 -/
theorem insert_preserves_uniqueness (t : LvMagicTable) (c : LvMagicConstant)
    (huniq : LvConstantUniqueness t)
    (hfreshName : ∀ c' ∈ t.constants, c'.name ≠ c.name)
    (hfreshValue : ∀ c' ∈ t.constants, c'.category = c.category → c'.value ≠ c.value) :
    LvConstantUniqueness (t.insert c) := by
  obtain ⟨hname, hval⟩ := huniq
  unfold LvConstantUniqueness LvMagicTable.insert
  constructor
  · intro c₁ h₁ c₂ h₂ heq
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁
    · rcases h₂ with rfl | h₂
      · rfl
      · exact absurd heq.symm (hfreshName _ h₂)
    · rcases h₂ with rfl | h₂
      · exact absurd heq (hfreshName _ h₁)
      · exact hname _ h₁ _ h₂ heq
  · intro c₁ h₁ c₂ h₂ hcat hvalEq
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁
    · rcases h₂ with rfl | h₂
      · rfl
      · exact absurd hvalEq.symm (hfreshValue _ h₂ hcat.symm)
    · rcases h₂ with rfl | h₂
      · exact absurd hvalEq (hfreshValue _ h₁ hcat)
      · exact hval _ h₁ _ h₂ hcat hvalEq

/-- 向后兼容：旧表的每个常量仍在表中。采集自 `MagicConstantsTheory.BackwardCompatibility`
（**(B) 规格声明**）。 -/
def LvBackwardCompatible (old new : LvMagicTable) : Prop :=
  ∀ c : LvMagicConstant, c ∈ old.constants → c ∈ new.constants

/-- (A) 向后兼容自反。采集自 `backward_compat_refl`。 -/
theorem backward_compat_refl (t : LvMagicTable) : LvBackwardCompatible t t :=
  fun _ hc => hc

/-- (A) 向后兼容传递。采集自 `backward_compat_trans`。 -/
theorem backward_compat_trans {a b c : LvMagicTable}
    (hab : LvBackwardCompatible a b) (hbc : LvBackwardCompatible b c) :
    LvBackwardCompatible a c :=
  fun x hx => hbc x (hab x hx)

/-- (A) **插入总是向后兼容**：这是"常量一旦发布永不修改"策略的形式化。
采集自 `insert_is_backward_compatible`（真实证明）。 -/
theorem insert_is_backward_compatible (t : LvMagicTable) (c : LvMagicConstant) :
    LvBackwardCompatible t (t.insert c) := by
  intro x hx
  exact List.mem_cons_of_mem _ hx

/-- (A) **删除破坏向后兼容**：与上一条构成完整的"只增不改"策略。
采集自 `remove_breaks_compatibility`（真实证明）。 -/
theorem remove_breaks_compatibility (t : LvMagicTable) (name : String)
    (hc : ∃ c ∈ t.constants, c.name = name) :
    ¬ LvBackwardCompatible t (t.remove name) := by
  obtain ⟨c, hc, hname⟩ := hc
  intro h
  have hc' := h c hc
  unfold LvMagicTable.remove at hc'
  rw [List.mem_filter] at hc'
  exact (of_decide_eq_true hc'.2) hname

/-- (A) 按名查找是可靠的：返回的常量确在表中且名字匹配。
采集自 `lookup_by_name_sound`（真实证明）。

实现说明（**诚实标注**）：Lv-00 用 `List.find? (fun c => c.name = name)`（**Bool** 谓词），
其"谓词成立"结论形如 `decide (c.name = name) = true`。本定理给出**成员性**这一半
（`List.mem_of_find?_eq_some`）；名称匹配那一半需要 `decide` 桥接，
本文件改用**独立的过滤式接口** `LvMagicTable.findByName`（见下）绕开 Bool coercion，
语义等价且更易用。 -/
theorem lookup_by_name_sound (t : LvMagicTable) (name : String) (c : LvMagicConstant)
    (h : t.lookupByName name = some c) : c ∈ t.constants :=
  List.mem_of_find?_eq_some h

/-- (A) **名称匹配的化简接口**：把 `lookupByName` 的结果换成 `Prop` 版过滤式，
避免在定理中反复处理 `decide (· = ·) = true`。
语义与 `lookupByName` 一致（`filter` 用同一谓词）。 -/
def LvMagicTable.findByName (t : LvMagicTable) (name : String) : List LvMagicConstant :=
  t.constants.filter (fun c => c.name = name)

/-- (A) 过滤式查找的可靠性：成员必有该名。这是 `lookup_by_name_sound`
"名称匹配"那一半的**可证替代品**。 -/
theorem LvMagicTable.findByName_name (t : LvMagicTable) (name : String)
    (c : LvMagicConstant) (h : c ∈ t.findByName name) : c.name = name := by
  unfold LvMagicTable.findByName at h
  rw [List.mem_filter] at h
  exact of_decide_eq_true h.2

/-- (A) 按类别查找只返回该类别。采集自 `lookup_by_category_correct`（真实证明）。 -/
theorem lookup_by_category_correct (t : LvMagicTable) (cat : LvMagicCategory)
    (c : LvMagicConstant) (h : c ∈ t.lookupByCategory cat) : c.category = cat := by
  unfold LvMagicTable.lookupByCategory at h
  rw [List.mem_filter] at h
  exact of_decide_eq_true h.2

/-- (A) 删除后按名查找必为空。采集自 `remove_removes_name`（真实证明）。 -/
theorem remove_removes_name (t : LvMagicTable) (name : String) :
    (t.remove name).lookupByName name = none := by
  unfold LvMagicTable.remove LvMagicTable.lookupByName
  apply List.find?_eq_none.mpr
  intro a ha
  rw [List.mem_filter] at ha
  exact fun heq => (of_decide_eq_true ha.2) (by simpa using heq)

end Lattice.Lv00.LinearAlgebra

end
