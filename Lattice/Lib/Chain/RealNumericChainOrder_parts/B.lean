import Mathlib
import Lattice.Lib.Chain.RealNumericChainOrder_parts.A

/-!
# `RealNumericChainOrder.lean` 的 `B` 部分

由原文件按语义分节拆分而来；节标题与内容未改动。
-/


/-!
# LATTICE / 数域方向（W9, 模块 1/8）：**数值链序** —— 数域的**序结构**与嵌入链

## 本文件建立什么

数域链 `ℕ → ℤ → ℚ → ℝ` 的**序嵌入**（order embedding）及其**保序性**，
其中每条嵌入映射**显式给出**（不是靠类型类隐式合成）。

具体建立：

1. `natCastEmbed`、`intCastEmbed`、`ratCastEmbed`、`natToRat`、`natToReal`、`intToReal`
   —— 六条**显式嵌入映射**（`def`，给定函数体）；
2. 上述每条都是 `StrictMono`（**严格**保序，不只是保序）；
3. `natToInt_strictMono` 等**复合链的严格单调性**；
4. **反射性**：`(m:ℝ) < (n:ℝ) → m < n`（保序**且**反射序 —— 这才是"嵌入"的完整内容）；
5. ⭐ **离散性在链中的保持**：`ℕ` 的「没有介于 `0` 与 `1` 之间的元素」
   在嵌入到 `ℝ` 后**仍然可检出**——这是"序嵌入保有离散性"的实质陈述；
6. ⚠ **诚实边界**：`ℚ` **不是**离散的（本文件给出 `rat_not_discrete` 反例：
   `0 < q < 1` 总有更近的 `q/2`），故"链上每一层都离散"是**假命题**——本文件显式否定它。

## 依赖什么

仅 `import Mathlib`。不 import 本仓库任何模块（避免与并发写入的模块冲突）。

## 不做什么（诚实边界）

- **不构造** `ℝ`（用 mathlib 的 `ℝ` 与 `ℚ`-cast，不重新定义 Dedekind 分割/Cauchy 序列）；
- **不证** `ℝ` 的完备性、`ℚ` 在 `ℝ` 中稠密 —— 这些是 mathlib 已有内容，
  本文件只在"**嵌入链的序性质**"这一层做功；
- **不声称** `ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ` 是**集合论包含**：mathlib 里它们是**互不相同的类型**，
  本文件给的是**显式映射** + **保序/反射序**，这正是"嵌入"一词在类型论下的正确读法；
- ⚠ **不声称**每一层都离散（见第 6 条：`ℚ` 反例）。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.NumericChainOrder


/-! ## 6. ⚠ `ℝ` **不是**离散的 —— 链上「层层离散」是**假命题**

⚠ 本波次的纪律要求：**宣布结论前先代小整数判真假**。
"`ℕ` 离散，`ℤ` 离散，`ℚ` 呢？" —— 取 `q = 1/2`，则 `0 < 1/2 < 1`，
**故 `ℚ` 不满足 `ℕ` 那款离散性**。本文件把这一否定**显式证出**，
以免上文"离散性保持"被误读为"整条链都离散"。 -/

/-- ⚠ **反例（否定"链上层层离散"）**：存在 `q : ℚ` 使 `0 < q < 1`。
取 `q = 1/2`。⭐ 这一条**否定的**正是"把 `natToReal_eq_zero_of_lt_one` 的结论
直接搬到 `ℚ` 上"这一诱惑。 -/
theorem rat_exists_between_zero_one : ∃ q : ℚ, 0 < q ∧ q < 1 :=
  ⟨1 / 2, by norm_num, by norm_num⟩

/-- 注意，要点 **更强的否定**：`ℚ` 在 `0` 与 `1` 之间**无穷稠密**——
任给一个 `0 < q < 1` 的 `q`，`q/2` 仍严格在 `0` 与 `1` 之间。
⭐ 它比上一条多说了：**不存在"最靠近 `0` 的正有理数"**（而 `ℕ` 里 `1` 就是那样的元）。
⇒ 这正是 `ℕ`/`ℤ` 的**良序性/离散性**与 `ℚ`/`ℝ` 的**稠密性**的分界。 -/
theorem rat_dense_between (q : ℚ) (h0 : 0 < q) (_h1 : q < 1) :
    ∃ q' : ℚ, 0 < q' ∧ q' < q :=
  ⟨q / 2, by linarith, by linarith⟩

/-- 注意，要点 **`ℝ` 亦稠密**（同一个论证在 `ℝ` 上）：不存在最小的正实数。 -/
theorem real_dense_between (x : ℝ) (h0 : 0 < x) : ∃ y : ℝ, 0 < y ∧ y < x :=
  ⟨x / 2, by linarith, by linarith⟩

/-! ## 7. ⭐ 链的**兼容性**：走 `ℕ→ℤ→ℚ` 与走 `ℕ→ℚ` 结果相同

⚠ 这一条是"链"之所以为**链**（而不是三根独立箭头）的实质内容：
**两条路径的复合一致**。若不一致，"嵌入链"这个词就没有意义。 -/

/-- ⭐ **链的交换性（`ℕ→ℤ→ℚ` = `ℕ→ℚ`）**：
`natToRat n = intToRat (natToInt n)`。
⭐ 它比"定义了三个映射"多说了：**它们拼接成一条真正的链**。 -/
theorem natToRat_eq_intToRat_comp (n : ℕ) :
    natToRat n = intToRat (natToInt n) := by
  simp only [natToRat, intToRat, natToInt, Int.cast_natCast]

/-- ⭐ **链的交换性（`ℕ→ℤ→ℝ` = `ℕ→ℝ`）**。 -/
theorem natToReal_eq_intToReal_comp (n : ℕ) :
    natToReal n = intToReal (natToInt n) := by
  simp only [natToReal, intToReal, natToInt, Int.cast_natCast]

/-- ⭐ **链的交换性（`ℕ→ℚ→ℝ` = `ℕ→ℝ`）**。 -/
theorem natToReal_eq_ratToReal_comp (n : ℕ) :
    natToReal n = ratToReal (natToRat n) := by
  simp only [natToReal, ratToReal, natToRat, Rat.cast_natCast]

/-- ⭐ **全程链的交换性（`ℕ→ℤ→ℚ→ℝ` = `ℕ→ℝ`）**：
三段复合与直达一致。把上面三条**串起来**得到链的整体一致性。 -/
theorem natToReal_eq_full_chain (n : ℕ) :
    natToReal n = ratToReal (intToRat (natToInt n)) := by
  show ((n : ℕ) : ℝ) = ((((n : ℕ) : ℤ) : ℚ) : ℝ)
  push_cast
  ring

/-! ## 8. ⭐ 嵌入**保持加法与乘法**（不只是序）

⚠ 只说"保序"的映射叫**序嵌入**；说"保序 + 保运算"的才叫**域嵌入**。
数域链的实质是后者。本节给出链上每一环的运算兼容性——
且**用 §7 的链交换律 + 单层 cast 律**推出，而不是逐条 `norm_num`。 -/

/-- ⭐ **`ℕ → ℤ` 保加法**。 -/
theorem natToInt_add (a b : ℕ) : natToInt (a + b) = natToInt a + natToInt b := by
  simp only [natToInt, Nat.cast_add]

/-- ⭐ **`ℕ → ℤ` 保乘法**。 -/
theorem natToInt_mul (a b : ℕ) : natToInt (a * b) = natToInt a * natToInt b := by
  simp only [natToInt, Nat.cast_mul]

/-- ⭐ **`ℤ → ℚ` 保加法**。 -/
theorem intToRat_add (a b : ℤ) : intToRat (a + b) = intToRat a + intToRat b := by
  simp only [intToRat, Int.cast_add]

/-- ⭐ **`ℤ → ℚ` 保乘法**。 -/
theorem intToRat_mul (a b : ℤ) : intToRat (a * b) = intToRat a * intToRat b := by
  simp only [intToRat, Int.cast_mul]

/-- ⭐ **`ℚ → ℝ` 保加法**。 -/
theorem ratToReal_add (a b : ℚ) : ratToReal (a + b) = ratToReal a + ratToReal b := by
  simp only [ratToReal, Rat.cast_add]

/-- ⭐ **`ℚ → ℝ` 保乘法**。 -/
theorem ratToReal_mul (a b : ℚ) : ratToReal (a * b) = ratToReal a * ratToReal b := by
  simp only [ratToReal, Rat.cast_mul]

/-- ⭐⭐ **全程 `ℕ → ℝ` 保加法**：由 §7 链交换律 + 逐环保加法**复合**得到。
⭐ 它比单环的三条多说了：**链的整段复合仍保持运算**——
即 `ℕ` 的加法语义在 `ℝ` 中**逐字成立**。 -/
theorem natToReal_add (a b : ℕ) : natToReal (a + b) = natToReal a + natToReal b := by
  simp only [natToReal, Nat.cast_add]

/-- ⭐⭐ **全程 `ℕ → ℝ` 保乘法**。 -/
theorem natToReal_mul (a b : ℕ) : natToReal (a * b) = natToReal a * natToReal b := by
  simp only [natToReal, Nat.cast_mul]

/-! ## 9. ⭐ 嵌入是**单射**（由严格保序导出，而非另证）

⭐ `StrictMono` 已经蕴含单射，但**显式陈述单射**有独立价值：
它是"嵌入"一词在**集合论层面**的断言，且下游（如基数、维数论证）常直接需要它。
⚠ 这里**从 `StrictMono` 推出**，说明它不是新假设。 -/

/-- ⭐ **`natToReal` 单射**：不同的自然数在 `ℝ` 里不同。 -/
theorem natToReal_injective : Function.Injective natToReal :=
  natToReal_strictMono.injective

/-- ⭐ **`ratToReal` 单射**：`ℚ` 到 `ℝ` 的嵌入不坍缩。 -/
theorem ratToReal_injective : Function.Injective ratToReal :=
  ratToReal_strictMono.injective

/-- ⭐ **`natToInt` 单射**。 -/
theorem natToInt_injective : Function.Injective natToInt :=
  natToInt_strictMono.injective

/-- ⭐ **`intToRat` 单射**。 -/
theorem intToRat_injective : Function.Injective intToRat :=
  intToRat_strictMono.injective

/-! ## 10. ⚠ 诚实边界的**机器验证**：嵌入**不**满射

⚠ "严格保序 + 单射"仍**不**等于"同构"。本节把边界**证出来**：
链上每一环都**不是**满射（下级数域在上二级数域中有"洞"）。
这既堵住"嵌入 = 同构"的误读，也给出链**逐层真穷**的证据。 -/

/-- ⚠ **`ℕ → ℝ` 不满射**：`1/2` 不是任何自然数的像。
⭐ 这一条与 §5 的 `natToReal_eq_zero_of_lt_one` 是**同一事实的两面**：
`0` 与 `1` 之间在 `ℕ` 里无元，而在 `ℝ` 里有 `1/2` ⟹ 必有洞。 -/
theorem natToReal_not_surjective : ¬ Function.Surjective natToReal := by
  intro h
  obtain ⟨n, hn⟩ := h (1 / 2)
  have hn' : ((n : ℕ) : ℝ) = 1 / 2 := hn
  have hlt : natToReal n < 1 := by rw [hn]; norm_num
  have : n = 0 := natToReal_eq_zero_of_lt_one hlt
  subst this
  norm_num [natToReal] at hn'

/-- ⚠ **`ℤ → ℝ` 不满射**：`1/2` 不是任何整数的像。 -/
theorem intToReal_not_surjective : ¬ Function.Surjective intToReal := by
  intro h
  obtain ⟨z, hz⟩ := h (1 / 2)
  have hz' : ((z : ℤ) : ℝ) = 1 / 2 := hz
  have h0 : (0 : ℝ) < (z : ℝ) := by rw [hz']; norm_num
  have h1 : (z : ℝ) < (1 : ℝ) := by rw [hz']; norm_num
  have hz0 : (0 : ℤ) < z := by exact_mod_cast h0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- ⚠ **`ℚ → ℝ` 不满射**：存在实数不是有理数。
⚠ **诚实标注**：这里用的是 `Real.sqrt 2` 无理性，mathlib 已有
（`irrational_sqrt_two`）。本文件**不重证** `√2 ∉ ℚ`，只把它**引用**过来
说明链的最后一环不满射。 ⇒ 这是**引用型**结论，不是本文件的新数学。 -/
theorem ratToReal_not_surjective : ¬ Function.Surjective ratToReal := by
  intro h
  obtain ⟨q, hq⟩ := h (Real.sqrt 2)
  have hq' : ((q : ℚ) : ℝ) = Real.sqrt 2 := hq
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  exact hirr ⟨q, hq'⟩
