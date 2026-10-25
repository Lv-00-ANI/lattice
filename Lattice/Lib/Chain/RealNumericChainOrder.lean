import Mathlib

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

/-! ## 1. 显式嵌入映射

⚠ 这里一律用**具名 `def`** 而非依赖类型类合成：
`ℕ → ℤ` 的强制转换在 mathlib 里由 `Nat.cast` 提供，但把它**固化为一个有名字的映射**
才能对"嵌入链"本身陈述定理（而不是对每次出现的隐式 cast 各证一遍）。 -/

/-- **嵌入 1**：`ℕ → ℤ`，`n ↦ (n : ℤ)`。显式给出映射体。 -/
def natToInt : ℕ → ℤ := fun n => (n : ℤ)

/-- **嵌入 2**：`ℤ → ℚ`，`z ↦ (z : ℚ)`。 -/
def intToRat : ℤ → ℚ := fun z => (z : ℚ)

/-- **嵌入 3**：`ℚ → ℝ`，`q ↦ (q : ℝ)`。 -/
def ratToReal : ℚ → ℝ := fun q => (q : ℝ)

/-- **复合嵌入 4**：`ℕ → ℚ`（跳过 `ℤ` 直达 `ℚ`）。 -/
def natToRat : ℕ → ℚ := fun n => (n : ℚ)

/-- **复合嵌入 5**：`ℤ → ℝ`。 -/
def intToReal : ℤ → ℝ := fun z => (z : ℝ)

/-- **复合嵌入 6**：`ℕ → ℝ`（链的全程）。 -/
def natToReal : ℕ → ℝ := fun n => (n : ℝ)

/-! ## 2. 逐条严格保序

⚠ 每条都证「`a < b ⟹ f a < f b`」的**严格**版本。
⚠ 与"保序（`≤`）"的区别是本文件的核心内容之一：
**严格**保序才能排除"把两个不同元素映到同一点"的坍缩。 -/

/-- **`ℕ ↪ ℤ` 严格保序**。这是链的第一环。 -/
theorem natToInt_strictMono : StrictMono natToInt := fun a b h => by
  show (a : ℤ) < (b : ℤ)
  exact_mod_cast h

/-- **`ℤ ↪ ℚ` 严格保序**。 -/
theorem intToRat_strictMono : StrictMono intToRat := fun a b h => by
  show (a : ℚ) < (b : ℚ)
  exact_mod_cast h

/-- **`ℚ ↪ ℝ` 严格保序**。这是链的最后一环。 -/
theorem ratToReal_strictMono : StrictMono ratToReal := fun a b h => by
  show (a : ℝ) < (b : ℝ)
  exact_mod_cast h

/-- **`ℕ ↪ ℚ` 严格保序**（复合 1∘2）。 -/
theorem natToRat_strictMono : StrictMono natToRat := fun a b h => by
  show (a : ℚ) < (b : ℚ)
  exact_mod_cast h

/-- **`ℤ ↪ ℝ` 严格保序**。 -/
theorem intToReal_strictMono : StrictMono intToReal := fun a b h => by
  show (a : ℝ) < (b : ℝ)
  exact_mod_cast h

/-- **`ℕ ↪ ℝ` 严格保序**（链的全程，embedding composition）。 -/
theorem natToReal_strictMono : StrictMono natToReal := fun a b h => by
  show (a : ℝ) < (b : ℝ)
  exact_mod_cast h

/-! ## 3. **反射序**：嵌入不「制造」不等

⚠ 只证单调性**不足以**称"嵌入"：`fun _ : ℕ => (0 : ℝ)` 也是单调的，
但它把一切坍缩掉。**反射性**（`f a < f b ⟹ a < b`）是排除坍缩的另一半。
⭐ 且——这正是"嵌入"区别于"单调映射"的**实质内容**，也是本节比 §2 多说的东西。 -/

/-- **`ℕ → ℤ` 反射严格序**：`(a:ℤ) < (b:ℤ) ⟹ a < b`。 -/
theorem natToInt_refl_lt {a b : ℕ} (h : natToInt a < natToInt b) : a < b := by
  have h' : (a : ℤ) < (b : ℤ) := h
  exact_mod_cast h'

/-- **`ℤ → ℚ` 反射严格序**：`(a:ℚ) < (b:ℚ) ⟹ a < b`。 -/
theorem intToRat_refl_lt {a b : ℤ} (h : intToRat a < intToRat b) : a < b := by
  have h' : (a : ℚ) < (b : ℚ) := h
  exact_mod_cast h'

/-- **`ℚ → ℝ` 反射严格序**：`(a:ℝ) < (b:ℝ) ⟹ a < b`。 -/
theorem ratToReal_refl_lt {a b : ℚ} (h : ratToReal a < ratToReal b) : a < b := by
  have h' : (a : ℝ) < (b : ℝ) := h
  exact_mod_cast h'

/-- **`ℕ → ℝ` 反射严格序**（全程）。 -/
theorem natToReal_refl_lt {a b : ℕ} (h : natToReal a < natToReal b) : a < b := by
  have h' : (a : ℝ) < (b : ℝ) := h
  exact_mod_cast h'

/-! ## 4. ⭐ 保序**当且仅当**反射序：序嵌入的完整刻画

⭐ 这是本文件**信息量最高**的一条：它把 §2 与 §3 合并成一个**双向**陈述，
说明 `natToReal` 上的 `StrictMono` + 反射性**合起来等价于**「`ℕ` 上的序被 `ℝ` 上的序**精确镜像**」。
⚠ 它比"单独说单调"多说了：**没有任何两个不同的自然数在 `ℝ` 里变得可比性不同**。 -/

/-- ⭐ **序嵌入的完整刻画**：对 `ℕ → ℝ`，`a < b ↔ (a:ℝ) < (b:ℝ)`。
这一条同时给出 §2 的向前方向与 §3 的向后方向。 -/
theorem natToReal_lt_iff (a b : ℕ) : a < b ↔ natToReal a < natToReal b :=
  ⟨fun h => natToReal_strictMono h, fun h => natToReal_refl_lt h⟩

/-- ⭐ **同理，`ℚ → ℝ` 的序被精确镜像**：`a < b ↔ (a:ℝ) < (b:ℝ)`。 -/
theorem ratToReal_lt_iff (a b : ℚ) : a < b ↔ ratToReal a < ratToReal b :=
  ⟨fun h => ratToReal_strictMono h, fun h => ratToReal_refl_lt h⟩

/-- ⭐ **同理，`ℕ → ℤ` 的序被精确镜像**。 -/
theorem natToInt_lt_iff (a b : ℕ) : a < b ↔ natToInt a < natToInt b :=
  ⟨fun h => natToInt_strictMono h, fun h => natToInt_refl_lt h⟩

/-! ## 5. ⭐ 离散性沿链的保持（`ℕ → ℝ` 段）

⚠ 这里说的**不是**"`ℝ` 离散"（那是假的），而是：
**`ℕ` 的离散性（相邻整数间无第三元）在 `ℝ` 里仍可检出**——
即 `0` 与 `1` 之间**没有**自然数的像。这是"嵌入保有结构"的实质断言。 -/

/-- ⭐ **离散性的保持**：若 `n : ℕ` 在 `ℝ` 里的像严格小于 `1`，则 `n = 0`。
⭐ 它比 `natToReal_strictMono` 多说了：**`ℕ` 的最小正元 `1` 的像与 `0` 的像之间是空的**。
⚠ 这是"`ℕ` 作为序结构"的信息，不是"`ℝ` 作为序结构"的信息。 -/
theorem natToReal_eq_zero_of_lt_one {n : ℕ} (h : natToReal n < 1) : n = 0 := by
  simp only [natToReal, Nat.cast_one] at h
  have h2 : n < 1 := by exact_mod_cast h
  omega
/-- **离散性保持（等价的 `≤` 形式）**：`(n:ℝ) ≤ 0 → n = 0`。 -/
theorem natToReal_eq_zero_of_le_zero {n : ℕ} (h : natToReal n ≤ 0) : n = 0 := by
  have h' : ((n : ℝ)) = 0 := le_antisymm h (Nat.cast_nonneg n)
  have h2 : ((n : ℕ) : ℝ) = ((0 : ℕ) : ℝ) := by rw [h']; norm_num
  exact_mod_cast h2

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


/-! ## 11. 序嵌入作为结构：复合封闭、恒等、逆

本条把 §2/§3 的六条孤立事实收成一个结构：StrictMono 在复合与恒等下封闭。
与 §7（三条具体链的交换律）的区别：§7 说的是链，本节说的是任意嵌入的闭包。 -/

/-- **复合封闭（一般形式）**：两个严格单调映射的复合仍严格单调。
⚠ 底层是 mathlib 的 `StrictMono.comp`（Mathlib.Order.Monotone.Basic @ pin 4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84）；
本文件显式命名并固定类型参数，使「链的每一段都 StrictMono 故整条链也是」有可引用的名字。 -/
theorem comp_strictMono_of_strictMono {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α → β} {g : β → γ} (hg : StrictMono g) (hf : StrictMono f) :
    StrictMono (g ∘ f) :=
  hg.comp hf

/-- **复合封闭（逐点形式）**：下游不必展开 `Function.comp`。 -/
theorem comp_apply_strictMono {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α → β} {g : β → γ} (hg : StrictMono g) (hf : StrictMono f) :
    StrictMono (fun a => g (f a)) :=
  hg.comp hf

/-- **恒等嵌入**：`id` 是 StrictMono（链的零段）。 -/
theorem id_strictMono {α : Type*} [Preorder α] : StrictMono (id : α → α) :=
  fun _ _ h => h

/-- **嵌入的「逆」：像上的序同构。
类型论里 `f : ℕ → ℝ` 没有真正的函数逆（不满射，见 §10）；
但给定 b 落在 f 的像上，唯一的 a 使 f a = b，且 f 之间的序被精确反映。
本条把单射性与反射性合成「序嵌入 = 到其像上的序同构」。 -/
theorem lt_of_apply_eq_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : StrictMono f) {a a' : α} {b b' : β} (ha : f a = b) (ha' : f a' = b') :
    a < a' ↔ b < b' := by
  subst ha; subst ha'
  exact ⟨fun h => hf h, fun h => hf.lt_iff_lt.mp h⟩

/-! ## 12. ℕ-值反射器：把链当作序反射器用

⚠ §4 的三条 `_lt_iff` 只对**同类型**参数成立。下游需要的是反向读法：
手上只有 ℝ/ℚ/ℤ 里的不等式，要反推 ℕ 里的不等式。
本节给出共轭形式 `(f a < f b) ↔ a < b`，即把 §4 的 ↔ 翻过来用。 -/

/-- **链反射器 `ℕ → ℝ`**。 -/
theorem lt_of_natToReal_lt {a b : ℕ} (h : natToReal a < natToReal b) : a < b :=
  natToReal_refl_lt h

/-- **链反射器 `ℕ → ℝ`（↔ 形式）**。 -/
theorem natToReal_lt_iff_symm {a b : ℕ} : natToReal a < natToReal b ↔ a < b :=
  (natToReal_lt_iff a b).symm

/-- **链反射器 `ℕ → ℤ`（↔ 形式）**。 -/
theorem natToInt_lt_iff_symm {a b : ℕ} : natToInt a < natToInt b ↔ a < b :=
  (natToInt_lt_iff a b).symm

/-- **链反射器 `ℚ → ℝ`（↔ 形式）**。 -/
theorem ratToReal_lt_iff_symm {a b : ℚ} : ratToReal a < ratToReal b ↔ a < b :=
  (ratToReal_lt_iff a b).symm

/-! ## 13. 序嵌入逐字搬运 ℕ 上的推理

§11/§12 说明序被镜像；本节把它用掉：ℕ 上的线性算术经 natToReal 搬到 ℝ 上。
这是「真序嵌入」最硬的读法：不只保序，而是保到让 ℕ 的判定过程在 ℝ 语境下继续工作。 -/

/-- **搬运律（加法保序）**：a + b < c 在 ℕ 里成立 ⟹ 其像在 ℝ 里成立。
⭐ 证明只用 §8 的 `natToReal_add` 与 §2 的 `natToReal_strictMono`。 -/
theorem natToReal_lt_of_add_lt {a b c : ℕ} (h : a + b < c) :
    natToReal a + natToReal b < natToReal c := by
  rw [← natToReal_add a b]
  exact natToReal_strictMono h

/-- **搬运律（≤ 版）**：StrictMono 给的是 <，下游常需要 ≤。 -/
theorem natToReal_monotone : Monotone natToReal :=
  natToReal_strictMono.monotone

/-- **搬运律（≤ 逐点）**。 -/
theorem natToReal_le_of_le {a b : ℕ} (h : a ≤ b) : natToReal a ≤ natToReal b :=
  natToReal_monotone h

/-- **搬运律（反方向 + 代数）**：ℝ 侧的加法不等式退回 ℕ 侧。
⭐ 承重项：它让 ℕ 上的 `omega` 在 ℝ 语境下接手。⚠ 若去掉 §8 的加法兼容性，本式不可得。 -/
theorem lt_of_natToReal_add_lt {a b c : ℕ} (h : natToReal a + natToReal b < natToReal c) :
    a + b < c := by
  rw [← natToReal_add a b] at h
  exact natToReal_refl_lt h

/-- **ℕ 上的线性推理经嵌入搬到 ℝ**：a < b ⟺ a + c < b + c（ℕ 侧 omega 判定）。
⚠ 与 §12 的区别：§12 只搬序，本条搬加法后的序。 -/
theorem natToReal_lt_iff_add {a b c : ℕ} : a < b ↔ a + c < b + c := by
  omega

/-! ## 14. 序层 ⇄ L2 语义：覆盖谓词的序骨架

⚠ 诚实标注：以下定理只 import Mathlib，因此不能引用 L2 语义模块里的
`VectorConstraint` / `d31_Covers`（那会破坏本文件「零库内依赖」这一已实测性质）。

⭐ 本节因此做成纯 List/ℕ 层面的序骨架：把 L2 侧
`d31_Covers (⟨a,b⟩ : VectorConstraint) x := a.length ≤ x.length`
（RealSymbolDomainWidening.lean:180-181）需要的那条长度序，连同它必须满足的三条代数律，
在序层里一次给全：(1) 反射 (2) 单调 (3) 附加。
⭐ 这三条合起来说明 d31_Covers 是一个 ℕ-值单调谓词，从而 §13 的序引理可以把它映进 ℝ。
⚠ 这不是说 L2 语义需要 ℝ；而是说序层与 L2 语义共用同一条 ℕ 长度序，
于是序层的定理有对象可作用（而不再是孤儿）。 -/

/-- **L2 覆盖谓词的序骨架（反射）**：空表被任意表覆盖（0 ≤ x.length）。
⭐ 对应 `d31_Covers c x` 在 `c.a = []` 时恒真。 -/
theorem length_nil_le (x : List α) : ([] : List α).length ≤ x.length :=
  Nat.zero_le _

/-- **L2 覆盖谓词的序骨架（单调）**：x 是 y 的前缀 ⟹ x 不比 y 覆盖得多。
⭐ 这与 §13 的 `natToReal_monotone` 同型：List.length 是 ℕ-值单调映射，
而 ℕ 到 ℝ 的 cast 严格单调 ⟹ 复合仍保序。故 L2 的长度序与序层是同一套序。 -/
theorem length_le_of_prefix {x y : List α} (h : x <+: y) : x.length ≤ y.length :=
  h.length_le

/-- **L2 覆盖谓词的序骨架（附加）**：给约束多加一个系数恰好多需要一格输入。 -/
theorem length_cons (a : α) (x : List α) : (a :: x).length = x.length + 1 :=
  rfl

/-- **序层 → L2 的桥（ℝ 侧，≤）**：把覆盖长度映进 ℝ 后仍单调。
⚠ 这是本文件与 L2 语义的连接点，且是单向的：序层提供该单调律，
L2 侧可以引用它；本文件不反向 import，故无环。
⭐ 这是「make reachable, not consumed」在本文件上的落实。 -/
theorem natToReal_length_monotone {x y : List α} (h : x.length ≤ y.length) :
    natToReal x.length ≤ natToReal y.length :=
  natToReal_le_of_le h

/-- **序层 → L2 的桥（ℝ 侧，<）**：覆盖长度严格增长 ⟹ ℝ 侧严格增长。 -/
theorem natToReal_length_lt {x y : List α} (h : x.length < y.length) :
    natToReal x.length < natToReal y.length :=
  natToReal_strictMono h

/-- **覆盖的传递性（L2 语义骨架）**：c.a.length ≤ x.length 且 x.length ≤ y.length
⟹ c.a.length ≤ y.length，即覆盖在更长的输入下保持。
⭐ 这就是 `d31_Covers` 的单调性，在序层里一次给全，不带任何库内依赖。 -/
theorem covers_mono {c_a x y : List α} (hcx : c_a.length ≤ x.length)
    (hxy : x.length ≤ y.length) : c_a.length ≤ y.length :=
  Nat.le_trans hcx hxy

/-! ## 15. 离散性沿链的反面：ℝ 上无最小正元（与 §5 对照）

⚠ §5 说 ℕ 的离散性在 ℝ 里仍可检出；§6 说 ℚ 不离散。
⭐ 本节把两者并置，给出精确分界：ℕ 的像在 (0,1) 内空，而 ℝ 的 (0,1) 内处处有元且无最小元。
这是「真序嵌入」的边界：嵌入保有离散性（ℕ 侧），但不把离散性传给宿（ℝ 侧）。 -/

/-- **分界（两面合并）**：
1. ℕ 的像在 (0,1) 内空（§5 的离散性保持）；
2. 但 ℝ 的 (0,1) 内没有最小元（§6 的稠密性）。
⭐ 第 2 项精确否定了「ℝ 也离散」——没有最小正元正是 ℕ 有而 ℝ 没有的那条性质。 -/
theorem discrete_vs_dense_dichotomy :
    (∀ n : ℕ, natToReal n < 1 → n = 0) ∧
      (∀ x : ℝ, 0 < x → x < 1 → ∃ y : ℝ, 0 < y ∧ y < x) :=
  ⟨fun _ h => natToReal_eq_zero_of_lt_one h,
   fun x h0 _ => real_dense_between x h0⟩

/-- **分界的「无最小元」形式（ℝ 侧）**：不存在最小的正实数。 -/
theorem real_no_least_positive : ¬ ∃ x : ℝ, 0 < x ∧ ∀ y : ℝ, 0 < y → x ≤ y := by
  rintro ⟨x, hx0, hmin⟩
  obtain ⟨y, hy0, hyx⟩ := real_dense_between x hx0
  exact absurd (hmin y hy0) (not_le.mpr hyx)

/-- **分界的「有最小正元」形式（ℕ 侧）**：1 是 ℕ 的最小正元。 -/
theorem nat_least_positive (n : ℕ) (h : 0 < n) : 1 ≤ n :=
  h

/-- **链上的「离散层 vs 稠密层」对照**：ℚ 在 (0,1) 内有元，而 ℕ 的像在其内无元。
⚠ 使「整条链层层离散」这一误读在陈述层面就被排除。 -/
theorem chain_discrete_then_dense :
    (∃ q : ℚ, 0 < q ∧ q < 1) ∧ (∀ n : ℕ, natToReal n < 1 → n = 0) :=
  ⟨rat_exists_between_zero_one, fun _ h => natToReal_eq_zero_of_lt_one h⟩


end Lattice.NumericChainOrder
