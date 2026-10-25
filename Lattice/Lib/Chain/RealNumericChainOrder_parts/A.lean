import Mathlib

/-!
# `RealNumericChainOrder.lean` 的 `A` 部分

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
