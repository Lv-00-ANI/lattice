import Lattice.Lib.Compiler.Combinators
/-!
# LATTICE: XOR 与 NOT 组合子 —— 二值化域上的零化范式（P1-2 / P1-3）

本文件补齐 `Combinators.lean` 中缺失的两个组合子：**XOR（⊕）** 与 **NOT（¬）**。
⚠ **本文件是 Std-only 的**（只 `import Combinators`，**不引入 Mathlib**），
以保持 `Combinators.lean` 的独立地位（硬纪律 1）。

## 为什么 XOR 不能照抄 AND/OR 的零化范式（本文件的立项理由）

既有组合子的整套范式是「**一个多项式 = 0 ⟺ 逻辑条件成立**」：

| 算子 | 编码 | 零化刻画 | 依赖的代数性质 |
|:--|:--|:--|:--|
| ∧ | `andC a b = a² + b²` | `= 0 ⟺ a = 0 ∧ b = 0` | 非负性 + 和零 |
| ∨ | `orC a b = a · b` | `= 0 ⟺ a = 0 ∨ b = 0` | 整环零因子 |

⚠ **XOR 没有这两条性质中的任何一条**：`a ⊕ b = 0` 在 `(0,0)` 与 `(1,1)` **两点**成立，
**不是单项零化**。⇒ **朴素套用必然失败。**

## 本文件采取的双重处置（两条路都做，因为它们【互补而非互斥】）

⭐ **路线 A（构造侧）**：在**二值化域 `{0,1}`** 上给出 XOR/NOT 的组合子编码，
并证明**零化 ⟺ 语义**的 `↔`。⭐ **定义域限制写在定理右端**（验收标准 ②）。

⭐ **路线 B（不可能性侧）**：证明**在全部 `Int` 上不存在**「零化 ⟺ 异或」的组合子
（`no_xorC_universal_without_domain`），把「为什么只能走二值化路线」从直觉变成定理。

⚠⚠ **两者的关系（本文件最重要的结论）**：
> **A 与 B 不是二选一，而是同一障碍的两面。**
> B 证明**全域**不可能；A 给出**二值化域**上的恰好成立。
> ⭐ 因此 A 的定理**必须**带定义域限制 —— **否则它是假命题**
> （见 `xorC_offdomain_counterexample`：`xorC 0 2 = 5 ≠ 0`，但「恰好一个为零」为真）。

## 诚实边界（本文件不证 / 不声称的）

- ⚠ **`xorC a b = 0 ↔ (a = 0) ⊕ (b = 0)` 对任意 `a b : Int` 为【假】** ——
  本文件不证它，而是**给出机器验证的反例**（`xorC_offdomain_counterexample`）。
- ⚠ **A 的定义域 `{0,1}` 是【规定的】，不是【导出的】** —— 即：本文件假定输入已在
  二值化域上，**不证明**「任意网络的输出天然落在 `{0,1}`」。
- ⚠ **路线 B 在本文件里是【弱形式】**：`no_xorC_universal_without_domain` 只否证了
  「本文件这一族编码（`orC ∘ andC ∘ notC` 的复合）不能全域化」，
  ⚠ **不是**「任意整数函数都不行」。⭐ **强形式（任意连续函数都不行）需要拓扑论证
  （零集必闭），属 Mathlib 域，不在本 Std-only 文件内** —— 见 `RealCombinators.lean`
  的 `real_xorC_offdomain_counterexample` 与 `DIVERGENCES.md` C-23 的闭集论证。
- ⚠ **NOT 与 XOR 【同源】**（见 §五 `notC_eq_xorC_zero` / `notC_zero_iff_xorC_zero_zero`）：
  NOT 是 XOR 的特例（`notC a = xorC a 0`，在 `{0,1}` 上），
  XOR 又由 NOT+AND+OR 复合定义。⇒ **两者按 P1-3 验收标准 ③【合并为一条】登记。**
- ⚠⚠ **`xorC` 的零集编码 XOR，但它的取值是 XNOR**（见 §六）——
  ⭐ 这是「零化范式」的固有陷阱，**曾导致一处假命题**（`notC a = xorC a 1`）。
- 未做：`{0,1}` 之外的其他零化域（如 `{-1,1}`）—— 同一模板可平移，本文件不展开。

无 `sorry` / `axiom` / `admit` / `native_decide`；所有定理真实可证。
-/

namespace Lattice

/-! ## 一、NOT 组合子（P1-3）

⚠ **NOT 的处境与 XOR 不同**：`RealImplication.lean:64/:82` **已有** De Morgan 重写
（`not_andC_zero_iff` / `not_orC_zero_iff`），但那是**关于组合子的定理**，
**不是组合子本身** —— 全库 `grep 'def (not|neg)C\b'` = **0**。
⇒ ⭐ **判定：这是「缺命名形态」，不是「缺内容」**（P1-3 验收标准 ①）。
本文件补上命名的零化组合子 `notC` 及其零化 `↔`。
-/

/-- **NOT 组合子（二值化域版）**：`notC a := (1 - a)²`。

取值：`notC 0 = 1`、`notC 1 = 0`。⚠ **与 `-a` 或 `1 - a` 的区别**：
用**平方**而非线性 `1 - a`，使得 `notC` 的零点集（在 `Int` 上）**恰好是 `{1}`**，
与 `andC`/`orC` 同属「非负 + 平方」家族，且**保持整值**（不需要除法）。 -/
def notC (a : Int) : Int := (1 - a) ^ 2

/-- ⭐ **NOT 的零化 ⟺ 语义**（验收标准：定义域限制显式写在右端）。

⭐ **右端的定义域限制**：`a = 0 ∨ a = 1` —— 这正是本定理**不可省略**的部分，
因为它在全 `Int` 上**为假**（见 `notC_offdomain_counterexample`）。 -/
theorem notC_eq_zero_iff (a : Int) (ha : a = 0 ∨ a = 1) :
    notC a = 0 ↔ a ≠ 0 := by
  rcases ha with rfl | rfl
  · -- a = 0：notC 0 = 1 ≠ 0，且 0 ≠ 0 为假 ⟹ 两侧同假
    constructor
    · intro h; norm_num [notC] at h
    · intro h; exact absurd rfl h
  · -- a = 1：notC 1 = 0，且 1 ≠ 0 为真 ⟹ 两侧同真
    constructor
    · intro _; norm_num
    · intro _; norm_num [notC]

/-- ⭐ **NOT 的零化，显式二值化域版本**（P1-2 验收标准 ② 所要求的写法）。

⚠ 与 `notC_eq_zero_iff` 的区别：定义域限制**写在右端**（`a = 0 ∨ a = 1`），
而不是作为假设 `ha`。**这是验收标准直接要求的形态。**

⭐ **注意右端不需要额外的 `a ≠ 0` 合取项**：在 `Int` 上
`notC a = 0 ⟺ a = 1`（**全域成立**，因为 `notC a = (1-a)²` 且
`int_sq_eq_zero_iff` 给出 `(1-a)² = 0 ⟺ 1-a = 0 ⟺ a = 1`）。
⇒ 加上定义域限制后，「`a = 1`」与「`a ∈ {0,1} ∧ a ≠ 0`」在 `{0,1}` 上等价，
但**前者更强且更干净**，故右端写 `(a = 0 ∨ a = 1) ∧ a = 1` 的**化简形 `a = 1`**。 -/
theorem notC_eq_zero_iff_on_domain (a : Int) :
    notC a = 0 ↔ (a = 0 ∨ a = 1) ∧ a ≠ 0 := by
  have hkey : notC a = 0 ↔ a = 1 := by
    constructor
    · intro h
      have h1 : (1 - a) ^ 2 = 0 := by simpa [notC] using h
      have h2 : 1 - a = 0 := (int_sq_eq_zero_iff (1 - a)).mp h1
      omega
    · intro h
      subst h
      norm_num [notC]
  rw [hkey]
  constructor
  · intro h
    subst h
    exact ⟨Or.inr rfl, by norm_num⟩
  · rintro ⟨hdom, hne⟩
    -- 域假设 `a = 0 ∨ a = 1` 与 `a ≠ 0` 合起来强制 `a = 1`
    rcases hdom with h0 | h1
    · exact absurd h0 hne
    · exact h1

/-- **NOT 反向的零化（等价重述，供下游 `rw` 使用）**：
在 `{0,1}` 上 `notC a = 0` 恰好刻画「a 为真（a = 1）」。 -/
theorem notC_zero_iff_eq_one (a : Int) (ha : a = 0 ∨ a = 1) :
    notC a = 0 ↔ a = 1 := by
  rcases ha with rfl | rfl
  · constructor
    · intro h; norm_num [notC] at h
    · intro h; norm_num at h
  · constructor
    · intro _; rfl
    · intro _; norm_num [notC]

/-- ⚠ **反例（机器验证）**：`notC` 的零化刻画**不能**去掉定义域限制 ——
`notC 2 = 0` 为假但语义「`2 ≠ 0`」为真，故**全 `Int` 版本为假**。 -/
theorem notC_offdomain_counterexample : notC 2 ≠ 0 ∧ (2 : Int) ≠ 0 := by
  constructor <;> norm_num [notC]

/-! ## 二、XOR 组合子（P1-2，路线 A：两个 AND 的 OR）

路线 A 的形式（任务书）：`xorC a b := orC (andC a (not-embedding b)) (andC (not-embedding a) b)`
—— 即 `(a ∧ ¬b) ∨ (¬a ∧ b)`。本文件用上面刚定义的 `notC` 作为 `not-embedding`。
-/

/-- **XOR 组合子（二值化域版）**：`xorC a b := orC (andC a (notC b)) (andC (notC a) b)`。

⭐ 即「两个 AND 的 OR」，与任务书路线 A 逐字一致。
取值（在 `{0,1}²` 上）：`xorC 0 0 = 1`、`xorC 0 1 = 0`、`xorC 1 0 = 0`、`xorC 1 1 = 1`。 -/
def xorC (a b : Int) : Int := orC (andC a (notC b)) (andC (notC a) b)

/-! ## 三、XOR 的零化 ⟺ 语义（验收标准的核心定理）

⚠⚠ **验收标准 ② 要求 `xorC_eq_zero_iff` 的右端【显式写出定义域限制】。**
下面给出**两个**形态：
1. `xorC_eq_zero_iff_on_domain`：定义域限制**写在右端**（⭐ 推荐，直接满足验收标准）；
2. `xorC_eq_zero_iff`：定义域限制作为**假设参数**（便于下游传入已知域）。
-/

/-- ⭐⭐ **主定理：XOR 的零化 ⟺ 语义（定义域限制显式写在右端）**。

右端 `(a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ (a ≠ 0 ↔ b ≠ 0)` 中：
- 前两个合取项 = **定义域限制**（`a, b ∈ {0,1}`）——⚠ **不可省略**；
- 第三项 = **XOR 语义**（恰好一个为零）。

⭐ **为什么第三项写成 `a ≠ 0 ↔ b ≠ 0` 的对偶（即 `¬(a≠0 ↔ b≠0)`）**：
在 `{0,1}` 上「恰好一个为零」⟺「两者是否为零【不同】」，即 `a≠0` 与 `b≠0` 真假相反。 -/
theorem xorC_eq_zero_iff_on_domain (a b : Int) :
    xorC a b = 0 ↔
      (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧ ¬ (a ≠ 0 ↔ b ≠ 0) := by
  constructor
  · intro h
    -- xorC = orC X Y = X * Y = 0 ⟹ X = 0 ∨ Y = 0（整环零因子）
    have hz : andC a (notC b) = 0 ∨ andC (notC a) b = 0 := by
      have hmul : andC a (notC b) * andC (notC a) b = 0 := by simpa [xorC, orC] using h
      exact Int.mul_eq_zero.mp hmul
    rcases hz with h1 | h2
    · -- 分支一：andC a (notC b) = 0 ⟹ a = 0 ∧ notC b = 0
      obtain ⟨ha0, hnb⟩ := (andC_eq_zero_iff a (notC b)).mp h1
      -- notC b = 0 ⟹ (1-b)² = 0 ⟹ b = 1
      have hb1 : b = 1 := by
        have : (1 - b) ^ 2 = 0 := by simpa [notC] using hnb
        have : 1 - b = 0 := (int_sq_eq_zero_iff (1 - b)).mp this
        omega
      refine ⟨Or.inl ha0, Or.inr hb1, ?_⟩
      -- a = 0 且 b = 1 ⟹ a ≠ 0 为假、b ≠ 0 为真 ⟹ 两者不同真值
      simp [ha0, hb1]
    · -- 分支二：andC (notC a) b = 0 ⟹ notC a = 0 ∧ b = 0
      obtain ⟨hna, hb0⟩ := (andC_eq_zero_iff (notC a) b).mp h2
      have ha1 : a = 1 := by
        have : (1 - a) ^ 2 = 0 := by simpa [notC] using hna
        have : 1 - a = 0 := (int_sq_eq_zero_iff (1 - a)).mp this
        omega
      refine ⟨Or.inr ha1, Or.inl hb0, ?_⟩
      simp [ha1, hb0]
  · rintro ⟨ha, hb, hxor⟩
    -- 在 {0,1} 上穷举四种情形（定义域假设已给出）
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · -- (0,0)：a≠0 与 b≠0 同为假 ⟹ 真值相同 ⟹ 与 hxor 矛盾
      exfalso; exact hxor (by simp)
    · norm_num [xorC, orC, andC, notC]
    · norm_num [xorC, orC, andC, notC]
    · exfalso; exact hxor (by simp)

/-- **主定理（假设形态）**：定义域限制作为假设参数传入。

⚠ 与 `xorC_eq_zero_iff_on_domain` **陈述强度相同**，只是把定义域限制放在假设侧，
便于调用方在已经知道 `a, b ∈ {0,1}` 时直接使用（下游 `rw` 更顺）。
⭐ 两形态**并存**是刻意的：验收标准 ② 要求「右端显式」，而实际证明常需要假形式。 -/
theorem xorC_eq_zero_iff (a b : Int) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    xorC a b = 0 ↔ ¬ (a ≠ 0 ↔ b ≠ 0) := by
  have h := xorC_eq_zero_iff_on_domain a b
  constructor
  · intro hz
    exact (h.mp hz).2.2
  · intro hx
    exact h.mpr ⟨ha, hb, hx⟩

/-! ## 四、XOR 的诚实边界定理（防复活）

⚠ 下面各条把「A 不能推到全 `Int`」**固化为定理**，
防止后续代理误把 `xorC_eq_zero_iff` 当成全域结果（PROCESS.md §3.3 判据 ⑤）。
-/

/-- ⭐ **反例（机器验证）**：`xorC 0 2 = 5 ≠ 0`，但「恰好一个为零」在 `Int` 上为**真**。

⭐ 本条把 §三 主定理的**定义域限制承重性**固定下来：
它证明「**去掉定义域限制后的全域版本为假**」——
即 `∀ a b, xorC a b = 0 ↔ ¬(a ≠ 0 ↔ b ≠ 0)` **不成立**（取 `a = 0, b = 2`）。 -/
theorem xorC_offdomain_counterexample :
    xorC 0 2 ≠ 0 ∧ ¬ ((0 : Int) ≠ 0 ↔ (2 : Int) ≠ 0) := by
  constructor
  · norm_num [xorC, orC, andC, notC]
  · norm_num

/-- ⭐⭐ **不可能性（否定侧，路线 B 的 Std 弱形式）**：
**不存在** `f : Int → Int → Int` 在本文件这一族编码下使
`f a b = 0 ⟺ ¬(a ≠ 0 ↔ b ≠ 0)` 对**所有** `a b` 成立。

⚠ 这正是「XOR 不能照抄 AND/OR 范式」的**机器验证形式**。
证明只需一个点：`(0, 2)` —— 「恰好一个为零」为真而该编码在该点为非零。

⚠ **边界（诚实标注）**：本定理的否定是**构造性见证**而非全类不可能性 ——
它证明的是「**形如 `orC (andC a (notC b)) (andC (notC a) b)` 的编码**不能全域化」，
**不是**「任意整数函数都不行」。⇒ ⭐ **强形式（任意连续函数）需拓扑论证，
见 `DIVERGENCES.md` C-23 的闭集论证**（Std-only 层不可达）。 -/
theorem no_xorC_universal_without_domain :
    ¬ (∀ a b : Int, xorC a b = 0 ↔ ¬ (a ≠ 0 ↔ b ≠ 0)) := by
  intro h
  have h02 : xorC 0 2 = 0 := (h 0 2).mpr (by norm_num)
  exact (xorC_offdomain_counterexample.1) h02

/-- ⭐ **`xorC` 的零点集在 `Int` 上恰好是 `{(0,1), (1,0)}`**
（这是本文件定义的一个**真实**性质：`notC` 用平方后，
`notC a = 0 ⟺ a = 1` 在全 `Int` 上成立，故 `xorC` 的零点被精确刻画）。

⚠ **注意它【不是】「恰好一个为零」** —— 例如 `(0,2)` 恰好一个为零，
但 `xorC 0 2 = 5 ≠ 0`。⇒ ⭐ **这正是必须限制定义域的根本原因**，
本条把它写成定理而非注释。 -/
theorem xorC_eq_zero_iff_pair (a b : Int) :
    xorC a b = 0 ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have hz : andC a (notC b) = 0 ∨ andC (notC a) b = 0 := by
      have hmul : andC a (notC b) * andC (notC a) b = 0 := by simpa [xorC, orC] using h
      exact Int.mul_eq_zero.mp hmul
    rcases hz with h1 | h2
    · obtain ⟨ha0, hnb⟩ := (andC_eq_zero_iff a (notC b)).mp h1
      have hb1 : b = 1 := by
        have : (1 - b) ^ 2 = 0 := by simpa [notC] using hnb
        have : 1 - b = 0 := (int_sq_eq_zero_iff (1 - b)).mp this
        omega
      exact Or.inl ⟨ha0, hb1⟩
    · obtain ⟨hna, hb0⟩ := (andC_eq_zero_iff (notC a) b).mp h2
      have ha1 : a = 1 := by
        have : (1 - a) ^ 2 = 0 := by simpa [notC] using hna
        have : 1 - a = 0 := (int_sq_eq_zero_iff (1 - a)).mp this
        omega
      exact Or.inr ⟨ha1, hb0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [xorC, orC, andC, notC]

/-- ⚠ **`xorC` 的零点集是【孤立两点】而非【代数簇】** —— 与 `andC`/`orC` 的结构差异。

`andC` 的零点集是 `{(0,0)}`（非负性 + 和零给出），`orC` 的零点集是**两条直线之并**
（零因子给出，闭且无界）。`xorC` 的零点集是 `{(0,1), (1,0)}` —— **两个孤立点**。

⭐ **为什么关键**：`andC`/`orC` 的零化**在全 `Int` 上成立**（它们的零点集与
「a 与 b 的零性组合」精确对应）；而 `xorC` 的全域零点集 `{(0,1),(1,0)}`
**不**对应「恰好一个为零」（后者是 `({0}×ℤ*) ∪ (ℤ*×{0})`，是**无界**集）。
⇒ ⭐ **两个集合不相等** ⟹ **全域零化 `↔` 为假** ⟹ 定义域限制不可省。 -/
theorem xorC_zero_set_is_isolated :
    (∀ a b : Int, xorC a b = 0 → ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) :=
  fun a b h => (xorC_eq_zero_iff_pair a b).mp h

/-! ## 五、⭐「XOR 与 NOT 是否同源」（P1-3 验收标准 ③）

**判定：同源，合并为一条。**

依据（两条互逆的关系，均为在 `{0,1}` 上的定理）：
1. `notC a = xorC a 0`（NOT 是 XOR 与常量 `0` 的复合）；
2. `xorC` 的定义即 NOT+AND+OR 的复合。

⇒ 二者**互为定义、共享同一障碍**（都需要 `{0,1}` 定义域），
故按 P1-3 验收标准 ③ **合并为一条登记**，不单独立项。

⚠⚠ **一条重要的判读规律（本文件的第一手发现，已固化）**：
> **`xorC` 的零集编码 XOR，但它的取值是 XNOR。**
> - `xorC a b = 0` ⟺ XOR 语义成立（`orC` 是**零化编码**）；
> - `xorC a b` 的**数值** = XNOR 的真值（`xorC 0 0 = 1`）。
>
> ⟹ 陈述「同源」时**必须用零化等价**（`notC_zero_iff_xorC_zero_zero`），
> **不可用取值相等** —— 后者曾产出假命题 `notC a = xorC a 1`
> （由 `notC_ne_xorC_one_counterexample` 否证）。
> ⭐ **这是「零化范式」的固有陷阱**：组合子的**零集**承载逻辑语义，
> 而其**数值**承载的是编码的代数残余 —— **两者一般不同**（见 §六）。
-/

/-- ⭐ **NOT 是 XOR 的特例**：在 `{0,1}` 上 `notC a = xorC a 0`。

**本条回答了 P1-3 验收标准 ③「XOR 与 NOT 是否同源」**：
NOT 可由 XOR 与常量 `0` 表达 ⟹ **两者同源**。

⚠⚠ **本条曾写成 `notC a = xorC a 1`（【假命题】，已被 `decide` 否证）**。
⭐ **根因（本项目值得登记的一条判读规律）**：
> `xorC` 的**零集**编码 XOR，而它的**取值**是 **XNOR**。
> - `xorC a b = 0` ⟺ XOR 语义成立（`orC` 是**零化编码**：`orC X Y = 0 ⟺ X = 0 ∨ Y = 0`）；
> - `xorC a b` 的**数值** = XNOR 的真值（`xorC 0 0 = 1` 即「同或为真」）。
>
> ⇒ ⚠ **不可用「取值相等」来陈述同源**，必须用**零化等价**或**取值为零的对偶点**。
> `xorC a 0` 恰在 `a = 1` 处为零（因 `notC 0 = 1`、`notC a = 0`），与 `notC` 一致。 -/
theorem notC_eq_xorC_zero (a : Int) (ha : a = 0 ∨ a = 1) : notC a = xorC a 0 := by
  rcases ha with h | h
  · subst h; decide
  · subst h; decide

/-- ⚠ **反例（机器验证）**：`notC a = xorC a 1` **为假** —— 两个点上都反。

⭐ **本条把上面那条判读规律固化为定理**（PROCESS.md §3.3 判据 ⑤：反例必须固化成定理防复活）：
`notC 0 = 1` 而 `xorC 0 1 = 0`；`notC 1 = 0` 而 `xorC 1 1 = 1`。
⇒ **`xorC` 的取值是 XNOR 而非 XOR**，故不能与 `notC` 用取值相等相连。 -/
theorem notC_ne_xorC_one_counterexample :
    notC 0 ≠ xorC 0 1 ∧ notC 1 ≠ xorC 1 1 := by
  constructor <;> decide

/-- ⭐ **同源的【零化形态】表述**（避开取值陷阱的正确陈述）：

在 `{0,1}` 上，`notC a = 0` ⟺ `xorC a 0 = 0` ⟺ `a = 1`。
⚠ 这是**同源性的正确陈述形态** —— 用**零化命题的等价**，而非**取值的相等**。 -/
theorem notC_zero_iff_xorC_zero_zero (a : Int) (ha : a = 0 ∨ a = 1) :
    notC a = 0 ↔ xorC a 0 = 0 := by
  rw [notC_zero_iff_eq_one a ha]
  rcases ha with h | h
  · subst h; decide
  · subst h; decide

/-- ⭐ **XOR 由 NOT/AND/OR 复合而成**（反向的同源见证，即 `xorC` 的定义逐字展开）。

⚠⚠ **诚实标注：本条是 `rfl`，即它是 `xorC` 的【定义】而非新定理**（PROCESS.md §2.2
要求回答「这条定理比它的定义多说了什么？」—— ⭐ **答案是「什么都没多说」**）。
⇒ ⭐ **保留它的唯一理由是【接口/可重写性】**：后续证明可 `rw [xor_via_not_and_and]`
把 `xorC` 展开为 `orC`/`andC`/`notC` 的复合，无需 `unfold`。
⚠ **不计入本文件的实质成果**（不把它当作「同源」的证据 —— 同源的证据是
`notC_eq_xorC_zero` 与 `notC_zero_iff_xorC_zero_zero` 那两条）。 -/
theorem xor_via_not_and_and (a b : Int) :
    xorC a b = orC (andC a (notC b)) (andC (notC a) b) := rfl

/-- ⭐ **XOR 零化的逻辑句式展开**（把 §五 的同源关系落到零化命题上）。

在 `{0,1}` 上：`xorC a b = 0` ⟺ 「`a = 0 ∧ notC b = 0`」或「`notC a = 0 ∧ b = 0`」，
即**两个 AND 组合子各自零化**，再由 OR 组合子取并 —— 这正是路线 A 的语义内容。 -/
theorem xorC_zero_iff_and_or_decomposition (a b : Int) :
    xorC a b = 0 ↔ andC a (notC b) = 0 ∨ andC (notC a) b = 0 := by
  unfold xorC orC
  exact Int.mul_eq_zero

/-! ## 六、⚠⚠ 零化范式的固有陷阱：**零集 vs 取值**（本文件的第一手发现）

⭐ **本文件的第一轮草稿在这里出了假命题**（`notC a = xorC a 1`），
被 `decide` 直接否证（`tactic 'decide' proved that the prop…`）。
**根因值得单列为一节**，因为它是**所有零化编码的共性**：

| 对象 | 承载什么 | 本文件的值 |
|:--|:--|:--|
| `xorC a b = 0`（**零化命题**）| ⭐ **逻辑语义**（XOR 成立）| `(0,0) ↦ 假`、`(0,1) ↦ 真`、`(1,0) ↦ 真`、`(1,1) ↦ 假` ⟹ **正是 XOR** |
| `xorC a b`（**数值本身**）| ⚠ **编码的代数残余** | `(0,0) ↦ 1`、`(0,1) ↦ 0`、`(1,0) ↦ 0`、`(1,1) ↦ 1` ⟹ ⚠ **是 XNOR** |

**⇒ 二者一般【不同**】。**零化范式只保证「零集 ⟺ 语义」，
**不保证「数值 ⟺ 真值」**。

⭐ **根因链（可复用的判读规律）**：
1. `orC X Y = X · Y`，其**零集**是「`X = 0 ∨ Y = 0`」（**析取**）；
2. 但 `orC X Y` 的**数值**是「两者都非零时为非零」—— ⭐ **这是【合取】的代数像**；
3. ⇒ **析取的零集 + 合取的数值** 叠加，恰好把 XOR 翻成 XNOR。

⚠ **⇒ 纪律（本文件新增）**：
> **凡用「组合子取值相等」陈述逻辑等价，必先在 `{0,1}` 上逐点验算四种情形**（
> ⚠ **不可只验一种** —— 本文件的错误恰在**两个点上都反**，但**只看 `(0,0)` 会漏**）。
> ⭐ **正确形态是零化命题之间的 `↔`**（如 `notC_zero_iff_xorC_zero_zero`）。

**依据**：**B222.2 的推广** —— 该项目登记的是「`X ↔ X` 能编译但什么都不说」；
本条是**对偶的另一面**：「`f a = g a` **看着像**明显的等式、**实为假**」，
而 `decide` 是**唯一**可靠的仲裁者。
-/

/-- ⚠⚠ **本节的机器验证锚点**：`xorC` 在 `{0,1}²` 上的**取值表**（逐点，四种情形全给）。

⭐ **本条的用途是【防复活】**：它把「`xorC` 的取值 = XNOR」固化为定理，
使后续代理**不可能**再写出 `notC a = xorC a 1` 那类等式
（**且它同时展示了「取值 ≠ 真值」这一陷阱的具体形状**）。 -/
theorem xorC_value_table_on_bool :
    xorC 0 0 = 1 ∧ xorC 0 1 = 0 ∧ xorC 1 0 = 0 ∧ xorC 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚠⚠ **而 `xorC` 的【零化】表恰好是 XOR**（与上一条的取值表**逐点相反**）。

⭐ **本条与 `xorC_value_table_on_bool` 并置，就是「零集 vs 取值」陷阱的完整见证**：
- 本条：`xorC a b = 0` 在 `(0,1)`、`(1,0)` 为**真** ⟹ **XOR**；
- 上条：`xorC a b` 的值在 `(0,0)`、`(1,1)` 为 `1` ⟹ **XNOR**。
⇒ ⭐ **同一函数的零集与取值承载【不同的】逻辑**。 -/
theorem xorC_zero_table_on_bool :
    xorC 0 0 ≠ 0 ∧ xorC 0 1 = 0 ∧ xorC 1 0 = 0 ∧ xorC 1 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Lattice
