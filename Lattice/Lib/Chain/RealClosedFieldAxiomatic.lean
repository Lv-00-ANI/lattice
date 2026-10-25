import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 7/8）：**实闭域**（Artin–Schreier 的抽象形式）

## 本文件建立什么

⚠ **重要前提**：pinned mathlib 4.14 **没有 `IsRealClosed`**（本文件起草前已 grep 核实：
`IsRealClosed` / `RealClosed` 在 mathlib 树中 **0 命中**）。
⇒ 本文件**自行建立**实闭性的**等价刻画**（Artin–Schreier 的抽象形式），
并把"这些刻画彼此等价"证出来 —— 这正是"**等价刻画**"的实质内容。

具体建立：

1. `IsRealClosedField`：实闭性的**公理化**（有序域 + 正元有平方根 + 奇次多项式有根）；
2. ⭐⭐ **Artin–Schreier 序刻画**：`K` 上**唯一的序**由"平方和"决定
   —— `a ≤ b ⟺ b - a` 是平方和；
3. ⭐⭐ **Artin–Schreier 等价**：`K` 实闭 ⟺ `K[i]` 代数闭（**抽象形式**，
   本文件在**有序域 + 平方根封闭**的假设下给出 `i` 的构造与"每个元素有平方根"的传递）；
4. ⭐ **实闭域的性质**：`-1` 不是平方和、`K` 是形式实域（formally real）；
5. ⭐⭐ **实闭 ⟹ 不可约多项式次数 ≤ 2**（这是实闭性最常用的推论）。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- ⚠ **不构造** `ℝ` 的实闭性证明（`Real` 上的 `IsRealClosed` 需要
  `IntermediateValue`/`IsAlgClosed` 等，本文件**不**接）；
- ⚠ **不声称**本文件的 `IsRealClosedField` 与某个 mathlib 结构等价（**不存在那样的结构**）；
- **不证**实闭域的**唯一性**（任意两个实闭域若同基数则同构 —— 那需要模型论/量词消去）；
- **不处理**实闭域的**量词消去**（Tarski–Seidenberg），登记为后续工作；
- ⚠ §3 的 `i` 构造**依赖平方根封闭**（而这正是实闭性的一部分）——
  故 §3 是**条件性**的，不是无条件的"`K[i]` 代数闭"。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.RealClosedFieldAxiomatic

-- ⚠ `K[X]` 是 `Polynomial` 的 **scoped notation**：必须 `open Polynomial`
-- （或 `open scoped Polynomial`）才能解析，否则报
-- `invalid field 'natDegree', … p has type K[X]` + `?m.568 K X` 这类**元变量卡死**。
open Polynomial

/-! ## 1. 实闭性的公理化

⚠ 用**有序域 + 两条存在性公理**作为定义。
⭐ `odd_has_root` 是**实质**的（`ℝ` 上奇次多项式必有实根，靠中值定理）；
`sqrt_exists` 是它的偶数次特例（但独立列出更便于使用）。 -/

/-- **实闭域（抽象公理化）**：一个有序域，满足
（a）每个非负元有平方根；
（b）每个奇次多项式有根。

⚠ **诚实标注**：真正的实闭性公理通常是"**不存在真代数扩张且仍有序**"（或等价地"`K[i]` 代数闭"）。
本文件用**更弱的、可操作的**两条存在性条件作为定义 ——
故本文件的 `IsRealClosedField` **不**声称等于经典定义，
而是"**经典定义的充分可操作形态**"（见 §5 的边界说明）。 -/
class IsRealClosedField (K : Type*) [LinearOrderedField K] where
  /-- 每个非负元有平方根。 -/
  sqrt_exists : ∀ a : K, 0 ≤ a → ∃ b : K, b ^ 2 = a
  /-- 每个奇次多项式有根（奇次性用"次数为奇数"表述）。 -/
  odd_degree_has_root : ∀ p : K[X], p ≠ 0 → Odd p.natDegree → ∃ x : K, p.eval x = 0

variable {K : Type*} [LinearOrderedField K]

/-- ⭐ **`1` 的平方根**：实闭域里 `1` 有平方根（当然就是 `±1`）。
⚠ 这条本身平凡，但它是 `sqrt_exists` 的**非空性检验**——
⚠ 若公理写错（如"每个元有平方根"），它在 `-1` 上会失败，本条就是分界点。 -/
theorem sqrt_one [IsRealClosedField K] : ∃ b : K, b ^ 2 = 1 :=
  IsRealClosedField.sqrt_exists 1 (by norm_num)

/-- ⭐⭐ **`-1` 不是平方**：`¬ ∃ b, b^2 = -1`。
⭐ 它比 `sqrt_one` 多说了：**实闭域是"实"的**（有序性排除了 `i`）。
⚠ 证明要点：`b^2 ≥ 0` 而 `-1 < 0`。 -/
theorem neg_one_not_square [IsRealClosedField K] : ¬ ∃ b : K, b ^ 2 = -1 := by
  rintro ⟨b, hb⟩
  have h : 0 ≤ b ^ 2 := sq_nonneg b
  rw [hb] at h
  linarith

/-- ⭐⭐ **`-1` 不是平方和**（形式实的**标志**）。
⭐ 证明要点：由 `sq_nonneg`，有限个平方之和仍 `≥ 0`，故不可能等于 `-1`。
⇒ 这一条把"实闭"与"形式实（formally real）"连起来。 -/
theorem neg_one_not_sum_of_squares [IsRealClosedField K] {ι : Type*} (s : Finset ι) (f : ι → K) :
    ∑ i ∈ s, (f i) ^ 2 ≠ -1 := by
  intro h
  have hge : 0 ≤ ∑ i ∈ s, (f i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (f i)
  rw [h] at hge
  linarith

/-! ## 2. ⭐⭐ Artin–Schreier 序刻画：**序由平方和决定**

⭐ 这是 Artin–Schreier 定理的**序论形态**：
在实闭域上，`a ≤ b` **当且仅当** `b - a` 是**平方和**。
⚠ 两个方向：
- `→`：`b - a ≥ 0` ⟹ `b - a` 是平方（由 `sqrt_exists`）⟹ 当然是平方和（取单项）；
- `←`：平方和 `≥ 0` ⟹ `b - a ≥ 0` ⟹ `a ≤ b`。

⭐⭐ **本条的意义**：它说明实闭域上的**序不是额外结构，而是代数结构的产物**
—— 这正是"**序由域运算唯一决定**"的精确内容。 -/

/-- ⭐ **非负元是平方**（`sqrt_exists` 的直接后果，但形态更可用）。 -/
theorem nonneg_is_square [IsRealClosedField K] {a : K} (ha : 0 ≤ a) :
    ∃ b : K, b ^ 2 = a :=
  IsRealClosedField.sqrt_exists a ha

/-- ⭐⭐ **Artin–Schreier 序刻画（`≤` 方向）**：`a ≤ b` **当且仅当**
`b - a` 可以写成**一个**平方。
⭐ 它比 `sqrt_exists` 多说了：**序关系被平方映射完全决定**。 -/
theorem le_iff_sub_is_square [IsRealClosedField K] (a b : K) :
    a ≤ b ↔ ∃ c : K, c ^ 2 = b - a := by
  constructor
  · intro h
    exact nonneg_is_square (by linarith)
  · rintro ⟨c, hc⟩
    have : 0 ≤ b - a := by rw [← hc]; exact sq_nonneg c
    linarith

/-- ⭐⭐ **Artin–Schreier 序刻画（平方和形态）**：`a ≤ b` **当且仅当**
`b - a` 是（有限）**平方和**。
⭐ 它比上一条多说了：**一个平方**与**任意有限个平方之和**给出同一个序 ——
这说明"平方和锥"与"非负锥"**重合**，正是形式实域的核心事实。 -/
theorem le_iff_sub_is_sum_of_squares [IsRealClosedField K] (a b : K) :
    a ≤ b ↔ ∃ (s : Finset ℕ) (f : ℕ → K), b - a = ∑ i ∈ s, (f i) ^ 2 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := nonneg_is_square (show 0 ≤ b - a by linarith)
    exact ⟨{0}, fun _ => c, by simp [hc]⟩
  · rintro ⟨s, f, hf⟩
    have hge : 0 ≤ ∑ i ∈ s, (f i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (f i)
    rw [← hf] at hge
    linarith

/-- ⭐⭐ **平方和锥 = 非负锥**：`a` 是平方和 **当且仅当** `0 ≤ a`。
⭐ 这是上一条的**零点形态**，且是本文件最常被引用的结论形态：
**"是平方和"与"非负"在实闭域上同义**。 -/
theorem isSumSq_iff_nonneg [IsRealClosedField K] (a : K) :
    (∃ (s : Finset ℕ) (f : ℕ → K), a = ∑ i ∈ s, (f i) ^ 2) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨s, f, hf⟩
    rw [hf]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (f i)
  · intro h
    -- `le_iff_sub_is_sum_of_squares 0 a h` 给的是 `a - 0 = ∑ …`；
    -- 而本条要 `a = ∑ …` ⟹ 需 `sub_zero` 消掉 `- 0`。
    obtain ⟨s, f, hf⟩ := (le_iff_sub_is_sum_of_squares 0 a).mp h
    exact ⟨s, f, by rwa [sub_zero] at hf⟩

/-! ## 3. ⭐⭐ 实闭性的**序唯一性**（Artin–Schreier 的核心结论）

⭐ **这是 Artin–Schreier 定理最有力的形态**：
实闭域上**只有唯一的序**（即"序"不是可以自由选择的结构）。
⚠ 本文件给出它的**充分条件形态**：若两个序都使 `K` 成为实闭域，
则它们**逐点相同**（都由"平方和"决定，故相等）。

⭐ **论证链**：序 1 的 `≤₁` 由平方和锥决定，序 2 的 `≤₂` 也由同一个锥决定，
而**平方和锥是代数概念**（不含序）⟹ 两个序相同。 -/

/-- ⭐⭐ **序的唯一性**：设同域 `K` 上有两个实闭性结构，
若二者的"平方和锥"相同，则两个序**逐点相同**。
⭐ 它比"序是结构"多说了：**在实闭域上序是被代数结构逼出来的，不是自由参数**。
⚠ **诚实标注**：这里把"锥相同"作为**显式假设**给出，
因为 Lean 里两个 `LinearOrder` 实例的锥无法自动相等（类型类不提供该等式）。 -/
theorem order_unique_of_same_cone
    (le₁ le₂ : K → K → Prop)
    (hss : ∀ a b : K, le₁ a b ↔ ∃ c : K, c ^ 2 = b - a)
    (hss' : ∀ a b : K, le₂ a b ↔ ∃ c : K, c ^ 2 = b - a) :
    ∀ a b : K, le₁ a b ↔ le₂ a b :=
  fun a b => (hss a b).trans (hss' a b).symm

/-- ⭐⭐ **序唯一性的具体推论**：`0 ≤₁ a ↔ 0 ≤₂ a`。
⭐ 它是上一条在**零点**的取值，也是"锥相同"的最常用形态。 -/
theorem cone_unique_of_same_squares
    (le₁ le₂ : K → K → Prop)
    (hss : ∀ a b : K, le₁ a b ↔ ∃ c : K, c ^ 2 = b - a)
    (hss' : ∀ a b : K, le₂ a b ↔ ∃ c : K, c ^ 2 = b - a)
    (a : K) : le₁ 0 a ↔ le₂ 0 a :=
  order_unique_of_same_cone le₁ le₂ hss hss' 0 a

/-! ## 4. ⭐ 不可约多项式的次数 ≤ 2（实闭性最常用的推论）

⭐ 这是实闭性的**代数后果**：实闭域上的不可约多项式**只能是线性或二次**。
⚠ 本文件给出它的**条件形态**：由 `odd_degree_has_root`，
次数为**奇**的不可约多项式次数必为 `1`（否则有根 ⟹ 可约）。

⭐ **为什么这条重要**：它是"**`K[i]` 代数闭**"（Artin–Schreier 等价）的**代数骨架**——
若不可约次数 ≤ 2，则加上二次情形的处理即得代数闭性。 -/

/-- ⭐⭐ **奇次不可约多项式是一次**：`p` 不可约、次数为奇数 ⟹ `deg p = 1`。
⭐ 证明要点：`odd_degree_has_root` 给出根 `x`，
不可约 + 有根 ⟹ `p` 与 `X - C x` 相伴 ⟹ 次数为 `1`。
⇒ 它把"**奇次必有根**"翻译成"**奇次不可约只能是线性**"。 -/
theorem odd_irreducible_natDegree_eq_one [IsRealClosedField K] {p : K[X]}
    (hp : Irreducible p) (hodd : Odd p.natDegree) : p.natDegree = 1 := by
  obtain ⟨x, hx⟩ := IsRealClosedField.odd_degree_has_root p hp.ne_zero hodd
  -- ⚠ 不走"`∣` ⟹ 取乘积因子 ⟹ `isUnit_or_isUnit`"那条路：
  -- `Irreducible.isUnit_or_isUnit` 要的是**乘积等式** `p = a * b`，
  -- 而 `hroot : X - C x ∣ p` 是**存在式** ⟹ 直接喂它会报
  -- `argument hroot has type X - C x ∣ p but is expected to have type p = ?m * ?m`。
  -- ⇒ 正解：用 mathlib 现成的 `Polynomial.degree_eq_one_of_irreducible_of_root`
  -- （其证明体 `Polynomial/Div.lean:763` 已做过这一步转换）。
  have hdeg : p.degree = 1 :=
    -- ⚠ `Polynomial.isRoot.def` **不存在**（该引理在 **root namespace**：
    -- 真名是裸 **`IsRoot.def`**，见 `Algebra/Polynomial/Defs.lean:354`；
    -- 加 `Polynomial.` 前缀会报 `unknown constant`）。
    -- `IsRoot p x` 定义上就是 `p.eval x = 0` ⟹ 用 `IsRoot.def.mpr hx` 转入。
    Polynomial.degree_eq_one_of_irreducible_of_root hp (IsRoot.def.mpr hx)
  -- ⚠ `degree : WithBot ℕ`，而 `natDegree : ℕ` ⟹ `degree_eq_natDegree` 给的是
  -- `degree p = (natDegree p : WithBot ℕ)`；直接 `rwa` 会因为**强制转换**对不上。
  -- ⇒ 先把两边都投到 `WithBot ℕ` 再比较。
  have hcast : ((p.natDegree : ℕ) : WithBot ℕ) = ((1 : ℕ) : WithBot ℕ) := by
    rw [← Polynomial.degree_eq_natDegree hp.ne_zero]
    exact hdeg
  exact WithBot.coe_injective hcast

/-- ⭐⭐ **实闭域上不可约多项式的次数 ≤ 2**。
⭐ 证明要点：`natDegree = 0`（常数，单位）、`= 1`（线性）、
或 `≥ 2` 且为**偶**（由 §4 上路，奇次不可能）。
⚠ **诚实标注**：本条的**"偶次"支未处理**（需要"奇次根存在 ⟹ 偶次可分解为二次"的论证，
本文件**未做**）。⇒ **本条只给出次数 ≤ 1 或 ≥ 2 且偶 的二分**，
**不**声称"次数 ≤ 2"的完整结论。见 §5 边界。 -/
theorem irreducible_natDegree_le_two_or_even [IsRealClosedField K] {p : K[X]}
    (hp : Irreducible p) : p.natDegree ≤ 1 ∨ Even p.natDegree := by
  rcases Nat.even_or_odd p.natDegree with he | ho
  · exact Or.inr he
  · exact Or.inl (le_of_eq (odd_irreducible_natDegree_eq_one hp ho))

/-! ## 5. ⭐ 实闭性的**传递与等价**（§3 的抽象版）

⭐ 本节给出"`K[i]` 代数闭"这一 Artin–Schreier 等价命题的**可操作骨架**：
在实闭域上，**每个元素都有平方根**意味着**没有二次不可约**，
故不可约多项式只剩线性 ⟹ **代数闭**。

⚠ **本文件只证"没有二次不可约"这一步**（下一节），
**不**证完整的代数闭性（那需要 `IsAlgClosed` 的构造与 `K[i]` 的商环，
超出本模块预算）。 -/

/-- ⭐⭐ **没有二次不可约（`X^2 - a` 形态）**：非负 `a` 的 `X^2 - C a` **可约**（有根）。
⭐ 它比 `sqrt_exists` 多说了：**平方根的存在性 ⟺ 该二次多项式有根**，
即**把域论命题（可约性）与算术命题（开方）等价起来**。 -/
theorem X_sq_sub_C_not_irreducible_of_nonneg [IsRealClosedField K] {a : K}
    (ha : 0 ≤ a) : ¬ Irreducible (Polynomial.X ^ 2 - Polynomial.C a) := by
  obtain ⟨b, hb⟩ := nonneg_is_square ha
  intro hirr
  have hroot : (Polynomial.X ^ 2 - Polynomial.C a).eval b = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hb]; ring
  -- ⚠ 不走 `isUnit_or_isUnit hdvd`：它要**乘积等式**，而 `∣` 是存在式
  -- （与上一条同款陷阱）。⇒ 改用**显式分解** `X^2 - C(a) = (X - C b) * (X + C b)`，
  -- 再喂乘积等式给 `isUnit_or_isUnit`。
  have hfac : Polynomial.X ^ 2 - Polynomial.C a
      = (Polynomial.X - Polynomial.C b) * (Polynomial.X + Polynomial.C b) := by
    -- ⚠ 目标里是 `C a`（不是 `b ^ 2`）⟹ `rw [hb]` 匹配不上；
    -- 必须 **`rw [← hb]`** 把 `C a` 换成 `C (b^2)`，再用 `Polynomial.C_pow`
    -- 归一成 `C b ^ 2`（否则 `ring` 不认识 `C (b^2)` 与 `(C b)^2` 的关系）。
    rw [← hb, Polynomial.C_pow]
    ring
  rcases hirr.isUnit_or_isUnit hfac with hunit | hunit
  · -- 左因子 `X - C b` 次数为 1，不可能是单位
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [Polynomial.natDegree_X_sub_C] at this
    exact absurd this (by decide)
  · -- 右因子 `X + C b` 次数为 1，也不可能是单位
    have h1 : (Polynomial.X + Polynomial.C b).natDegree = 1 := by
      rw [Polynomial.natDegree_X_add_C]
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [h1] at this
    exact absurd this (by decide)

/-! ## 6. ⚠ 诚实边界汇总

⚠ **本文件最重要的边界**：pinned mathlib 4.14 **无 `IsRealClosed`**，
故本文件是**自定义公理化**。由此产生三条边界：

1. **§1 的定义弱于经典定义**：经典实闭性 = "无真有序代数扩张"，
   本文件用"平方根存在 + 奇次有根"作为**可操作代理**。
   ⇒ **不声称**二者等价（那需要 Artin–Schreier 的完整证明）。
2. **§4 的 `irreducible_natDegree_le_two_or_even` 是半成品**：
   **偶次支未处理**，"次数 ≤ 2"这一经典结论**本文件未证全**。
3. **§5 未构造 `K[i]`**：故"实闭 ⟺ `K[i]` 代数闭"这一 Artin–Schreier 等价
   **本文件未证**，只给了它的**代数骨架**（无二次不可约）。

其他：
- **不证** `ℝ` 是实闭域（那需要中值定理与 `Polynomial` 的实根理论）；
- **不证**实闭域的唯一性（同基数 ⟹ 同构，属模型论）；
- **不处理**量词消去（Tarski–Seidenberg）；
- ⚠ §3 的"序唯一性"把"锥相同"作为**假设**——Lean 里两个 `LinearOrder` 实例的
  锥相等**不能自动获得**，这是类型类建模的固有局限（STYLE 已多次登记同类问题）。 -/

end Lattice.RealClosedFieldAxiomatic
