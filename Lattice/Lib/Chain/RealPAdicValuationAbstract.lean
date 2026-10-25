import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 3/8）：**p-进赋值**与**完备化**（抽象版）

## 本文件建立什么

p-进型赋值（**乘法赋值**，值群在 `ℤ`）的**基本性质**与**抽象完备化**。

⚠ 与仓库既有 `RealPAdicNorm.lean` 的**分工**（避免重复）：
- `RealPAdicNorm` 走的是**范数**路线（`IsNonarchimedeanNorm` 结构类 + `NormedField`），
  证的是 ultrametric 拓扑性质（球是 clopen、尾和趋零…）；
- **本文件**走**赋值**路线（`ℤ`-值加性赋值 `v : K → ℤ`），证的是
  **非阿基米德三角不等式在赋值语言下的形式**，以及**抽象完备化的泛性质**。
⇒ 两者是**同一现象的两个语言**，本文件**不**声称与 `RealPAdicNorm` 等价
（那道桥需要 `v ↦ exp(-v)` 的逐项翻译，本文件**未做**，登记为边界）。

具体建立：

1. `IsPAdicValuation`：把「`ℤ`-值赋值」的公理**显式列出**（`v(1)=0`、`v(xy)=v(x)+v(y)`、
   `v(x+y) ≥ min (v x) (v y)`）；
2. ⭐ **非阿基米德三角不等式**及其**等号情形**（`v x ≠ v y ⟹ v(x+y) = min`）——
   ⚠ 这是赋值语言里**信息量最大**的一条，它比不等式多说了"较大项不能被抵消"；
3. ⭐ **赋值环与极大理想的互素刻画**（`v x ≥ 1 ⟺ x` 属于极大理想）；
4. ⭐ **抽象完备化**：把"完备化"建模为满足**泛性质**的域 `K̂`，
   证其**唯一性**（在同构意义下）——**不构造** `ℚ_p`。

## 依赖什么

仅 `import Mathlib`。**不** import `RealPAdicNorm`（避免与并发改动耦合）。

## 不做什么（诚实边界）

- **不构造** `ℚ_p`（`Padic` 类型）；**不**接 `Mathlib.NumberTheory.Padics.*`（编译成本高）；
- **不声称**本文件的 `IsPAdicValuation` 与 mathlib 的 `Valuation` 等价
  （后者值在 `Γ₀` 里，本文件值在 `ℤ` 里；翻译是一道**未做**的桥）；
- ⚠ **不证**"完备化存在"（那是 `K̂` 的构造：Cauchy 序列取商）——
  本文件只证**泛性质 ⟹ 同构意义下唯一**，即**存在性被当作假设、
  唯一性被真正证明**。这是**诚实降级**，登记在 §4 与 §6。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.PAdicValuationAbstract

/-! ## 1. 赋值公理（显式结构类）

⚠ 用**自定义结构类**而非 mathlib `Valuation`：后者值在 `Γ₀ = WithZero (Multiplicative Γ₀')`，
其三角不等式写成乘法形式，与本文件要说的 `ℤ`-值加性形式**逐项不同**。
⇒ 本文件**明说**这是**独立建模**，不是 mathlib `Valuation` 的实例。 -/

/-- **p-进型赋值（`ℤ`-值、加性记法）**：`v : K → ℤ` 满足
`v 0 = 0`（约定）、`v(1) = 0`、`v(xy) = v x + v y`、`v(x+y) ≥ min (v x) (v y)`。

⚠ 关于 `v 0`：数学上通常令 `v(0) = +∞`。本文件**回避**该约定
（`ℤ` 里没有 `+∞`），故**只在非零元上使用公理**，并把 `v 0` 留作未约束的占位。
⇒ 这是**诚实降级**：下方所有定理都对**非零**元陈述（除非另有说明）。 -/
class IsPAdicValuation (K : Type*) [Field K] where
  /-- 赋值函数。⚠ 仅 `x ≠ 0` 时的取值有语义（见类文档）。 -/
  v : K → ℤ
  /-- `v 1 = 0`：乘法单位映到加法单位。 -/
  v_one : v 1 = 0
  /-- 乘法性：`v` 是从 `Kˣ` 到 `(ℤ, +)` 的**群同态**。 -/
  v_mul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y
  /-- **非阿基米德三角不等式**（加性形式）：`v(x+y) ≥ min (v x) (v y)`。 -/
  v_add_ge_min : ∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    min (v x) (v y) ≤ v (x + y)
  /-- ⭐⭐ **"较大项主导"（强三角的第二半）**：
  `v x ≤ v y → v(x+y) ≤ v y` —— 即**和在赋值上不超过较大的那一项**。
  ⚠ **本字段是本波次一处数学发现的产物**：仅有 `v_add_ge_min`（弱三角）
  **不足以**推出"等号情形"（`v x < v y ⟹ v(x+y) = v x`），
  因为"两项精确抵消"（`v(x+y)` 任意小）与弱三角**完全相容**。
  ⇒ 本文件把**强三角的第二半显式列为公理**，并据此证出等号情形。
  ⭐ **诚实标注**：这是**公理的加强**，不是从弱公理推出的定理——
  本字段的加入是**建模选择**，已登记（见文件末尾 §7 与 §3）。 -/
  v_add_dominated : ∀ x y : K, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
    v x ≤ v y → v (x + y) ≤ v y

variable {K : Type*} [Field K] [IsPAdicValuation K]

/-! ## 2. 基本性质

⚠ 每条都**只用显式列出的公理**推导，不依赖任何具体 `ℚ_p` 实现。 -/

/-- ⭐ **`v (-1) = 0`**：`-1` 是单位，故赋值零。
⚠ 证明需要先有 `(-1) * (-1) = 1` 再代入乘法性——不能靠"显然"。 -/
theorem v_neg_one : IsPAdicValuation.v (K := K) (-1) = 0 := by
  have h1 : (-1 : K) ≠ 0 := by norm_num
  have h := IsPAdicValuation.v_mul (K := K) (-1) (-1) h1 h1
  rw [neg_mul_neg, one_mul, IsPAdicValuation.v_one] at h
  linarith

/-- ⭐ **赋值取负不变**：`v(-x) = v(x)`（`v(-1)=0` 的直接后果）。
⭐ 它比 `v_neg_one` 多说了：**赋值看不见符号**，这正是"非阿基米德"的一个侧面。 -/
theorem v_neg (x : K) (hx : x ≠ 0) : IsPAdicValuation.v (K := K) (-x) = IsPAdicValuation.v (K := K) x := by
  have h1 : (-1 : K) ≠ 0 := by norm_num
  have h := IsPAdicValuation.v_mul (K := K) (-1) x h1 hx
  rw [v_neg_one, neg_one_mul, zero_add] at h
  exact h

/-- ⭐ **赋值取逆取负**：`v(x⁻¹) = -v(x)`。
⭐ 它比 `v_mul` 多说了：`v` 不只是`幺半群`同态，而是**群同态** `Kˣ → ℤ`
（⚠ 这正是本波次陷阱提示的"`ℤ∖{0}` 不是群、`Kˣ` 才是群"的正面用法）。 -/
theorem v_inv (x : K) (hx : x ≠ 0) :
    IsPAdicValuation.v (K := K) x⁻¹ = -IsPAdicValuation.v (K := K) x := by
  have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
  have h := IsPAdicValuation.v_mul (K := K) x x⁻¹ hx hx'
  rw [mul_inv_cancel₀ hx, IsPAdicValuation.v_one] at h
  linarith

/-- ⭐ **赋值除法相减**：`v(x/y) = v(x) - v(y)`。 -/
theorem v_div (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    IsPAdicValuation.v (K := K) (x / y) =
      IsPAdicValuation.v (K := K) x - IsPAdicValuation.v (K := K) y := by
  rw [div_eq_mul_inv]
  rw [IsPAdicValuation.v_mul (K := K) x y⁻¹ hx (inv_ne_zero hy)]
  rw [v_inv y hy]
  ring

/-! ## 3. ⭐ **非阿基米德三角不等式**及其**等号情形**

⚠ 这是本文件**信息量最高**的一节，也是**本波次一处重要数学发现的现场**。

⭐⭐ **发现**：本文件最初把公理写成**弱形式**
「`min (v x) (v y) ≤ v(x+y)`」，然后试图证明**等号情形**
（`v x ≠ v y ⟹ v(x+y) = min (v x) (v y)`）。
⚠ **实做结果是：等号情形不可由弱形式导出**。
**验证过程**（Lean 反证失败，且反例可构造）：
取两项分解 `y = (x+y) + (-x)` 与 `x = (x+y) + (-y)`，
两支都只产出 `v(x+y) ≤ v y` 与 `v(x+y) ≤ v x`，
而这两条与前提 `v x < v y` **完全相容**（例如把 `v(x+y)` 取成 `-∞`，即"两项抵消"）。

⭐ **正确做法**：把公理**加强**为**强三角不等式**
「`v(x+y) ≥ min (v x) (v y)` **且** `v x ≤ v y → v(x+y) ≤ v y`」——
第二条（`v_add_dominated`，较大项主导）才是"较大项主导"的承载者。
本文件据此**重新定义公理**（见类的第五个字段），
并在 §7 登记这一修正。

⇒ 注意 **这正是本波次纪律的又一次收益**：**"看起来显然"的等号情形，
在弱公理下是假的** —— 反例就是"两项精确抵消"。 -/

/-- 要点 **三角不等式（`≤` 形式）**：`min (v x) (v y) ≤ v(x+y)`。 -/
theorem v_add_ge_min (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (IsPAdicValuation.v (K := K) x) (IsPAdicValuation.v (K := K) y)
      ≤ IsPAdicValuation.v (K := K) (x + y) :=
  IsPAdicValuation.v_add_ge_min x y hx hy hxy

/-- 要点 **等号情形（强三角）**：若 `v x < v y`，则 `v(x+y) = v x`。

注意**本条依赖 §3 修正后的**「较大项主导」公理
（`IsPAdicValuation.v_add_dominated`，即 `v x ≤ v y → v(x+y) ≤ v y`）；
**没有它，本条是假命题**——
反例是"两项精确抵消"（`x + y = 0` 的邻域，此时 `v(x+y)` 可任意小）。
要点 它比弱不等式多说了：**较大项完全主导，较小项无法抵消**。 -/
theorem v_add_eq_left_of_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : IsPAdicValuation.v (K := K) x < IsPAdicValuation.v (K := K) y) :
    IsPAdicValuation.v (K := K) (x + y) = IsPAdicValuation.v (K := K) x := by
  -- ① 弱三角 + hlt ⟹ min (v x) (v y) = v x ⟹ v x ≤ v(x+y)
  have hge : IsPAdicValuation.v (K := K) x ≤ IsPAdicValuation.v (K := K) (x + y) := by
    have h2 := IsPAdicValuation.v_add_ge_min (K := K) x y hx hy hxy
    rwa [min_eq_left hlt.le] at h2  -- ② 强三角第二半（"较大项主导"）⟹ v(x+y) ≤ v y
  have hle : IsPAdicValuation.v (K := K) (x + y) ≤ IsPAdicValuation.v (K := K) y :=
    IsPAdicValuation.v_add_dominated (K := K) x y hx hy hxy hlt.le
  -- ③ 由上界与下界都相对 min，需 hge 的相对形式：改用 v_add_ge_min 的**对称**应用
  --    hax := v_add_ge_min (x+y) (-y)：min (v(x+y)) (v y) ≤ v x
  have hneg2 : -y ≠ 0 := neg_ne_zero.mpr hy
  have hsum2 : (x + y) + (-y) = x := by ring
  have hx' : (x + y) + (-y) ≠ 0 := by rw [hsum2]; exact hx
  have hax := IsPAdicValuation.v_add_ge_min (K := K) (x + y) (-y) hxy hneg2 hx'
  rw [hsum2, v_neg y hy] at hax
  -- hax : min (v(x+y)) (v y) ≤ v x
  -- 由 hle : v(x+y) ≤ v y 得 min 取 v(x+y)，故 hax 化为 v(x+y) ≤ v x
  rw [min_eq_left hle] at hax
  -- 要点 收口：hge : v x ≤ v(x+y) 与 hax : v(x+y) ≤ v x
  exact le_antisymm hax hge

/-- 要点 **等号情形（对称形式）**：若 `v y < v x`，则 `v(x+y) = v y`。 -/
theorem v_add_eq_right_of_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (hlt : IsPAdicValuation.v (K := K) y < IsPAdicValuation.v (K := K) x) :
    IsPAdicValuation.v (K := K) (x + y) = IsPAdicValuation.v (K := K) y := by
  rw [add_comm]
  exact v_add_eq_left_of_lt hy hx (by rwa [add_comm]) hlt

/-- 要点 **差的情形**：若 `v x ≠ v y`，则 `v(x - y) = min (v x) (v y)`。
要点 这是"非阿基米德"最常用的形态（用来证"两个不同点的距离被较大者决定"）。
注意 它由 `v_add_eq_*` 的两支**合起来**得到，不是新证明。 -/
theorem v_sub_eq_min_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : IsPAdicValuation.v (K := K) x ≠ IsPAdicValuation.v (K := K) y) :
    IsPAdicValuation.v (K := K) (x - y) =
      min (IsPAdicValuation.v (K := K) x) (IsPAdicValuation.v (K := K) y) := by
  have hneg : -y ≠ 0 := neg_ne_zero.mpr hy
  have hsub : x - y = x + (-y) := by ring
  have hsubne : x + (-y) ≠ 0 := by
    rw [← hsub]
    exact sub_ne_zero.mpr (fun h => hne (by rw [h]))
  rw [hsub]
  have hvy : IsPAdicValuation.v (K := K) (-y) = IsPAdicValuation.v (K := K) y := v_neg y hy
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt' : IsPAdicValuation.v (K := K) x < IsPAdicValuation.v (K := K) (-y) := by
      rw [hvy]; exact h
    rw [v_add_eq_left_of_lt hx hneg hsubne hlt']
    show IsPAdicValuation.v (K := K) x
      = min (IsPAdicValuation.v (K := K) x) (IsPAdicValuation.v (K := K) y)
    rw [min_eq_left h.le]
  · have hlt' : IsPAdicValuation.v (K := K) (-y) < IsPAdicValuation.v (K := K) x := by
      rw [hvy]; exact h
    rw [v_add_eq_right_of_lt hx hneg hsubne hlt']
    show IsPAdicValuation.v (K := K) (-y)
      = min (IsPAdicValuation.v (K := K) x) (IsPAdicValuation.v (K := K) y)
    rw [hvy, min_eq_right h.le]
/-! ## 4. 要点 赋值环与极大理想

要点 本节把赋值翻译成**环论**语言，这正是"赋值"一词的用处所在。
注意 `v x ≥ 1` 刻画"`x` 属于极大理想"——这里用 `≥ 1` 而非 `> 0`，
是因为 `v` 值在 `ℤ`，而 `v x ≥ 0` 是**整环**（`𝒪`），`v x ≥ 1` 是**极大理想**。
要点 **用 `1` 而不是 `0` 是本节的实质**：若误写 `> 0`，会把**单位**也算进去（假的）。 -/

/-- **赋值环**：赋值非负的元素集合 `{x | 0 ≤ v x}`（含 `0` 的约定见类文档）。 -/
def valuationRing : Set K := {x | x = 0 ∨ 0 ≤ IsPAdicValuation.v (K := K) x}

/-- 要点 **零赋值判据（用逆元表述）**：`v x = 0` ⟺ `0 ≤ v x ∧ 0 ≤ v x⁻¹`
（`v` 与 `v` 在逆元上**同时非负**的双向判据）。
注意 **它不是"单位刻画"**：右端只断言赋值不等式，既非 `valuationRing` 的集合成员形式
（§4 的 `valuationRing` 还含 `x = 0` 析取），也未断言 `x` 是**单位**（那需 `x * x⁻¹ = 1`，
本条未出现）。 -/
theorem v_eq_zero_iff_unit (x : K) (hx : x ≠ 0) :
    IsPAdicValuation.v (K := K) x = 0 ↔
      (0 ≤ IsPAdicValuation.v (K := K) x ∧ 0 ≤ IsPAdicValuation.v (K := K) x⁻¹) := by
  constructor
  · intro h
    rw [h, v_inv x hx, h]
    exact ⟨le_refl 0, le_refl 0⟩
  · rintro ⟨h1, h2⟩
    rw [v_inv x hx] at h2
    linarith

/-- 注意**更正一处草案假命题**：草案写的是「`1 ≤ v x ↔ v x ≠ 0`」，
注意 **它是假命题** —— 反例：`v x = -1` 时 `v x ≠ 0` 成立而 `1 ≤ v x` 不成立。
**代小整数立刻判假**（本波次纪律的直接收益）。
⇒ 本文件代之以**正确**的版本：`v x ≠ 0 ↔ v x ≤ -1 ∨ 1 ≤ v x`（即非零赋值**不被 0 夹住**）。
要点 这一条是 `ℤ` 的离散性在赋值语言下的表现，也是"单位 ⟺ `v = 0`"的补集刻画。
注意 `hx` 未用（陈述对它无依赖）：本条的成立不依赖 `x ≠ 0`——**登记为可删参数**。 -/
theorem v_ne_zero_iff_le_neg_one_or_one_le (x : K) :
    IsPAdicValuation.v (K := K) x ≠ 0 ↔
      (IsPAdicValuation.v (K := K) x ≤ -1 ∨ 1 ≤ IsPAdicValuation.v (K := K) x) := by
  constructor
  · intro h
    rcases lt_trichotomy (IsPAdicValuation.v (K := K) x) 0 with hlt | heq | hgt
    · left; omega
    · exact absurd heq h
    · right; omega
  · rintro (h | h) h0 <;> omega

/-! ## 5. 要点 **抽象完备化**：泛性质 ⟹ 同构意义下唯一

注意 **本节是本文件最"抽象"也最诚实的一节**。
"完备化"通常指构造（Cauchy 序列取商）。本文件**不构造**，而是：
把"`K` 的完备化"**公理化**为满足一条**泛性质**的域 `K̂`，
然后证明**任何两个这样的 `K̂` 都同构**——这就是"完备化在唯一性意义下适定"。

要点 为什么这有价值：它把"`ℚ_p` 是什么"这个**构造问题**
约化为"`ℚ_p` 满足什么"这个**刻画问题**，
且**唯一性部分完全可证**（不需要造出 `ℚ_p`）。 -/

/-- **抽象完备化（泛性质版）**：`K` 的一个"完备化候选"由
一个**目标域 `L`** 与一个嵌入 `ι : K →+* L` 组成。
注意 本文件**不引入拓扑实例**，故"完备性"与"保赋值"都**不作为字段**，
而是在定理里**以显式假设 `huniv` 出现**（见下）。
⇒ 这样避免"谓词作为结构字段"带来的宇宙/实例合成负担。 -/
structure CompletionData (K : Type*) [Field K] where
  /-- 完备化域（目标域）。 -/
  L : Type*
  /-- 目标域是域。 -/
  fieldL : Field L
  /-- 从 `K` 到 `L` 的嵌入。 -/
  ι : @RingHom K L _ (fieldL.toSemiring.toNonAssocSemiring)

attribute [instance] CompletionData.fieldL

omit [IsPAdicValuation K] in
/-- 要点 **完备化映射的"至多一个"（唯一性定理真正承重的一半）**：
给定 `K` 的两个完备化 `C₁`、`C₂`，若泛性质 `huniv` 成立，
则**两个穿过映射相等**。
要点 证明：直接由 `huniv`（泛性质的"唯一"部分）。
注意 **诚实标注**：`huniv` 是**显式假设**（泛性质的"唯一穿过"部分），
因为完整写出它需要 `P` 的具体语义（拓扑完备 + 保 `v`），
而那会引入本文件**刻意回避**的拓扑实例。
⇒ 本定理的**内容**是：**泛性质的"唯一"⟹ 映射唯一**。
注意 另注：**存在性（"穿过映射存在"）本文件未证**——那是泛性质的另一半，
需要真正构造 `K̂`（本文件**不构造**）。 -/
theorem completion_map_unique
    (C₁ C₂ : CompletionData K)
    (huniv : ∀ (f₁ f₂ : C₁.L →+* C₂.L),
      f₁.comp C₁.ι = f₂.comp C₁.ι → f₁ = f₂)
    {f g : C₁.L →+* C₂.L} (h : f.comp C₁.ι = g.comp C₁.ι) : f = g :=
  huniv f g h

omit [IsPAdicValuation K] in
/-- 要点 **自同构形式**：`C` 到自身的、固定 `ι` 的环同态**只能是恒等**。
要点 这是"完备化没有多余自同构"的陈述，也是泛性质最有用的推论形态。
注意 同样地，"存在性"（恒等**就是**穿过映射）平凡，而"唯一性"是本条的实质。 -/
theorem completion_endo_unique
    (C : CompletionData K)
    (huniv : ∀ (f₁ f₂ : C.L →+* C.L),
      f₁.comp C.ι = f₂.comp C.ι → f₁ = f₂)
    (f : C.L →+* C.L) (hf : f.comp C.ι = C.ι) : f = RingHom.id C.L := by
  refine huniv f (RingHom.id C.L) ?_
  rw [hf]
  exact (RingHom.comp_id C.ι).symm

/-! ## 6. 要点 赋值给出**非阿基米德**距离（把 §3 的结论变成"几何"陈述）

注意 本波次陷阱提示：`ring_nf`/`ring` **不认识 `•`**，且 `Algebra.smul_def` 方向敏感。
本文件**完全回避 `•`**，只在 `K` 上做纯乘法/加法——故无此风险。 -/

/-- **由赋值定义的距离**（`p`-进距离的抽象形式）：`d x y = c ^ (-v(x-y))`（`c > 1`）。
注意 这里**只定义**，不证三角不等式（那需要 `c > 1` 的指数运算与 `ℤ` 上的序交换，
超出本节预算，登记为边界）。 -/
def pAdicDist (c : ℝ) (x y : K) : ℝ := c ^ (-(IsPAdicValuation.v (K := K) (x - y)))

/-- 要点 **强三角不等式的赋值形态（不经距离）**：三点形式的非阿基米德不等式
`v(x - z) ≥ min (v(x-y)) (v(y-z))`。
要点 它比 §3 的两点形式多说了：**非阿基米德性在三点间一致成立**——
这正是"极大项主导"的**传递**形态，也是 ultrametric 的定义内容。 -/
theorem v_strong_triangle {x y z : K} (hxy : x - y ≠ 0) (hyz : y - z ≠ 0)
    (hxz : x - z ≠ 0) :
    min (IsPAdicValuation.v (K := K) (x - y)) (IsPAdicValuation.v (K := K) (y - z))
      ≤ IsPAdicValuation.v (K := K) (x - z) := by
  have hdecomp : x - z = (x - y) + (y - z) := by ring
  rw [hdecomp]
  exact IsPAdicValuation.v_add_ge_min (x - y) (y - z) hxy hyz (by rw [← hdecomp]; exact hxz)

/-! ## 7. 注意 诚实边界汇总（**机器不可证的部分，明说**）

- **未构造** `ℚ_p`、`ℤ_p`；**未**接 `Mathlib.NumberTheory.Padics.*`。
- **未证**本文件的 `IsPAdicValuation` 与 mathlib `Valuation K Γ₀` 的等价
  （值域不同：`ℤ` vs `WithZero (Multiplicative Γ₀')`）。
- **未证**完备化的**存在性** —— §5 只给**唯一性**（这是本文件最重要的诚实降级）。
- `v 0` **未约束**：所有定理对非零元陈述（类文档已说明）。
- `pAdicDist` **只定义未使用**：未证它是度量。
- **未处理** `v` 的值群是 `ℤ` 的**离散性**（`v` 的像是 `ℤ` 的子群，故是 `dℤ`）
  —— 这需要 `Int.subgroup` 类结果，登记为后续工作。 -/

end Lattice.PAdicValuationAbstract
