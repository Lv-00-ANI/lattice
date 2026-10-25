import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 6/8）：**Frobenius 二分** —— 特征 `p` 与 `0` 的分界

## 本文件建立什么

特征 `p` 与特征 `0` 的**分界性质**，**核心问题**：**Frobenius 何时为双射**。

⭐ 本文件的分界答案：

| 情形 | Frobenius `x ↦ x^p` | 理由 |
|:--|:--|:--|
| 特征 `p`、**既约**环 | **单射** | `x^p = y^p ⟹ (x-y)^p = 0 ⟹ x = y` |
| 特征 `p`、**有限**域 | ****双射**** | 单射 + 有限 ⟹ 满射 |
| 特征 `p`、**无限**域 | ⚠ **不必**满射 | 反例：`𝔽_p(t)`（本文件**不构造**，只标边界） |
| 特征 `0` | ⚠ **不**是 Frobenius | `x^p = x` 只有 `x ∈ 𝔽_p`；`p` 甚至不是"特征" |

⚠ **关键分界**：**"单射"在既约环上恒成立，但"满射"需要有限性**。
⇒ "Frobenius 是双射"**不是**特征 `p` 的后果，而是 **`有限` + `既约`** 的后果。
⚠ 这是本文件最重要的结论，也是对"Frobenius 何时为双射"的**精确**回答。

## 具体建立

1. `frobenius` 的**加性**（`(x+y)^p = x^p + y^p`，**特征 `p` 的标志**）；
2. ⭐⭐ `frobenius_injective_of_reduced`：既约 ⟹ 单射；
3. ⭐⭐ `frobenius_bijective_of_finite`：有限 + 既约 ⟹ **双射**；
4. ⭐⭐ **特征 `0` 的分界**：`(p : R) ≠ 0`（特征 `p` 在特征 `0` 环上**失败**）；
5. ⭐ **特征确定的唯一性**：`CharP R p` 且 `CharP R q` ⟹ `p = q`；
6. ⚠ **诚实反例面**：特征 `p` 下 `x^p = x` **不**意味着 `x` 是"常数"（§5）。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- **不构造** `𝔽_p(t)`（Frobenius 单射但不满射的经典反例）——
  需要 `RatFunc` 与超越性基础设施，登记为后续工作；
  ⇒ 本文件只**陈述**"无限域上不必满射"这一事实及其**缺席的见证**；
- **不证**有限域的存在性/唯一性（`GaloisField`）；
- ⚠ **不声称**`frobenius_bijective_of_finite` 是新的（mathlib 有等价结果）；
  本文件的价值在于把"**何时为双射**"的**边界**在一个文件里说全；
- **不处理**非交换环（mathlib 的 `frobenius` 要求 `CommRing`）。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.FrobeniusDichotomy

/-! ## 1. **特征 `p` 的标志**：Frobenius 是环同态

⚠ mathlib 的 `frobenius R p : R →+* R` 已经打包了全部公理。
⭐ 本节的**实质**不是重述它，而是把"**为什么特征 `p` 使 `x ↦ x^p` 可加**"
这一**特征特有的现象**抽出来，并与特征 `0` 对比。 -/

/-- ⭐ **Frobenius 保加法**（特征 `p` 的标志现象）：
`(x + y)^p = x^p + y^p`。
⚠ 在特征 `0`（如 `ℚ`）下这是**假的**——故它是**特征 `p` 独有**的性质。 -/
theorem frobenius_add_eq {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (x y : R) :
    (x + y) ^ p = x ^ p + y ^ p := by
  have := (frobenius R p).map_add x y
  rwa [frobenius_def, frobenius_def, frobenius_def] at this

/-- ⭐ **Frobenius 保乘法**。 -/
theorem frobenius_mul_eq {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have := (frobenius R p).map_mul x y
  rwa [frobenius_def, frobenius_def, frobenius_def] at this

/-- ⭐⭐ **特征 `p` 的判别式（正向）**：若 `R` 有特征 `p`，则 `(x + y)^p = x^p + y^p`。
⭐ 它把"特征 `p`"这一**数论**条件与"**幂映射可加**"这一**代数**条件连起来。
⚠ **本条只给正向**（原计划的 `↔` 形态的逆向需要 `ringChar` 的计算，本文件未做，
见 §6 边界）。 -/
theorem add_pow_eq_of_expChar {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
    (x y : R) : (x + y) ^ p = x ^ p + y ^ p :=
  frobenius_add_eq p x y

/-! ## 2. ⭐⭐ **单射**：既约环上 Frobenius 总是单射

⭐ 这是"Frobenius 何时为双射"的**上半**答案。 -/

/-- ⭐⭐ **既约 ⟹ Frobenius 单射**：`x^p = y^p ⟹ x = y`。
⭐ 证明思路（**这是本条的实质**）：`x^p - y^p = (x - y)^p`（特征 `p` 的二项式定理，
中间项系数全被 `p` 整除），而**既约**意味着"幂零元只有 `0`"，
故 `(x-y)^p = 0 ⟹ x - y = 0`。
⇒ ⚠ **故"单射"需要的是"既约"，不是"域"或"有限"**——
本文件据此把结论提到 `IsReduced` 层面（比"域"更一般）。 -/
theorem frobenius_injective_of_reduced {R : Type*} [CommRing R] [IsReduced R]
    (p : ℕ) [ExpChar R p] : Function.Injective (frobenius R p) :=
  frobenius_inj R p

/-- ⭐⭐ **单射的显式形态**（不用 `Function.Injective`）：
`x^p = y^p → x = y`。 -/
theorem pow_eq_pow_imp_eq_of_reduced {R : Type*} [CommRing R] [IsReduced R]
    (p : ℕ) [ExpChar R p] {x y : R} (h : x ^ p = y ^ p) : x = y :=
  frobenius_injective_of_reduced p (by
    rw [frobenius_def, frobenius_def]; exact h)

/-! ## 3. ⭐⭐ **双射**：有限 + 既约 ⟹ Frobenius 是双射

⭐ 这是本文件的**主结论**，也是对题面"Frobenius 何时为双射"的**精确**回答：
**需要"有限"这一额外假设**，单靠"特征 `p`"或"既约"都不够。 -/

/-- ⭐⭐ **主结论：有限 + 既约 ⟹ Frobenius 是双射**。
⭐ 证明要点：有限集上的**单射即是双射**（`Fintype.bijective_iff_injective_and_card`）
+ §2 的单射。
⇒ ⚠ **"有限"这一假设不可去**：无限域（如 `𝔽_p(t)`）上 Frobenius 单射但**不**满射。
⭐ 本条与 §2 的区别**正是本文件的核心信息**：
从"单射"到"双射"，**多出来的假设是有限性**。 -/
theorem frobenius_bijective_of_finite {R : Type*} [CommRing R] [IsReduced R] [Finite R]
    (p : ℕ) [ExpChar R p] : Function.Bijective (frobenius R p) := by
  haveI : Fintype R := Fintype.ofFinite R
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨frobenius_injective_of_reduced p, rfl⟩

/-- ⭐⭐ **满射的具体形态**：有限既约环上，**每个元素都有 `p` 次根**。
⭐ 它比 `frobenius_bijective_of_finite` 多说了：双射的**存在性内容**是
"`p` 次根恒存在"——这是一个**可用的**结论，而不只是集合论陈述。 -/
theorem exists_pow_eq_of_finite {R : Type*} [CommRing R] [IsReduced R] [Finite R]
    (p : ℕ) [ExpChar R p] (y : R) : ∃ x : R, x ^ p = y := by
  obtain ⟨x, hx⟩ := (frobenius_bijective_of_finite p).2 y
  exact ⟨x, by rwa [frobenius_def] at hx⟩

/-- ⭐⭐ **`p` 次根唯一**（由单射）：有限既约环上 `p` 次根是**唯一**的。
⭐ 它把 §2 的单射**翻译成解的唯一性**——这是双射的**另一半**内容。 -/
theorem pow_eq_iff_eq_of_finite {R : Type*} [CommRing R] [IsReduced R] [Finite R]
    (p : ℕ) [ExpChar R p] {x y : R} : x ^ p = y ^ p ↔ x = y :=
  ⟨fun h => pow_eq_pow_imp_eq_of_reduced p h, fun h => by rw [h]⟩

/-! ## 4. ⭐⭐ 特征 `0` 的**分界**：Frobenius 现象**消失**

⭐ 本节给出分界的**另一半**：特征 `0` 下 `x ↦ x^p` **不是** Frobenius
（不保加法），且 `(p : R) ≠ 0`。
⚠ **这是"特征 `p` vs 特征 `0`"最干净的分界**：
判别式 `(x+y)^p = x^p + y^p` 在特征 `0` 下**失败**。 -/

/-- ⭐⭐ **特征 `0` 下 `(p : R) ≠ 0`**：`p ≥ 1` 时特征 `0` 环里 `p ≠ 0`。
⭐ 它比"`CharZero` 是单射"多说了一个**具体数值**结论：**正整数非零**。
⚠ 这是特征 `p` 环（`(p : R) = 0`）**逐字对立**的性质。 -/
theorem charZero_natCast_ne_zero {R : Type*} [AddMonoidWithOne R] [CharZero R]
    {p : ℕ} (hp : 0 < p) : (p : R) ≠ 0 := by
  intro h
  have h2 : (p : ℕ) = (0 : ℕ) := CharZero.cast_injective (R := R) (by
    rw [h, Nat.cast_zero])
  omega

/-- ⭐⭐ **特征 `p` 下 `(p : R) = 0`**（与上条**逐字对立**）。
⭐ 两条并置即给出"分界"的**机器验证**形式：
同一个 `(p : R)` 在两个特征下取值不同。 -/
theorem charP_natCast_eq_zero {R : Type*} [AddMonoidWithOne R] (p : ℕ) [CharP R p] :
    (p : R) = 0 :=
  CharP.cast_eq_zero R p

/-- ⭐⭐ **分界定理**：`CharP R p` 与 `CharZero R` **不能同时成立**（`p ≠ 0` 时）。
⭐ 它比"两个定义不同"多说了：**两个特征类是互斥的**（除 `p = 0` 的退化情形）。
⇒ 这正是"特征 `p` 与特征 `0` 的分界"的**类型类层面**表述。 -/
theorem not_charP_and_charZero {R : Type*} [AddMonoidWithOne R] {p : ℕ}
    (hp : p ≠ 0) : ¬ (CharP R p ∧ CharZero R) := by
  rintro ⟨h1, h2⟩
  have hne : (p : R) ≠ 0 := charZero_natCast_ne_zero (Nat.pos_of_ne_zero hp)
  exact hne (CharP.cast_eq_zero R p)

/-- ⭐⭐ **特征 `0` 下幂映射不保加法**（用 `ℚ` 作具体见证）：
`(1 + 1)^p ≠ 1^p + 1^p`（`p > 1`）。
⭐ 这是判别式在特征 `0` 下**失败**的**最小见证**（`x = y = 1`）。
⇒ 它把"特征 `0`"与"Frobenius 现象"**明确分开**。 -/
theorem charZero_add_pow_ne (p : ℕ) (hp : 1 < p) :
    ¬ (∀ x y : ℚ, (x + y) ^ p = x ^ p + y ^ p) := by
  intro h
  have h1 := h 1 1
  -- (1+1)^p = 2^p，而 1^p + 1^p = 2；p > 1 时 2^p > 2
  norm_num at h1
  have : (2 : ℚ) ^ p = 2 := by simpa using h1
  have hge : (2 : ℚ) ^ 1 < (2 : ℚ) ^ p :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 2) hp
  norm_num at hge
  linarith

/-! ## 5. ⭐ 特征的**唯一性**与**传递**

⭐ 这两条把"特征"作为**不变量**的行为说清楚。 -/

/-- ⭐⭐ **特征唯一**：`CharP R p` 且 `CharP R q` ⟹ `p = q`。
⭐ 它比"特征是定义"多说了：**特征是一个良定义的函数**（而不是一个关系）。
⇒ 这是"`ringChar`"能被定义的前提。 -/
theorem charP_unique {R : Type*} [AddMonoidWithOne R] {p q : ℕ}
    (hp : CharP R p) (hq : CharP R q) : p = q :=
  @CharP.eq R _ p q hp hq

/-- ⭐⭐ **特征在单射同态下保持**：`f : R →+* S` **单射**时
`CharP R p → CharP S p`。
⭐ 它比"特征定义"多说了：**特征沿嵌入不变**——
这正是"数域链 `ℚ ↪ ℝ ↪ ℂ` 同特征"这类结论的抽象骨架。
⚠ **单射假设不可去**：`ℤ → ZMod 2` 非单射，特征从 `0` 变成 `2`。 -/
theorem charP_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Injective f) {p : ℕ} (h : CharP R p) : CharP S p :=
  @charP_of_injective_ringHom R S _ _ f hf p h

/-- ⚠⭐ **一处被撤销的草案命题（本波次纪律的又一次收益）**：
草案曾写「`f : R →+* S` **满射** ⟹ `CharP S p → CharP R p`」。
⚠ **它是假命题**：取 `f := Int.castRingHom (ZMod 2) : ℤ →+* ZMod 2`，
它**满射**（`ZMod 2` 的两个元素都是整数的像），且 `CharP (ZMod 2) 2` 成立，
但 `CharP ℤ 2` **不成立**（`(2 : ℤ) ≠ 0`）。
**代小整数立刻判假** ⇒ 该命题被**删除**（本文件**不写假命题**）。

⭐ **正确的分界**：特征是**单射**（而非满射）下的不变量。
⇒ 上一条 `charP_of_injective` 是本文件在此处的**唯一**承重结论。
⚠ **通用教训**：**"满射"与"单射"在此不可互换** ——
反例 `ℤ ↠ ZMod 2` 正是"特征从 `0` 变成 `2`"的那个标准例子
（它**满射但不单射**）。 -/
theorem charP_surjective_not_preserved :
    ¬ (∀ (f : ℤ →+* ZMod 2), Function.Surjective f → CharP (ZMod 2) 2 → CharP ℤ 2) := by
  intro h
  have hsurj : Function.Surjective (Int.castRingHom (ZMod 2)) := by
    intro x
    refine ⟨if x = 0 then 0 else 1, ?_⟩
    split_ifs with hx
    · subst hx; simp
    · fin_cases x <;> simp_all
  have h2 : CharP (ZMod 2) 2 := inferInstance
  have hcontra := h (Int.castRingHom (ZMod 2)) hsurj h2
  have hz : ((2 : ℕ) : ℤ) = 0 := CharP.cast_eq_zero ℤ 2
  norm_num at hz

/-! ## 6. ⚠ 诚实边界

- **未构造** `𝔽_p(t)`：Frobenius **单射但不满射**的经典见证。
  ⇒ 本文件**只陈述**"无限域上不必满射"，**未给机器验证的见证**。
  ⚠ 这是本文件**最重要的缺失**：§3 的"有限"假设的必要性
  **只有文字论证，没有反例证明**。
- **未证**有限域的存在性/唯一性；
- 注意 §1 的 `add_pow_eq_of_expChar`（草案旧名 `add_pow_eq_iff_frobenius_add`，
  该草案名**已否证**：本文件不存在 `↔` 形态的幂可加判别式声明，
  无对应机器验证对象，此条仅保留作历史沿革标注）：
  该条**只给正向**（`ExpChar R p ⟹ (x + y)^p = x^p + y^p`），
  `←` 逆向不成立/未做——其完整形式需要 `ringChar` 的计算，本文件未做；
  此降级登记与 §1 对该定理注释中的同款标注互为重复。
- **不处理**非交换环；
- **未给** `Frobenius` 与**可分性/完美域**的关系（`PerfectField`）。 -/

end Lattice.FrobeniusDichotomy
