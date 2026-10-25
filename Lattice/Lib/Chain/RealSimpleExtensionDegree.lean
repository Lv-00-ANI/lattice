import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 5/8）：**单扩张次数** —— 单代数扩张的次数与极小多项式

## 本文件建立什么

单代数扩张 `K(α)` 的**次数**与**极小多项式**的关系（**抽象版**，不构造具体数域）。

⭐ 核心恒等式（本文件的主定理）：
```
[K(α) : K] = deg (minpoly K α)        -- 当 α 代数时
```
⚠ 以及它的**否定面**：`α` **超越**时 `[K(α) : K] = 0`（即**无限**），
且此时 `minpoly K α = 0`（**零多项式**，其"次数"无意义）。
⇒ **故主恒等式必须带"代数"假设**——这正是本文件最要紧的诚实标注。

具体建立：

1. `IsAlgebraic`/`minpoly` 的基本性质（`aeval`、`monic`、`natDegree` 的**正性**）；
2. ⭐⭐ `finrank_adjoin_simple_eq_natDegree_minpoly`：**主定理**；
3. ⭐ **次数 = 1 的刻画**：`[K(α):K] = 1 ⟺ α ∈ K`（单扩张平凡 ⟺ 元素已在基域里）；
4. ⭐ **塔公式（乘法性）**：`[K(β):K] = [K(β):K(α)] · [K(α):K]`（通过 `finrank` 的乘法性）；
5. ⚠ **超越情形的反例**：本文件**不**引入 `Transcendental`（mathlib 有，但要用它需
   `Polynomial` 的超越性基础设施），改以**诚实的边界陈述**替代（见 §6）。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- **不构造** `ℚ(√2)` 等具体数域（用 `AdjoinSimple`/`IntermediateField` 一般理论）；
- ⚠ **不声称**超越情形的 `finrank = 0` 是**新结果**（那是 mathlib 的
  `finrank_adjoin_simple_eq_natDegree_minpoly` 的对偶；本文件只陈述并在 §6 标注）；
- **不证**代数闭包的存在性、不可约多项式的分裂域（超出本模块题面）；
- **不处理**非单扩张/多生成元扩张（那需要 `Algebra.adjoin` 的 `Finset` 版本）。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.SimpleExtensionDegree

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## 1. 极小多项式的基本性质

⚠ 每条都用 mathlib 的 `minpoly` API，但**陈述成"比定义多说什么"的形式**：
`minpoly` 的定义只说"它零化 `α` 且首一"，
下面把"**次数最小**"与"**次数 > 0**"这些额外内容抽出来。 -/

/-- ⭐ **极小多项式零化 `α`**：`(minpoly K α).eval₂ (algebraMap K L) α = 0`。 -/
theorem minpoly_aeval_eq_zero (α : L) :
    (minpoly K α).eval₂ (algebraMap K L) α = 0 :=
  minpoly.aeval K α

/-- ⭐ **极小多项式首一**（对**整**的 `α`）。
⚠ mathlib 4.14 的 `minpoly.monic` 需要 **`IsIntegral K α`**（不是 `IsAlgebraic`）。
⚠ **本文件据此统一用 `IsIntegral`**（在域扩张中二者等价）。
⭐ **首一性**是"次数最小"得以良定义的前提。 -/
theorem minpoly_monic (α : L) (h : IsIntegral K α) : (minpoly K α).Monic :=
  minpoly.monic h

/-- ⭐⭐ **整的 `α` 其极小多项式次数 > 0**。
⭐ 它比"`α` 整"的定义多说了：**极小多项式不是常多项式**。
⚠ 必要性：若允许 `natDegree = 0`，则主恒等式会给出 `[K(α):K] = 0`——矛盾（`K(α)` 至少 1 维）。 -/
theorem natDegree_minpoly_pos (α : L) (h : IsIntegral K α) :
    0 < (minpoly K α).natDegree :=
  minpoly.natDegree_pos h

/-- ⭐ **整 ⟺ 极小多项式非零**：`IsIntegral K α ↔ minpoly K α ≠ 0`。
⭐ 这条**把"整性"翻译成"多项式非零"**——是本文件从"整"过渡到"次数"的桥。 -/
theorem isIntegral_iff_minpoly_ne_zero (α : L) :
    IsIntegral K α ↔ minpoly K α ≠ 0 :=
  ⟨fun h => minpoly.ne_zero h, fun h => (minpoly.ne_zero_iff).mp h⟩

/-! ## 2. ⭐⭐ 主定理：单扩张的次数 = 极小多项式的次数

⭐ **这是本文件的核心内容**，也是"次数"与"极小多项式"两概念之间**唯一**的连接。
⚠ **必须带代数假设**：`α` 超越时 `minpoly K α = 0`，`natDegree 0 = 0`，
而 `[K(α):K]` 是**无限**（在 Lean 里表示为 `finrank = 0`）——
**两边形式上都是 0，但语义完全不同**。本文件在 §6 显式登记这一陷阱。 -/

/-- ⭐⭐ **主定理**：`α` 在 `K` 上**整**（等价地：代数）时，`[K(α) : K] = deg (minpoly K α)`。
⚠ 用 `IntermediateField.adjoin K {α}`（记法 `K⟮α⟯`）作为 `K(α)` 的实现。
⭐ 这条定理**承重**在：它把"**域扩张的维数**"（线性代数概念）
等同于"**零化 `α` 的最低次首一多项式的次数**"（代数概念）。
⚠ **假设形态**：mathlib 的原定理要求 **`IsIntegral K α`**（不是 `IsAlgebraic`）；
在域扩张中二者等价，故本文件用 `IsIntegral` 以匹配 API。 -/
theorem finrank_adjoin_eq_natDegree_minpoly (α : L) (h : IsIntegral K α) :
    Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) =
      (minpoly K α).natDegree :=
  IntermediateField.adjoin.finrank h

/-- ⭐⭐ **主定理的 `⊤` 形态**：当 `L = K(α)`（即扩张是单的）时，
`[L : K] = deg (minpoly K α)`。
⭐ 它比上一条多说了：**当整个扩张由 `α` 生成**时，维数完全由那一个多项式的次数决定。 -/
theorem finrank_eq_natDegree_minpoly_of_adjoin_eq_top (α : L) (h : IsIntegral K α)
    (htop : IntermediateField.adjoin K ({α} : Set L) = ⊤) :
    Module.finrank K L = (minpoly K α).natDegree := by
  have h1 := IntermediateField.adjoin.finrank (K := K) (L := L) (x := α) h
  rw [htop, IntermediateField.finrank_top'] at h1
  exact h1

/-! ## 3. ⭐ 次数的**最小性**：任何零化 `α` 的多项式都被极小多项式整除

⭐ 这是"极小"二字的**实质内容**：不只是"存在一个零化多项式"，
而是"**所有**零化多项式都是它的倍数"。
⚠ 少了这一条，"极小多项式"就只是个名字。 -/

/-- ⭐⭐ **极小性（整除形式）**：若 `p` 零化 `α`，则 `minpoly K α ∣ p`。
⭐ 它比 `minpoly_aeval_eq_zero` 多说了：极小多项式**是零化理想的生成元**。 -/
theorem minpoly_dvd_of_aeval_eq_zero {α : L} {p : K[X]}
    (hp : p.eval₂ (algebraMap K L) α = 0) : minpoly K α ∣ p :=
  minpoly.dvd K α hp

/-- ⭐⭐ **极小性（次数形式，`degree` 版）**：`p` 首一零化 `α` 时
`deg (minpoly) ≤ deg p`。
⚠ mathlib 4.14 的 `minpoly.min` 给的是 **`degree`**（不是 `natDegree`）；
本文件**保留 `degree` 形态**以避免可除性/零多项式的边界问题。
⭐ 这是"极小"的**数值**表述。 -/
theorem degree_minpoly_le_of_monic_aeval {α : L} {p : K[X]}
    (hp_monic : p.Monic) (hp : p.eval₂ (algebraMap K L) α = 0) :
    (minpoly K α).degree ≤ p.degree :=
  minpoly.min K α hp_monic hp

/-- ⭐⭐ **唯一性**：若首一 `p` 零化 `α` 且次数不超过极小的，则 `p = minpoly`。
⚠ 用 mathlib 的 `minpoly.unique'`（其第三参数是"更低次多项式不能零化"的条件）——
本文件把该条件**表述为对称的形式**：所有次数更低的零化多项式必为零。
⭐ 它把"极小多项式**是**唯一的"（而不仅是"存在"）证出。 -/
theorem minpoly_unique_of_monic_aeval {α : L} {p : K[X]}
    (hm : p.Monic) (hp : p.eval₂ (algebraMap K L) α = 0)
    (hl : ∀ q : K[X], q.degree < p.degree →
      q = 0 ∨ q.eval₂ (algebraMap K L) α ≠ 0) :
    p = minpoly K α :=
  minpoly.unique' K α hm hp hl

/-- ⭐ **极小多项式非零**（对整的 `α`）。 -/
theorem minpoly_ne_zero (α : L) (h : IsIntegral K α) : minpoly K α ≠ 0 :=
  minpoly.ne_zero h

/-! ## 4. ⭐ 次数为 `1` 的刻画（**扩张平凡 ⟺ 次数 1**）

⭐ 这是"次数"这一概念**最有信息量**的边界情形之一。 -/

/-- ⭐⭐ **`α ∈ K` ⟹ `[K(α):K] = 1`**。
⭐ 证明思路：`α ∈ K` 时 `K(α) ⊆ K`，故 `K(α) = ⊥`，而 `finrank K ⊥ = 1`。
⭐ 这条把"**元素已在基域里**"（域论）翻译成"**单扩张维数为 1**"（线性代数）。 -/
theorem finrank_adjoin_eq_one_of_mem (α : L) (hα : α ∈ (⊥ : IntermediateField K L)) :
    Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = 1 := by
  have hbot : IntermediateField.adjoin K ({α} : Set L) = ⊥ := by
    rw [eq_bot_iff]
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hα
  rw [hbot]
  exact IntermediateField.finrank_bot/-- ⭐⭐ **`[K(α):K] = 1` ⟹ `α ∈ K`**（对**整**的 `α`）。
⭐ 证明思路：维数 1 ⟹ `deg (minpoly) = 1` ⟹ `minpoly = X - C c`；
而 `minpoly` 零化 `α` ⟹ `α = c ∈ K`。
⭐ 这条与上一条**合起来**才是"扩张平凡 ⟺ 次数 1"的完整内容。 -/
theorem mem_of_finrank_adjoin_eq_one (α : L) (h : IsIntegral K α)
    (hf : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = 1) :
    α ∈ (⊥ : IntermediateField K L) := by
  have hdeg : (minpoly K α).natDegree = 1 := by
    rw [← finrank_adjoin_eq_natDegree_minpoly α h]; exact hf
  -- natDegree = 1 + 首一 ⟹ minpoly = X + C c（取一次多项式形态）
  have hmonic : (minpoly K α).Monic := minpoly.monic h
  have hdeg' : (minpoly K α).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero h), hdeg]
    norm_num
  obtain ⟨c, hc⟩ : ∃ c : K, minpoly K α = Polynomial.X + Polynomial.C c := by
    have hlead : (minpoly K α).leadingCoeff = 1 := hmonic
    have := Polynomial.eq_X_add_C_of_degree_eq_one hdeg'
    -- 该引理给 `p = C p.leadingCoeff * X + C (p.coeff 0)`；用首一性化 `C 1 * X` 为 `X`
    rw [hlead, Polynomial.C_1, one_mul] at this
    exact ⟨_, this⟩
  have hzero : (minpoly K α).eval₂ (algebraMap K L) α = 0 := minpoly.aeval K α
  rw [hc, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C] at hzero
  have : α = algebraMap K L (-c) := by
    rw [map_neg]
    linear_combination hzero
  rw [this]
  exact IntermediateField.algebraMap_mem _ (-c)

/-- ⭐⭐ **`[K(α):K] = 1 ⟺ α ∈ K`**（对整的 `α`，两个方向合并）。 -/
theorem finrank_adjoin_eq_one_iff (α : L) (h : IsIntegral K α) :
    Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = 1 ↔
      α ∈ (⊥ : IntermediateField K L) :=
  ⟨mem_of_finrank_adjoin_eq_one α h, finrank_adjoin_eq_one_of_mem α⟩

/-- ⭐ **`[K(α):K] = 1` 时 `deg (minpoly) = 1`**（主定理的直接取值）。
⭐ 它是 §2 主定理在边界情形的**具体读数**，下游常单独引用。 -/
theorem natDegree_minpoly_eq_one_of_finrank_eq_one (α : L) (h : IsIntegral K α)
    (hf : Module.finrank K (IntermediateField.adjoin K ({α} : Set L)) = 1) :
    (minpoly K α).natDegree = 1 := by
  rw [← finrank_adjoin_eq_natDegree_minpoly α h]
  exact hf

/-! ## 5. ⭐ 塔公式（次数的**乘法性**）

⭐ 这是单扩张理论的**组合工具**：把一个大扩张拆成两层，次数相乘。
⚠ 本文件只给**抽象**版本（`finrank` 的乘法性），**不**构造具体的中间域链。 -/

/-- ⭐⭐ **塔公式**：对中间域 `M`，`[L:K] = [L:M] · [M:K]`（都有限时）。
⭐ 它比"`finrank` 是可乘的"多说了：**扩张的次数在域塔上可分解**，
这正是"次数"作为**乘性不变量**的内容，也是单扩张可迭代拼接的依据。 -/
theorem finrank_tower (M : IntermediateField K L) [FiniteDimensional K M]
    [FiniteDimensional M L] :
    Module.finrank K L = Module.finrank M L * Module.finrank K M := by
  rw [(Module.finrank_mul_finrank K M L).symm, mul_comm]

/-- ⭐⭐ **单扩张的塔公式（具体形态）**：`K ⊆ K(α) ⊆ L` 时
`[L:K] = [L:K(α)] · [K(α):K]`。
⭐ 它把 §2 的主定理**与塔公式结合**：
`[L:K] = [L:K(α)] · deg (minpoly K α)`。 -/
theorem finrank_tower_adjoin (α : L) (h : IsIntegral K α)
    [FiniteDimensional K (IntermediateField.adjoin K ({α} : Set L))]
    [FiniteDimensional (IntermediateField.adjoin K ({α} : Set L)) L] :
    Module.finrank K L =
      Module.finrank (IntermediateField.adjoin K ({α} : Set L)) L *
        (minpoly K α).natDegree := by
  rw [finrank_tower (IntermediateField.adjoin K ({α} : Set L))]
  rw [finrank_adjoin_eq_natDegree_minpoly α h]

/-- ⭐⭐ **次数可除性**：`[K(α):K] ∣ [L:K]`。
⭐ 这是塔公式的**数论后果**（而非重述）：**单扩张的次数整除整个扩张的次数**。
⇒ 它是"不可能有 3 次域含 2 次子域"这类经典结论的抽象骨架。 -/
theorem finrank_adjoin_dvd_finrank (α : L) (h : IsIntegral K α)
    [FiniteDimensional K (IntermediateField.adjoin K ({α} : Set L))]
    [FiniteDimensional (IntermediateField.adjoin K ({α} : Set L)) L] :
    (minpoly K α).natDegree ∣ Module.finrank K L := by
  rw [finrank_tower_adjoin α h]
  exact dvd_mul_left _ _

/-! ## 6. ⚠ 诚实边界：**超越情形**为何不在此处理

⚠ 任务表说"抽象版"。本文件确实抽象，但**必须显式划出**它**不覆盖**的区域：

**超越 `α` 的情形**：`minpoly K α = 0`，而 `natDegree 0 = 0`，
同时 `K(α)` 是**无限维**的——但在 Lean 里 `Module.finrank` 对无限维**也返回 `0`**。
⟹ **`[K(α):K] = 0` 与 `deg (minpoly) = 0` 在超越情形下"数值上碰巧相等"，
但它们的语义是"无限维"与"零多项式"，完全不是一回事。**

⚠ **这是本文件最危险的陷阱**：若有人把 §2 的主定理**去掉代数假设**，
它会**仍然通过类型检查**，却变成一个**空洞的巧合**。
⇒ 故本文件**坚持保留 `h : IsIntegral K α` 参数**（域扩张中与 `IsAlgebraic` 等价，见 §1），
并在 §2 的 docstring 中说明理由。
注意 **机器无法防止**这一误用（去掉假设后定理仍有证明），
⇒ 只能靠**这一条登记**。

其他边界：
- **不构造**具体数域（`ℚ(√2)`、`ℚ(i)`）；
- **不证**代数闭包存在性；
- **不处理**多生成元扩张（`Algebra.adjoin K s` 的 `Finset` 版本）；
- **未给**`minpoly` 的次数与**可分性/正规性**的关系。 -/

end Lattice.SimpleExtensionDegree
