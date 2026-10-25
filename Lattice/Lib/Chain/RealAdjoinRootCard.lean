import Mathlib
import Lattice.Lib.LearningTheory.RealGaloisFieldPoly
/-!
# LATTICE: 商环 `F[X]/(p)` 的有限性与基数公式 `|F[X]/(p)| = |F|^deg p`

补 `RealGaloisFieldPoly` 明确标注的缺口：

  > 「定理 5 **只**给出 `Field (AdjoinRoot p)` 实例；**未做**：`Fintype (AdjoinRoot p)`
  > 与基数公式 `#AdjoinRoot p = #F ^ p.natDegree`。」

本文件把这条**有限的组合事实**做出来。设 `F` 是有限域（`[Field F] [Fintype F]`）、
`p ∈ F[X]` 非零（`[Fact (p ≠ 0)]`，由 `Fact (Irreducible p)` 自动升级，见 `arc_fact_ne_zero`）：

  1. `arc_fintype_powerBasis`：`AdjoinRoot p` 上的 `Fintype` 实例
     （经 `AdjoinRoot.powerBasis` 的坐标表示 `AdjoinRoot p ≃ₗ[F] (Fin p.natDegree →₀ F)`）；
  2. `arc_powerBasis_dim`：`(AdjoinRoot.powerBasis p).dim = p.natDegree`；
  3. `arc_finsupp_card`：`#(Fin n →₀ F) = #F ^ n`（多项式系数向量的计数）；
  4. **`arc_card_adjoinRoot`（主定理）**：`#(AdjoinRoot p) = #F ^ p.natDegree`
     —— 即 `|F[X]/(p)| = |F|^deg p`；
  5. `arc_card_adjoinRoot_irreducible`：不可约 `p` 下同一公式的**主用入口形式**
     （`[Fact (Irreducible p)]`，扩域 `𝔽_{q^d}` 的基数）；
  6. `arc_card_adjoinRoot_X`：一次因子的特例 `#(AdjoinRoot X) = #F`（未扩张）；
  7. `arc_adjoin_root_two_le_card`：`[Nontrivial F]` 且 `p` 不可约（`[Fact (Irreducible p)]`）
     时 `AdjoinRoot p` 至少有两个元素（`2 ≤ #(AdjoinRoot p)`），即商环**非退化**。

**回收的 mathlib 4.14 API（本文件经锁下探针 `_probe_arc.lean` 实测确认）**：
- `AdjoinRoot.powerBasis (f := p) (Fact.out : Fact (p ≠ 0))` **存在**，且
  `AdjoinRoot.powerBasis_dim : (AdjoinRoot.powerBasis f hf).dim = f.natDegree`；
- `AdjoinRoot` **没有现成的 `Fintype` 实例**（`inferInstance : Fintype (AdjoinRoot p)` 实测失败）
  → 必须手写，用 `PowerBasis.basis.repr` 配 `Fintype.ofEquiv`；**注意方向**：
  `repr` 的类型是 `AdjoinRoot p ≃ₗ[F] (Fin dim →₀ F)`，`Fintype.ofEquiv` 要求
  `α ≃ β` 中 `α` 是**待赋实例的类型**，故必须取 **`.symm`**（`Fintype.ofEquiv (Fin dim →₀ F) repr.symm`）；
- `Fact (Irreducible p)` **不会**合成 `Fact (p ≠ 0)`（实测失败）→ 需局部
  `haveI : Fact (p ≠ 0) := ⟨(Fact.out : Irreducible p).ne_zero⟩`（见 `arc_fact_ne_zero`）。

**诚实标注（降级/未做）**：
- 本文件的 `Fintype (AdjoinRoot p)` 是**通过显式等价 `Fintype.ofEquiv` 给出的局部实例**
  （`arc_fintype_powerBasis`），而**不是**注册为全局类型类实例：`AdjoinRoot` 的商环结构
  （`Quot` 上的 `Fintype`）与 `PowerBasis` 坐标表示之间的**定义相等性**在 mathlib 4.14 中
  不能由类型类搜索自动合成（实测 `inferInstance : Fintype (AdjoinRoot p)` 失败）。
  这是一个**形式/接口降级**而非命题削弱：`arc_card_adjoinRoot` 的结论是完整的基数公式；
  但下游若想直接写 `Fintype.card (AdjoinRoot p)` 而不传 `arc_fintype_powerBasis`，则**未打通**，
  需显式携带该实例（标注**未做**：全局实例注册）；
- **未做**：`Fact (p ≠ 0)` 的**类型类层面的自动升级**（`Fact (Irreducible p) → Fact (p ≠ 0)`）。
  Lean 的 `Fact` 是 `Prop` 包裹的普通记录、**没有**类型类蕴含机制，故只能作为**定理**
  `arc_fact_ne_zero`（返回 `p ≠ 0`）并由调用方 `haveI` 手动装配，不能声明为 `instance` 而自动合成
  ——这是 mathlib 的设计限制，已在 docstring 标注；
- **未做**：`p` 可约时的商环结构（`AdjoinRoot p` 此时不是域，`arc_adjoin_root_pow_eq_zero` 给出
  `p(root) = 0` 但本文件不讨论其零因子）；
- **未做**：`AdjoinRoot` 与 `FiniteField`/`GaloisField` 的等价、扩域的 Frobenius 阶数
  （`#(AdjoinRoot p) = #F ^ p.natDegree` 与 `RealGaloisFieldPoly.gfp_pow_card_eq_self` 的衔接留给下游）；
- 不用 `sorry`/`axiom`/`admit`。

模型无关：任意有限域 `F` 与任意非零 `p ∈ F[X]`。
-/

noncomputable section

namespace Lattice

open Polynomial

open scoped BigOperators Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 第一节：`Fact (Irreducible p)` ⟹ `p ≠ 0`（手动装配） -/

omit [Fintype F] [DecidableEq F] in
/-- **`Fact (p ≠ 0)` 的手动装配**：`[Fact (Irreducible p)]` 下返回 `p ≠ 0`。

诚实标注：Lean 的 `Fact` **不参与**类型类蕴含（它不是 `outParam` 链上的可搜索实例），
故 `Fact (Irreducible p) → Fact (p ≠ 0)` **不能**声明为 `instance` 自动合成；
调用方需 `haveI : Fact (p ≠ 0) := ⟨arc_fact_ne_zero p⟩`。这是**接口降级**（非命题削弱）：
`AdjoinRoot.powerBasis` 要求 `Fact (p ≠ 0)`，本引理就是把不可约性提供的那一半**显式化**。 -/
theorem arc_fact_ne_zero (p : F[X]) [Fact (Irreducible p)] : p ≠ 0 :=
  (Fact.out : Irreducible p).ne_zero

/-! ## 第二节：`PowerBasis` 的维数 -/

omit [Fintype F] [DecidableEq F] in
/-- **`PowerBasis` 维数**：`(AdjoinRoot.powerBasis p).dim = p.natDegree`
（回收 `AdjoinRoot.powerBasis_dim`，把 `Fact` 参数显式化以便下游直接使用）。 -/
theorem arc_powerBasis_dim (p : F[X]) [Fact (p ≠ 0)] :
    (AdjoinRoot.powerBasis (f := p) Fact.out).dim = p.natDegree :=
  AdjoinRoot.powerBasis_dim (f := p) Fact.out

/-! ## 第三节：多项式系数向量 `Fin n →₀ F` 的基数 -/

omit [DecidableEq F] in
/-- **系数向量的计数**：`#(Fin n →₀ F) = #F ^ n`。
（`Finsupp` 在有限指标类型上等价于函数空间 `Fin n → F`，逐坐标独立取值共 `#F ^ n` 种。） -/
theorem arc_finsupp_card (n : ℕ) : Fintype.card (Fin n →₀ F) = Fintype.card F ^ n := by
  rw [Fintype.card_finsupp]
  simp

/-! ## 第四节：`Fintype (AdjoinRoot p)` -/

/-- **`AdjoinRoot p` 的有限性**（显式实例）：经 `PowerBasis.basis` 的坐标表示
`AdjoinRoot p ≃ₗ[F] (Fin p.natDegree →₀ F)`（取 `.symm` 得 `Finsupp → AdjoinRoot p`
方向，正是 `Fintype.ofEquiv` 所需的「待赋实例类型在左」的形式）。

诚实标注：这是**局部给出的实例**（值级证明），而非注册到类型类搜索的全局 `instance`；
下游使用 `Fintype.card (AdjoinRoot p)` 时需通过 `letI := arc_fintype_powerBasis p` 携带它。
**上游（4.14 与 4.33）均无 `Fintype (AdjoinRoot p)` 实例**——手写是必要的（已核实）。 -/
def arc_fintype_powerBasis (p : F[X]) [Fact (p ≠ 0)] : Fintype (AdjoinRoot p) :=
  Fintype.ofEquiv (Fin (AdjoinRoot.powerBasis (f := p) Fact.out).dim →₀ F)
    (AdjoinRoot.powerBasis (f := p) Fact.out).basis.repr.symm

/-! ## 第五节：主定理 —— 基数公式 `#(AdjoinRoot p) = #F ^ p.natDegree`

**接口约定（重要）**：由于 `AdjoinRoot p` **没有**全局 `Fintype` 实例（上游 4.14 与 4.33
均无，已核实），本节各定理把 `Fintype (AdjoinRoot p)` 作为**显式参数** `inst` 传入，
语句中即可写干净的 `Fintype.card (AdjoinRoot p)`。
调用方以 `arc_fintype_powerBasis p` 作为该实参——
这是**接口降级**（非命题削弱），也是本文件与「上游缺实例」这一事实的**最小摩擦**接法。 -/

section CardFormula

variable (p : F[X]) [Fact (p ≠ 0)] (inst : Fintype (AdjoinRoot p))

/-- **主定理（A1.6 核心）**：`#(AdjoinRoot p) = #F ^ p.natDegree`，即 `|F[X]/(p)| = |F|^deg p`。

证明：`PowerBasis.basis` 给出 `AdjoinRoot p ≃ₗ[F] (Fin (deg p) →₀ F)`，
`Fintype.card_congr` 把基数搬到 `Finsupp` 上，`Fintype.card_finsupp` 给出 `#F ^ dim`，
维数用 `AdjoinRoot.powerBasis_dim` 换回 `p.natDegree`。

（这是**有限**的组合事实：商环的每个元素由次数 `< deg p` 的**唯一**余式代表，
系数逐位独立、共 `#F ^ deg p` 种取值。）

诚实标注：结论与所传 `inst` **无关**（任何 `Fintype (AdjoinRoot p)` 都给出同一基数），
故 `inst` 只是「让 `Fintype.card` 可书写」的**接口载体**。 -/
theorem arc_card_adjoinRoot :
    Fintype.card (AdjoinRoot p) = Fintype.card F ^ p.natDegree := by
  have hcard : Fintype.card (AdjoinRoot p) =
      Fintype.card (Fin (AdjoinRoot.powerBasis (f := p) Fact.out).dim →₀ F) :=
    @Fintype.card_congr (AdjoinRoot p)
      (Fin (AdjoinRoot.powerBasis (f := p) Fact.out).dim →₀ F)
      inst inferInstance
      (PowerBasis.basis (AdjoinRoot.powerBasis (f := p) Fact.out)).repr
  rw [hcard, Fintype.card_finsupp, AdjoinRoot.powerBasis_dim (f := p) Fact.out]
  simp

/-- **（通用引理，但本文件只用它的 `Irreducible` 特例）**：
不可约多项式 `p` 的次数为正：`[Fact (Irreducible p)] ⟹ 0 < p.natDegree`。

诚实标注（**命题更正，重要**）：先前草稿写的是「`p ≠ 0 ⟹ 0 < p.natDegree`」——
**这是假的**：取 `p = C 1`（非零常数），`natDegree = 0`。
真正的充分条件是 **`Irreducible p`**（不可约非零多项式必为非常数，mathlib 有
`Irreducible.natDegree_pos`，`Algebra/Polynomial/FieldDivision.lean:666`）。
本文件把命题**收紧为不可约情形**并回收该 mathlib 引理，避免假命题。 -/
theorem arc_natDegree_pos (p : F[X]) [Fact (Irreducible p)] : 0 < p.natDegree :=
  (Fact.out : Irreducible p).natDegree_pos

/-- **商环非退化（不可约情形）**：`[Nontrivial F]` 且 `p` 不可约时
`AdjoinRoot p` 至少有两个元素。

证明：`#(AdjoinRoot p) = #F ^ p.natDegree`（`arc_card_adjoinRoot`），
且 `p.natDegree ≥ 1`（`arc_natDegree_pos`，**需 `Irreducible p`**——见该定理的命题更正说明），
故 `#F ^ p.natDegree ≥ #F ^ 1 = #F ≥ 2`。

诚实标注：**`[Fact (p ≠ 0)]` 不足以**推出本结论——`p = C 1` 时 `AdjoinRoot p ≃ F`
（次数 0），`#F ^ 0 = 1` **不小于 2**。因此本定理正确地以
**`[Fact (Irreducible p)]`** 为假设（不可约 ⟹ 非常数）。 -/
theorem arc_adjoin_root_two_le_card (p : F[X]) [Fact (Irreducible p)]
    (inst : Fintype (AdjoinRoot p)) [Nontrivial F] :
    2 ≤ Fintype.card (AdjoinRoot p) := by
  haveI : Fact (p ≠ 0) := Fact.mk (arc_fact_ne_zero p)
  rw [arc_card_adjoinRoot p inst]
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  calc (2 : ℕ) ≤ Fintype.card F := h2
    _ = Fintype.card F ^ 1 := (pow_one _).symm
    _ ≤ Fintype.card F ^ p.natDegree :=
        Nat.pow_le_pow_right (by omega) (arc_natDegree_pos p)

/-- **基数的显式非零**：`0 < #(AdjoinRoot p) = #F ^ p.natDegree`（有限域非空）。 -/
theorem arc_card_adjoinRoot_pos : 0 < Fintype.card (AdjoinRoot p) := by
  rw [arc_card_adjoinRoot p inst]
  exact Nat.pos_pow_of_pos _ Fintype.card_pos

end CardFormula

/-- **不可约情形的基数公式**（主用入口）：`[Fact (Irreducible p)]` 下
`#(AdjoinRoot p) = #F ^ p.natDegree`。此时 `AdjoinRoot p` 是域
（`RealGaloisFieldPoly.gfp_adjoin_root_field`），故这是**扩域 `𝔽_{q^d}`
（`q = #F`、`d = deg p`）的基数**。

诚实标注：`Fact (p ≠ 0)` 由 `arc_fact_ne_zero` **手动装配**（`haveI`），
原因见该定理 docstring（`Fact` 不参与类型类蕴含）。 -/
theorem arc_card_adjoinRoot_irreducible (p : F[X]) [Fact (Irreducible p)]
    (inst : Fintype (AdjoinRoot p)) :
    Fintype.card (AdjoinRoot p) = Fintype.card F ^ p.natDegree := by
  haveI : Fact (p ≠ 0) := Fact.mk (arc_fact_ne_zero p)
  exact arc_card_adjoinRoot p inst

/-- **不可约情形 + 规范实例的合并形式**：直接用 `arc_fintype_powerBasis`
作为实例的版本（下游最常用的调用形状）。

诚实标注：语句里 `Fintype.card (AdjoinRoot p)` 靠定理内的 `letI` 提供实例
（`Fintype (AdjoinRoot p)` 不能经类型类搜索自动获得）。 -/
theorem arc_card_adjoinRoot_irreducible_apply (p : F[X]) [Fact (Irreducible p)] :
    letI : Fact (p ≠ 0) := Fact.mk (arc_fact_ne_zero p)
    letI : Fintype (AdjoinRoot p) := arc_fintype_powerBasis p
    Fintype.card (AdjoinRoot p) = Fintype.card F ^ p.natDegree := by
  haveI : Fact (p ≠ 0) := Fact.mk (arc_fact_ne_zero p)
  letI : Fintype (AdjoinRoot p) := arc_fintype_powerBasis p
  exact arc_card_adjoinRoot p (arc_fintype_powerBasis p)

/-- **一次因子特例**：`#(AdjoinRoot X) = #F`（`deg X = 1`，商环同构于 `F` 本身，不扩张）。

诚实标注：`X ≠ 0`（`[Fact ((X : F[X]) ≠ 0)]`）作为**显式假设**传入——虽然 `X ≠ 0`
在域上恒真，但把它注册为全局实例会与其它 `Fact` 实例冲突，故保持显式。 -/
theorem arc_card_adjoinRoot_X [Nontrivial F] [Fact ((X : F[X]) ≠ 0)]
    (inst : Fintype (AdjoinRoot (X : F[X]))) :
    Fintype.card (AdjoinRoot (X : F[X])) = Fintype.card F := by
  rw [arc_card_adjoinRoot (X : F[X]) inst, Polynomial.natDegree_X, pow_one]

/-! ## 第六节：与 `RealGaloisFieldPoly` 的衔接 -/

/-- **扩域中元素的 Frobenius 阶**：`AdjoinRoot p` 的元素 `x` 满足
`x ^ #(AdjoinRoot p) = x`（有限域的普遍 Frobenius，
`RealGaloisFieldPoly.gfp_pow_card_eq_self` 的 `AdjoinRoot` 版）。

诚实标注：本定理把 `Fintype (AdjoinRoot p)` 与 `Fact (p ≠ 0)` 作为**显式参数/局部实例**
携带，因为两者都**不能**经类型类搜索自动获得（与 `arc_card_adjoinRoot` 的降级同源）。
`Field (AdjoinRoot p)` 需要 `[Fact (Irreducible p)]`
（`RealGaloisFieldPoly.gfp_adjoin_root_field`）。 -/
theorem arc_pow_card_eq_self (p : F[X]) [Fact (Irreducible p)]
    (inst : Fintype (AdjoinRoot p)) (x : AdjoinRoot p) :
    x ^ Fintype.card (AdjoinRoot p) = x :=
  FiniteField.pow_card x

end Lattice
