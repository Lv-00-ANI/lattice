import Mathlib
import Lattice.Lib.Chain.RealPolyInterp
import Lattice.Lib.Chain.RealPrimeFieldExt
/-!
# LATTICE: 有限域上的多项式 —— 根数上界、`X^q − X` 的完全分解、Frobenius、商环

`RealPolyInterp`（Lagrange 基的 cardinal 性质）与 `RealPrimeFieldExt`（素数域/秩-零化度）
的**有限域多项式**补全。设 `F` 是有限域（`[Field F] [Fintype F] [DecidableEq F]`，`q = #F`）：

  1. `gfp_card_roots_le_natDegree`：`f ≠ 0` ⟹ `f` 的根数 ≤ `deg f`
     ——「`deg f = n` ⟹ 根 ≤ `n`」（回收 `Polynomial.card_roots'`）；
  2. `gfp_X_pow_card_sub_X_eq_prod`：**`X^q − X = ∏_{a∈F}(X − a)`**
     —— 有限域的完全分解（`X^q − X` 的根恰为全部元素）；
  3. `gfp_pow_card_eq_self`：`a^q = a`（Frobenius / `f^q = f` 在每点成立）；
  4. `gfp_pow_card_sub_one_eq_one`：`a ≠ 0 ⟹ a^(q−1) = 1`；
  5. `gfp_adjoin_root_field`：不可约 `p` 的商环 `AdjoinRoot p` 是域（构造扩域）。

**诚实标注（降级/未做）**：
- 定理 5 **只**给出 `Field (AdjoinRoot p)` 实例（`Fact (Irreducible p)` 假设下）；
  **`Fintype (AdjoinRoot p)` 与基数公式 `#AdjoinRoot p = #F ^ p.natDegree` 现已由
  `RealAdjoinRootCard` 补齐**（该文件用 `AdjoinRoot.powerBasis` 的系数表示手写
  `Fintype` 实例并证出基数）——本文件的缺口**已闭合**，见 `RealAdjoinRootCard` 的
  `arc_card_adjoinRoot` 与 `arc_card_adjoinRoot_irreducible`。
  （历史注：此处原标注「未做」，原因是 4.14 未提供现成 `Fintype` 实例——该判断**正确**，
  但缺口已被 `RealAdjoinRootCard` 以显式实例 + `Fintype.ofEquiv` 补齐。）
- 未做：多项式环 `F[X]` 的唯一分解/不可约判定（`Fact p.Irreducible` 作为**显式假设**传入）；
- 定理 2 用「两边求值相同 + 首一 + 次数相同 ⟹ 差为零多项式」的根计数论证，
  不依赖 mathlib 的 `Polynomial` 剖分引理。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

namespace Lattice

open Polynomial Finset

open scoped BigOperators Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 定理一：根数上界（`deg f = n ⟹ 根 ≤ n`） -/

/-- **根数上界**：非零多项式 `f ∈ F[X]` 在有限域 `F` 中的根数不超过其次数
（回收 `Polynomial.card_roots'` + `Multiset.toFinset_card_le`）。 -/
theorem gfp_card_roots_le_natDegree (f : F[X]) (hf : f ≠ 0) :
    (Finset.univ.filter (fun a : F => f.IsRoot a)).card ≤ f.natDegree := by
  have h1 : f.roots.toFinset.card ≤ f.natDegree :=
    calc f.roots.toFinset.card ≤ (f.roots).card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
  refine le_trans ?_ h1
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
  exact ha.2

/-! ## 定理二：`X^q − X = ∏_{a∈F}(X − a)` -/

/-- **有限域的完全分解**：`X^#F − X = ∏_{a∈F}(X − a)`。

证明：记 `P = ∏_a (X − a)`、`Q = X^q − X`。`P` 首一、`natDegree P = q`；`Q` 首一、
`natDegree Q = q`。取差 `P − Q`：每个 `a ∈ F` 都是 `P` 与 `Q` 的根，故 `P − Q` 在 `F` 上
处处为零；而 `P − Q` 的次数严格小于 `q`（首项相消），由根计数引理
`eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` 得 `P − Q = 0`。 -/
theorem gfp_X_pow_card_sub_X_eq_prod :
    (X ^ Fintype.card F - X : F[X]) = ∏ a : F, (X - C a) := by
  classical
  set P : F[X] := ∏ a : F, (X - C a) with hP
  set Q : F[X] := (X ^ Fintype.card F - X : F[X]) with hQ
  have hPmonic : P.Monic := by
    rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ (fun a _ => Polynomial.monic_X_sub_C a)
  have hPnat : P.natDegree = Fintype.card F := by
    rw [hP, Polynomial.natDegree_prod (s := Finset.univ) (f := fun a : F => (X - C a : F[X]))
      (by intro a _; exact (Polynomial.monic_X_sub_C a).ne_zero)]
    simp [Polynomial.natDegree_X_sub_C]
  have hQmonic : Q.Monic := by
    rw [hQ]
    exact Polynomial.monic_X_pow_sub
      (by rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
  have hQnat : Q.natDegree = Fintype.card F := by
    rw [hQ]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card
  have hQne : Q ≠ 0 := by
    rw [hQ]
    exact FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  -- 求值：P 与 Q 在 F 上处处为零
  have hPeval : ∀ x : F, P.eval x = 0 := by
    intro x
    have hdvd : (X - C x : F[X]) ∣ P := by
      rw [hP]
      exact Finset.dvd_prod_of_mem (fun a : F => (X - C a : F[X])) (Finset.mem_univ x)
    obtain ⟨r, hr⟩ := hdvd
    rw [hr, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul]
  have hQeval : ∀ x : F, Q.eval x = 0 := by
    intro x
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, FiniteField.pow_card,
      sub_self]
  have hsubeval : ∀ x : F, (P - Q).eval x = 0 := by
    intro x
    rw [Polynomial.eval_sub, hPeval x, hQeval x, sub_zero]
  -- 次数界：natDegree (P − Q) < q
  have hcard : (P - Q).natDegree < Fintype.card F := by
    by_cases h0 : P - Q = 0
    · rw [h0, Polynomial.natDegree_zero]
      exact Fintype.card_pos
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
      have hdegP : P.degree = (Fintype.card F : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hPmonic.ne_zero, hPnat]
      have hdegQ : Q.degree = (Fintype.card F : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hQne, hQnat]
      have hd : P.degree = Q.degree := by rw [hdegP, hdegQ]
      have hlc : P.leadingCoeff = Q.leadingCoeff := by
        rw [hPmonic.leadingCoeff, hQmonic.leadingCoeff]
      have hlt := Polynomial.degree_sub_lt hd hPmonic.ne_zero hlc
      rwa [hdegP] at hlt
  have hzero : P - Q = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (P - Q) Finset.univ
      (fun i _ => hsubeval i) (by simpa using hcard)
  have : P = Q := sub_eq_zero.mp hzero
  exact this.symm

omit [DecidableEq F] in
/-- 推论：`X^q − X` 的根恰为 `F` 的全部元素（根集 = 全集）。 -/
theorem gfp_eval_X_pow_card_sub_X_eq_zero (a : F) :
    (X ^ Fintype.card F - X : F[X]).eval a = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, FiniteField.pow_card, sub_self]

/-! ## 定理三、四：Frobenius（`f^q = f` 在每点成立） -/

omit [DecidableEq F] in
/-- **Frobenius**：有限域中每个元素满足 `a^q = a`（`q = #F`）。
（回收 `FiniteField.pow_card`；亦可由定理二在 `a` 处求值得到。） -/
theorem gfp_pow_card_eq_self (a : F) : a ^ Fintype.card F = a :=
  FiniteField.pow_card a

omit [DecidableEq F] in
/-- Frobenius 的非零元形式：`a ≠ 0 ⟹ a^(q−1) = 1`。 -/
theorem gfp_pow_card_sub_one_eq_one (a : F) (ha : a ≠ 0) :
    a ^ (Fintype.card F - 1) = 1 :=
  FiniteField.pow_card_sub_one_eq_one a ha

omit [DecidableEq F] in
/-- 由定理二得到的 `a^q = a`（展示分解与 Frobenius 的等价性）。 -/
theorem gfp_pow_card_eq_self_of_prod (a : F) : a ^ Fintype.card F - a = 0 := by
  have h := gfp_eval_X_pow_card_sub_X_eq_zero (F := F) a
  simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using h

/-! ## 定理五：商环 / 不可约多项式构造扩域 -/

omit [Fintype F] [DecidableEq F] in
/-- **不可约多项式的商环是域**：`[Fact p.Irreducible]` 下 `AdjoinRoot p` 是域
（mathlib 实例 `AdjoinRoot.instField`；`p` 不可约作为**显式假设**传入）。

诚实标注（**形式调整**）：原稿写作 `theorem ... : Field (AdjoinRoot p)`，但 `Field` 是
**类型类（Type 层）而非 `Prop`**，`theorem` 只接受命题——已改为 `def`（语义不变，
仍是「给出该实例」），否则报 `type of theorem ... is not a proposition`。

**缺口已闭合**：`Fintype (AdjoinRoot p)` 与基数 `#(AdjoinRoot p) = #F ^ p.natDegree`
由 **`RealAdjoinRootCard`**（`arc_fintype_powerBasis` / `arc_card_adjoinRoot`）补齐；
本文件不再标注该缺口「未做」。 -/
def gfp_adjoin_root_field (p : F[X]) [Fact (Irreducible p)] : Field (AdjoinRoot p) :=
  inferInstance

omit [Fintype F] [DecidableEq F] in
/-- 商环的乘法单位（非零元可逆）：不可约 `p` 下 `x ≠ 0 ⟹ x·x⁻¹ = 1`（域的推论）。 -/
theorem gfp_adjoin_root_mul_inv_cancel (p : F[X]) [Fact (Irreducible p)]
    (x : AdjoinRoot p) (hx : x ≠ 0) : x * x⁻¹ = 1 :=
  mul_inv_cancel₀ hx

end Lattice
