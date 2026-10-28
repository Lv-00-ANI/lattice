import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealConstraintEdit
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lift.TotalLoss

open Lattice.Lift.SymbolToWeightCorrectness
/-!
# D1-5：编辑的不变量 —— 从「谓词是否保持」到「量如何变换」

对应调研报告 `_deep_out/D_D1-5.md` 的 T1–T8。

## 0. ⚠⚠ 本文件对报告的**实质性订正**（最重要的一节）

⭐ **报告 T5′（`list_append_eq_zipwith_add_iff_length`）是【假命题】**，
本文件**证否**它并给出**正确**的充要条件。

报告断言：

    `a ++ dw = a.zipWith (· + ·) dw  ⟺  a.length = dw.length`     （**假**）

反例：`a = [1]`、`dw = [5]`（**长度恰好对齐**）⟹ 左端 `[1,5]`、右端 `[6]`。**不相等**。
⭐ 原因是报告把 `zipWith (·+·)` 的语义（**逐坐标相加**，`1+5=6`）与
`++`（**拼接**，`[1] ++ [5] = [1,5]`）混为一谈。长度对齐是**必要**条件，**远非充分**。

⇒ 本文件给出正确的充要条件（`append_eq_zipWith_add_iff`）：

    `a ++ dw = a.zipWith (· + ·) dw  ⟺  a = [] ∧ dw = []`

⭐ **这个订正强化了报告的结论**：报告想说的是「两侧编辑载体不同构」——
本文件证明它们**几乎处处不同构**（只有平凡情形一致），比报告设想的**更尖锐**。

## 1. 本文件的中心判断（与报告一致，并加以机器化）

报告的承重诊断是：既有编辑保持律**全部是 `Prop → Prop` 的布尔保持**，
而 `_S-04.zeroing_blind_to_length` 已证明这个维度**饱和**（连「有几条约束」都看不见）。
⇒ 本文件按报告的三个方向交付：

| 方向 | 报告条目 | 本文件交付 |
|:--|:--|:--|
| **① 量（数值）怎么变** | T1 / T6′ | `edit_regime_gap_exact`、`edit_regime_agree_iff` |
| **② 析取式 / 反驳可能** | T2 / T6′ | `edit_breaks_zeroing_generically`、`edit_regime_short_input_report_false` |
| **③ 充要条件（判据 4）** | T2′ / T5 | `edit_preserves_zeroing_iff_at_solution`、`append_eq_zipWith_add_iff` |

## 2. 其它订正（详见 `_prove_out/P_D1-5.md`）

- ⭐⭐ **报告 T6′（保守版）也是【假命题】**：它断言「`x.length ≤ a.length` ⟹
  两种编辑给出同一残差」。反例：`a = [1]`、`dw = [1]`、`x = [1]`（假设全满足）
  ⟹ 左 `1`、右 `2`。真因：它漏掉了**承重**条件 `dot dw x = 0`。
  正确形式见 `edit_regime_agree_iff` / `edit_regime_agree_of_dot_zero`，
  反例见 `edit_regime_short_input_report_false`。
- **T5 第二条的 `∀ b : Int` 量词多余**：`b` 两侧逐字相同，不承重。
- **T1 第一条（残差偏移）逐字就是** `editConstraint_semantic_pointwise` 的改写，
  只当引理，不作非平凡性证据（与报告预判一致）。
- **T1 第二条的报告草案用 `Finset.sum`**，而 `RealConstraintEdit.lean:184-188` 已登记
  `Finset.sum_singleton` 在该 mathlib 版本**不存在** ⟹ 本文件改用 `List` 形式。
- **T4 第三条被报告判为 rfl 空壳**（`applySymEdit cs n e : ConstraintSet`，
  故 `activated_closure_iff_zeroFixing` 代入即得）⟹ 本文件**不复证**，
  改交付 T4 第一条（激活下零点判定，跨模块）。

## 3. 非平凡性自查（按任务书四条判据）

| 定理 | 判据 1 消融 | 判据 2 反驳 | 判据 3 跨模块 | 判据 4 量化 |
|:--|:-:|:-:|:-:|:-:|
| `append_eq_zipWith_add_iff` (T5 订正) | ✅ | ✅✅ | ✅✅ | ✅✅ |
| `append_eq_zipWith_add_iff_length_necessary` | ✅ | — | ✅ | ✅ |
| `edit_regime_gap_exact` (T6′) | ✅ | ✅ | ✅✅ | ✅ |
| `edit_regime_agree_iff` (T6′′) | ✅ | ✅ | ✅✅ | ✅✅ |
| `edit_regime_short_input_report_false` (T6′ 反例) | ✅ | ✅✅ | ✅✅ | — |
| `edit_regime_agree_of_dot_zero` | ✅✅ | ✅ | ✅✅ | ✅ |
| `edit_regime_disagree_witness` | ✅ | ✅✅ | ✅✅ | — |
| `totalLoss_edit_exact_quadratic` (T1) | ✅ | ✅ | ✅ | ✅✅ |
| `edit_preserves_zeroing_iff_at_solution` (T2′) | ✅✅ | ✅ | ✅ | ✅✅ |
| `edit_breaks_zeroing_generically` (T2) | ✅ | ✅✅ | ✅ | — |
| `edit_preserves_witness_if_untouched` (T3) | ✅ | ✅ | — | — |
| `edited_activated_zero_iff_residual` (T4-1) | ✅ | ✅ | ✅✅ | ✅ |

⚠ 本文件**无** `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

namespace Lattice.Lib.Editing.RealEditInvariantCatalog
/-! ## §一、`List` / `zipWith` 地基：T5 的**订正**

`dot` 是 `foldl` + `zip`（`ConvertVectorLinear:31`），`zip` 在长度不等时**截断**。
符号侧编辑 `applySymEdit` 用 `++`（**拼接**，`RealConstraintEdit:105`），
权重侧编辑 `editLayer` 用 `zipWith (·+·)`（**逐坐标相加**，`RealEditSemantics:105`）。
⇒ 「两侧编辑载体是否同构」精确地归结为一条 `List` 等式。本节把它**彻底解决**。 -/

/-- **`zipWith` 的长度恰为两侧长度之 min**
（Lean core `Init/Data/List/Nat/TakeDrop.lean:561` 的 `List.length_zipWith`）。 -/
lemma zipWith_add_length (a dw : List Int) :
    (a.zipWith (· + ·) dw).length = min a.length dw.length :=
  List.length_zipWith (· + ·) a dw

/-- ⭐⭐ **T5 订正（主定理）：两侧编辑载体同构的【精确】充要条件**。

    `a ++ dw = a.zipWith (· + ·) dw  ⟺  a = [] ∧ dw = []`

⭐⭐ **为什么报告的长度条件是错的**：`zipWith (·+·)` 是**逐坐标相加**
（`[1].zipWith (·+·) [5] = [6]`），而 `++` 是**拼接**（`[1] ++ [5] = [1,5]`）。
长度对齐**必要但不充分** —— `a = [1]`、`dw = [5]` 就是反例。

⭐ **非平凡性**：
- **判据 2（反驳可能）**：`a = [1]`、`dw = [5]`（**长度对齐**，故直接反驳报告）
  ⟹ `[1,5] ≠ [6]`；
- **判据 4（量化）**：给出**充要条件**，右端完全可判定；
- **判据 3（跨模块）**：把 `RealConstraintEdit`（`++` 线）与
  `RealEditSemantics`（`zipWith` 线）**第一次**放进同一命题。

⭐ **`←` 方向**：`a = [] ∧ dw = []` 时两端都是 `[]`（`rfl`）。
⭐ **`→` 方向**：由长度得 `a.length + dw.length = min a.length dw.length`
（`zipWith` 取 min），故两者皆 `0`。 -/
theorem append_eq_zipWith_add_iff (a dw : List Int) :
    a ++ dw = a.zipWith (· + ·) dw ↔ a = [] ∧ dw = [] := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [List.length_append, zipWith_add_length] at hlen
    have ha : a.length = 0 := by omega
    have hd : dw.length = 0 := by omega
    exact ⟨List.eq_nil_of_length_eq_zero ha, List.eq_nil_of_length_eq_zero hd⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- ⭐ **T5 报告版里**对**的那一半**：长度对齐是**必要**条件。

报告把「必要」当成了「充要」。本条保留正确的必要方向，
并由 `append_ne_zipWith_add_witness` 说明它**不充分**。 -/
theorem append_eq_zipWith_add_iff_length_necessary (a dw : List Int)
    (h : a ++ dw = a.zipWith (· + ·) dw) : a.length = dw.length := by
  have hlen := congrArg List.length h
  rw [List.length_append, zipWith_add_length] at hlen
  omega

/-- ⭐⭐ **T5 判据 2（直接反驳报告的具体见证）**：

取 `a = [1]`、`dw = [5]` —— ⚠ **长度恰好对齐**（`1 = 1`），
按报告应为相等，实际给出 `[1,5] ≠ [6]`。

⇒ 这不是「证不出来」，是**报告的命题为假**。 -/
theorem append_ne_zipWith_add_witness :
    ∃ (a dw : List Int), a.length = dw.length ∧ a ++ dw ≠ a.zipWith (· + ·) dw :=
  ⟨[1], [5], rfl, by decide⟩

/-- ⭐ **T5 的语义读数（跨模块，判据 3）**：两侧编辑线在**长度**上分道扬镳 ——
追加型把长度**增大** `dw.length`，截断型把长度**钉死**为 `a.length`。

⭐ 这是「两侧编辑载体不同构」在**可计算量**上的形式。 -/
theorem edit_carriers_diverge_on_length (a dw : List Int) (hdw : dw ≠ []) :
    (a ++ dw).length ≠ (a.zipWith (· + ·) dw).length := by
  rw [List.length_append, zipWith_add_length]
  have : 0 < dw.length := List.length_pos_of_ne_nil hdw
  omega

/-- ⭐ **T5 推论（记录层）**：`VectorConstraint` 上的同一命题。

报告原陈述带 `∀ b : Int` 量词。本文件证明它**完全多余** ——
`a ++ dw` 与 `a.zipWith (·+·) dw` 只改 `a` 字段，`b` 两侧**逐字相同**。 -/
theorem vecConstraint_append_eq_zipWith_iff (a dw : List Int) (b : Int) :
    ({ a := a ++ dw, b := b } : VectorConstraint) = ⟨a.zipWith (· + ·) dw, b⟩
      ↔ a = [] ∧ dw = [] := by
  constructor
  · intro h
    exact (append_eq_zipWith_add_iff a dw).mp (congrArg VectorConstraint.a h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## §二、`dot` 地基引理（T1/T6′ 承重件） -/

/-- **`dot` 与空表的零性**：`dot a [] = 0`（`zip` 截断到空）。

⚠ 与 `_S-01.dot_nil_right_s01` / `RealSymbolToWeightWidened.dot_nil_right_s01`
同名同义；本文件**自证**以保持自包含，并在报告里登记这条**已知重复**。 -/
lemma dot_nil_right (a : List Int) : dot a [] = 0 := by
  simp [dot]

/-- **`dot` 与 `++` 的分解（自包含重述）**。
⚠ 与 `RealConstraintEdit.dot_append_sub` 逐字相同；重述使引理链自包含，
并在报告里登记这条**已知重复**。 -/
lemma dot_append_sub (a b x : List Int) :
    dot (a ++ b) x = dot a x + dot b (x.drop a.length) :=
  -- qualified on purpose: this is a restatement of the lemma in RealConstraintEdit,
  -- and after the de-prime pass the two share a short name, so the bare call would
  -- resolve to THIS lemma and make it self-recursive (termination then fails).
  Lattice.dot_append_sub a b x

/-- ⭐ **`dot` 只看第二个参数的**前缀**（**长度版**）：若 `a.length ≤ b.length`，
则追加在 `b` 之后的尾部**不被 `zip` 看到**：`dot a (b ++ c) = dot a b`。

⚠ **长度前提不可删（这是本文件踩过的坑）**：`dot` 用 `zip` 截断到**较短**一侧，
故无前提时命题**为假** —— `a = [1]`、`b = []`、`c = [5]`：
左端 `dot [1] [5] = 5`、右端 `dot [1] [] = 0`，`5 ≠ 0`。
⚠ 报告**未**要求本条；它是 `dot_append_of_length_eq` 的必需件。 -/
lemma dot_append_right_of_le (a b c : List Int) (h : a.length ≤ b.length) :
    dot a (b ++ c) = dot a b := by
  have hzip : a.zip (b ++ c) = a.zip b := by
    induction a generalizing b with
    | nil => rfl
    | cons p ps ih =>
        cases b with
        | nil => simp at h
        | cons q qs =>
            have h' : ps.length ≤ qs.length := by simpa using h
            -- `simp only` 已把首分量 `p = p` 自动关闭，只剩尾分量。
            simpa only [List.cons_append, List.zip_cons_cons, List.cons.injEq, true_and]
              using ih qs h'
  unfold dot
  rw [hzip]

/-- ⭐ **`dot` 在长度对齐下的坐标对齐律**（T6′ 与 T1 的承重件）：

    `dot (a ++ b) (x ++ y) = dot a x + dot b y`（当 `a.length = x.length`）

⚠ **长度前提不可删（判据 1）**：删掉后取 `a = [1]`、`b = []`、`x = []`、`y = [7]`：
左端 `dot [1] [7] = 7`，右端 `dot [1] [] + dot [] [7] = 0` ⟹ **结论为假**。 -/
lemma dot_append_of_length_eq (a b x y : List Int) (h : a.length = x.length) :
    dot (a ++ b) (x ++ y) = dot a x + dot b y := by
  rw [dot_append_sub a b (x ++ y)]
  have hdrop : (x ++ y).drop a.length = y := List.drop_left' h.symm
  rw [hdrop, dot_append_right_of_le a x y (le_of_eq h)]

/-! ## §三、T6′：截断型 vs 追加型的**语义差异**量化（数值类，判据 3+4 双落点）

⭐ 报告判据：这是**最有价值的跨模块落点** —— 连接 `RealConstraintEdit.dot_append_sub`
（符号侧）与 `RealEditSemantics.dot_zipWith_add_of_length`（权重侧），
**两文件互不 import**（实测两文件 import 集相同但互不引用）。 -/

/-- ⭐⭐ **T6′ 主定理：两种编辑在同一点的输出【差】的精确闭式**。

    `dot (a ++ dw) x - dot (a.zipWith (·+·) dw) x = dot dw (x.drop a.length) - dot dw x`
      （当 `a.length = dw.length`）

⭐ **判据 4**：右端是**精确闭式**（不是不等式、不是存在性）。
⭐ **判据 3**：左半来自 `RealConstraintEdit.dot_append_sub`（符号侧 `++` 线），
右半来自 `RealEditSemantics.dot_zipWith_add_of_length`（权重侧 `zipWith` 线）——
**全仓此前没有任何定理同时引用这两条**。

⚠ **长度前提不可删**：`zipWith` 的分配律在截断时为**假**
（`a = []`、`dw = [1]`、`x = [1]` ⟹ `0 ≠ 1`，`RealEditSemantics.lean:193` 已登记）。 -/
theorem edit_regime_gap_exact (a dw x : List Int) (h : a.length = dw.length) :
    dot (a ++ dw) x - dot (a.zipWith (· + ·) dw) x
      = dot dw (x.drop a.length) - dot dw x := by
  rw [dot_append_sub, dot_zipWith_add_of_length a dw x h]
  ring

/-- ⭐⭐ **T6′′（判据 4）：两种编辑在给定点一致的【充要条件】**。

由 `edit_regime_gap_exact`，差额恰为 `dot dw (x.drop a.length) - dot dw x`。
两者相等 **⟺** 该差额为零：

    `dot (a++dw) x = dot (a.zipWith (·+·) dw) x  ⟺  dot dw (x.drop a.length) = dot dw x`

⭐ **判据 4**：这是**充要条件**，右端**可计算**。

⚠⚠ **重要订正**：报告推荐的 T6′ 保守版断言「`x.length ≤ a.length` ⟹ 两者相等」。
**该断言为假**。反例（长度对齐 `a.length = dw.length = 1`、`x.length = 1 ≤ 1`）：
`a = [1]`、`dw = [1]`、`x = [1]` ⟹ 左 `dot [1,1] [1] = 1`、右 `dot [2] [1] = 2`，`1 ≠ 2`。
⭐ 真因：`x.length ≤ a.length` 只保证 `x.drop a.length = []`，**不保证** `dot dw x = 0`。
⇒ 正确的充分条件是 **`dot dw x = 0`**（见 `edit_regime_agree_of_dot_zero`）。 -/
theorem edit_regime_agree_iff (a dw x : List Int) (h : a.length = dw.length) :
    dot (a ++ dw) x = dot (a.zipWith (· + ·) dw) x
      ↔ dot dw (x.drop a.length) = dot dw x := by
  have hgap := edit_regime_gap_exact a dw x h
  constructor
  · intro heq; omega
  · intro heq; omega

/-- ⭐ **T6′′ 的正面读数（正确版的「短输入」定理）**：
若 `x.length ≤ a.length` **且** `dot dw x = 0`，则两种编辑在该点给出同一残差。

⭐ 这是报告 T6′ 的**订正**：报告漏掉了 `dot dw x = 0`，而它是**承重**的
（反例见 `edit_regime_short_input_report_false`）。 -/
theorem edit_regime_agree_of_dot_zero (a dw x : List Int)
    (hlen : a.length = dw.length) (hx : x.length ≤ a.length) (hz : dot dw x = 0) :
    dot (a ++ dw) x = dot (a.zipWith (· + ·) dw) x := by
  rw [edit_regime_agree_iff a dw x hlen, List.drop_eq_nil_of_le hx, dot_nil_right, hz]

/-- ⭐⭐ **判据 2：报告 T6′ 保守版的直接反例（机器可验）**。

`a = [1]`、`dw = [1]`（**长度对齐**）、`x = [1]`（**`x.length = 1 ≤ a.length = 1`**）——
报告的假设全部满足，但两种编辑给出 `1 ≠ 2`。

⇒ 报告 T6′ 是**假命题**；真因是它漏掉了 `dot dw x = 0`。 -/
theorem edit_regime_short_input_report_false :
    ∃ (a dw x : List Int), a.length = dw.length ∧ x.length ≤ a.length
      ∧ dot (a ++ dw) x ≠ dot (a.zipWith (· + ·) dw) x :=
  ⟨[1], [1], [1], rfl, by decide, by decide⟩

/-- ⭐ **T6′ 的边界读数（判据 2）**：差异**确实**可以发生。

⭐ **见证**：`a = []`、`dw = [1]`、`x = [1]` ⟹ 左 `dot [1] [1] = 1`、
右 `dot [] [1] = 0`，`1 ≠ 0`。 -/
theorem edit_regime_disagree_witness :
    ∃ (a dw x : List Int), dot (a ++ dw) x ≠ dot (a.zipWith (· + ·) dw) x :=
  ⟨[], [1], [1], by decide⟩

/-! ## §四、T1：损失值的**精确**变换律（数值类）

报告判断：零化律（`totalLoss = 0`）**看不见非零时的值**。
`TotalLoss.totalLoss_eq_zero_iff_allSatisfied`（`TotalLoss.lean:103`）只说
「`= 0` ⟺ 全满足」，对 `≠ 0` 时的**值**只字未提。本节给**精确等式**。

⚠ **报告草案的技术问题（已订正）**：报告写成 `∑ i in Finset.range n, ...`，
而 `RealConstraintEdit.lean:184-188` 已诚实登记 `Finset.sum_singleton` 在该
mathlib 版本**不存在**。⇒ 本文件改用与 `totalLoss` 实现形状一致的 `List` 形式
（`sqSum` 是 `List.foldr`，`TotalLoss.lean:44`）。 -/

/-- 编辑后第 `i` 行的**残差**（`VectorConstraintSat` 的左端）。 -/
def residual (cs : ConstraintSet) (x : List Int) (i : Nat) : Int :=
  dot (cs.getD i ⟨[], 0⟩).a x + (cs.getD i ⟨[], 0⟩).b

/-- 编辑在第 `i` 行上的 **δ**（可计算闭式，**右端不出现编辑后的约束集**）。 -/
def deltaAt (cs : ConstraintSet) (e : SymEdit) (x : List Int) (i : Nat) : Int :=
  dot (e.daw i) (x.drop (cs.getD i ⟨[], 0⟩).a.length) + e.db i

/-- ⭐ **T1 引理（`residual`/`deltaAt` 形式）：残差的**精确**偏移律**。

⚠ **诚实登记**：本条**逐字就是** `RealConstraintEdit.editConstraint_semantic_pointwise`
（`:288-292`，已证）的改写（`cs' := applySymEdit cs n e`）。
⇒ 本文件**只把它当引理**，**不**作为非平凡性证据。 -/
theorem residual_edit_eq (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Fin n)
    (x : List Int) :
    residual (applySymEdit cs n e) x i.val = residual cs x i.val + deltaAt cs e x i.val := by
  unfold residual deltaAt
  rw [applySymEdit_getD cs n e i.val i.isLt, dot_append_sub]
  ring

/-- ⭐ **`getD` 与 `map` 的交换（`List.range` 特化）**：
`i < n` 时 `((List.range n).map g).getD i d = g i`。

⭐ 这是 `totalLoss_edit_eq` 的技术内核：它把 `List.map` 之下的 `getD` 归约成
**逐项形态** `g i`，从而可以套用 `applySymEdit_getD`。

⚠ Lean core / Batteries **没有** `List.getD_map`（实测全仓搜索 0 命中），故本文件自证。 -/
lemma list_getD_map_range {β : Type} (g : Nat → β) (n i : Nat) (d : β) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hi), List.getElem_range]
  rfl

/-- ⭐ **逐行辅助引理**：编辑后第 `i` 行（`i < n`）的**层输出**等于
`residual cs x i + deltaAt cs e x i`。

⚠ 本引理是 `totalLoss_edit_eq` 的技术内核：它在 `applySymEdit` **尚未展开**时
用 `applySymEdit_getD` 取出第 `i` 项，避免 `List.map_map` 把 `getD` 埋进 `Function.comp`。 -/
lemma layerOut_applySymEdit (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat)
    (hi : i < n) (x : List Int) :
    LayerOut (convertVec ((applySymEdit cs n e).getD i ⟨[], 0⟩)) x
      = residual cs x i + deltaAt cs e x i := by
  rw [applySymEdit_getD cs n e i hi]
  simp only [LayerOut, convertVec, residual, deltaAt]
  rw [dot_append_sub]
  ring

/-- ⭐⭐ **T1 主定理（总损失的精确变换律）**：

    `totalLoss (applySymEdit cs n e) x
       = sqSum ((List.range n).map (fun i => residual cs x i + deltaAt cs e x i))`

⚠ **注意 `sqSum` 自带平方**（`TotalLoss.lean:44`：`sqSum xs = (xs.map (·^2)).foldr ...`），
故右端的 `map` 里**不写** `^2` —— 写上是**双重平方**（本文件初版踩过这个坑）。

⭐ **它比零化律多说什么**：`totalLoss_eq_zero_iff_allSatisfied` 只在 `= 0` 时给信息；
本条对**任意**残差给**等值** —— 编辑后的总损失**逐行**由「原残差 + δ」算出，
**右端不出现编辑后的约束集** ⟹ 可**计算**（判据 4）。

⭐ **判据 4（量化）**：这是**精确等式**，不是不等式、不是存在性。

⚠ ⭐ **本条不需要 `n = cs.length`**：`applySymEdit` 的输出长度**恒为 `n`**
（`applySymEdit_length`），而 `totalLoss` 只依赖**输出列表本身**。
报告以为需要长度对齐 —— 那是因为它把右端写成了「对 `cs` 的逐行求和」。
本文件把右端也写成 `range n`，于是**长度假设被完全消掉**（这是对报告的加强）。 -/
theorem totalLoss_edit_eq (cs : ConstraintSet) (n : Nat) (e : SymEdit) (x : List Int) :
    totalLoss (applySymEdit cs n e) x
      = sqSum ((List.range n).map (fun i => residual cs x i + deltaAt cs e x i)) := by
  unfold totalLoss
  -- 第一步：`applySymEdit cs n e = (range n).map g`（定义级），
  -- `compileToLayer l = l.map convertVec`，故两层 `map` 合成一层，
  -- 再用 `list_getD_map_range` 把 `getD` 归约成**逐项形态** `g i`。
  have hmap : (compileToLayer (applySymEdit cs n e)).map (fun l => LayerOut l x)
      = (List.range n).map (fun i =>
          LayerOut (convertVec ((applySymEdit cs n e).getD i ⟨[], 0⟩)) x) := by
    unfold compileToLayer
    rw [applySymEdit]
    simp only [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < n := List.mem_range.mp hi
    have hgd : ((List.range n).map (fun i =>
        { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
          b := (cs.getD i ⟨[], 0⟩).b + e.db i })).getD i
          (⟨[], 0⟩ : VectorConstraint)
        = { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
            b := (cs.getD i ⟨[], 0⟩).b + e.db i } :=
      list_getD_map_range _ n i _ hi'
    rw [hgd]
    rfl
  rw [hmap]
  -- 现在两侧都是 `sqSum ((range n).map F)`，逐项改写 `F` 即可。
  apply congrArg sqSum
  apply List.map_congr_left
  intro i hi
  rw [layerOut_applySymEdit cs n e i (List.mem_range.mp hi) x]

/-- ⭐⭐ **T1 推论：编辑后总损失的**精确二次展开**。

    `totalLoss cs' x = Σ_i (rᵢ² + 2·rᵢ·δᵢ + δᵢ²)`

⚠ **为什么用 `List.sum` 而非 `sqSum`**：`sqSum` 自带平方
（`TotalLoss.lean:44`），若右端再用 `sqSum` 就会**双重平方**。
展开式已经含有 `rᵢ²` 与 `δᵢ²`，故必须用**不平方的**求和 `List.sum`。

⭐ 这是报告 T1 第二条要求的「精确二次展开」，用 `List` 形式落地。
⭐ **判据 4**：完全可计算。 -/
theorem totalLoss_edit_exact_quadratic (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (x : List Int) :
    totalLoss (applySymEdit cs n e) x
      = ((List.range n).map (fun i =>
          (residual cs x i) ^ 2 + 2 * (residual cs x i) * (deltaAt cs e x i)
            + (deltaAt cs e x i) ^ 2)).sum := by
  rw [totalLoss_edit_eq]
  -- `sqSum xs = (xs.map (·^2)).foldr (·+·) 0`，而 `List.sum xs = xs.foldr (·+·) 0`
  -- （`TotalLoss.lean:44` 与 core `List.sum`）。故先把 `sqSum` 展开成 `map (·^2)` 形态，
  -- 再逐项用 `(r+δ)^2 = r²+2rδ+δ²` 改写。
  unfold sqSum
  rw [List.sum_eq_foldr]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  show (residual cs x i + deltaAt cs e x i) ^ 2
      = residual cs x i ^ 2 + 2 * residual cs x i * deltaAt cs e x i + deltaAt cs e x i ^ 2
  ring

/-- ⭐ **T1 的零化读数（与既有 `totalLoss_eq_zero_iff_allSatisfied` 的接口）**：

编辑后总损失为零 **⟺** 每一行的「原残差 + δ」为零。

⭐ 这是 T2′ 的技术内核，也是「零化律看不见的那一层」与「看得见的那一层」的桥。 -/
theorem totalLoss_edit_eq_zero_iff (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (x : List Int) :
    totalLoss (applySymEdit cs n e) x = 0
      ↔ ∀ i ∈ List.range n, residual cs x i + deltaAt cs e x i = 0 := by
  rw [totalLoss_edit_eq, sqSum_eq_zero_iff]
  constructor
  · intro h i hi
    have := h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
    simpa using this
  · intro h v hv
    rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
    simpa using h i hi

/-- ⭐⭐ **T2′ 主定理（零化律失效域的充要条件，判据 4）**。

在「编辑前该点已被零化」的前提下：

    `totalLoss cs' x = 0  ⟺  ∀ i < n, δᵢ = 0`

⭐⭐ **为什么 `hx` 是承重的（判据 1 消融）**：删掉 `hx`，取 `cs = [⟨[1],0⟩]`、
`x = [1]`（原残差 `1 ≠ 0`）、`n = 1`、`e.db 0 = -1`（`δ = -1 ≠ 0`）：
编辑后残差 `1 + (-1) = 0` ⟹ `totalLoss cs' x = 0` **成立**，
而 `∀ i, δᵢ = 0` **为假** ⟹ **`↔` 的反向失败，结论变假**（不是证不出来）。

⭐ **判据 4（量化）**：右端是**逐行可计算**的等式 `δᵢ = 0`。
⭐ **诚实标注**：报告 T2′ 的右端写成 `∀ i : Fin n`；本文件用 `∀ i < n`（与 `range` 配套），
二者等价。⚠ 报告的 `x.drop` 项被**逐字沿用**（它是 `deltaAt` 的定义体）——这正是
`dot` 的 `zip` 截断语义**真正进入命题**的地方。 -/
theorem edit_preserves_zeroing_iff_at_solution (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (x : List Int) (hx : totalLoss cs x = 0) :
    totalLoss (applySymEdit cs n e) x = 0 ↔ ∀ i < n, deltaAt cs e x i = 0 := by
  rw [totalLoss_edit_eq_zero_iff]
  -- 由 `hx` 与 `totalLoss_eq_zero_iff_allSatisfied` 得 `AllSatisfied cs x`。
  -- ⚠ 关键：`residual cs x i = 0` 对**一切** `i` 成立，**无需** `i < cs.length`：
  --   - `i < cs.length` 时，`cs.getD i ⟨[],0⟩ = cs[i] ∈ cs`，由 `AllSatisfied` 即得；
  --   - `i ≥ cs.length` 时，`getD` 返回默认值 `⟨[],0⟩`，其残差 `dot [] x + 0 = 0`。
  have hres : ∀ i, residual cs x i = 0 := by
    intro i
    rcases lt_or_ge i cs.length with hi | hi
    · have hs : AllSatisfied cs x := (totalLoss_eq_zero_iff_allSatisfied cs x).mp hx
      have hsat := hs cs[i] (List.getElem_mem hi)
      unfold residual
      rw [List.getD_eq_getElem _ _ hi]
      exact hsat
    · have hd : cs.getD i ⟨[], 0⟩ = ⟨[], 0⟩ :=
        List.getD_eq_default _ _ (by simpa using hi)
      unfold residual
      rw [hd]
      simp [dot]
  constructor
  · intro h i hi
    have := h i (List.mem_range.mpr hi)
    rw [hres i] at this
    simpa using this
  · intro h i hi
    rw [hres i, h i (List.mem_range.mp hi)]
    simp

/-! ## §五、T2：零化律的**失效域**（反驳可能 + 析取式）

报告判断：编辑**不**保持零化律，且反例必须**不是**靠 `zip` 截断造出来的。
本节给**机器可验**的见证。 -/

/-- ⭐⭐ **T2 主定理：零化律的失效见证（判据 2）**。

存在具体编辑 `e` 与输入 `x`，使：

1. 编辑前总损失为零（`totalLoss cs x = 0`）；
2. 编辑后总损失**严格为正**（`0 < totalLoss cs' x`）；
3. ⚠⚠ 编辑的支撑**非空**（`e.S.Nonempty`）—— 即「编辑确实做了事」，不是空转；
4. ⚠ **不是靠 `zip` 截断造出来的**：见证取 `e.daw 0 = []`（**不追加任何系数**），
   只改偏置 `e.db 0 = 1`。故 `dot` 的截断**完全未参与**。

⭐ **见证**：`cs = [⟨[1], 0⟩]`、`x = [0]`、`n = 1`、`e = ⟨{0}, fun _ => [], fun _ => 1⟩`。
- 编辑前残差 `dot [1] [0] + 0 = 0` ⟹ `totalLoss cs x = 0` 成立
- `x.drop 1 = []`，δ `= dot [] [] + 1 = 1`；编辑后残差 `0 + 1 = 1` ⟹ `totalLoss = 1 > 0` 成立

⭐ **判据 2（反驳可能）**：这就是**具体反例** —— 零化律**不**在编辑下保持。 -/
theorem edit_breaks_zeroing_generically :
    ∃ (cs : ConstraintSet) (n : Nat) (e : SymEdit) (x : List Int),
      e.S.Nonempty
        ∧ totalLoss cs x = 0
        ∧ 0 < totalLoss (applySymEdit cs n e) x := by
  refine ⟨[{ a := [1], b := 0 }], 1, ⟨{0}, fun _ => [], fun _ => 1⟩, [0], ?_, ?_, ?_⟩
  · exact ⟨0, Finset.mem_singleton_self 0⟩
  · -- 编辑前：残差 `dot [1] [0] + 0 = 0` ⟹ 总损失零
    unfold totalLoss sqSum compileToLayer LayerOut convertVec dot
    simp [List.map, List.foldr]
  · -- 编辑后：`totalLoss (applySymEdit ..) [0] = sqSum [(0+1)^2] = 1 > 0`
    rw [totalLoss_edit_eq]
    -- `List.range 1 = [0]`：用 `List.range_succ` 展开（core 无 `range_one`）。
    simp only [Nat.reduceAdd, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, sqSum, List.foldr, residual, deltaAt, dot,
      List.drop, List.zip, List.foldl, zero_add, List.append_nil]
    norm_num

/-- ⭐ **T3 主定理（析取式保持律）：未受编辑触碰的行保持原满足性**。

零化律是 `∀` 式（**每一行**都要保持）；本定律是**逐行**式：
只要某行**不在支撑内**，它的满足性就**逐字保持** —— 编辑对它是**恒等**。

⭐ **判据 1（消融）**：删掉 `hi : i.val ∉ e.S`，取 `e` 使 `daw i ≠ []`，
则该行**确实改变**（`RealConstraintEdit.offSupport_is_load_bearing` 已给具体见证）
⟹ **结论变假**。

⚠ **诚实标注（rfl 风险）**：报告预判本条「近 rfl」—— 因为
`applySymEdit_off_support_eq`（`RealConstraintEdit.lean:420`，已证）已给出
「支撑外的行**逐字相等**」，而 `VectorConstraintSat` 是记录字段的函数，
由前者 `congrArg` 立得。⇒ 本文件**保留它作为引理**（它使 T3 的语义内容可见），
但**不**把它计为非平凡性证据（与报告一致）。 -/
theorem edit_preserves_witness_if_untouched (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (hsup : ∀ i : Nat, i ∉ e.S → e.daw i = [] ∧ e.db i = 0)
    (i : Fin n) (hi : i.val ∉ e.S) (x : List Int)
    (hsat : VectorConstraintSat (cs.getD i.val ⟨[], 0⟩) x) :
    VectorConstraintSat ((applySymEdit cs n e).getD i.val ⟨[], 0⟩) x := by
  rw [applySymEdit_off_support_eq cs n e hsup i hi]
  exact hsat

/-! ## §六、T4：激活下的零点判定（跨模块，判据 3）

⭐ 报告判断：这是**跨模块**落点 —— 连接 `RealConstraintEdit`（符号侧编辑）
与 `RealSymbolToWeightNonlinear` / `RealCompileExtractClosed`（零点结构），
**三者当前互不 import**（实测 `RealConstraintEdit.lean:1-5` 不引用后两者）。

⚠ **报告 T4 第三条被否掉**：`activated_closure_iff_zeroFixing`
（`RealCompileExtractClosed.lean:323`）对**任意** `ConstraintSet` 全称量化，
而 `applySymEdit cs n e : ConstraintSet` ⟹ **代入即得**，
证明体应为 `exact activated_closure_iff_zeroFixing act` ⟹ **rfl 空壳**。
⇒ 本文件**不复证**它，改交付**第一条**（激活下的逐行零点判定）。 -/

/-- ⭐⭐ **T4 主定理：编辑 + 激活的完整链条上，零点判定被 δ 精确钉住**。

在 `ZeroFixing act` 下：

    `actAllZero act (applySymEdit cs n e) x  ⟺  ∀ i < n, residual cs x i + δᵢ = 0`

⭐ **判据 3（跨模块）**：本条**首次**把三个互不 import 的模块放进同一命题 ——
`RealConstraintEdit`（`applySymEdit`，符号侧编辑）、
`RealSymbolToWeightNonlinear`（`ZeroFixing`，激活的零点结构）、
`RealCompileExtractClosed`（`actAllZero`/`actLayerOut`，列表级激活语义）。

⭐ **判据 1（消融）**：删掉 `hσ : ZeroFixing act`，取 `act = reluZ`，
由 `reluZ_not_zeroFixing`（`RealSymbolToWeightNonlinear.lean:79`）知命题**为假**
（`RealCompileExtractClosed.activated_loop_breaks` 已给机器见证）。

⭐ **判据 4（量化）**：右端是**逐行可计算**的线性等式。 -/
theorem edited_activated_zero_iff_residual (act : ℤ → ℤ) (hσ : ZeroFixing act)
    (cs : ConstraintSet) (n : Nat) (e : SymEdit) (x : List Int) :
    actAllZero act (applySymEdit cs n e) x
      ↔ ∀ i < n, residual cs x i + deltaAt cs e x i = 0 := by
  -- `actAllZero act cs' x ↔ ∀ v ∈ actLayerOut act cs' x, v = 0`
  --   `↔ ∀ i ∈ range n, act (residual' i) = 0`   [`actLayerOut` 展开 + `map_map`]
  --   `↔ ∀ i ∈ range n, residual' i = 0`          [`ZeroFixing`]
  --   `↔ ∀ i ∈ range n, residual cs x i + δᵢ = 0`  [`residual_edit_eq`]
  unfold actAllZero actLayerOut
  rw [show (compileToLayer (applySymEdit cs n e)).map (fun l => act (LayerOut l x))
      = (List.range n).map (fun i => act (residual cs x i + deltaAt cs e x i)) from ?_]
  · constructor
    · intro h i hi
      exact (hσ _).mp (h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    · intro h v hv
      rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
      exact (hσ _).mpr (h i (List.mem_range.mp hi))
  · -- 把两层 `map` 合成一层（`list_getD_map_range` 把 `getD` 归约成逐项形态），
    -- 再用 `layerOut_applySymEdit` 逐项改写
    have hmap : (compileToLayer (applySymEdit cs n e)).map (fun l => act (LayerOut l x))
        = (List.range n).map (fun i =>
            act (LayerOut (convertVec ((applySymEdit cs n e).getD i ⟨[], 0⟩)) x)) := by
      unfold compileToLayer
      rw [applySymEdit]
      simp only [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hi' : i < n := List.mem_range.mp hi
      have hgd : ((List.range n).map (fun i =>
          { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
            b := (cs.getD i ⟨[], 0⟩).b + e.db i })).getD i
            (⟨[], 0⟩ : VectorConstraint)
          = { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
              b := (cs.getD i ⟨[], 0⟩).b + e.db i } :=
        list_getD_map_range _ n i _ hi'
      rw [hgd]
      rfl
    rw [hmap]
    apply List.map_congr_left
    intro i hi
    rw [layerOut_applySymEdit cs n e i (List.mem_range.mp hi) x]

end Lattice.Lib.Editing.RealEditInvariantCatalog