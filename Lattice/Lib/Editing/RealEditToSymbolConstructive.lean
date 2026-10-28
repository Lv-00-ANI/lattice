import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Editing.RealCanonicalForm
/-!
# LATTICE D1-2: 符号侧「编辑」与「规范化」的关系

## 0. ⭐ 任务书前提的更正（承 `_deep_out/D_D1-2.md`）

任务书把本角度的缺口写成「编辑 ⟹ **符号侧更新不存在**」。
⚠ **该前提为假**：符号侧编辑**存在**且**已被证**
（`RealEditSemantics.editConstraint`，`RealEditSemantics.lean:443`）。

⭐⭐ **真缺口**：`RealCanonicalForm.canonicalize`（符号侧**规范化**，gcd 约化）
与 `RealEditSemantics.editConstraint`（符号侧**编辑**，逐项相加）之间
**从未建立任何关系** —— 实测 `RealEditSemantics` 不 import `RealCanonicalForm`、
`RealCanonicalForm` 不 import `RealEditSemantics`，且**无任何模块同时 import 二者**。
⭐ **本文件是第一个**（判据 3：跨模块）。

## 1. 本文件证什么

| # | 定理 | 内容 | 判据 |
|:--|:--|:--|:--|
| T1 | `canonicalize_editConstraint_not_commute` | 两路径**不可交换**（具体见证） | 1,2,3 |
| T2 | `canonicalize_editConstraint_not_commute_witness_content_eq` | ⭐ 见证的**内容相等** ⟹ 否证「保内容 ⟹ 交换」 | 1,2,4 |
| T3 | `edit_blind_to_semantics_witness` | ⭐ 编辑**语义不可见**、**对象可见** | 1,2,4 |
| T4 | `edit_scaling_witness_family` | 上述现象的**参数化族**（每个非零 `k`） | 1,2,4 |
| T5 | `editConstraint_image_not_surjective_on_length` | 编辑通道**不可能**覆盖全部层（可计算下界） | 1,4 |
| T6 | `editConstraint_reachable_iff_length` | ⭐ 像集的**充要刻画**（可达 ⟺ 长度对齐） | 1,4 |

⚠ **不做**（承调研报告撤回）：`symbol_edit_commutes_with_compile_setLevel` ——
调研代理已判其为 `rfl` 级空壳（`RealConstraintEdit.lean:449-450` **自述**），
且已在 `RealConstraintEdit.edit_compiles_to_weight_side` 与
`_X-05.compile_commutes_edit` 被证过**两次**。

无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、见证的定义与求值引理 -/

/-- ⭐ **T1/T2 的基准约束**：`a = [2]`、`b = 2`（内容 = `gcd 2 2 = 2`）。 -/
def d12C : VectorConstraint := { a := [2], b := 2 }

/-- ⭐ **T1/T2 的编辑增量**：`dw = [2]`（与 `c.a` 长度对齐）、`db = 0`。

⚠ 取 `db = 0` 是**刻意**的：它使编辑后的 `b` 不变，从而内容**恰好保持**为 `2`
（`gcd 4 2 = 2 = gcd 2 2`）—— 这正是 T2 否证「保内容 ⟹ 交换」所需的**紧**构造。 -/
def d12Δ : LayerDelta := { dw := [2], db := 0 }

/-- `d12C` 的内容是 `2`。 -/
lemma d12_content : constraintContent d12C = 2 := by
  simp only [constraintContent, listGcdNat, d12C, List.foldr_cons, List.foldr_nil]
  norm_num

/-- ⭐ **编辑后的约束**：`{a := [4], b := 2}`（`[2] zipWith (+) [2] = [4]`；`2 + 0 = 2`）。 -/
lemma d12_edited : editConstraint d12C d12Δ = { a := [4], b := 2 } := rfl

/-- ⭐⭐ **编辑【不改变】内容**：`content (editConstraint d12C d12Δ) = content d12C = 2`。

⭐ **这是 T2 的承重量** —— 它说明「不可交换」**不是**内容漂移的副产品，
而是**即使在内容严格保持时也发生**。 -/
lemma d12_edited_content :
    constraintContent (editConstraint d12C d12Δ) = constraintContent d12C := by
  rw [d12_edited, d12_content]
  simp only [constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
  norm_num

/-- `d12C` 的规范形：`{a := [1], b := 1}`（逐分量除以内容 `2`）。 -/
lemma d12_canon : canonicalize d12C = { a := [1], b := 1 } := by
  simp only [canonicalize, constraintContent, listGcdNat, d12C,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- ⭐ **左路径**（先编辑、后规范化）的值：`{a := [2], b := 1}`（`[4,2] / 2`）。 -/
lemma d12_left : canonicalize (editConstraint d12C d12Δ) = { a := [2], b := 1 } := by
  rw [d12_edited]
  simp only [canonicalize, constraintContent, listGcdNat,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- 要点 **右路径**（先规范化、后编辑）的值：`{a := [3], b := 1}`（`[1] zipWith (+) [2] = [3]`；`1 + 0 = 1`）。 -/
lemma d12_right : editConstraint (canonicalize d12C) d12Δ = { a := [3], b := 1 } := by
  rw [d12_canon]
  rfl

/-- ⭐ 两路径的**值确实不同**（用 `a` 分量 `[2] ≠ [3]` 区分）。 -/
lemma d12_vals_ne : ({ a := [2], b := 1 } : VectorConstraint) ≠ { a := [3], b := 1 } := by
  intro h
  have : ([2] : List Int) = [3] := congrArg VectorConstraint.a h
  simp at this

/-! ## 二、⭐ 主定理组：编辑与规范化**不可交换** -/

/-- ⭐⭐ **T1（本角度主定理）：符号侧「编辑后规范化」与「规范化后编辑」【不可交换】。**

⭐ **见证**：`c := {a := [2], b := 2}`、`Δ := ⟨[2], 0⟩`（`dw` 与 `c.a` 长度对齐）。
- **左端**：`editConstraint c Δ = {a := [4], b := 2}`，内容 `2`，
  `canonicalize` 得 `{a := [2], b := 1}`；
- **右端**：`canonicalize c = {a := [1], b := 1}`，再编辑得 `{a := [3], b := 1}`。
- ⭐ `{a := [2], b := 1} ≠ {a := [3], b := 1}`（`a` 分量区分）⟹ **不交换**。

**非平凡性**：
1. **消融**：把 `Δ` 换成 `⟨[0], 0⟩`（即**恒等**编辑），两端**都**退化为 `canonicalize c`，
   结论**变假** —— 见 `editConstraint_zero_delta`（`RealEditSemantics.lean:365` 同族）
   与本节 `d12_zero_delta_commutes`（**机器见证消融**）。
2. **反驳**：本定理**否证**「gcd 约化与逐项相加相容」这一自然猜想。
3. **跨模块**：⭐ 首次连接 `RealCanonicalForm`（规范化线）与 `RealEditSemantics`（编辑线）。 -/
theorem canonicalize_editConstraint_not_commute :
    ∃ (c : VectorConstraint) (Δ : LayerDelta),
      canonicalize (editConstraint c Δ) ≠ editConstraint (canonicalize c) Δ := by
  refine ⟨d12C, d12Δ, ?_⟩
  rw [d12_left, d12_right]
  exact d12_vals_ne

/-- ⭐ **零增量编辑（**任意**长度对齐的零增量版）**：若 `Δ.dw` 与 `c.a` 等长且
每个分量都是 `0`、`Δ.db = 0`，则 `editConstraint c Δ = c`。

⭐ **把"零增量"抽象成两个前提**（而非写死 `c.a.map (fun _ => 0)`），
是为了让**同一条引理**能同时用在 `c` 与 `canonicalize c` 上 ——
两者的 `a` 长度相同（`List.map` 保长），故 `Δ` 可**共用**。 -/
lemma editConstraint_eq_self_of_zero (c : VectorConstraint) (Δ : LayerDelta)
    (hlen : Δ.dw.length = c.a.length) (hzero : ∀ v ∈ Δ.dw, v = 0) (hdb : Δ.db = 0) :
    editConstraint c Δ = c := by
  obtain ⟨a, b⟩ := c
  obtain ⟨dw, db⟩ := Δ
  simp only at hlen hzero hdb
  subst hdb
  show ({ a := a.zipWith (· + ·) dw, b := b + 0 } : VectorConstraint) = { a := a, b := b }
  congr 1
  · -- `dw` 全零且与 `a` 等长 ⟹ `a zipWith (+) dw = a`
    induction a generalizing dw with
    | nil =>
      have : dw = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      rfl
    | cons hd tl ih =>
      cases dw with
      | nil => simp at hlen
      | cons wd wt =>
        have hwd : wd = 0 := hzero wd (by simp)
        have hlen' : wt.length = tl.length := by
          simpa only [List.length_cons, Nat.succ.injEq] using hlen
        have hz' : ∀ v ∈ wt, v = 0 := fun v hv => hzero v (by simp [hv])
        subst hwd
        simp only [List.zipWith_cons_cons, ih wt hz' hlen']
        ring_nf
  · ring

/-- ⭐ **判据 1（消融）的机器见证**：**把编辑整个删掉**（即取「零增量」编辑
`Δ₀ := ⟨c.a.map (fun _ => 0), 0⟩`），两条路径**相等** ——
即 T1 的结论**依赖编辑的非平凡性**，删掉它结论**变假**。

⭐ **为什么这是真正的消融而不是换了命题**：`editConstraint c Δ₀ = c`
（`editConstraint_eq_self_of_zero`），故本引理的内容正是
「**没有编辑时**两条路径一致」。

⚠ **为什么不能取 `Δ.dw = []`（更"零"的增量）**：`zipWith` 在长度不等时
**截断**（`RealEditSemantics.lean` §7.3），`[]` 会把 `c.a` 整个抹掉 ——
这正是 `editLayer_nil_dw_not_identity` 登记的同一陷阱。
⇒ **零增量必须"长度对齐"**，故写成 `c.a.map (fun _ => 0)`。 -/
lemma d12_zero_delta_commutes (c : VectorConstraint) :
    canonicalize (editConstraint c ⟨c.a.map (fun _ => 0), 0⟩)
      = editConstraint (canonicalize c) ⟨c.a.map (fun _ => 0), 0⟩ := by
  -- ⭐ `Δ₀ := ⟨c.a.map (fun _ => 0), 0⟩` 同时是 `c` 与 `canonicalize c` 的零增量：
  --    前者的 `a` 就是 `c.a`（**`rfl`**）；后者的 `a` 是 `c.a.map` 的像，**保长**。
  have hlen1 : (⟨c.a.map (fun _ => 0), 0⟩ : LayerDelta).dw.length = c.a.length := by
    simp only [List.length_map]
  have hlen2 : (⟨c.a.map (fun _ => 0), 0⟩ : LayerDelta).dw.length
      = (canonicalize c).a.length := by
    simp only [List.length_map, canonicalize]
  have hz : ∀ v ∈ (⟨c.a.map (fun _ => 0), 0⟩ : LayerDelta).dw, v = 0 := by
    intro v hv
    obtain ⟨_, _, h0⟩ := List.mem_map.mp hv
    exact h0.symm
  rw [editConstraint_eq_self_of_zero c _ hlen1 hz rfl,
      editConstraint_eq_self_of_zero (canonicalize c) _ hlen2 hz rfl]

/-- ⭐⭐ **T2（判据 2 + 4 的承重条）：不可交换【不】由内容漂移引起。**

本定理给出**同一条** T1 见证，并**额外证明**：编辑前后的内容**完全相等**。

⭐⭐ **它否证的是调研报告的一条判定**：报告 T5 声称
「保内容是交换的**充分**条件」—— 本定理是它的**机器反例**
（`content c' = content c` 成立，而**交换不成立**）。

⚠ **诚实登记**：调研报告同时判定 T5 的 `⟹` 方向（交换 ⟹ 保内容）**不成立**；
**本文件未找到该方向的反例**，且我的推导（见报告）指向它**可能成真**。
⇒ **该方向本文件【不证】，如实登记为未决。** -/
theorem canonicalize_editConstraint_not_commute_witness_content_eq :
    ∃ (c : VectorConstraint) (Δ : LayerDelta),
      constraintContent (editConstraint c Δ) = constraintContent c ∧
      canonicalize (editConstraint c Δ) ≠ editConstraint (canonicalize c) Δ := by
  refine ⟨d12C, d12Δ, d12_edited_content, ?_⟩
  rw [d12_left, d12_right]
  exact d12_vals_ne

/-! ## 三、⭐ 编辑的「语义盲 / 对象可见」二分（判据 2 + 4）

⚠ **诚实降级登记（承调研报告）**：本节的**现象**与既有
`RealEditToSymbol.semEq_coarser_than_eq`（`:250`）及
`RealEditSymbolAgreement.edit_diff_not_representative`（`:247`）
**是同一现象的第三次复现**。⭐ **故本节的独立价值仅在「编辑侧」
（`editConstraint` 载体），不声称是全新发现。**
⚠ 且本节**不跨越到 `RealCanonicalForm`**（不同 T1/T2），判据 3 **弱**。 -/

/-- ⭐ **T3：存在符号侧编辑，语义上【什么都没变】，但对象上【可见】。**

见证：`c := {a := [1], b := 1}`、`Δ := ⟨[1], 1⟩`（即 `k = 2` 的**缩放型**编辑）。
- `editConstraint c Δ = {a := [2], b := 2} = scaleVec c 2`（**机器验证**：`rfl`）；
- **语义等价**由 `scaleVec_preserves`（`ConvertVectorLinear.lean:105`，`lam = 2 ≠ 0`）直接给出；
- **对象不等**由 `a` 分量 `[1] ≠ [2]` 给出。

⭐ **判据 2**：本定理**否证**「编辑必然改变约束语义」这一自然猜想。 -/
theorem edit_blind_to_semantics_witness :
    ∃ (c : VectorConstraint) (Δ : LayerDelta),
      (∀ x : List Int, VectorConstraintSat (editConstraint c Δ) x ↔ VectorConstraintSat c x) ∧
      editConstraint c Δ ≠ c := by
  refine ⟨{ a := [1], b := 1 }, ⟨[1], 1⟩, ?_, ?_⟩
  · -- ⭐ 编辑恰好是缩放（`k = 2`），故套 `scaleVec_preserves`
    intro x
    have h : editConstraint ({ a := [1], b := 1 } : VectorConstraint) ⟨[1], 1⟩
        = scaleVec ({ a := [1], b := 1 } : VectorConstraint) 2 := rfl
    rw [h]
    exact (scaleVec_preserves ({ a := [1], b := 1 } : VectorConstraint) x 2 (by norm_num)).symm
  · -- 对象不等：`a` 分量 `[2] ≠ [1]`
    intro h
    have : ([2] : List Int) = [1] := congrArg VectorConstraint.a h
    simp at this

/-- ⭐⭐ **T4（判据 4：参数化族）：上述「语义盲」现象对【每个 `k ∉ {0, 1}`】都成立。**

⭐ **这是 T3 的量化加强**：不是单一存在性，而是**整族见证**
（`k = 2` 只是其中一员）。

⭐ **构造**：取 `c := {a := [1], b := 1}`、`Δ := ⟨[k-1], k-1⟩`。
则 `editConstraint c Δ = {a := [k], b := k} = scaleVec c k`（**逐字**，
因为两者都是"逐分量乘 `k`"的加性/乘性写法）—— **机器验证为本引理内的 `h`**。

⭐⭐ **两个前提都【承重】，且各自对应一条判据**：
- **`hk0 : k ≠ 0` 不可省（判据 1 消融）**：若 `k = 0`，编辑把约束**清零**
  （`scaleVec c 0` 是零约束），语义等价**变假** —— 零约束 `0·x + 0 = 0`
  对**一切** `x` 成立，与 `x + 1 = 0` 的零点集（单点 `x = -1`）完全不同。
  ⇒ **删掉 `k ≠ 0`，结论变假**。
- **`hk1 : k ≠ 1` 不可省**：`k = 1` 时 `Δ = ⟨[0], 0⟩` 是**恒等**编辑，
  `editConstraint c Δ = c`，第三项 `≠ c` **变假**。

⚠ **本条的诚实边界**：原稿（调研报告 T3 的"参数化族"）写作"任意 `k ≠ 0`"，
⚠ **该形式为假**（`k = 1` 即反例）。⭐ 本文件**修正为 `k ∉ {0, 1}`**，
并把原因写在 docstring 里 —— 这是**加强前提**，不是弱化结论。 -/
theorem edit_scaling_witness_family (k : Int) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
    ∃ (c : VectorConstraint) (Δ : LayerDelta),
      editConstraint c Δ = scaleVec c k ∧
      (∀ x : List Int, VectorConstraintSat (editConstraint c Δ) x ↔ VectorConstraintSat c x) ∧
      editConstraint c Δ ≠ c := by
  refine ⟨{ a := [1], b := 1 }, ⟨[k - 1], k - 1⟩, ?_, ?_, ?_⟩
  · -- ⭐ 关键恒等式：加性编辑 = 乘性缩放
    show ({ a := [1].zipWith (· + ·) [k - 1], b := 1 + (k - 1) } : VectorConstraint)
        = scaleVec ({ a := [1], b := 1 } : VectorConstraint) k
    show ({ a := [1].zipWith (· + ·) [k - 1], b := 1 + (k - 1) } : VectorConstraint)
        = ({ a := [1].map (fun v => v * k), b := 1 * k } : VectorConstraint)
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil]
    congr 1
    · ring_nf
    · ring_nf
  · -- 语义等价：编辑恰好是 `scaleVec c k`，套 `scaleVec_preserves`
    intro x
    have h : editConstraint ({ a := [1], b := 1 } : VectorConstraint) ⟨[k - 1], k - 1⟩
        = scaleVec ({ a := [1], b := 1 } : VectorConstraint) k := by
      show ({ a := [1].zipWith (· + ·) [k - 1], b := 1 + (k - 1) } : VectorConstraint)
          = scaleVec ({ a := [1], b := 1 } : VectorConstraint) k
      show ({ a := [1].zipWith (· + ·) [k - 1], b := 1 + (k - 1) } : VectorConstraint)
          = ({ a := [1].map (fun v => v * k), b := 1 * k } : VectorConstraint)
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil]
      congr 1
      · ring_nf
      · ring_nf
    rw [h]
    exact (scaleVec_preserves ({ a := [1], b := 1 } : VectorConstraint) x k hk0).symm
  · intro h
    have ha : ([1 + (k - 1)] : List Int) = [1] := congrArg VectorConstraint.a h
    simp only [List.cons.injEq, true_and] at ha
    -- `1 + (k - 1) = k`，故 `ha : k = 1` —— 与 `hk1` 矛盾
    omega

/-! ## 四、⭐ 编辑通道的像集边界（判据 1 + 4）

⚠ 任务书的原话方向是「编辑 ⟹ 存在符号更新」。⚠ **该方向在 `List Int` 载体上
本质上是 `rfl` 空壳**（`RealEditToSymbol.lean:133` 已证 `convertVec` **是双射**，
`:194` 已机器化该消融）。⭐ **本节给出该方向【唯一】残留的可证内容**：
把「存在性」转成**像集的边界**。 -/

/-- ⭐ **T5（判据 4：可计算下界）：编辑通道【不可能】覆盖全部权重层。**

对任意层长 `n`，只要 `n ≠ c.a.length`，就**不存在**任何与 `c.a` 长度对齐的编辑 `Δ`
使 `convertVec (editConstraint c Δ)` 落在长度为 `n` 的层上。

⭐ **为什么这是「可计算的下界」而非空洞存在性**：
障碍是**具体可算**的整数 `|n - c.a.length|`（长度差），
不是"某个不可名状的反例"。

⭐ **判据 1（消融）**：⚠ **删掉长度对齐前提，结论变假** ——
`zipWith` **截断**，此时 `w.length = min c.a.length Δ.dw.length`
可以**任意小**（见 `RealEditSemantics.editLayer_nil_dw_not_identity`）。
⇒ 这是严格的「删掉假设**变假**」，不是"证不出来"。

⚠ **判据 2 弱**（这是"不可能"而非反驳某猜想）；**判据 3 弱**
（依赖全在 `ConvertVectorLinear` + `RealEditSemantics` 之内）。 -/
theorem editConstraint_image_not_surjective_on_length
    (n : Nat) (c : VectorConstraint) (hn : n ≠ c.a.length) :
    ∀ Δ : LayerDelta, c.a.length = Δ.dw.length →
      (convertVec (editConstraint c Δ)).w.length ≠ n := by
  intro Δ hlen hcontra
  -- ⭐ 长度锁定：`convertVec (editConstraint c Δ)` 的权重就是 `c.a zipWith (+) Δ.dw`，
  --    而 `zipWith` 在长度对齐时**保长** ⟹ 其长度恒为 `c.a.length`。
  have hlock : (convertVec (editConstraint c Δ)).w.length = c.a.length := by
    show (c.a.zipWith (· + ·) Δ.dw).length = c.a.length
    rw [List.length_zipWith, hlen, Nat.min_self]
  exact hn (hcontra ▸ hlock)

/-- ⭐⭐ **T6（判据 4：充要刻画）：编辑像集的【精确】边界。**

⭐ **这是 T5 的充要加强**：T5 只说"长度不符就不可达"，
本定理给出**反向**——**任何**长度符合的层**都**可达。

⇒ 合起来：`{convertVec (editConstraint c Δ) | Δ 与 c 长度对齐}` 的像集
**恰好**是 `{W | W.w.length = c.a.length}`（`b` 上无约束）。

⭐ **判据 1（消融）**：同 T5（长度对齐前提不可省 —— 见 ⟹ 方向里用到的保长性）。
⭐ **判据 4**：给出**充要条件**（"可达 ⟺ 长度相等"），这是量化判据的最强形式。

⚠ **诚实登记**：本条的 **⟸** 方向是**存在性构造**，其内容为
「用 `W.w - c.a` 作增量即可还原 `W.w`」。⭐ 若 `Δ` 被允许**依赖 `W`**
（本定理正是如此），则该方向接近 `rfl`；⚠ **但 ⟹ 方向不是**
（它用到 `zipWith` 的保长性这一**非**定义性事实），
且**双向合起来才是"像集刻画"** —— 这是 T5 的单向形式**无法**给出的内容。 -/
theorem editConstraint_reachable_iff_length
    (c : VectorConstraint) (W : LinearLayer) :
    (∃ Δ : LayerDelta, c.a.length = Δ.dw.length ∧
        convertVec (editConstraint c Δ) = W)
      ↔ W.w.length = c.a.length := by
  constructor
  · -- ⟹：长度锁定（`zipWith` 保长）
    rintro ⟨Δ, hlen, rfl⟩
    show (c.a.zipWith (· + ·) Δ.dw).length = c.a.length
    rw [List.length_zipWith, hlen, Nat.min_self]
  · -- ⟸：构造 `Δ.dw := W.w.zipWith (· - ·) c.a`、`Δ.db := W.b - c.b`
    intro hW
    refine ⟨⟨W.w.zipWith (· - ·) c.a, W.b - c.b⟩, ?_, ?_⟩
    · -- 长度对齐：`W.w.length = c.a.length`（由 `hW` 与 `List.length_zipWith`）
      rw [List.length_zipWith, hW, Nat.min_self]
    · -- ⭐ 逆向重构的**交换律形式**：`y.zipWith (+) (x.zipWith (-) y) = x`（长度对齐时）
      have hzip : ∀ (x y : List Int), x.length = y.length →
          y.zipWith (· + ·) (x.zipWith (· - ·) y) = x := by
        intro x
        induction x with
        | nil =>
          intro y hy
          have : y = [] := List.eq_nil_of_length_eq_zero hy.symm
          subst this
          rfl
        | cons hd tl ih =>
          intro y hy
          cases y with
          | nil => simp at hy
          | cons yd yt =>
            simp only [List.length_cons, Nat.succ.injEq] at hy
            simp only [List.zipWith_cons_cons]
            rw [ih yt hy]
            congr 1
            ring_nf
      -- ⭐ 先在**不解构 `W`** 的层级上把向量部分改写掉（`hzip W.w c.a hW` 正是所需）
      have hvec : c.a.zipWith (· + ·) (W.w.zipWith (· - ·) c.a) = W.w := hzip W.w c.a hW
      obtain ⟨w, b⟩ := W
      simp only [convertVec, editConstraint, LayerDelta.dw, LayerDelta.db,
                 LinearLayer.mk.injEq, VectorConstraint.a] at hvec ⊢
      rw [hvec]
      exact ⟨rfl, by ring⟩

end Lattice
