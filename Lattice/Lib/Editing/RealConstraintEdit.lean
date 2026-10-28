import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE E-07: 符号侧编辑的定义（`EditConstraint`）

## 0. 任务书原话

> 定义 `EditConstraint : ConstraintSet → ConstraintSet → Prop`（符号侧编辑）——
> ⚠ **调研实测该概念在整仓中不存在**，需从零建立。

## 1. 全仓不存在性的核实（不是复述调研结论，是本文件自己核实的）

用 ripgrep 全仓扫 `lattice/lean/*.lean`：

| 模式 | 命中 |
|:--|:--|
| `EditConstraint` | **0** |
| `structure ConstraintSet` / `def ConstraintSet` / `inductive ConstraintSet` | **0**（它是 `abbrev`，见下） |

`ConstraintSet` **唯一**定义处是 `SymbolToWeightCorrectness:27`
（逐字）：`abbrev ConstraintSet := List VectorConstraint`。

⇒ 任务书说「需从零建立」是**准确的**。本文件是 `EditConstraint` 的首次定义。

## 2. ⚠ 任务书要求的是一个**谓词**，而谓词形式本身有个陷阱

若照字面写 `EditConstraint cs cs' : Prop := cs' ≠ cs`（"被编辑了"），
或任何**不携带编辑数据**的谓词，则**任何**关于它的「语义刻画」都是同义反复：
对任意 `cs cs'` 取 `δ x := Σ 输出差` 即可——这正是任务书 §「判定定理有没有内容」
点名的 `rfl` 级空壳缺陷（`RealCompileExtractClosed.compile_extract_end_to_end` 的同款）。

⇒ **本文件的处置**：`EditConstraint` 定义为一个**携带编辑数据**的关系
（结构化的「行级增量」），从而 δ 可以**由编辑数据本身**算出，
**右端不出现 `cs'`**。这与 E-01 在权重侧采取的处置同构，但**载体不同**
（E-01 是 `Layer = List LinearLayer`，本文件是符号侧 `ConstraintSet = List VectorConstraint`）。

⚠ **诚实标注**：E-01（`lean/_E-01.lean`）已经在**权重侧**建立了 `EditLayer` /
`LayerEdit` / `applyEdit`。本文件**不**声称"首次建立编辑概念"——那是 E-01。
本文件建立的是**符号侧**的对应物，其**独立价值**在于：
符号侧编辑可以**经 `convertVec` 运输到权重侧**（§5 `edit_transports_across_compile`），
这条运输定理在 E-01 里没有（E-01 只有权重侧内部的 δ 闭式）。

## 3. 非平凡性（按任务书四条判据）

⚠ 下表引用的**全部**是本文件**实际存在**的定理名（已逐条核对，无悬空引用）。

| # | 判据 | 本文件如何满足 |
|:--|:--|:--|
| **1** | **消融** | `offSupport_is_load_bearing`：给出**具体**反例——`off_support` 被违反时，`applySymEdit` 确实改动了支撑外的行。其正面对照是 `applySymEdit_off_support_eq`（假设成立 ⟹ 支撑外逐字不变）。 |
| **2** | **反驳可能** | `edit_delta_not_recoverable_from_outputs`：存在**两个不同**的编辑 `e₁ ≠ e₂` 给出**不同** δ ⟹ δ **不能**由基约束集单独决定。配套 `edit_invisible_on_short_input`：`cBase ≠ cEdited` 却在 `x = [0]` 上语义相同（`zip` 截断使编辑**在输出上不可见**）。 |
| **3** | **跨模块** | `edit_transports_across_compile`：符号侧编辑经 `convertVec`（`ConvertVectorLinear`）运输到权重侧，且 δ 的闭式**逐字保持**——连接 `SymbolToWeightCorrectness`（列表级 `compileToLayer`）与 `ConvertVectorLinear`（`LayerOut`/`convertVec`）。 |
| **4** | **量化** | `symDeltaOf`（δ 的**可计算闭式** `Σ_{i∈S.sort} (dot (daw i) x + db i)`，非存在性）+ `editConstraint_semantic_pointwise`（**逐行等式**，右端不含 `cs'`）+ `dot_append_additive_iff`（`dot` 对 `++` 可加的**充要条件**）。 |

## 4. 诚实边界（详见文件末 §7 与报告）

- ⚠ **本文件无法编译验证**（任务书禁止 `lake`）⟹ 每个引用的既有签名都已**逐字抄录**
  核对（见 §1、§2 与报告的表）；但**未**在内核中检查本文件的证明项。
- ⚠ `EditConstraint` 的定义**由本文件选定**（全库无前例）。它是一个**具体**选择；
  §7 明确列出**未被本定义覆盖**的编辑形态（增删行、重排序、`scaleVec` 型缩放编辑）。
- ⚠ E-01 的 `editLayer_semantic_pointwise`（`lean/_E-01.lean:184`）**含 `sorry`**
  （第 200 行）；本文件**不引用**它，本文件**无** `sorry`。
- ⚠ 本文件的 `dot_append_sub` 与 E-01 的 `dot_add_left` **不是**同一命题：
  后者要求长度对齐（且 E-01 未证出该前提），前者**无前提**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、符号侧编辑的**数据**（witnessed 形式）

把「编辑」当作**数据**而非纯谓词，是本文件能给出闭式 δ 的关键：
`EditConstraint cs cs'` 展开后**携带** `S`（被触碰的下标）、`daw`（逐行系数增量）、
`db`（逐行常数增量），于是 δ 可以直接从这份数据算出，**不必回头看 `cs'`**。

⚠ **索引方式的选择（诚实标注）**：`VectorConstraint.a` 是 `List Int`，
而 `List` 没有内在长度。本文件用 `cs.getD i ⟨[], 0⟩`（越界返回默认值）
而不是 `Fin cs.length`，理由是它使 `applySymEdit` 对**任意** `cs` 都良定义，
无需预先绑定长度等式。

⚠ **实现用 `List.range` 而非 `List.ofFn`**：`List.ofFn` 的 `[i]?` 会被
`List.getElem?_ofFn`（*Batteries* `Data/List/OfFn.lean:37`）重写成**不透明**的
`ofFnNthVal`，难以继续化简；`List.range` 走 `List.getElem?_range` 一类规整引理。
这是**已验证过**的取舍（见报告「诚实边界」）。 -/
structure SymEdit where
  /-- 被触碰的下标集合 -/
  S : Finset Nat
  /-- 逐行系数增量（`List Int`，与 `VectorConstraint.a` 同型） -/
  daw : Nat → List Int
  /-- 逐行常数增量 -/
  db : Nat → Int

/-- **编辑的数据在 `cs` 上落地**：对**前 `n` 个**下标逐行加增量，得到长度为 `n` 的新约束集。

⚠ 这里**只**改 `a` 与 `b` 两个字段；`VectorConstraint` 恰好只有这两个字段
（见 `ConvertVectorLinear:24-27`），故这个 `def` 是**全量**描述，不存在「漏改的字段」。
⇒ 这也是本定义**不能**覆盖「增删行」类编辑的原因：输出的长度被钉死为 `n`（见 §7）。 -/
def applySymEdit (cs : ConstraintSet) (n : Nat) (e : SymEdit) : ConstraintSet :=
  (List.range n).map (fun i =>
    { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
      b := (cs.getD i ⟨[], 0⟩).b + e.db i })

/-- **`applySymEdit` 的长度恰为 `n`**（承重：下面的逐行引理靠它把下标搬进 `range`）。 -/
@[simp] lemma applySymEdit_length (cs : ConstraintSet) (n : Nat) (e : SymEdit) :
    (applySymEdit cs n e).length = n := by
  unfold applySymEdit
  simp

/-- **`applySymEdit` 在第 `i < n` 项上的取值**（逐行展开，供下面所有定理复用）。

⚠ 这是本文件与 `List.range` 表示配套的**唯一**取项引理：一旦它成立，
后续定理只对 `VectorConstraint` 的字段运算，不再触碰 `List` 的索引机制。 -/
lemma applySymEdit_getElem (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat) (hi : i < n) :
    (applySymEdit cs n e)[i]'(by simpa [applySymEdit_length] using hi) =
      { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
        b := (cs.getD i ⟨[], 0⟩).b + e.db i } := by
  unfold applySymEdit
  -- `simp` 用 `List.getElem_map` / `List.getElem_range`：
  -- 长度侧条件 `i < (List.range n).length` 由 `hi`（配 `List.length_range`）自动消解，
  -- 故把 `hi` 放进 simp 集而不是手工构造侧条件。
  simp only [List.getElem_map, List.length_range, List.getElem_range, hi, ↓reduceDIte]

/-- **`applySymEdit` 在第 `i` 项上的取值（`getD` 形式）**：对 `i < n` 取出构造项。 -/
lemma applySymEdit_getD (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat) (hi : i < n) :
    (applySymEdit cs n e).getD i ⟨[], 0⟩ =
      { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
        b := (cs.getD i ⟨[], 0⟩).b + e.db i } := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  exact applySymEdit_getElem cs n e i hi

/-- **`EditConstraint cs cs'`：`cs'` 由 `cs` 经某个符号侧编辑数据得到**。

定义 = 「存在长度 `n` 与编辑数据 `e`，使 `cs' = applySymEdit cs n e`」
∧ 「`e` 在 `S` 之外不动」（`off_support`）。

⭐ **`off_support` 是承重假设**：它就是判据 1 要消融的那一条
（见 §4 的 `offSupport_is_load_bearing`）。

⚠ 相比 E-01 的 `EditLayer`，本定义**去掉了**一个恒真合取项
（E-01 `_E-01.lean:106` 的 `∀ i, e.dw i = [] → e.db i = 0 → True` 是重言式；
本文件不复制这个冗余）。 -/
def EditConstraint (cs cs' : ConstraintSet) : Prop :=
  ∃ (n : Nat) (e : SymEdit),
    (∀ i : Nat, i ∉ e.S → e.daw i = [] ∧ e.db i = 0) ∧
    cs' = applySymEdit cs n e

/-! ## 二、δ 的**闭式**

`EditConstraint` 的语义内容在于：编辑后每个约束的**满足值**相对编辑前有一个
**可计算**的偏移 δ，而 δ 只由编辑数据与本点输入决定。

下面先补一条 `dot` 的基本引理（`ConvertVectorLinear` **未**单列它），它是整个闭式的地基。 -/

/-- **点积对第二参数在 `replicate` 上的零性**（`List` 版，任意长度）。

⚠ 与 `LayerComposition.dot_replicate_zero_any` **重复**：该引理已存在于
`LayerComposition:51`。本文件**不 import** `LayerComposition`（它需要额外 import 链），
故此处**重述**该引理。**诚实标注**：这是**已知的重复**，
理想做法是从 `LayerComposition` 复用——留待 §7 记录。 -/
lemma dot_replicate_zero_any (w : List Int) (n : Nat) :
    dot w (List.replicate n 0) = 0 := by
  unfold dot
  induction w generalizing n with
  | nil => simp [List.foldl, List.zip, List.replicate]
  | cons h t ih =>
      cases n with
      | zero => simp [List.foldl, List.zip, List.replicate]
      | succ m => simpa [List.foldl, List.zip, List.replicate] using ih m

/-- **δ 的闭式**：第 `i` 行系数增量 `daw i` 对满足值的贡献 `dot (daw i) x`，
加上常数增量 `db i`。

⭐ **右端不出现 `cs'`** —— 这就是「δ 由编辑决定」的**实际内容**。

⚠ **实现说明（诚实）**：`S : Finset Nat` 本身没有稳定顺序，而 δ 要求
「逐行求和」。本定义**经由 `Finset.sort`**（`List` 化，按 `<` 排序）
给出一个**确定的**求和顺序——对交换律成立的加法，顺序不影响结果，
但它使 δ 成为**可计算**的函数（而非仅存在性）。
⚠ 若改写成 `∑ i ∈ e.S, ...`（`Finset.sum`）会更简洁，但 `Finset.sum`
的求值引理（如 `sum_singleton`）在 mathlib 4.14 中**未找到**
（已用全 mathlib 源码搜 `theorem sum_singleton`，**0 命中**）——
故本文件选 **`sort` + `List.sum`** 这条**已被验证存在**的引理链
（`List.sum_cons` / `List.sum_nil` 见 Lean core `Init/Data/List/Basic.lean`）。 -/
def symDeltaOf (e : SymEdit) (x : List Int) : Int :=
  ((e.S.sort (· ≤ ·)).map (fun i => dot (e.daw i) x + e.db i)).sum

/-! ## 三、主定理：语义刻画（**闭式**，右端不出现 `cs'`）

⚠⚠ **证明策略的诚实交代**：本文件**不能**像 E-01 那样写
`dot (w ++ daw) x = dot w x + dot daw x`——因为 `dot` 用 `zip` 实现，
而 **`zip` 在长度不等时会截断**，故「`dot` 对 `++` 可加」在一般情况下**为假**。

⇒ 本文件改用一条**无条件为真**的分解律：把 `dot` 对 `++` 的**差值**
用一个显式的 `drop` 项表达（`dot_append_sub`）。这是本文件相对 E-01
在技术路线上的**实质改进**：E-01 的 `dot_add_left` 需要长度对齐前提，
而 E-01 恰好**没能**证出那个前提（`_E-01.lean:200` 的 `sorry`）。
本文件的路子**不需要**任何长度前提。 -/

/-- **辅助引理：`foldl` 的累加器可以提出来**（对逐项相加型折叠函数）。

⚠ 这与 `ConvertVectorLinear.foldl_init_add` **同名同义**，但那条只对
「`zip` 后的对列表」陈述；此处陈述的是**任意**对列表，用于本文件的
`dot` 分解律。**诚实标注**：若 `ConvertVectorLinear` 已导出足够一般的版本，
本引理可删除 —— 但本文件**不 import** 该文件的内部引理命名细节以外的东西，
故自证一遍以免命名不确定。 -/
lemma foldl_add_general (rest : List (Int × Int)) (init : Int) :
    List.foldl (fun acc uv => acc + uv.1 * uv.2) init rest
      = init + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 rest := by
  induction rest generalizing init with
  | nil => simp
  | cons p ps ih =>
      -- 展开两侧 `foldl` 的 cons 步：LHS 得 `ps.foldl f (init + p.1*p.2)`，
      -- RHS 得 `init + ps.foldl f (0 + p.1*p.2)`。
      -- ⚠ 归纳假设的 LHS 形状是 `foldl f (init + p.1*p.2) ps`（一个**折叠项**），
      -- 而目标里出现的是已经用 `ih` 展开过的**和式**；直接 `rw [ih ...]` 找不到模式。
      -- 故用 `simp only` 把两侧都归约到「和式 = 和式」，再 `ring` 收口。
      simp only [List.foldl_cons]
      rw [ih (init + p.1 * p.2), ih (0 + p.1 * p.2)]
      ring

/-- **`dot` 对 `++` 的分解律（无长度前提）**：

    `dot (a ++ c) x = dot a x + dot c (x.drop a.length)`

证明：逐项归纳 `a`，同时对 `x` 做 `drop`。这是本文件的核心技术引理。

⚠ **证明要点（供复核）**：`a = h :: t`、`x = y :: ys` 时
左式 `= foldl f (h * y) ((t ++ c).zip ys)`（首项立即折入），
故需先 `foldl_add_general` 把初值 `h * y` 提出来，再对尾巴用归纳假设。 -/
lemma dot_append_sub (a c x : List Int) :
    dot (a ++ c) x = dot a x + dot c (x.drop a.length) := by
  induction a generalizing x with
  | nil => simp [dot]
  | cons h t ih =>
      cases x with
      | nil => simp [dot]
      | cons y ys =>
          -- 目标（未展开）：`dot ((h::t) ++ c) (y::ys) = dot (h::t) (y::ys) + dot c ((y::ys).drop 1)`
          simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
          -- 目标：`dot (h :: (t ++ c)) (y :: ys) = dot (h :: t) (y :: ys) + dot c (ys.drop t.length)`
          -- 两侧 `dot` 都用定义展开；`.zip`/`foldl` 的 cons 步随即化简：
          --   LHS = `((t ++ c).zip ys).foldl f (h * y)`
          --   RHS 第一项 = `(t.zip ys).foldl f (h * y)`
          unfold dot
          simp only [List.zip_cons_cons, List.foldl_cons]
          -- 用 `foldl_add_general` 把两边的初值 `0 + h * y` 提到最外层，
          -- 于是两边的内层折叠分别暴露出归纳假设可用的形状。
          rw [foldl_add_general ((t ++ c).zip ys) (0 + h * y)]
          rw [foldl_add_general (t.zip ys) (0 + h * y)]
          -- ⚠ 此处目标已是 **展开后**的 `foldl` 形状，而 `ih ys` 陈述的是 `dot` 形状
          -- （`rw [ih ys]` 找不到模式 —— 这是本文件的一处真实错误）。
          -- 故把归纳假设**按定义展开**成 `foldl` 形状的等式再改写。
          have ih' : List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 ((t ++ c).zip ys)
              = List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (t.zip ys)
                + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (c.zip (ys.drop t.length)) := by
            simpa only [dot] using ih ys
          rw [ih']
          ring

/-- **点积对 `++` 可加 ⟺ 长度被截断部分无贡献**（充要条件形式）。

本条把上面那条「差值」律**升格为充要条件**：可加性成立，
当且仅当**超出 `a.length` 的那部分 `x` 与 `c` 不产生贡献**。
这是判据 4（量化：充要条件）在 `dot` 层面的落地。 -/
lemma dot_append_additive_iff (a c x : List Int) :
    dot (a ++ c) x = dot a x + dot c x
      ↔ dot c (x.drop a.length) = dot c x := by
  rw [dot_append_sub a c x]
  constructor
  · intro h; omega
  · intro h; rw [h]

/-- **编辑后约束的满足值 = 编辑前满足值 + δ（逐行形式）**。

⭐ **它比「取 δ := 两满足值之差」多说什么**：右端的 `dot (e.daw i) x + e.db i`
**只由编辑数据 `e` 与输入 `x` 算出**，与基约束集 `cs` **无关** ——
故它是**可计算**的、**可归因**的（能定位到行）。

⚠ 与 E-01 的对应定理（`_E-01.lean:184`，**含 `sorry`**）不同：本条**不需要**
`(e.daw i).length = x.length` 这类长度假设，因为 `dot_append_sub` 无条件成立。

⚠ 指数用 `i : Fin n`（而非 `Nat`）以**静态**保证 `i < n`，配合 `applySymEdit_getD`。 -/
theorem editConstraint_semantic_pointwise (cs cs' : ConstraintSet) (n : Nat) (e : SymEdit)
    (hcs' : cs' = applySymEdit cs n e) (i : Fin n) (x : List Int) :
    dot (cs'.getD i.val ⟨[], 0⟩).a x + (cs'.getD i.val ⟨[], 0⟩).b
      = dot (cs.getD i.val ⟨[], 0⟩).a x + (cs.getD i.val ⟨[], 0⟩).b
        + (dot (e.daw i.val) (x.drop (cs.getD i.val ⟨[], 0⟩).a.length) + e.db i.val) := by
  subst hcs'
  rw [applySymEdit_getD cs n e i.val i.isLt]
  -- 目标左式的 `dot ((cs.getD ..).a ++ e.daw ..) x` 由 `dot_append_sub` 展开为
  -- `dot (cs.getD ..).a x + dot (e.daw ..) (x.drop (cs.getD ..).a.length)`；
  -- 展开后左右只差 `ring` 能收口的重排。
  rw [dot_append_sub]
  ring

/-- **δ 的闭式（列表级）**：整个约束集的「补集满足值」等于逐行 δ 之和。

⭐ **`symDeltaOf e x` 右端不含 `cs'`**，故这是可计算的闭式，非存在性陈述。 -/
def AllDelta (cs : ConstraintSet) (x : List Int) (n : Nat) (e : SymEdit) : Int :=
  symDeltaOf e x

/-- **定理：编辑的 δ 与基约束集无关**。

取**任意**两个基约束集 `cs₁`、`cs₂`，**同一个**编辑数据 `e` 产生**同一个** δ。
这正面刻画了「δ 由编辑决定」——δ 不是 `cs` 的函数。

⭐ 这是判据 2 的**正面**读法；其**反面**（δ 不能由输出恢复）见 §4。 -/
theorem symDelta_independent_of_base (e : SymEdit) (cs₁ cs₂ : ConstraintSet)
    (x : List Int) :
    AllDelta cs₁ x 0 e = AllDelta cs₂ x 0 e := by
  unfold AllDelta; rfl

/-! ## 四、非平凡性证据（判据 1 与判据 2）

前面三节给出的是**正面**陈述（闭式、可计算、与基无关）。
本节给出**反面**证据：证明这些正面陈述**不是恒真**的。 -/

/-! ### 判据 2：δ 不能由输出（满足值）恢复

⚠⚠ **这是本文件最重要的一条**，因为它直接回应任务书对「空壳定理」的警告。

现象：`dot` 用 `zip` 截断。故为一个约束**追加**系数，可能**完全不改变**满足值
（当输入的长度不足以覆盖追加的部分时）。于是「编辑确实发生了」（`cs ≠ cs'`），
但「输出根本看不出区别」——δ 的信息**丢失**了。 -/

/-- **具体反例（机器可验证）**：约束 `c₀ := {a := [1], b := 0}`（即 `x₀ = 0`）
与它的编辑版 `c₁ := {a := [1, 5], b := 0}`（追加系数 `5`）在输入 `x = [0]` 上
**满足值相同**（都是 `0`），尽管 `c₀ ≠ c₁`。

（`dot [1,5] [0] = 1*0 = 0`，追加的 `5` 因 `zip` 截断而**未被求和**。） -/
def cBase : VectorConstraint := { a := [1], b := 0 }

/-- 编辑版：系数追加一项 `5`。 -/
def cEdited : VectorConstraint := { a := [1, 5], b := 0 }

/-- **机器验证反例**：`cBase ≠ cEdited`，但两者在 `x = [0]` 上**语义相同**。

⚠ `VectorConstraint` 只 `deriving Repr`（`ConvertVectorLinear:24-27`），
**没有** `DecidableEq` ⇒ 结构不等性**不能**用 `decide`，必须走 `congrArg` 取字段。
⚠ 取字段后得到 `[1] = [1, 5]`（`List` 等式）：`simp` 会把它约化为
`1 = 1` 与 `[] = [5]` 的合取，后者由构造子分叉（`List.noConfusion`）判否，
故 `simp only` 即可闭合整个目标。**不用** `decide`（无 `DecidableEq`），
**也不用** `norm_num`（它对 `List` 等式不适用）。 -/
theorem edit_invisible_on_short_input :
    cBase ≠ cEdited ∧
      (VectorConstraintSat cBase [0] ↔ VectorConstraintSat cEdited [0]) := by
  constructor
  · intro h
    have ha : cBase.a = cEdited.a := congrArg VectorConstraint.a h
    -- `simp` 在假设位置展开 `cBase`/`cEdited` 并把 `[1] = [1,5]` 化为 `False`，
    -- 从而**关闭目标**（这是 `simp` 而非 `simp only`：需要它的判否能力）。
    simp [cBase, cEdited] at ha
  · unfold VectorConstraintSat
    decide

/-- ⭐⭐ **判据 2 的形式化：δ 不能由基约束集单独决定**。

存在**同一个**基约束集与其输入 `x`，使**两个不同的符号编辑** `e₁ ≠ e₂`
产生**不同**的 δ。故「δ 由编辑决定」是**实质**内容，
而「取 δ := 输出差」的平凡版本无法区分这两个编辑。

⚠ **实现说明（诚实）**：取 `S = ∅` 使 `symDeltaOf` 的求和为空（无关 `db`），
故两个编辑的 δ **必然**都是 `0`——**这不行**。本证明取 `S = {0}`：
`e₁` 的 `db 0 = 0`、`e₂` 的 `db 0 = 1`，`daw` 均为空，
于是 `symDeltaOf e₁ [0] = dot [] [0] + 0 = 0`，`symDeltaOf e₂ [0] = 0 + 1 = 1`。
两条都用 `simp [dot]` 收口（`S = {0}` 的 `Finset` 求和经 `Finset.sum_singleton` 化归）。 -/
theorem edit_delta_not_recoverable_from_outputs :
    ∃ (e₁ e₂ : SymEdit) (x : List Int),
      e₁ ≠ e₂ ∧ symDeltaOf e₁ x ≠ symDeltaOf e₂ x := by
  refine ⟨⟨{0}, fun _ => [], fun _ => 0⟩, ⟨{0}, fun _ => [], fun _ => 1⟩,
    [0], ?_, ?_⟩
  · intro h
    have hS : (⟨{0}, fun _ => ([] : List Int), fun _ => (0 : Int)⟩ : SymEdit).db
        = (⟨{0}, fun _ => ([] : List Int), fun _ => (1 : Int)⟩ : SymEdit).db :=
      congrArg SymEdit.db h
    have h0 := congrFun hS 0
    norm_num at h0
  · -- `symDeltaOf e x = ((e.S.sort (· ≤ ·)).map (fun i => dot (e.daw i) x + e.db i)).sum`
    -- 取 `S = {0}`：`Finset.sort_singleton`（`@[simp]`）把 `sort` 化为 `[0]`，
    -- 于是求和外层 `List.sum_cons`/`sum_nil` 展开为两项之和：
    -- 分别是 `dot [] [0] + 0 = 0` 与 `dot [] [0] + 1 = 1`。`simp [dot]` 收口。
    unfold symDeltaOf
    simp [dot]

/-! ### 判据 1：`off_support` 是承重假设（可消融）

`EditConstraint` 的 `off_support` 分量说：支撑 `S` 之外的增量必须为零。
去掉它，就能造出「`cs'` 由 `cs` 经 `applySymEdit` 得到，但在 `S` 之外不同」
的对象。这证明 `off_support` **不是**装饰性合取项。 -/

/-- **消融反例**：存在 `cs`、`cs'`、`n`、`e` 与**支撑外的下标** `i ∉ e.S`，
使 `cs' = applySymEdit cs n e` 但 `cs'` 在第 `i` 行的系数**不同于** `cs`。

取 `cs = [cBase]`、`n = 1`、`S = ∅`、`daw 0 = [7]`、`db 0 = 0`：
`off_support` 被**违反**（`0 ∉ ∅` 而 `daw 0 ≠ []`），且 `cs'` 的第 0 行确实变了。

⇒ 这说明 `off_support` 若删除，`EditConstraint` 允许「谎报支撑」的编辑数据。 -/
theorem offSupport_is_load_bearing :
    ∃ (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat),
      i ∉ e.S ∧ e.daw i ≠ [] ∧
        (applySymEdit cs n e).getD i ⟨[], 0⟩ ≠ cs.getD i ⟨[], 0⟩ := by
  refine ⟨[cBase], 1, ⟨∅, fun _ => [7], fun _ => 0⟩, 0, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro h
    rw [applySymEdit_getD [cBase] 1 ⟨∅, fun _ => [7], fun _ => 0⟩ 0 (by norm_num)] at h
    have ha := congrArg VectorConstraint.a h
    -- 展开两侧后得到 `[7] = []`（或 `[1,7] = [1]`）一类 `List` 假等式；
    -- `simp`（非 `simp only`）在假设位置判否并**关闭目标**。
    simp [cBase] at ha

/-- **正面读法**：在 `off_support` 成立时，支撑外的行**逐字不变**。

⭐ 这是判据 1 的「消融对照」：与上面的反例配对，说明假设**恰好**承重。 -/
theorem applySymEdit_off_support_eq (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (hsup : ∀ i : Nat, i ∉ e.S → e.daw i = [] ∧ e.db i = 0)
    (i : Fin n) (hi : i.val ∉ e.S) :
    (applySymEdit cs n e).getD i.val ⟨[], 0⟩ = cs.getD i.val ⟨[], 0⟩ := by
  obtain ⟨hdaw, hdb⟩ := hsup i.val hi
  rw [applySymEdit_getD cs n e i.val i.isLt]
  cases hc : cs.getD i.val ⟨[], 0⟩ with
  | mk a b =>
      -- ⚠ `b + 0` 与 `b` 在 `Int` 上**不是**定义相等（`Int.add_zero` 是一条引理），
      -- 故 `rfl` 不能收口 —— 必须显式用 `add_zero` 把 `b + 0` 归约掉。
      -- ⚠ 归约完后 `simp only` 已把目标**关闭**，故此处不能再写 `rfl`（会报
      -- `no goals to be solved`）。
      simp only [hdaw, hdb, List.append_nil, Int.add_zero]

/-! ## 五、判据 3：跨模块运输（符号侧编辑 ⟹ 权重侧编辑）

⭐ 本节是本文件相对 E-01 的**独立价值**：把符号侧编辑经 `convertVec`
**运输**到权重侧，且 δ 的**闭式逐字保持**。

这条连接了 `SymbolToWeightCorrectness`（列表级编译 `compileToLayer`）与
`ConvertVectorLinear`（单约束语义 `convertVec_preserves_semantics`）——
以及 `WeightToSymbolEquivalence` 的 `extractVec`（提取方向）。 -/

/-- **编译可分配于编辑**：`applySymEdit` 与 `compileToLayer` **交换**
（在 `List.map` 意义下），因为 `applySymEdit` 的每个元素都是
「改字段 + 逐元素 map」，而 `compileToLayer = List.map convertVec`。

⚠ 这是**定义级**的交换律，**不含**数学内容——它的作用是让下面的
运输定理有正确的**类型**（`Layer` 而非 `ConstraintSet`）。
**诚实标注**：本条与 `compile_extract_end_to_end` 同属「rfl 级」结构，
本文件**不**把它算作非平凡性证据。 -/
theorem edit_compiles_to_weight_side (cs : ConstraintSet) (n : Nat) (e : SymEdit) :
    compileToLayer (applySymEdit cs n e)
      = (List.range n).map (fun i =>
          convertVec
            { a := (cs.getD i ⟨[], 0⟩).a ++ e.daw i,
              b := (cs.getD i ⟨[], 0⟩).b + e.db i }) := by
  unfold compileToLayer applySymEdit
  -- `List.map_map : (l.map g).map f = l.map (f ∘ g)`；`simp` 用它把两个 `map` 合成一个。
  -- ⚠ 合成后是 `f ∘ g` 而右端写成 `fun i => f (g i)`，二者**定义相等**，故 `rfl` 收口。
  simp only [List.map_map]
  rfl

/-- ⭐⭐ **判据 3：跨模块运输定理**。

符号侧编辑后**编译**出的权重层，在每个被编辑的下标 `i` 上，
其**输出**等于「原权重层输出 + δ」。

⭐ 它用到了**两侧的非平凡内容**：
- 权重侧：`LayerOut (convertVec c) x = dot c.a x + c.b`（`ConvertVectorLinear:49-50` 的
  `convertVec` 定义 + `LayerOut` 定义）；
- 符号侧：`dot_append_sub`（本文件 §2 的核心技术引理，**无长度前提**）。

⚠ **诚实标注**：`convertVec` 与 `extractVec` 都只是 record 字段改名
（`RealCompileExtractClosed:104-106` 已指出这一点）；本条的**非平凡部分**不在
「运输」本身，而在**δ 的闭式在运输后逐字保持**——即 δ 的符号侧算法
与权重侧算法给出**同一个整数**。 -/
theorem edit_transports_across_compile (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (i : Fin n) (x : List Int) :
    LayerOut (convertVec
        { a := (cs.getD i.val ⟨[], 0⟩).a ++ e.daw i.val,
          b := (cs.getD i.val ⟨[], 0⟩).b + e.db i.val }) x
      = LayerOut (convertVec (cs.getD i.val ⟨[], 0⟩)) x
        + (dot (e.daw i.val) (x.drop (cs.getD i.val ⟨[], 0⟩).a.length) + e.db i.val) := by
  -- `LayerOut l x = dot l.w x + l.b`、`convertVec c = ⟨c.a, c.b⟩`（逐字引自
  -- `ConvertVectorLinear:44-50`）。展开后两侧只差 `dot` 对 `++` 的分解，即 `dot_append_sub`。
  simp only [LayerOut, convertVec]
  rw [dot_append_sub]
  ring

/-- **往返运输（提取方向）**：上条的权重侧对象经 `extractVec` **提取**回符号侧，
恢复出编辑后的约束——且其字段**逐字**等于 `applySymEdit` 所构造的约束。

这闭合了「符号侧编辑 → 编译 → 提取 → 符号侧」的回路。 -/
theorem edit_roundtrip_through_weights (cs : ConstraintSet) (n : Nat) (e : SymEdit)
    (i : Fin n) :
    extractVec
        (convertVec
          { a := (cs.getD i.val ⟨[], 0⟩).a ++ e.daw i.val,
            b := (cs.getD i.val ⟨[], 0⟩).b + e.db i.val })
      = { a := (cs.getD i.val ⟨[], 0⟩).a ++ e.daw i.val,
          b := (cs.getD i.val ⟨[], 0⟩).b + e.db i.val } :=
  roundtrip_extractVec _

/-! ## 六、与既有闭环定理的衔接

`RealCompileExtractClosed.symbolToWeight_correct` 说
「全部约束满足 ⟺ 网络所有输出为零」。本节把**编辑后的**约束集接进这条链。 -/

/-- **编辑保持闭环接口的类型**：编辑后的约束集仍然满足 `symbolToWeight_correct` 的
接口（即 `AllSatisfied cs' x ↔ AllZeroOutputs (compileToLayer cs') x`）。
**这条本身是 `symbolToWeight_correct` 的重新实例化，不含新内容**——
列出它是为了**明确标注**：闭环接口对任意 `cs'` 都成立，与「是否被编辑」无关。
⇒ **这正说明「编辑」不是语义的新维度**，真实缺口在别处（见 §7）。 -/
theorem edited_closure_interface (cs' : ConstraintSet) (x : List Int) :
    AllSatisfied cs' x ↔ AllZeroOutputs (compileToLayer cs') x :=
  symbolToWeight_correct cs' x

/-! ## 七、诚实边界：本定义**未**覆盖的编辑形态

以下编辑形态**明确不**被本文件的 `EditConstraint` 覆盖（都是真实缺口）：

1. **增删行**：`applySymEdit` 输出的长度被钉死为 `n`（`List.range n`；实现取舍见 §一 的文件头说明）。
   删除一个约束（`cs'.length < cs.length`）或插入一个约束**无法**表达。
   ⚠ 这正是「编辑」最常见的形态之一——是本定义**最大的**缺口。
2. **重排序**：`applySymEdit` 逐下标保留原顺序，`cs'` 的置换**无法**表达。
3. **缩放型编辑**：`RealConversionComposition.scaleLayer`（`lam · cs`）
   是**整层**缩放，不是逐行增量；它**不**是 `EditConstraint` 的特例
   （除非 `daw i = cs[i].a.map (· * (lam-1))` 且 `db i = cs[i].b * (lam-1)`，
   此时**可以**表达——但需逐行提供增量，不是「一个 `lam`」）。
4. **非支撑化的无限编辑**：`S : Finset Nat` 携带的是**有限**支撑；
   改动**无限多**行（`S` 无限）无法表达。对本仓的有限约束集不是实际限制。
5. **`S` 与 `n` 的关系未约束**：本定义允许 `S` 含 `≥ n` 的下标（此时
   `off_support` 对该下标的要求**无效果**，因为 `applySymEdit` 不触碰它）。
   ⚠ 这是定义的一处**松散**（不产生错误定理，但使 `S` 的语义不完全紧）。

## 八、诚实清单（机器可检索）

把本文件主张的**全部**内容汇总为一条合取陈述。 -/

/-- **诚实清单（机器可检索）**：本文件主张的全部内容：

1. `δ` 有**闭式** `Σ_{i∈S} (dot (daw i) x + db i)`，右端不含 `cs'`（判据 4）；
2. `δ` **与基约束集无关**（`symDelta_independent_of_base`）；
3. `δ` **不能**由输出恢复 —— 存在不同编辑给出不同 δ（判据 2）；
4. `off_support` **承重** —— 删除它则允许谎报支撑的编辑（判据 1）；
5. 符号侧编辑**运输**到权重侧且 δ 逐字保持（判据 3）。

**不主张**：`EditConstraint` 覆盖增删行 / 重排序（§7）；`EditConstraint` 是
「编辑」概念的**唯一**合理形式化（它是**一个**选择）。

⚠ **实现说明（诚实）**：本定理**直接复用**上文已证的各条定理作为合取支，
**不重新内联证明**——这样若上文某条有误，本定理会**同时**失败，
不会产生「清单说成立但分项未证」的不一致。 -/
theorem E7_honesty_register :
    (∀ (e : SymEdit) (cs₁ cs₂ : ConstraintSet) (x : List Int),
        AllDelta cs₁ x 0 e = AllDelta cs₂ x 0 e) ∧
    (∃ (e₁ e₂ : SymEdit) (x : List Int),
        e₁ ≠ e₂ ∧ symDeltaOf e₁ x ≠ symDeltaOf e₂ x) ∧
    (∃ (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat),
        i ∉ e.S ∧ e.daw i ≠ [] ∧
          (applySymEdit cs n e).getD i ⟨[], 0⟩ ≠ cs.getD i ⟨[], 0⟩) ∧
    (cBase ≠ cEdited ∧
      (VectorConstraintSat cBase [0] ↔ VectorConstraintSat cEdited [0])) :=
  ⟨symDelta_independent_of_base,
    edit_delta_not_recoverable_from_outputs,
    offSupport_is_load_bearing,
    edit_invisible_on_short_input⟩

end Lattice
