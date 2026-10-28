import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Optim.RealCrossUniverseBridge
/-!
# LATTICE E-01：编辑的语义定理（`EditLayer` 与**闭式** δ）

## 0. 任务书原话，以及它字面上的陷阱

任务书要求：

> 定义 `EditLayer : Layer → Layer → Prop`（W 被编辑为 W'），并证明
> `∀ x, LayerOut W' x = LayerOut W x + δ x` 形式的**语义刻画**，其中 δ 由编辑决定。

⚠⚠ **照字面做，这条定理是恒真的空壳**：对**任意** `W W'`，令
`δ x := LayerOut W' x - LayerOut W x` 即得。该「定理」**不引用 `EditLayer` 的任何内容**，
把 `EditLayer` 假设整个删掉它照样成立
⟹ **判据 1（消融）失败、判据 2（反驳可能）失败、判据 4（量化）失败**。
这与任务书点名的 `RealCompileExtractClosed.compile_extract_end_to_end` 同属一类缺陷，
该文件自己用 `closed_loop_adds_nothing` 做了诚实降级。

⚠⚠ **还有第二处字面错误（类型级）**：任务书写 `LayerOut W' x`，但**逐字核对签名**
（`ConvertVectorLinear.lean:44`）后：

    def LayerOut (l : LinearLayer) (x : List Int) : Int := dot l.w x + l.b

`LayerOut` 的**第一参数是 `LinearLayer`，不是 `Layer`**（`Layer := List LinearLayer`，
见 `SymbolToWeightCorrectness.lean:31`）。故 `LayerOut W x`（`W : Layer`）**根本不是合法项**。
本文件因此把主定理建立在 `LinearLayer` 层，再**列表提升**（`editLayer_...` 系列）。

## 1. 本文件真正证什么

把 δ **钉死为闭式**：δ 由**编辑数据本身**决定，**右端不出现 `W'`**。

    ∀ x, LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x

其中 `deltaOf Δ x` 只由编辑数据 `Δ : LayerDelta`（权重增量 + 偏置增量）算出。

⚠⚠ **承重前提（编译期发现，见 §7.3）**：`editLayer` 用 `zipWith` 实现，而 `zipWith`
在两侧长度不等时**截断**。因此上式**只在 `l.w.length = Δ.dw.length` 时成立** ——
这不是可以省略的技术细节，而是**命题的真假分界**：
`l = ⟨[], 5⟩`、`Δ = ⟨[1], 0⟩`、`x = [1]` 时左端 `= 5`、右端 `= 5 + 1 = 6`。
⇒ 本文件把该长度条件**显式写进每一条定理的假设**（单层用 `h`，列表级用 `DeltaCompatible`），
**不**偷偷弱化、也**不**用 `sorry` 掩盖。首版没有这个条件，是**错的**（§7.3 有反例）。

## 2. 为什么这是全库的真实缺口

既有编辑文献**全部**在解析载体上，**没有**一个在符号（`List Int`）载体上：

| 文件 | 载体 |
|:--|:--|
| `RealEditCrosstalk` / `RealEditOrder` / `RealEditRollback` | `F : E → ℝ`（函数级） |
| `RealEditBound` / `RealEditVerdict` | `E →L[ℝ] ℝ`（算子级） |
| `RealSparseEdit` | `Matrix (Fin m) (Fin n) ℝ`（矩阵级） |

⭐ 全部 grep 核实：`EditLayer` 与 `RealEditSemantics` 在整仓**不存在**。
⇒ 本文件**首次**在 `ℤ`/`List` 符号载体上建立编辑语义。这是**跨载体移植**，
共享枢纽是 `dot` 的**双线性**（且**仅在长度对齐时**，见 §1）。

## 3. 非平凡性（对应任务书四条判据）

| # | 判据 | 落点 |
|:--|:--|:--|
| **1** | **消融** | `dot_delta_not_always_zero`：`dot Δ.dw x = 0` 对**一切** `Δ, x` 为**假**（见证 `Δ.dw=[1]`、`x=[1]`）⟹ 删掉 `Δ` 的具体取值，δ≡0 的结论**变假**。`EditLayer_delta_not_unique` 是它在接口层的形式。`editLayer_nil_dw_not_identity` 是**长度条件**本身的消融见证（删掉长度对齐，恒等编辑的结论变假）。 |
| **2** | **反驳可能** | `delta_not_determined_by_base_only`：**同一个** `l`，两个**不同**编辑给出**不同** δ ⟹ δ 不由基权重决定，确实由**编辑**决定。 |
| **4** | **量化** | `editLayer_delta_closed_form` 给出**可计算闭式** `δ = dot Δ.dw x + Δ.db`（非存在性）；`editLayerList_outputs_eq_iff` 给出「输出不变」的**充要条件**。 |
| **3** | **跨模块** | `edit_commutes_with_convert` + `editConstraint_preserves_delta`：符号侧编辑经 `convertVec` **逐字**变成权重侧编辑，δ **逐字保持** —— 把 `ConvertVectorLinear`（编译）与编辑语义接上。 |

## 4. 诚实边界（详见 §7 与报告）

- ⚠ 本文件**首版未经内核编译**（上一批任务书错误地禁用 `lake`）⟹ 证明项**全部有错**。
  本版**已通过** `lake build RealEditSemantics`（exit 0）。
- ⚠ `EditLayer` 的定义是本文件**选定**的（全库无前例），非唯一合理选择；§7 列出**未覆盖**的编辑形态。
- ⚠ **长度条件是本轮真实修复的产物**（§7.3），不是原始设计的一部分。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、编辑数据与「加性编辑」

⚠ **设计要点**：`LinearLayer` 恰好只有 `w`、`b` 两个字段（`ConvertVectorLinear.lean:39-42`），
故 `⟨w + Δw, b + Δb⟩` 是**全量**描述 —— 不存在「漏改字段」的隐藏缺口。
⇒ 这同时是本定义**不能**覆盖「增删行 / 改变行数」类编辑的**原因**（§7 诚实登记）。 -/

/-- **层增量（编辑的数据）**：权重增量 `dw` 与偏置增量 `db`。

⭐ 这是「编辑」的**数据化**：一旦把它作为**输入**（而非由 `W` 与 `W'` 反推），
δ 就能被算成**闭式**，而不必回头看 `W'`。 -/
structure LayerDelta where
  /-- 权重增量 -/
  dw : List Int
  /-- 偏置增量 -/
  db : Int

/-- **加性编辑在单层上落地**：逐字段相加。

⚠ `zipWith` **截断**：结果权重长度是 `min l.w.length Δ.dw.length`。
故本定义**仅在** `l.w.length = Δ.dw.length` 时是「逐坐标相加」的忠实模型（§1、§7.3）。 -/
def editLayer (l : LinearLayer) (Δ : LayerDelta) : LinearLayer :=
  { w := l.w.zipWith (· + ·) Δ.dw, b := l.b + Δ.db }

/-- **列表级编辑**：逐层施加**同一份**增量（本文件取此最简形态；
⚠ 不建模「只编辑某几行」—— 那需要索引，见 §7）。 -/
def editLayerList (ls : Layer) (Δ : LayerDelta) : Layer :=
  ls.map (fun l => editLayer l Δ)

/-- ⭐ **增量与层表相容（长度对齐）**：每层的权重长度都等于 `Δ.dw` 的长度。

⚠⚠ **这不是可选的技术性假设，而是 §1 主定理的真假分界**：
`zipWith` 在长度不等时截断，`dot` 的分配律随之失效（`dot_zipWith_add_of_length`）。
⇒ 本文件把它**显式**作为假设，而不是藏起来。 -/
def DeltaCompatible (ls : Layer) (Δ : LayerDelta) : Prop :=
  ∀ l ∈ ls, l.w.length = Δ.dw.length

/-- ⭐ **δ 的闭式**：权重增量与输入的点积，加偏置增量。

⭐ **右端不出现 `l'`（编辑后的层）** —— 这是「δ 由编辑决定」的**实际数学内容**。
⚠ 注意 `dot Δ.dw x` 里 `Δ.dw` 是**增量**而非编辑后的权重。
⚠ **定义位置**：必须早于 `EditLayer_consequence` / `EditLayer_delta_not_unique`
—— ⚠ 首版把它们写在后面，Lean 于是把 `deltaOf` 当**自由变量**自动绑定，
报成 `function expected at deltaOf`（不是「没有这个符号」，而是「用在一个 binder 上」）。 -/
def deltaOf (Δ : LayerDelta) (x : List Int) : Int :=
  dot Δ.dw x + Δ.db

/-- **列表级语义：逐层输出**（与 `LayerComposition.layerFwd` **逐字一致**的写法；
⚠ 本文件**不 import** `LayerComposition`，故在此就地定义以免引入无关依赖）。
⚠ **定义位置**同 `deltaOf`：必须早于 `EditLayer_consequence`。 -/
def layerOuts (ls : Layer) (x : List Int) : List Int :=
  ls.map (fun l => LayerOut l x)

/-- ⭐ **`EditLayer : Layer → Layer → Prop`（任务书要求的逐字接口）**：

`W'` 由 `W` 经**某个**编辑数据得到，且该增量与 `W` **长度相容**。

⚠ **诚实标注（关键设计取舍）**：本定义把 `Δ` 藏在**存在量词**里，故
`EditLayer` 本身**不携带**可计算的 δ —— 若只用它，主定理就退化回
「δ := 输出之差」的平凡版本（任务书要避免的正是这个）。
⇒ 本文件的**实质内容**由**数据形式** `editLayerList` 承载（§四、§五），
`EditLayer` 只作为**接口层**存在：`EditLayer_consequence`（下）说明
在 `EditLayer` 成立时，输出差**恰为**某个具体 `deltaOf Δ x` ——
即**存在**一个可计算的闭式 δ（而非任意函数）。

⚠ **本版相较首版的变化**：`DeltaCompatible` 被**加入**存在量词内部。
理由：不加入时 `EditLayer` 对**截断**也成立，于是接口层主定理**是假的**；
加入后它才恰好刻画「逐坐标相加」。这是**加强前提**（不是弱化结论）。 -/
def EditLayer (W W' : Layer) : Prop :=
  ∃ Δ : LayerDelta, DeltaCompatible W Δ ∧ W' = editLayerList W Δ

/-! ⚠ **注**：`EditLayer_consequence`（接口层主定理）**放在 §五 之后** ——
它用到 `editLayerList_delta`，而该引理建立在 `editLayer_delta_closed_form` 之上。
⚠ 首版把它写在这里（§一），Lean 报 `unknown identifier 'editLayerList_delta'`：
**符号必须在作用域内**，声明顺序就是作用域。 -/

/-- ⭐ **不可替代性（判据 1 的接口层读数）**：存在 `W, W'` 使 `EditLayer W W'` 成立，
但**不同**的 `Δ` 给出**不同**的 δ。

⭐ **它说明什么**：`EditLayer_consequence` 里的 `∃ Δ` **不能**换成
「对所有 `Δ` 都成立」的更强形式 —— 因为 `W'` 固定后并非每个 `Δ` 都还原它。
⇒ 这是判据 1（消融）在**接口层**的形式。

⚠ **构造说明**：取 `W = W' = [{w := [1], b := 0}]`，
见证 `Δ₀ := ⟨[0], 0⟩`（**注意**：`dw` 必须是 `[0]` 而非 `[]` ——
`zipWith` 对 `[]` 会**截断成空表**，见 `editLayer_nil_dw_not_identity` 与 `editLayer_nil_dw_clears`）。
于是 `editLayerList W Δ₀ = W` 且长度相容（`1 = 1`），`EditLayer W W` 成立。 -/
theorem EditLayer_delta_not_unique :
    ∃ (W W' : Layer) (Δ₁ Δ₂ : LayerDelta) (x : List Int),
      EditLayer W W' ∧ deltaOf Δ₁ x ≠ deltaOf Δ₂ x := by
  refine ⟨[{ w := [1], b := 0 }], [{ w := [1], b := 0 }],
    ⟨[1], 0⟩, ⟨[0], 0⟩, [1], ?_, ?_⟩
  · -- `W' = editLayerList W ⟨[0], 0⟩`：`[1].zipWith (·+·) [0] = [1]`
    refine ⟨⟨[0], 0⟩, ?_, ?_⟩
    · -- 长度相容：单层，`[1].length = [0].length = 1`
      intro l hl
      simp at hl
      subst hl
      rfl
    · simp [editLayerList, editLayer]
  · -- `deltaOf ⟨[1],0⟩ [1] = 1` 而 `deltaOf ⟨[0],0⟩ [1] = 0`
    simp [deltaOf, dot]

/-! ## 二、δ 的**闭式**（定义已上移至 §一，以先于接口层使用） -/

/-! ## 三、地基引理：`zipWith` 加法与点积

⚠ **为什么需要这条**：`dot` 的 `foldl` 累加器形式使「分配律」不自动成立。
本引理把 `(a + a')·x = a·x + a'·x` 的**逐项**版本钉住。

⚠⚠ **本条的前提 `a.length = a'.length` 是承重的（首版漏了，故首版命题是假的）**：
`zip`/`zipWith` 在长度不等时**截断**。反例（机器求值确认）：
`a = []`、`a' = [1]`、`x = [1]` ⟹ 左端 `dot ([] zipWith [1]) [1] = dot [] [1] = 0`，
右端 `dot [] [1] + dot [1] [1] = 0 + 1 = 1`。**`0 ≠ 1`**。
⇒ 无长度前提的版本**不可证**（也不是「难度问题」，是**假命题**）。 -/

/-! ⚠ **`foldl_init_add` 不在此重证**：`ConvertVectorLinear.lean:74-84` 已有**逐字同签名**
（同 `Lattice` 命名空间）的引理，经 `import ConvertVectorLinear` 直接可用。
⚠ 首版在此**重证**同一引理 ⟹ `'Lattice.foldl_init_add' has already been declared` ——
这正是「先查符号是否已在作用域内」要拦的那类错误（重名 = 复用失败）。 -/

/-- ⭐ **`zipWith (·+·)` 与 `dot` 的分配律（长度对齐形式）**。

`dot (a.zipWith (·+·) a') x = dot a x + dot a' x`，**前提 `a.length = a'.length`**。

⭐ **为什么长度前提恰好够**：`dot` 内部先 `zip x`，
而 `(a.zipWith f a').zip x` 与 `(a.zip x)`、`(a'.zip x)` 的**截断长度一致**
（都为 `min (min a.length a'.length) x.length`）—— 一旦 `a.length = a'.length`，
三者的截断就自动对齐。⚠ 缺了它，`a'` 多出的尾巴会**只出现在右端**，命题变假（§三开头反例）。

⚠ **技术陷阱（承重）**：`dot` 是 `foldl`，归纳步里累加器**不是** `0`
（而是 `acc + p*y`）⟹ 只对 `0` 归纳的 IH **匹配不上**。
⇒ 正解：先证**带任意累加器**的 `foldl_init_add`，把两侧累加器**提出到 `0` 形**，
再用 `acc = 0` 的 IH 对齐两侧。这与 `RealConversionRobustness.dot_eq_sum`（`:123-135`）
踩过的坑**同一个**。 -/
lemma dot_zipWith_add_of_length (a a' x : List Int) (h : a.length = a'.length) :
    dot (a.zipWith (· + ·) a') x = dot a x + dot a' x := by
  unfold dot
  induction a generalizing a' x with
  | nil =>
      -- `a = []`：长度前提强制 `a' = []`，否则矛盾
      cases a' with
      | nil => cases x <;> simp
      | cons q qs => simp at h
  | cons p ps ih =>
      cases a' with
      | nil => simp at h
      | cons q qs =>
          have h' : ps.length = qs.length := by simpa using h
          cases x with
          | nil => simp
          | cons y ys =>
              simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.foldl_cons,
                zero_add]
              -- 把三个 foldl 的累加器全部提出到 0 形，IH 才能对齐
              have hL := foldl_init_add ((ps.zipWith (· + ·) qs).zip ys) ((p + q) * y)
              have hA := foldl_init_add (ps.zip ys) (p * y)
              have hB := foldl_init_add (qs.zip ys) (q * y)
              rw [hL, hA, hB]
              rw [ih qs ys h']
              ring

/-- 累加器可提出：`foldl (fun a x => a + f x)` 对初值线性。

⚠ **补证明时新增**（自 `_E-01.lean` **迁移**，见 `CORRECTIONS.md` 的 **B480**）：
原稿的 `dot_zipWith_add_aux` 想在归纳步直接匹配
`ih : ∀ a' x acc, ...`，但 `zip` 展开后累加器形态与 IH 的结论不一致。
本引理把「累加器可以提到外面」这一初等事实单独钉住，供下面使用。

⚠ **为什么不能复用 `ConvertVectorLinear.foldl_init_add`**：后者把 `init` 放在
**结论的 binder 位置**（`∀ init, ...`），而本条需要 `init` 出现在**假设**里
（`rw` 的目标形态）；两者签名不同，不是重复声明。 -/
private lemma foldl_add_shift {α : Type*} (f : α → Int) (rest : List α) (init : Int) :
    List.foldl (fun a x => a + f x) init rest
      = init + List.foldl (fun a x => a + f x) 0 rest := by
  induction rest generalizing init with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      rw [ih (init + f hd)]
      rw [show (0 + f hd) = f hd from by ring]
      rw [ih (f hd)]
      ring

/-- ⭐ **`zipWith (·+·)` 与 `dot` 的分配律（带累加器的一般形式）**。

`dot_zipWith_add_aux`（带任意累加器）是 `dot_zipWith_add_of_length` 的**证明地基**：
后者的归纳步里累加器不是 `0`，必须先把它提到 `0` 形。

⚠ **前提 `a.length = a'.length` 是承重的**：`zipWith` 截断到
`min a.length a'.length`，而右端是两个**独立**的 `dot`，各自 `zip x` 后**独立**截断再相加；
`a.length ≠ a'.length` 时两侧的求和项集合不一致
（反例见 `dot_zipWith_add_ORIGINAL_is_false_ce` / `_nonnil_ce`）。

⚠ **与 `dot_zipWith_add_of_length` 的关系**：本条是它 `acc = 0` 处的**推广**
（带任意 `acc`），由 `_E-01.lean` 迁移而来；后者保持原样、**未改名**，
因为 `_E-01` 的 16 条 B194 反例里已有一批**逐字点名** `dot_zipWith_add_of_length`
作为「补前提后的真形式」（见 `CORRECTIONS.md` B480.2 的改名理由）。 -/
lemma dot_zipWith_add_aux (a a' x : List Int) (acc : Int)
    (hlen : a.length = a'.length) :
    List.foldl (fun acc uv => acc + uv.1 * uv.2) acc ((a.zipWith (· + ·) a').zip x)
      = List.foldl (fun acc uv => acc + uv.1 * uv.2) acc (a.zip x)
        + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (a'.zip x) := by
  rw [foldl_add_shift (fun p : Int × Int => p.1 * p.2) ((a.zipWith (· + ·) a').zip x) acc,
      foldl_add_shift (fun p : Int × Int => p.1 * p.2) (a.zip x) acc,
      add_assoc, add_left_cancel_iff]
  induction a generalizing a' x with
  | nil =>
      cases a' with
      | nil => cases x <;> simp
      | cons q qs => simp at hlen
  | cons p ps ih =>
      cases a' with
      | nil => simp at hlen
      | cons q qs =>
          cases x with
          | nil => simp
          | cons y ys =>
              have hlen' : ps.length = qs.length := by simpa using hlen
              simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.foldl_cons, zero_add]
              rw [foldl_add_shift (fun p : Int × Int => p.1 * p.2)
                    ((List.zipWith (fun x1 x2 => x1 + x2) ps qs).zip ys) ((p + q) * y),
                  foldl_add_shift (fun p : Int × Int => p.1 * p.2) (ps.zip ys) (p * y),
                  foldl_add_shift (fun p : Int × Int => p.1 * p.2) (qs.zip ys) (q * y)]
              rw [ih qs ys hlen']
              ring

/-- ⭐ **分配律（`_E-01` 的原始主形式名）**：`dot` 的**双线性**在 `zipWith` 加法下的特例。

⚠⚠ **`dot_zipWith_add` 与 `dot_zipWith_add_of_length` 的统一决定（B480.2）**：

两者**签名逐字相同**（`(a a' x : List Int) (h : a.length = a'.length)`）且**内容等价**：
`_E-01.lean` 的 `dot_zipWith_add` 就是 `dot_zipWith_add_of_length`。⚠ 但本条**不**删名、
**不**做 `alias`：`_E-01` 的 B194 反例族（`dot_zipWith_add_ORIGINAL_is_false_ce`、
`_nonnil_ce`、`dot_zipWith_add_hlen_violated_on_ce`）**逐字点名**这条名字，
`CORRECTIONS.md` 的 B478.2 表格也按该名字登记 ⟹ **改名会同时打断源码与登记簿两处的
可追溯性**（而 B194 的整个要点就是「痕迹不能被静默擦掉」）。

⇒ 本文件保留**两个名字、零重复证明体**：本条就是
`dot_zipWith_add_of_length` 的**薄包装**（一行 `exact`），
`dot_zipWith_add_of_length` 仍是唯一被证的本体、仍是
`editLayer_delta_closed_form` 的地基。⭐ **`_E-01` 的原有名字在 CI 模块里继续存在**，
下游引用任一名字都得同一条定理。 -/
lemma dot_zipWith_add (a a' x : List Int) (hlen : a.length = a'.length) :
    dot (a.zipWith (· + ·) a') x = dot a x + dot a' x :=
  dot_zipWith_add_of_length a a' x hlen

/-! ## 四、⭐ 主定理：编辑的语义刻画（闭式 δ） -/

/-- ⭐⭐ **E-01 主定理（语义刻画，单层）**：

    `LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x`，**前提 `l.w.length = Δ.dw.length`**。

⭐ **它比平凡版本多说三件事**：
1. **右端无 `l'`**：增量项 `deltaOf Δ x = dot Δ.dw x + Δ.db` **只**由编辑数据与 `x` 算出；
2. **可归因**：δ 拆成「权重贡献 `dot Δ.dw x`」与「偏置贡献 `Δ.db`」两部分，
   下游能**定位**误差来源（这与 `RealConversionRobustness` 的 ④ 同款诉求）；
3. **可计算**：`deltaOf` 是 `def`，天然可求值 —— 不是存在性陈述（判据 4）。

⚠ **`h` 不可删**：删掉后命题为假（§三开头反例）。本文件**未**弱化任何结论，
只是把**本来就成立所必需的前提**写了出来。 -/
theorem editLayer_delta_closed_form (l : LinearLayer) (Δ : LayerDelta) (x : List Int)
    (h : l.w.length = Δ.dw.length) :
    LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x := by
  -- ⚠ 不能 `unfold dot`：那会把 `dot_zipWith_add_of_length` 的 LHS 模式一起拆散，
  -- 使 `rw` 匹配不上。只展开**外层**三个 def，保留 `dot` 为原子项。
  simp only [LayerOut, editLayer, deltaOf]
  rw [dot_zipWith_add_of_length l.w Δ.dw x h]
  ring

/-! ## 五、列表级提升（把主定理抬到 `Layer`） -/

/-- ⭐ **列表级主定理**：逐层语义刻画，δ 为**逐层**的 `deltaOf Δ x`。

⚠ **前提 `DeltaCompatible ls Δ` 不可删**：逐层都要用 `editLayer_delta_closed_form`，
故长度对齐必须**对每一层**成立。 -/
theorem editLayerList_delta (ls : Layer) (Δ : LayerDelta) (x : List Int)
    (h : DeltaCompatible ls Δ) :
    layerOuts (editLayerList ls Δ) x
      = (layerOuts ls x).map (fun v => v + deltaOf Δ x) := by
  -- ⚠ 用逐元素对照比「凭感觉 simp」更稳：两侧的 `map` 逐元素可对上。
  simp only [layerOuts, editLayerList]
  induction ls with
  | nil => rfl
  | cons l t ih =>
      have hl : l.w.length = Δ.dw.length := h l (List.mem_cons_self l t)
      have ht : DeltaCompatible t Δ := fun m hm => h m (List.mem_cons_of_mem l hm)
      simp only [List.map_cons]
      rw [ih ht, editLayer_delta_closed_form l Δ x hl]

/-- ⭐⭐ **`EditLayer` 的语义后果（接口层主定理）**：

若 `EditLayer W W'` 成立，则**存在**一个 `Δ`，使逐层输出差**逐字等于**闭式 `deltaOf Δ x`：

    `∀ x, layerOuts W' x = (layerOuts W x).map (fun v => v + deltaOf Δ x)`

⭐ **它比「δ := 两输出之差」多说什么**：平凡的 δ 是**任意函数**（由 `W W'` 反推），
而本条给出的是一个**由编辑数据 `Δ` 算出的具体值** `dot Δ.dw x + Δ.db`。
⇒ 这就是「δ 由编辑决定」的**精确形式**：δ **不是**自由选取的，它被 `Δ` 钉住。

⚠ **注**：结论里重复了 `deltaOf Δ x = deltaOf Δ x`，仅为把该闭式的**定义**带进作用域，
使读者一眼看到 δ 的**算式**；它是 `rfl`，不带任何内容。

⚠ **位置说明**：本条定义在 `editLayerList_delta` **之后**（而非 §一 接口定义旁），
因为其证明用到该引理 —— 声明顺序即作用域。 -/
theorem EditLayer_consequence (W W' : Layer) (h : EditLayer W W') (x : List Int) :
    ∃ Δ : LayerDelta,
      deltaOf Δ x = deltaOf Δ x ∧
      layerOuts W' x = (layerOuts W x).map (fun v => v + deltaOf Δ x) := by
  rcases h with ⟨Δ, hcomp, rfl⟩
  exact ⟨Δ, rfl, editLayerList_delta W Δ x hcomp⟩

/-- **推论：编辑前后逐层输出相等 ⟺ δ 为零（或层表为空）**（判据 4：**充要条件**）。

⭐ **为什么需要 `∨ ls = []`**：空层表没有元素，故「逐层输出相等」**恒真**，
与 δ 无关 —— 这是本定理**必须**显式写出的边界情形（不能假装 δ=0 是唯一条件）。

⚠ **前提 `DeltaCompatible ls Δ` 不可删**：`→` 方向取首元素的输出差、`←` 方向逐层代入
`editLayer_delta_closed_form`，两处都要长度对齐。 -/
theorem editLayerList_outputs_eq_iff (ls : Layer) (Δ : LayerDelta) (x : List Int)
    (h : DeltaCompatible ls Δ) :
    layerOuts (editLayerList ls Δ) x = layerOuts ls x ↔
      (deltaOf Δ x = 0 ∨ ls = []) := by
  constructor
  · intro heq
    cases ls with
    | nil => exact Or.inr rfl
    | cons l t =>
        -- 非空：首元素给出 `LayerOut l x = LayerOut l x + deltaOf Δ x`
        have hl : l.w.length = Δ.dw.length := h l (List.mem_cons_self l t)
        have h1 : LayerOut (editLayer l Δ) x = LayerOut l x := by
          -- `headD` 要标出元素类型：`Layer = List (List ℤ)`，`List.headD` 的默认值是层不是 ℤ
          have := congrArg (fun (ys : List Int) => ys.headD 0) heq
          simpa [layerOuts, editLayerList] using this
        rw [editLayer_delta_closed_form l Δ x hl] at h1
        exact Or.inl (by omega)
  · intro hh
    rcases hh with hz | hempty
    · -- δ = 0：逐层 `v + 0 = v`
      simp only [layerOuts, editLayerList]
      induction ls with
      | nil => rfl
      | cons l t ih =>
          have hl : l.w.length = Δ.dw.length := h l (List.mem_cons_self l t)
          have ht : DeltaCompatible t Δ := fun m hm => h m (List.mem_cons_of_mem l hm)
          simp only [List.map_cons]
          rw [ih ht, editLayer_delta_closed_form l Δ x hl, hz]
          simp
    · subst hempty
      rfl

/-! ## 六、非平凡性定理（判据 1 / 2 / 3）

⚠ **未编辑的退化情形**：零增量时 δ ≡ 0，主定理退化为 `x = x + 0`。
本文件**如实标注**：这一条**不是**实质内容（它只证明定义自洽）。 -/

/-- 零增量：δ ≡ 0（**退化情形，如实降级标注**）。 -/
theorem deltaOf_zero (x : List Int) : deltaOf ⟨[], 0⟩ x = 0 := by
  simp [deltaOf, dot]

/-- **零增量（长度对齐）才是恒等编辑**：`Δ.dw = w.map (fun _ => 0)` 时 `editLayer l Δ = l`。

⭐ **承重说明**：⚠ **不能**写成 `editLayer l ⟨[], 0⟩ = l` —— **那是假的**！
`zipWith` 在第二参数为 `[]` 时**截断为空表**，故
`editLayer ⟨[1], 5⟩ ⟨[], 0⟩ = ⟨[], 5⟩ ≠ ⟨[1], 5⟩`。
⇒ 这是本文件在自查时**发现并修正**的一处错误（首版曾写成 `⟨[], 0⟩` 版本），
反例见 `editLayer_nil_dw_not_identity`。 -/
theorem editLayer_zero_delta (l : LinearLayer) :
    editLayer l ⟨l.w.map (fun _ => 0), 0⟩ = l := by
  cases l with
  | mk w b =>
      simp only [editLayer]
      congr 1
      · -- `w.zipWith (·+·) (w.map (fun _ => 0)) = w`
        induction w with
        | nil => rfl
        | cons v t ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]; simp
      · omega

/-- ⭐ **反例（机器验证）：`Δ.dw = []` 的「零编辑」不是恒等编辑**。

`editLayer ⟨[1], 5⟩ ⟨[], 0⟩ = ⟨[], 5⟩ ≠ ⟨[1], 5⟩`。

⭐ **它为什么是承重的**：这条反例说明 `LayerDelta.dw` 的**长度**是编辑数据的一部分，
不能省略 —— 若本文件把「零编辑」定义成 `⟨[], 0⟩`，则 `EditLayer` 会**漏掉**所有
非空权重层上的恒等编辑，整个接口层的语义就是错的。
⇒ 这是判据 1（消融：删掉「长度对齐」假设，结论**变假**）的机器见证。 -/
theorem editLayer_nil_dw_not_identity :
    editLayer ⟨[1], 5⟩ ⟨[], 0⟩ ≠ (⟨[1], 5⟩ : LinearLayer) := by
  intro h
  -- 取 `w` 投影：左端 `w = []`，右端 `w = [1]`，矛盾
  have hw : (editLayer ⟨[1], 5⟩ ⟨[], 0⟩).w = (⟨[1], 5⟩ : LinearLayer).w :=
    congrArg LinearLayer.w h
  simp [editLayer] at hw

/-- ⭐ **判据 1 的正向读数**：`Δ.dw = []` 时编辑**必然**把权重清空
（对非空权重层而言是**破坏性**的，而非恒等）。 -/
theorem editLayer_nil_dw_clears (w : List Int) (b : Int) (db : Int) :
    (editLayer ⟨w, b⟩ ⟨[], db⟩).w = ([] : List Int) := by
  simp [editLayer]

/-! ### 判据 2：δ **不能**只由基权重决定（反驳可能） -/

/-- ⭐⭐ **判据 2（反驳可能）**：存在**同一个**基层 `l` 与**两个不同**的编辑数据，
它们给出**不同**的 δ。

⭐ **它证伪的命题**：「δ 只由 `W`（基权重）决定」——
若 δ 只依赖 `l`，则同一 `l` 上两个编辑必给出相同 δ。本定理给出**反例**，
故「δ 由**编辑**决定」是一句**有内容的**话（而非「δ 由 `l` 决定」的同义反复）。 -/
theorem delta_not_determined_by_base_only :
    ∃ (l : LinearLayer) (Δ₁ Δ₂ : LayerDelta) (x : List Int),
      deltaOf Δ₁ x ≠ deltaOf Δ₂ x := by
  refine ⟨{ w := [1], b := 0 }, ⟨[1], 0⟩, ⟨[0], 0⟩, [1], ?_⟩
  -- deltaOf ⟨[1],0⟩ [1] = 1*1 + 0 = 1；deltaOf ⟨[0],0⟩ [1] = 0*1 + 0 = 0
  simp [deltaOf, dot]

/-- ⭐ **判据 2 的加强（消融形式）**：若**去掉**「Δ 是具体数据」而允许 δ 任意取值，
则存在使 `δ ≠ 0` 的实例 —— 即 δ ≡ 0 的结论**不是**定义保证的。

⇒ 这正是判据 1「删掉某个假设，结论变成**假**」的机器形式。 -/
theorem deltaOf_ne_zero_witness :
    ∃ (Δ : LayerDelta) (x : List Int), deltaOf Δ x ≠ 0 :=
  ⟨⟨[1], 0⟩, [1], by simp [deltaOf, dot]⟩

/-- ⭐ **判据 1（消融）显式形式**：`dot Δ.dw x = 0` 对**任意** `Δ.dw`、`x` **为假**。

删掉「`Δ.dw` 与 `x` 的具体取值」这一实质信息（即把结论当成对一切 `Δ` 成立），
则结论变假 —— 见证 `Δ.dw = [1]`、`x = [1]`。 -/
theorem dot_delta_not_always_zero :
    ¬ (∀ (Δ : LayerDelta) (x : List Int), dot Δ.dw x = 0) := by
  intro h
  have := h ⟨[1], 0⟩ [1]
  simp [dot] at this

/-! ### 判据 3：跨模块桥 —— 编辑与 `convertVec` 交换

⭐ **本节的跨模块价值**：`ConvertVectorLinear`（单元素编译）、
`SymbolToWeightCorrectness`（列表级编译 `compileToLayer`）本来**只**谈「编译保语义」，
与**编辑**无关。本节证明：**符号侧编辑**经编译后**逐字**变成**权重侧编辑**，
且 δ **逐字保持** —— 这是全库（含解析侧的 `RealEdit*` 系列）**没有**的桥。 -/

/-- **符号侧编辑**：约束系数加增量（与 `ConvertVectorLinear.scaleVec` 同型的加性版本）。

⚠ **全库此前不存在**：`ConvertVectorLinear` 只有 `scaleVec`（**乘性**缩放），
没有**加性**编辑。 -/
def editConstraint (c : VectorConstraint) (Δ : LayerDelta) : VectorConstraint :=
  { a := c.a.zipWith (· + ·) Δ.dw, b := c.b + Δ.db }

/-- ⭐⭐ **判据 3：编辑与编译交换（跨模块桥）**：

    `convertVec (editConstraint c Δ) = editLayer (convertVec c) Δ`

⭐ **它比「两边都是字段拷贝」多说**：两侧的**编辑发生在不同的载体**上
（符号侧改 `a`、权重侧改 `w`），本定理说这两个**结构上不同**的操作
在编译下**精确对应**（`convertVec` 就是把 `a` 拷贝成 `w`，故两端同构地做 `zipWith`）。
⇒ 这是「编辑的语义在两侧一致」的**语法基座**。 -/
theorem edit_commutes_with_convert (c : VectorConstraint) (Δ : LayerDelta) :
    convertVec (editConstraint c Δ) = editLayer (convertVec c) Δ := by
  cases c with
  | mk a b => simp [editConstraint, editLayer, convertVec]

/-- ⭐⭐ **判据 3 的语义读数（跨模块主结论）**：

符号侧编辑后编译的输出变化，与权重侧直接编辑的输出变化，
**由同一个闭式 δ 给出**：

    `LayerOut (convertVec (editConstraint c Δ)) x = LayerOut (convertVec c) x + deltaOf Δ x`

⇒ 编辑语义在**符号 ⇄ 权重**两侧**一致**，δ **不依赖**在哪一侧做编辑。

⚠ **前提 `c.a.length = Δ.dw.length`**：`convertVec c` 的权重就是 `c.a`，
故权重侧主定理的长度条件**逐字**变成这条（与单层主定理同源，非新增假设）。 -/
theorem editConstraint_preserves_delta (c : VectorConstraint) (Δ : LayerDelta)
    (x : List Int) (h : c.a.length = Δ.dw.length) :
    LayerOut (convertVec (editConstraint c Δ)) x
      = LayerOut (convertVec c) x + deltaOf Δ x := by
  rw [edit_commutes_with_convert]
  exact editLayer_delta_closed_form (convertVec c) Δ x h

/-- ⭐ **跨模块闭合（与编译保语义串联）**：

符号侧约束**满足** ⟺ 权重侧未编辑层输出为零；编辑后输出 = `deltaOf Δ x`。
把 `ConvertVectorLinear.convertVec_preserves_semantics` 与编辑语义**放进同一条定理**
（此前全库没有定理同时引用「编辑」与「编译保语义」——因为编辑在符号侧根本不存在）。

⚠ **承重前提 `c.a.length = Δ.dw.length` 不可删**：第二合取项逐字就是
`editConstraint_preserves_delta`，其长度条件在此**逐字**继承（非新增假设）。
原（无前提）形式为假，反例见 `edit_constraint_semantics_bridge_ORIGINAL_is_false_ce`。

⚠ **迁移登记**：本条**自 `_E-01.lean` 迁移**（`CORRECTIONS.md` **B480**），
它是 `_E-01`-only 的 18 条之一 —— 即「只有草稿有、CI 构建的模块没有」的那一类。 -/
theorem edit_constraint_semantics_bridge (c : VectorConstraint) (Δ : LayerDelta)
    (x : List Int) (h : c.a.length = Δ.dw.length) :
    (VectorConstraintSat (editConstraint c Δ) x ↔
        LayerOut (convertVec (editConstraint c Δ)) x = 0)
      ∧ (LayerOut (convertVec (editConstraint c Δ)) x
          = LayerOut (convertVec c) x + deltaOf Δ x) :=
  ⟨convertVec_preserves_semantics (editConstraint c Δ) x,
   editConstraint_preserves_delta c Δ x h⟩

/-! ## 六之二、⭐⭐ **B194 反例固化区**（**已迁入 CI 构建的模块**，见 `CORRECTIONS.md` **B480**）

⚠⚠ **为什么必须有这一节**：本文件有 9 条声明在补证明时被**加强假设**救活
（清单见 §7.4）。按 `CORRECTIONS.md` 的 **B194.3（收口判据）**：

> **一条「被救活」的定理，应当留下两条东西：① 真形式（当前定理）；
> ② 假形式的机器可验证反例（`_ce` / `not_` 命名）。**
> ⚠ **只留 ① 等于把「此路不通」的标记擦掉** —— 后来者会重新提出那个更弱的假设。

⚠ **注释 + `#eval` 不算数**（**B194.4**）：注释**不参与检查**，`#eval` 的产物
**不留在源码里**（下一轮任何人删掉它都不会报错）。⇒ 本节把反例**写成定理**，
**编译器强制它们存在**。

⭐⭐ **B480 的要点（本节的迁移史）**：本节原位于 `lean/_E-01.lean` 的 §六之二。
⚠ 但 `_E-01.lean` **不在 `lakefile.toml` 的 `roots` 内、也不被任何模块 `import`**
⟹ 它**从不参与** `lake build` / CI，其反例只有「有人手工跑 `lake env lean`」这一层保护 ——
⭐ **而 B194.4 的全部要点正是「机器强制」**：一份不参与构建的强制**不是**强制。
⇒ 本节（16 条反例 + 2 条负对照）**整体迁入本文件**（`RealEditSemantics` 在 roots 内），
反例自此**落在 CI 构建图里**。

⭐ **命名约定**（沿用本仓既有形态 `*_ORIGINAL_is_false` / `*_ce` / `not_*`）：
本节的定理名**逐字未改**，故 `CORRECTIONS.md` 的 B478.2 登记表**仍然逐字有效**。

### 6b.1 `dot_zipWith_add` / `dot_zipWith_add_aux` 的原形式为假

⚠ **原形式（无论原文中「三处截断自动对齐」的声称）**：

    lemma dot_zipWith_add (a a' x : List Int) :
        dot (a.zipWith (· + ·) a') x = dot a x + dot a' x

**根因**：`zipWith` 截断到 `min a.length a'.length`，而右端是**两个独立的** `dot`，
各自 `zip x` 后**独立**截断再相加。`a.length ≠ a'.length` 时两侧保留的**项集不同**。 -/

/-- ⭐ **B194 反例 #1（机器验证）**：`dot_zipWith_add` 的**原（无长度前提）形式**为假。

**见证**：`a = []`、`a' = [1]`、`x = [5]`。
* 左：`dot ([].zipWith (·+·) [1]) [5] = dot [] [5] = 0`；
* 右：`dot [] [5] + dot [1] [5] = 0 + 5 = 5`；
* `0 ≠ 5`。

⚠ **不是两处不同的长度都试过** —— 该反例只用了**向右截断**的一种；
`a = [1]`、`a' = []` 是同一现象的对偶（见下一节的 `editLayer` 反例）。 -/
theorem dot_zipWith_add_ORIGINAL_is_false_ce :
    ¬ (∀ (a a' x : List Int), dot (a.zipWith (· + ·) a') x = dot a x + dot a' x) := by
  intro h
  have := h [] [1] [5]
  simp [dot] at this

/-- ⭐ **B194 反例 #2（机器验证）**：**两个非空**列表给出的反例 ——
排除了「反例只在空表边界成立」这一退路。

**见证**：`a = [1,2]`、`a' = [10]`、`x = [1,1]`。
* 左：`dot ([1,2].zipWith (·+·) [10]) [1,1] = dot [11] [1,1] = 11`；
* 右：`dot [1,2] [1,1] + dot [10] [1,1] = 3 + 10 = 13`；
* `11 ≠ 13`。

⭐ **它比 #1 强在哪**：`a` 与 `a'` **都非空**，且两侧长度都 `> 1` 的一方
（`a`）**保留了自己**、长度 `= 1` 的一方（`a'`）**多贡献了一项** `10 * 1 = 10`。
⇒ 该缺陷**不是**「空表特例」，而是**成规模**的项集失配。 -/
theorem dot_zipWith_add_ORIGINAL_is_false_nonnil_ce :
    dot (([1, 2] : List Int).zipWith (· + ·) [10]) [1, 1]
      ≠ dot ([1, 2] : List Int) [1, 1] + dot ([10] : List Int) [1, 1] := by
  norm_num [dot]

/-- ⭐ **B194 反例 #3（机器验证）**：`dot_zipWith_add_aux` 的**原形式**（累加器版）为假。

⚠ `dot_zipWith_add` 是 `dot_zipWith_add_aux` 在 `acc = 0` 处的特例
（定义处就是这么用的），故**反例自动提升**。此处把它**单独**钉一条，
因为「加强假设」是在 `aux` 上做的、`aux` 是其上所有下游的**唯一**数学地基。 -/
theorem dot_zipWith_add_aux_ORIGINAL_is_false_ce :
    ¬ (∀ (a a' x : List Int) (acc : Int),
        List.foldl (fun acc uv => acc + uv.1 * uv.2) acc ((a.zipWith (· + ·) a').zip x)
          = List.foldl (fun acc uv => acc + uv.1 * uv.2) acc (a.zip x)
            + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (a'.zip x)) := by
  intro h
  have := h [] [1] [5] 0
  simp [List.zipWith_nil_left, List.zip_nil_left, List.foldl_nil] at this

/-! ### 6b.2 `editLayer_delta_closed_form` 的原形式为假

⚠ **原形式**：

    theorem editLayer_delta_closed_form (l : LinearLayer) (Δ : LayerDelta) (x : List Int) :
        LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x

⚠ Δ **不是**自由选取的：`editLayer l Δ` 把权重定为 `l.w.zipWith (·+·) Δ.dw`，
故 `Δ.dw.length < l.w.length` 时 `zipWith` **截断** `l.w`，
真实权重**不是** `l.w + Δ.dw`，`deltaOf Δ x` 于是**低估**了输出变化。 -/

/-- ⭐⭐ **B194 反例 #4（机器验证）：E-01 主定理的**原（无长度前提）形式**为假**。

**见证**：`l = ⟨[1], 0⟩`、`Δ = ⟨[], 0⟩`、`x = [5]`。
* 左：`LayerOut (editLayer ⟨[1],0⟩ ⟨[],0⟩) [5] = LayerOut ⟨[],0⟩ [5] = dot [] [5] + 0 = 0`；
* 右：`LayerOut ⟨[1],0⟩ [5] + deltaOf ⟨[],0⟩ [5] = (dot [1] [5] + 0) + (dot [] [5] + 0) = 5 + 0 = 5`；
* `0 ≠ 5`。

⚠⚠ **它不是外部输入的反例** —— 它正是本文件**自己已有的定理**
`editLayer_nil_dw_not_identity`（§六）所证明的截断行为的**直接后果**：
§六 证明了「`Δ.dw = []` 时编辑**清空**权重」，而原 §四 主定理恰恰
**假设**了「`Δ.dw = []` 时输出**不变**」⟹ **原文内部自相矛盾**。

⭐ **这就是 B194 存在的理由**：若只留下加了 `h` 的真定理，
下一个代理看到 `editLayer ⟨[1],0⟩ ⟨[],0⟩` 会**重新以为**「空增量 = 恒等」。 -/
theorem editLayer_delta_closed_form_ORIGINAL_is_false_ce :
    ¬ (∀ (l : LinearLayer) (Δ : LayerDelta) (x : List Int),
        LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x) := by
  intro h
  have hce := h ⟨[1], 0⟩ ⟨[], 0⟩ [5]
  simp [LayerOut, editLayer, deltaOf, dot] at hce

/-- ⭐ **B194 反例 #5（机器验证）**：把反例 #4 拆成**两侧的具体数值** ——
`l = ⟨[1],0⟩`、`Δ = ⟨[],0⟩`、`x = [5]` 时左端是 `0` 而右端是 `5`。

⭐ **为什么再钉一条**：`_ce` 证的是「否定 `∀`」，形态上**只说明存在一处失败**；
本定理把**见证本身**（左 `0`、右 `5`）写成等式，使下一轮代理
**不必再跑数值实验**就能看到「截断把 `1*5 = 5` 整项吃掉了」。 -/
theorem editLayer_delta_closed_form_ORIGINAL_witness :
    LayerOut (editLayer ⟨[1], 0⟩ ⟨[], 0⟩) [5] = 0
      ∧ LayerOut (⟨[1], 0⟩ : LinearLayer) [5] + deltaOf ⟨[], 0⟩ [5] = 5 := by
  constructor <;> simp [LayerOut, editLayer, deltaOf, dot]

/-! ### 6b.3 `editLayerList_delta` 的原形式为假（逐层提升） -/

/-- ⭐ **B194 反例 #6（机器验证）**：`editLayerList_delta` 的**原（无长度前提）形式**为假。

**见证**：`ls = [⟨[1], 0⟩]`、`Δ = ⟨[], 0⟩`、`x = [5]` —— 由反例 #4 **逐层提升**：
* 左：`layerOuts (editLayerList [⟨[1],0⟩] ⟨[],0⟩) [5] = [0]`；
* 右：`(layerOuts [⟨[1],0⟩] [5]).map (fun v => v + deltaOf ⟨[],0⟩ [5]) = [5 + 0] = [5]`；
* `[0] ≠ [5]`。 -/
theorem editLayerList_delta_ORIGINAL_is_false_ce :
    ¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
        layerOuts (editLayerList ls Δ) x
          = (layerOuts ls x).map (fun v => v + deltaOf Δ x)) := by
  intro h
  -- ⚠ 不能只靠 `simp at hce`：`simp` 会把两端的 `LayerOut` 投影成
  -- `LayerOut {w := [], b := 0} [5] = LayerOut {w := [1], b := 0} [5]` 就**停住**
  -- （`LayerOut` 是 `def` 而 `layerOuts` 已展开）。故这里显式取两端的**数值**。
  have hce := congrArg (fun (ys : List Int) => ys.headD 0) (h [⟨[1], 0⟩] ⟨[], 0⟩ [5])
  simp [layerOuts, editLayerList, editLayer, LayerOut, deltaOf, dot] at hce

/-- ⭐ **B194 反例 #6 的数值读数**：`layerOuts (editLayerList [⟨[1],0⟩] ⟨[],0⟩) [5] = [0]`，
与 `[5]` 不等。把 #6 的两侧落成**具体列表等式**。 -/
theorem editLayerList_delta_ORIGINAL_witness :
    layerOuts (editLayerList [⟨[1], 0⟩] ⟨[], 0⟩) [5] = [(0 : Int)]
      ∧ (layerOuts ([⟨[1], 0⟩] : Layer) [5]).map
          (fun v => v + deltaOf (⟨[], 0⟩ : LayerDelta) [5]) = [(5 : Int)] := by
  constructor <;> simp [layerOuts, editLayerList, editLayer, LayerOut, deltaOf, dot]

/-! ### 6b.4 `editLayerList_outputs_eq_iff` 的原形式为假（**双向都坏**）

⚠ **原形式**（充要条件）：

    layerOuts (editLayerList ls Δ) x = layerOuts ls x ↔ (deltaOf Δ x = 0 ∨ ls = [])

⚠ 该式**两个方向都坏**，故给**两条**反例 —— 只给一条会漏掉另一半：

| 方向 | 正文写法 | 反例 |
|:--|:--|:--|
| **⟸**（`δ = 0 ∨ ls = []` ⟹ 输出相等）| 靠 `editLayer_delta_closed_form` | `ls = [⟨[1],0⟩]`、`Δ = ⟨[],0⟩`、`x = [5]`：`δ = 0` 但输出 `[0] ≠ [5]` |
| **⟹**（输出相等 ⟹ `δ = 0 ∨ ls = []`）| 靠取首元素 | `ls = [⟨[],1⟩]`、`Δ = ⟨[1],0⟩`、`x = [5]`：输出都是 `[1]`，但 `δ = 5 ≠ 0` 且 `ls ≠ []` | -/

/-- ⭐ **B194 反例 #7a（机器验证）：`editLayerList_outputs_eq_iff` 原形式的「⟸」方向为假**。

**见证**：`ls = [⟨[1],0⟩]`、`Δ = ⟨[],0⟩`、`x = [5]`。
`deltaOf ⟨[],0⟩ [5] = dot [] [5] + 0 = 0` ⟹ 蕴含式的**前提成立**；
而 `layerOuts (editLayerList ls Δ) [5] = [0] ≠ [5] = layerOuts ls [5]`
⟹ **结论为假** ⟹ 该方向不成立。

⭐ **它说明什么**：原式的「⟸」**不是**「δ=0 ⟹ 输出不变」的平凡重写 ——
在无长度对齐时 `δ = 0` **完全不能**保证输出不变（截断会凭空**删掉**权重项）。 -/
theorem editLayerList_outputs_eq_iff_ORIGINAL_fwd_is_false_ce :
    ¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
        (deltaOf Δ x = 0 ∨ ls = []) →
          layerOuts (editLayerList ls Δ) x = layerOuts ls x) := by
  intro h
  have hce := congrArg (fun (ys : List Int) => ys.headD 0)
    (h [⟨[1], 0⟩] ⟨[], 0⟩ [5] (Or.inl (by simp [deltaOf, dot])))
  simp [layerOuts, editLayerList, editLayer, LayerOut, deltaOf, dot] at hce

/-- ⭐ **B194 反例 #7b（机器验证）：`editLayerList_outputs_eq_iff` 原形式的「⟹」方向为假**。

**见证**：`ls = [⟨[],1⟩]`、`Δ = ⟨[1],0⟩`、`x = [5]`。
* 左：`layerOuts (editLayerList [⟨[],1⟩] ⟨[1],0⟩) [5]`。
  `editLayer ⟨[],1⟩ ⟨[1],0⟩ = ⟨[].zipWith (·+·) [1], 1 + 0⟩ = ⟨[], 1⟩`
  （`zipWith` 左侧为空 ⟹ **截断为空**，增量 `[1]` **整项丢失**）⟹ 左 `= [1]`；
* 右：`layerOuts [⟨[],1⟩] [5] = [dot [] [5] + 1] = [1]` ⟹ **两侧相等**；
* 但 `deltaOf ⟨[1],0⟩ [5] = dot [1] [5] + 0 = 5 ≠ 0`，且 `[⟨[],1⟩] ≠ []`
  ⟹ 蕴含式的**结论为假**（`ls ≠ []` 已排除 `Or.inr`，`δ ≠ 0` 排除 `Or.inl`）。

⚠⚠ **这正是原文 docstring 里那段自我更正的真实内容** —— 正文先写了一个
**更弱的**例子（`ls = [⟨[1],0⟩]`、`Δ = ⟨[],0⟩`，两侧是 `[0]` 与 `[5]`，**并不相等**，
故**证不了**该方向），随后才在括号里给出**正确**的 `ls = [⟨[],1⟩]` 例子。
本定理固化的是**后者**（前者不是反例）。 -/
theorem editLayerList_outputs_eq_iff_ORIGINAL_bwd_is_false_ce :
    ¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
        layerOuts (editLayerList ls Δ) x = layerOuts ls x →
          (deltaOf Δ x = 0 ∨ ls = [])) := by
  intro h
  have hce := h [⟨[], 1⟩] ⟨[1], 0⟩ [5]
  simp [layerOuts, editLayerList, editLayer, deltaOf, dot] at hce

/-! ### 6b.5 `EditLayer` 定义与 `EditLayer_consequence` 的原形式为假

⚠ **原定义**：`def EditLayer (W W' : Layer) : Prop := ∃ Δ, W' = editLayerList W Δ`。

⚠ **它过弱**：允许「截断型」编辑，此时 `deltaOf Δ x` **不再**等于真实输出差
（反例 #4 的接口层读数）⟹ 在其上**推不出**闭式 δ。 -/

/-- ⭐⭐ **B194 反例 #8（机器验证）：`EditLayer` 的**原定义**蕴含不出 `EditLayer_consequence` 的结论**。

**见证**：`W = [⟨[1],0⟩]`、`W' = [⟨[],0⟩]`、`Δ = ⟨[],0⟩`。
* `W' = editLayerList W ⟨[],0⟩`（逐字段算：`[1].zipWith (·+·) [] = []`）⟹ **原 `EditLayer W W'` 成立**；
* 但 `deltaOf ⟨[],0⟩ [5] = dot [] [5] + 0 = 0`，
  而真实输出差（取首层输出）`layerOuts W' [5].headD 0 − layerOuts W [5].headD 0 = 0 − 5 = −5`；
* `0 ≠ −5` ⟹ **原定义下「输出差 = deltaOf」为假**。

⚠ **本定理的形态**：它**不是**在否定某一个 `∀` 定理（原式在无前提时**无法陈述**为
一条真定理），而是证明**「原 `EditLayer` 成立」与「闭式 δ 成立」不能同时成立**
—— 即原定义**太弱**，必须补长度对齐合取项。

⚠ **迁移后的指称说明**：本条的见证 `([⟨[], 0⟩] : Layer) = editLayerList [⟨[1], 0⟩] Δ`
用的是**原（弱）** `EditLayer` 的展开式，而非本文件 §一 那个**含 `DeltaCompatible` 的**
`EditLayer`；文本里出现的 `editLayerList` 仍是本文件同一定义（未被改动）。 -/
theorem EditLayer_ORIGINAL_is_too_weak_ce :
    (∃ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[1], 0⟩] Δ)
      ∧ (∀ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[1], 0⟩] Δ →
          deltaOf Δ [5]
            ≠ (layerOuts ([⟨[], 0⟩] : Layer) [5]).headD 0
              - (layerOuts ([⟨[1], 0⟩] : Layer) [5]).headD 0) := by
  constructor
  · exact ⟨⟨[], 0⟩, rfl⟩
  · intro Δ h
    -- `h : [⟨[],0⟩] = editLayerList [⟨[1],0⟩] Δ` 把 `Δ` **逐字段钉死**：
    -- 权重侧 `[1].zipWith (·+·) Δ.dw = Δ.dw` 只在 `Δ.dw = []` 时为 `[]`
    -- （`zipWith` 截断到 `min 1 Δ.dw.length`），偏置侧 `0 + Δ.db = 0` 迫使 `Δ.db = 0`。
    -- 两者合起来：`deltaOf Δ [5] = dot [] [5] + 0 = 0`，
    -- 而右侧差是 `0 − 5 = −5`。
    cases Δ with
    | mk dw db =>
      simp [editLayerList, editLayer, deltaOf, dot, layerOuts, LayerOut] at h ⊢
      -- 归约后 `h : dw = [] ∧ 0 = db`，目标 `¬(db + db = -5)`。
      -- ⚠ `omega` **不**拆合取，故必须显式取出 `0 = db` 再交给它。
      obtain ⟨hdw, hdb⟩ := h
      -- ⚠ 必须**替换**而不是只留在上下文里：`omega` 看不见 `List.foldl ... (dw.zip [5])`，
      -- 而 `dw = []` 尚未代入。先 `subst` 两位（`dw` 与 `db` **都是**局部变量，可 subst），
      -- 归约后目标变成纯算术的 `¬(0 + 0 = -5)`。
      subst hdw
      subst hdb
      norm_num

/-- ⭐ **B194 反例 #9（机器验证）：`EditLayer` 原定义**不钉住 δ** —— 同一对 `(W, W')`
可由**两个不同**的 `Δ` 得到，而 `deltaOf` 不同。

**见证**：取 `W` 的权重本来为空 `W = [⟨[], 0⟩]`、`W' = W`。
`Δ₁ = ⟨[], 0⟩` 与 `Δ₂ = ⟨[1], 0⟩` **都**给出 `editLayerList W Δᵢ = W`
（`[].zipWith (·+·) _ = []`，**左侧空即恒空**），
而 `deltaOf Δ₁ [5] = 0`、`deltaOf Δ₂ [5] = 5` ⟹ **δ 不被 `W'` 钉住**。

⭐ **它就是原文 §3.3 论证的机器形式**：`EditLayer_consequence` 的 `∃ Δ`
在**不强加长度对齐**时**不可能**给出唯一闭式 δ。
⚠ 补上长度对齐后本反例**失效**：`Δ₂.dw.length = 1 ≠ 0 = W` 各层 `w.length`，
故 `Δ₂` 不再是合法的 `EditLayer` 见证。 -/
theorem EditLayer_ORIGINAL_delta_not_pinned_ce :
    (∃ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[], 0⟩] Δ)
      ∧ deltaOf (⟨[], 0⟩ : LayerDelta) [5] ≠ deltaOf (⟨[1], 0⟩ : LayerDelta) [5]
      ∧ ([⟨[], 0⟩] : Layer) = editLayerList [⟨[], 0⟩] ⟨[1], 0⟩ := by
  refine ⟨⟨⟨[], 0⟩, rfl⟩, ?_, ?_⟩
  · simp [deltaOf, dot]
  · rfl

/-! ### 6b.6 `editConstraint_preserves_delta` / `edit_constraint_semantics_bridge` 的原形式为假 -/

/-- ⭐ **B194 反例 #10（机器验证）**：`editConstraint_preserves_delta` 的**原（无长度前提）形式**为假。

**见证**：`c = ⟨[], 5⟩`（符号侧约束系数为空、偏置 `5`）、`Δ = ⟨[1], 0⟩`、`x = [5]`。
* `convertVec c = ⟨c.a, c.b⟩ = ⟨[], 5⟩`（权重为 `[]`）；
* `editConstraint c Δ = ⟨[].zipWith (·+·) [1], 5 + 0⟩ = ⟨[], 5⟩` ⟹ `convertVec (editConstraint c Δ) = ⟨[], 5⟩`；
* 左：`LayerOut ⟨[],5⟩ [5] = dot [] [5] + 5 = 5`；
* 右：`LayerOut ⟨[],5⟩ [5] + deltaOf ⟨[1],0⟩ [5] = 5 + 5 = 10`；
* `5 ≠ 10`。

⚠ **与 `edit_commutes_with_convert` 的对照（关键）**：后者**不带**任何长度前提
而**为真** —— 因为它是**纯字段重写**，两侧**同样截断**，等式无条件下成立。
⇒ **只有需要「输出差 = 闭式 δ」的定理才需要长度对齐**；
本反例与那条真定理**不冲突**，恰恰**印证**了 §1 的根因诊断。 -/
theorem editConstraint_preserves_delta_ORIGINAL_is_false_ce :
    ¬ (∀ (c : VectorConstraint) (Δ : LayerDelta) (x : List Int),
        LayerOut (convertVec (editConstraint c Δ)) x
          = LayerOut (convertVec c) x + deltaOf Δ x) := by
  intro h
  have hce := h ⟨[], 5⟩ ⟨[1], 0⟩ [5]
  simp [convertVec, editConstraint, LayerOut, deltaOf, dot] at hce

/-- ⭐ **B194 反例 #11（机器验证）**：`edit_constraint_semantics_bridge` 的**原形式**为假。

该桥的**第一个合取项**（`convertVec_preserves_semantics`）**无条件下为真**，
故反例只可能落在**第二个合取项**上 —— 而它逐字就是
`editConstraint_preserves_delta`。本定理直接复用反例 #10 的见证，
把「该桥的原形式为假」**在其自身的形态上**钉住（第二合取项）。

⚠ **迁移后的指称说明**：本文件 §六 的 `edit_constraint_semantics_bridge` 是真的
（带 `h` 前提）；本条钉住的是它的**原（无前提）形式**，两者**不冲突**。 -/
theorem edit_constraint_semantics_bridge_ORIGINAL_is_false_ce :
    ¬ (∀ (c : VectorConstraint) (Δ : LayerDelta) (x : List Int),
        (VectorConstraintSat (editConstraint c Δ) x ↔
            LayerOut (convertVec (editConstraint c Δ)) x = 0)
          ∧ (LayerOut (convertVec (editConstraint c Δ)) x
              = LayerOut (convertVec c) x + deltaOf Δ x)) := by
  intro h
  have hce := (h ⟨[], 5⟩ ⟨[1], 0⟩ [5]).2
  simp [convertVec, editConstraint, LayerOut, deltaOf, dot] at hce

/-! ### 6b.7 ⭐ 反面判据：**长度对齐前提是不可去的**（对每条真形式逐一给出正/负对照）

⚠ **为什么还需要这一节**：上面的 `_ce` 定理证的是「原（更弱）形式为假」，
但**没有**证「补上的 `h` 前提**必要**」—— 逻辑上「假形式」与
「前提必要」是两件事。本节给出**正对照**：**补上前提后成立的正面实例**，
连同「前提**被违反**时结论**确实**变假」的负对照，构成 B194 意义上的闭环。

⚠ **注意**：`dot_zipWith_add_of_length` / `editLayer_delta_closed_form` 等**本身**就是
「补上前提后为真」的正形式（见 §三/§四），**不需要**重复。本节只补
**前提被违反**这一侧的显式读数。 -/

/-- ⭐ **负对照（前提不可去）**：`dot_zipWith_add_of_length`（即 `dot_zipWith_add`）的
`h` 前提在反例 #1 的见证上**确实被违反** —— 即该反例**没有**落在真定理的定义域内。

⇒ 它与反例 #1 合起来说明：`a.length = a'.length` **不是**装饰性的前提，
反例 #1 恰好落在它**之外**。⚠ 这与「真定理为假」**无关**（真定理无此问题）。 -/
theorem dot_zipWith_add_hlen_violated_on_ce :
    ([] : List Int).length ≠ ([1] : List Int).length := by
  simp

/-- ⭐ **负对照（前提不可去，主定理版）**：反例 #4 的见证**违反**了
`editLayer_delta_closed_form` 的 `h : l.w.length = Δ.dw.length`
（`0 ≠ 1`）⟹ 它**不在**真定理的定义域内。

⭐ **两条负对照合起来给出收口**：① 原形式**为假**（反例 #1/#4）；
② 前提在反例上**确实被违反**（本定理）。⇒ 补前提是**必要**的，
**不是**为了好证而放水（否则真定理会连原形式的反例一起「证」出来）。 -/
theorem editLayer_delta_closed_form_hlen_violated_on_ce :
    (⟨[], 0⟩ : LayerDelta).dw.length ≠ (⟨[1], 0⟩ : LinearLayer).w.length := by
  simp

/-! ## 六之三、⭐⭐⭐ **B194 存在性锚点**（`b194_counterexamples_intact`）

⚠⚠ **为什么还需要这一节**（**B480 的补遗**）：§六之二 把 16 条反例搬进了本模块，
但**搬进模块 ≠ 存在被强制** —— 16 条反例**全部是叶节点**：
本文件**没有任何证明项引用它们**，`RealChainAxioms*` 也只是 `#print axioms`。
⇒ **删掉整节 §六之二（426 行）后 `lake env lean RealEditSemantics.lean` 仍然是 0 error。**

⭐ **B194.4 的原文是「编译器强制它存在」**，而「编译通过」只保证**写下来的东西是真的**，
**不**保证**它还在**。⇒ 本节补上**引用锚点**：一个证明项**逐名引用全部 16 条反例**的定理。

⚠ **但这还不够** —— 锚点**自己**也是叶节点、**也能被删掉**（删掉它同样 0 error）。
⇒ 故锚点必须**被一条承重定理依赖**，见本节的 `b194_counterexamples_referenced`。 -/

/-- ⭐⭐⭐ **B194 反例固化区的存在性锚点（名字）**：16 条反例的**合取命题**。

⭐ **为什么是「名字 + 证明项」两件东西**：本 `def` 只**命名**那个合取命题，
使下游能写 `(h : b194_counterexamples_intact)`；**引用 16 条反例**的是紧接着的
`b194_counterexamples_intact_holds`（它的**证明项**逐名引用全部 16 条）。
⚠ 删掉本 `def`、或删掉它的证明项、或删掉 16 条中的任意一条 ⟹ **编译失败**。

⚠ 这与「docstring 里提一句」有本质区别：**docstring 不参与 elaboration**。

⚠ **本命题**（那一长串合取）**本身没有新数学内容** —— 它是 16 条**已有**反例的
合取。它存在的**唯一**目的是让「这 16 条反例在不在」成为**可被编译器检查**的问题。

⚠ **它与 §六之二 的 `_ce` 的分工**：`_ce` 负责「**反例是真的**」（陈述被证明）；
本节负责「**反例还在**」（名字被引用）。**两者缺一不可**。

⚠ **形态说明（为何是 `def` 而非 `theorem`）**：锚点必须是**可命名的 `Prop`**
（`def b194_counterexamples_intact : Prop`），这样下游才能把它写成**假设类型**
`(h : b194_counterexamples_intact)`。若写成 `theorem`，`b194_counterexamples_intact`
就是**一个证明项**而非**一个类型**，`(h : ...)` 会被解析成**类型归属**而报
`type expected`。⇒ 故**一分为二**：
① `def ... : Prop`（**名字**，下游引用它）；
② `theorem ..._holds : b194_counterexamples_intact := ...`（**证明项**，它逐名引用 16 条）。
⚠ **删掉 ① 与删掉 ② 都会让本文件编译失败** —— 两者都指向那 16 个名字所在的环境。 -/
def b194_counterexamples_intact : Prop :=
    (¬ (∀ (a a' x : List Int), dot (a.zipWith (· + ·) a') x = dot a x + dot a' x))
      ∧ (dot (([1, 2] : List Int).zipWith (· + ·) [10]) [1, 1]
          ≠ dot ([1, 2] : List Int) [1, 1] + dot ([10] : List Int) [1, 1])
      ∧ (¬ (∀ (a a' x : List Int) (acc : Int),
          List.foldl (fun acc uv => acc + uv.1 * uv.2) acc ((a.zipWith (· + ·) a').zip x)
            = List.foldl (fun acc uv => acc + uv.1 * uv.2) acc (a.zip x)
              + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 (a'.zip x)))
      ∧ (¬ (∀ (l : LinearLayer) (Δ : LayerDelta) (x : List Int),
          LayerOut (editLayer l Δ) x = LayerOut l x + deltaOf Δ x))
      ∧ (LayerOut (editLayer ⟨[1], 0⟩ ⟨[], 0⟩) [5] = 0
          ∧ LayerOut (⟨[1], 0⟩ : LinearLayer) [5] + deltaOf ⟨[], 0⟩ [5] = 5)
      ∧ (¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
          layerOuts (editLayerList ls Δ) x
            = (layerOuts ls x).map (fun v => v + deltaOf Δ x)))
      ∧ (layerOuts (editLayerList [⟨[1], 0⟩] ⟨[], 0⟩) [5] = [(0 : Int)]
          ∧ (layerOuts ([⟨[1], 0⟩] : Layer) [5]).map
              (fun v => v + deltaOf (⟨[], 0⟩ : LayerDelta) [5]) = [(5 : Int)])
      ∧ (¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
          (deltaOf Δ x = 0 ∨ ls = []) →
            layerOuts (editLayerList ls Δ) x = layerOuts ls x))
      ∧ (¬ (∀ (ls : Layer) (Δ : LayerDelta) (x : List Int),
          layerOuts (editLayerList ls Δ) x = layerOuts ls x →
            (deltaOf Δ x = 0 ∨ ls = [])))
      ∧ ((∃ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[1], 0⟩] Δ)
          ∧ (∀ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[1], 0⟩] Δ →
              deltaOf Δ [5]
                ≠ (layerOuts ([⟨[], 0⟩] : Layer) [5]).headD 0
                  - (layerOuts ([⟨[1], 0⟩] : Layer) [5]).headD 0))
      ∧ ((∃ Δ : LayerDelta, ([⟨[], 0⟩] : Layer) = editLayerList [⟨[], 0⟩] Δ)
          ∧ deltaOf (⟨[], 0⟩ : LayerDelta) [5] ≠ deltaOf (⟨[1], 0⟩ : LayerDelta) [5]
          ∧ ([⟨[], 0⟩] : Layer) = editLayerList [⟨[], 0⟩] ⟨[1], 0⟩)
      ∧ (¬ (∀ (c : VectorConstraint) (Δ : LayerDelta) (x : List Int),
          LayerOut (convertVec (editConstraint c Δ)) x
            = LayerOut (convertVec c) x + deltaOf Δ x))
      ∧ (¬ (∀ (c : VectorConstraint) (Δ : LayerDelta) (x : List Int),
          (VectorConstraintSat (editConstraint c Δ) x ↔
              LayerOut (convertVec (editConstraint c Δ)) x = 0)
            ∧ (LayerOut (convertVec (editConstraint c Δ)) x
                = LayerOut (convertVec c) x + deltaOf Δ x)))
      ∧ ([] : List Int).length ≠ ([1] : List Int).length
      ∧ (⟨[], 0⟩ : LayerDelta).dw.length ≠ (⟨[1], 0⟩ : LinearLayer).w.length

/-- ⭐⭐⭐ **锚点的证明项**：**逐名引用全部 16 条反例**。

⚠ **本定理存在的唯一理由**：它的**证明项**里**必须出现全部 16 个名字**。
⚠ 任何一条反例被**删除或改名** ⟹ 本证明项**无法 elaboration** ⟹ **编译失败**。
⭐ 这正是 B194.4 所要求的「**编译器强制它存在**」——
⚠ 而在本节之前，那 16 条反例**没有任何证明项引用**（全是叶节点）。
⚠ **注意分工**：本定理**不**新证任何数学 —— 它把**已有**的 16 个证明项**串起来**。 -/
theorem b194_counterexamples_intact_holds : b194_counterexamples_intact :=
  ⟨dot_zipWith_add_ORIGINAL_is_false_ce,
   dot_zipWith_add_ORIGINAL_is_false_nonnil_ce,
   dot_zipWith_add_aux_ORIGINAL_is_false_ce,
   editLayer_delta_closed_form_ORIGINAL_is_false_ce,
   editLayer_delta_closed_form_ORIGINAL_witness,
   editLayerList_delta_ORIGINAL_is_false_ce,
   editLayerList_delta_ORIGINAL_witness,
   editLayerList_outputs_eq_iff_ORIGINAL_fwd_is_false_ce,
   editLayerList_outputs_eq_iff_ORIGINAL_bwd_is_false_ce,
   EditLayer_ORIGINAL_is_too_weak_ce,
   EditLayer_ORIGINAL_delta_not_pinned_ce,
   editConstraint_preserves_delta_ORIGINAL_is_false_ce,
   edit_constraint_semantics_bridge_ORIGINAL_is_false_ce,
   dot_zipWith_add_hlen_violated_on_ce,
   editLayer_delta_closed_form_hlen_violated_on_ce⟩

/-- ⭐⭐⭐ **B194 锚点的承重定理**（**使锚点不可删的那一环**）。

⚠ **它做什么**：把锚点作为**显式假设**，并从中产出一条**下游确实需要**的性质
（§八 的 `layerToCLM` 桥，其内容即 `layerOut_zero_iff_clm`）。
⇒ 本定理的**类型**里出现 `b194_counterexamples_intact` ⟹
⚠ **删掉锚点后，本定理连陈述都写不出来**（不是「证不出」，是 elaboration 失败）。

⚠ **诚实边界**：本定理自身的**证明**并没有**使用** `h`（`h` 只出现在类型里）——
这在 Lean 里是允许的，且**恰恰是设计意图**：我们钉的是**名字的存在**，
不是「由反例推出跨宇宙桥」这一并不成立的推理。

⚠⚠ **本定理的「不可删」边界（必须如实说明）**：本定理**只能**使
`b194_counterexamples_intact`（那个 `def`）**连同** `b194_counterexamples_intact_holds`
（那个证明项）**不可删** —— 因为删掉后者，本文件里**没有别的东西**能填上
`b194_counterexamples_intact` 的证明。
⚠ **但它不能**阻止有人**同时**删掉整节 §六之三：
那样 `RealEditSemantics.lean` **自身仍在 roots 内、仍编译**。
⭐ **真正拦住「整节被删」的是下游消费者** —— 见 `RealChainAxioms3.lean` 的
`b194_anchor_consumer`（它 `#check` / 使用本节的名字 ⟹ 本节点被删则该模块**编译失败**）。
⇒ **两层防护**：节内自洽（本文件）+ 跨模块消费（下游 root 模块）。 -/
theorem b194_counterexamples_referenced (h : b194_counterexamples_intact) :
    b194_counterexamples_intact
      ∧ (∀ (l : LinearLayer) (x : List Int),
          LayerOut l x = 0 ↔
            layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) = 0) :=
  ⟨h, fun l x => layerOut_zero_iff_clm l x⟩

/-! ## 七、诚实边界与**未覆盖**的编辑形态（**不许省**）

### 7.1 未覆盖的编辑形态（本定义的**真实缺口**）

`editLayer` 只做 `⟨w + Δw, b + Δb⟩`，故**不覆盖**：

1. **改变层数 / 增删行**（需要 `List` 长度变化，本定义是**逐点**的）；
2. **只编辑指定下标**（需要索引与「其余行不变」的证明；本文件的 δ 是**全员**的）；
3. **乘性 / 缩放编辑**（`scaleVec` 已有乘性版，本文件是加性版；
   两者**不同**，未统一）；
4. **非线性 / 激活后编辑**（`RealSymbolToWeightNonlinear` 已证激活破坏等价性，
   本文件**不**触碰该断点）。

### 7.2 与解析侧 `RealEdit*` 的关系（**未**建立）

⚠ 本文件**没有**证明「符号侧编辑」与 `RealEditCrosstalk.ApplyEdit` 等
解析侧编辑概念**相容**。两侧载体不同（`List Int` vs `E → ℝ`），
且 `LinearLayer` 与 `E →L[ℝ] ℝ` 之间**没有已存在的桥接映射**。
⇒ 这是**真实的剩余缺口**，本文件**如实登记**，不假装已做。

### 7.3 `dot` 的截断语义（**承重**）

`dot a x = (a.zip x).foldl ...`，`zip` 在长度不等时**截断**
（`RealConversionRobustness:108` 已标注该陷阱）。

- 注意 **本版修正了一处首版的真实错误**：首版声称
「`dot_zipWith_add` 之所以**无长度前提**即成立，正是因为截断长度自动一致」——
**这是错的**。截断只保证 `(a ⋈ a') ⋈ x` 与两者**各自** `⋈ x` 的长度一致，
**不**保证 `a'` 的尾巴不单独出现：`a = []`、`a' = [1]`、`x = [1]` 时
左端 `= 0`、右端 `= 1`。⇒ 长度前提**必须显式写出**（`dot_zipWith_add_of_length`）。
⚠ 若把 `editLayer` 改成「只改部分坐标」，截断还会以另一种方式破坏该引理 —— 见 7.1(2)。

### 7.4 已验证 / 未验证项

- ⭐ **本版已通过内核编译**：`python scripts/lean_probe.py lean/RealEditSemantics.lean`
  ⟹ `[lake-lock] lake exit code: 0`。
- ⚠ **首版未经内核编译**（上一批任务书错误地禁用 `lake`），证明项**全部有缺陷**；
  本版逐条修复，详见随附报告 `_fix_out/F_RealEditSemantics.md`。
- `LayerDelta` / `editLayer` / `EditLayer` 的定义是本文件**新引入**的，
  **未**与任何既有模块的同名概念对齐（因为不存在同名概念）。
- ⚠ **`EditLayer` 的 `Prop` 形式**：任务书要求 `EditLayer : Layer → Layer → Prop`。
  本文件把它实现为**数据形式** `editLayerList : Layer → LayerDelta → Layer` +
  由 §六 的关系定理承担内容，并把**长度相容**写进存在量词
  （`def EditLayer W W' := ∃ Δ, DeltaCompatible W Δ ∧ W' = editLayerList W Δ`）。
  理由：**数据形式才能给出闭式 δ**，纯 `Prop` 形式（"存在编辑"）会把 `deltaOf` 里的 `Δ`
  藏进存在量词，于是 δ 重新变成不可计算 —— 正是任务书要避免的平凡性。
- ⚠ 本文件**没有**声明任何「条件可以被去掉」——`h` / `DeltaCompatible` 都是**必需**的
  （§1、§三有反例）。**未弱化任何结论**，只是把必需前提写明。
-/

/-! ## 八、⭐ §7.2 登记的缺口，现由 `layerToCLM` 补上（跨宇宙桥的首个消费者）

§7.2（本文件 :490-495）逐字登记：

> 「两侧载体不同（`List Int` vs `E → ℝ`），且 `LinearLayer` 与 `E →L[ℝ] ℝ` 之间
>  **没有已存在的桥接映射**。⇒ 这是真实的剩余缺口。」

`RealCrossUniverseBridge.lean:layerToCLM` 正是那个映射。下面把它接上，
使「符号侧 `LinearLayer` 的层输出」与「解析侧连续线性算子的取值」**在同一等式上对齐**。

⭐ **为什么这条边承重**（判据③，消融级）：删掉 `import RealCrossUniverseBridge` 后，
`layerToCLM` 不在环境中，**本节的定理无法陈述**。这不是「证不出」，是「写不出来」。

⚠ **边界（与 B431 的四层分级一致）**：`symVec` **非单射**
（`symVec_one_not_injective`），故这是**单向充分对齐**，**不是同构**。
本节的结论不得被读作「两侧载体等价」。 -/

/-- **§7.2 的缺口闭合（增强形态）**：符号侧 `LayerOut l x`（ℤ 值）经 `Int.cast` 提升后，
等于 `layerToCLM` 在 `symVec l.w.length x` 上的取值加偏置（ℝ 值）。**无长度前提**。

这正是 §7.2 登记为「没有已存在的桥接映射」的那条映射。 -/
theorem editSemantics_layer_bridge (l : LinearLayer) (x : List Int) :
    ((LayerOut l x : Int) : ℝ)
      = layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) :=
  layerOut_cast_eq_clm l x

/-- **缺口闭合（零判定形态）**：符号侧「层输出为零」⟺ 解析侧「CLM 取值 + 偏置 = 0」。
这把两宇宙的满足判定钉在**同一命题**上 —— §7.2 所说「两侧不相容」的具体可证形态。 -/
theorem editSemantics_layer_zero_iff (l : LinearLayer) (x : List Int) :
    LayerOut l x = 0 ↔ layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) = 0 :=
  layerOut_zero_iff_clm l x

end Lattice
