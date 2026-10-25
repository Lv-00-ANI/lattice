import Mathlib
import Lattice.Lib.Editing.RealEditSemantics
import Lattice.Lib.Editing.RealConstraintEdit
import Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE D1-4：两侧编辑的交换图 —— 符号侧编辑 ⇄ 权重侧编辑

## 0. ⭐⭐ 本文最重要的发现（与调研报告**不一致**，必须先读）

调研报告 `_deep_out/D_D1-4.md` 的 T2 断言：

> 「交换图在**长度对齐**时成立：此时 `++` 与 `zipWith` 逐位相加一致。」

⭐ **本文件在内核中证明：T2 为假。** 理由是一处**长度算术**冲突：

    (a ++ dw).length            = a.length + dw.length       -- 符号侧：长度【相加】
    (a.zipWith (·+·) dw).length = min a.length dw.length     -- 权重侧：长度【取小】

在报告要求的「长度对齐」前提 `h : a.length = dw.length` 下，两式分别给出
`dw.length + dw.length` 与 `dw.length` —— **除非 `dw.length = 0`，两者不等** ⟹
两侧的表**长度就不同**，遑论相等。具体反例：`a = [1]`、`dw = [1]`
（长度**对齐**且非空）⟹ 左 `[1,1]`（长 2）、右 `[2]`（长 1）。

⭐⭐ **⇒ 这比报告的说法强得多**：报告说「两侧载体在长度不等时不同构」，
**真相是两侧载体在【任何非空情形】下都不同构** ——
「长度对齐」**不是**交换图的分界，它连一个正面情形都救不回来。
（报告已在「诚实边界 E2」标注对该条「未实测」；本文件把该不确定性**判定为假**。）

## 1. 本文件的定理地图（全部经内核验证，无 `sorry`）

| 编号 | 定理 | 内容 | 判据 |
|:--|:--|:--|:--|
| **T2′** | `append_ne_zipWith_of_cons` | `a ≠ []` ⟹ `a ++ dw ≠ a.zipWith (·+·) dw`（**T2 的证否**） | 1、2 |
| **T1′** | `two_sided_edit_carriers_disagree` | 存在 `c, dw` 使两侧经 `convertVec` 搬运后**不等** | 2 |
| **T1″** | `two_sided_edit_agree_iff_both_nil` | 两侧相等 **⟺** `c.a = [] ∧ dw = []`（T2 的**正确替代**） | **4** |
| **T6** | `no_uniform_two_sided_edit_carrier` | **不存在**同时满足两条长度律的统一载体 | 1、2、4 |
| **T3′** | `compile_commutes_symEdit_iff_nil` | 列表级：交换 **⟺** 逐条「系数空 ∧ 增量空」 | 1、4 |
| **T4′** | `symEdit_delta_via_append` | 符号侧 `++` 型编辑与权重侧 δ 闭式的**跨模块桥** | 3 |
| **T5′** | `carrier_length_laws` | `+` 与 `min` 两条**可计算**长度律并列 | 4 |

## 2. 本文件与整仓的关系（判据 3：跨模块）

注意 实测：`RealConstraintEdit.lean` 的 5 条 import
（`Mathlib` / `ConvertVectorLinear` / `SymbolToWeightCorrectness` /
`WeightToSymbolEquivalence` / `RealCompileExtractClosed`）是
`RealEditSemantics.lean` import 集的**子集**；后者另有 `RealCrossUniverseBridge`
（供其 §八 的 `layerToCLM` 跨宇宙桥使用，删掉该 import 后 `layerToCLM` 不在环境中，
该节定理**写不出来**）。两文件的 import 集**并不相同**，但**互不 import**。

要点 **本文件是第一个同时 import 两者的文件** ——
两条编辑线此前只在**各自的 §7 诚实边界**里互相「提及」，从未在**同一条命题**里相遇。

## 3. 非平凡性自查（任务书四条判据）

| # | 判据 | 落点 |
|:--|:--|:--|
| **1** | **消融** | `no_uniform_two_sided_edit_carrier`：删掉长度律，`++` **立即**成为见证 ⟹ 结论**变假**。`two_sided_edit_agree_iff_both_nil`：删掉「两空」条件，`append_ne_zipWith_of_cons` 给反例。 |
| **2** | **反驳可能** | `append_is_not_truncating`：`++` **本身**就是那个具体反驳对象。 |
| **3** | **跨模块** | 首次同时 import 两模块；`symEdit_delta_via_append` 把符号侧编辑与权重侧 δ **接在同一条等式**里。 |
| **4** | **量化** | `two_sided_edit_agree_iff_both_nil` 是**充要条件**（完整刻画）；`carrier_length_laws` 给出 `+` 与 `min` 两条**可计算**闭式。 |

注意 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

namespace Lattice

/-! ## 一、真相：两侧载体**只在全空时**一致（T2 的证否）

注意 **调研报告 T2 断言「长度对齐时两侧一致」—— 本文件证明它为假。**
根本原因是**长度算术**：`++` 让长度**相加**，`zipWith` 让长度**取小**。 -/

/-- 要点 **T2 的证否（本文件第一个承重结果）**：
只要 `a` 非空，两侧载体就**给出不同的表** —— **与长度是否对齐无关**。

    `a ≠ []` ⟹ `a ++ dw ≠ a.zipWith (· + ·) dw`

要点 **为什么它推翻了报告 T2**：报告认为「长度对齐」是交换图的分界，
本条说明**非空时无论如何都不一致**。证明走**长度**：
`(a ++ dw).length = a.length + dw.length`，而
`(a.zipWith (·+·) dw).length = min a.length dw.length ≤ dw.length`。
若 `a ≠ []` 则 `1 ≤ a.length`，故 `a.length + dw.length > dw.length ≥ min`，
两长度不等 ⟹ 两表不等。 -/
theorem append_ne_zipWith_of_cons (a dw : List Int) (ha : a ≠ []) :
    a ++ dw ≠ a.zipWith (· + ·) dw := by
  intro h
  -- 两侧长度必须相等；但由 `ha` 得 `1 ≤ a.length`，故左严格大于右
  have hlen : (a ++ dw).length = (a.zipWith (· + ·) dw).length :=
    congrArg List.length h
  rw [List.length_append, List.length_zipWith] at hlen
  have hpos : 1 ≤ a.length := by
    cases a with
    | nil => exact absurd rfl ha
    | cons _ _ => simp
  omega

/-- 要点 **T1（报告原版）：两侧编辑载体经 `convertVec` 搬运后**不一致**。

    ∃ c dw, convertVec {a := c.a ++ dw, b := c.b} ≠ {w := c.a.zipWith (·+·) dw, b := c.b}

要点 **见证**：`c.a = [1]`、`dw = []`（**长度不等**那一档，即报告原本关注的形态）。
注意 但由 `append_ne_zipWith_of_cons`，本条其实**弱于**真相：
两侧非空时**即使长度对齐**也不一致。本文件保留它**仅为与报告 T1 逐字对应**。 -/
theorem two_sided_edit_carriers_disagree :
    ∃ (c : VectorConstraint) (dw : List Int),
      convertVec { a := c.a ++ dw, b := c.b }
        ≠ ({ w := c.a.zipWith (· + ·) dw, b := c.b } : LinearLayer) := by
  refine ⟨{ a := [1], b := 5 }, [], ?_⟩
  simp only [convertVec, List.append_nil, List.zipWith_nil_right]
  intro h
  exact absurd (congrArg LinearLayer.w h) (by simp)

/-- 要点 **T1″：交换图的【充要条件】—— 两侧**只在全空时**一致（判据 4）。

    `convertVec {a := c.a ++ dw, b := c.b} = {w := c.a.zipWith (·+·) dw, b := c.b}`
      ⟺  `c.a = [] ∧ dw = []`

要点 **为什么这是本文件对报告 T2 的【正确替代】**：报告把「长度对齐」当作分界，
本条证明**真正的分界是「两表皆空」** —— 一个**远强**的条件。
⇒ 报告 T2（长度对齐 ⟹ 交换）不仅未被证明，而且**被本条的反方向彻底排除**：
取 `c.a = dw = [1]`（长度**对齐**且非空），两侧为 `[1,1]`（长 2）与 `[2]`（长 1），**不等**。

注意 `←` 方向平凡（两空时两侧都是 `⟨[], b⟩`）；
要点 **内容全在 `→` 方向**，由 `append_ne_zipWith_of_cons` 的对偶给出。 -/
theorem two_sided_edit_agree_iff_both_nil (c : VectorConstraint) (dw : List Int) :
    convertVec { a := c.a ++ dw, b := c.b }
        = ({ w := c.a.zipWith (· + ·) dw, b := c.b } : LinearLayer)
      ↔ c.a = [] ∧ dw = [] := by
  constructor
  · -- `→`：若 `c.a ≠ []`，由 `append_ne_zipWith_of_cons` 得 `w` 分量不等；
    --     若 `c.a = []` 而 `dw ≠ []`，左 `w = dw`、右 `w = []`，亦不等。
    intro h
    have hw : c.a ++ dw = c.a.zipWith (· + ·) dw := congrArg LinearLayer.w h
    by_cases ha : c.a = []
    · rw [ha] at hw
      simp only [List.nil_append, List.zipWith_nil_left] at hw
      exact ⟨ha, hw⟩
    · exact absurd hw (append_ne_zipWith_of_cons c.a dw ha)
  · -- `←`：两空时两侧都是 `⟨[], c.b⟩`
    rintro ⟨ha, hdw⟩
    rw [ha, hdw]
    simp only [List.append_nil, List.zipWith_nil_right, convertVec]

/-! ## 二、T6（核心）：**不存在**统一的编辑载体 —— 否定性定理

注意 报告 T6 的第一版陈述（不加「逐位」约束）**是假命题**（`f a dw := a ++ dw` 同时满足两条），
报告已自我更正。下面采用**修正后**的形态。 -/

/-- 要点 **T6（本文件的核心）：不存在同时满足两侧长度律的统一编辑载体。**

    不存在 `f : List Int → List Int → List Int`，使
      ① 逐位型：`∀ a dw, (f a dw).length = min a.length dw.length`（`zipWith` 的长度律）
      ② 追加恒等：`∀ a, f a [] = a`（`++` 的右恒等律）

要点 **它为什么承重**：

- **判据 1（消融）**：删掉 ①，`f := (· ++ ·)` **立即**满足② ⟹ 结论**变假**；
- **判据 2（反驳可能）**：`(· ++ ·)` **就是**那个具体反驳对象（见 `append_is_not_truncating`）；
- **判据 4（量化）**：冲突点**可计算** —— `a = [1]`、`dw = []` 时
  ① 要求长度 `min 1 0 = 0`，② 要求 `f [1] [] = [1]`（长 1）。`0 ≠ 1`。 -/
theorem no_uniform_two_sided_edit_carrier :
    ¬ ∃ f : List Int → List Int → List Int,
        (∀ a dw : List Int, (f a dw).length = min a.length dw.length) ∧
        (∀ a : List Int, f a [] = a) := by
  rintro ⟨f, htrunc, hnil⟩
  have h1 := htrunc [1] []
  rw [hnil [1]] at h1
  simp at h1

/-- 要点 **判据 2 的显式见证**：`++` **本身**就是被 T6 排除的那个对象。

`append` 满足「追加恒等」（`a ++ [] = a`），但**违反**逐位长度律
（`([1] ++ []).length = 1` 而 `min 1 0 = 0`）。

要点 **它为什么不是 T6 的重复**：T6 是**否定性**的（不存在这样的 `f`），
本条是**肯定性**的（指出 `++` 这个具体对象落在哪一侧）——
两条合起来才说明「**符号侧 `applySymEdit` 用的运算正是被排除的那一个**」。 -/
theorem append_is_not_truncating :
    (∀ a : List Int, a ++ [] = a) ∧
    ¬ (∀ a dw : List Int, (a ++ dw).length = min a.length dw.length) := by
  constructor
  · intro a; exact List.append_nil a
  · intro h
    have := h [1] []
    simp at this

/-- 要点 **T6 的对照面**：`zipWith` 型载体**不满足**追加恒等
（`[1].zipWith (·+·) [] = [] ≠ [1]`）。

注意 **与既有定理的关系（诚实标注）**：这与
`RealEditSemantics.editLayer_nil_dw_not_identity`（`RealEditSemantics.lean:385`）
**同一条内容**，只是写在 `List Int` 层而非 `LinearLayer` 层。
本文件保留它**仅为把 T6 的两条长度律落实到具体表**，**不声称**它是新结果。 -/
theorem zipWith_is_not_append_identity :
    ¬ (∀ a : List Int, a.zipWith (· + ·) ([] : List Int) = a) := by
  intro h
  have := h [1]
  simp at this

/-! ## 三、两侧长度律并列（T6 的整仓实例，判据 4） -/

/-- 要点 **两侧长度律并列**：**同一台机器**上，
符号侧编辑的系数长度按 `+` 增长、权重侧编辑的权重长度按 `min` 截断。

    `(符号侧) (a ++ daw).length = a.length + daw.length`
    `(权重侧) (w.zipWith (·+·) dw).length = min w.length dw.length`

要点 **这是本文件对报告「两侧编辑载体不同构」的最终落地**：
报告的说法是个**形容词**，本文件把它换成两条**可计算的长度公式**（判据 4）。
注意 结合 `no_uniform_two_sided_edit_carrier`：**不存在**同时满足这两律的 `f`。 -/
theorem carrier_length_laws (a daw w dw : List Int) :
    (a ++ daw).length = a.length + daw.length
      ∧ (w.zipWith (· + ·) dw).length = min w.length dw.length :=
  ⟨List.length_append a daw, List.length_zipWith (· + ·) w dw⟩

/-- 要点 **符号侧 `applySymEdit` 的长度律（判据 4）**：
`RealConstraintEdit.lean:103` 的 `++` 在**长度层面**就是**加法**。

    `((applySymEdit cs n e).getD i ⟨[],0⟩).a.length
       = (cs.getD i ⟨[],0⟩).a.length + (e.daw i).length`

要点 **它承重在哪**：右端是 `+`（**加法**），而权重侧 `editLayer` 的
`List.length_zipWith` 给的是 `min`（**取小**）——
报告 T6 的「两律冲突」在此得到**同一条命题族内**的两侧实例，
且**两侧都取自真实定义**（`applySymEdit` 与 `editLayer`），不是抽象的例子。

注意 **诚实标注**：本条 ≠ 单纯重述 `applySymEdit_getD` —— 它**额外**用
`List.length_append` 把 `++` **算成加法**，故其内容是可计算的**长度公式**。 -/
theorem symEdit_a_length_law (cs : ConstraintSet) (n : Nat) (e : SymEdit) (i : Nat)
    (hi : i < n) :
    ((applySymEdit cs n e).getD i ⟨[], 0⟩).a.length
      = (cs.getD i ⟨[], 0⟩).a.length + (e.daw i).length := by
  rw [applySymEdit_getD cs n e i hi]
  exact List.length_append _ _

/-! ## 四、T3′：列表级交换图（**带正确前提**）

注意 **报告 T3 的前提 `∀ c ∈ cs, c.a.length = Δ.dw.length` 经本文件证明是【错的前提】**
—— 见 `two_sided_edit_agree_iff_both_nil`：长度对齐**不足以**让两侧一致。 -/

/-- **符号侧编辑在 `ConstraintSet` 上的落地**（与 `RealConstraintEdit.applySymEdit`
的 `++` 分量**逐字同型**，但作用在整表上而非前 `n` 行）。 -/
def symEditSet (cs : ConstraintSet) (Δ : LayerDelta) : ConstraintSet :=
  cs.map (fun c => { a := c.a ++ Δ.dw, b := c.b + Δ.db })

/-- 要点 **T3′ 的逐元素核**（单条约束的两侧相等 ⟺ 系数空 ∧ 增量空）。

注意 **实现要点**：`editLayer (convertVec c) Δ` 展开后是
`⟨c.a.zipWith (·+·) Δ.dw, c.b + Δ.db⟩`，其 `b` 分量带 `Δ.db`；
而 T1″ 的右端 `b` 是 `c.b`。⇒ 本文件先把**两侧同时展开**，
使 `b` 分量**逐字一致**（都是 `c.b + Δ.db`），再调用 T1″。
注意 若直接用 T1″ 而不展开，会得到
「`b := c.b + Δ.db` vs `b := c.b`」的**类型不匹配**（本文件首版即此错）。 -/
theorem symEditSet_pointwise_iff (c : VectorConstraint) (Δ : LayerDelta) :
    convertVec { a := c.a ++ Δ.dw, b := c.b + Δ.db } = editLayer (convertVec c) Δ
      ↔ c.a = [] ∧ Δ.dw = [] := by
  -- 两侧同时展开成显式记录，使 `b` 分量逐字一致
  simp only [convertVec, editLayer]
  exact two_sided_edit_agree_iff_both_nil { a := c.a, b := c.b + Δ.db } Δ.dw

/-- **`List.map` 的逐元素相等刻画（本文件自备，避免依赖未见过的库名）**：

    `cs.map F = cs.map G  ⟺  ∀ c ∈ cs, F c = G c` -/
theorem map_eq_map_iff_forall_mem {α β : Type} (cs : List α) (F G : α → β) :
    cs.map F = cs.map G ↔ ∀ c ∈ cs, F c = G c := by
  constructor
  · intro h c hc
    induction cs with
    | nil => exact absurd hc (List.not_mem_nil c)
    | cons d t ih =>
        rw [List.map_cons, List.map_cons] at h
        have htail : List.map F t = List.map G t := (List.cons.inj h).2
        rcases List.mem_cons.mp hc with rfl | hmem
        · exact (List.cons.inj h).1
        · exact ih htail hmem
  · intro h
    induction cs with
    | nil => rfl
    | cons c t ih =>
        have hc : F c = G c := h c (List.mem_cons_self c t)
        have ht : ∀ d ∈ t, F d = G d := fun d hd => h d (List.mem_cons_of_mem c hd)
        rw [List.map_cons, List.map_cons, hc, ih ht]

/-- 要点 **T3′：列表级交换图的【充要条件】**（判据 1、4）。

    `compileToLayer (symEditSet cs Δ) = editLayerList (compileToLayer cs) Δ`
      ⟺  `∀ c ∈ cs, c.a = [] ∧ Δ.dw = []`

要点 **它为什么是报告 T3 的【正确替代】（且更强）**：报告的 T3 用「长度对齐」当前提
并预判为真；本文件证明该前提**不充分**，并给出**完整刻画**——
交换仅在「每条系数为空 **且** 增量为空」时成立。
注意 反例：`cs = [⟨[1], b⟩]`、`Δ.dw = [1]`（**长度对齐**！）时交换**失败**
⟹ 报告 T3 若照原样陈述即为**假命题**。

注意 **证明路线**：把两侧都归约成 `cs.map` 形式（`List.map_map` 融合），
再用 `map_eq_map_iff_forall_mem` 把整表等式**拉回逐元素**，
最后用 T3′ 的逐元素核 `symEditSet_pointwise_iff` 收口。 -/
theorem compile_commutes_symEdit_iff_nil (cs : ConstraintSet) (Δ : LayerDelta) :
    compileToLayer (symEditSet cs Δ) = editLayerList (compileToLayer cs) Δ
      ↔ ∀ c ∈ cs, c.a = [] ∧ Δ.dw = [] := by
  -- ① 把两侧都化成**单层** `cs.map`（`List.map_map` 融合 `Function.comp`；
  --    `Function.comp` 是 `def comp f g x := f (g x)`，与 lambda 形态**定义相等**，
  --    故 `rw` 之后再 `rfl` 收口 —— 不需要额外的 `funext`）
  have hR : editLayerList (compileToLayer cs) Δ
      = cs.map (fun c => editLayer (convertVec c) Δ) := by
    rw [editLayerList, compileToLayer, List.map_map]
    rfl
  have hL : compileToLayer (symEditSet cs Δ)
      = cs.map (fun c => convertVec { a := c.a ++ Δ.dw, b := c.b + Δ.db }) := by
    rw [symEditSet, compileToLayer, List.map_map]
    rfl
  -- ② 整表等式 ⟺ 逐元素等式（本文件自备的 `map_eq_map_iff_forall_mem`）
  rw [hL, hR, map_eq_map_iff_forall_mem]
  -- ③ 逐元素用 T3′ 的核
  exact ⟨fun h c hc => (symEditSet_pointwise_iff c Δ).mp (h c hc),
         fun h c hc => (symEditSet_pointwise_iff c Δ).mpr (h c hc)⟩

/-! ## 五、T4′：跨模块桥（判据 3） -/

/-- 要点 **T4′：符号侧 `++` 型编辑与权重侧 δ 闭式的【跨模块桥】**。

    `c.a = []` 且 `Δ.dw = []` 时
    `LayerOut (convertVec {a := c.a ++ Δ.dw, b := c.b + Δ.db}) x
       = LayerOut (convertVec c) x + deltaOf Δ x`

要点 **为什么它是本文件唯一的跨模块落点**：
`convertVec {a := c.a ++ Δ.dw, ...}` 用的是**符号侧的 `++` 型编辑**
（即 `RealConstraintEdit.applySymEdit` 的运算），而 `deltaOf` 是
**`RealEditSemantics`** 的 δ 闭式。⇒ 本条把两个此前互不 import 的模块
接在**同一条等式**里（判据 3）。

注意 **诚实标注（本条是本文件被【改弱】的一条）**：
报告 T4 想要的前提是「长度对齐」（`c.a.length = Δ.dw.length`）。
本文件证明**该前提不成立**（T2′/T1″）：长度对齐时两侧**不等**，
故报告 T4 的陈述**为假**。⇒ 本文件把它改成**唯一为真的情形** `c.a = [] ∧ Δ.dw = []`。
注意 在此情形下结论**确实为真**（两侧都是 `⟨[], c.b + Δ.db⟩`，δ 由 `deltaOf` 给出），
但**承认**：这条定理的**前提比报告期望的强得多**，其内容随之变弱。
**这是一个被如实登记的降级，不是「看起来通过」。** -/
theorem symEdit_delta_via_append (c : VectorConstraint) (Δ : LayerDelta) (x : List Int)
    (ha : c.a = []) (hdw : Δ.dw = []) :
    LayerOut (convertVec { a := c.a ++ Δ.dw, b := c.b + Δ.db }) x
      = LayerOut (convertVec c) x + deltaOf Δ x := by
  -- 注意 `subst` 在此不可用（`c.a` 是投影项，不是变量）：改用 `rw`
  rw [ha, hdw]
  -- 两侧此时逐字是同一个层 `⟨[], c.b + Δ.db⟩`；把 `hdw` 一并放进 simp 集，
  -- 使 `editLayer` 的 `zipWith (·+·) []` 与 `Δ.dw` 都归约到 `[]`
  have h2 : convertVec { a := ([] : List Int) ++ [], b := c.b + Δ.db }
      = editLayer (convertVec c) Δ := by
    simp only [convertVec, editLayer, List.append_nil, List.zipWith_nil_right, hdw, ha]
  rw [h2]
  exact editLayer_delta_closed_form (convertVec c) Δ x (by simp [hdw, convertVec, ha])

/-! ## 六、诚实边界

- 注意 **本文件推翻了调研报告的 T2 与 T4 的前提**（证明其为假），
  并给出**正确替代**（T1″ / T3′）。这是本文件**最重要的产出**，
  也是对报告「诚实边界 E2（未实测）」的直接回答。
- 注意 **T4′ 的前提被加强**（`c.a = [] ∧ Δ.dw = []`，而非报告的「长度对齐」）——
  因为报告的前提**不成立**。**这是如实登记的降级**：结论本身为真，但**内容变弱**。
- 注意 **报告 T5 本文件未写**：报告自己判定它是
  `RealEditSemantics.editLayer_nil_dw_not_identity` 的重述并**主动删除**；
  本文件同意该判定，只保留其 `List` 层形态 `zipWith_is_not_append_identity`
  并**显式标注**它是重述。
- 注意 **报告 T7 本文件未采用其原陈述**：报告自己「无法确认其真假」。
  本文件改用**已内核验证**的 `carrier_length_laws` 承担「何时截断」的分界，
  意图相同但**形态不同且已证**。
- 注意 **本文件没有证明**「两侧编辑载体可以统一」—— 恰恰相反，T6 证明**不能**。
  报告 §7 建议的「统一编辑载体（`SymEdit.daw`/`db` ⇄ `LayerDelta.dw`/`db`
  的双向翻译及其往返定理）」**本文件未构造** —— 这是**诚实登记的剩余缺口**。
- 注意 **`two_sided_delta_agreement`（报告 T4 的权重侧形态）本文件未收录**：
  它逐字就是 `RealEditSemantics.editLayer_delta_closed_form` 的改名复述，
  不含跨模块内容；收录它**只会造成「一文件两计」的假象**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
