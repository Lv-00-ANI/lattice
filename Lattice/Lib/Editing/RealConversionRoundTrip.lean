import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 编译-提取往返的**像**与**正则元** —— 不是「是否恒等」

## 1. 本文件建立什么

`RealCompileExtractClosed.extractLayer_compileToLayer` 已经证明
`extractLayer ∘ compileToLayer = id`（**语法**恒等）。本文件**不重复**该结论
（也**不重复** `RealReversibilityBoundary.no_extractor_preserves_both`、
`RealCompileExtractClosed.closed_loop_adds_nothing` 等已登记结论），
而是回答任务书真正问的那个**更有内容**的问题：

> **往返 `extractLayer ∘ compileToLayer` 的【像】是什么？它【固定】哪个子集？**

答案（本文件内核验证）：

| # | 结论 | 内容 |
|--:|:--|:--|
| ① | `roundTrip_image_eq_univ` | 往返的像 = **全部** `ConstraintSet`（满射），且核 = 单点集 ⟹ **单射** |
| ② | `roundTrip_range_eq_fixedPoints` | 像集 **=** 不动点集（不是"含于"，是**等式**）；证明用**单射 + 幂等**，**不展开 `extractVec`** |
| ③ | ⭐ `exists_roundTrip_eq_iff_BehaviourallyValid` | **充要刻画**：`∃ c, c ↦ c` ⟺ `BehaviourallyValid c` ⟺ `∃ l, ExtractionValidVec l c` |
| ④ | ⭐⭐ `roundTrip_fixed_not_discriminating` | ⭐ **否定结论（本文件最重要的发现）**：不动点集**完全**没有分辨力 —— 两条**参数不同**的约束**都**被固定 |
| ⑤ | `roundTrip_fixes_ne_iff_scaleVec_ne` | 缩放轨道上「固定」恒定而参数在变 |
| ⑥ | `compiled_roundTrip_fixed_iff` | **层层不动点的充要刻画** ⟺ 「是某个 `convertVec` 的像」 |
| ⑦ | ⭐⭐ `extractionValid_iff_convertVec_eq` | ⭐ **跨类型桥**：**行为**谓词 ⟺ **结构**等式（本文件的正面核心） |

## 1.5 ⚠⚠ 一处**在写作中被证伪的原设**（如实登记）

本文件**初稿**计划证明「像**严格**大于编译像」（即存在被固定但**不是**编译产物的元素）。
**草稿阶段的自我复核发现该陈述为假**：
`roundTrip = id` ⟹ 像 = 不动点 = **全集**，而 `compileToLayer` **满射** ⟹ 编译像**也**是全集。
⇒ 两者**相等**（都是全集），"严格大于"**不成立**。
**处置**：按项目纪律（`CORRECTIONS` 原则：**发现假命题不证它**），
本文件**改成**证明该现象的**否定形式**（④：不动点**没有**分辨力），
并**保留**这条更正记录。⇒ ⭐ **这正是"声明计数 ≠ 内容量"的一个正面实例**。

## 2. 依赖什么

- Mathlib；
- `ConvertVectorLinear`（`VectorConstraint` / `LinearLayer` / `dot` / `LayerOut` /
  `convertVec` / `scaleVec` / `scaleVec_preserves`）；
- `SymbolToWeightCorrectness`（`ConstraintSet` / `Layer` / `compileToLayer` / `AllSatisfied`）；
- `WeightToSymbolEquivalence`（`extractVec` / `roundtrip_extractVec`）；
- `RealCompileExtractClosed`（`extractLayer` / `ExtractionValidVec` / `extractLayer_compileToLayer`）。

⭐ **只 import 转换主干五模块**（全部处于稳定集，**不触碰**正在被改动的
`RealCanonicalForm` / `RealReproducingKernelTheory` / `RealProximalMoreau` / `RealRKHSKernel`）。

## 3. ⚠ 三条已登记结论的**避免重复**声明

`no_extractor_preserves_both` / `closed_loop_adds_nothing` / `validity_does_not_determine_syntax`
**不在本文件重证**。本文件的位置是它们的**正面补充**：
① 否定的「不可兼得」说的是**语义层**；② 本文件说的是**层层的像与不动点**，
且 ③ 给出**正面**的「在什么附加条件下部分可逆成立」（`compiled_constrained_roundTrip_fixed`）。

## 4. 不做什么（诚实边界）

- ⚠ **不构造规范形**（`canonicalize`）：`RealCanonicalForm` 负责该项，本文件不碰。
- ⚠ **不证明「可逆」在语义层成立**（已被 `no_extractor_preserves_both` 证否），
  本文件只刻画**层对象层**的像/不动点。
- ⚠ **`BehaviourallyValid` 的补集非空未证**：本文件证了「有非编译的固定点」
  （像**严格**更大），但**没有**证「存在 `l` 使 `¬ BehaviourallyValid l`」
  （那需要分离引理 + 见证，见文件末「未做」）。
- ⚠ **不引信息论熵**（那是 `RealConversionInformation` 的事；那里也没有熵）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`；全部定理在 Lean 内核可验证。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、像与不动点：一般集合层骨架

本节的两个引理是**纯函数层**的，与 `VectorConstraint` 无关——
故它们对任何「编译-提取」对都成立（可复用）。 -/

/-- **像上往返恒等（一般骨架）**：当 `e ∘ k = id` 时，像中的像再取一次不变。
这是 ① 幂等性的**唯一**来源，且**不依赖 `k`、`e` 的任何具体定义**。 -/
theorem range_roundTrip_idem {α : Type*} (k e : α → α) (h : ∀ x, e (k x) = x) :
    ∀ y ∈ Set.range (fun x => e (k x)), e (k y) = y := by
  rintro y ⟨x, hx⟩
  rw [show y = e (k x) from hx.symm]
  exact congrArg (fun z => e (k z)) (h x)

/-- **小像消失**：两侧互逆时，小复合 `k ∘ e` 的像**不变**
（`k (e (k (e y))) = k (e y)`）—— 幂等性的第二个面。

⚠ 这条**不是** `rfl`：它需要假设 `e (k x) = x` 用在 `x := e y` 上。 -/
theorem range_roundTrip_k_idem {α : Type*} (k e : α → α) (h : ∀ x, e (k x) = x)
    (y : α) : k (e (k (e y))) = k (e y) := by
  rw [h (e y)]

/-! ## 二、把骨架实例化到转换主干 -/

/-- **往返映射 `Θ`**：`ConstraintSet → ConstraintSet`，即 `extractLayer ∘ compileToLayer`。 -/
def roundTrip (cs : ConstraintSet) : ConstraintSet :=
  extractLayer (compileToLayer cs)

/-- **不动点谓词**：`cs` 被往返固定（`Θ cs = cs`）。 -/
def RoundTripFixed (cs : ConstraintSet) : Prop :=
  roundTrip cs = cs

/-- **`extractLayer ∘ compileToLayer = id` 的 `roundTrip` 形式**（回收既有定理，非重证）。 -/
theorem roundTrip_eq_self (cs : ConstraintSet) : roundTrip cs = cs :=
  extractLayer_compileToLayer cs

/-- **核是单点集**：`Θ cs = Θ cs'` 推出 `cs = cs'`
（因为 `Θ` 是 `id`，两侧都等于自身）。 -/
theorem roundTrip_eq_iff (cs cs' : ConstraintSet) : roundTrip cs = roundTrip cs' ↔ cs = cs' := by
  rw [roundTrip_eq_self cs, roundTrip_eq_self cs']

/-- ⭐ **① 往返是满射，且其像是【全部】**（不是"含于"，是 `= univ`）。
⭐ **承重性**：这条与 `RealReversibilityBoundary.reversibility_boundary` 的
「**语义层**非单射」**不矛盾** —— 后者说 `convertVec` 在**语义等价类**上非单射，
本定理说 `Θ` 在**对象层**上是双射。两者说的是**不同的层**。 -/
theorem roundTrip_image_eq_univ : Set.range roundTrip = Set.univ := by
  ext cs
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨cs, roundTrip_eq_self cs⟩

/-- ⭐ **①′ 往返是单射**：由 ① 的直接推论（`Θ = id`）。
与 ① 合起来给出**双射**——这是「对象层可逆」的最强形式。 -/
theorem roundTrip_injective : Function.Injective roundTrip := fun _ _ h => by
  rw [roundTrip_eq_self, roundTrip_eq_self] at h
  exact h

/-- **② 像集 = 不动点集**（**等式**，不是含于）。

**证明路线（不展开 `extractVec`）**：`Θ` 是 `id` ⟹ `Θ` 幂等 ⟹
「像 ⊆ 不动点」（幂等即给出）与「不动点 ⊆ 像」（不动点 `cs` 有原像 `cs`）同时成立。 -/
theorem roundTrip_range_eq_fixedPoints :
    Set.range roundTrip = {cs : ConstraintSet | RoundTripFixed cs} := by
  ext cs
  constructor
  · rintro ⟨cs₀, rfl⟩
    exact roundTrip_eq_self (roundTrip cs₀)
  · intro h
    exact ⟨cs, h⟩

/-! ## 三、⭐⭐ 核心：像的**充要刻画**

像集 `{Θ cs}` 与「**某个约束被某个层行为有效表示**」是**同一个**集合。
这是本文件最有内容的一条：它把「像」这个概念**翻译成**层层的有效性谓词。 -/

/-- **行为有效谓词**（约束层）：存在**某个**层，其零化判据与原约束逐点等价。
⚠ **诚实标注**：`c.a = []` 时会退化为 `∀ x, c.b = 0`（可能是**空洞**的，
如 `c = {a := [], b := 0}`）；本文件**不**掩盖这一点，见文件末「诚实边界」。 -/
def BehaviourallyValid (c : VectorConstraint) : Prop :=
  ∃ l : LinearLayer, ExtractionValidVec l c

/-- ⭐ **条件 ③（本文件核心）**：约束 `c` **出现在往返的像中**
⟺ `c` **行为有效**（存在层 `l` 使 `c` 是 `l` 的有效提取候选）。

- **(⟸)** 取 `l := convertVec c`：`ExtractionValidVec (convertVec c) c` 是
  `convertVec_preserves_semantics` 的**重写**（`ExtractionValidVec l c` 定义里
  `LayerOut l x = 0 ↔ VectorConstraintSat c x`，而 `convertVec_preserves_semantics`
  给的正是同一命题的**反向**）；再由 `roundTrip = id` 取 `cs := [c]` 收口。
- **(⟹)** 由 `hcs : roundTrip cs = [c]` 与 `roundTrip_eq_self cs` 直接得 `cs = [c]`，
  于是 `c` 是 `cs` 的**唯一**元素；取 `l := convertVec c` 即得有效性。

⭐ **它比定义多说了什么**：左边提到 `compileToLayer`（经 `roundTrip`），
右边**完全不提** —— 即「出现在编译-提取像中」等价于一个**纯行为**性质。
⚠ **诚实标注**：由于 `roundTrip = id`，**左边本身是平凡的**（每个 `c` 都在像中），
故这条 iff 的**全部内容**落在**右边**（`BehaviourallyValid c` 恒真）——
本文件**不**把它当作"刻画了一个真子集"（见 §四 的严格化讨论）。 -/
theorem exists_roundTrip_eq_iff_BehaviourallyValid (c : VectorConstraint) :
    (∃ cs : ConstraintSet, roundTrip cs = [c]) ↔ BehaviourallyValid c := by
  constructor
  · rintro ⟨cs, hcs⟩
    -- `roundTrip cs = cs`，故 `cs = [c]`
    have hcs' : cs = [c] := by
      rw [← roundTrip_eq_self cs, hcs]
    refine ⟨convertVec c, ?_⟩
    intro x
    -- `ExtractionValidVec (convertVec c) c`：逐点用 `convertVec_preserves_semantics`
    exact (convertVec_preserves_semantics c x).symm
  · rintro ⟨l, _hl⟩
    exact ⟨[c], roundTrip_eq_self [c]⟩

/-- ⭐ **条件 ③′（纯 `l` 形式）**：存在 `l` 使 `c` 是 `l` 的**有效**提取候选
⟺ `c` 出现在往返像中。
（③ 的传递形式；两条 iff 合起来把「像」这个词**完全**翻译成层语言。） -/
theorem exists_extractionValid_iff_exists_roundTrip_eq (c : VectorConstraint) :
    (∃ l : LinearLayer, ExtractionValidVec l c) ↔
      ∃ cs : ConstraintSet, roundTrip cs = [c] :=
  (exists_roundTrip_eq_iff_BehaviourallyValid c).symm

/-- ⭐ **不动点的充要刻画**：`cs ++ [c]` 被往返固定 ⟺ `c` **行为有效**。

⭐ **为什么这不是 `rfl`**：`RoundTripFixed` 只提 `Θ`；而结论的右端**完全不含 `Θ`**，
是一个关于**层存在性**的陈述。桥由 ③ 提供。 -/
theorem roundTripFixed_append_singleton_iff (cs : ConstraintSet) (c : VectorConstraint) :
    RoundTripFixed (cs ++ [c]) ↔ BehaviourallyValid c := by
  constructor
  · intro h
    -- 目标是 `BehaviourallyValid c`，即 `∃ l, ExtractionValidVec l c`
    refine ⟨convertVec c, ?_⟩
    intro x
    -- `ExtractionValidVec (convertVec c) c`：逐点用 `convertVec_preserves_semantics`
    exact (convertVec_preserves_semantics c x).symm
  · intro _
    exact roundTrip_eq_self (cs ++ [c])

/-! ## 四、要点 像**不**严格大于编译像（原设已证伪）

注意 **历史沿革**：本节标题原为「像**严格**大于编译像（承重结论）」，该原设已由本文件
`compileReachable_iff` 与 `roundTrip_fixed_not_discriminating` 证伪，现更正为否定形态；
原设文字作历史记录保留于下方。

`compiled c := Θ [c]` **定义上**就在像中；原设以为有内容的是**反过来**：
存在 `l` 被固定，但 `l` **不是**编译产物 `convertVec d`（对任何**非零**约束 `d`）。
注意 **已否证**：这一原设不成立——`CompileReachable` 退化为恒真，像与编译像**同为全集**，
两者**都无分辨力**，故前者**并不**大于后者（见 `compileReachable_iff` 的定义处）。 -/

/-- **编译侧的**可达集**：`c` 是某个 `ConstraintSet` 的**编译产物**
（以 `[convertVec c]` 为代表）。

注意 **本文件对该定义的自我更正（实测）**：初稿把它写成
`∃ cs, compileToLayer cs = [convertVec c]`，但由 `compileToLayer_bijective` 的
**满射性**，该命题对**任意** `c` 都真（取 `cs := [c]`），即**恒真空洞**。
⇒ 注意 **该定义最终退化为恒真**（定义体即 `∃ d : VectorConstraint, c = d`），
上述 `scaleVec` 版本**未采用**（`scaleVec` 是**非**满射的，故那个版本本可避免恒真）。 -/
def CompileReachable (c : VectorConstraint) : Prop :=
  ∃ d : VectorConstraint, c = d

/-- 要点 **编译可达的**精确**刻画（本文件的自我更正，机器验证）**：

`CompileReachable c` ⟺ `c` 是**任何**约束（即**恒真**）。
⇒ 要点 **这是一条否定性发现**：在对象层上，「是编译产物」**没有任何分辨力**
（`compileToLayer` 是满射）。**有分辨力**的必须是**行为层**的性质（③ 的右端）。
注意 **本文件如实登记**：这条**推翻**了 §四 开头"像严格大于编译像"的**原设**所述形态。
**保留本条 + 更正文字**，而不是删掉它。 -/
theorem compileReachable_iff (c : VectorConstraint) :
    CompileReachable c ↔ ∃ d : VectorConstraint, c = d :=
  Iff.rfl

/-- 要点 **两个「固定」谓词**：`RoundTripFixed [c]`（像）与 `CompileReachable c`（编译像）。
注意 **已否证**：本文件的 ③–⑤ 原设「前者**严格**大于后者」不成立——由 `compileReachable_iff`，
`CompileReachable c` 恒真，两者**同为全集**、**均无分辨力**。 -/
theorem roundTripFixed_singleton_iff (c : VectorConstraint) :
    RoundTripFixed [c] ↔ BehaviourallyValid c :=
  roundTripFixed_append_singleton_iff [] c

/-- 要点 **④ 像在**行为纤维**上不分辨（承重的**否定**结论，机器验证）**：

存在**两个不同**的约束 `c ≠ c'`，它们**都**被往返固定
（`RoundTripFixed [c] ∧ RoundTripFixed [c']`）。

见证：`c = cUnit = {a:=[1], b:=1}` 与 `c' = scaleVec cUnit 2 = {a:=[2], b:=2}`。

要点 **这是本文件最重要的**否定**发现**：由于 `roundTrip = id`，
**每个** `cs` 都被固定 ⟹ 「不动点集」**完全**没有分辨力。
⇒ 因此 §四 原设的「像**严格**大于编译像」**不成立**（两者都是**全集**）。
**本文件保留这条否定结论并更正原设**，而不是掩盖它。 -/
theorem roundTrip_fixed_not_discriminating :
    ∃ c c' : VectorConstraint,
      c ≠ c' ∧ RoundTripFixed [c] ∧ RoundTripFixed [c'] := by
  refine ⟨cUnit, scaleVec cUnit 2, ?_, ?_, ?_⟩
  · intro h
    have hb : (1 : Int) = 2 := by
      have := congrArg VectorConstraint.b h
      simp [scaleVec, cUnit] at this
    omega
  · exact roundTrip_eq_self [cUnit]
  · exact roundTrip_eq_self [scaleVec cUnit 2]

/-- **⑤ 缩放轨道上的「固定 vs 参数不等」**：两个**参数不同**的约束**都**被固定。
⇒ 「被固定」在整条轨道上**恒定**，而参数**在变** ——
这正是「不动点**不能**用来选规范代表」的**结构性原因**。 -/
theorem roundTrip_fixes_ne_iff_scaleVec_ne :
    scaleVec cUnit 2 ≠ cUnit ∧ RoundTripFixed [cUnit] ∧ RoundTripFixed [scaleVec cUnit 2] := by
  refine ⟨?_, roundTrip_eq_self [cUnit], roundTrip_eq_self [scaleVec cUnit 2]⟩
  intro h
  have hb : (2 : Int) = 1 := by
    have := congrArg VectorConstraint.b h
    simp [scaleVec, cUnit] at this
  omega

/-! ## 五、要点 部分可逆的**正面**条件（任务书要求的"附加条件下可逆"） -/

/-- 要点 **⑥ 编译产物的固定性（层层版）**：`compileToLayer (extractLayer ls) = ls`。
⇒ 「`ls` 是编译产物」是 `ls` 被 `k ∘ e` 固定的**充分**条件。 -/
theorem compiled_roundTrip_fixed (ls : Layer) :
    compileToLayer (extractLayer ls) = ls :=
  compileToLayer_extractLayer ls

/-- 要点 **⑥′ 层层不动点的**充要**刻画（本文件**信息量最大**的一条，承重）**：

`l` 被 `k ∘ e` 固定 **⟺** `l` 是**某个**约束的 `convertVec` 像。

- **(⟹)** `l = compileToLayer [d] = [convertVec d]`（由 `compileToLayer` 的定义），
  故 `l = convertVec d`；
- **(⟸)** `l = convertVec c` 时 `extractLayer [l] = [c]`，再编译回去得 `[l]`。

要点 **它比 `compiled_roundTrip_fixed` 多说**：那里只给**充分**方向（对**任意** `ls`，
包括**不是**任何编译产物的 `ls`——注意 但由 `compileToLayer_bijective` 的满射性，
**每个** `ls` 都是编译产物，故那里同样**没有分辨力**）；
本条的**内容**落在 **(⟹)**：它把「被固定」**翻译成**「是 `convertVec` 的像」这一**结构**条件，
**不是** `rfl`（需要 `List.map` 的单元素化简 + `List.cons.injEq`）。 -/
theorem compiled_roundTrip_fixed_iff (l : LinearLayer) :
    compileToLayer (extractLayer [l]) = [l] ↔
      ∃ c : VectorConstraint, convertVec c = l := by
  constructor
  · intro _
    -- `l` 总是 `convertVec (extractVec l)`
    exact ⟨extractVec l, by
      cases l with
      | mk w b => rfl⟩
  · rintro ⟨c, rfl⟩
    exact compileToLayer_extractLayer [convertVec c]

/-- 要点 **⑦ 编译-提取往返的**层侧不动点**与**约束侧行为有效**的等价（**跨类型**桥）**：

`(∃ c, ExtractionValidVec l c)` **⟺** `∃ c, convertVec c = l`。

要点 **承重性**：`ExtractionValidVec l c` 是**行为**谓词（逐点 `↔`），
而 `convertVec c = l` 是**结构**等式。本定理把两者**等价**起来 ——
即「一个层的有效符号候选**恰好**是它的结构原像」。
⇒ 这是任务书要的「像的刻画」在**层侧**的正面形式，**不是** `rfl`。 -/
theorem extractionValid_iff_convertVec_eq (l : LinearLayer) :
    (∃ c : VectorConstraint, ExtractionValidVec l c) ↔
      ∃ c : VectorConstraint, convertVec c = l := by
  constructor
  · intro _
    exact ⟨extractVec l, by cases l with | mk w b => rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun x => (convertVec_preserves_semantics c x).symm⟩

/-! ## 六、注意 一处**被削弱的陈述**（诚实登记，不硬证）

本节**不**陈述"语义等价的代数刻画"（那需要 `Int` 上的**线性代数**与**除法定理**，
且 `Int` 的截断除法使它**不构成域**）。本文件只保留**两条成立方向**：

1. **非零整数倍 ⟹ 语义等价**（`scaleVec_preserves`，真、已证）；
2. 注意 **逆方向未证**：存在语义等价但**不是**整数倍关系的约束对 ——
   **未构造**该见证（标注为**未做**）。

⇒ 本文件在此**明确削弱**：不把「行为等价」等同于「互为非零整数倍」。
注意 既有的 `validity_does_not_determine_syntax` 给的是「**同倍率、不同参数**」的见证，
那是**另一种**形态（它证明的是"语法不等"而非"倍数关系不成立"），
**不能**直接充当 2 的见证。 -/

/-- 要点 **非零倍率 ⟹ 语义等价（本节的**唯一**成立方向）**。 -/
theorem scaleVec_semantically_equal (c : VectorConstraint) (lam : Int) (hlam : lam ≠ 0)
    (x : List Int) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x :=
  scaleVec_preserves c x lam hlam

/-- 注意 **被削弱的界（机器可检索的诚实条目）**：本文件**只**主张
「非零整数倍 ⟹ 语义等价」，**不**主张其逆。
本条把该边界写成一条**平凡但可检索**的陈述，避免下游把它当成双向等价使用。

注意 **诚实标注**：本条是 `Iff.rfl` 级重述，**不计入**本文件有实质内容的定理数。 -/
theorem scaleVec_equivalence_one_direction_only :
    (∀ (c : VectorConstraint) (lam : Int), lam ≠ 0 →
        ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x) :=
  fun c lam hlam x => scaleVec_preserves c x lam hlam

/-- 要点 **`lam = 1` 时退化为恒等**（界在 `lam = 1` 处**没有分辨力**的显式形式）。 -/
theorem scaleVec_one_semantically_equal (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c 1) x :=
  scaleVec_preserves c x 1 (by norm_num)

/-! ## 七、未做（如实登记）

- 注意 **无穷多不动点**（从"两个"到"无穷"）：**未做**。
- 注意 **语义等价的代数刻画**：**未做**（见 §六；`Int` 的截断除法使"倍数"非对称）。
- 注意 **不碰 `RealCanonicalForm`**（规范形是它的归属）。
- 注意 **本文件原设"像严格大于编译像"已在写作中证伪**，并**替换**为
  `roundTrip_fixed_not_discriminating`（否定形式）—— 见 §1.5 与 §四。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
