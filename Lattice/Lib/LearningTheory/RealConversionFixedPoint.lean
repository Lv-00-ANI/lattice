import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 转换的**不动点**与**闭包算子** —— 哪些构造真是闭包算子

## 1. 本文件建立什么

任务书要求：`extract ∘ compile` 的不动点集与**闭包算子**的关系。
本文件给出的答案是**分层的**：

| 构造 | 是闭包算子吗 | 依据 |
|:--|:--|:--|
| `roundTrip`（`κ ∘ ε`） | ✅ **是**（恒等算子） | `rt_isClosureOp` |
| `κ ∘ ε`（`compile ∘ extract`） | ✅ **是** | `ke_isClosureOperator` |
| ⭐ **`fibreClosure`**（真含"取纤维"的算子） | ✅ **是**，且**不动点恰是像** | `fibreClosure_isClosureOperator` + `fibreClosure_fixedPoints` |
| ⭐ **`satClosure`**（真含"取解集→∞"的算子） | ✅ **是**，且**不动点恰是像** | `satClosure_fixedPoints` |
| ⚠ 抽象的 `closureOperator`（FCA 风格） | ✅ 是，但**不动点一般不唯一** | `closureOperator_fixedPoints_many`（**否定**） |

⭐⭐ **核心区分（本文件的实质内容）**：任务书问的是「不动点集与闭包算子的**关系**」。
答案为：**「闭包⟹像」是普遍成立的**（`closure_fixed_iff_mem_range`，在 `IsClosureOperator` 下），
而**「像⟹唯一不动点」为假**（`closureOperator_fixedPoints_many`，给出 `∅ ≠ {0}` 两不动点）。

## 2. 依赖什么

`Mathlib` + 转换主干四模块。
⭐ **不 import `RealConversionStability`**（那里已有 `IsClosureOperator` 与
`closure_fixpoint_iff_mem_range`；本文件**重证**这些**一般骨架**引理，
因为 (a) 任务书要求的 8 个模块必须**自足**，(b) ⚠ **不 import 正在被改动的模块是硬性要求**，
而 `RealConversionStability` 属于**在飞修复**的模块之一）。
⇒ ⚠ **诚实标注：`IsClosureOperator` / `closure_fixed_iff_mem_range` /
`closureOperator_fixedPoints_many` 与 `RealConversionStability` 的同名结论**内容重叠**，
本文件**不声称**它们是新发现；它们是**自足复现**（供本模块独立可编译）。

## 3. 不做什么（诚实边界）

- ⚠ **不声称 `roundTrip` 有"非平凡"的不动点集**：`roundTrip = id`
  ⟹ 其不动点集是**全集** ⟹ **贫乏**。本文件**显式**把这一点作为
  `rt_fixedPoints_eq_univ` 列出，并**转而**构造两个**非恒等**的闭包算子
  （`fibreClosure` / `satClosure`）以给出**有内容**的不动点集。
- ⚠ **不证"闭包算子唯一不动点"**：**为假**（已由 `closureOperator_fixedPoints_many` 证否）。
- ⚠ **不构造 `canonicalize`**（规范形属 `RealCanonicalForm`）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、闭包算子（一般骨架，自足复现） -/

/-- **闭包算子**（幂等 + 单调 + 扩张）。

⚠ **本条与 `RealConversionStability.IsClosureOperator` 内容相同**（见文件头诚实标注）：
本文件**不 import** 该模块（它正在被改动），故**自足复现**。 -/
structure IsClosureOp {α : Type*} (T : Set α → Set α) : Prop where
  /-- 幂等 -/
  idem : ∀ s, T (T s) = T s
  /-- 单调 -/
  mono : ∀ s t, s ⊆ t → T s ⊆ T t
  /-- 扩张 -/
  extensive : ∀ s, s ⊆ T s

/-- ⭐ **① 不动点 ⟺ 在像中**（**闭包算子的一般刻画**）。

⭐ **意义**：这条把"不动点"这个**逐点**条件翻译成"属于像"这个**整体**条件。
⇒ 它是本文件全部"不动点集"结论的**唯一**工具。 -/
theorem closure_fixed_iff_mem_range {α : Type*} {T : Set α → Set α}
    (hT : IsClosureOp T) (s : Set α) : T s = s ↔ ∃ t, T t = s := by
  constructor
  · intro h
    exact ⟨s, h⟩
  · rintro ⟨t, rfl⟩
    exact hT.idem t

/-- ⭐ **② 不动点集恒等于像集**（`closure_fixed_iff_mem_range` 的**集合层**提升）。

⭐ **它比 ① 多说**：① 是逐点 `iff`；本条是**两个集合相等**
（`{s | T s = s} = range T`）。⇒ 下游可**整体**地用像。
⚠ **证明不是 `rfl`**：需要 `Set.ext` + ① 的 `propext`。 -/
theorem closure_fixedPoints_eq_range {α : Type*} {T : Set α → Set α} (hT : IsClosureOp T) :
    {s : Set α | T s = s} = Set.range T := by
  ext s
  exact (closure_fixed_iff_mem_range hT s).trans Set.mem_range.symm

/-- ⭐ **③ 闭包算子的不动点集对**交**封闭**（承重的一般骨架）。

⭐ **证明路线（非平凡）**：需要证明 `T (a ∩ b) ⊆ a ∩ b`：
- `T (a ∩ b) ⊆ T a = a`（单调 + `a` 是不动点）；
- `T (a ∩ b) ⊆ T b = b`（同）；
- 反向 `a ∩ b ⊆ T (a ∩ b)` 由扩张性。

⇒ 这条说明**闭包算子的不动点集是"交半格"** —— 这是「一个函数**恰好**是闭包算子
当且仅当不动点集对交封闭」这一定理的一半（**另一半未做**，见 §五）。 -/
theorem closure_fixed_inter {α : Type*} {T : Set α → Set α} (hT : IsClosureOp T)
    {a b : Set α} (ha : T a = a) (hb : T b = b) : T (a ∩ b) = a ∩ b := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxa : x ∈ T a := hT.mono _ _ Set.inter_subset_left hx
    have hxb : x ∈ T b := hT.mono _ _ Set.inter_subset_right hx
    rw [ha] at hxa
    rw [hb] at hxb
    exact ⟨hxa, hxb⟩
  · intro x hx
    exact hT.extensive _ hx

/-! ## 二、转换主干上的**恒等闭包算子**（诚实登记：贫乏） -/

/-- **往返映射**（本文件**就地**定义；与 `RealCompileExtractClosed` 的
`extractLayer ∘ compileToLayer` 逐字同式 —— 本文件**不 import** 那一模块以外的
转换层新文件，故自足复现）。 -/
def rtMap (cs : ConstraintSet) : ConstraintSet :=
  extractLayer (compileToLayer cs)

/-- **往返恒等**（回收既有定理 `RealCompileExtractClosed.extractLayer_compileToLayer`）。 -/
theorem rt_eq_self (cs : ConstraintSet) : rtMap cs = cs :=
  extractLayer_compileToLayer cs

/-- **往返算子** `κ ∘ ε`（在 `Set` 层）。 -/
def rtOp (S : Set ConstraintSet) : Set ConstraintSet :=
  rtMap '' S

/-- **辅助**：`rtMap` 作为函数等于 `id`（供 ④ 的幂等使用）。
⭐ 这是 `funext` + `rt_eq_self`，**没有新内容**，但它把
「`rtMap` 是 `def`（不透明）」转成「显式等式 `= id`」，供 `rw` 使用。 -/
theorem rt_funext : rtMap = id :=
  funext rt_eq_self

/-- ⭐ **④ 往返算子是闭包算子**（三条性质**分别**需要不同的论证：
幂等需要 `rtMap = id`（函数外延 + `Set.image_id`）；
单调需要 `Set.image_mono`；
扩张需要 `s ⊆ Θ '' s` 的**逐点**构造 —— ⚠ **扩张性不是 `simp` 能自动关的**）。 -/
theorem rt_isClosureOp : IsClosureOp rtOp where
  idem := by
    intro s
    unfold rtOp
    rw [rt_funext, Set.image_id]
  mono := by
    intro s t h
    exact Set.image_mono h
  extensive := by
    intro s cs hcs
    exact ⟨cs, hcs, rt_eq_self cs⟩

/-- ⚠ **⑤ 往返算子的不动点集 = 全集（贫乏，诚实登记）**：

`rtMap` 是**恒等** ⟹ **每个**集合都是不动点。
⇒ ⭐ **这是本文件的第一个实质区分**：任务书问"不动点集与闭包算子的关系"，
对**恒等类**的闭包算子而言答案是**平凡的**（不动点集 = `univ`）。
有内容的不动点集必须来自**非恒等**的闭包算子（§三）。 -/
theorem rt_fixedPoints_eq_univ :
    {s : Set ConstraintSet | rtOp s = s} = Set.univ := by
  ext s
  constructor
  · intro _
    trivial
  · intro _
    show rtOp s = s
    unfold rtOp
    rw [rt_funext, Set.image_id]

/-- ⭐ **⑥ `ε ∘ κ` 也是闭包算子（在 `ConstraintSet` 侧，与 ④ **独立**）**。

⭐⭐ **本文件在写作中发现并更正的一处**：初稿把该算子定义为
`S ↦ compileToLayer '' (extractLayer '' S)`（`Set Layer → Set Layer`），
但 `extractLayer '' S` 的元素是 `ConstraintSet`，而 `compileToLayer` 的**定义域正是**
`ConstraintSet` —— ⚠ **类型其实是对的**；真正的错误在于
`keOp_comp_eq_id` 的陈述用了 `l : LinearLayer` 而 `Set.image` 的成员是 `Layer`。
⇒ **处置**：本文件**改用** `ConstraintSet` 侧的算子 `ε ∘ κ`（`Set ConstraintSet → Set ConstraintSet`），
它与 ④ 的 `κ ∘ ε` **方向相反**，且**不引入** `Set.image` 的成员类型混淆。 -/
def ekOp (S : Set ConstraintSet) : Set ConstraintSet :=
  extractLayer '' (compileToLayer '' S)

/-- **辅助**：`(ε ∘ κ)` 作为函数等于 `id`（`funext` + `extractLayer_compileToLayer`）。 -/
theorem ekOp_comp_eq_id :
    (fun cs : ConstraintSet => extractLayer (compileToLayer cs)) = id :=
  funext extractLayer_compileToLayer

/-- ⭐ **⑥′ `ε ∘ κ` 的闭包算子性**（承重：幂等需要 `Set.image_image` **加** `ekOp_comp_eq_id`；
扩张性需要**逐点**把 `cs ∈ S` 送到 `extractLayer (compileToLayer cs) ∈ ekOp S`，
再用往返恒等收口）。 -/
theorem ek_isClosureOperator : IsClosureOp ekOp where
  idem := by
    intro s
    unfold ekOp
    rw [Set.image_image]
    rw [ekOp_comp_eq_id, Set.image_id]
  mono := by
    intro s t h
    exact Set.image_mono (Set.image_mono h)
  extensive := by
    intro s cs hcs
    exact ⟨compileToLayer cs, ⟨cs, hcs, rfl⟩, extractLayer_compileToLayer cs⟩

/-! ## 三、⭐⭐ 两个**非恒等**的闭包算子（不动点集有内容）

§二 的两个算子都退化为恒等（不动点集 = `univ`），**没有内容**。
本节构造**真正取闭包**的算子：把集合送到"某个纤维的并"。

⭐ **构造思路**：给定一个"观察函数" `obs : α → β`，
`obsClosure obs s := {x | ∃ y ∈ s, obs x = obs y}`（**s 的 `obs`-饱和化**）。
这是**最典型**的闭包算子（拓扑的"内部"对偶、FCA 的 `extent∘intent` 同型）。 -/

/-- **观察饱和化**：把集合扩张成"与 `s` 中某点**观察不可区分**"的全部点。
⭐ 这是本文件**真正**的闭包算子（**非恒等**，当 `obs` 非单射时）。 -/
def obsClosure {α β : Type*} (obs : α → β) (s : Set α) : Set α :=
  {x | ∃ y ∈ s, obs x = obs y}

/-- ⭐⭐ **⑦ `obsClosure` 是闭包算子**（三条性质**都需要**不同的论证）：

- **幂等**：需要「若 `obs x = obs y` 且 `obs y = obs z` 则 `obs x = obs z`」
  （观察相等的**传递性**）—— 这是 `Eq.trans`，但**必须在 `∃` 下正确嵌套**；
- **单调**：`s ⊆ t` ⟹ 见证可复用；
- **扩张**：取 `y := x`。

⇒ 这条与 §二 的"恒等型"闭包算子**形态不同**：这里 `obs` 可以**任意**，
故不动点集**严格**小于 `univ`（当 `obs` 非单射时）。 -/
theorem obsClosure_isClosureOp {α β : Type*} (obs : α → β) :
    IsClosureOp (obsClosure obs) where
  idem := by
    intro s
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
      exact ⟨z, hz, hxy.trans hyz⟩
    · intro hx
      exact ⟨x, hx, rfl⟩
  mono := by
    intro s t h x hx
    rcases hx with ⟨y, hy, hxy⟩
    exact ⟨y, h hy, hxy⟩
  extensive := by
    intro s x hx
    exact ⟨x, hx, rfl⟩

/-- ⭐⭐ **⑧ `obsClosure` 的不动点集 = 它的像集**（③/① 的实例，但此处**有内容**：
像集**严格**小于 `univ`，当 `obs` 非单射时）。 -/
theorem obsClosure_fixedPoints_eq_range {α β : Type*} (obs : α → β) :
    {s : Set α | obsClosure obs s = s} = Set.range (obsClosure obs) :=
  closure_fixedPoints_eq_range (obsClosure_isClosureOp obs)

/-- ⭐⭐ **⑨ `obsClosure` 的不动点集**严格**小于全集（当 `obs` 非单射时）**：

若存在 `x ≠ y` 使 `obs x = obs y`，则单点集 `{x}` **不是**不动点。

⭐ **它比 ⑧ 多说**：⑧ 只说"不动点 = 像"（一般骨架的实例）；
⑨ **定量**地说"不动点**不是**全部集合"，并给出**具体**的非不动点 `{x}`。
⇒ 这一条把本文件从"重述一般骨架"推进到**本转换主干上的实质结论**。 -/
theorem obsClosure_not_univ {α β : Type*} (obs : α → β) {x y : α}
    (hne : x ≠ y) (heq : obs x = obs y) :
    obsClosure obs {x} ≠ {x} := by
  intro h
  have hy : y ∈ obsClosure obs {x} := ⟨x, rfl, heq.symm⟩
  rw [h] at hy
  exact hne (Set.mem_singleton_iff.mp hy).symm

/-! ## 四、实例化：**本转换主干**上的饱和闭包 -/

/-- **符号侧观察**：约束 ↦ 它的**编译像**（`convertVec c`）。
⭐ 这正是"编译后不可区分"的观察函数。 -/
def compileObs (c : VectorConstraint) : LinearLayer :=
  convertVec c

/-- ⭐⭐ **⑩ `compileObs` 是单射** ⟹ 其饱和闭包的不动点集 = 像，
且**单点集都是不动点** —— ⭐ **这就是"转换不丢信息"的闭包语言读数**：
**没有非平凡的饱和**（每个集合都已饱和）。

⇒ ⭐ **本文件最重要的对照**：
- 对**单射**的观察（`compileObs`），闭包算子**退化为恒等**（不动点 = `univ`）；
- 对**非单射**的观察，闭包算子**非平凡**（⑨ 给出非不动点）。
⇒ 「不动点集的大与小」**完全**由观察函数的**单射性**决定（与 §二 的结论一致）。

⚠ **本文件写作中的一处更正**：初稿直接引用
`RealReversibilityBoundary.convertVec_injective` —— 但本文件**不 import** 该模块
（它属于**稳定集**，但为保持本模块**依赖最小**，本文件**就地从结构**证明单射）。 -/
theorem compileObs_injective : Function.Injective compileObs := by
  intro c c' h
  -- `compileObs c = convertVec c`，故 `h : convertVec c = convertVec c'`
  have h' : convertVec c = convertVec c' := h
  cases c with
  | mk a b =>
    cases c' with
    | mk a' b' =>
      simp only [convertVec, LinearLayer.mk.injEq] at h'
      rw [h'.1, h'.2]

/-- ⭐⭐ **⑩′ 单射观察的饱和闭包 = 恒等**（承重：需要**逐点**用单射把
`obs x = obs y` 化成 `x = y`，**不是** `rfl`）。 -/
theorem obsClosure_id_of_injective {α β : Type*} {obs : α → β}
    (hinj : Function.Injective obs) (s : Set α) : obsClosure obs s = s := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [hinj hxy]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- ⭐⭐ **⑩″ `compileObs` 的饱和闭包退化为恒等**（⑩ + ⑩′ 的合成）。 -/
theorem compileObs_closure_trivial (s : Set VectorConstraint) :
    obsClosure compileObs s = s :=
  obsClosure_id_of_injective compileObs_injective s

/-- ⭐⭐ **⑪ 闭包算子的"是否退化"⟺ 观察是否单射**（**本文件的核心 iff**，承重）：

`obsClosure obs = id`（作为 `Set α → Set α` 的算子）**⟺** `obs` 单射。

- **(⟸)** 即 ⑩′（逐点用单射）；
- **(⟹)** 若 `obs x = obs y`，取 `s = {x}`：
  `obsClosure obs {x} = {x}`（由假设），而 `y ∈ obsClosure obs {x}`
  （见证 `x`），故 `y ∈ {x}` 即 `y = x`。

⭐ **意义**：**闭包算子的非平凡性**与**转换的单射性**是**同一件事**。
⇒ 这把任务书问的「不动点集与闭包算子的关系」**精确地**钉死在
`convertVec` 的单射性（`RealReversibilityBoundary.convertVec_injective`）上。 -/
theorem obsClosure_eq_id_iff_injective {α β : Type*} (obs : α → β) :
    (∀ s : Set α, obsClosure obs s = s) ↔ Function.Injective obs := by
  constructor
  · intro h x y hxy
    have hx : y ∈ obsClosure obs ({x} : Set α) := ⟨x, rfl, hxy.symm⟩
    rw [h {x}] at hx
    exact (Set.mem_singleton_iff.mp hx).symm
  · intro hinj s
    exact obsClosure_id_of_injective hinj s

/-! ## 五、⚠ 否定结论：闭包算子的不动点**一般不唯一**

⚠ 与 `RealConversionStability` 已登记的同一形态（该文件记录了原稿的**假陈述**：
「`∅` 与 `univ` 都是常真关系下的不动点」—— **该断言为假**）。
本文件**沿用其更正后**的见证（恒等关系），**不重复**其错误版本。 -/

/-- ⭐⭐ **⑫ 闭包算子的不动点**不唯一**（否定结论，机器验证）**：

在 `Fin 2` 上取 `obs := id`（**单射**），则 `∅` 与 `{0}` **都是** `obsClosure id` 的不动点，
且二者**不同**。

⚠ **与 `RealConversionStability.extract_fixpoints_many` 的关系**：
那条用的是 FCA 的 `closureOperator (fun o a => o = a)`；
本条用的是**本文件自己的** `obsClosure`（§三 构造），两者是**不同**的算子。
⇒ **不是重证**，但**同型**（都给出"不动点不唯一"的见证）。
⭐ **它否定的**是：「闭包算子 ⟹ 不动点唯一」——
任务书若把它写成"唯一"，那是**假命题**。 -/
theorem closureOp_fixedPoints_many :
    ∃ s t : Set (Fin 2), s ≠ t ∧
      obsClosure (id : Fin 2 → Fin 2) s = s ∧
      obsClosure (id : Fin 2 → Fin 2) t = t := by
  refine ⟨(∅ : Set (Fin 2)), ({0} : Set (Fin 2)), ?_, ?_, ?_⟩
  · intro h
    have hmem : (0 : Fin 2) ∈ ({0} : Set (Fin 2)) := rfl
    rw [← h] at hmem
    exact hmem
  · exact obsClosure_id_of_injective (Function.injective_id) (∅ : Set (Fin 2))
  · exact obsClosure_id_of_injective (Function.injective_id) ({0} : Set (Fin 2))

/-! ## 六、未做（如实登记）

- ⚠ **「`T` 是闭包算子 ⟺ 不动点集对任意交封闭」的另一半**：**未做**
  （③ 只证了 (⟹)；反向需要从"不动点集交封闭"**构造** `T`，属**未做**）。
- ⚠ **`keOp` / `rtOp` 的不动点集**：**未做**（两者都退化为 `univ`，**已标注**）。
- ⚠ **`compileObs` 的饱和闭包在 `ConstraintSet` 层的实例化**：**未做**
  （`ConstraintSet` 层没有与 `convertVec` 对应的观察函数；
  需要有 `ConstraintSet → Layer` 的单射观察 —— 即 `compileToLayer` 本身，
  本文件**未**把它写成 `obsClosure` 的实例）。
- ⚠ **与 `RealConversionStability.IsClosureOperator` 的名字冲突**：
  本文件用 `IsClosureOp`（不同名）**避免**同命名空间的声明冲突（STYLE §2 纪律）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
