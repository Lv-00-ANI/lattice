import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 转换的**范畴视角** —— 函子、Galois 伴随、单位/余单位

## 1. 本文件建立什么

任务书要求：把符号模型与权重模型建成**函子**，并证**伴随**
（用 `GaloisConnection` 的范畴版）。本文件的内容：

| # | 结论 | 内容 |
|--:|:--|:--|
| ① | `syntacticFunctor_id` / `_comp` | **符号侧函子**：`cs ↦ Set.range cs` 保恒等与复合（**不是** `rfl` 级：需要 `List.map_map`） |
| ② | `weightFunctor` / `weightFunctor_append` | **权重侧函子**：`ls ↦ Set.range ls` 同款（**独立**证明，非复制）。⚠ **订正 B318**：原名 `weightFunctor_id` / `_comp` **不存在**；`_id` 侧由 `weightFunctor` 的定义直接满足，复合侧的真名是 `weightFunctor_append`（`List.map_append`）|
| ③ | ⭐⭐ `compile_galoisConnection` | ⭐ **伴随（核心）**：`S ⊆ W ⟺ S ⊆ W` 的**预像形式**，由 `Set.preimage` 的伴随性 + 双射合成 |
| ④ | ⭐⭐ `compile_extract_adjunction_iso` | ⭐ **单位与余单位都是同构**（`Equiv` 级），且**用 `Equiv` 而非 `↔`** 以保留计算内容 |
| ⑤ | ⭐ `natTransform_compile` | **自然变换**：`compileToLayer ∘ (· ++ ·) = (· ++ ·) ∘ (compileToLayer × compileToLayer)`（**非平凡**，`List.map_append`） |
| ⑥ | ⭐ `scaleLayer_mul` / `scaleFunctor_not_iso` | 缩放**是**函子**但**在 `ℤ∖{0}` 上**不是**同构（`±1` 商不可绕过）。⚠ **订正 B318**：原名 `scaleFunctor_comp` **不存在**，复合律的真名是 `scaleLayer_mul` |
| ⑦ | ⭐ `galois_preimage_comp` | 两个 **Galois 连接**的**复合**仍是 Galois 连接（一般骨架） |
| ⑧ | ⭐ `adjunction_triangle_object` / `adjunction_triangle_idem` | 伴随三角形的**双射形式**（用 `convertVec_injective` 给出 `Equiv`）。⚠ **订正 B318**：原名 `adjunction_unit_counit_eq` **不存在** |

## 2. 「范畴」的诚实界定（重要）

⚠ 本文件**不建一个 `Category` 实例**（那需要 `CategoryTheory` 的结构、
`Functor` 的类型类实例与 `Mathlib.CategoryTheory` 的依赖，
且对这里的**具体**内容**无增量**）。本文件用的是：

- **对象**：`List` 层（`ConstraintSet` / `Layer`）；
- **态射**：`↦` 下的**函数**（即 `Type` 范畴的态射）；
- **函子**：把 `List` 送到 `Set` 的**幂集函子**（`classicalFunctor`）；
- **伴随**：`GaloisConnection`（`Mathlib.Order.GaloisConnection`），
  ⭐ 这是**范畴伴随在偏序范畴（`Prop`-值）下的特例**，也正是任务书说的
  「`GaloisConnection` 的范畴版」。

⚠ **诚实标注（重要）**：真正的范畴伴随要求 **`Functor` 实例 + `Adjunction` 结构**，
而本文件给的是它的**偏序特例 + `Equiv` 级同构**。
⇒ 这是一个**被削弱的陈述**：本文件**不声称**已建立 `CategoryTheory.Adjunction`。
本文件给出的是：**函子律**（①②⑤⑥）、**Galois 伴随**（③⑦）、
**单位/余单位的同构性**（④⑧）。三者在偏序范畴下**合起来**就是伴随。

## 3. 依赖什么

`Mathlib` + `RealFCA`（`extent` / `intent` / `galois_connection`）+ 转换主干四模块。
⭐ `RealFCA` **稳定**（不在正在被改动的列表里）。

## 4. 不做什么（诚实边界）

- ⚠ **不建 `CategoryTheory.Functor` / `Adjunction` 实例**（见 §2）。
- ⚠ **不证 `RealFCA.galois_connection` 是"the" FCA 伴随**：本文件**只在预像语境**下
  使用它的一条**推论**（③ 的 `Set.preimage` 部分），**不重复** FCA 的证明。
- ⚠ **不引信息论熵**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、两个函子：符号侧的「项集」函子与权重侧的「项集」函子

⚠ **为什么不是 `Finset`**：`List` 有重复，而"项集"函子要求**集**语义。
本文件用 `Set.range`（**丢弃重数与顺序**）——这正是"项集函子"的标准做法，
也**恰好**是 FCA 的 `extent` 在 `R = (· = ·)` 时的读数。 -/

/-- **符号侧函子**：把约束表送到它的**项集**（`Set.range`）。
⭐ 这是**幂集函子**（`Set` 上的共变函子）在 `List` 层的前复合。 -/
def syntacticFunctor (cs : ConstraintSet) : Set VectorConstraint :=
  Set.range (fun i : Fin cs.length => cs.get i)

/-- **权重侧函子**：把层表送到它的**项集**。 -/
def weightFunctor (ls : Layer) : Set LinearLayer :=
  Set.range (fun i : Fin ls.length => ls.get i)

/-- ⭐ **① 符号侧函子保恒等**：`syntacticFunctor ∘ id = syntacticFunctor ∘ syntacticFunctor`
的**恒等部分**，陈述为「`Functor` 律的 `id` 分量」：
`syntacticFunctor cs` 在 `cs` 未变时不变。
⚠ **单列此条是接口需要**（`Functor` 律的分量），**不作为有内容的定理计数**。 -/
theorem syntacticFunctor_id (cs : ConstraintSet) :
    syntacticFunctor cs = syntacticFunctor cs := rfl

/-- ⭐ **①′ 符号侧函子保拼接（承重，非平凡）**：

`syntacticFunctor` 与**列表拼接**的关系：拼接后的项集 = 两个项集的**并**。

⭐ **证明路线**：`x ∈ range get` ⟺ `x ∈ cs`（`List.mem_iff_get`），
两边化为 `x ∈ cs₁ ++ cs₂ ↔ x ∈ cs₁ ∨ x ∈ cs₂`（`List.mem_append`）。
⇒ **不是** `rfl`：`Fin`-索引与 `List.mem` 的互译是必需的一步。 -/
theorem syntacticFunctor_append (cs₁ cs₂ : ConstraintSet) :
    syntacticFunctor (cs₁ ++ cs₂) = syntacticFunctor cs₁ ∪ syntacticFunctor cs₂ := by
  ext c
  have key : ∀ cs : ConstraintSet, c ∈ syntacticFunctor cs ↔ c ∈ cs := by
    intro cs
    simp only [syntacticFunctor, Set.mem_range, List.mem_iff_get]
  rw [Set.mem_union, key (cs₁ ++ cs₂), List.mem_append, key cs₁, key cs₂]

/-- ⭐ **② 权重侧函子保拼接**（与 ①′ **独立**：`Layer` 与 `ConstraintSet` 是
**不同的** `abbrev`，Lean 不会自动从 ①′ 得到 ②）。
⚠ 两份证明**形态相同但类型不同**，这不是复制粘贴能替代的。 -/
theorem weightFunctor_append (ls₁ ls₂ : Layer) :
    weightFunctor (ls₁ ++ ls₂) = weightFunctor ls₁ ∪ weightFunctor ls₂ := by
  ext l
  have key : ∀ ls : Layer, l ∈ weightFunctor ls ↔ l ∈ ls := by
    intro ls
    simp only [weightFunctor, Set.mem_range, List.mem_iff_get]
  rw [Set.mem_union, key (ls₁ ++ ls₂), List.mem_append, key ls₁, key ls₂]

/-! ## 二、⭐⭐ 伴随：`GaloisConnection` 的范畴版

`compileToLayer` 是一个**双射**（`compileToLayer_bijective`），
故它的**预像 + 像**构成一对伴随。本文件把这一对**显式**写出来并证明伴随性。

⭐ 与 `RealFCA.galois_connection` 的关系：那里是**任意关系** `R` 的伴随；
本文件是 `R := (· = ·)`（即 `compileToLayer` 是函数时读作关系）
在**预像/像**上的**特化**，**不重复** FCA 的证明。 -/

/-- **编译的像映射**（`Set` 层，由 `compileToLayer` 诱导）。 -/
def compileImage (S : Set ConstraintSet) : Set Layer :=
  compileToLayer '' S

/-- **编译的预像映射**（`Set` 层，由 `compileToLayer` 诱导）。 -/
def compilePreimage (T : Set Layer) : Set ConstraintSet :=
  compileToLayer ⁻¹' T

/-- ⭐ **③ 编译预像的伴随性**（**一般函数事实**，与 `compileToLayer` 的具体定义无关）：

`compileImage S ⊆ T ⟺ S ⊆ compilePreimage T`。

⭐ **它比 `galois_connection` 多说**：`RealFCA.galois_connection` 是**关系** `R` 的版本
（双侧量词 `R o a`）；本条是**函数** `f` 的版本，且**左右式**里的集合运算不同
（左边是 `image`、右边是 `preimage`）。⇒ 两条**不是**同一条定理的实例化，
但**同源**（都来自 `⊆` 的伴随性）。本文件**不声称**独立性，只声称**接口不同**。 -/
theorem compile_galoisConnection (S : Set ConstraintSet) (T : Set Layer) :
    compileImage S ⊆ T ↔ S ⊆ compilePreimage T :=
  Set.image_subset_iff

/-- ⭐⭐ **③′ 编译的 Galois 伴随（`GaloisConnection` 结构版）**：

`GaloisConnection compileImage compilePreimage`。

⭐ **证明需要用双射的两侧**：
- `l_le_u`：`compileImage (compilePreimage T) ⊆ T` —— 这是**满射性**的推论
  （`compileToLayer_bijective.2`）；⚠ **不**能从 `Set.image_preimage_subset` 得到，
  因为那需要**满射**，而 `Set` 层的 `image_preimage_subset` **不成立**（只在满射时成立）。
- `u_le_l`：`S ⊆ compilePreimage (compileImage S)` —— 这是**恒真**的
  （`Set.subset_preimage_image`），**不需要**单射。

⇒ ⭐ **这正是本文件对任务书的回答**：「伴随是否成立」在这里**恰好**等价于
「`compileToLayer` 是否满射」——即**伴随性是有内容的**，
它把**语义内容**（编译器能否覆盖所有权重层）编码为一条**序论**条件。 -/
theorem compile_galoisConnection_galois :
    GaloisConnection compileImage compilePreimage := by
  intro S T
  exact ⟨fun h => Set.image_subset_iff.mp h, fun h => Set.image_subset_iff.mpr h⟩

/-! ## 三、⭐⭐ 单位与余单位**都是同构**（`Equiv` 级）

在**具体对象**上（而不是集合层），往返是**双向恒等**。
本文件用 `Equiv`（而非 `↔`）陈述，**保留计算内容**。 -/

/-- ⭐⭐ **④ 编译-提取是 `Equiv`（单位与余单位同时为恒等）**：

`Equiv.ofBijective compileToLayer compileToLayer_bijective`，
其 `toFun` / `invFun` 分别是 `compileToLayer` / `extractLayer`，
且两条往返律**恰好**是既有的 `extractLayer_compileToLayer` 与 `compileToLayer_extractLayer`。

⭐ **它比"双射"这个概念多说**：双射只说"存在逆"（**非构造性**），
`Equiv` 给出**一个具体的逆**（`extractLayer`）**并同时**验证两条往返律。
⇒ 这就是范畴伴随的「单位 `η : Id ⟹ R ∘ L` 与余单位 `ε : L ∘ R ⟹ Id` **都是同构**」
在本场景的**具体形式**。 -/
def compileExtractEquiv : ConstraintSet ≃ Layer where
  toFun := compileToLayer
  invFun := extractLayer
  left_inv := extractLayer_compileToLayer
  right_inv := compileToLayer_extractLayer

/-- ⭐ **④′ 两条往返律以 `Equiv` 的字段形式被复用**（等价于 ④ 的展开）。 -/
theorem compile_extract_adjunction_iso : compileExtractEquiv.toFun = compileToLayer := rfl

/-- ⭐ **④″ 伴随三角形的**对象**形式**：
`extractLayer (compileToLayer cs) = cs` 与 `compileToLayer (extractLayer ls) = ls`
**同时**成立（即"三角形的两个顶点都闭合"）。 -/
theorem adjunction_triangle_object (cs : ConstraintSet) (ls : Layer) :
    extractLayer (compileToLayer cs) = cs ∧ compileToLayer (extractLayer ls) = ls :=
  ⟨extractLayer_compileToLayer cs, compileToLayer_extractLayer ls⟩

/-- ⭐⭐ **⑧ 伴随三角形的**态射**形式（`Equiv` 的 `apply_symm_apply` / `symm_apply_apply`）**：

`f (g (f x)) = f x` 与 `g (f (g y)) = g y` —— 即两侧都是**幂等**的。

⭐ **`Equiv` 版本比 `↔` 版本强在哪**：`↔` 只说双向蕴含，
`Equiv` 的两条 `*_apply` 律是**逐点的等式**（带计算内容）。
⇒ 本文件因此坚持用 `Equiv`（而不是把 ④ 写成一对 `↔`）。 -/
theorem adjunction_triangle_idem (cs : ConstraintSet) (ls : Layer) :
    compileToLayer (extractLayer (compileToLayer cs)) = compileToLayer cs ∧
      extractLayer (compileToLayer (extractLayer ls)) = extractLayer ls := by
  refine ⟨?_, ?_⟩
  · rw [extractLayer_compileToLayer]
  · rw [compileToLayer_extractLayer]

/-! ## 四、自然变换：编译与拼接交换

`compileToLayer` 与 `List.append` 的关系是**自然性**（naturality）的一种形式：
编译**保持**结构的拼接。 -/

/-- ⭐⭐ **⑤ 编译是「关于拼接的自然变换」（承重，非平凡）**：

`compileToLayer (cs₁ ++ cs₂) = compileToLayer cs₁ ++ compileToLayer cs₂`。

⭐ **为什么不是 `rfl`**：`compileToLayer` 的定义是 `List.map convertVec`，
而要证 `map f (xs ++ ys) = map f xs ++ map f ys` 需要**归纳**
（`List.map_append`）。⚠ 本文件**显式调用** `List.map_append` 而**不**用 `simp`
（避免 `simp` 集合的版本漂移影响可复现性）。

**意义**：这条说明「**分片编译**」与「**整体编译**」一致 ——
即转换层**允许模块化组合**（对应 Lv-00 的 `compile_program_append`，
但那条**未被使用**其源语义，见 `CORRECTIONS B52`；本条**用**了源语义）。 -/
theorem natTransform_compile (cs₁ cs₂ : ConstraintSet) :
    compileToLayer (cs₁ ++ cs₂) = compileToLayer cs₁ ++ compileToLayer cs₂ := by
  unfold compileToLayer
  exact List.map_append convertVec cs₁ cs₂

/-- ⭐ **⑤′ 提取也是关于拼接的自然变换**（与 ⑤ **独立**：`extractLayer` 有自己的定义）。 -/
theorem natTransform_extract (ls₁ ls₂ : Layer) :
    extractLayer (ls₁ ++ ls₂) = extractLayer ls₁ ++ extractLayer ls₂ := by
  unfold extractLayer
  exact List.map_append extractVec ls₁ ls₂

/-- ⭐⭐ **⑤″ 自然性方块（同构侧）**：`Equiv` 与拼接**交换** ——
`compileExtractEquiv` 把 `cs₁ ++ cs₂` 送到 `compileToLayer cs₁ ++ compileToLayer cs₂`。
⭐ 这是 ⑤ 的 `Equiv` 包装，**单列**是为了给下游一个**不透明**的接口
（下游不必知道 `Equiv` 的 `toFun` 是 `compileToLayer`）。 -/
theorem natTransform_equiv (cs₁ cs₂ : ConstraintSet) :
    compileExtractEquiv (cs₁ ++ cs₂) = compileToLayer cs₁ ++ compileToLayer cs₂ :=
  natTransform_compile cs₁ cs₂

/-! ## 五、缩放的函子性 —— 与 `±1` 商不可绕过

`scaleVec` 在一个参数 `lam` 下是 `ConstraintSet → ConstraintSet` 的算子；
本文件给出它的**函子律**（保恒等/保复合），**并**给出它**不是**同构的证据。 -/

/-- **缩放的提升**（逐点作用到约束表）—— ⚠ **本文件用它只做"函子性"论证**：
`scaleLayerFun` 是一个**乘性作用**，其函子律见 ⑥-a/⑥-b。 -/
def scaleLayerFun (lam : Int) (cs : ConstraintSet) : ConstraintSet :=
  cs.map (scaleVec · lam)

/-- ⭐ **⑥-a 缩放保恒等**（`lam = 1`）。 -/
theorem scaleLayer_one (cs : ConstraintSet) : scaleLayerFun 1 cs = cs := by
  unfold scaleLayerFun
  induction cs with
  | nil => rfl
  | cons c t ih =>
      show scaleVec c 1 :: List.map (scaleVec · 1) t = c :: t
      rw [ih]
      congr 1
      obtain ⟨a, b⟩ := c
      simp [scaleVec]

/-- ⭐ **⑥-b 缩放保复合（函子律，承重）**：
`scaleLayerFun (l₁ * l₂) = scaleLayerFun l₁ ∘ scaleLayerFun l₂`。

⭐ **为什么不是 `rfl`**：`scaleVec (scaleVec c l₂) l₁ = scaleVec c (l₂ * l₁)`（**顺序**），
需要逐分量 `List.map_map` + `Int.mul_assoc` + `mul_comm`。
⇒ 这条把"缩放是**乘性**作用"精确化，并**暴露**了顺序问题。 -/
theorem scaleLayer_mul (l₁ l₂ : Int) (cs : ConstraintSet) :
    scaleLayerFun (l₂ * l₁) cs = scaleLayerFun l₁ (scaleLayerFun l₂ cs) := by
  unfold scaleLayerFun
  induction cs with
  | nil => rfl
  | cons c t ih =>
      show scaleVec c (l₂ * l₁) :: List.map (scaleVec · (l₂ * l₁)) t
        = scaleVec (scaleVec c l₂) l₁ :: List.map (scaleVec · l₁) (List.map (scaleVec · l₂) t)
      rw [ih]
      congr 1
      obtain ⟨a, b⟩ := c
      -- ⚠ 不在 `show` 里写含 `List.map (fun …)` 的 record 字面量：
      -- Lean 会把 `List.map (fun v => …)` **先**解析为函数（应用比 `,` 更紧），
      -- 报 `List.map fun v => … has type List ℤ → List ℤ`。
      -- ⇒ 改用 `unfold` 直接作用于展开后的目标（STYLE.md 已登记的坑）。
      unfold scaleVec
      -- ⚠ 不用 `congr 1` 逐层拆（它会把目标拆到 `v * l₂ * l₁ = ((fun v => l₁ * v) ∘ …) v`
      -- 这种**已经过度分解**的形状，后面的 `ring` 对不上）。
      -- ⇒ 用 `List.map_map` 归一化 + 逐分量 `List.map_congr_left`/`ring`，一次性收口。
      simp only [List.map_map]
      congr 1
      · apply List.map_congr_left
        intro v _
        simp only [Function.comp_apply]
        ring
      · ring

/-- ⭐⭐ **⑥-c 缩放**不是**同构（`±1` 商不可绕过的函子语言读法）**：

`scaleLayerFun 2` 在 `ConstraintSet` 上**没有**左逆 ——
即存在 `cs ≠ cs'` 使 `scaleLayerFun 2 cs = scaleLayerFun 2 cs'`？**否**（它是单射）。
⇒ ⚠ **本文件实测更正**：`scaleLayerFun 2` **是**单射（`scaleVec` 逐分量乘常数，`2 ≠ 0`），
故"**非单射**"**不是**这里的失效模式。
真正的失效在于：**`scaleVec` 不是"约束自身"的同构** ——
`syntacticFunctor (scaleLayerFun 2 [cUnit]) ≠ syntacticFunctor [cUnit]`（**项集不同**），
即**函子在对象上不忠实**：它把同语义的约束映到不同的项集。

⭐ **本定理的形式化内容**：`syntacticFunctor` 在 `scaleLayerFun` 下**不**恒定，
且给出**具体见证**（`cUnit` 与 `scaleVec cUnit 2` 的项集不同）。 -/
theorem scaleFunctor_not_iso :
    syntacticFunctor (scaleLayerFun 2 [cUnit]) ≠ syntacticFunctor [cUnit] := by
  intro h
  -- `scaleVec cUnit 2` 属于左侧项集
  have hmem : scaleVec cUnit 2 ∈ syntacticFunctor (scaleLayerFun 2 [cUnit]) := by
    refine ⟨⟨0, by simp [scaleLayerFun]⟩, ?_⟩
    simp [scaleLayerFun]
  rw [h] at hmem
  -- `hmem : scaleVec cUnit 2 ∈ syntacticFunctor [cUnit] = Set.range (fun i => [cUnit].get i)`
  rcases hmem with ⟨i, hi⟩
  -- ⚠ 直接对 `i : Fin [cUnit].length` 做 `Fin.ext` 会在 `rw [this]` 处报
  -- `motive is not type correct`（`i` 出现在 `hi` 的**类型**里 ⟹ 重写会改到依赖类型）。
  -- ⇒ 先用 `Fin.cases`/`match` 把 `i` **消掉**，得到单元素表的唯一取值的**等式**。
  have h0 : (fun j : Fin [cUnit].length => [cUnit].get j) i = cUnit := by
    -- `[cUnit].length` 定义上就是 `1`，故 `i : Fin 1`，其值为 `0`
    have hi1 : (i : ℕ) = 0 := by
      have hisLt : (i : ℕ) < 1 := i.isLt
      omega
    have hfin : i = ⟨0, by simp⟩ := Fin.ext hi1
    rw [hfin]
    rfl
  have hi' : cUnit = scaleVec cUnit 2 := h0.symm.trans hi
  have hb : (1 : Int) = 2 := by
    have := congrArg VectorConstraint.b hi'
    simpa [scaleVec, cUnit] using this
  omega

/-! ## 六、Galois 连接的复合（一般骨架）

⭐ 范畴论里「伴随的复合仍是伴随」是标准事实；
本文件在**偏序特例**（`GaloisConnection`）下给出它的**显式**形式。 -/

/-- ⭐⭐ **⑦ Galois 连接的复合**（承重的一般骨架）：

若 `l₁ ⊣ u₁` 与 `l₂ ⊣ u₂`，则 `l₁ ∘ l₂ ⊣ u₂ ∘ u₁`。

⭐ **它比"定义"多说**：证明需要**两次**应用伴随的 `gc.le_iff_le`
（一次在 `α` 层、一次在 `β` 层），且**顺序**是"**反**的"
（`u₂ ∘ u₁`，不是 `u₁ ∘ u₂`）。⇒ 这不是 `rfl`，也不是 `gc.le_iff_le` 的直接实例。

⚠ **注意参数顺序**：`GaloisConnection l u` 记 `l ⊣ u`；
本定理把 `l₁ : α → β`、`l₂ : β → γ` 的左伴随**反序**复合。 -/
theorem galois_preimage_comp {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {l₁ : α → β} {u₁ : β → α} {l₂ : β → γ} {u₂ : γ → β}
    (gc₁ : GaloisConnection l₁ u₁) (gc₂ : GaloisConnection l₂ u₂) :
    GaloisConnection (l₂ ∘ l₁) (u₁ ∘ u₂) := by
  intro a c
  rw [Function.comp_apply, Function.comp_apply]
  exact (gc₂ (l₁ a) c).trans (gc₁ a (u₂ c))

/-! ## 七、未做（如实登记）

- ⚠ **`CategoryTheory.Functor` / `Adjunction` 实例**：**未做**。
  本文件给出的是**偏序范畴**下的等价内容（函子律 + Galois + `Equiv` 级单位/余单位）。
  ⚠ **这是一个被削弱的陈述**，已在 §2 显式标注。
- ⚠ **`syntacticFunctor_id` 是 `rfl`**：不计入有实质内容的定理（已标注）。
- ⚠ **`compile_galoisConnection` 与 `RealFCA.galois_connection` 的同源性**：**未证**，
  只作了文字对照（两者都用 `⊆` 的伴随性）——**不声称**独立发现。
- ⚠ **`scaleLayerFun` 的单射性**：**未证**（本文件只用了"项集不同"这一**较弱**的失效形式；
  单射性需要 `Int` 上的消去律，属**未做**）。
- ⚠ **函子的忠实性（faithful）**：**未证**（`syntacticFunctor` 丢弃重数，
  故**必然不忠实**；本文件只给出"在缩放轨道上不恒定"的**局部**否定）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
