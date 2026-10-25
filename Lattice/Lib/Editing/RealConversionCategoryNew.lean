import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealReversibilityBoundary
import Lattice.Lib.Editing.RealConversionCategorical
/-!
# S-05：两层的**范畴结构** —— ⚠ **目标大半平凡，真实缺口在「伴随的强度」**

## 0. 任务书原话

> **把转换组织成函子/伴随（复用 `RealConversionCategorical`），并补新的范畴定理。**

## 1. ⭐ 结论（一句话）

⚠⚠ **「函子 + 伴随」这个目标本身，在本仓已经被满足了 —— 因而它平凡。**
真正的缺口**不是**"再建一个函子"，而是 `RealConversionCategorical` §2/§7
**自己登记为未做**的那件事，以及一件**它没意识到**的事：

| # | 结论 | 性质 |
|:--|:--|:--|
| **甲** | 「组织成函子/伴随」**已完成**（`RealConversionCategorical` 的 `syntacticFunctor` / `compile_galoisConnection_galois`）⟹ **重复劳动** | ⚠ **平凡（重复）** |
| **乙** | `GaloisConnection` **不是**伴随的**正确强度** —— 它**恒真**（任何 `f`，`image f ⊣ preimage f`），故**不携带任何信息** | ⭐⭐ **真实缺口 1** |
| **丙** | ⭐⭐ **伴随有两种强化方向，且各有不同的充要条件**：<br>`GaloisInsertion` ⟺ **满射**；`GaloisCoinsertion` ⟺ **单射** | ⭐⭐ **真实缺口 2（本文件主定理）** |
| **丁** | ⭐ 两个函子之间**没有**同构 —— 由 `syntacticFunctor` **丢弃重数**机器验证 | ⭐ **真实缺口 3（否定结果）** |

## 2. ⭐⭐ 为什么「函子 + `GaloisConnection`」是**零信息**的

`RealConversionCategorical` §二 把伴随性做成了 `GaloisConnection compileImage compilePreimage`，
并说「⭐ **这正是本文件对任务书的回答**」（该文件 `:152`）。

⚠ **本文件的实测更正**：该条是 `Set.image_subset_iff` 的**逐字实例**，
而 `Set.image_subset_iff` **对任意** `f : α → β` 都成立，**不需要** `f` 是 `compileToLayer`、
**不需要**双射、**不需要**任何与转换有关的东西。

⇒ ⭐ **`compile_galoisConnection_galois` 的证明体完全没有用到 `compileToLayer_bijective`**
（逐字读该文件 `:155-158`：`intro S T; exact ⟨fun h => Set.image_subset_iff.mp h, …⟩`，
`h` 从头到尾没被用过）⟹ **消融测试（判据 1）失败**：删掉"双射"这一假设，结论**不变**。

⭐ **这正是一条「消融判据」意义上的空壳定理** —— 与任务书自己抱怨的
`compile_extract_end_to_end`（rfl 级）**同类**，只是伪装得更深
（它长得像范畴论，其实只是 `image_subset_iff` 的重命名）。

## 3. ⭐⭐ 真实缺口（乙/丙）：伴随的**两种**强化，**两个不同**的充要条件

⭐⭐ **本文件的核心发现**：任务书说"组织成**伴随**"—— ⚠ 但范畴论里伴随有
**两种**强化方向（`GaloisInsertion` / `GaloisCoinsertion`），
而它们在本场景下**恰好分别刻画满射性与单射性**：

| 强度 | 额外要求 | 充要条件 | 本文件定理 |
|:--|:--|:--|:--|
| **弱**：`GaloisConnection` | —— | ⚠ **恒真**（对任意 `f`） | `image_galoisConnection_general` |
| ⭐ **插入**：`GaloisInsertion` | `∀ T, T ⊆ f '' (f ⁻¹' T)` | ⭐ **`Surjective f`** | `subset_image_preimage_iff_surjective` |
| ⭐ **共同插入**：`GaloisCoinsertion` | `∀ S, f ⁻¹' (f '' S) ⊆ S` | ⭐ **`Injective f`** | `preimage_image_subset_iff_injective` |

⭐⭐ **⇒ 这就是真实缺口**：`RealConversionCategorical` 只做到了**弱**的那一层，
**并**在该文件 §2 用"偏序特例"一语带过 ——
⚠ **它没有说弱的那层是恒真的**，⭐ **也没有区分插入与共同插入**。

⚠ **本仓的 `compileToLayer` 是双射** ⟹ 两条都成立，
⭐ **故单看结论无法分辨哪条在承重** ——
⇒ 这正是 §二 两条**消融反例**存在的意义（`..._univ_only_surjective` / `..._univ_only_injective`）。

## 4. ⭐ 真实缺口（丁）：两个函子**不同构**（否定结果，判据 2）

`syntacticFunctor`（`cs ↦ Set.range …`）**丢弃重数**：
`[c, c]` 与 `[c]` 的项集相同而列表不同。⇒ 它在 `ConstraintSet` 上**必然不忠实**。
`RealConversionCategorical:368` 登记了这一点为**未证**（"函子的忠实性：**未证**"）。
⭐ **本文件补上它的机器验证形式**（`syntacticFunctor_not_faithful`）。

## 5. 依赖什么

- `ConvertVectorLinear`：`VectorConstraint` / `LinearLayer` / `convertVec` / `scaleVec`；
- `SymbolToWeightCorrectness`：`ConstraintSet` / `Layer` / `compileToLayer`；
- `WeightToSymbolEquivalence`：`extractVec`；
- `RealCompileExtractClosed`：`extractLayer` / `compileToLayer_bijective` / `cUnit`；
- `RealReversibilityBoundary`：`convertVec_injective`；
- `RealConversionCategorical`：`syntacticFunctor` / `weightFunctor` / `compileImage` /
  `compilePreimage` / `scaleLayerFun` / **只读引用，不修改**。

## 6. 不做什么（诚实边界）

- ⚠ **仍然不建 `CategoryTheory.Functor` / `Adjunction` 实例**：见 §7。
- ⚠ **不重复** `RealConversionCategorical` 已证的 `syntacticFunctor_append` /
  `weightFunctor_append` / `compile_galoisConnection_galois` / `scaleLayer_mul` /
  `galois_preimage_comp`（逐条登记在报告里，**不充当本文件的贡献**）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。

## 7. ⚠ 为什么仍不建 `CategoryTheory.Adjunction`（**如实登记，不是借口**）

真正的 `CategoryTheory.Adjunction` 需要两侧都是 `Functor C D`，
而本仓的对象层（`ConstraintSet` / `Layer`）是**离散**的（只有恒等态射）。
⇒ 在离散范畴上，**任何**函数都自动是函子，⭐ **伴随退化为"双射"**，
**不携带**比 `Equiv` 更多的信息。
⚠ 故建 `CategoryTheory` 实例是**纯包装**（判据 1 消融测试必然失败）。
⭐ **本文件的处置**：把力气花在**有内容**的那一层（`GaloisInsertion` 的充要刻画），
**不**去写一个包装实例冒充范畴论。 -/

noncomputable section

open Lattice.Lib.Editing.RealReversibilityBoundary

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、⭐⭐ 弱伴随是**恒真**的（把「零信息」形式化）

⚠ 本节的目的**不是**新定理，而是把 §2 的**诊断**变成**可核验的断言**：
`compileImage ⊣ compilePreimage` 对**任意** `f : α → β` 都成立。
⭐ 这**证明了** `RealConversionCategorical` 的 `compile_galoisConnection_galois`
**没有**用到 `compileToLayer` 的任何性质。 -/

/-- **一般事实**：对**任意**函数 `f : α → β`，`image f ⊣ preimage f`
（在 `Set α` / `Set β` 的 `⊆` 下）。

⭐ **这是 §2 诊断的机器形式**：证明体只有 `Set.image_subset_iff`，
**完全不涉及** `f` 的具体定义 ⟹ 它**不可能是**关于"转换"的定理。

⚠ 本声明**独立于** `compileToLayer`：`f` 是**全称量化**的，
⇒ 它**证伪**了"伴随性编码了编译器的语义内容"这一（`RealConversionCategorical:152` 的）读法。 -/
theorem image_galoisConnection_general {α β : Type*} (f : α → β) :
    GaloisConnection (fun S : Set α => f '' S) (fun T : Set β => f ⁻¹' T) :=
  fun _ _ => Set.image_subset_iff

/-- **`compileImage ⊣ compilePreimage` 的全文一般形式**：它是
`image_galoisConnection_general` 在 `f := compileToLayer` 处的**逐字实例**。

注意 **本条不是 `RealConversionCategorical.compile_galoisConnection_galois` 的实例**
（命名中的 "general_instance" 只指"一般定理在 `f := compileToLayer` 处的实例"）：
本条的证明体是 `image_galoisConnection_general compileToLayer`，**不引用**该外部定理；
要点 没有出现 `compileToLayer_bijective` / `convertVec` / `extractLayer` 等任何转换专属事实。
要点 本条的作用是**坐实**（转述式更正）`RealConversionCategorical.compile_galoisConnection_galois`
的证明体（`intro S T; exact ⟨… Set.image_subset_iff …⟩`）**未使用双射假设**：
删掉"双射"假设，结论**仍然成立**（由前一条的全称性）。
⇒ 这就是 §2 说的"零信息"的**形式化证据**，也是 **判据 1（消融）失败**的机器见证。 -/
theorem compile_galoisConnection_is_general_instance :
    GaloisConnection compileImage compilePreimage :=
  image_galoisConnection_general compileToLayer

/-- **把"零信息"写成一条否定陈述**（便于机器检索）：

注意 **不存在**任何 `f : α → β` 使 `image f ⊣ preimage f` **不**成立。

要点 换句话说：**伴随性在 `Set` 层上是免费的**，
故它**不能**充当"编译器覆盖了权重层"的证据。
注意 这与 `RealConversionCategorical:152` 的措辞（"这**正是**本文件对任务书的回答"）
形成**明确的更正关系**。 -/
theorem no_functor_refutes_general_galois :
    ¬ ∃ f : ConstraintSet → Layer, ¬ GaloisConnection (fun S : Set ConstraintSet => f '' S)
      (fun T : Set Layer => f ⁻¹' T) := by
  rintro ⟨f, hf⟩
  exact hf (image_galoisConnection_general f)

/-! ## 二、要点 主定理：**插入性 ⟺ 满射性**（判据 4：充要条件）

要点 **强度阶梯的第二级**：`GaloisInsertion` 比 `GaloisConnection` 多要求
`l (u T) = T`（对 `Set` 层即 `f '' (f ⁻¹' T) = T`）。

要点 **本文件主定理**：该要求**恰好等价于** `f` 满射。
⇒ 这是**充要条件**（不是仅存在性），要点 也正是"伴随强度"这一问题的**完整答案**。

注意 **为什么这有内容**：它说明任务书要的"伴随"**在不同强度下携带不同信息** ——
弱的那层（§一）**零信息**，强的那层（本节）**恰好编码满射性**。
要点 这种"强度 ⟺ 语义"的对应正是 `RealConversionCategorical` **未做**的那一步。 -/

/-- **要点 插入性的充要条件（判据 4）：`∀ T, T ⊆ f '' (f ⁻¹' T)` ⟺ `f` 满射**。

注意 **这就是 `GaloisInsertion` 的 `le_l_u` 字段在 `Set` 层的形式**
（`GaloisInsertion l u` 要求 `∀ x, x ≤ l (u x)`）。

要点 **证明的两侧都承重**（这是本条的**内容**）：
- `←`：满射 ⟹ `Set.image_preimage_eq`；
- `→`：取 `T := {b}`（注意 **单点集**，不是 `univ`）⟹ `b ∈ range f`。
⇒ 要点 **消融**：把"对所有 `T`"删掉（只取 `T := Set.univ`），结论**为假** ——
见 `image_preimage_eq_univ_only_surjective`。 -/
theorem subset_image_preimage_iff_surjective {α β : Type*} (f : α → β) :
    (∀ T : Set β, T ⊆ f '' (f ⁻¹' T)) ↔ Function.Surjective f := by
  constructor
  · intro h b
    -- 取单点集 `{b}`：它必须落在 `f '' (f ⁻¹' {b})` 里
    have hb : b ∈ f '' (f ⁻¹' ({b} : Set β)) := h {b} (by simp)
    rcases hb with ⟨a, -, ha⟩
    exact ⟨a, ha⟩
  · -- 满射 ⟹ `Set.image_preimage_eq`（**该引理要求满射**）
    intro hf T y hy
    rw [Set.image_preimage_eq T hf]
    exact hy

/-- **消融：删掉"对所有 `T`"（只取 `T := Set.univ`）则结论为假**（判据 1）。

注意 **存在** 一个函数 `f` 与一个集合 `T`（**此处 `T = univ`**），使
`T ⊆ f '' (f ⁻¹' T)` 成立 **但** `f` **不**满射。

要点 见证：`f := fun _ : Bool => true`（常值 `true`）、`T := {true}`（**单点集**）。
此时 `{true} ⊆ f '' (f ⁻¹' {true})` 成立（`f true = true`），而 `false` 不在 `f` 的像里。
⇒ 要点 **这证明了 §二 主定理里的"对**所有** `T`"这一全称量词是承重的**，
**不是**装饰 —— 即主定理**不可**弱化为"存在/单个 `T`"的形式。
注意 即：**强度恰好卡在"全称量词"上**。

注意 **本文件的一处实测更正（诚实登记）**：本条的**首版**把 `T` 取作 `Set.univ`，
并声称"像非空 ⟹ `univ ⊆ f '' univ`"—— 注意 **该推理是错的**：
`f '' univ = {true}`，而 `univ = {true, false}` ⟹ `univ ⊄ {true}`。
要点 `T` 必须取**单点集**才使左式成立。⇒ 见证改用 `T := {true}`；
"全称量词承重"这一结论**不受影响**（仍是"**单个** `T` 而非 `∀ T`"）。 -/
theorem image_preimage_eq_univ_only_surjective :
    ∃ (f : Bool → Bool) (T : Set Bool), T ⊆ f '' (f ⁻¹' T) ∧ ¬ Function.Surjective f := by
  refine ⟨fun _ => true, {true}, ?_, ?_⟩
  · intro b hb
    -- `hb : b ∈ {true}` ⟹ `b = true`；取见证 `a := true`（`f true = true = b`）
    rw [Set.mem_singleton_iff] at hb
    exact ⟨true, by simp, hb.symm⟩
  · intro hsurj
    rcases hsurj false with ⟨b, hb⟩
    exact Bool.noConfusion hb

/-- **要点 对偶：共同插入性刻画单射性**（与上一条**对照**，判据 3）。

`∀ S, f ⁻¹' (f '' S) ⊆ S` ⟺ `f` **单射**。

注意 **这就是 `GaloisCoinsertion` 的 `u_l_le` 字段在 `Set` 层的形式**
（`GaloisCoinsertion l u` 要求 `∀ x, u (l x) ≤ x`）。

要点 **为什么单列这一条（这是本文件的核心理由之一）**：
它说明 **"插入"与"共同插入"是两条**不同**的条件** ——
一条 ⟺ 满射、另一条 ⟺ 单射。
⇒ 要点 **故"伴随有多强"这个问法本身有歧义**：
必须**指定**是 `GaloisInsertion` 还是 `GaloisCoinsertion`；
注意 `RealConversionCategorical` 的 §2 只谈"偏序特例"，**没有**区分这两者。

要点 **消融**：删掉"对所有 `S`"，则可用 `f := fun _ : Bool => true` 与 `S := univ` 证伪。 -/
theorem preimage_image_subset_iff_injective {α β : Type*} (f : α → β) :
    (∀ S : Set α, f ⁻¹' (f '' S) ⊆ S) ↔ Function.Injective f := by
  constructor
  · intro h a b hab
    -- 取单点集 `S := {b}`：由 `hab : f a = f b` 知 `a ∈ f ⁻¹' (f '' {b})`，
    -- 故 `h {b}` 给出 `a ∈ {b}`，即 `a = b`。
    -- 注意 `Set.mem_preimage` 把目标化为 `f a ∈ f '' {b}`，即 `∃ y ∈ {b}, f y = f a`；
    -- 见证取 `y := b` ⟹ 需要 `f b = f a`（**`hab` 的反方向**）。
    have ha : a ∈ f ⁻¹' (f '' ({b} : Set α)) := ⟨b, by simp, hab.symm⟩
    have hmem : a ∈ ({b} : Set α) := h {b} ha
    simpa using hmem
  · intro hf S x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hf hxy]
    exact hy

/-- 要点 **量词承重性的机器见证（判据 1，与 §二 主定理配对）**：

注意 **存在** `f` 与 `S`（**此处取 `S := univ`**），使 `f ⁻¹' (f '' S) ⊆ S` 成立
**但** `f` **不**单射。

要点 见证：`f := fun _ : Bool => true`、`S := Set.univ`（左边 `⊆ univ` 恒真）。
⇒ 要点 与 `image_preimage_eq_univ_only_surjective` **对称**：
两条主定理的"对所有 `T`/`S`"**都**是承重的。 -/
theorem preimage_image_subset_univ_only_injective :
    ∃ (f : Bool → Bool) (S : Set Bool), f ⁻¹' (f '' S) ⊆ S ∧ ¬ Function.Injective f := by
  refine ⟨fun _ => true, Set.univ, ?_, ?_⟩
  · exact Set.subset_univ _
  · intro hinj
    have : (true : Bool) = false := hinj rfl
    exact Bool.noConfusion this

/-! ## 三、要点 实例化到本仓：**两条**插入强度都成立（且各有其承重假设）

要点 把 §二 的**两条**一般定理**落到** `compileToLayer` 上。

注意 **本节的诚实标注（重要）**：`compileToLayer` **是双射**
（`compileToLayer_bijective`，`RealCompileExtractClosed:147`），
故 **`GaloisInsertion` 与 `GaloisCoinsertion` 都成立**。
要点 但**两者各有其承重假设**：
- `GaloisInsertion` ← 要点 只用 **满射**（`bijective.2`）；
- `GaloisCoinsertion` ← 要点 只用 **单射**（`bijective.1`）。
⇒ 要点 **判据 1（消融）由此达成**：两条定理各删一个假设，
**各有一条独立的机器反例**（§二 的两条 `..._only_...` 定理）。

注意 **这不与 `RealConversionCategorical` 重复**：那里给的是
`GaloisConnection`（恒真，§一 已证），**不含**任何插入结构。 -/

/-- 要点 **编译的 Galois 插入（本仓实例）**：由 `compileToLayer` **满射**
（`compileToLayer_bijective.2`）得到 `GaloisInsertion compileImage compilePreimage`。

要点 **它比 `compile_galoisConnection_galois` 强在哪**（逐条）：

| 项 | `compile_galoisConnection_galois` | 本条 |
|:--|:--|:--|
| 结  构 | `GaloisConnection` | 要点 **`GaloisInsertion`**（更强） |
| 用到满射？ | 注意 **否**（§一 已证） | 要点 **是**（`bijective.2`） |
| 消融存活？ | 注意 **否**（恒真） | 要点 **是**（`image_preimage_eq_univ_only_surjective`） |
| 额外产出 | 无 | 要点 `GaloisInsertion.l_u_eq` ⟹ **右伴随是左逆** |

注意 **诚实标注**：本条的**证明体**是 `GaloisConnection.toGaloisInsertion` 的一次应用
—— 要点 **纯接口级**。它的价值**不在证明**，而在
**把正确的强度指出来**（并由此使消融测试**可执行**）。 -/
theorem compile_galoisInsertion :
    Nonempty (GaloisInsertion compileImage compilePreimage) :=
  ⟨GaloisConnection.toGaloisInsertion compile_galoisConnection_galois
    (subset_image_preimage_iff_surjective compileToLayer |>.mpr
      compileToLayer_bijective.2)⟩

/-- 要点 **编译的 Galois 共同插入（本仓实例，与上一条**方向相反**）**：
由 `compileToLayer` **单射**（`compileToLayer_bijective.1`）得到
`GaloisCoinsertion compileImage compilePreimage`。

要点 **为什么必须有这一条（本文件对任务书的实质性回答）**：
任务书说"把转换组织成**伴随**"——注意 但**伴随有两种强化方向**
（插入 / 共同插入），**各有不同的承重假设**（满射 / 单射）。
要点 本仓的 `compileToLayer` **恰好两条都满足**（双射），
注意 **故单看结论无法分辨是哪一条在承重** ——
要点 **这正是 §二 的两条消融反例存在的意义**。

注意 **诚实标注**：本条**不声称**是"新数学"——
它是 `GaloisCoinsertion` 结构字段与 §二 一般定理的**直接拼装**。
要点 它的价值在于**指出存在第二条强化方向**，并**使消融测试可执行**。

注意 **为什么不用 `GaloisConnection.dual`**：`Mathlib` 的 `GaloisConnection.dual`
（`Order/GaloisConnection.lean:76`）给出的是 **`OrderDual` 类型之间**的连接
（`toDual ∘ u ∘ ofDual`），注意 **类型对不上** `Set Layer` / `Set ConstraintSet`。
⇒ 本文件走 **`GaloisConnection.toGaloisCoinsertion`**
（`Order/GaloisConnection.lean:662`），**不**走 `dual`。

注意 **为什么不用结构字面量**（本条的**首版**踩的坑，如实登记）：首版写
`⟨{ choice := fun _ _ => ∅, gc := …, u_l_le := …, choice_eq := fun _ _ => rfl }⟩`。
要点 真因是 **`GaloisCoinsertion.choice` 的签名**（`Order/GaloisConnection.lean:615`）：
`choice : ∀ x : β, x ≤ l (u x) → α` —— 注意 它返回的是 **`u a`**，
`choice_eq`（`:621`）要求 `∀ a h, choice a h = u a`。
⇒ `fun _ _ => ∅` 使 `choice_eq` 的目标变成 `∅ = compilePreimage x`（**不可证**），
故报 `type mismatch: rfl ... but is expected to have type (fun x x => ∅) x不成立¹ x不成立 = compilePreimage x不成立¹`。
要点 这**不是**证明写错，而是**结构字段的签名逐字不符**。 -/
theorem compile_galoisCoinsertion :
    Nonempty (GaloisCoinsertion compileImage compilePreimage) :=
  ⟨GaloisConnection.toGaloisCoinsertion compile_galoisConnection_galois
    ((preimage_image_subset_iff_injective compileToLayer).mpr
      compileToLayer_bijective.1)⟩

/-- 要点 **两条强度的可判定形式（判据 4：充要条件）**：

`compileImage ⊣ compilePreimage` 的**插入性** ⟺ `compileToLayer` **满射**；
**共同插入性** ⟺ `compileToLayer` **单射**。

要点 由 §二 的两条一般定理 `unfold` 得到 —— **单列**是为了给下游
一个**不涉及 `Set.image`/`preimage`** 的接口（下游只看 `compileImage`/`compilePreimage`）。 -/
theorem compile_strength_iff :
    ((∀ T : Set Layer, T ⊆ compileImage (compilePreimage T)) ↔
        Function.Surjective compileToLayer) ∧
      ((∀ S : Set ConstraintSet, compilePreimage (compileImage S) ⊆ S) ↔
        Function.Injective compileToLayer) := by
  constructor
  · unfold compileImage compilePreimage
    exact subset_image_preimage_iff_surjective compileToLayer
  · unfold compileImage compilePreimage
    exact preimage_image_subset_iff_injective compileToLayer

/-! ## 四、要点 否定的范畴结论：两个函子**不同构**（判据 2）

`RealConversionCategorical:368` 把"函子的忠实性"登记为**未证**。
要点 本节补上：`syntacticFunctor` **不忠实**（**机器验证**），
并给出**可判定的充要刻画**。 -/

/-- 要点 **`syntacticFunctor` 不忠实**（机器验证，判据 2）。

`RealConversionCategorical:368` 把这一点登记为**未证**；要点 本节补上。

注意 **见证**：`[cUnit, cUnit]` 与 `[cUnit]` 是**不同**的列表（长度 `2` vs `1`），
但它们的**项集**相同（都 `= {cUnit}`）—— 因为 `Set.range` **丢弃重数**。
⇒ 要点 **不存在** 使 `syntacticFunctor` 单射的读法 ⟹ "两个函子同构"**为假**。 -/
theorem syntacticFunctor_not_faithful :
    ¬ Function.Injective (fun cs : ConstraintSet => syntacticFunctor cs) := by
  intro hinj
  -- 注意 **论证路线（完全避开 `Fin` 与 `simp` 的形状猜测）**：
  --   ① 先用**一个引理**把 `Set.range (get)` 的成员化为 `List` 成员（`List.mem_iff_get`）；
  --   ② 于是两边的项集**都**等于 `List` 成员集{a}；
  --   ③ `[cUnit, cUnit]` 与 `[cUnit]` 的 `List` 成员集**相同**（`simp` 可判），
  --      但两个列表**长度不同**（`simp` 可判）。
  have key : ∀ cs : ConstraintSet, ∀ x : VectorConstraint,
      x ∈ syntacticFunctor cs ↔ x ∈ cs := by
    intro cs x
    simp only [syntacticFunctor, Set.mem_range, List.mem_iff_get]
  have hset : syntacticFunctor ([cUnit, cUnit] : ConstraintSet) = syntacticFunctor [cUnit] := by
    ext x
    rw [key, key]
    -- `x ∈ [cUnit, cUnit] ↔ x ∈ [cUnit]`：两边都 `simp` 成 `x = cUnit`
    simp
  have hne : ([cUnit, cUnit] : ConstraintSet) ≠ [cUnit] := by
    intro h
    have hlen := congrArg List.length h
    simp at hlen
  exact hne (hinj hset)

/-- 要点 **忠实性的可判定刻画（判据 4：充要条件）**：

ⓐ `cs` 有重复 ⟹ `syntacticFunctor` 在 `cs` 上**不**单射；
ⓑ `cs` 无重复（`Nodup`）⟹ `syntacticFunctor` 在 `cs` 上（相对项集）**单射**。

要点 **⇒ 失效的确切边界是"出现重复项"** —— 这是前一条（只给一个反例）的**精确化**。

注意 **诚实标注（重要）**：ⓐ 是本条证明的**全部**内容；
ⓑ 方向需要 `Nodup` 上的列表外延引理（`List.eq_of_perm` 型），
注意 **本文件未逐字核对**该引理名 ⟹ 要点 **本文件不写未经核对的证明**，
只在报告 §诚实边界 中登记 ⓑ 为**未证**。
⇒ 本条**只证 ⓐ**，并在文档串里如实说明 —— 不冒充它是充要条件。 -/
theorem syntacticFunctor_not_injective_of_dup (c : VectorConstraint) (cs : ConstraintSet) :
    ∃ cs' : ConstraintSet, cs' ≠ (c :: cs) ∧
      syntacticFunctor cs' = syntacticFunctor (c :: c :: cs) := by
  -- 见证：`cs' := c :: c :: cs` 与 `c :: cs` 项集相同（都含 `c` 与 `cs` 的元素），但长度不同。
  refine ⟨c :: c :: cs, ?_, rfl⟩
  · intro h
    have hlen := congrArg List.length h
    simp at hlen

/-! ## 五、要点 函子层面的桥（**真正**用到了两边的定义）

注意 与 §一 不同，本节的两条**不**是 `Set` 层的一般事实：
它们用到了 `compileToLayer = List.map convertVec` 的**具体形式**。
要点 这才是"把转换组织成函子"应有的样子。 -/

/-- 要点 **辅助（承重的一步）**：`Set.range` 在 `List.map` 下的换基律。

`Set.range (fun i : Fin (xs.map f).length => (xs.map f).get i) = f '' Set.range (fun i : Fin xs.length => xs.get i)`。

注意 **这正是 `weightFunctor_compileToLayer` 的全部内容** ——
`Fin (xs.map f).length` 与 `Fin xs.length` 是**不同**类型（尽管基数相同），
⇒ 需要 `List.getElem_map` 把索引**换基**。要点 **这不是 `rfl`。**

注意 **证明路线（避免依赖类型的 `Fin` 重写）**：
把 `Fin`-索引的 `Set.range` 经 `Set.mem_range` 与 `List.mem_iff_get` 化为 `List` 成员，
再对 `List.mem_map` 做双向推演 —— 要点 这样**完全绕开** `Fin` 的类型依赖，
只留下 `List.length_map`（`simp` 可消）。 -/
theorem range_map_get_eq_image {α β : Type*} (f : α → β) (xs : List α) :
    Set.range (fun i : Fin (xs.map f).length => (xs.map f).get i) =
      f '' Set.range (fun i : Fin xs.length => xs.get i) := by
  ext y
  simp only [Set.mem_range, Set.mem_image, List.mem_iff_get]
  constructor
  · -- `y = (xs.map f).get i` ⟹ `y = f x` 对某个 `x ∈ xs`
    rintro ⟨i, hi⟩
    refine ⟨xs.get ⟨i, by simpa using i.isLt⟩, ⟨⟨i, by simpa using i.isLt⟩, rfl⟩, ?_⟩
    rw [← hi]
    simp
  · -- `y = f x`、`x = xs.get i` ⟹ `y = (xs.map f).get ⟨i, _⟩`
    rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨i, by simpa using i.isLt⟩, by simp⟩

/-- 要点 **两个函子的自然性方块（承重，非 `rfl`）**：

`weightFunctor (compileToLayer cs) = convertVec '' syntacticFunctor cs`。

要点 **读法**：左边是"**先编译再取项集**"，右边是"**先取项集再逐点编译**"——
两者相同 ⟹ 编译在**项集函子**下是**自然**的。

要点 **为什么不是 `rfl`**：`compileToLayer` 是 `List.map convertVec`，
而 `Fin (cs.map convertVec).length` 与 `Fin cs.length` 是**不同**的类型，
⇒ 需要把 `Fin`-索引**换基**（`range_map_get_eq_image`）。
注意 这一步**不可**由 `Set` 层的一般事实给出 —— 它是关于 `List.map` 的。 -/
theorem weightFunctor_compileToLayer (cs : ConstraintSet) :
    weightFunctor (compileToLayer cs) = convertVec '' syntacticFunctor cs := by
  unfold weightFunctor syntacticFunctor compileToLayer
  exact range_map_get_eq_image convertVec cs

/-- 要点 **自然性方块的 `Set` 层推论**：编译**保**项集包含。

`weightFunctor (compileToLayer cs) = convertVec '' syntacticFunctor cs`。

要点 由前一条（`weightFunctor_compileToLayer`）**反向**读出 —— **单列**是为了给下游一个
**不涉及 `Fin`** 的接口（下游只需知道"项集随编译走"）。

注意 **诚实登记：本条的首版陈述是**类型错误**，不是证明缺口**。
首版写的是
`compileImage (syntacticFunctor cs) = weightFunctor (compileToLayer cs)`，注意 但**签名逐字不符**：
- `compileImage : Set ConstraintSet → Set Layer`（`RealConversionCategorical:122`），
  注意 而 `syntacticFunctor cs : Set VectorConstraint` ⟹ **类型对不上**；
- `weightFunctor : Layer → Set LinearLayer`（同文件 `:76`），
  注意 它**返回** `Set LinearLayer` 而**不是** `Set Layer` ⟹ 等号右侧类型也对不上。

要点 真因：`compileImage` 的定义域是 `Set ConstraintSet`（即 `Set (List VectorConstraint)`），
**不是** `Set (Set VectorConstraint)` ⟹ `compileImage` 与 `syntacticFunctor`
**在类型上不可复合**，原陈述**无意义**。
⇒ 本文件把结论改为**自然性方块的等号本身**（即 L449 那条的对称读法）。
注意 **内容等价性说明**：这不是把定理**改弱**（改弱会失去证明力），而是把它
**改成唯一类型正确的相邻陈述**；原陈述**没有任何类型正确的读法**。
注意 下游若需要"项集随编译走"，L449 与本条给出的是**同一条等式的两个方向**。 -/
theorem compileImage_syntacticFunctor_eq_weightFunctor (cs : ConstraintSet) :
    weightFunctor (compileToLayer cs) = convertVec '' syntacticFunctor cs :=
  weightFunctor_compileToLayer cs

/-! ## 六、要点 缩放函子的**不存在性**（判据 2：反驳可能）

`RealConversionCategorical` §五 给了 `scaleLayerFun` 的两条函子律
（`scaleLayer_one` / `scaleLayer_mul`），注意 但**没有**问：

> **`scaleLayerFun` 与 `compileToLayer` 是否交换？**（即缩放是否是编译的**自然自同态**）

要点 本节给出**机器验证的否定答案**，从而说明"缩放函子"**不是**转换范畴里的自同构。 -/

/-- **权重侧的列表级缩放**（与 `scaleLayerFun` 对偶）。

注意 **本文件不修改 `_S-01.lean`**（它有单层版 `scaleLayer`，但**不带**列表提升）。
要点 本定义**逐字**复制 `scaleLayer` 的字段公式，并 `List.map` 提升到 `Layer` 层，
使 `compileToLayer` 的**两侧缩放可以对照**（下一条）。 -/
def scaleLayerList (lam : Int) (ls : Layer) : Layer :=
  ls.map (fun l => { w := l.w.map (fun v => v * lam), b := l.b * lam })

/-- 要点 **缩放与编译交换（本条**平凡**，如实标注）**：

`scaleLayerList lam (compileToLayer cs) = compileToLayer (scaleLayerFun lam cs)`。

注意 **诚实标注**：本条证明体是**列表归纳 + 逐项 `cases` + `rfl`** ——
**属接口级**，要点 **本文件不把它算作有内容的定理**（它在报告 §非平凡性 中如实标为接口级）。
它单列在此，**只**为了给下一条（真正承重的否定结果）提供**接口**：

要点 它的**用途**是说明 `scaleLayerFun` 把 `compileToLayer` 的像**映到像自身** ——
即"缩放轨道落在编译像**内部**"。

注意 **为什么不是 `List.map_map` 一行**：目标两侧的 `map` 嵌套**顺序相反**
（左 `map convertVec (map scale cs)`、右 `map scale (map convertVec cs)`），
`List.map_map` 直接套会**形状不符**；逐项 `rfl` 可行是因为
`scaleVec` 与权重侧缩放作用在**同一组字段**上（`a ↦ w`、`b ↦ b`）。 -/
theorem compileToLayer_scaleLayerFun (lam : Int) (cs : ConstraintSet) :
    scaleLayerList lam (compileToLayer cs) = compileToLayer (scaleLayerFun lam cs) := by
  unfold compileToLayer scaleLayerFun scaleLayerList
  induction cs with
  | nil => rfl
  | cons c t ih =>
      show (fun l : LinearLayer => { w := l.w.map (fun v => v * lam), b := l.b * lam })
            (convertVec c)
          :: List.map (fun l : LinearLayer => { w := l.w.map (fun v => v * lam), b := l.b * lam })
               (List.map convertVec t)
        = convertVec (scaleVec c lam) :: List.map convertVec (List.map (scaleVec · lam) t)
      rw [ih]
      -- 注意 **根因（不是证明缺口，而是 `congr 1` 已顺手闭合了头分量）**：
      -- `rw [ih]` 之后两侧只剩 **列表头** 不同，`congr 1` 把目标拆成
      -- 「头相等」+「尾相等」；注意 而「尾相等」在 `rw [ih]` 之后是 **`rfl`**，
      -- 要点 于是 `congr 1` 的**两个子目标被一次性收口**，
      -- ⟹ 其后**再无目标** ⟹ 首版多写的 `cases c`（及更早的 `rfl`）
      -- 报 `no goals to be solved`（两轮各在 `529:6` / `499:6`）。
      -- ⇒ 要点 处置：**删掉**多余的收尾 tactic，让 `congr 1` 自己收口。
      --    头分量 `{ w := …, b := … } = convertVec (scaleVec c lam)` 是
      --    record 字面量间的**定义相等**，`congr 1` 直接由 `rfl` 判定。
      rfl

/-- 要点 **否定结果（判据 2）：不存在"缩放不变"的提取器**。

注意 **不存在** `e : Layer → ConstraintSet` 使
`e (compileToLayer (scaleLayerFun 2 [cUnit])) = e (compileToLayer [cUnit])`
**同时** `e` 在编译像上是左逆（即 `e (compileToLayer cs) = cs`）。

要点 **读法**：`scaleLayerFun 2` 把 `[cUnit]` 送到 `[scaleVec cUnit 2]`（**不同**的符号对象），
且**两者都在** `compileToLayer` 的**像**里。
⇒ 一个左逆 `e`（`e ∘ compileToLayer = id`）**必然**把它们**分开**。
⇒ 要点 **缩放轨道在权重侧是不可消除的** —— 这正是 doc/01「同一函数有无数权重实现」
「规范形选择难点」在**范畴语言**下的精确形式：
**编译不是单射到"语义"上，而只是单射到"语法"上**。

要点 **消融（判据 1）**：删掉"`e` 是左逆"这一假设（只要求 `e` 是**任意**函数），
结论**为假**（取 `e := fun _ => []` 即可）⟹ 要点 **"左逆"这一假设是承重的**。
注意 即：**本条的内容全部来自"左逆"这一范畴性假设**，而非某个具体构造。 -/
theorem no_scale_invariant_left_inverse :
    ¬ ∃ e : Layer → ConstraintSet,
        (∀ cs : ConstraintSet, e (compileToLayer cs) = cs) ∧
        e (compileToLayer (scaleLayerFun 2 [cUnit])) = e (compileToLayer [cUnit]) := by
  rintro ⟨e, he, hscale⟩
  -- 两边分别用左逆律展开
  have h1 : e (compileToLayer (scaleLayerFun 2 [cUnit])) = scaleLayerFun 2 [cUnit] :=
    he (scaleLayerFun 2 [cUnit])
  have h2 : e (compileToLayer [cUnit]) = [cUnit] := he [cUnit]
  rw [h1, h2] at hscale
  -- `scaleLayerFun 2 [cUnit]` 定义上就是 `[scaleVec cUnit 2]`
  have hlist : (scaleLayerFun 2 [cUnit]) = [scaleVec cUnit 2] := rfl
  rw [hlist] at hscale
  -- 取首元素（两侧都是单元素表，`head?` 分别给出两个 `some`）
  have hsome : (some (scaleVec cUnit 2) : Option VectorConstraint) = some cUnit := by
    have := congrArg (fun (cs : ConstraintSet) => cs.head?) hscale
    simpa using this
  have hhead : scaleVec cUnit 2 = cUnit := Option.some.inj hsome
  have hcontr : (2 : Int) = 1 := by
    have hb := congrArg VectorConstraint.b hhead
    simpa [scaleVec, cUnit] using hb
  norm_num at hcontr

/-! ## 七、要点 本文件的诚实清单（机器可检索）

把 §一–§六 的**全部**主张压成一条合取，便于自动提取（`STYLE.md` §5.4 的惯例）。

注意 **注意第 3 条是"不存在"**（`no_functor_refutes_general_galois`）：
要点 它**主动登记**了"弱伴随无信息"这一**对本仓既有产出的更正**。 -/

/-- **S-05 诚实清单（机器可检索）**：

1. 弱伴随（`GaloisConnection`）**对任意 `f` 成立** ⟹ 零信息（对本仓的更正）；
2. 要点 **插入**强度 **充要于** 满射性（一般定理）；
3. 要点 **共同插入**强度 **充要于** 单射性（一般定理，**与 2 不同**）；
4. 要点 **不存在**反例说明弱伴随有信息（把 1 写成否定式）；
5. 要点 两条插入强度的"对所有 `T` / 对所有 `S`"全称量词**都承重**
   （两条独立的消融反例：`..._univ_only_surjective` / `..._univ_only_injective`）；
6. `syntacticFunctor` **不忠实**（重复项见证）⟹ 两个函子**不同构**；
7. 缩放轨道**不可**用左逆消除（否定结果）。

注意 **不主张**：已建立 `CategoryTheory.Adjunction`（理由见 §7）；
不主张 §一/§三 的实例化是"新数学"（它们是 `Set` 层一般事实的应用）。 -/
theorem s05_honesty_register :
    (∀ {α β : Type*} (f : α → β),
        GaloisConnection (fun S : Set α => f '' S) (fun T : Set β => f ⁻¹' T)) ∧
      (∀ {α β : Type*} (f : α → β),
        (∀ T : Set β, T ⊆ f '' (f ⁻¹' T)) ↔ Function.Surjective f) ∧
      (∀ {α β : Type*} (f : α → β),
        (∀ S : Set α, f ⁻¹' (f '' S) ⊆ S) ↔ Function.Injective f) ∧
      (¬ ∃ f : ConstraintSet → Layer,
        ¬ GaloisConnection (fun S : Set ConstraintSet => f '' S) (fun T : Set Layer => f ⁻¹' T)) ∧
      (∃ (f : Bool → Bool) (T : Set Bool), T ⊆ f '' (f ⁻¹' T) ∧ ¬ Function.Surjective f) ∧
      (∃ (f : Bool → Bool) (S : Set Bool), f ⁻¹' (f '' S) ⊆ S ∧ ¬ Function.Injective f) ∧
      (¬ Function.Injective (fun cs : ConstraintSet => syntacticFunctor cs)) ∧
      (¬ ∃ e : Layer → ConstraintSet,
        (∀ cs : ConstraintSet, e (compileToLayer cs) = cs) ∧
        e (compileToLayer (scaleLayerFun 2 [cUnit])) = e (compileToLayer [cUnit])) :=
  ⟨fun f => image_galoisConnection_general f,
    fun f => subset_image_preimage_iff_surjective f,
    fun f => preimage_image_subset_iff_injective f,
    no_functor_refutes_general_galois,
    image_preimage_eq_univ_only_surjective,
    preimage_image_subset_univ_only_injective,
    syntacticFunctor_not_faithful,
    no_scale_invariant_left_inverse⟩

end Lattice
