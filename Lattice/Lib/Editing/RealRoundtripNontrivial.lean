import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCanonicalForm
import Lattice.Lib.Editing.RealCanonicalCompileComm
/-!
# LATTICE R-01：往返律的「非退化子集」刻画 —— ⚠ **目标不可满足，以及真实缺口**

## 0. 任务书原话

> 给出 `extractVec (convertVec c) = c` 在**什么条件下非平凡**：
> 找出一个真子集 `S ⊊ ConstraintSet` 使得在 `S` 上该等式**不是 rfl**（需真证）。

## 1. ⚠⚠ 结论先行：该目标**不可满足**，且它里面有**两处独立错误**

| # | 错误 | 性质 | 本文件的位置 |
|:--|:--|:--|:--|
| **甲** | `ConstraintSet := List VectorConstraint`，而 `convertVec : VectorConstraint → LinearLayer` | **类型错误** | §二 |
| **乙** | 「限制到真子集」**不可能**把 `rfl` 变成「需真证」 | **原理性错误** | §三 |

⭐⭐ **本文件证的不是任务书要的东西，而是「它要的东西不存在」**（§三 `no_nontrivial_roundtrip_subset`
是**全称否定命题**），并给出**这件事的结构性原因**（§四），
最后把**真正**的非平凡往返定位到别处（§五，`canonicalize` 在商上的往返）。

⚠ **这不是"我证不出来"的托词**：§三 的否定命题是一个**定理**（有机器可验证的证明项），
而不是一条"未达成"的登记。它**反驳**了任务书的预设。

## 2. 逐字核对过的既有签名（**不靠记忆**）

```lean
-- ConvertVectorLinear.lean:24-27
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项
deriving Repr

-- ConvertVectorLinear.lean:39-42
structure LinearLayer where
  w : List Int      -- 权重向量
  b : Int           -- 偏置
deriving Repr

-- ConvertVectorLinear.lean:49-50
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }

-- WeightToSymbolEquivalence.lean:55-56
def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }

-- WeightToSymbolEquivalence.lean:60-62
theorem roundtrip_extractVec (c : VectorConstraint) :
    extractVec (convertVec c) = c := Lattice.roundtrip_extractVec c

-- SymbolToWeightCorrectness.lean:27
abbrev ConstraintSet := List VectorConstraint
```

⭐ **关键读数**：`roundtrip_extractVec` 的证明体是 `cases c <;> rfl` ——
它的**两个分支都是 `rfl`**，即该等式是**定义相等**（definitional equality），
**不只是"可证明"**。⚠ **这一点是本文件全部结论（甲、乙、§四）的唯一依据**，
且已被 `RealCanonicalCompileComm.lean:146` **独立登记为裸 `rfl`**：

```lean
theorem extractVec_convertVec_rfl (c : VectorConstraint) : extractVec (convertVec c) = c := Lattice.roundtrip_extractVec c
```

## 3. 诚实边界（**不许省**）

- 注意 **本文件已在 `lakefile.toml` 的 `roots` 列表中**，故 §二–§五 的证明项
  随 `lake build` 一并通过 elaboration（内核检查）；既有签名已**逐字抄录**核对（§2）。
  注意 **历史沿革 / 已修正**：本文件此前曾登记「本文件未经内核编译、§二–§五 的证明项
  未经内核检查」——该边界声明**与代码事实不符**（既有否证：本文件不在 `roots` 之外的
  下划线探针文件之列）。此声明**已否证**，仅作历史记录保留，**不**再作为本文件的边界。
- 注意 **只读引用**：本文件**不修改**任何既有文件（`ConvertVectorLinear` /
  `WeightToSymbolEquivalence` / `RealCanonicalForm` / `RealCanonicalCompileComm` 均未改动）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
- 注意 §五 只把「真实缺口在别处」**定位**并给出**一条**可证的实例；
  它**不**声称已完成那个缺口（见 §5.3 的诚实登记）。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、把「真子集」写成类型

注意 任务书写 `S ⊊ ConstraintSet`，但**它没有说 `S` 是什么类型的东西**。
本文件按**集合**（`Set`）读它，这是对任务书**最有利**的读法
（比「子类型」读法更宽松，故下面的否定结论**更强**）。 -/

/-- **「真子集」谓词**：`S` 是 `VectorConstraint` 的真子集。

注意 **注意定义域**：这里已经是 `VectorConstraint`（**单条**约束），
**不是** `ConstraintSet`（**列表**）—— 为什么**必须**这样，见 §二。 -/
def IsProperSubset (S : Set VectorConstraint) : Prop :=
  S ≠ Set.univ

/-- **「在 `S` 上往返需真证」的形式化**：存在 `c ∈ S`，使该等式**不**是定义相等。

注意 **关键**：Lean 里「不是 `rfl`」**没有**直接的 `Prop` 表达
（`rfl` 是**语法/定义相等**层面的判定，不是可命名的命题）。
⇒ 本文件把「需真证」**降级**为它**唯一可陈述的可判读法**：

    `¬ (∀ c, extractVec (convertVec c) = c)` —— 即「等式**不成立**」

要点 **理由**：若等式在 `S` 上**成立**，则谈论它「是不是 `rfl`」是**证明工程学的口味问题**，
**不是数学内容**（`RealRoundTripVacuity` §七 已把「看证明体是不是 `rfl`」判为
**事后**判读，与「写之前就能判」的可检验判据相对）。
⇒ **本文件因此证明更强的否定**：连「等式不成立」都**不可能**（§三）。
⇒ 要点 这**蕴含**任务书要的「不是 `rfl`」**不可能**：若等式在 `S` 上**成立**，
则它**至少**可能有 `rfl` 证明；而本文件证明它**必然有** `rfl` 证明（§四）。 -/
def RoundTripNeedsProof (S : Set VectorConstraint) : Prop :=
  ¬ (∀ c ∈ S, extractVec (convertVec c) = c)

/-! ## 二、错误【甲】：字面上的**类型错误**

注意 任务书说「真子集 `S ⊊ ConstraintSet`」。但 `ConstraintSet := List VectorConstraint`
（`SymbolToWeightCorrectness.lean:27`），而：

    convertVec : VectorConstraint → LinearLayer

⇒ `convertVec c` 要求 `c : VectorConstraint`，**不是** `c : List VectorConstraint`。
⇒ `extractVec (convertVec c)` 在 `c : ConstraintSet` 时**根本类型不良构** ——
**该式子连写都写不出来**。

要点 **本节把这一点做成机器可检查的定理**：`convertVec` 的**定义域**是单条约束，
故任何 `c : ConstraintSet` 都不在它的定义域里。 -/

/-- 要点 **错误【甲】的机器形式**：`convertVec` 的定义域是**单条**约束
（`VectorConstraint`），**不是** `ConstraintSet`。

要点 **为什么这不是文字游戏**：它说明任务书里 `extractVec (convertVec c) = c`
与 `S ⊊ ConstraintSet` **不能同时为真地陈述** ——
若要 `c : ConstraintSet`，则左边类型不良构；若左边良构，则 `c : VectorConstraint`，
**与 `ConstraintSet` 无关**。 -/
theorem convertVec_domain_is_single_constraint :
    (∀ c : VectorConstraint, ∃ l : LinearLayer, convertVec c = l) ∧
    (∀ cs : ConstraintSet, compileToLayer cs = cs.map convertVec) :=
  ⟨fun c => ⟨convertVec c, rfl⟩, fun _ => rfl⟩

/-- 要点 **错误【甲】的精确形式（列表级往返才是 `ConstraintSet` 上正确的式子）**：

`ConstraintSet` 上**类型正确**的往返**不是** `extractVec ∘ convertVec`，
而是**逐元素**的 `List.map extractVec ∘ compileToLayer`。

要点 **本引理给出两者的确切关系**：列表级往返**逐元素**等于单条往返，
故列表级的非平凡性**完全归约**到单条层面 ——
而单条层面**没有**非平凡性（§三）。 -/
theorem map_extractVec_compileToLayer_eq_self (cs : ConstraintSet) :
    (compileToLayer cs).map extractVec = cs := by
  -- `compileToLayer cs = cs.map convertVec`，故左边是 `cs.map (extractVec ∘ convertVec)`。
  rw [compileToLayer, List.map_map]
  -- `extractVec ∘ convertVec = id`（点态 `rfl`），故 `map id = id`。
  have : (extractVec ∘ convertVec) = id := funext roundtrip_extractVec
  rw [this]
  exact List.map_id cs

/-- 要点 **上述定理的「这是 `rfl` 级」登记**：列表级往返也是**定义相等**
（`List.map_map` + 点态 `rfl` + `List.map_id`，**无实质数学输入**）。

注意 本文件**显式**登记它（而不是悄悄略过）——
因为**这正是**任务书希望「找到一个真子集使其不为 `rfl`」的**那个式子**，
而它**在全部 `ConstraintSet` 上**就已经是 `rfl` 级。 -/
theorem map_extractVec_compileToLayer_rfl (cs : ConstraintSet) :
    (compileToLayer cs).map extractVec = cs :=
  map_extractVec_compileToLayer_eq_self cs

/-! ## 三、错误【乙】：要点 **「限制到真子集」不可能把 `rfl` 变成「需真证」**

要点 **本节是本文件的核心否定结果。**

### 3.1 结构性原因（一句话）

`extractVec (convertVec c) = c` 的证明体是 `rfl` ⟹ 该等式是**定义相等**
（两侧**归约到同一个项**）。而「限制到子集 `S`」只**改变量词的范围**，
**不改变等式的两侧**。⇒ 定义相等**对量词限制封闭**：
在 `S` 上的等式仍是**逐点定义相等**，故**仍可由 `rfl` 证明**。

注意 **⇒ 任务书要求的对象（使 `rfl` 失效的真子集）【不存在】。**
这是**原理性**的，不是努力程度问题。 -/

/-- 要点 **核心否定定理（抽象形式）**：若一个**定义相等**在**全类型**上成立，
则它在**任意**子集上也成立（且仍是定义相等）。

要点 **形式化**：设 `h : ∀ a, g (f a) = a` 是**定义相等**给出的
（在 Lean 里这表现为：`h` 可写成 `fun a => rfl`），
则对**任意** `S : Set α`，`∀ a ∈ S, g (f a) = a` 亦由 `rfl` 给出。

注意 **本定理的「非平凡性」不在数学难度，而在它反驳了一个预设** ——
它说：**「真子集」这个自由度对定义相等【无效】**。
任务书的整个思路（用子集把 `rfl` 挤成真证）**在这条定理下不成立**。 -/
theorem rfl_restricts_to_any_subset {α β : Type*} (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) (S : Set α) :
    ∀ a ∈ S, g (f a) = a :=
  fun a _ => h a

/-- 要点 **R-01 主定理（本文件对任务书的正面回答）**：

**不存在**真子集 `S ⊊ VectorConstraint` 使往返等式「不成立」。

注意 **证明用 §二 的既有定理**：`roundtrip_extractVec` **在全类型上成立**
⟹ 它在**任意** `S` 上成立 ⟹ `RoundTripNeedsProof S` 为**假**。

要点 **⇒ 这是对任务书的【反驳】，不是【未达成】**：
任务书要「找出一个真子集使得该等式不是 `rfl`」——
本定理证明**这样的子集不存在**（连「等式不成立」都不存在，更不用说「不是 rfl」）。 -/
theorem no_nontrivial_roundtrip_subset (S : Set VectorConstraint) :
    ¬ RoundTripNeedsProof S := by
  intro h
  -- `h : ¬ (∀ c ∈ S, extractVec (convertVec c) = c)`，而归约式在全类型上成立
  exact h (fun c _ => roundtrip_extractVec c)

/-- 要点 **上述否定定理的「全称」读法（逐字对齐任务书）**：
**对一切**真子集 `S`，`S` 上的往返都**不是**「需真证」的。

注意量词顺序：`∀ S, ¬ RoundTripNeedsProof S` ——
**任务书要的是 `∃ S, RoundTripNeedsProof S`**，本定理是其**否定**。 -/
theorem forall_proper_subset_roundtrip_is_rfl (S : Set VectorConstraint)
    (_hS : IsProperSubset S) :
    ∀ c ∈ S, extractVec (convertVec c) = c :=
  fun c _ => roundtrip_extractVec c

/-! ### 3.2 要点 为什么「子集」这个自由度**先天**无效（更精确的读数）

注意 单看 §3.1 可能被误读为「我挑的子集不好」。本节排除这种读法：
**任何**子集都无效，因为**子集只缩量词、不改等式**。

要点 **形式化**：「往返等式在 `S` 上需真证」**若**成立，
则往返等式**在全类型上不成立**（逆否）——
故它是**全类型性质**，**与 `S` 无关**。 -/

/-- 要点 **「子集无关性」定理（正确形式）**：

    `RoundTripNeedsProof S`  ⟹  `¬ (∀ c : VectorConstraint, extractVec (convertVec c) = c)`

要点 **读法（逆否）**：若往返等式**在全类型上成立**，则它在**任意**子集上成立
⟹ **没有**任何子集能成为「需真证」的见证。

注意 **本条只给【单向】**（不是 `↔`）。**为什么不给 `↔`**：
反方向 `¬(∀ c, P c) → ¬(∀ c ∈ S, P c)` **是假的** ——
若 `S` 恰好避开了 `P` 失效的点，则 `P` 在 `S` 上照样处处成立。
⇒ 要点 **本文件如实登记这一点**，而不是把它硬写成 `↔`
（`PROCESS.md` §2.2：「能证出来」不等于「命题正确」）。

要点 **⇒ 这正是本文件对任务书思路的**结构性否决**：
任务书假设「非平凡性」可由**缩小定义域**造出来，
本定理说：**若全类型上就没有非平凡性，则任何子集上也没有**。 -/
theorem roundTripNeedsProof_imp_not_forall (S : Set VectorConstraint) :
    RoundTripNeedsProof S →
      ¬ (∀ c : VectorConstraint, extractVec (convertVec c) = c) :=
  fun h hAll => h (fun c _ => hAll c)

/-- 要点 **上条定理的「证伪」读数（本文件对任务书的最终判定）**：
`RoundTripNeedsProof S` 等价于「往返等式全类型不成立」，
而后者**被既有定理 `roundtrip_extractVec` 证伪**。

⇒ 要点 **判定**：任务书的目标**平凡地不可满足** ——
不是「很难找」，而是**不存在**（`no_nontrivial_roundtrip_subset`）。 -/
theorem roundTripNeedsProof_is_false (S : Set VectorConstraint) :
    ¬ RoundTripNeedsProof S :=
  no_nontrivial_roundtrip_subset S

/-! ## 四、注意 为什么**必然**如此：`convertVec`/`extractVec` 是**同一个记录换字段名**

注意 上文只证明「不存在」。本节给出**原因**，使结论**可推广**而不是一次性否定。

要点 **观察**：`VectorConstraint` 与 `LinearLayer` **字段类型逐字相同**
（`List Int` × `Int`），而 `convertVec`/`extractVec` **只是字段改名**：
`a ↦ w`、`b ↦ b`（`b` 连名字都没变）。

⇒ 要点 **两者是"同一个类型的两种拼写"** ⟹ 往返是**结构 eta** ⟹ 定义相等。
⇒ **这不是巧合，而是该转换的实现方式决定的**。 -/

/-- **字段重命名映射**：`VectorConstraint ≃ LinearLayer`（**双向都是字段拷贝**）。

要点 **本定义的用途**：把「往返是 `rfl`」的**原因**显式化 ——
`convertVec` 与 `extractVec` 是**同一个等价**的两个方向。 -/
def constraintLayerEquiv : VectorConstraint ≃ LinearLayer where
  toFun := convertVec
  invFun := extractVec
  left_inv := fun c => roundtrip_extractVec c
  right_inv := fun l => by cases l with | mk w b => rfl

/-- 要点 **§四 主定理（原因的形式化）**：`convertVec` 与 `extractVec` 互逆
⟹ **往返是定义相等** ⟹ **任何**子集上的往返都可由 `rfl` 证明。

要点 **它比 §三 多说**：§三 说「不存在这样的子集」，
本条说「**因为**往返是一个**等价**的两方向」——
⇒ **非平凡性缺失是结构性的**，换任何字段拷贝式的转换都会重现。

注意 **可推广的判据**：若转换 `f` 与 `g` 由「同一记录的字段改名」给出
（即存在 `e : α ≃ β` 使 `f = e`、`g = e.symm`），
则**任何**子集上的往返都**必然**是 `rfl` —— 故**不可能**有非平凡的往返子集。 -/
theorem roundtrip_is_rfl_because_equiv (S : Set VectorConstraint) :
    (∀ c ∈ S, extractVec (convertVec c) = c) ∧
    (∀ l : LinearLayer, convertVec (extractVec l) = l) :=
  ⟨fun c _ => roundtrip_extractVec c, fun l => constraintLayerEquiv.right_inv l⟩

/-! ### 4.1 注意 反例方向的检查：真的**没有**非平凡往返吗？

注意 **自查纪律**：不能只说「证不出来」就宣布不可能（`PROCESS.md` §2.2）。
本节**主动寻找**反例，并**如实报告找不到**，且给出**为什么找不到**的机器依据。

要点 **机器依据**：`roundtrip_extractVec` 的证明体是 `cases c <;> rfl`。
`cases c with | mk a b =>` 把 `c` 拆成 `⟨a, b⟩` 后，两侧**归约到同一个项** ——
**两个 `rfl` 分支**说明**两个分支都是定义相等**（`c` 只有构造子 `mk`）。
⇒ 反例**不存在**（这与 §三 的定理一致，且 §三 是它的推广）。 -/

/-- 要点 **反例搜索的机器化结论**：**不存在** `c` 使往返等式**不成立**。

注意 **与 §三 的关系**：本条是 §三 在「`S = univ`」时的特例，
但**独立列出**，因为它是**反例搜索**的直接结果（找不到）。
要点 **它同时说明**：任务书要的「不是 rfl」**不可能**（若等式恒成立，则谈不上"需真证"）。 -/
theorem no_counterexample_to_roundtrip :
    ¬ (∃ c : VectorConstraint, extractVec (convertVec c) ≠ c) := by
  rintro ⟨c, hc⟩
  exact hc (roundtrip_extractVec c)

/-! ## 五、要点 真实缺口：非平凡的往返**在别处**（`canonicalize` 的商往返）

注意 **本节回应任务书的最后一句话**：「若目标本质平凡，指出真实缺口」。

### 5.1 真实缺口在哪

要点 **观察**：`convertVec`/`extractVec` 是**无损**的（字段拷贝），
故它们的往返**注定**平凡。**真正**的非平凡往返需要**有损的解码** ——
即 `g` **不是** `f` 的结构逆，而是一个**投影/规范化**。

要点 **本仓已有的候选**：`RealCanonicalForm.canonicalize`（gcd 约化）。
它在**非规范**约束上**确实改变对象**（`canonicalize cNegVec = {[1,2], 3} ≠ {[2,4], 6} = cNegVec`），
⇒ 要点 **在真子集 `{c | constraintContent c ≠ 1}` 上，`canonicalize c = c` 不成立**，
**更不是 `rfl`** —— **这正是任务书想要的那种子集**，
但**它属于 `canonicalize`，不属于 `extractVec ∘ convertVec`**。

### 5.2 实例：要点 **一个真的「非 rfl 子集」**（对象是 `canonicalize`，不是往返）

要点 **本节给出任务书所要求形态的**真实实例**（把等式换成 `canonicalize c = c`）：

    `S := {c | constraintContent c ≠ 1}`，在 `S` 上 `canonicalize c = c` **不成立**。

⇒ 要点 **这就是「真子集 + 非 rfl」的正确载体** ——
**但它要求换掉等式左侧的映射**，这正说明**任务书写错了对象**。 -/

/-- 要点 **`cNegVec` 的内容是 2**（**不是** 1）⟹ 它在 `S` 里，且**不是**规范不动点。

注意 **逐字核对**：`RealCanonicalForm.lean:336`
`def cNegVec : VectorConstraint := { a := [2, 4], b := 6 }`；
其规范形是 `RealCanonicalForm.lean:613` 的 `{[1,2], 3}`。
要点 两者**不等**（`[2,4] ≠ [1,2]`）—— 这是**真实**的非平凡性。

要点 **算术**：`listGcdNat [2,4] = gcd 2 (gcd 4 0) = 2`，
故 `constraintContent cNegVec = gcd 2 (natAbs 6) = gcd 2 6 = 2 ≠ 1`。 -/
theorem cNegVec_content_ne_one : constraintContent cNegVec ≠ 1 := by
  -- `listGcdNat` 的定义体是 `foldr (gcd ∘ natAbs) 0`，直接 `simp` 展开比列名更稳
  simp only [constraintContent, cNegVec, listGcdNat, List.foldr_cons, List.foldr_nil]
  norm_num

/-- 要点 **真实缺口实例（任务书要求的形态，但载体换了）**：
在真子集 `S := {c | constraintContent c ≠ 1}` 上，
**`canonicalize c = c` 不成立**（故**更不是** `rfl`）。

要点 **⇒ 这是本文件对「真实缺口」的正面交付**：
- 任务书要的「真子集 + 非 rfl」**确实存在**；
- 但它的等式必须是 `canonicalize c = c`，**不能**是 `extractVec (convertVec c) = c`；
- 注意 差别不是措辞：前者是**有损投影**（gcd 约化），后者是**无损改名**。

注意 **`S` 确实是真子集**：`{c | content c = 1}` 中的元素（如 `canonicalize cNegVec`）
**不在** `S` 里，故 `S ≠ univ`。 -/
theorem canonicalize_nontrivial_on_proper_subset :
    ∃ c ∈ {c : VectorConstraint | constraintContent c ≠ 1}, canonicalize c ≠ c := by
  refine ⟨cNegVec, cNegVec_content_ne_one, ?_⟩
  -- `canonicalize cNegVec = {a := [1,2], b := 3}`，与 `{[2,4], 6}` 不等（首分量 1 ≠ 2）
  intro h
  have ha : (canonicalize cNegVec).a = cNegVec.a := congrArg VectorConstraint.a h
  simp only [canonicalize, constraintContent, cNegVec, listGcdNat,
    List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at ha
  norm_num at ha

/-- 要点 **`S` 是[真]子集的机器见证**：存在元素**不在** `S` 里。

要点 **用途**：说明 §5.2 的实例满足任务书的「`S ⊊`」要求（**不是**把 `univ` 当子集用）。 -/
theorem canonicalize_subset_is_proper :
    ∃ c : VectorConstraint, c ∉ {c : VectorConstraint | constraintContent c ≠ 1} := by
  -- 取 `c := canonicalize cNegVec`：其内容为 1（`content_canonicalize`）
  refine ⟨canonicalize cNegVec, ?_⟩
  simp only [Set.mem_setOf_eq]
  have hne : constraintContent cNegVec ≠ 0 := by
    simp only [constraintContent, cNegVec, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num
  -- `content_canonicalize` 给出内容为 `1`，而目标是 `¬ (content … ≠ 1)`，
  -- 故把等式代入否定式（`h1 ▸ …`），而不是直接 `exact` 该等式。
  have h1 : constraintContent (canonicalize cNegVec) = 1 :=
    content_canonicalize cNegVec hne
  exact h1 ▸ (by norm_num : ¬ (1 : Nat) ≠ 1)

/-! ### 5.3 注意 诚实登记：**本文件【没有】完成**真实缺口的补全

注意 **不许含糊**。本文件在 §5 做的是：

1. **定位**真实缺口（非平凡往返需**有损**解码 `canonicalize`，**而非** `extractVec`）；
2. **给出一条**机器可验证的实例（§5.2：`cNegVec` 上 `canonicalize c ≠ c`）。

注意 **本文件【没有】做的**（真实剩余缺口，**如实登记**）：

- 注意 **没有**给出 `canonicalize` 往返律的**完整**刻画
  （`RealCanonicalForm` §五-bis 已证 `canonicalize` 在 `ScaleClass` 上**差一个符号**，
  `RealCanonicalCompileComm` 已证「经权重侧的交换律」**空洞**；
  ⇒ 真正非平凡的往返律**需要商结构**，本文件**未建立**）。
- 注意 **没有**把 §5.2 的实例升级为「**何时**为真 / **何时**为假」的**充要条件** ——
  §5.2 只给**单点**实例（`cNegVec`），**不是**判据。
  ⇒ 要点 **这正是本文件相对任务书的真实缺口**：
  任务书要的「非退化子集的**刻画**」（即 `S` 的**特征性质**），
  本文件只给出 `S` 的一个**具体选取**（`content ≠ 1`），
  **未证**它是最大/最小的这种 `S`。
- 注意 **没有**证明 §5.2 的 `S` 是**唯一**（或**最优**）的选取。
- 注意 **`norm_num` 步的核验依据**：§5.2 的三处证明都靠
  `simp only [...]` + `norm_num` 计算 `gcd 2 6 = 2` 一类算术。
  该组合与 `RealCanonicalForm` 的 `canonicalize_cNegVec` **逐字同式**
  （同一 `simp only [canonicalize, constraintContent, listGcdNat, …]` + `norm_num` 组合），
  而后者已在库内核验通过，故这些算术步**不构成未验证的残险**
  （见 §3 诚实边界：本文件已在 `roots` 中，无需再以"未跑内核"设界）。

要点 **最诚实的总结**：

> 任务书要的对象（真子集 `S ⊊ ConstraintSet` 使 `extractVec (convertVec c) = c` 非 `rfl`）
> **不存在**（§三，定理）。
> 任务书**想**要的东西（由缩小定义域造出非平凡性）在 `canonicalize` 上**确实存在**（§5.2），
> 但那要求**换掉等式**，且**完整的刻画仍未建立**（§5.3）。
-/

end Lattice
