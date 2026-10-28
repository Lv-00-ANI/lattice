import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
/-!
# LATTICE R-03：往返的「单射性障碍」 —— ⚠ **目标前提为假，以及真实缺口**

## 0. 任务书原话

> 证明 `extractVec` 不是单射（同一符号可由多个权重得到），并给出**纤维的精确刻画**。

## 1. ⚠⚠ 结论先行：任务书的**前提本身是假的**

`extractVec` **是**单射。⭐ 本文件给出**机器可验证的反驳**（§三 `extractVec_injective`），
并给出任务书真正想要的**精确刻画**（§四）—— 但它的内容是
**「纤维恒为单点」**，即**与任务书的预期相反**。

⚠ **这不是「我证不出来」**：§三是一条**定理**（有证明项），
它**反驳**了任务书的预设，而不是把它登记为"未达成"。

## 2. 逐字核对过的既有签名（**不靠记忆**）

```lean
-- ConvertVectorLinear.lean:24-27
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项

-- ConvertVectorLinear.lean:39-42
structure LinearLayer where
  w : List Int      -- 权重向量
  b : Int           -- 偏置

-- ConvertVectorLinear.lean:49-50
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }

-- WeightToSymbolEquivalence.lean:55-56
def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }

-- WeightToSymbolEquivalence.lean:60-62
theorem roundtrip_extractVec (c : VectorConstraint) :
    extractVec (convertVec c) = c := by cases c <;> rfl
```

⭐ **关键读数**：`VectorConstraint` 与 `LinearLayer` **都恰好只有两个字段**，
且字段类型**逐字相同**（`List Int`、`Int`）。`extractVec` 只是把
`w ↦ a`、`b ↦ b`（`b` 连名字都没变）。

⇒ ⭐ **`extractVec` 是结构同构的一个方向** ⟹ 它**必然是单射**。
任务书说它「不是单射」—— **这与定义直接矛盾**。

## 3. ⚠ 「同一符号可由多个权重得到」：正确的落点是**语义层**，不是对象层

任务书用一句「同一符号可由多个权重得到」表达直觉。该直觉**有真内容**，
但它说的**不是** `extractVec` 的单射性，而是：

> **把权重按「它表示的函数」而非「它的字段」分类时**，
> 一个函数**确实**有多个权重实现（缩放自由度）。

⭐ 本文件在 §五把这件事**独立地**证出来（`semantic_not_injective`），
载体是**语义映射** `fun l => ∀ x, LayerOut l x = 0`，而**不是** `extractVec`。
⚠ 两者的区别不是措辞：前者是**有损投影**，后者是**无损改名**（§六）。

## 4. 诚实边界（详列于 §七）

无 `sorry` / `axiom` / `admit` / `native_decide`；**只读**引用既有模块，**不修改**任何既有文件。
⚠ **未验证编译**（任务书严禁 `lake` / `lake build` / `lake env lean` / `scripts\probe.ps1`）。
-/

namespace Lattice.Lib.Editing.RealExtractNonInjective
/-! ## 一、纤维（fiber）的形式化

⚠ 任务书要「纤维的**精确刻画**」，但**没有给纤维的定义**。
本文件按标准数学读法取之：`f` 在 `y` 处的纤维是 `f ⁻¹' {y}`。 -/

/-- **纤维**：`f` 在 `y` 处的原像（=`f ⁻¹' {y}`）。

⚠ 本定义**只**用 `Set`，不引入新结构，故下面的刻画定理可用最少的集合引理证明。 -/
def fiber {α β : Type*} (f : α → β) (y : β) : Set α :=
  {x | f x = y}

/-- **纤维的成员判定**（`fiber` 的 `simp` 引理；**逐字**展开定义即得）。 -/
@[simp] theorem mem_fiber {α β : Type*} (f : α → β) (y : β) (x : α) :
    x ∈ fiber f y ↔ f x = y :=
  Iff.rfl

/-! ## 二、⭐ 障碍的**真实**来源：字段个数

⚠ 在证「`extractVec` 是单射」之前，先说明**为什么必然如此**，
使结论**可推广**（而不只是一次性的事实）。

⭐ 观察：`LinearLayer` 的**唯一**构造子是 `mk w b`
（`ConvertVectorLinear.lean:39-42`，**只有 `w`、`b` 两个字段**）。
⇒ 两个层相等 ⟹ 逐字段相等 ⟹ 其 `a`、`b` 投影相等 ⟹ 对应的约束相等。

⚠ **这正是任务书预期失效的原因**：要制造「同一符号多个权重」，
需要在 `LinearLayer` 里**额外**塞入 `extractVec` 读不到的字段（如 `scale`、`rank`）。
⚠ **本仓的 `LinearLayer` 没有这样的字段** —— 故该现象在**本层**不存在（§六讨论怎么改才会存在）。 -/

/-! ## 三、⭐⭐ 主结果：`extractVec` **是**单射（对任务书的反驳）

⭐ **本节是本文件对任务书的正面回答**，且答案是**否定**的。 -/

/-- ⭐⭐ **R-03 主定理（反驳任务书）**：`extractVec : LinearLayer → VectorConstraint`
**是单射**。

⚠ **证明**：`LinearLayer` 只有构造子 `mk w b`。设 `l`、`l'` 有
`extractVec l = extractVec l'`。对二者展开记录，该等式分别给出
`l.w = l'.w` 与 `l.b = l'.b`（`extractVec` 的两个字段正是 `w`、`b`），
逐字段相等即层次相等。

⭐⭐ **⇒ 任务书要证的命题（`extractVec` 不是单射）为【假】**。
本定理是它的**否定**，故它是对任务书的**反驳**，不是「未达成」。

⚠ **本定理不依赖任何 mathlib 引理**（只用 `cases` 展开记录 + 定义化简），
故其正确性不依赖我对 mathlib 命名的记忆。 -/
theorem extractVec_injective : Function.Injective extractVec := by
  intro l l' h
  cases l with
  | mk w b =>
    cases l' with
    | mk w' b' =>
      -- `h : extractVec ⟨w,b⟩ = extractVec ⟨w',b'⟩`，展开 `extractVec` 后逐分量取
      simp only [extractVec, VectorConstraint.mk.injEq] at h
      rw [h.1, h.2]

/-- ⭐ **`convertVec` 也是单射**（编译方向的对应事实，本文件内导出）。

⚠ **为何需要它**：`extractVec_injective` 只对 `extractVec` 给出单射；
而 §五 的两个「不同」子目标手里拿到的是 `convertVec r03C = convertVec (scaleVec r03C 2)`，
即用以从 `convertVec` 的相等反推 `r03C = scaleVec r03C 2` 再交给 `scaleVec_ne_self_two` 反驳。

⭐ **证明**：`convertVec` 在**编译像**上与 `extractVec` 互逆
（`roundtrip_extractVec c : extractVec (convertVec c) = c`）。
设 `convertVec c = convertVec c'`，两边同时 `extractVec` 并用往返恒等即得 `c = c'`。

⚠ 本引理**只用既有模块的往返定理**，不引入任何新假设。 -/
theorem convertVec_injective : Function.Injective convertVec := by
  intro c c' h
  -- 两边同时取 `extractVec`：`extractVec (convertVec c) = extractVec (convertVec c')`
  have h' : extractVec (convertVec c) = extractVec (convertVec c') := congrArg extractVec h
  -- 再用往返恒等把两侧分别化成 `c`、`c'`
  rwa [roundtrip_extractVec c, roundtrip_extractVec c'] at h'

/-- ⭐ **主定理的「纤维」读法**：`extractVec` 的**每条纤维至多一个元素**
（任意 `c` 的纤维至多是单点集）。

⭐ **这是任务书要的「纤维刻画」的【真答案】** ——
但它的内容是「纤维不爆炸」，**与任务书预期的「纤维 >1」相反**。 -/
theorem fiber_extractVec_subsingleton (c : VectorConstraint) :
    ∀ l ∈ fiber extractVec c, ∀ l' ∈ fiber extractVec c, l = l' := by
  intro l hl l' hl'
  simp only [mem_fiber] at hl hl'
  exact extractVec_injective (hl.trans hl'.symm)

/-- ⭐ **`extractVec` 不是「非单射」的机器化形式**（反例**不存在**）：

不存在两个**不同**的层，使 `extractVec` 把它们送到**同一个**约束。

⚠ **这是对任务书「同一符号可由多个权重得到」在【对象层】的直接证伪**：
在 `extractVec` 这一支上，**没有**这样的两个层。 -/
theorem no_fiber_of_extractVec_has_two_points :
    ¬ (∃ l l' : LinearLayer, l ≠ l' ∧ extractVec l = extractVec l') := by
  rintro ⟨l, l', hne, heq⟩
  exact hne (extractVec_injective heq)

/-! ## 四、⭐ 纤维的**精确刻画**（任务书的第二问，正面回答）

⚠ 任务书要「纤维的**精确**刻画」。⭐ 上一节只给了「至多一个元素」（上界），
**不是**精确刻画 —— 精确刻画必须给出纤维**恰是什么集合**。

⭐ **精确答案**：`extractVec` 在 `c` 处的纤维**恰好**是单点集 `{convertVec c}`。
⇒ 这**同时**给出「非空」（`convertVec c` **就在**纤维里）与「至多一个」（§三）。
⚠ 二者合起来才是「精确」。 -/

/-- ⭐ **纤维的非空性**：`convertVec c` **落入** `extractVec` 在 `c` 处的纤维。

⚠ **依据**：`roundtrip_extractVec`（`WeightToSymbolEquivalence.lean:60`）。 -/
theorem convertVec_mem_fiber (c : VectorConstraint) :
    convertVec c ∈ fiber extractVec c :=
  roundtrip_extractVec c

/-- ⭐⭐ **纤维的精确刻画（R-03 第二问的正面答案）**：

    `fiber extractVec c = {convertVec c}`

⭐⭐ **本定理是「精确」的**：它**同时**蕴含
- **非空**：`convertVec c ∈ fiber extractVec c`（右边含一个元素，故左边非空）；
- **单点（不爆炸）**：纤维里没有第二个元素（§三 的上界）。

⚠⚠ **⇒ 任务书问的「多个权重得到同一符号」在 `extractVec` 上【不存在】**：
它的纤维恒为**恰好一个**元素。

⚠ **证明**：用 `Set.ext` 双向。`⊆` 方向用 §三 的单射性；
`⊇` 方向用 `convertVec_mem_fiber`（即 `roundtrip_extractVec`）。
⚠ **不依赖 `Set.eq_singleton_iff_unique_mem`** 等 mathlib 命名 ——
本文件按 `⊆`/`⊇` 手工展开，以规避命名记忆风险。 -/
theorem fiber_extractVec_eq_singleton (c : VectorConstraint) :
    fiber extractVec c = {convertVec c} := by
  ext l
  simp only [mem_fiber, Set.mem_singleton_iff]
  constructor
  · -- `extractVec l = c ⟹ l = convertVec c`：由单射性 + 往返
    intro hl
    exact extractVec_injective (hl.trans (roundtrip_extractVec c).symm)
  · -- `l = convertVec c ⟹ extractVec l = c`：往返恒等
    intro hl
    rw [hl]
    exact roundtrip_extractVec c

/-- ⭐ **精确刻画的存在性-唯一性读法**（把 §四 主定理写成任务书「多个权重」的**反面**）：

「`extractVec` 在 `c` 处的纤维中，**存在**元素，且该元素**唯一**」。

⚠ **这是「精确刻画」最贴近任务书措辞的形式**：
任务书期待「纤维有多个元素」；本定理说**恰好一个**。 -/
theorem fiber_extractVec_exists_unique (c : VectorConstraint) :
    ∃! l : LinearLayer, extractVec l = c :=
  ⟨convertVec c, roundtrip_extractVec c,
    fun _ hl' => extractVec_injective (hl'.trans (roundtrip_extractVec c).symm)⟩


/-- ⭐ **纤维势的精确断言**：`extractVec` 的每条纤维都是**单点集**
（在 `Set` 层：纤维等于某个单点集）。

⚠ 与 §三 的 `fiber_extractVec_subsingleton` 的区别：§三 只说「至多一个」，
本条说「**恰好**一个」—— 后者才是**精确**刻画。 -/
theorem fiber_extractVec_is_singleton (c : VectorConstraint) :
    ∃ l : LinearLayer, fiber extractVec c = {l} :=
  ⟨convertVec c, fiber_extractVec_eq_singleton c⟩

/-! ## 五、⭐⭐ 任务书**真正想说的**：语义层的非单射（真实缺口，正面交付）

⚠ 本文件到此为止都是**否定**结果。本节转为**正面**：
把任务书那句「同一符号可由多个权重得到」的**直觉**落到它**唯一成立**的地方。

### 5.1 落点：不是 `extractVec`，而是「按语义分类」

⭐ **语义映射**：把层 `l` 送到它**所表示函数的零化谓词**
`fun x => LayerOut l x = 0`。
⚠ 这个映射**丢掉**了「用哪个符号写」的信息，只保留**行为**。

⭐ **本仓已有的机器见证**（`ConvertVectorLinear.lean`）：
- `scaleVec`（:69-70）：把约束整体乘以 `lam`；
- `scaleVec_preserves`（:105）：`lam ≠ 0` 时**满足集不变**。
⇒ ⭐ `revC` 与 `scaleVec revC 2` 是**两个不同的权重**，却表示**同一个函数**。 -/

/-- ⭐ **见证约束**：`x₀ + 1 = 0`，即 `a = [1]`、`b = 1`。
⚠ **本定义与 `RealReversibilityBoundary.revC` 逐字相同**，但**本文件不 import 该模块**
（避免为一条见证引入整个 ℝ 侧依赖链）；故在此**重新定义**，并如实标注它与该处的重复。 -/
def r03C : VectorConstraint := { a := [1], b := 1 }

/-- ⭐ **两个权重确实【不同】**：`scaleVec r03C 2 ≠ r03C`
（`b` 字段是 `1 * 2 = 2`，而 `r03C.b = 1`）。

⚠ **证明**：`congrArg VectorConstraint.b` 取投影，把结构等式化为整数等式 `2 = 1`。 -/
theorem scaleVec_ne_self_two : scaleVec r03C 2 ≠ r03C := by
  intro h
  have hb : r03C.b * 2 = r03C.b := by
    have := congrArg VectorConstraint.b h
    simpa [scaleVec] using this
  -- `r03C.b = 1`，故 `hb : 1 * 2 = 1`，即 `2 = 1` —— 由 `norm_num` 消解
  simp only [r03C] at hb
  norm_num at hb

/-- ⭐ **语义映射**：层 `l` ↦ 它所表示函数的**零化谓词**。

⚠ **这是本文件 §五 的核心定义**：它把「权重表示的**函数**」形式化为
`List Int → Prop`。**任务书的直觉正是关于这个映射的**，而不是关于 `extractVec` 的。 -/
def LayerSemantics (l : LinearLayer) : List Int → Prop :=
  fun x => LayerOut l x = 0

/-- ⭐⭐ **语义映射【不是】单射**（机器验证的存在性反例）：

存在两个**不同**的层 `w ≠ w'`，它们表示**同一个函数**
（`LayerSemantics w = LayerSemantics w'`，作为函数**逐点相等**）。

⭐⭐ **⇒ 这就是任务书那句话的【正确落点】**：`extractVec` 是单射（§三），
但**语义映射不是** —— 「同一函数多个权重实现」**确实存在**，
只是它发生在**语义层**，**不在 `extractVec` 这一支上**。

⚠ **证明**：取 `w := convertVec r03C`、`w' := convertVec (scaleVec r03C 2)`。
- **不同**：由 `scaleVec_ne_self_two` + `convertVec` 的单射性（用 §四 的往返）。
- **同函数**：`convertVec_preserves_semantics`（:55）把两边都化到
  `VectorConstraintSat`，再用 `scaleVec_preserves`（:105，`lam = 2 ≠ 0`）。
⚠ 本证明**用到两个既有模块的非平凡内容**：`ConvertVectorLinear` 的
`convertVec_preserves_semantics` + `scaleVec_preserves`（后者经 `dot_map_mul` 线性引理）。 -/
theorem semantic_not_injective :
    ∃ w w' : LinearLayer, w ≠ w' ∧ LayerSemantics w = LayerSemantics w' := by
  refine ⟨convertVec r03C, convertVec (scaleVec r03C 2), ?_, ?_⟩
  · -- 两个权重不同：若相等，则经 `convertVec` 的单射 + `roundtrip_extractVec` 拉回得
    -- `r03C = scaleVec r03C 2`，与 `scaleVec_ne_self_two` 矛盾
    intro h
    exact scaleVec_ne_self_two (convertVec_injective h).symm
  · -- 两者表示同一个函数：`funext` 后逐点把两边都化到 `VectorConstraintSat`
    funext x
    -- 目标此刻是 `(LayerOut (convertVec r03C) x = 0) = (LayerOut (convertVec (scaleVec r03C 2)) x = 0)`
    -- —— 一个 `Prop` 之间的等式；用 `propext` 化为 `↔` 再逐段桥接
    apply propext
    exact (convertVec_preserves_semantics r03C x).trans
      ((scaleVec_preserves r03C x 2 (by norm_num)).trans
        (convertVec_preserves_semantics (scaleVec r03C 2) x).symm)

/-- ⭐ **语义层非单射的「纤维」读法**（把 §五 主定理译成任务书的纤维语言）：

`LayerSemantics` 在**函数** `LayerSemantics (convertVec r03C)` 处的纤维
**至少有两个不同元素**（`convertVec r03C` 与 `convertVec (scaleVec r03C 2)`）。

⭐⭐ **⇒ 对照 §四**：`extractVec` 的纤维**恒为单点**（§四），
而 `LayerSemantics` 的纤维**可以有两个以上元素**（本条）。
⚠ **这一对照正是「为什么任务书指错了对象」的机器化说明**。 -/
theorem semantic_fiber_has_two_points :
    ∃ w : LinearLayer, w ∈ fiber LayerSemantics (LayerSemantics (convertVec r03C)) ∧
      ∃ w' : LinearLayer, w' ∈ fiber LayerSemantics (LayerSemantics (convertVec r03C))
        ∧ w ≠ w' := by
  refine ⟨convertVec r03C, ?_, convertVec (scaleVec r03C 2), ?_, ?_⟩
  · -- `convertVec r03C` 落在自己的语义处：定义上相等
    simp only [mem_fiber]
  · -- `convertVec (scaleVec r03C 2)` 的语义与之**函数相等**（逐点桥接，非 `rfl`）
    simp only [mem_fiber]
    funext x
    apply propext
    -- ⚠ `LayerSemantics` 是**不透明** `def`（STYLE.md:834）⟹ 先用 `simp only [LayerSemantics]`
    -- 把目标展开成 `LayerOut … = 0`，才能与 `convertVec_preserves_semantics` 的结论匹配。
    -- ⚠ 此处目标方向是 `w' ↔ w`（与 `semantic_not_injective` 的 `w ↔ w'` **相反**），
    -- 故桥接的**项序也随之反向**并以 `.symm` 收尾。
    simp only [LayerSemantics]
    exact (convertVec_preserves_semantics (scaleVec r03C 2) x).trans
      ((scaleVec_preserves r03C x 2 (by norm_num)).symm.trans
        (convertVec_preserves_semantics r03C x).symm)
  · -- 两者不同：由 `scaleVec_ne_self_two` 经 `convertVec` 的单射拉回（与 `semantic_not_injective` 同型）
    intro h
    exact scaleVec_ne_self_two (convertVec_injective h).symm

/-! ### 5.2 ⚠ 诚实登记：§五 的局限

⚠ **不许含糊**。§五 做到的是：

1. **证明**语义映射**非单射**（`semantic_not_injective`，机器验证）；
2. **定位**任务书直觉的**正确载体**（语义层，非 `extractVec`）。

⚠ **§五 【没有】做到的**（如实登记）：
- ⚠ `semantic_not_injective` 的见证是**存在性**的，**不是**「纤维的精确刻画」
  （即：**未**给出「哪些函数有几个权重实现」的充要条件）；
- ⚠ `semantic_fiber_has_two_points` 只给**≥2**，**未**给出上界
  （「无穷多实现」需 `Int` 的无限性论证，**本文件未做**）；
- ⚠ §五 的语义映射取的是「**零化谓词**」这一特定编码；
  ⚠ **另一个**自然选择是「解集 `{x | VectorConstraintSat c x}`」。
  ⭐ 二者在本模型下**等价**（由 `convertVec_preserves_semantics`），
  但**本文件未把这一等价性证成定理**（**未做的部分**）。 -/

/-! ## 六、⚠ 结构性诊断：怎样才能真的造出「单射性障碍」

⚠ 上文说「`extractVec` 是单射」。本节说明**为什么**，以及**改什么**才会不成立 ——
使结论**可推广**，而不是一次性的。

⭐ **充分条件**：若把 `LinearLayer` 改为携带**额外字段** `extra`，
而 `extractVec` **不读**该字段（如 `extractVec l := {a := l.w, b := l.b}` 忽略 `l.extra`），
则**立刻**得到非单射的 `extractVec`：两个只差 `extra` 的层映到同一约束。

⚠ **本仓现状**：`LinearLayer` **恰好只有** `w`、`b`（`ConvertVectorLinear.lean:39-42`），
**没有** `extractVec` 读不到的字段 ⇒ **该机制在本层【不适用】**。

⭐⭐ **⇒ 这是对任务书的最终判定**：
任务书把「同一符号多个权重」当成 `extractVec` 的**性质**，
但它其实是**靶类型字段个数**的性质 ——
**在当前 `LinearLayer` 定义下，该性质不存在**。
⚠ **要让它存在，必须先[修改] `LinearLayer`** —— 而这是**改既有定义**，
⚠ **超出本任务「只创建新文件」的授权**（任务书 §纪律），**本文件不做**。 -/

/-- ⭐ **诊断的形式化（抽象版）**：若 `extractVec` **忽略**某一个投影
（即存在两个只在该投影上不同的元素），则它**不是**单射。

⚠ **本定理是 §六 的可推广判据**：它把「非单射」**归约**到
「存在一个 `extractVec` 读不到的字段（自由度）」。

⭐ **本定理也说明 §三 为何必然成立**：`LinearLayer` **没有**这样的自由度，
故 §三 的前提（存在两个只差被忽略字段的元素）**为空**。

⚠ **本定理的 `f` 是任意函数**（抽象形式），故它可复用于检查**其他**转换映射。 -/
theorem not_injective_of_ignored_argument {α β : Type*} (f : α → β)
    (x y : α) (hne : x ≠ y) (heq : f x = f y) : ¬ Function.Injective f :=
  fun hinj => hne (hinj heq)

/-- ⭐ **§六 判据的实例化（**单向**，避开经典选择）**：

**存在碰撞 ⟹ `extractVec` 不是单射。**

⭐ **本定理把任务书的命题【精确地】化归为一个可检验的条件**：

    任务书要的命题的【前提】  =  存在 `l ≠ l'` 使 `extractVec l = extractVec l'`

⚠ **只证这一方向是刻意的**：反方向（`¬Injective → ∃ 碰撞`）需要经典逻辑
（`¬∀a b, …` 展开为存在性见证需 `Classical` + `push_neg`），
⚠ 本文件**不引入该依赖**，因为本文件**只用**这一方向（§六 与 `r03_claim_is_false`）。
⭐ **如实登记**：反方向**本文件未证**（见 §七 诚实边界）。

⚠ 而 §三 `no_fiber_of_extractVec_has_two_points` **证伪**了上述前提。
⇒ ⭐ **任务书的命题被归约为一个关于类型定义的事实**（`LinearLayer` 有无多余字段）。 -/
theorem collision_implies_not_injective
    (h : ∃ l l' : LinearLayer, l ≠ l' ∧ extractVec l = extractVec l') :
    ¬ Function.Injective extractVec := by
  obtain ⟨l, l', hne, heq⟩ := h
  exact not_injective_of_ignored_argument extractVec l l' hne heq

/-- ⭐⭐ **R-03 的最终判定（本条是全文件的落点）**：

**任务书要求证的存在性命题为假** —— 不存在使 `extractVec` 塌缩的两个不同层。

⚠ **与 §三 的关系**：§三 是「`extractVec` 是单射」，本条是它的**存在性否定形式**；
⭐ **本条的用处**：它**逐字**否定任务书 `∃` 形式的断言，故可**直接**引用以驳回该任务。 -/
theorem r03_claim_is_false :
    ¬ (∃ l l' : LinearLayer, l ≠ l' ∧ extractVec l = extractVec l') :=
  no_fiber_of_extractVec_has_two_points

end Lattice.Lib.Editing.RealExtractNonInjective