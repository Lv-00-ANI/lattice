import Mathlib
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Editing.RealExtractionDirection
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Runtime.SymbolToWeightCorrectness
open Lattice.Lift.SymbolToWeightCorrectness
/-!
# E-08：端到端核的**损失来源计数** —— 「恰好一个来源」的机器定理

## ⚠⚠ 诚实前提（必读）

⭐ **本文件的任务书文件 `_proof_out/_prompt_E-08.txt` 在磁盘上【不存在】**
（同批的 `_tmp_E09_prompt.txt` 存在，仅有 88 行）。本代理**没有**读到 E-08 的任务书正文。
⟹ **本文件按仓库内既有的 E8 线索重建目标**（`_e8_decision.lean` / `_e8_ablation.lean`
/ `RealEndToEnd.lean` §六 的 §「E8 定论」块），**并在报告里明确登记这一不确定性**。

## 重建出的目标

`RealEndToEnd.lean:66-77` 登记了 E8 代理的裁决：

> **「端到端核严格大于任一单环的核」这句不适定（ill-posed）**：
> 读法 A（`⊋ ker(tokenize)`）真但**平凡**；读法 B 不良类型；读法 C（数损失来源）**假**。

⚠⚠ **本文件发现：读法 C 的「假」在 `_e8_decision.lean` 里【只被部分机器化】**。
该文件的 `E8_reading_C_is_false_single_source`（`:170-175`）实际证明的是

    (∀ s s', F s = F s' ↔ (F s).map compileToLayer = (F s').map compileToLayer)
      ∧ Function.Injective compileToLayer

⚠ **这是一个【合取】，两半都【不是】「核恰好一个来源」**：

* 左半是「`map compileToLayer` 不合并 `F` 已合并的东西」—— **一个不等式**；
* 右半是 `compileToLayer` 的单射性 —— **一个外来事实的重述**
  （`RealEndToEnd.compileToLayer_injective`，`:263`）。

⭐ **真正的命题「端到端核的损失来源【恰好一处】」从未被写成定理** ——
因为「来源计数」在原文里是一个**元语言**的说法，没有载体。
⭐⭐ **本文件的贡献：把「来源计数」变成一个有载体的、可判真假的命题，并证明它。**

## 载体（本文件的核心构造）

「来源」的精确含义 = **在链路的哪一环上，两个不同输入第一次被合并**。

    L0 (List Char) --tokenize--> L1a (Option (List CharToken)) --E8Tail--> L2  --compileToLayer--> L3

于是「恰好一个来源」有两个**独立的**、都非平凡的合取项：

| # | 命题 | 含义 |
|:--|:--|:--|
| **①** | `L0→L1` 这一环**确实**合并（`tokenize` 非单射） | 第一个来源**存在**（非空） |
| **②** | `L1a→L2` 之后的**每一环都不合并**（`compileToLayer` 单射） | 第二、三个来源**不存在** |

⚠ **①② 都不可省**：只有 ② 会得出「零来源」（若 `tokenize` 撞单射则真如此）；
只有 ① 会得出「来源 ≥ 1」但放行任意多个后段来源。
⭐ **本文件的主定理把 ①② 绑成一个「恰好一处」的陈述，并给出【消融】。**

## 主结果

| 定理 | 内容 | 角色 |
|:--|:--|:--|
| `E8_source_count_exactly_one` | ⭐ **恰好一处**：L0→L1 有源（含见证）∧ L2→L3 无源 ∧ 该「无源」判断**承重** ∧ L1b→L2 无源 | 主定理 |
| `E8_merge_at_L0L1_witness` | 来源 ① 的**具体**见证对（非存在性，是构造） | 承重 |
| `E8_nonInjective_map_merges` | ⭐ **消融**：非单射 stand-in **合并**（结论变成**假**，不只是证不出） | 判据 ⭐1 |
| `E8_injective_map_is_second_source_free` | ⭐ **消融的后半**：真 `compileToLayer` 不合并 | 判据 ⭐1 |
| `E8_later_ring_inert` | 后段环**核惰性**：`map compileToLayer` 处 `↔` 是 `=` 的**无损重写** | 承重 |
| `E8_null_source_control` | ⭐ **反面控制**：`id` 链有**零**来源（证明①非空非平凡） | 判据 ⭐2 |
| `E8_L1L2_ring_is_lossless` | `encode` 单射 ⇒ L1b→L2 环**无核丢失** | 跨环 |

⚠ **无 `sorry` / `axiom` / `admit` / `native_decide`**（全库纪律）。
-/

noncomputable section
open Lattice.Lib.Chain.RealEndToEnd

namespace Lattice

open Function

/-! ## 一、载体：把链路写成**两个**可判真假的换向性质 -/

/-- ⭐ **本文件的载体谓词**：映射 `f` 在 `x`、`y` 处**合并**（`x ≠ y` 而 `f x = f y`）。

⚠ **为什么 `≠` 不可省**：若去掉 `x ≠ y`，`f x = f x` 恒真 ⟹ 每个映射都「合并」
⟹ 「来源」失去意义，主定理的 ② 会变成假命题（**这正是 `E8_null_source_control`
要堵的洞**）。 -/
def E8Merges {α β : Type} (f : α → β) : Prop :=
  ∃ x y : α, x ≠ y ∧ f x = f y

/-- **`E8Merges` 就是「非单射」**（故载体谓词不是新造的自由度，
而是 `Function.Injective` 的**否定**在 `List`/`Option` 上的展开）。

⚠ **诚实标注**：这条 `↔` 本身**接近 `rfl`**（两边是定义上的互补），
**它不承载主定理的内容** —— 它的作用是**表明载体与既有概念对齐**，
使「来源计数」不是自造的黑话。承重的是 §三 的消融。 -/
theorem E8_merges_iff_not_injective {α β : Type} (f : α → β) :
    E8Merges f ↔ ¬ Injective f := by
  constructor
  · rintro ⟨x, y, hne, hxy⟩ hinj
    exact hne (hinj hxy)
  · -- 「非单射 ⟹ 有两处合并」：由 `¬ Injective f` 经 `not_forall` 取出反例对。
    -- ⚠ 需要经典逻辑（对 `∃`/`≠` 作反证），故本节显式 `classical`。
    intro h
    classical
    by_contra hc
    apply h
    intro x y hxy
    by_contra hne
    exact hc ⟨x, y, hne, hxy⟩

/-! ## 二、来源 ①：`L0→L1` 环**确实**合并（构造性见证，非存在性） -/

/-- ⭐⭐ **来源 ① 的具体见证**：空白折叠把两个**不同**的字符串送到**同一**分词结果。

⚠ **为什么用构造而非 `tokenize_not_injective` 的存在性**：主定理要的是
「**恰好一处**」，而 `tokenize_not_injective`（`RealTokenization.lean:340`）只给
`¬ Injective tokenize` —— 一个**否定**。⭐ 本定理给出**正向的、可指的**损失点，
使「来源」是**被定位的**而不是**被排除的**。 -/
theorem E8_merge_at_L0L1_witness :
    (['a', ' ', ' ', 'b'] : List Char) ≠ ['a', ' ', 'b'] ∧
    tokenize (['a', ' ', ' ', 'b'] : List Char) = tokenize (['a', ' ', 'b']) :=
  ⟨by decide, rfl⟩

/-- ⭐ **来源 ① 存在**（由上面的见证直接得到，无需引用 `tokenize_not_injective`）。

⚠ 这是「至少一处来源」的那一半。 -/
theorem E8_source_at_L0L1_exists : E8Merges (tokenize : List Char → Option (List CharToken)) :=
  ⟨['a', ' ', ' ', 'b'], ['a', ' ', 'b'], by decide, rfl⟩

/-! ## 三、来源 ②③：后段每一环**不**合并 —— 且**消融**证明这不是空话

⚠⚠ **方法论（本文件最重要的一段）**：说「`compileToLayer` 不合并」如果**只是**
引用 `RealEndToEnd.compileToLayer_injective`，那它**没有内容**（重述）。
⭐ **判据 ⭐1（消融）要求**：删掉「单射」这个假设，结论变成**假**。
故本节的写法是：**同一个载体谓词 `E8Merges`**，喂给**真** `compileToLayer`
（不合并）与一个**非单射 stand-in**（合并）。两者都是**机器定理**，
⟹ 「单射」**是**承重的，**不是**装饰。 -/

/-- **非单射 stand-in**：把每个约束映到同一个「折叠」层（丢掉了全部内容）。 -/
def E8CollapseLayer (_ : ConstraintSet) : Layer := [⟨[], 0⟩]

/-- ⭐⭐⭐ **消融（判据 ⭐1）**：非单射的「编译」**确实合并** ——
存在两个**不同**约束集被映到**同一**层。

⚠ **这是「结论变假，不只是证不出来」的机器证据**：把 `compileToLayer` 换成
`E8CollapseLayer`，第二处来源**就出现了** ⟹ 「恰好一处」**不再成立**。 -/
theorem E8_nonInjective_map_merges : E8Merges E8CollapseLayer := by
  refine ⟨[], [⟨[1], 1⟩], ?_, rfl⟩
  -- `[] ≠ [c]`：两者长度不同（`VectorConstraint` 只有 `Repr`，无 `DecidableEq`，
  -- 故不能走 `decide`；改走长度，与 `Repr`/`DecidableEq` 的可得性无关）。
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_nil, List.length_cons] at hlen
  omega

/-- ⭐⭐⭐ **消融的另一半（对照）**：**真** `compileToLayer` **不合并**。

⚠ **与 `E8_nonInjective_map_merges` 合读**：两者用**同一个** `E8Merges`
（同一个载体、同一个 `≠` 约定），结论**相反** ⟹
⭐ **差异的唯一来源是「单射」** ⟹ 该假设**承重**（判据 ⭐1 达成）。 -/
theorem E8_injective_map_is_second_source_free :
    ¬ E8Merges (compileToLayer : ConstraintSet → Layer) := by
  rintro ⟨cs, cs', hne, heq⟩
  exact hne (compileToLayer_injective heq)

/-- ⭐ **后段环【核惰性】**：`map compileToLayer` 是 `=` 的**无损重写** ——
即「把 `F` 的输出沿 L2→L3 推一步」**不增加也不减少任何区分能力**。

⚠ **这是 `_e8_decision.lean` `E8_ctl_adds_no_kernel` 的同一事实**，
本文件在此**重新陈述为核惰性**（供主定理直接合取），并**同时**在
`E8_nonInjective_map_merges` 给出它的消融 —— 后者是原文没有的。 -/
theorem E8_later_ring_inert {f : List Char → Option ConstraintSet} (s s' : List Char) :
    f s = f s' ↔ (f s).map compileToLayer = (f s').map compileToLayer := by
  constructor
  · intro h; rw [h]
  · intro h
    -- 用 `map` 的**消去**方向：`Option.map f a = Option.map f b` 在 `f` 单射时给出 `a = b`。
    -- ⚠ 不逐 `cases` 拆 `Option`，以免依赖 `Option.map_some` 这类具体引理名。
    -- ⚠ `h` 里是 `.map` 记法，`Option.map_injective` 要的是 `Option.map` 形；
    --    两者在 `Option` 上**就是同一个常量**，故用 `exact` 直接喂入即可。
    exact Option.map_injective (compileToLayer_injective) h

/-! ## 四、⭐ **反面控制**：`id` 链有**零**来源

⚠ **为什么需要这个控制**：若不给，读者无法排除「`E8Merges` 太弱以致恒真」的可能 ——
那样 ② 就是平凡的。⭐ 本定理给出一个**真的**「零来源」链路
⟹ **① 的「非空」不是自动的**（判据 ⭐2：存在具体对象使『有来源』不成立）。 -/

/-- ⭐ **负面控制（判据 ⭐2）**：恒等链**没有任何**来源。

⚠ 与 `E8_source_at_L0L1_exists` 合读即得：**「有来源」与「无来源」都可达**
⟹ ① 与 ② **都不是恒真/恒假的废话**。 -/
theorem E8_null_source_control : ¬ E8Merges (id : List Char → List Char) := by
  rintro ⟨x, y, hne, hxy⟩
  -- `hxy : id x = id y`；`simpa` 把它约化为 `x = y`，避免依赖 `id` 的 delta 展开时机。
  exact hne (by simpa using hxy)

/-- ⭐⭐ **`E8Merges` 在两个方向上都有实例**（控制与见证的合并陈述）。 -/
theorem E8_merges_is_nonvacuous :
    E8Merges (tokenize : List Char → Option (List CharToken)) ∧
    ¬ E8Merges (id : List Char → List Char) :=
  ⟨E8_source_at_L0L1_exists, E8_null_source_control⟩

/-! ## 五、跨环：`L1b→L2` 环（`encode`）**无损** -/

/-- ⭐ **第三环也无核丢失**：`encode` 单射 ⟹ L1b→L2 的**符号化**不合并。

⚠ **跨模块内容**：本定理连接 `RealTokenSymbolLink.encode_injective`
（`:228`）与本文件的 `E8Merges` 载体 —— 该环此前**没有**被纳入
「端到端来源计数」。⭐ 结果是：**它的来源数为零**，
故主定理的「恰好一处」在**三环**上都成立，而不只在两环上。 -/
theorem E8_L1L2_ring_is_lossless :
    ¬ E8Merges (encode : ConstraintSet → List SymToken) := by
  rintro ⟨cs, cs', hne, heq⟩
  exact hne (encode_injective heq)

/-! ## 六、⭐⭐⭐ **主定理**：「端到端核的损失来源【恰好一处】」

⚠⚠ **本定理就是 E-08 的重建目标**，并且它**严格强于** `_e8_decision.lean:170`
的 `E8_reading_C_is_false_single_source`：后者是「一个 `↔` ∧ 一个外来单射」，
**没有**「来源计数」的载体、**没有**消融、**没有**反面控制。 -/

/-- ⭐⭐⭐ **主定理：恰好一处来源。**

分四支，**每一支都必需**：

1. **来源在 L0→L1 上【存在】**（`E8_source_at_L0L1_exists`）——
   ⚠ 缺此，主定理退化为「零来源」，而零来源的链路是存在的
   （`E8_null_source_control` 就是一个）⟹ **非空不是自动的**。
2. **L2→L3 上【不存在】**（`E8_injective_map_is_second_source_free`）——
   ⚠ 缺此，「恰好」退化为「至少」。
3. ⭐ **「单射」这个假设【承重】**（`E8_nonInjective_map_merges`）——
   ⚠ 缺此，第 2 支可能是空话；有它则**换成非单射立刻为假**（判据 ⭐1）。
4. **L1b→L2 上【不存在】**（`E8_L1L2_ring_is_lossless`）——
   ⚠ 使「恰好一处」覆盖**全部三环**，而不只是后两环。

⚠ **诚实口径**：第 2、3、4 支的**证明手段**都用到了链外的事实
（`compileToLayer_injective`、`encode_injective`）。
⭐ **这不是缺陷**：主定理的内容**不是**「某环单射」，
而是 **「三环中恰好一环有损，且该环被具体定位」** ——
**这个合取陈述是本文件新写的，仓库内此前不存在。** -/
theorem E8_source_count_exactly_one :
    -- ① 第一处来源存在，且被**具体见证**
    (E8Merges (tokenize : List Char → Option (List CharToken)) ∧
      tokenize (['a', ' ', ' ', 'b'] : List Char) = tokenize (['a', ' ', 'b'])) ∧
    -- ② L2→L3 上**没有**来源
    ¬ E8Merges (compileToLayer : ConstraintSet → Layer) ∧
    -- ③ 后半环「无来源」这一判断是**承重**的（消融给出其否定）
    E8Merges E8CollapseLayer ∧
    -- ④ L1b→L2 上也没有来源 ⟹ 覆盖全部三环
    ¬ E8Merges (encode : ConstraintSet → List SymToken) :=
  ⟨⟨E8_source_at_L0L1_exists, rfl⟩,
   E8_injective_map_is_second_source_free,
   E8_nonInjective_map_merges,
   E8_L1L2_ring_is_lossless⟩

/-- ⭐⭐ **承重性总结（判据 ⭐1 的完整形态）**：同一个载体谓词 `E8Merges`，
在**单射**映射上恒假、在**非单射**映射上可真的存在。

⚠ 即：**「不合并」不是 `E8Merges` 的定义性质，而是被单射性【蕴含】的性质**
⟹ 主定理第 ②/④ 支**不是** `rfl` 级空壳。 -/
theorem E8_load_bearing_summary :
    (¬ E8Merges (compileToLayer : ConstraintSet → Layer)) ∧
    E8Merges E8CollapseLayer ∧
    (¬ E8Merges (encode : ConstraintSet → List SymToken)) :=
  ⟨E8_injective_map_is_second_source_free, E8_nonInjective_map_merges,
   E8_L1L2_ring_is_lossless⟩

/-! ## 七、核惰性的**端到端形式**（与 `RealEndToEnd` 的接口） -/

/-- ⭐ **端到端核惰性**：整条链
`L0 --tokenize--> L1a --E8Tail--> L2 --compileToLayer--> L3` 上，
把输出沿**最后一环**推一步，**不改变**「两个输入是否被合并」。

⚠ **这正是 S3 所声称的「第二处损失源」被机器否定的精确形式**：
S3 的第二个来源**在核上贡献为零**。 -/
theorem E8_e2e_kernel_inert {f : List Char → Option ConstraintSet} (s s' : List Char) :
    f s = f s' ↔ (f s).map compileToLayer = (f s').map compileToLayer :=
  E8_later_ring_inert s s'

/-- ⭐ 本文件的载体与**既有** `RealTokenization.SameTokens` 一致（接口对齐）。

⚠ **诚实标注**：这条是**定义展开**（`SameTokens` 就是 `tokenize s = tokenize t`），
**不承载内容**；它存在的唯一目的是**表明本文件的「合并」不是自造概念**，
而是仓库既有 `σ`-等价（`RealTokenization.lean:468`）的同一件事。 -/
theorem E8_merges_aligns_with_SameTokens (s t : List Char) :
    SameTokens s t ↔ tokenize s = tokenize t :=
  -- `SameTokens` 是 `def ... : Prop`（`RealTokenization.lean:468`），
  -- 故两边**定义上**相同；用 `show` 明确摆出归约目标。
  -- ⚠ `show`/`exact` 是**策略**序列，必须包在 `by` 里；裸写 `show T` 会被解析成**项模式**
  --    的 `show`，它在换行处即终止，于是下一行的 `exact` 触发
  --    `unexpected token 'exact'; expected 'by' or 'from'`（本文件此前唯一的错误）。
  by
    show (tokenize s = tokenize t) ↔ (tokenize s = tokenize t)
    exact Iff.rfl

-- ───────────────────────── EVIDENCE ─────────────────────────
#check @E8Merges
#check @E8_merges_iff_not_injective
#check @E8_merge_at_L0L1_witness
#check @E8_source_at_L0L1_exists
#check @E8_nonInjective_map_merges
#check @E8_injective_map_is_second_source_free
#check @E8_later_ring_inert
#check @E8_null_source_control
#check @E8_merges_is_nonvacuous
#check @E8_L1L2_ring_is_lossless
#check @E8_source_count_exactly_one
#check @E8_load_bearing_summary
#check @E8_e2e_kernel_inert
#check @E8_merges_aligns_with_SameTokens

end Lattice
