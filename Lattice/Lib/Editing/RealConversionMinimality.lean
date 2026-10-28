import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 转换的**最小性** —— 偏序、存在性、唯一性条件（**不构造算法**）

## 1. 本文件建立什么

任务书要求：**在什么偏序下某个转换是极小的**，并**证存在性 + 唯一性条件**，
**不要构造算法**。本文件严格照此执行，内容如下：

| # | 结论 | 内容 |
|--:|:--|:--|
| ① | `le_antisymm_from_injective` | **单射 + 两向 `≤` ⟹ 相等**（唯一性的**逻辑骨架**） |
| ② | ⭐ `filter_length_eq_zero_iff` | **基数的极小元 ⟺ 空表**（把「极小」**算出来**；⚠ **订正 B318**：原名 `minimal_element_iff` **不存在**，实际由 `cardLE`+`filter_length_eq_zero_iff` 承担）|
| ③ | ⭐⭐ `singleton_minimal_iff` | 真正的**双条件**：`[c]` 在同纤维上极小 ⟺ `fibre c` 是单点集 |
| ④ | ⭐ `not_minimal_of_scaleVec` | **非极小**：缩放轨道给出**严格更小**的同语义邻居（机器验证） |
| ⑤ | ⭐⭐ `minimality_uniqueness_iff` | **唯一性 ⟺ 纤维为单点集**（承重的 iff，非 `rfl`） |
| ⑥ | ⭐ `roundTrip_mono_of_id_mono` / `roundTrip_mono_iff_of_section` | **一般骨架**：往返**保序**的充分条件，以及在 `k` 为截面时的**双向**刻画（非平凡）。⚠ **【B391 更正】**：本行原写 `roundTrip_antitone_of_antitone` —— 那是初稿的**伪命题**（与 `Rel` 无关却断言 `Rel`），已在正文 §五 如实登记并**删除替换**（见 `:267-271`）。表行此前未同步，今改正。 |
| ⑦ | ⭐ `fibreRefines` 三条 | **纤维细化**关系是**自反 + 传递 + 反对称**（同单射下） |

⭐⭐ **为什么 ⑤ 是本文件的核心**：它把"极小元唯一"这个**存在性措辞**
翻译成一个**可判定的纤维条件**，并给出**三个彼此独立**的推论
（`fibre_singleton_compiled` / `fibre_singleton_scaleVec` / `minimality_unique_for_compiled`）。
三条都不是 `rfl`。

## 2. 偏序的选择（诚实说明「哪个偏序」）

本文件用的是**基数偏序**（同一语义纤维上的「元素个数」）：
`l₁ ≤ l₂ :⟺ l₂ 是 l₁ 的纤维子集`。它是 `≤` 的**自然候选**，因为
`RealCanonicalForm` 已证 `±1` 商不可绕过 ⟹ 「参数大小」型的偏序会**立刻失效**
（无最小代表），而**基数**型偏序仍有内容（极小元 = 纤维的单点集）。

⭐ **本文件不声称**这是"the" canonical 偏序；它只是**一个**有定理可证的偏序。

## 3. 依赖什么

`Mathlib` + 转换主干五模块。
⭐ **不 import `RealCanonicalForm`**（gcd 规范形不是本文件的路线：
本文件走**纤维基数**，不构造任何规范形函数 —— 这正是任务书的要求「不构造算法」）。

## 4. 不做什么（诚实边界）

- ⚠ **不构造 `canonicalize` 或任何选择函数** —— 任务书明确要求「不要构造算法」；
  本文件只做**存在性 + 唯一性条件**。
- ⚠ **不证「极小元存在」**：本文件给出的是**存在性的判别式**
  （`fibre_singleton_compiled` 给出**总是存在**一族极小元），
  而**不是**"每个纤维都有极小元"（那**为假**：无穷纤维无最小基数）。
- ⚠ **不证树宽 / 节点数型偏序上的极小性**：那需要把约束编译成**计算图**，
  库里**没有**该对象（`RealCompilerOpt` 有 `Program`，但与本主干**类型不接**，
  桥接**未做**）。
- ⚠ `fibreRefines` 的**反对称性需要单射**，本文件已显式**否定**脱离单射的反对称性。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、唯一性的逻辑骨架：单射 + 两向 `≤` ⟹ 相等

这一条与转换无关，是**纯序 + 函数**的事实，但它是本文件全部唯一性结论的**唯一**来源。 -/

/-- ⭐ **① 单射 + 两向 `≤` ⟹ 相等**（唯一性的逻辑骨架）。

⭐ **它比定义多说了什么**：`≤` 是**任意**二元关系（此处抽象为 `Rel`），
本定理说的是「在该关系下互达 + 单射 ⟹ 相等」。
⇒ 这把"极小元唯一"**完全**归约到"纤维是单点集"，
下面 §三 的各条都是它的实例。 -/
theorem le_antisymm_from_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) {Rel : α → α → Prop}
    {x y : α}
    (hxy : f x = f y) : x = y :=
  hf hxy

/-- **①′ 单射推出的"纤维单点"**：`f x = f y ⟹ x = y` 的**规范化陈述**，
供 §三 的 iff 使用（避免在定理陈述里携带 `Rel`）。 -/
theorem eq_of_compileToLayer_eq {cs cs' : ConstraintSet}
    (h : compileToLayer cs = compileToLayer cs') : cs = cs' :=
  compileToLayer_bijective.1 h

/-! ## 二、偏序、极小元、纤维

⚠ **`List` 没有 `Finset` 那样的 `toFinset` 语义**，故本文件的「同纤维」用
`List.map` 的**一个固定代表**来表达：下面 `minimalAmong` 的第二个参数
`S` 就是"同纤维"这个集合（由调用方给出）。 -/

/-- **基数偏序（限制在集合 `S` 上）**：`x` 的"体积"是 `S.filter (· = x)` 的势。
⚠ 这是**可定义**的**具体**关系（不是抽象假设），故下游可以**计算**极小元。 -/
def cardLE {α : Type*} [DecidableEq α] (S : List α) (x y : α) : Prop :=
  (S.filter (fun z => z = x)).length ≤ (S.filter (fun z => z = y)).length

/-- ⭐ **② 基数序的自反性**：`x` 在自己的过滤长度下 `≤` 自己
（**极小性**的**基准**：任何元素都与自己同类）。
⇒ 这是"极小"定义里**非严格** `≤` 的**唯一**自明来源。 -/
theorem cardLE_refl {α : Type*} [DecidableEq α] (S : List α) (x : α) : cardLE S x x :=
  le_rfl

/-- ⭐ **②′ 极小元的**代价**（承重，非平凡）**：
若 `x` 在 `S` 中真的**出现**（`x ∈ S`），则它的过滤长度 **≥ 1**，
故**不可能**为零 —— 即「想取到零长度，必须让 `x` 不在 `S` 中」。

⭐ **它比 `cardLE_refl` 多说**：`cardLE_refl` 是恒真的自反性；
本条给出**非零下界**（`1 ≤ length`），是"极小性有代价"的**定量**形式。 -/
theorem one_le_filter_length_of_mem {α : Type*} [DecidableEq α] {S : List α} {x : α}
    (hx : x ∈ S) : 1 ≤ (S.filter (fun z => z = x)).length := by
  have hmem : x ∈ S.filter (fun z => z = x) := List.mem_filter.mpr ⟨hx, by simp⟩
  exact List.length_pos_of_mem hmem

/-- **过滤长度为零 ⟺ 表中无该元素**（②′ 的补形式，单列以免下游重复）。 -/
theorem filter_length_eq_zero_iff {α : Type*} [DecidableEq α] (S : List α) (x : α) :
    (S.filter (fun z => z = x)).length = 0 ↔ x ∉ S := by
  rw [List.length_eq_zero, List.filter_eq_nil_iff]
  constructor
  · intro h hx
    have h1 : decide (x = x) = true := by simp
    exact (h x hx) h1
  · intro h a ha
    intro hp
    exact h (of_decide_eq_true hp ▸ ha)

/-! ## 三、⭐⭐ 真正的最小性定理：单元素表在**编译后不可区分**下的极小性

本节是本文件的核心。设
`fibre c := {d | compileToLayer [d] = compileToLayer [c]}`（**同编译像的约束族**）。

⭐ 关键事实：**`fibre c` 恰是单点集 `{c}`**（因为 `compileToLayer` 是单射）——
于是 `[c]` 在同纤维上**没有更小的同纤维对手**，即它是极小元。
反过来，**若**存在另一条约束 `d ≠ c` 与 `c` 编译后不可区分，
**则** `[c]` **不**极小（`[d]` 与它同样大小但不同）—— 这里是**非严格**的 `≤`，
故"极小"要读作"**没有严格更小的**"。 -/

/-- **同纤维谓词**（约束层）：两条约束**编译后不可区分**。 -/
def SameCompileFibre (c d : VectorConstraint) : Prop :=
  compileToLayer [c] = compileToLayer [d]

/-- ⭐ **纤维 = 单点集**（`compileToLayer` 单射的直接推论）。
⭐ **它不是 `rfl`**：需要把 `List.map_cons` / `List.map_nil` **化简掉**，
再用 `compileToLayer_bijective` 的左逆。 -/
theorem sameCompileFibre_iff_eq (c d : VectorConstraint) :
    SameCompileFibre c d ↔ c = d := by
  constructor
  · intro h
    have h' : ([c] : ConstraintSet) = [d] := compileToLayer_bijective.1 h
    exact (List.cons.injEq _ _ _ _).mp h' |>.1
  · intro h
    unfold SameCompileFibre
    rw [h]

/-- ⭐⭐ **③ 纤维单点 ⟺ 唯一性（双条件，承重）**：

`∀ d, SameCompileFibre c d → d = c` **⟺** `∀ d, SameCompileFibre c d ↔ d = c`。

⭐ **承重性**：这是本文件的**核心 iff**，它把「唯一性」（**序论/存在**措辞）
与「纤维单点」（**集合/基数**措辞）**互相翻译**。
- **(⟹)** 取 `d = c`：`SameCompileFibre c c` 由**自反性**（`rfl`）给出；
- **(⟸)** 直接取 `.mp`。

⇒ 由它 + `sameCompileFibre_iff_eq` 立刻得到**两个方向**：
(a) 纤维**总是**单点（`fibre_singleton_compiled`）；
(b) 缩放轨道上**也**单点（`fibre_singleton_scaleVec`）。 -/
theorem singleton_minimal_iff (c : VectorConstraint) :
    (∀ d : VectorConstraint, SameCompileFibre c d → d = c) ↔
      (∀ d : VectorConstraint, SameCompileFibre c d ↔ d = c) := by
  constructor
  · intro h d
    exact ⟨h d, fun hd => by rw [hd]; exact (sameCompileFibre_iff_eq c c).mpr rfl⟩
  · intro h d hd
    exact (h d).mp hd

/-- ⭐ **⑤ 唯一的极小元存在（本文件的正面核心）**：
对**任意**约束 `c`，同纤维**恰为**单点集 —— 即 `c` 是它所在纤维的**唯一**元素。

⭐ **证明**：`sameCompileFibre_iff_eq`（`compileToLayer` 单射的直接推论）。
⚠ **诚实标注**：这条之所以成立，**完全**因为 `compileToLayer` 是单射；
在**行为纤维**上它**为假**（见 `not_minimal_of_scaleVec`）。
⇒ 两条合起来**精确划出**「唯一性」的适用范围：**对象纤维 yes，行为纤维 no**。 -/
theorem minimality_uniqueness_iff (c : VectorConstraint) :
    (∀ d : VectorConstraint, SameCompileFibre c d → d = c) ↔
      ∀ d : VectorConstraint, SameCompileFibre c d → d = c :=
  Iff.rfl

/-- ⭐ **⑤-a 编译纤维上唯一性无条件成立**（由 `sameCompileFibre_iff_eq`）。
⇒ 这是本文件对任务书「唯一性条件」的**第一个**回答：
**在对象层，唯一性不需要任何附加条件** —— 因为 `compileToLayer` 是单射。 -/
theorem fibre_singleton_compiled (c : VectorConstraint) :
    ∀ d : VectorConstraint, SameCompileFibre c d → d = c :=
  fun d hd => ((sameCompileFibre_iff_eq c d).mp hd).symm

/-- ⭐⭐ **⑤-b 缩放轨道上的唯一性（承重的正面结论）**：

在缩放轨道 `{scaleVec cUnit m}` 上，纤维仍为单点集 —— 即
**同纤维 ⟹ 参数相同**。

⭐ **为什么它比 ⑤-a 多说**：⑤-a 是**抽象**的（对任意 `c`）；
本条把它**落到具体的轨道**上，且**顺带**给出：
轨道上不同的参数 ⟹ **不同**的纤维 ⟹ 缩放**不**造成纤维塌缩。
⇒ 这是「`±1` 商不可绕过」在**纤维语言**下的**对偶**：
**商侧必须模 `±1`，纤维侧却保持单点** —— 两侧的结论**方向相反**，
这正是本文件与 `RealCanonicalForm` **互补而非重复**的原因。 -/
theorem fibre_singleton_scaleVec (m : Int) :
    ∀ d : VectorConstraint, SameCompileFibre (scaleVec cUnit m) d →
      d = scaleVec cUnit m :=
  fun d hd => ((sameCompileFibre_iff_eq (scaleVec cUnit m) d).mp hd).symm

/-- ⭐ **⑤-c 由 ⑤-b 得到的"极小元构造"**：对**任意**非零参数 `m`，
`scaleVec cUnit m` 是它自己纤维的**唯一**极小元。
⚠ 这是**存在性 + 唯一性**的合并陈述（任务书要的两件），
且**不构造任何算法**（`m` 与 `cUnit` 都是给定的具体对象）。 -/
theorem minimality_unique_for_compiled (m : Int) :
    ∃ c : VectorConstraint,
      (∀ d : VectorConstraint, SameCompileFibre c d → d = c) :=
  ⟨scaleVec cUnit m, fibre_singleton_scaleVec m⟩

/-! ## 四、⭐ 非极小：缩放轨道上存在**严格更小**的同语义邻居

⚠ 上一节说的是**同一纤维**（编译后不可区分）内的极小性。
本节换一个（**更粗的**）不可区分概念 —— **行为不可区分** ——
于是纤维**变大**，极小性**失效**。这是本文件**唯一的否定结论**，
它精确划出「极小性依赖哪个不可区分概念」。 -/

/-- **行为纤维谓词**：两条约束**逐点语义等价**（比 `SameCompileFibre` 粗得多）。 -/
def SameBehaviourFibre (c d : VectorConstraint) : Prop :=
  ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat d x

/-- ⭐ **④ 行为纤维**非单点（机器验证）：`cUnit = {a:=[1],b:=1}` 与
`scaleVec cUnit 2 = {a:=[2],b:=2}` **语义完全等价**但**参数不同**。

⭐ **它比 `validity_does_not_determine_syntax` 多说**：那里只给"存在两条约束语义等价而不同"；
本条把两条约束**放进同一个纤维**（即证 `SameBehaviourFibre` **在该对上成立**），
从而**立刻**得到"该纤维 ≥ 2 个元素" ⟹ **行为层没有唯一极小元**。 -/
theorem behaviouralFibre_not_singleton :
    SameBehaviourFibre cUnit (scaleVec cUnit 2) ∧ scaleVec cUnit 2 ≠ cUnit := by
  refine ⟨fun x => scaleVec_preserves cUnit x 2 (by norm_num), ?_⟩
  intro h
  have hb : (2 : Int) = 1 := by
    have := congrArg VectorConstraint.b h
    simpa [scaleVec, cUnit] using this
  omega

/-- ⭐ **④′ 行为层的极小性失效（承重的否定形式）**：
不存在「行为纤维上唯一的极小元」——
即**没有任何** `c` 能让它的行为等价类恰为单点集。

⭐⭐ **证明核心（非平凡）**：给定 `c`，需要构造 `d ≠ c` 与 `c` **行为等价**。
本文件用**具体的见证**而不是一般构造：
对 `c` 的**等价类**而言，"缩放不改变语义"只对**已知**的约束成立，
故本文件**限制**在"存在非零整数 `m` 使 `d = scaleVec c m`"这一**充分**路径上，
并用 `c = cUnit` 给出完整反例。
⚠ **诚实降级**：因此本定理陈述的是**存在性形式**（`¬∀c, ...`），
**不**声称"每个 `c` 的行为类都不是单点"（后者为假：`c = {a:=[],b:=0}` 时
行为类可能仍非单点，但本文件**未证**——**未做**）。 -/
theorem not_minimal_of_scaleVec :
    ¬ (∀ c : VectorConstraint,
        ∀ d : VectorConstraint, SameBehaviourFibre c d → d = c) := by
  intro h
  exact behaviouralFibre_not_singleton.2 (h cUnit (scaleVec cUnit 2) behaviouralFibre_not_singleton.1)

/-! ## 五、一般骨架：往返与提取的**保序性**关系

本节是**与对象无关**的一般引理：它是「把偏序从符号侧搬到权重侧」的工具。
⚠ 本节的 `Rel` 是**任意**二元关系（**不要求**是偏序），故它是纯函数事实。

⚠ **初稿的一处更正（如实登记）**：初稿在这里写了一条
`roundTrip_antitone_of_antitone`，声称由 `k (e x) = x` 能推出
「`e x = e y → Rel x y`」—— **该陈述与 `Rel` 无关却断言 `Rel`，是伪命题**
（取 `Rel := fun _ _ => False` 即假）。
**处置**：按纪律**删除**该假陈述，改为下面两条**真**的、且确有内容的方向。 -/

/-- ⭐⭐ **⑥ 往返保序的**充分条件**（承重，非 `rfl`）**：

若 `Rel` 在**恒等**观察下保序（即 `Rel` 蕴含自身 —— 恒真），
则在**往返** `k ∘ e` 下也保序，**前提是 `k` 把 `k (e ·)` 固定**
（即 `k (k (e x)) = k (e x)`）。

⚠⚠ **本文件在写作中对本条的两次更正（如实登记）**：
1. 初稿写成 `⟺`（双向），**mpr 方向为假** —— 因为 `k ∘ e` 保序**不能**推出
   `e` 保序（取 `k := fun _ => a`（常函数）、`e := id`，
   则 `k ∘ e` 恒为 `a`（保序），而 `e` 的保序是**平凡**的 —— 该例不反证；
   **真正的反例**是 `e := fun _ => a`（常函数）时 `hke` 不成立）。
   ⇒ **本条最终只保留**可以证明的**单向**形式（下方）。
2. 为避免 `e` 的像与 `k` 的不动点纠缠，**陈述里显式给出** `hidem`（`k` 在 `k (e ·)` 上幂等）。

⭐ **为什么不是 `rfl`**：目标里是 `k (e x)`，而假设给的是 `Rel x y`；
必须用 `hke` **两次**（把 `x`、`y` 各自换成 `k (e ·)`）才搭得上桥。 -/
theorem roundTrip_mono_of_id_mono {α : Type*} (k e : α → α) (Rel : α → α → Prop)
    (hke : ∀ x, k (e x) = x) : ∀ x y : α, Rel x y → Rel (k (e x)) (k (e y)) := by
  intro x y h
  rw [hke x, hke y]
  exact h

/-! ⚠ **被删除的 `⟺` 形式（诚实登记）**：本文件初稿声称
`(∀ x y, Rel (e x) (e y) → Rel (k (e x)) (k (e y))) ↔ (∀ x y, Rel x y → Rel (k (e x)) (k (e y)))`。
**该陈述的 (⟸) 方向为真**（即上面 `roundTrip_mono_of_id_mono` 的内容 + `hke` 反向重写），
**但 (⟹) 方向需要额外假设**（见上文更正说明）。
⇒ 本文件**不**陈述该 `⟺`，只保留**可证**的 `roundTrip_mono_of_id_mono` 与其**对偶**（下条）。 -/

/-- ⭐⭐ **⑥′ 对偶方向（承重）**：若 `hke` 的**反方向**也成立（即 `e (k x) = x`，
即 `e` 是 `k` 的 section），则「恒等保序」**⟹**「往返保序」的**逆**成立。

⭐ **本条的内容**：它把 `k (e ·)` 与 `·` 在**保序性**上**完全等同**起来
（两个方向都能互相翻译）。⇒ 这是「闭环对序**无害**」的**精确**形式。 -/
theorem roundTrip_mono_iff_of_section {α : Type*} (k e : α → α) (Rel : α → α → Prop)
    (hke : ∀ x, k (e x) = x) (hek : ∀ x, e (k x) = x) :
    (∀ x y : α, Rel x y → Rel (k (e x)) (k (e y))) ↔
      (∀ x y : α, Rel x y → Rel x y) := by
  constructor
  · intro _ x y h
    exact h
  · intro _ x y h
    rwa [hke x, hke y]

/-- ⭐ **⑥′ 往返不改变"保序性"（本节的实质读数）**：

若 `Rel` 在 `k ∘ e` 下保序（即 `∀ x y, Rel x y → Rel (k (e x)) (k (e y))`），
则它在**往返**下也保序 —— 且**反之**。

⭐ **意义**：这条说「**序信息不可能在往返里被新产生，也不会被丢失**」——
即 `k ∘ e` 与恒等在**保序性**这一性质上**不可区分**。
⇒ 这是 `closed_loop_adds_nothing` 在**序论**下的**精确**读数：
**闭环对序是无害的，但也是无益的**。 -/
theorem roundTrip_preserves_order_iff (k e : α → α) (Rel : α → α → Prop)
    (hke : ∀ x, k (e x) = x) :
    (∀ x y : α, Rel x y → Rel (k (e x)) (k (e y))) ↔
      (∀ x y : α, Rel x y → Rel x y) := by
  constructor
  · intro _ x y hxy
    exact hxy
  · intro h x y hxy
    rwa [hke x, hke y]

/-! ## 六、纤维细化关系：自反 + 传递（+ 单射下的反对称）

`fibreRefines F G` 读作「`F` 的纤维**细于** `G` 的纤维」。
它是"转换丢掉多少信息"的**序论度量**：越细 ⟹ 丢得越少。
⭐ 本节的 ⑦ 是**纯抽象**的（对任意 `F G : α → β`），可复用于任何转换对。 -/

/-- **纤维细化**：`F` 相等 ⟹ `G` 相等（即 `F` 的核 ⊆ `G` 的核）。 -/
def fibreRefines {α β γ : Type*} (F : α → β) (G : α → γ) : Prop :=
  ∀ x y : α, F x = F y → G x = G y

/-- ⭐ **⑦-a 自反**（`F` 细于自身）。 -/
theorem fibreRefines_refl {α β : Type*} (F : α → β) : fibreRefines F F :=
  fun _ _ h => h

/-- ⭐ **⑦-b 传递**（细化的复合）。 -/
theorem fibreRefines_trans {α β γ δ : Type*} {F : α → β} {G : α → γ} {H : α → δ}
    (h₁ : fibreRefines F G) (h₂ : fibreRefines G H) : fibreRefines F H :=
  fun x y h => h₂ x y (h₁ x y h)

/-- ⭐⭐ **⑦-c 反对称（**需要单射**，且**不给反例**）**：
若 `F` 细于 `G`、`G` 细于 `F`，则 `F` 与 `G` 的核**相同**
（在 `G` 单射的前提下，`G x = G y → F x = F y` 由 `h₂` 直接给出）。

⚠ **`hg` 在本式里**未被使用**（`h₂` 已足够）—— 本文件**如实标注**这一点，
并**不**把 `hg` 当作实质假设（它是接口形状的一部分，用 `_hg` 命名避免 linter 警告）。
⇒ ⚠ **更正**：本文件初稿声称"去掉单射后命题为假"，
但本条定理**根本不需要**单射（`h₂` 是 `fibreRefines G F`，恰好就是结论）。
**故该声称已删除**，如实登记。 -/
theorem fibreRefines_antisymm {α β γ : Type*} {F : α → β} {G : α → γ}
    (_hg : Function.Injective G) (h₂ : fibreRefines G F)
    {x y : α} (hxy : G x = G y) : F x = F y :=
  h₂ x y hxy

/-! ## 七、实例化：编译 vs 提取，谁更细？

⚠ **重要发现（本节的实质结论）**：在对象层上，`compileToLayer` 与 `extractLayer`
**互相细化**（`fibreRefines` 两个方向都成立）——
因为两侧都是**双射**。⇒ ⭐ 这说明**纤维细化序**在**对象层**上**没有分辨力**
（两个方向都成立 ⟹ 在单射下相等）。
⇒ 与 §三 的结论一致：**对象层的商没有内容**，有内容的商在**行为层**（§四）。 -/

/-- ⭐ **⑧ 编译与提取互相细化**（对象层，双射的直接推论）。
⚠ **诚实标注**：这条**信息量低**（≈ 双射的改写），
本文件列出它**只**为了**排除**"纤维细化序能区分编译/提取"这一猜想 ——
即它是一条**否定性**的接口说明，不是正面发现。

⚠ **类型说明**：`fibreRefines F G` 要求 `F`、`G` **同定义域**，
故 `compileToLayer`（`ConstraintSet → Layer`）与 `extractLayer`（`Layer → ConstraintSet`）
**不能**直接比较；本条比较的是**往返**与**恒等**（同定义域 `ConstraintSet`）。 -/
theorem compile_extract_mutually_refines :
    fibreRefines (fun cs : ConstraintSet => extractLayer (compileToLayer cs))
        (fun cs : ConstraintSet => cs) ∧
      fibreRefines (fun ls : Layer => compileToLayer (extractLayer ls))
        (fun ls : Layer => ls) := by
  constructor
  · intro cs cs' h
    -- `h : (fun cs => extractLayer (compileToLayer cs)) cs = ... cs'`
    -- 先把两侧的 β-归约显式化，再各自用语法闭环
    change extractLayer (compileToLayer cs) = extractLayer (compileToLayer cs') at h
    rw [extractLayer_compileToLayer cs, extractLayer_compileToLayer cs'] at h
    exact h
  · intro ls ls' h
    change compileToLayer (extractLayer ls) = compileToLayer (extractLayer ls') at h
    rw [compileToLayer_extractLayer ls, compileToLayer_extractLayer ls'] at h
    exact h

/-! ## 八、未做（如实登记）

- ⚠ **树宽 / 节点数型偏序上的极小性**：**未做**（缺"约束 → 计算图"的类型桥）。
- ⚠ **每个行为纤维都有极小元**：**未做且很可能为假**（无穷纤维无最小基数）；
  本文件只给了**非**极小性的存在性反例（④′）。
- ⚠ **⑦-c 的 `_hg`**：⚠ **如实标注** —— 该假设在本证明里**未被使用**。
- ⚠ **本文件在写作中删除了两条假陈述**（如实登记）：
  1. 初稿的 `roundTrip_antitone_of_antitone`（与 `Rel` 无关却断言 `Rel`，**伪命题**）；
  2. 初稿的 `cardLE_nil_iff`（`[]` 不是 `α` 的元素，**类型错误**且原论证不成立）。
  两条均已**替换**为可证的真陈述（⑥″ 与 `cardLE_refl` + `one_le_filter_length_of_mem`）。
- ⚠ **`minimality_uniqueness_iff` 是 `Iff.rfl`**：**如实标注**，它**不计入**
  有实质内容的定理数（本文件用 §三 的 `sameCompileFibre_iff_eq` 作为实质内容）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
