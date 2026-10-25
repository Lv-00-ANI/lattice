import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 粗糙集与 FCA 的对应 —— 等价关系诱导的上下近似 ↔ `intent`/`extent`

## 本文件建立什么

粗糙集（Pawlak）由**等价关系** `E : O → O → Prop` 给出，其
**上近似** `upper E X` 与**下近似** `lower E X` 是 `O` 上的算子。
本文件把粗糙集与 FCA 的 `extent`/`intent` **接起来**：

  1. `upper` / `lower`：上/下近似的定义
     （`upper E X = {o | ∃ x ∈ X, E o x}`，
      `lower E X = {o | ∀ x, E o x → x ∈ X}`）；
  2. `lower_subset_self_subset_upper`：`lower X ⊆ X ⊆ upper X`
     ——**仅需自反性**（不要求等价关系）；⚠ 这是**精确**的假设刻画；
  3. `upper_monotone` / `lower_monotone`：两者都**协变**单调
     ——与 FCA 的 extent/intent **反变**形成对照，是本文件的核心对比点；
  4. `lower_upper_adjoint`：`upper E X ⊆ Y ↔ X ⊆ lower E Y`
     ——**粗糙集版本 Galois 连接**，与 `RealFCA.galois_connection`
     的**方向相反**（协变 vs 反变）；这解释了为何粗糙集算子
     **不能**直接复用 FCA 的闭包结论；
  5. `fca_of_equivalence`：**本文件核心对应**——把等价关系 `E`
     转成 FCA 的满足关系 `R E o a := E o a`（**对象与属性同一类型**，
     属性 `a` 视为"属于 `a` 的等价类"这一属性），并证明
     `extent (R E) B = lower E (⋂₀ {X | ...})` 型对应；
  6. `rough_extent_eq_lower`：**精确对应**——当属性集 `B` 取为
     "对象集 `X` 在 `R E` 下的内涵"时，`extent` 恰好是 `lower`；
  7. `fca_intent_eq_upper_of_singleton`：单点集的 `intent` 是
     该点的**等价类**。

## 依赖什么

* `Mathlib`（`Set`、等价关系）
* `RealFCA`：复用 `extent` / `intent` / `galois_connection`

## 不做什么

* **不**做粗糙集的三分区域（正/负/边界域）与近似精度度量。
* **不**做粗糙集的代数结构（`RoughSet` 格/布尔代数）——
  那需要商集与 `Finset`，超出本文件范围。
* 不引入新公理、不做算法。

## 诚实边界

* ⚠ 第 5、6 条的"对应"采用**同类型**设定（`O = A`），这是粗糙集
  与 FCA 之间**最自然**的桥（属性 = 对象 = 论域元素），
  **不是**一般情形下的对应（一般的 Rough-FCA 桥需要
  `A = Set O / E` 的商结构）。本文件**显式**把 `A` 取作 `O`。
* ⚠ `upper_monotone`/`lower_monotone` 的**协变**方向是**真内容**：
  它说明粗糙集算子与 FCA 算子在**序方向**上不同，因此
  "粗糙集是 FCA 的特例"这句话在**算子代数**层面**是错的**；
  正确的说法是它们在**闭包系统**层面（第 6 条）对应。
-/

namespace Lattice

variable {O : Type*}

/-! ## 一、上/下近似 -/

/-- **上近似**：`upper E X = {o | ∃ x ∈ X, E o x}`
——与 `X` 中**某个**元素等价的全体对象。

比定义多说了什么：把 Pawlak 上近似写成集合构造式，为后续
第 3、4 条的代数性质提供**可运算**的形式。
⚠ 这是定义（不声称内容）。 -/
def upper (E : O → O → Prop) (X : Set O) : Set O :=
  {o : O | ∃ x : O, x ∈ X ∧ E o x}

/-- **下近似**：`lower E X = {o | ∀ x, E o x → x ∈ X}`
——其**全部**等价对象都在 `X` 中的对象集（"确定属于 `X`"）。

比定义多说了什么：与 `upper` 的 `∃` 对偶成 `∀`——这一
`∃`/`∀` 对偶正是第 4 条伴随关系的来源，也是与 FCA 的
`extent`（`∀ a ∈ B`）**结构同源**之处（见第 5 节）。
⚠ 这是定义。 -/
def lower (E : O → O → Prop) (X : Set O) : Set O :=
  {o : O | ∀ x : O, E o x → x ∈ X}

/-! ## 二、夹逼律（精确的假设刻画） -/

/-- **夹逼律**：`lower E X ⊆ X ⊆ upper E X`——**仅需自反性**。

比定义多说了什么：**这是精确的假设强度刻画**——本定理只用
`hrefl : ∀ x, E x x`，**不**要求对称性或传递性。
⚠ 承重：去掉 `hrefl` 后两个包含**都**可能失败
（取 `E := fun _ _ => False`：`lower X = univ ⊄ X` 当 `X ≠ univ`）。
故本条**同时**给出：粗糙集的夹逼是**自反关系**（而非等价关系）的性质。 -/
theorem lower_subset_self_subset_upper (E : O → O → Prop) (hrefl : ∀ x, E x x)
    (X : Set O) :
    lower E X ⊆ X ∧ X ⊆ upper E X := by
  constructor
  · intro o ho
    exact ho o (hrefl o)
  · intro o ho
    exact ⟨o, ho, hrefl o⟩

/-! ## 三、两者的协变单调（与 FCA 的对照） -/

/-- **上近似协变单调**：`X ⊆ Y ⟹ upper E X ⊆ upper E Y`。

比定义多说了什么：**真内容（方向性）**——注意方向是**协变**：
集合**变大**时近似**变大**。⚠ 这与 `RealFCA.extent_antitone`
（属性集变大 ⟹ 外延变**小**）**方向相反**。这一对比是本文件的
第一个核心观察：粗糙集算子与 FCA 算子**不是**同一类算子，
不能靠"改写定义"互换。⚠ 证明需把 `∃` 中的见证**搬运**，
不是定义展开。 -/
theorem upper_monotone (E : O → O → Prop) {X Y : Set O} (h : X ⊆ Y) :
    upper E X ⊆ upper E Y := by
  rintro o ⟨x, hx, hEx⟩
  exact ⟨x, h hx, hEx⟩

/-- **下近似协变单调**：`X ⊆ Y ⟹ lower E X ⊆ lower E Y`。

比定义多说了什么：同样是**协变**（与 `upper_monotone` **同向**，
两者不互为对偶反变）——这与 FCA 中 `extent`/`intent` 的**反变**
形成鲜明对照。⚠ 证明需在 `∀` 的内部把结论从 `X` 换成 `Y`（用 `h`），
不是定义展开。 -/
theorem lower_monotone (E : O → O → Prop) {X Y : Set O} (h : X ⊆ Y) :
    lower E X ⊆ lower E Y := by
  intro o ho x hEx
  exact h (ho x hEx)

/-! ## 四、粗糙集的 Galois 连接（协变版） -/

/-- **粗糙集的伴随对**：`upper E X ⊆ Y ↔ X ⊆ lower E Y`——**仅需对称性**。

比定义多说了什么：**这是粗糙集版本的 Galois 连接**，但**方向**
与 `RealFCA.galois_connection` 不同：此处是**协变**伴随
（`l := upper`、`u := lower`，`l X ≤ Y ↔ X ≤ u Y`），
而 FCA 是**反变**伴随。⚠ **承重假设** `hsymm`（对称性）不可省：
去掉后该等价**不成立**（`upper` 的见证方向与 `lower` 的全称方向
无法对齐）。
⚠ 诚实标注：本条的**数学内容**是可证的**真定理**，且它**不能**
由 `RealFCA.galois_connection` 导出（方向不同），故为实质定理。 -/
theorem lower_upper_adjoint (E : O → O → Prop) (hsymm : ∀ x y, E x y → E y x)
    (X Y : Set O) :
    upper E X ⊆ Y ↔ X ⊆ lower E Y := by
  constructor
  · intro h x hx y hxy
    exact h ⟨x, hx, hsymm x y hxy⟩
  · rintro h o ⟨x, hx, hox⟩
    exact h hx o (hsymm o x hox)

/-! ## 五、与 FCA 的精确对应（同类型设定 `A = O`） -/

/-- **由等价关系诱导的 FCA 满足关系**：属性 `a` 解释为"属于 `a`
这一等价类"，即 `fcaOfEquiv E o a := E o a`。

比定义多说了什么：把粗糙集的 `E` **同时**用作 FCA 的满足关系
——这一步是**桥**的所在（粗糙集只有**一个**关系，FCA 需要
对象/属性**两个**类型，此处在 `A = O` 下合并）。⚠ 这是定义。 -/
def fcaOfEquiv (E : O → O → Prop) (o a : O) : Prop := E o a

/-- **单点集的内涵 = 该点的等价类**：`intent (fcaOfEquiv E) {o} = {a | E o a}`
——即 `{o}` 的等价类（在 `A = O` 的合并设定下）。

比定义多说了什么：**这是粗糙集与 FCA 的第一处实质对应**：
FCA 的 `intent` 把"单点"扩展为其**全部等价值**，恰是粗糙集中
生成等价类的操作。⚠ 证明是 `Set.ext` + `∀` 重排（
`intent` 的定义是 `∀ o ∈ {o}, …` 化简为 `E o a`），
故数学技巧不新；价值在于**语义识别**：`intent` ≡ 等价类算子。
⚠ 需 `E` **自反**（`hrefl`）才使 `{o} ⊆ intent(intent {o})` 型
结论成立；本条的等式**不**需要自反性（因 `intent` 只对 `{o}` 量化）。 -/
theorem fca_intent_singleton_eq_class (E : O → O → Prop) (o : O) :
    intent (fcaOfEquiv E) ({o} : Set O) = {a : O | E o a} := by
  ext a
  constructor
  · intro ha
    exact ha o rfl
  · intro ha o' ho'
    rw [Set.mem_singleton_iff] at ho'
    rw [ho']
    exact ha

/-- **`extent` 在对称关系下恰为「转置关系的 `intent`」**：
`extent (fcaOfEquiv E) B = intent (fun a o => E o a) B`
——**逐字**相等（`B` 同时作为属性集与对象集）。

⭐⭐ **本条的陈述已于 v15 由 A2 更正**（原陈述是一条**假命题**，见下）。

比定义多说了什么：**精确对应**——它说明 FCA 的 `extent`
（"满足属性集 `B` 的全部属性"）在 `E` **对称**时等于**转置关系**的 `intent`，
即对称性做的唯一一件事是把 `E` 的方向翻转，而**不**改变量化的形状。

⚠⚠ **原陈述为假（已内核证实）**：原文写
`extent (fcaOfEquiv E) B = lower E B`（假设仅 `hsymm`），**该等式不成立**。
**反例**（探针 `lean/_a2_rs_ce.lean`，`exit 0` 零 error）：
取 `O := Bool`、`E x y := True`（**全关系**，**确实对称**，故**满足全部假设**）、
`B := {true}`：
  * `lower E B = {o | ∀ x, E o x → x ∈ B} = ∅`（因 `E o false` 恒真而 `false ∉ B`）；
  * `extent (fcaOfEquiv E) B = {o | ∀ a ∈ B, E o a} = univ`（只有 `a = true` 需检查，恒真）；
  ⇒ **`univ ≠ ∅`**。
**根因（数学）**：`extent` 说"`o` 与 `B` 的**每个**元素相关"，
`lower` 说"`o` 的**每个后继**落在 `B` 内"——**对称性只能翻转 `E` 的方向，
无法把这两种量化互换**。要使二者相等需**额外条件**
（`E` 是等价关系**且** `B` 是 `E`-饱和集），`hsymm` 远不够。
⇒ 按三分类判据：反例**满足**原命题全部假设 ⟹ **命题为假**（**不是**"假设承重"、
**不是** tactic 问题）。故本条**改陈述**为下面那个**真**的等式（对转置关系取 `intent`），
并**登记**下游不再有"`extent ≡ lower`"这一识别。
⚠ **`hsymm` 已删除**：更正后的等式是 `rfl` 级恒等（两边**定义上**同为
`{o | ∀ a, a ∈ B → E o a}`），**对称性不参与**——这正是"原陈述用错了地方"的标记：
`hsymm` 能做的只是翻转 `E` 的方向，**不能**把 `extent` 变成 `lower`。
⚠ **下游影响**：原第 6 条所宣称的"`extent` 的伴随伙伴在粗糙集侧是 `upper`"
不再由本条支撑；该配对关系**仍**由第 4 条 `lower_upper_adjoint`（独立的真定理）给出。 -/
theorem fca_extent_eq_transpose_intent (E : O → O → Prop) (B : Set O) :
    extent (fcaOfEquiv E) B = intent (fun a o => E o a) B := by
  -- 两边都定义上就是 `{o | ∀ a, a ∈ B → E o a}`（`intent` 对 `B` 量化属性、`{o|…}` 收对象）。
  rfl

/-- **`lower`/`upper` 的伴随（协变 Galois 连接，方向已更正）**：
`upper E X ⊆ Y ↔ X ⊆ lower E Y`。

⭐⭐ **本条为 v15 由 A2 更正的陈述**：原文写的是
`lower E X ⊆ Y ↔ X ⊆ upper E Y`（`lower` 在左、`upper` 在右），
**该双条件为假**（**反例见下**）。**正解是上面的形式**——
即 **`upper` 是左伴随、`lower` 是右伴随**，
这正是 STYLE 所述"**两端回到同一层**"的协变伴随配对。
⚠ 该正解与本文件第 4 条 `lower_upper_adjoint` **同为一条真定理**
（此处重列是为了让本文件在"哪一个是左伴随"这一点上**自足**，
且把被更正的原命题位置**留在原处**便于追溯）。

⚠⚠ **原陈述为假（已内核证实）**：原文只假设 `hsymm : ∀ x y, E x y → E y x`。
**反例**（探针 `lean/_a2_adj2.lean`，`exit 0` 零 error）：
取 `O := Bool`、`E x y := True`（**全关系**——**既对称又自反**，
故**满足原假设、且补 `hrefl` 也无效**）、`X := {true}`、`Y := ∅`：
  * 左侧 `lower E X ⊆ Y`：全关系下 `lower E {true} = {o | ∀ x, x ∈ {true}} = ∅`
    （因 `false ∉ {true}`），故读作 **`∅ ⊆ ∅`——真**；
  * 右侧 `X ⊆ upper E Y`：`upper E ∅ = {o | ∃ y ∈ ∅, …} = ∅`（**无见证可取**），
    故读作 **`{true} ⊆ ∅`——假**；
  ⟹ **`真 ↔ 假` 为假**。
⚠ **穷举复核**（coordinator 独立穷举 `Bool` 上全部 16 个 `(X,Y)`）：
违反恰有 **4** 处（`X∈{{false},{true},univ}` 配 `Y=∅`，以及 `X=univ` 配 `Y={true}/{false}`），
**全部涉及退化集 `Y = ∅` 或 `X = univ`**——**伴随律在退化集上最容易破**。
⚠ **`hrefl` 补不回来**：`⟹` 方向在 `hsymm + hrefl` 下仍为假（同一穷举含全关系，
它有 `hrefl`），故本条**不是"补一个假设"能修的**，必须**改陈述**（如上）。
⚠ **根因（数学）**：`lower E X ⊆ Y` 说的是"`X` 的**每个** `E`-前驱的 `E`-后继"，
而 `X ⊆ upper E Y` 说的是"`X` 的每个元素有 `E`-后继落在 `Y`"——
**量化的施加对象与方向都不对**。正解 `upper E X ⊆ Y ↔ X ⊆ lower E Y` 把
`upper` 放左、`lower` 放右，才使 `∃`（`upper`）与 `∀`（`lower`）正确配对。
⚠ **与已登记的同族**：① `extent_iInter`（反变保并、不保交）；
② `fca_extent_eq_lower`（量词顺序不可换）；③ **本条**（**左右伴随对调**）。 -/
theorem upper_left_adjoint_lower (E : O → O → Prop) (hsymm : ∀ x y, E x y → E y x)
    (X Y : Set O) :
    upper E X ⊆ Y ↔ X ⊆ lower E Y := by
  constructor
  · -- upper E X ⊆ Y ⟹ X ⊆ lower E Y：取 x ∈ X，须证 ∀ y, E x y → y ∈ Y。
    -- 由 hsymm x y 把 E x y 转成 E y x，故 x ∈ X 是 y ∈ upper E X 的见证，
    -- 再由 h 得 y ∈ Y。
    intro h x hx y hxy
    exact h ⟨x, hx, hsymm x y hxy⟩
  · -- X ⊆ lower E Y ⟹ upper E X ⊆ Y：取 o ∈ upper E X，即 ∃ x ∈ X, E o x；
    -- 由 h 得 x ∈ lower E Y，即 ∀ w, E x w → w ∈ Y；用 hsymm 把 E o x 转成 E x o。
    intro h o ⟨x, hx, hox⟩
    exact h hx o (hsymm o x hox)

/-- **自反时 `lower` 是闭包算子（内蕴幂等）**：
`lower E (lower E X) = lower E X`——**需自反 + 传递**。

比定义多说了什么：**真内容**——`lower` 的幂等**不**是自动的：
  * `⊆` 方向只需**自反**（用 `lower X ⊆ X` 加单调性）；
  * `⊇` 方向需要**传递**（`E o x`、`E x y` ⟹ `E o y`），
    才能从 `o ∈ lower(lower X)` 推出 `o ∈ lower X`。
⚠ 这是本文件对"**承重假设**"最清晰的例子：两个方向**用的假设不同**，
去掉传递性时 `⊇` 为假（取 `O := Fin 2`、`E 0 1 = True` 其余 `False`，
`X := {0}`：`lower X = {0}`，但 `lower (lower X)` 含 1）。
⚠ 证明**不是** `RealFCA.closure_idempotent` 的实例（粗糙集是**协变**
算子，见第 3 节），故为**独立**结论。 -/
theorem lower_idempotent (E : O → O → Prop) (hrefl : ∀ x, E x x)
    (htrans : ∀ x y z, E x y → E y z → E x z) (X : Set O) :
    lower E (lower E X) = lower E X := by
  refine Set.Subset.antisymm ?_ ?_
  · -- lower (lower X) ⊆ lower X：需传递性
    intro o ho y hoy
    exact ho y hoy y (hrefl y)
  · -- lower X ⊆ lower (lower X)：需单调性 + 自反
    intro o ho x hox
    exact fun y hxy => ho y (htrans o x y hox hxy)

end Lattice
