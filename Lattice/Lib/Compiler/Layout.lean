import Lattice.Core.PartialSection
import Lattice.Lib.Compiler.IRWeightsBridge
import Lattice.Lib.Compiler.GridAlgebra

/-!
# **产物契约：布局、语义域、构造配方，以及**部分**求值**

## 这个文件回答规划 P0-a 的那一问

规划 §4.1 要求产物携带 `layout` / `weights` / `domain` / `eval` / `recipe`，并规定：
**「`eval` 必须与 `layout` 一致；只有 `weights` 而缺 `layout` 与 `recipe` 的产物不得进入行为级定理。」**

本文件把那条约束做成**类型**，而不是靠文档约束：

- `layout` 的类型是 `Lattice.Core.PartialSection (ℕ → Segment) (ℕ → ℝ)`，
  即「编码全、解码部分、解码是编码的左逆、编码单射」——**这正是第 1036 轮那个抽象的一个实例**；
- `eval` **不是字段**，而是由 `layout.extract` 与 `recipe.n` **派生**的函数。

**⇒ 为什么这一点重要：`Runtime/VerificationLoop.objective` 曾经是**自由字段**，
于是「再注入」在 508 次提交里只是一个没人用的定义（第 1042 轮实测）。
把 `eval` 写成派生函数，使同一个错误**在类型层不可重复**：没有 layout 就没有载荷，没有载荷就没有求值。**

## 为什么 `eval` 返回 `Option`

**因为 `layout.extract` 返回 `Option`。** 若把求值写成 `ℝ`，就必须在某处**猜**一个值来填提取失败的情形；
那正是规划 §4.2 禁止的「`none` 被当成普通值」。

**⇒ 本文件让失败**从布局一路显式传到求值**：`eval A x = none` 当且仅当
「按 `A` 自己的布局，`A.weights` 解不出分段族」。调用者无法在不解码的情况下拿到一个数。**

## 与既有 `Core/ModelArtifact.lean` 的关系

那个 `ModelArtifact` 是「拓扑 + 适配该拓扑的权重」（`arch` + `weights : Weights arch`），
它约束的是**形状**；本文件约束的是**解释**。二者互补，本文件不替换它。
-/

namespace Lattice.Lib.Compiler

open Lattice.Core

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge

/-- **语义域**：行为比较所依据的区间。

**⇒ 只带 `lo ≤ hi` 这一条，因为本层只关心「在哪比较」；
`gridEval` 在任意 `x` 上都有定义，故域是**承诺范围**而非定义域。** -/
structure SemDomain where
  /-- Lower endpoint. -/
  lo : ℝ
  /-- Upper endpoint. -/
  hi : ℝ
  /-- The domain is not inverted. -/
  lo_le_hi : lo ≤ hi

/-- **构造配方**：产生该载荷时实际使用的参数。

**⇒ `n` 是网格参数，`hn` 是它非零的证据。把 `hn` 放进结构而不是当作定理前提，
是因为 `segmentIndex n x` 在 `n = 0` 时无意义——**边界条件必须在产物里就有定义**，而不是留给调用者。** -/
structure CompileRecipe where
  /-- The grid parameter actually used. -/
  n : ℕ
  /-- **The parameter is usable**: `0 < n`. -/
  hn : 0 < n

/-- **网格布局：一个 `PartialSection`。**

**⇒ 四个字段逐条对应既有定理：**
- `compile := encodeGrid`（全函数，`IRWeightsBridge.lean:63`）
- `extract := decodeGrid`（`IRWeightsBridge.lean:67`）
- `retract := decodeGrid_encodeGrid`（在像上解码回到原族）
- `compile_injective := encodeGrid_injective`

**⇒ 于是「布局」不是一份新发明的约定，而是**已经证明过的那组性质**的打包。
这直接满足规划 D1：「消费者必须携带解码函数与布局参数」。** -/
noncomputable def gridLayout : PartialSection (ℕ → Segment) (ℕ → ℝ) where
  compile := encodeGrid
  -- **`decodeGrid` is TOTAL (`IRWeights → ℕ → Segment`): reading two positions per segment cannot fail.
  -- So the layout's `extract` wraps it in `some`, and the `Option` in the type is genuinely unused HERE --
  -- which is exactly the difference between this layout and a layout whose decoding can fail.**
  extract := fun w => some (decodeGrid w)
  retract := fun g => by
    show some (decodeGrid (encodeGrid g)) = some g
    rw [decodeGrid_encodeGrid]
  compile_injective := encodeGrid_injective

/-- **被求值的产物。**

**⇒ 五个契约项里 `eval` **不在字段中**：它是派生的（见 `decodedFamily` 与 `eval`）。
所以「只带权重、解释不明」的产物**无法构造出求值**，这正是规划 §4.1 那条约束的类型化。** -/
structure EvaluatedArtifact where
  /-- **How the payload is to be interpreted.** -/
  layout : PartialSection (ℕ → Segment) (ℕ → ℝ)
  /-- The numeric payload, uninterpreted. -/
  weights : ℕ → ℝ
  /-- The interval on which behaviour is promised. -/
  domain : SemDomain
  /-- **The parameters actually used to build the payload.** -/
  recipe : CompileRecipe

namespace EvaluatedArtifact

/-- **载荷（派生，且**部分**）**：按该产物**自己的**布局解释其权重。

**⇒ 这是「同一底层类型、不同解释」的落点：`decodedFamily` 不是 `weights`，而是
`layout.extract weights`，其类型是 `Option`。缺 layout 的对象根本没有这个函数。** -/
noncomputable def decodedFamily (A : EvaluatedArtifact) : Option (ℕ → Segment) :=
  A.layout.extract A.weights

/-- **求值（派生，且**部分**）**：解码出的分段族在网格参数下的取值。

**⇒ 两个来源都被产物固定：`decodedFamily` 来自 `layout`，`n` 来自 `recipe`。
调用者无法只给权重就得到求值；提取失败则求值也失败，**不填入任何默认值**。** -/
noncomputable def evalAt (A : EvaluatedArtifact) (x : ℝ) : Option ℝ :=
  A.decodedFamily.map (fun g => gridEval g A.recipe.n x)

/-- **由分段族构造产物**：用 `gridLayout` 编码，并记下所用的参数。

**⇒ 这是产物唯一的「从符号侧进入」的构造入口：调用者必须先给出**分段族**，
而不能只给权重——于是「解释」先于「载荷」。** -/
noncomputable def ofSegments (g : ℕ → Segment) (dom : SemDomain) (r : CompileRecipe) :
    EvaluatedArtifact where
  layout := gridLayout
  weights := encodeGrid g
  domain := dom
  recipe := r

/-- **⭐ 由分段族构造的产物恒可求值，且值就是该族的网格求值。**

**⇒ 这条不是定义展开：它用 `PartialSection.retract`（即 `decodeGrid_encodeGrid`）证明
`decodedFamily (ofSegments g …) = some g`，再由 `Option.map` 得到 `some (gridEval g n x)`。**

**⇒ 它的内容正是规划 A.6 的第一条验收：「仿射样例误差为零，且该零误差来自**构造**而非定义」——
这里证明的是**求值忠于被编译的族**，且**失败分支在这条路上不出现**（`some`，不是「恰好非 none」）。** -/
theorem evalAt_ofSegments (g : ℕ → Segment) (dom : SemDomain) (r : CompileRecipe) (x : ℝ) :
    (ofSegments g dom r).evalAt x = some (gridEval g r.n x) := by
  -- **`show` names the layout's own `compile`, not `encodeGrid`: they are defeq but `rw` matches
  -- syntactically, and `retract` is stated over `layout.compile`.**
  show (gridLayout.extract (gridLayout.compile g)).map (fun h => gridEval h r.n x)
      = some (gridEval g r.n x)
  rw [gridLayout.retract g]
  rfl

/-- **⭐ 提取失败与求值失败是同一件事。**

**⇒ `(A.evalAt x).isSome ↔ (A.decodedFamily).isSome`：`eval` 没有引入**任何**新的失败原因，
它只是把布局的失败**原样传下去**。**

**⇒ 这条使规划 §4.2 的「失败语义」可判定：`eval = none` 的唯一解释是
「按该产物的布局，其权重解不出分段族」，而不是「域外」「参数非法」或「实现未完成」——
后三者在本结构里根本不可能发生（`n > 0` 由 `recipe.hn` 保证，域不限制求值）。** -/
theorem evalAt_isSome_iff_decoded_isSome (A : EvaluatedArtifact) (x : ℝ) :
    (A.evalAt x).isSome ↔ A.decodedFamily.isSome := by
  cases h : A.decodedFamily with
  | none => simp [evalAt, h]
  | some g => simp [evalAt, h]


/-- **求值只依赖载荷与参数，不直接依赖权重。**

**⇒ 若两个产物的载荷与参数相同，则它们在每一点上的求值相同。
**⇒ 这条把「行为由解释决定」写成可引用的事实：**权重不同但载荷相同的两个产物行为完全一样**，
故「比较权重」不是比较行为；要比较行为必须比较 `decodedFamily` + `n`。** -/
theorem evalAt_congr_of_decoded_eq (A B : EvaluatedArtifact)
    (hp : A.decodedFamily = B.decodedFamily) (hn : A.recipe.n = B.recipe.n) (x : ℝ) :
    A.evalAt x = B.evalAt x := by
  show A.decodedFamily.map (fun g => gridEval g A.recipe.n x)
      = B.decodedFamily.map (fun g => gridEval g B.recipe.n x)
  rw [hp, hn]

end EvaluatedArtifact

end Lattice.Lib.Compiler