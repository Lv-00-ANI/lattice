/-
Copyright: LATTICE

# 可变宽度层的分析：`MLayer` 与 `NLayer` 的可微性

## 目标（第 158 轮规划的直接落实）

**第 158 轮实测：损失链 133 条声明中，106 条与宽度无关，只有 27 条依赖定宽 `AffineLayer`。**
**而 `Chain : ℕ → ℕ → Type`（`VariableNet.lean`）已经是正确的可变宽度载体。**

**本文件开始在那 27 条上工作，从最基础的一层做起。**

## ⚠ 一个实测出来的技术约束

**`Matrix (Fin m) (Fin n) ℝ` 【没有】`NormedAddCommGroup` 实例**（第 158 轮探针：
`failed to synthesize NormedAddCommGroup (Matrix (Fin m) (Fin n) ℝ)`），
**而 `Fin m → Fin n → ℝ` 【有】**。

**⇒ 参数空间的载体必须写成 `Fin m → Fin n → ℝ`，不能是 `Matrix`。
`Matrix` 只出现在 `mlayerAct` 的定义内部。**

**这与 `singleParams` 的选择一致**（它用 `Fin n → Fin n → ℝ` 而不是 `Matrix`），
**所以不是新发明，而是同一条约束在变宽情形下的重述。**

## 与定宽版的对应

| 定宽（`StackDerivative.lean`） | 本文件的可变宽度版 |
|:--|:--|
| `singleParams n` = `(Fin n → Fin n → ℝ) × (Fin n → ℝ)` | `mlayerParams m n` = `(Fin m → Fin n → ℝ) × (Fin n → ℝ)` |
| `differentiableAt_affineAct_params` | `differentiableAt_mlayerAct_params` |
| `differentiableAt_affineAct` | `differentiableAt_mlayerAct` |

**⚠ 关键差别**：**定宽版的参数类型只带一个 `n`（方阵）；变宽版必须同时带 `m` 与 `n`。
这使 `stackParams k n`（`Fin k →` 定长栈）【无法】直接推广——
宽度序列不再是常数，`Fin k →` 表达不了，必须用 `Chain`。**
-/
import Mathlib
import Lattice.Core.VariableNet
import Lattice.Core.VariableActLayer
import Lattice.Core.AnalysisHelper

open Matrix

namespace Lattice.Core

/-- **`MLayer` 的参数空间**——`m → n` 的权重（写成函数形式）加长度为 `n` 的偏置。

**⚠ 用 `Fin m → Fin n → ℝ` 而不是 `Matrix (Fin m) (Fin n) ℝ`：
后者没有 `NormedAddCommGroup` 实例，`fderiv` 无法作用。** -/
abbrev mlayerParams (m n : ℕ) : Type := (Fin m → Fin n → ℝ) × (Fin n → ℝ)

/-- **参数空间是赋范向量空间**——**`fderiv` 的前提**，由 `Pi`／`Prod` 实例自动给出。 -/
noncomputable instance instNormedAddCommGroupMlayerParams (m n : ℕ) :
    NormedAddCommGroup (mlayerParams m n) :=
  inferInstance

noncomputable instance instNormedSpaceMlayerParams (m n : ℕ) :
    NormedSpace ℝ (mlayerParams m n) :=
  inferInstance

/-- **把函数形式的权重送回 `MLayer`**。 -/
noncomputable def mlayerOf {m n : ℕ} (q : mlayerParams m n) : MLayer m n where
  W := fun i j => q.1 i j
  b := q.2

/-- **`mlayerAct` 的逐坐标展开**（转成函数的权重形式）。 -/
theorem mlayerAct_apply {m n : ℕ} (q : mlayerParams m n) (x : Fin m → ℝ) (j : Fin n) :
    mlayerAct (mlayerOf q) x j = (∑ i, q.1 i j * x i) + q.2 j :=
  rfl

/-- ⭐⭐ **`MLayer` 对【输入】可微**——**定宽版 `differentiableAt_affineAct` 的变宽对应。** -/
theorem differentiableAt_mlayerAct {m n : ℕ} (q : mlayerParams m n) (x : Fin m → ℝ) :
    DifferentiableAt ℝ (fun y : Fin m → ℝ => mlayerAct (mlayerOf q) y) x := by
  have hfun : (fun y : Fin m → ℝ => mlayerAct (mlayerOf q) y)
      = fun y : Fin m → ℝ => fun j => (∑ i, q.1 i j * y i) + q.2 j := by
    funext y
    funext j
    exact mlayerAct_apply q y j
  rw [hfun]
  fun_prop

/-- ⭐⭐ **`MLayer` 对【参数】可微**——**定宽版 `differentiableAt_affineAct_params` 的变宽对应。**

**参数类型是 `mlayerParams m n`（带两个宽度），而不是 `singleParams n`（只带一个）。**

**⚠ 证明用 `fun_prop`**：**手写的 `eval`／`apply` 链在 `Pi` 与 `Prod` 的嵌套上反复失配
（第 158 轮试了五轮），而 `fun_prop` 一次通过。** -/
theorem differentiableAt_mlayerAct_params {m n : ℕ}
    (q : mlayerParams m n) (x : Fin m → ℝ) :
    DifferentiableAt ℝ (fun g : mlayerParams m n => mlayerAct (mlayerOf g) x) q := by
  have hfun : (fun g : mlayerParams m n => mlayerAct (mlayerOf g) x)
      = fun g : mlayerParams m n => fun j => (∑ i, g.1 i j * x i) + g.2 j := by
    funext g
    funext j
    exact mlayerAct_apply g x j
  rw [hfun]
  fun_prop

/-- ⭐⭐⭐ **`MLayer` 的【联合】可微性**——**参数与输入同时变动。**

**这是定宽版 `differentiableAt_affineAct_joint` 的变宽对应，也是 `Chain` 上损失链的起点。** -/
theorem differentiableAt_mlayerAct_joint {m n : ℕ}
    (q : mlayerParams m n) (x : Fin m → ℝ) :
    DifferentiableAt ℝ
      (fun r : mlayerParams m n × (Fin m → ℝ) =>
        mlayerAct (mlayerOf r.1) r.2) (q, x) := by
  have hfun : (fun r : mlayerParams m n × (Fin m → ℝ) =>
        mlayerAct (mlayerOf r.1) r.2)
      = fun r : mlayerParams m n × (Fin m → ℝ) =>
          fun j => (∑ i, r.1.1 i j * r.2 i) + r.1.2 j := by
    funext r
    funext j
    exact mlayerAct_apply r.1 r.2 j
  rw [hfun]
  fun_prop

/-! ## `Chain` 的参数空间与 `act` 的可微性

**`Chain : ℕ → ℕ → Type` 的每一层宽度不同，所以它的参数空间是一个【依赖类型**。

**⚠ 两个技术要点（第 159 轮探针证实）：**

1. **必须用 `match` 形式而不是 equation compiler 的模式**——
   **`| _, _, .cons _ rest =>` 会报 `invalid pattern, variable 'n' occurred more than once`，
   而 `match c with | .cons (m := m') (n := n') _ rest =>` 能正确绑定这一层的宽度；**
2. **`Chain.cons` 的两个参数没有名字**，所以位置模式 `_ rest` 是唯一写法。 -/

/-- **把 `MLayer` 送回参数形式**——`mlayerOf` 的逆。 -/
def mlayerParamsOf {m n : ℕ} (l : MLayer m n) : mlayerParams m n :=
  (fun i j => l.W i j, l.b)

/-- **往返一致**：`mlayerOf` 与 `mlayerParamsOf` 互逆。 -/
theorem mlayerOf_mlayerParamsOf {m n : ℕ} (l : MLayer m n) :
    mlayerOf (mlayerParamsOf l) = l := by
  cases l
  rfl

/-- **`Chain` 的参数空间**——逐层累积的 `mlayerParams`。 -/
abbrev ChainParams : {m n : ℕ} → Chain m n → Type :=
  fun {m n} ch =>
    match ch with
    | .idf _ => PUnit
    | .cons (m := m') (n := n') _ rest => mlayerParams m' n' × ChainParams rest

/-- **恒等链的参数空间是 `PUnit`**（定义级）。 -/
theorem chainParams_idf (n : ℕ) : ChainParams (Chain.idf n) = PUnit :=
  rfl

/-! ### `abbrev` 而不是 `def`：一个被实测的决定

**`ChainParams` 必须是 `abbrev`**，**否则 `PUnit`／`Prod` 的实例【不会】穿过它传播**（第 160 轮实测）。

**⚠ 第 161 轮的探针修正了第 160 轮的一个判断**：
**`abbrev` 的归约足以让 `idf`、一层、两层、三层的 `cons` 都自动解出实例**
（`exact differentiableAt_snd` 直接通过）。
**第 160 轮的超时来自【手写的实例定义加 `attribute [instance]`】**，而那是错误的修法。** -/

/-- ⭐⭐ **`Chain` 的参数化作用**：从 `ChainParams ch` 取每一层的参数。

**⚠ 第二参数的类型是 `ChainParams ch`，随 `ch` 变——递归时 `p.2` 的类型正好是 `ChainParams rest`。** -/
noncomputable def Chain.actWith : {m n : ℕ} → (ch : Chain m n) → ChainParams ch →
    (Fin m → ℝ) → Fin n → ℝ
  | _, _, .idf _, _, x => x
  | _, _, .cons (n := n') _ rest, p, x => actWith rest p.2 (mlayerAct (mlayerOf p.1) x)

/-- **递归展开**（定义级）。 -/
theorem Chain.actWith_cons {m n n' : ℕ} (l : MLayer m n) (rest : Chain n n')
    (p : ChainParams (Chain.cons l rest)) (x : Fin m → ℝ) :
    Chain.actWith (Chain.cons l rest) p x
      = Chain.actWith rest p.2 (mlayerAct (mlayerOf p.1) x) :=
  rfl

/-- **恒等链的参数化作用是恒等**。 -/
theorem Chain.actWith_idf (n : ℕ) (p : ChainParams (Chain.idf n)) (x : Fin n → ℝ) :
    Chain.actWith (Chain.idf n) p x = x :=
  rfl

/-- ⭐⭐⭐ **`Chain.act` 对【输入】可微**——**第 159 轮证明，第 161 轮区域重写时【丢失**，
**第 177 轮恢复。**

**⚠ 这是一处【回归**：第 159 轮提交（`1a98716`）里有这条定理，
第 161 轮（`efb2d0f`）把整个「`abbrev` 说明 + `actWith`」区域重写时把它一并删掉了，
而第 163 轮随后在文档串里声称它「完整证明」存在——
**那是文档与代码脱节，第 177 轮同时修正了两者。** -/
theorem differentiableAt_chainAct : {m n : ℕ} → (ch : Chain m n) → (x : Fin m → ℝ) →
    DifferentiableAt ℝ (fun y : Fin m → ℝ => Chain.act ch y) x
  | _, _, .idf n, x => by
      have hid : (fun y : Fin n → ℝ => Chain.act (Chain.idf n) y) = id := by
        funext y
        exact Chain.act_idf y
      rw [hid]
      exact differentiableAt_id
  | _, _, .cons (m := m') (n := n') l rest, x => by
      have hstep : (fun y : Fin m' → ℝ => Chain.act (Chain.cons l rest) y)
          = (fun z : Fin n' → ℝ => Chain.act rest z) ∘ (fun y => mlayerAct l y) := by
        funext y
        rfl
      rw [hstep]
      exact (differentiableAt_chainAct rest _).comp x
        (differentiableAt_mlayerAct (mlayerParamsOf l) x)

/-! ### ⚠ 未闭合：`Chain.actWith` 的联合可微性

**目标**：`DifferentiableAt ℝ (fun r : ChainParams ch × (Fin m → ℝ) => Chain.actWith ch r.1 r.2) (p, x)`。

**第 161 轮实测到的确切障碍**：**定理的签名在归纳之前就要 `[NormedAddCommGroup (ChainParams ch)]`，
而 `ch` 那时是【变量】，类型类搜索无法归约（第 160 轮已测：超时）。**

**把实例作为显式参数（第 160 轮诊断的第二个候选）也不行**：
**`cons` 支的递归调用需要的是 `NormedAddCommGroup (ChainParams rest)`，
而调用方手里只有 `NormedAddCommGroup (ChainParams (Chain.cons l rest))`，
即一个 `Prod` 的实例——从它【取不出】第二分量的实例**（Lean 报类型不匹配）。

**⇒ 真正可行的修法是让 `ChainParams` 的实例由【构造】给出而不是由【搜索】给出**：
既然 `ChainParams (cons l rest) = mlayerParams _ _ × ChainParams rest`，
**就该在 `cons` 支用 `haveI` 把 `rest` 的实例【递归构造】出来**，
**而不是指望 `iA` 里含有它。**

**⚠ 但递归构造需要一个【返回实例值】的函数**，而第 160 轮试过——
**`inferInstanceAs` 在递归分量上超时。** **原因可能是 `ChainParams` 的 `match` 让
`inferInstanceAs` 的目标类型无法归约。**

**⇒ 下一步应当先把 `ChainParams` 改写成【不用 `match`】的形式**，
例如用一个显式的「宽度序列」`List ℕ` 加 `Sigma`，**使每一层的参数类型可直接计算。**
**那是一个定义层面的改动，第 162 轮做。** -//-! ### `actWith` 的联合可微性：为什么签名写法行不通，以及正确的写法

**第 161 轮实测：定理的签名 `{m n} → (ch : Chain m n) → [...] → ...` 在归纳【之前】
就要解 `NormedAddCommGroup (ChainParams ch)`，而那时 `ch` 是变量，搜索无法展开，超时。**

**本轮又实测：把实例写成显式参数也不行**——
**`cons` 支的递归调用需要 `rest` 的实例，而调用方只有 `cons l rest`（一个 `Prod`）的实例，
取不出第二分量。手写 `ParamsNAGC` 反而触发
`synthesized type class instance is not definitionally equal`。**

**⇒ 事实上，对【具体】形状类型类搜索完全胜任**：
**一层、两层、三层、四层的 `cons` 伸进 `differentiableAt_snd` 都直接通过。**

**⇒ 所以正确的写法不是让定理对变量 `ch` 成立、再靠递归补实例，
而是把可微性【作为 `Chain` 递归的一部分】陈述，让每次递归都在更浅的具体形状上工作。**

**⚠ 但定理的【类型】仍要提到 `ChainParams ch`，所以这条路在 Lean 里仍受限。**

**⇒ 第 162 轮【不声称】`differentiableAt_chainActWith_joint`。**
**已确认的是：**

1. **`Chain.actWith` 的定义与两条 `rfl` 引理（第 161 轮）；**
2. **对具体链形状，`ChainParams` 的实例由搜索自动给出，`differentiableAt_snd` 直接可用**
   （本轮实测到四层）；
3. **签名里的变量 `ch` 才是障碍，而那是 Lean 类型类系统与依赖类型的交界问题，
   不是数学问题。** -//-! ### 宽度序列方案：已验证可行的部分，与仍然受阻的部分

**第 163 轮试了「把参数空间从 `ChainParams ch`（依赖 `Chain`）换成
`ParamsOf ws`（只依赖 `List ℕ`）」，以绕开第 162 轮定位的障碍。**

## 已验证可行（`lake build` 下）

**1. `Chain.toWidths`**：**`(m, _, .idf _) ↦ [m]`，`(m, _, .cons _ rest) ↦ m :: toWidths rest`**，
**首元素必须由外层 `m` 给出**（用 `_` 会报 `don't know how to synthesize placeholder for argument 'head'`）。

**2. `abbrev ParamsOf : List ℕ → Type`**：
**`[] ↦ PUnit`，`[_] ↦ PUnit`，`a :: b :: rest ↦ mlayerParams a b × ParamsOf (b :: rest)`**，
**在 `lake build` 下编译通过。**

**3. ⚠ 一个探针工具的假象**：
**同一个定义在 `lake env lean` 单独检查时报
`code generator does not support recursor 'List.rec'`，
而在 `lake build` 下【正常**。**⇒ 本项目的正式构建用 `lake build`，所以这不是问题；
但用 `lake env lean` 做探针时会在 `Type` 值定义上误报。**

## 仍然受阻

**`NormedAddCommGroup`／`NormedSpace` 在 `ParamsOf ws` 上的实例**：

**`| [] => inferInstanceAs (NormedAddCommGroup PUnit)` 无法通过**——
**报错是 `synthesized type class instance is not definitionally equal to …`。
`NormedSpace` 的签名更要求先有 `SeminormedAddCommGroup (ParamsOf ws)`，
而那正是要解的东西，于是【同一个障碍以另一种形式重现】。**

**⇒ 换载体【没有**绕开第 162 轮的障碍：**它把「依赖 `Chain` 的变量无法展开」
换成了「对 `ws` 量化的实例无法在定义体内取得」。**

## 结论

**第 160–163 轮四次尝试的净结果是：**

- **具体形状可行**：**对任意【写出来的】`Chain`（任意深度），`ChainParams` 的实例自动解出，
  `actWith` 与 `differentiableAt_snd` 直接可用（第 162 轮实测到四层）。**
- **变量量化受阻**：**对 `ch`／`ws` 作全称量化的单一陈述，在 Lean 的类型类系统里无法表达，
  除非把实例作为【参数】传入——而那样递归时取不出子结构。**

**⇒ 这是一个【Lean 表达能力】的限制，不是数学缺口。**
**已登记的替代路线**：**把参数空间写成【扁平】的形式**
（例如 `Fin (totalParams) → ℝ` 加一组索引引理），
**那样实例由 `Pi` 一次给出，不需要任何递归。** -//-! ### 第五种路线（扁平参数）也受阻，原因是一个 Lean 4.14 的具体限制

**第 164 轮试了「扁平参数空间」**：
**参数写成 `Fin (ParamsDim ws) → ℝ`，使实例由 `Pi` 一次给出，完全不需要递归。**

**这条路在【数学上】是对的，而且 `Pi` 的实例确实对任意 `ws` 成立。
但它撞上了一个【工具链】的限制：**

**`def` 或 `noncomputable def` 返回 `Type` 时，Lean 4.14 的编译器会对它做 IR 检查，
而定义体内含有 `List` 的模式匹配就会失败**：

    failed to compile definition, compiler IR check failed

**本轮试过的全部写法及结果：**

| 写法 | 结果 |
|:--|:--|
| `def ParamsCount : List ℕ → ℕ` 三段模式 | IR 检查失败 |
| `noncomputable def ParamsCount` | 仍失败 |
| `abbrev ParamsCount` | 定义本身通过，但下游 `FlatParams` 失败 |
| `abbrev ParamsCount` 用 `zipWith` | IR 检查失败 |
| `def ParamsDim := ws.length * ws.length + ws.length`（无模式匹配） | 通过 |
| `abbrev FlatParams := Fin (ParamsDim ws) → ℝ` | IR 检查失败 |
| `noncomputable def FlatParams` | IR 检查失败 |

**⇒ 瓶颈不在数学、不在类型类，而在【Lean 4.14 对 `Type` 值定义的 IR 检查】。**

## 这意味着什么

**四轮（160–164）共试了五种路线，全部受阻于同一个层次：
Lean 的工具链与类型类系统，而不是数学。**

**已确认可行的部分：**

1. **`Chain.act` 对 `Chain` 的递归可微性**（第 159 轮，
   `differentiableAt_chainAct`）——**⚠ 该定理在第 161 轮的区域重写中曾被【删除**，
   **第 177 轮恢复；本节此前的措辞声称它「完整证明」，而那段时期内代码里并没有它。**
2. **`Chain.actWith` 的参数化作用**（第 161 轮，含两条 `rfl` 引理）；
3. **对【具体】链形状，`ChainParams` 的实例自动解出**（第 162 轮实测到四层）；
4. **`affineAct` 的仿射性与共线性保持**（第 156 轮，这是表达能力的实质结论）。

**仍受阻的部分：对变量 `ch` 量化的联合可微性。**
**它的数学是「每层一次 `comp`」，第 159 轮已为 `Chain.act` 证过；
缺的只是一个能装下实例的类型。**

## 登记：真正可行的下一步

**如果要把这条补完，正确的做法是【绕开 `Type` 值定义】**：

- **把扁平维度写成一个 `Nat` 值的【参数】**（`ParamsDim : List ℕ → ℕ` 作为 hypothesis 传入），
  **而不是在 `Type` 定义里计算它**；
- **或者固定一个上界 `B`，把参数空间写成 `Fin B → ℝ`，`B` 由调用方给出。**

**两种都不需要在 `Type` 定义里做模式匹配，因此都绕开 IR 检查。**
**这留给后续轮次。** -//-! ## 扁平参数空间：把维度作为【显式参数】，彻底绕开 `Type` 值的计算

## 关键的一步

**前五条路线（第 160–164 轮）都受阻于：`Type` 值定义里的计算不被 Lean 4.14 接受
（`def`／`noncomputable def` 返回 `Type` 时触发 IR 检查，`List` 模式匹配就失败）。**

**⇒ 正确做法是【把类型直接展开】：
参数空间就写成 `Fin B → ℝ`，**`B : ℕ` 由调用方作为参数给出**，
**`Type` 位置上没有任何计算，也就没有任何模式匹配。**

**这是最简单的一条，也是我此前一直绕开的一条。** -/

/-- ⭐⭐⭐ **扁平参数空间**——`B` 是维度，由调用方给出。

**`Fin B → ℝ` 的 `NormedAddCommGroup`／`NormedSpace ℝ` 由 `Pi` 实例【一次】给出，
对【任意】`B` 成立，不需要递归、不需要 `match`、不需要依赖索引。** -/
abbrev FlatParams (B : ℕ) : Type := Fin B → ℝ

/-- ⭐⭐⭐ **`FlatParams B` 是赋范向量空间**——**对任意 `B`，包括变量。**

**⚠ 用 `theorem … : Nonempty …` 而不是 `example … : … := inferInstance`**：
**后者会被当作需要编译的定义，而 `Type` 值位置的实例项会触发 IR 检查。
写成 `Prop` 值的定理就没有这个问题。** -/
theorem flatParams_normedAddCommGroup (B : ℕ) :
    Nonempty (NormedAddCommGroup (FlatParams B)) :=
  ⟨inferInstanceAs (NormedAddCommGroup (Fin B → ℝ))⟩

/-- ⭐⭐⭐ **`FlatParams B` 上的 `NormedSpace ℝ`**——同上。 -/
theorem flatParams_normedSpace (B : ℕ) :
    Nonempty (NormedSpace ℝ (FlatParams B)) :=
  ⟨inferInstanceAs (NormedSpace ℝ (Fin B → ℝ))⟩

/-- **参数总数的精确公式**（作为 `Prop` 陈述，不做 `Type` 位置的计算）。

**⚠ 写成 `Nat` 值的定理而不是 `Type` 定义的一部分**：
**这样它可以被引用、被证明，而不会触发任何 IR 检查。** -/
def ParamsCount : List ℕ → ℕ
  | [] => 0
  | a :: [] => 0
  | a :: b :: rest => a * b + b + ParamsCount (b :: rest)

theorem paramsCount_nil : ParamsCount [] = 0 := rfl

theorem paramsCount_single (a : ℕ) : ParamsCount [a] = 0 := rfl

theorem paramsCount_two (a b : ℕ) : ParamsCount [a, b] = a * b + b := rfl

/-! ## `Chain` 在扁平参数上的作用与可微性

## 做法

**参数向量 `g : FlatParams B`（即 `Fin B → ℝ`）与链 `ch` 一起决定网络的输出。
读参数的函数 `g ↦ g i` 对 `i : Fin B` 可微（`differentiableAt_apply`），
**所以只要把作用写成 `g i` 的复合，`fun_prop` 就能一次收掉。**

**本节先证最基本的一条：扁平参数向量上的读坐标可微。**

**⚠ 真正的 `actWith` 版本需要一个把 `g` 切成分片的编码函数——
那需要在 `Fin` 上做除法取余，是常规但冗长的工作。**
**本节把可微性的【核心事实】先钉住：对变量 `B` 与任意 `i`，
`g ↦ g i` 可微。这正是前几轮缺的那一块。** -/

/-- ⭐⭐⭐ **扁平参数上的坐标投影可微**——**对【变量】`B`。**

**这是 `FlatParams B` 能承载损失链的根本原因**：
**`NormedAddCommGroup (FlatParams B)` 对任意 `B` 成立（本节上一条），
所以 `fderiv` 可以作用于它，而读坐标是最基本的可微函数。** -/
theorem flatParams_differentiableAt_apply (B : ℕ) (i : Fin B) (g : FlatParams B) :
    DifferentiableAt ℝ (fun h : FlatParams B => h i) g := by
  fun_prop

/-- ⭐⭐⭐ **扁平参数上的仿射组合可微**——**`FlatParams` 上的线性泛函。**

**这条与 `mlayerAct` 的形状一致**：`x ↦ ∑ i, w i * g (σ i) + c`，
**所以链的每一层都可以在扁平参数上重建。** -/
theorem flatParams_differentiableAt_linear (B : ℕ) (k : ℕ)
    (w : Fin k → ℝ) (σ : Fin k → Fin B) (c : ℝ) (g : FlatParams B) :
    DifferentiableAt ℝ (fun g : FlatParams B => (∑ i, w i * g (σ i)) + c) g := by
  fun_prop

/-- ⭐⭐⭐ **扁平参数上的逐点可微性**——`Fin n → ℝ` 值的情形。 -/
theorem flatParams_differentiableAt_linear_vec (B : ℕ) (k n : ℕ)
    (w : Fin k → Fin n → ℝ) (σ : Fin k → Fin B) (c : Fin n → ℝ) (g : FlatParams B) :
    DifferentiableAt ℝ
      (fun g : FlatParams B => fun j => (∑ i, w i j * g (σ i)) + c j) g := by
  fun_prop

/-! ## 扁平槽位：把 `(层, i, j)` 映到参数向量的一个位置

## 结构

**每层的参数数是 `a × b + b`（`a × b` 个权重加 `b` 个偏置）。
各层的区域由【前缀和】给出，所以不同层落在不交的区间。**

**⚠ 槽位映射只产生 `Fin B` 的一个【值】，不需要证明它是满射或单射**：
**每层只读自己的区域，所以映射的性质不影响正确性。**
**这使得 `σ` 可以是纯算术，不需要任何精细的对应证明。** -/

/-- **一层的参数数**：`a × b` 个权重加 `b` 个偏置。 -/
def layerParamCount (a b : ℕ) : ℕ := a * b + b

/-- **各层区域的起始偏移**（前缀和）。

**`layerOffsets [2,3,4] = [0, 9, 25]`**：
**第 1 层从 `2×3+3 = 9` 开始，第 2 层从 `9 + 3×4+4 = 25` 开始。** -/
def layerOffsets : List ℕ → List ℕ
  | [] => []
  | [_] => [0]
  | a :: b :: rest => 0 :: (layerOffsets (b :: rest)).map (fun x => x + layerParamCount a b)

/-- **参数总数的精确公式**——**等于最后一层偏移加上最后一层的参数数。** -/
def ParamsCountExact : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => layerParamCount a b + ParamsCountExact (b :: rest)

/-- **三层例子**——`[2,3,4]` 的总参数数是 `9 + 16 = 25`。 -/
theorem paramsCountExact_example : ParamsCountExact [2, 3, 4] = 25 := rfl

/-- **偏移的例子**——`[2,3,4]` 的三层分别从 `0, 9, 25` 开始。 -/
theorem layerOffsets_example : layerOffsets [2, 3, 4] = [0, 9, 25] := rfl

/-- **空序列**：没有层，没有参数。 -/
theorem layerOffsets_nil : layerOffsets [] = [] := rfl

/-- **单层**：偏移为零，参数数为 `a × b + b`（由 `ParamsCountExact` 给出）。 -/
theorem layerOffsets_single (a : ℕ) : layerOffsets [a] = [0] := rfl

/-- **空序列的参数总数为零**。 -/
theorem paramsCountExact_nil : ParamsCountExact ([] : List ℕ) = 0 := rfl

/-- ⭐ **一层的参数数是正的**（当 `b > 0`）——**所以每层确实占一段非空区域。** -/
theorem layerParamCount_pos (a b : ℕ) (hb : 0 < b) : 0 < layerParamCount a b := by
  simp only [layerParamCount]
  omega

/-- ⭐⭐ **两层时，第二层的偏移正好是第一层的参数数**——**不交性的起点。** -/
theorem layerOffsets_two (a b : ℕ) :
    layerOffsets [a, b] = [0, layerParamCount a b] := by
  simp only [layerOffsets, List.map, Nat.zero_add]

/-! ## 扁平层作用：把偏移算术与线性可微性接起来

## 设计：所有量都作为【参数】传入

**第 162–166 轮的教训是同一个**：
**凡是可以「算出来」的东西，如果它出现在 `Type` 位置或依赖位置，
就在 Lean 里制造障碍；而把它作为【参数】传入就一切顺利。**

**⇒ 本节的 `slotOf` 只需要 `off`、`b`、`i`、`j`——`ws` 根本不出现。**
**而槽位在 `Fin B` 里的良定性由【假设】`h : slotOf off b i j < B` 给出，不由证明给出。** -/

/-- **槽位**：第 `off` 段起、第 `i` 行（长度 `b`）、第 `j` 列。

**`slotOf off b i j = off + i * b + j`**——**纯算术，没有 `List`，没有 `Fin` 的构造。** -/
def slotOf (off b i j : ℕ) : ℕ := off + i * b + j

/-- **第一行的槽位从 `off` 开始**。 -/
theorem slotOf_zero_row (off b j : ℕ) : slotOf off b 0 j = off + j := by
  simp only [slotOf, Nat.zero_mul, Nat.zero_add, Nat.add_zero]

/-- **相邻两行相差 `b`**。 -/
theorem slotOf_succ_row (off b i j : ℕ) :
    slotOf off b (i + 1) j = slotOf off b i j + b := by
  simp only [slotOf]
  ring

/-- **同一行相邻两列相差一**。 -/
theorem slotOf_succ_col (off b i j : ℕ) :
    slotOf off b i (j + 1) = slotOf off b i j + 1 := by
  simp only [slotOf]
  ring

/-- ⭐⭐ **同一行内不同列给出不同槽位**——**单射性在这一维上是【直接的**。** -/
theorem slotOf_inj_col (off b i : ℕ) {j j' : ℕ} (h : slotOf off b i j = slotOf off b i j') :
    j = j' := by
  simp only [slotOf] at h
  omega

/-- ⭐⭐ **相邻行在同一列上相差 `b`**，**所以 `b > 0` 时不同行不同槽位。** -/
theorem slotOf_row_add (off b i : ℕ) (hb : 0 < b) {i' : ℕ} (hi : i < i') :
    slotOf off b i 0 < slotOf off b i' 0 := by
  simp only [slotOf]
  have : i * b < i' * b := by
    exact Nat.mul_lt_mul_of_pos_right hi hb
  omega

/-- ⭐⭐⭐ **扁平层作用**：从扁平参数向量读出这一层的权重与偏置。

**`g ⟨slotOf off b i j, _⟩` 就是「第 `off` 段里第 `(i,j)` 个参数」，
而 `(∑ i, w i j * g (…) ) + c j` 正是 `mlayerAct` 的形状。**

**⚠ 良定性由假设 `hbound` 给出，不由证明给出**——**这是第 165 轮的同一个模式。** -/
noncomputable def flatLayerAct {B a b : ℕ} (off : ℕ)
    (hbound : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < B)
    (w : Fin a → Fin b → ℝ) (c : Fin b → ℝ) (g : Fin B → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, w i j * g ⟨slotOf off b i.val j.val, hbound i j⟩) + c j

/-- ⭐⭐⭐ **扁平层作用对参数可微**——**这是整个扁平参数链的核心。**

**由第 165 轮的 `flatParams_differentiableAt_linear_vec` 直接得到**：
**一旦把 `σ i = ⟨slotOf off b i.val j.val, hbound i j⟩` 固定下来，
`g ↦ ∑ i, w i j * g (σ i) + c j` 就是那条定理的形状。** -/
theorem flatLayerAct_differentiableAt {B a b : ℕ} (off : ℕ)
    (hbound : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < B)
    (w : Fin a → Fin b → ℝ) (c : Fin b → ℝ) (g : Fin B → ℝ) :
    DifferentiableAt ℝ (fun h : Fin B → ℝ => flatLayerAct off hbound w c h) g := by
  have hfun : (fun h : Fin B → ℝ => flatLayerAct off hbound w c h)
      = fun h : Fin B → ℝ => fun j : Fin b =>
          (∑ i : Fin a, w i j * h ⟨slotOf off b i.val j.val, hbound i j⟩) + c j := by
    funext h
    funext j
    simp only [flatLayerAct]
  rw [hfun]
  fun_prop

/-! ## ⚠ 一个必须指出的结构缺陷：`flatLayerAct` 的 `B` 承担了两个角色

## 缺陷

**`flatLayerAct` 的签名是**

    flatLayerAct {B a b : ℕ} (off : ℕ)
        (hbound : ∀ i j, slotOf off b i.val j.val < B)
        (w : Fin a → Fin b → ℝ) (c : Fin b → ℝ) (g : Fin B → ℝ) : Fin b → ℝ

**其中 `B` 【同时】是：**

1. **参数向量的长度**（`g : Fin B → ℝ`）；
2. **层的输入维度**（`g` 的索引类型必须是 `Fin B`，而读出的值喂给 `∑ i, w i j * ·`，其中 `i : Fin a`）。

**⚠ 第 1 条和 `a` 并不冲突——`a` 是权重的行数，`B` 是向量长度。
真正的问题是【第二层】的情形：它的输入是 `Fin b → ℝ`（第一层的输出），
但它的参数仍然从 `g : Fin B → ℝ` 里读。**

**⇒ 两次调用 `flatLayerAct` 时，第二次的 `B` 必须是 `b`（因为输入是 `Fin b`），
但它的 `hbound` 说的是「槽位 `< B`」——两者维度不同，无法传递。**

**第 168 轮实测的报错正是这个**：

    flatLayerAct off₁ h₁ w₁ c₁ g  has type  Fin b → ℝ
    but is expected to have type  Fin B → ℝ

## 正确的形式

**需要把参数向量长度 `N` 与层输入维度 `a` 分成【两个】类型参数**：

    flatLayerAct' {N a b : ℕ} (off : ℕ)
        (hbound : ∀ i j, slotOf off b i.val j.val < N)
        (w : Fin a → Fin b → ℝ) (c : Fin b → ℝ) (g : Fin N → ℝ) : Fin b → ℝ

**⚠ 但 `flatLayerAct'` 的输出是 `Fin b → ℝ`，而它的输入是 `Fin N → ℝ`——
所以复合时要求 `N = b`，仍然把两者绑在一起。**

**⇒ 真正的解法是把「参数」与「激活」分开：
`flatParamAct : (Fin N → ℝ) → (Fin a → ℝ) → (Fin b → ℝ)`，
即先读参数、再把激活喂进去。**
**那样两层复合时，第一层的输出 `Fin b → ℝ` 直接作为第二层的【激活】输入，
而两层的【参数】都从同一个 `Fin N → ℝ` 读——维度不再冲突。**

**⇒ 这是下一步的正确形式，第 169 轮做。** -//-! ## `flatParamAct`：参数与激活分开的层作用

## 为什么这样分开就解决了第 168 轮的缺陷

**`flatLayerAct` 的问题是一个 `B` 同时当「参数向量长度」与「层输入维度」，
所以第二层的输入（`Fin b`）与它读参数的地方（`Fin B`）冲突。**

**⇒ `flatParamAct` 把两者【分开**：

- **参数向量 `g : Fin N → ℝ` 只用于【读出】权重与偏置**；
- **激活向量 `x : Fin a → ℝ` 是【作用的对象**，它的维度与 `N` 无关。

**于是两层复合是**：`flatParamAct g₂ (flatParamAct g₁ x)`——**两层的参数都从同一个 `Fin N` 读，
而激活的维度 `b` 只在复合处出现一次。**

## 结构

    flatParamAct {N a b} (off) (hbound : ∀ i j, slotOf off b i.val j.val < N)
        (g : Fin N → ℝ) (x : Fin a → ℝ) : Fin b → ℝ
      := fun j => (∑ i, w(g, off, i, j) * x i) + c(g, off, j)

**其中 `w`、`c` 从 `g` 的槽位读出。** -/

/-- **从扁平向量读出权重的第 `(i, j)` 项**。 -/
noncomputable def readW {N a b : ℕ} (off : ℕ)
    (hbound : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (g : Fin N → ℝ) (i : Fin a) (j : Fin b) : ℝ :=
  g ⟨slotOf off b i.val j.val, hbound i j⟩

/-- **从扁平向量读出偏置的第 `j` 项**——**偏置紧接在权重之后，所以槽位偏移 `a × b`。** -/
noncomputable def readC {N a b : ℕ} (off : ℕ)
    (hboundC : ∀ (j : Fin b), off + a * b + j.val < N)
    (g : Fin N → ℝ) (j : Fin b) : ℝ :=
  g ⟨off + a * b + j.val, hboundC j⟩

/-- ⭐⭐⭐ **`flatParamAct`：参数与激活分开的层作用**。

**`g` 提供权重与偏置，`x` 是作用对象——两者的维度 `N` 与 `a` 互不相干。** -/
noncomputable def flatParamAct {N a b : ℕ} (off : ℕ)
    (hw : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (hc : ∀ (j : Fin b), off + a * b + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i, readW off hw g i j * x i) + readC off hc g j

/-- **`flatParamAct` 的展开式**——**显式写出 `readW`／`readC`，供后续证明使用。**

**⚠ `fun_prop` 不认识 `flatParamAct`（第 169 轮实测：`No theorems found for Lattice.Core.flatParamAct`），
所以必须先展开成坐标投影的形式。** -/
theorem flatParamAct_apply {N a b : ℕ} (off : ℕ)
    (hw : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (hc : ∀ (j : Fin b), off + a * b + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) (j : Fin b) :
    flatParamAct off hw hc g x j
      = (∑ i : Fin a, g ⟨slotOf off b i.val j.val, hw i j⟩ * x i)
        + g ⟨off + a * b + j.val, hc j⟩ := by
  simp only [flatParamAct, readW, readC]

/-- ⭐⭐⭐ **`flatParamAct` 对【激活】可微**——**这是复合所需要的。** -/
theorem flatParamAct_differentiableAt_activation {N a b : ℕ} (off : ℕ)
    (hw : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (hc : ∀ (j : Fin b), off + a * b + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ (fun y : Fin a → ℝ => flatParamAct off hw hc g y) x := by
  have hfun : (fun y : Fin a → ℝ => flatParamAct off hw hc g y)
      = fun y : Fin a → ℝ => fun j : Fin b =>
          (∑ i : Fin a, g ⟨slotOf off b i.val j.val, hw i j⟩ * y i)
            + g ⟨off + a * b + j.val, hc j⟩ := by
    funext y
    funext j
    exact flatParamAct_apply off hw hc g y j
  rw [hfun]
  fun_prop

/-- ⭐⭐⭐ **`flatParamAct` 对【参数】可微**——**这是训练所需要的。** -/
theorem flatParamAct_differentiableAt_params {N a b : ℕ} (off : ℕ)
    (hw : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (hc : ∀ (j : Fin b), off + a * b + j.val < N)
    (x : Fin a → ℝ) (g : Fin N → ℝ) :
    DifferentiableAt ℝ (fun h : Fin N → ℝ => flatParamAct off hw hc h x) g := by
  have hfun : (fun h : Fin N → ℝ => flatParamAct off hw hc h x)
      = fun h : Fin N → ℝ => fun j : Fin b =>
          (∑ i : Fin a, h ⟨slotOf off b i.val j.val, hw i j⟩ * x i)
            + h ⟨off + a * b + j.val, hc j⟩ := by
    funext h
    funext j
    exact flatParamAct_apply off hw hc h x j
  rw [hfun]
  fun_prop

/-- ⭐⭐⭐ **`flatParamAct` 对【参数与激活】联合可微**——**两层复合所需的完整陈述。** -/
theorem flatParamAct_differentiableAt_joint {N a b : ℕ} (off : ℕ)
    (hw : ∀ (i : Fin a) (j : Fin b), slotOf off b i.val j.val < N)
    (hc : ∀ (j : Fin b), off + a * b + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ
      (fun r : (Fin N → ℝ) × (Fin a → ℝ) => flatParamAct off hw hc r.1 r.2) (g, x) := by
  have hfun : (fun r : (Fin N → ℝ) × (Fin a → ℝ) => flatParamAct off hw hc r.1 r.2)
      = fun r : (Fin N → ℝ) × (Fin a → ℝ) => fun j : Fin b =>
          (∑ i : Fin a, r.1 ⟨slotOf off b i.val j.val, hw i j⟩ * r.2 i)
            + r.1 ⟨off + a * b + j.val, hc j⟩ := by
    funext r
    funext j
    exact flatParamAct_apply off hw hc r.1 r.2 j
  rw [hfun]
  fun_prop

/-! ## 两层复合：第 168 轮缺陷的直接修法

## 为什么 `flatParamAct` 使复合成为可能

**`flatLayerAct` 的 `B` 同时是参数向量长度与层输入维度，所以第二层冲突。
`flatParamAct` 把它们分开：**

- **参数向量 `g : Fin N → ℝ`——两层【共用】，所以两次的 `N` 都是 `N`；**
- **激活向量 `x : Fin a → ℝ`——第二层的 `a` 是第一层的输出维度 `b`。**

**⇒ 复合是 `flatParamAct off₂ hw₂ hc₂ g (flatParamAct off₁ hw₁ hc₁ g x)`，
**两次调用的 `N` 都是 `N`，没有任何维度被迫扮演两个角色。** -/

/-- ⭐⭐⭐ **两层复合**——**`flatParamAct` 的直接应用。** -/
noncomputable def compose2 {N a b d : ℕ} (off₁ off₂ : ℕ)
    (hw₁ : ∀ (i : Fin a) (j : Fin b), slotOf off₁ b i.val j.val < N)
    (hc₁ : ∀ (j : Fin b), off₁ + a * b + j.val < N)
    (hw₂ : ∀ (i : Fin b) (j : Fin d), slotOf off₂ d i.val j.val < N)
    (hc₂ : ∀ (j : Fin d), off₂ + b * d + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) : Fin d → ℝ :=
  flatParamAct off₂ hw₂ hc₂ g (flatParamAct off₁ hw₁ hc₁ g x)

/-- ⭐⭐⭐ **两层复合对【参数与激活】联合可微**——**第 168 轮未能证出的那条。**

**由两次 `flatParamAct_differentiableAt_joint` 与一次 `comp`：
第一层的输出 `Fin b → ℝ` 正是第二层的激活输入。** -/
theorem compose2_differentiableAt_joint {N a b d : ℕ} (off₁ off₂ : ℕ)
    (hw₁ : ∀ (i : Fin a) (j : Fin b), slotOf off₁ b i.val j.val < N)
    (hc₁ : ∀ (j : Fin b), off₁ + a * b + j.val < N)
    (hw₂ : ∀ (i : Fin b) (j : Fin d), slotOf off₂ d i.val j.val < N)
    (hc₂ : ∀ (j : Fin d), off₂ + b * d + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ
      (fun r : (Fin N → ℝ) × (Fin a → ℝ) => compose2 off₁ off₂ hw₁ hc₁ hw₂ hc₂ r.1 r.2) (g, x) := by
  have hstep : (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
        compose2 off₁ off₂ hw₁ hc₁ hw₂ hc₂ r.1 r.2)
      = (fun s : (Fin N → ℝ) × (Fin b → ℝ) =>
            flatParamAct off₂ hw₂ hc₂ s.1 s.2)
        ∘ (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
            (r.1, flatParamAct off₁ hw₁ hc₁ r.1 r.2)) := by
    funext r
    rfl
  rw [hstep]
  refine (flatParamAct_differentiableAt_joint off₂ hw₂ hc₂ g
      (flatParamAct off₁ hw₁ hc₁ g x)).comp (g, x) ?_
  exact DifferentiableAt.prod differentiableAt_fst
    (flatParamAct_differentiableAt_joint off₁ hw₁ hc₁ g x)

/-- ⭐⭐⭐ **两层复合对【参数】可微**——**训练所需的陈述。** -/
theorem compose2_differentiableAt_params {N a b d : ℕ} (off₁ off₂ : ℕ)
    (hw₁ : ∀ (i : Fin a) (j : Fin b), slotOf off₁ b i.val j.val < N)
    (hc₁ : ∀ (j : Fin b), off₁ + a * b + j.val < N)
    (hw₂ : ∀ (i : Fin b) (j : Fin d), slotOf off₂ d i.val j.val < N)
    (hc₂ : ∀ (j : Fin d), off₂ + b * d + j.val < N)
    (x : Fin a → ℝ) (g : Fin N → ℝ) :
    DifferentiableAt ℝ
      (fun h : Fin N → ℝ => compose2 off₁ off₂ hw₁ hc₁ hw₂ hc₂ h x) g := by
  have hstep : (fun h : Fin N → ℝ => compose2 off₁ off₂ hw₁ hc₁ hw₂ hc₂ h x)
      = (fun s : (Fin N → ℝ) × (Fin b → ℝ) => flatParamAct off₂ hw₂ hc₂ s.1 s.2)
        ∘ (fun h : Fin N → ℝ => (h, flatParamAct off₁ hw₁ hc₁ h x)) := by
    funext h
    rfl
  rw [hstep]
  refine (flatParamAct_differentiableAt_joint off₂ hw₂ hc₂ g
      (flatParamAct off₁ hw₁ hc₁ g x)).comp g ?_
  exact DifferentiableAt.prod differentiableAt_id
    (flatParamAct_differentiableAt_params off₁ hw₁ hc₁ x g)

/-! ## 三层复合：把「不重叠」写成递推等式

## 为什么三层值得单独做

**`compose2` 允许 `off₁` 与 `off₂` 任意；若两者重叠，两层读同一段参数。**
**数学上仍可微，但**语义上不是两层网络**。**

**⇒ 本节的 `compose3` 把偏移写成【递推等式】**：

    off₂ = off₁ + a * b + b
    off₃ = off₂ + b * d + d

**这样「相邻层不重叠」由【构造】保证，不需要任何证明——
而 `layerParamCount a b = a * b + b`（第 166 轮）正是这个步长。** -/

/-- **一层的总占用量**——**与第 166 轮的 `layerParamCount` 一致。** -/
theorem slotStep_eq_layerParamCount (a b : ℕ) :
    a * b + b = layerParamCount a b :=
  rfl

/-- ⭐⭐ **第三层起点由前两层算出**——**递推的第一步。** -/
def thirdOffset (off₁ a b : ℕ) : ℕ := off₁ + layerParamCount a b

/-- ⭐⭐ **第四层起点由前三层算出**——**递推的第二步。** -/
def fourthOffset (off₁ a b d : ℕ) : ℕ := thirdOffset off₁ a b + layerParamCount b d

/-- **第三层起点确实比第一层大**（当 `b > 0`）。 -/
theorem thirdOffset_gt (off₁ a b : ℕ) (hb : 0 < b) :
    off₁ < thirdOffset off₁ a b := by
  simp only [thirdOffset, layerParamCount]
  have : 0 < a * b + b := by
    have : 0 < b := hb
    nlinarith
  omega

/-- ⭐⭐⭐ **三层复合**——**偏移由递推给出，所以三层读的区间互不相交。**

**⚠ 三个 `hbound` 各自以 `N` 为上界**：**它们读的是同一个 `g : Fin N → ℝ`。** -/
noncomputable def compose3 {N a b d e : ℕ} (off₁ : ℕ)
    (hw₁ : ∀ (i : Fin a) (j : Fin b), slotOf off₁ b i.val j.val < N)
    (hc₁ : ∀ (j : Fin b), off₁ + a * b + j.val < N)
    (hw₂ : ∀ (i : Fin b) (j : Fin d),
      slotOf (thirdOffset off₁ a b) d i.val j.val < N)
    (hc₂ : ∀ (j : Fin d),
      thirdOffset off₁ a b + b * d + j.val < N)
    (hw₃ : ∀ (i : Fin d) (j : Fin e),
      slotOf (fourthOffset off₁ a b d) e i.val j.val < N)
    (hc₃ : ∀ (j : Fin e),
      fourthOffset off₁ a b d + d * e + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) : Fin e → ℝ :=
  flatParamAct (off := fourthOffset off₁ a b d) hw₃ hc₃ g
    (flatParamAct (off := thirdOffset off₁ a b) hw₂ hc₂ g
      (flatParamAct (off := off₁) hw₁ hc₁ g x))

/-- ⭐⭐⭐ **三层复合对【参数与激活】联合可微**——**归纳步的第二次验证。** -/
theorem compose3_differentiableAt_joint {N a b d e : ℕ} (off₁ : ℕ)
    (hw₁ : ∀ (i : Fin a) (j : Fin b), slotOf off₁ b i.val j.val < N)
    (hc₁ : ∀ (j : Fin b), off₁ + a * b + j.val < N)
    (hw₂ : ∀ (i : Fin b) (j : Fin d),
      slotOf (thirdOffset off₁ a b) d i.val j.val < N)
    (hc₂ : ∀ (j : Fin d),
      thirdOffset off₁ a b + b * d + j.val < N)
    (hw₃ : ∀ (i : Fin d) (j : Fin e),
      slotOf (fourthOffset off₁ a b d) e i.val j.val < N)
    (hc₃ : ∀ (j : Fin e),
      fourthOffset off₁ a b d + d * e + j.val < N)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ
      (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
        compose3 off₁ hw₁ hc₁ hw₂ hc₂ hw₃ hc₃ r.1 r.2) (g, x) := by
  have hstep : (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
        compose3 off₁ hw₁ hc₁ hw₂ hc₂ hw₃ hc₃ r.1 r.2)
      = (fun s : (Fin N → ℝ) × (Fin d → ℝ) =>
            flatParamAct (off := fourthOffset off₁ a b d) hw₃ hc₃ s.1 s.2)
        ∘ (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
            (r.1, compose2 off₁ (thirdOffset off₁ a b) hw₁ hc₁ hw₂ hc₂ r.1 r.2)) := by
    funext r
    rfl
  rw [hstep]
  refine (flatParamAct_differentiableAt_joint (off := fourthOffset off₁ a b d) hw₃ hc₃ g
    (compose2 off₁ (thirdOffset off₁ a b) hw₁ hc₁ hw₂ hc₂ g x)).comp (g, x) ?_
  exact DifferentiableAt.prod differentiableAt_fst
    (compose2_differentiableAt_joint off₁ (thirdOffset off₁ a b) hw₁ hc₁ hw₂ hc₂ g x)

/-! ## 去掉 `hbound`：越界读零，从而消掉依赖假设

## 为什么这是关键一步

**第 165–172 轮的 `flatParamAct` 需要三组 `hbound`：**

    hw : ∀ i j, slotOf off b i.val j.val < N
    hc : ∀ j, off + a * b + j.val < N

**这三组假设【随层数增长】，而它们的类型取决于每层的宽度——
这正是任意深度无法归纳的原因。**

**⇒ 本节的路线与第 138 轮的 `netPoints` 相同：越界时【返回零】**：

    readSlot g k := if h : k < N then g ⟨k, h⟩ else 0

**于是 `flatParamAct` 不需要任何 `hbound`**，**而越界位置读出零——
对「层数超参数上限」的情形，那是一个明确且无害的语义。** -/

/-- **越界读零的槽位读取**。

**⚠ 与 `trunc` 同一模式**（第 138 轮 `netPoints` 的 `if h : j < K then … else 0`）：
**用 `ℕ` 索引而不是 `Fin N`，从而不需要预先证明索引在界内。** -/
noncomputable def readSlot {N : ℕ} (g : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k < N then g ⟨k, h⟩ else 0

/-- ⭐ **界内时 `readSlot` 就是坐标投影。** -/
theorem readSlot_of_lt {N : ℕ} (g : Fin N → ℝ) {k : ℕ} (h : k < N) :
    readSlot g k = g ⟨k, h⟩ := by
  simp only [readSlot, dif_pos h]

/-- ⭐ **界外时 `readSlot` 为零。** -/
theorem readSlot_of_ge {N : ℕ} (g : Fin N → ℝ) {k : ℕ} (h : N ≤ k) :
    readSlot g k = 0 := by
  simp only [readSlot]
  exact dif_neg (by omega)

/-- ⭐⭐⭐ **`readSlot` 对参数【可微】**——**固定的 `k` 下它是投影或常值。**

**⚠ 关键**：**`k < N` 不依赖 `g`，所以 `by_cases` 分出的两支分别是
「坐标投影」（可微）与「常值零」（可微）。** -/
@[fun_prop]
theorem readSlot_differentiableAt {N : ℕ} (k : ℕ) (g : Fin N → ℝ) :
    DifferentiableAt ℝ (fun h : Fin N → ℝ => readSlot h k) g := by
  by_cases hk : k < N
  · have hfun : (fun h : Fin N → ℝ => readSlot h k) = fun h : Fin N → ℝ => h ⟨k, hk⟩ := by
      funext h
      exact readSlot_of_lt h hk
    rw [hfun]
    fun_prop
  · have hfun : (fun h : Fin N → ℝ => readSlot h k) = fun _ : Fin N → ℝ => (0 : ℝ) := by
      funext h
      exact readSlot_of_ge h (by omega)
    rw [hfun]
    fun_prop

/-- ⭐⭐⭐ **无 `hbound` 的层作用**——**参数与激活分离，且不需要任何界假设。** -/
noncomputable def flatParamActSafe {N a b : ℕ} (off : ℕ)
    (g : Fin N → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i : Fin a, readSlot g (slotOf off b i.val j.val) * x i)
    + readSlot g (off + a * b + j.val)

/-- ⭐⭐⭐ **`flatParamActSafe` 对【激活】可微**——**无 `hbound`，所以这一条对【任意】宽度成立。** -/
theorem flatParamActSafe_differentiableAt_activation {N a b : ℕ} (off : ℕ)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ (fun y : Fin a → ℝ =>
      flatParamActSafe (b := b) off g y) x := by
  have hfun : (fun y : Fin a → ℝ => flatParamActSafe (b := b) off g y)
      = fun y : Fin a → ℝ => fun j : Fin b =>
          (∑ i : Fin a, readSlot g (slotOf off b i.val j.val) * y i)
            + readSlot g (off + a * b + j.val) := by
    funext y
    funext j
    rfl
  rw [hfun]
  fun_prop

/-- ⭐⭐⭐ **`flatParamActSafe` 对【参数与激活】联合可微**——**由 `readSlot_differentiableAt` 支撑。** -/
theorem flatParamActSafe_differentiableAt_joint {N a b : ℕ} (off : ℕ)
    (g : Fin N → ℝ) (x : Fin a → ℝ) :
    DifferentiableAt ℝ
      (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
        flatParamActSafe (b := b) off r.1 r.2) (g, x) := by
  have hfun : (fun r : (Fin N → ℝ) × (Fin a → ℝ) =>
      flatParamActSafe (b := b) off r.1 r.2)
      = fun r : (Fin N → ℝ) × (Fin a → ℝ) => fun j : Fin b =>
          (∑ i : Fin a, readSlot r.1 (slotOf off b i.val j.val) * r.2 i)
            + readSlot r.1 (off + a * b + j.val) := by
    funext r
    funext j
    rfl
  rw [hfun]
  fun_prop

/-! ## 任意深度：沿 `Chain` 折叠

## 为什么现在可以

**`flatParamActSafe` 不带任何界假设（第 173 轮），
所以沿 `Chain` 的递归不需要携带任何随层数增长的假设。**
**这正是第 162–172 轮一直缺的那一块。**

## 偏移的递推

**每层的起点是「上一层起点 + 上一层占用量」，而占用量是 `layerParamCount`。**
**所以偏移是随 `ch` 一起递归算出来的，不作为额外参数传入。** -/

/-- **`Chain` 的逐层起始偏移**——**随 `ch` 递归，与第 172 轮的 `thirdOffset`／`fourthOffset` 一致。** -/
noncomputable def chainOffsets : {m n : ℕ} → Chain m n → ℕ → List ℕ
  | _, _, .idf _, _ => []
  | _, _, .cons (m := m') (n := n') _ rest, off =>
      off :: chainOffsets rest (off + layerParamCount m' n')

/-- **单层链的偏移表只有一项**（`idf` 之后没有层）。 -/
theorem chainOffsets_idf (n off : ℕ) : chainOffsets (Chain.idf n) off = [] :=
  rfl

/-- ⭐⭐ **两层链的偏移表与 `thirdOffset` 一致**——**与第 172 轮的递推对齐。** -/
theorem chainOffsets_two (m n c off : ℕ) (l₁ : MLayer m n) (l₂ : MLayer n c) :
    chainOffsets (Chain.cons l₁ (Chain.cons l₂ (Chain.idf c))) off
      = [off, thirdOffset off m n] := by
  simp only [chainOffsets, thirdOffset]

/-- ⭐⭐⭐ **任意深度的链作用**——**每层从 `g` 读参数，激活逐层传下去。**

**⚠ `N` 是参数向量长度，对所有层【相同】**；**层的输入／输出宽度由 `Chain` 的构造子强制。** -/
noncomputable def flatChainAct {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
    (Fin N → ℝ) → (Fin m → ℝ) → Fin n → ℝ
  | _, _, .idf _, _, _, x => x
  | _, _, .cons (m := m') (n := n') _ rest, off, g, x =>
      flatChainAct rest (off + layerParamCount m' n') g
        (flatParamActSafe (N := N) (a := m') (b := n') off g x)

/-- **空链的作用是恒等**。 -/
theorem flatChainAct_idf {N n : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : Fin n → ℝ) :
    flatChainAct (N := N) (Chain.idf n) off g x = x :=
  rfl

/-- ⭐⭐⭐ **任意深度的链作用对【参数与激活】联合可微**——**第 162 轮以来的目标。**

**对 `ch` 递归**：

- **`idf`**：作用是第二投影，可微；
- **`cons`**：`flatChainAct (cons l rest) off g x = flatChainAct rest off' g (flatParamActSafe off g x)`，
  **与内层映射 `r ↦ (r.1, flatParamActSafe off r.1 r.2)` 复合，
  而后者由第 173 轮的 `flatParamActSafe_differentiableAt_joint` 可微。** -/
theorem flatChainAct_differentiableAt_joint {N : ℕ} :
    {m n : ℕ} → (ch : Chain m n) → (off : ℕ) → (g : Fin N → ℝ) → (x : Fin m → ℝ) →
    DifferentiableAt ℝ
      (fun r : (Fin N → ℝ) × (Fin m → ℝ) =>
        flatChainAct (N := N) ch off r.1 r.2) (g, x)
  | _, _, .idf n, off, g, x => by
      have hid : (fun r : (Fin N → ℝ) × (Fin n → ℝ) =>
          flatChainAct (N := N) (Chain.idf n) off r.1 r.2) = fun r => r.2 := by
        funext r
        exact flatChainAct_idf off r.1 r.2
      rw [hid]
      exact differentiableAt_snd
  | _, _, .cons (m := m') (n := n') l rest, off, g, x => by
      have hstep : (fun r : (Fin N → ℝ) × (Fin m' → ℝ) =>
            flatChainAct (N := N) (Chain.cons l rest) off r.1 r.2)
          = (fun s : (Fin N → ℝ) × (Fin n' → ℝ) =>
              flatChainAct (N := N) rest (off + layerParamCount m' n') s.1 s.2)
            ∘ (fun r : (Fin N → ℝ) × (Fin m' → ℝ) =>
                (r.1, flatParamActSafe (N := N) (a := m') (b := n') off r.1 r.2)) := by
        funext r
        rfl
      rw [hstep]
      refine (flatChainAct_differentiableAt_joint rest
        (off + layerParamCount m' n') g
        (flatParamActSafe (N := N) (a := m') (b := n') off g x)).comp (g, x) ?_
      exact DifferentiableAt.prod differentiableAt_fst
        (flatParamActSafe_differentiableAt_joint (N := N) (a := m') (b := n') off g x)

/-- ⭐⭐ **`flatChainAct` 对【输入】可微**——**由联合定理与 `x ↦ (g, x)` 复合。** -/
theorem flatChainAct_differentiableAt_input {N : ℕ} :
    {m n : ℕ} → (ch : Chain m n) → (off : ℕ) → (g : Fin N → ℝ) → (x : Fin m → ℝ) →
    DifferentiableAt ℝ (fun y : Fin m → ℝ => flatChainAct (N := N) ch off g y) x
  | _, _, ch, off, g, x =>
    (flatChainAct_differentiableAt_joint ch off g x).comp x
      (DifferentiableAt.prod (differentiableAt_const g) differentiableAt_id)

/-! ## 参数侧的线性：仿射像封闭性的基础

## 为什么需要这一节

**第 179 轮确定：一般可实现性需要「目标配置落在链的仿射像内」这个前提。
而「像在仿射组合下封闭」的充分条件是【链作用对参数 `g` 线性**。】

**⇒ 本节证明这条线性，从最原子的 `readSlot` 开始。**

## 层次

1. **`readSlot` 对 `g` 线性**——界内是坐标投影，界外两侧都是零；
2. **`flatParamActSafe` 对 `g` 线性**——求和与常数项；
3. **`flatChainAct` 对 `g` 线性**——逐层归纳。

**⚠ 三者都【无前提**：`readSlot` 的 `if` 由 `k < N` 决定，不依赖 `g`。** -/

/-- ⭐⭐ **`readSlot` 对参数线性**——**界内两侧都是同一个投影，界外两侧都是零。** -/
theorem readSlot_linear {N : ℕ} (g₁ g₂ : Fin N → ℝ) (a b : ℝ) (k : ℕ) :
    readSlot (fun i => a * g₁ i + b * g₂ i) k
      = a * readSlot g₁ k + b * readSlot g₂ k := by
  by_cases hk : k < N
  · rw [readSlot_of_lt _ hk, readSlot_of_lt _ hk, readSlot_of_lt _ hk]
  · rw [readSlot_of_ge _ (by omega), readSlot_of_ge _ (by omega),
      readSlot_of_ge _ (by omega)]
    ring

/-! **为什么不需要单独的「凸组合」别名**：

**别名普查（第 180 轮）把 `readSlot_affine` 标为 `forward` 别名**——
**它只是 `readSlot_linear g₁ g₂ (1 - t) t k` 的转写调用，不提供新内容。
⇒ 删掉它，调用方直接写 `readSlot_linear g₁ g₂ (1 - t) t k`。** -/

/-! ### `flatParamActSafe` 对参数的线性

**第 180 轮记下的障碍**：`rw [Finset.mul_sum]` 在

    ∑ i, ((1-t) * A i + t * B i) * x i + ((1-t) * C + t * D)
      = (1-t) * ((∑ i, A i * x i) + C) + t * ((∑ i, B i * x i) + D)

**上找不到模式。**

**⇒ 第 181 轮先在【抽象形状】上把路径试通了**：**关键是 `Finset.mul_sum` 要用【反向**
（`← Finset.mul_sum`）——因为 `(1-t)` 已经在求和【内部】，需要把它【提出来**，
而不是推进去。** -/

/-- ⭐⭐⭐ **`flatParamActSafe` 对参数线性**——**求和与常数项各自线性。**

**证明顺序**：`ring` 展开乘积 → `sum_add_distrib` 拆求和 → `← mul_sum` 提出公因子 → `ring` 收尾。** -/
theorem flatParamActSafe_affine {N a b : ℕ} (off : ℕ) (g₁ g₂ : Fin N → ℝ)
    (t : ℝ) (x : Fin a → ℝ) :
    flatParamActSafe (N := N) (a := a) (b := b) off
        (fun i => (1 - t) * g₁ i + t * g₂ i) x
      = fun j => (1 - t) * flatParamActSafe (N := N) (a := a) (b := b) off g₁ x j
          + t * flatParamActSafe (N := N) (a := a) (b := b) off g₂ x j := by
  funext j
  simp only [flatParamActSafe, readSlot_linear]
  have hsplit : ∀ i : Fin a,
      ((1 - t) * readSlot g₁ (slotOf off b i.val j.val)
        + t * readSlot g₂ (slotOf off b i.val j.val)) * x i
      = (1 - t) * (readSlot g₁ (slotOf off b i.val j.val) * x i)
        + t * (readSlot g₂ (slotOf off b i.val j.val) * x i) := by
    intro i
    ring
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

/-! ### ⚠ 未闭合：`flatChainAct` 的双重线性，以及它需要的三条依赖

## 目标

    flatChainAct ch off ((1-t)·g₁ + t·g₂) ((1-t)·p₁ + t·p₂)
      = (1-t) · flatChainAct ch off g₁ p₁ + t · flatChainAct ch off g₂ p₂

**这是仿射像封闭性需要的最终形状：像中两点的凸组合，由两个参数的凸组合实现。**

## 第 182 轮的尝试与确切障碍

**我先证了一条辅助引理（`flatParamActSafe` 对【激活】线性），它通过了。
但把两条线性合成双线性时，`cons` 支的依赖次序暴露了一个结构问题：**

**`cons` 支的目标是**

    flatChainAct rest off' 新参数 (flatParamActSafe off 新参数 新输入)

**而它需要【三次】重写：**

1. **`flatParamActSafe_affine`**：把「新参数作用在 X 上」变成「旧中间激活的凸组合」——
   **但它只对【参数】做，激活仍是 X 原样；**
2. **`flatParamActSafe_linear_activation`**：把 X（本身已是 `(1-t)p₁ + t p₂`）展开成凸组合——
   **⚠ 这一步之后激活变成【双重】凸组合 `(1-t)·A + t·B`，其中 `A`、`B` 又各含一层凸组合；**
3. **`rest` 的归纳假设**：**它期望激活是【一次】凸组合，而现在是两次，对不上。**

**⇒ 根本原因**：**双线性定理的右侧把 `p₁`、`p₂` 当作【已经确定的】两个点，
而 `cons` 支的中间激活是【由新参数算出来的】，两者不是同一个东西。**

**⇒ 正确做法不是把双线性当作一条定理，而是【两条分别的线性**：

    (a) `flatChainAct_affine`：`flatChainAct ch off ((1-t)g₁ + t g₂) x
          = (1-t)·flatChainAct ch off g₁ x + t·flatChainAct ch off g₂ x`
    (b) `flatChainAct_linear_activation`：`flatChainAct ch off g ((1-t)p₁ + t p₂)
          = (1-t)·flatChainAct ch off g p₁ + t·flatChainAct ch off g p₂`

**而 (a) 就是仿射像封闭性真正需要的——它说「两个参数给出的两点，其凸组合由参数的凸组合实现」，
`x` 固定。** **⇒ 所以先做 (a)，不做双线性。**

## (a) 的证明计划（下一轮）

**`cons` 支**：

    flatChainAct (cons l rest) off ((1-t)g₁ + t g₂) x
      = flatChainAct rest off' ((1-t)g₁ + t g₂) (flatParamActSafe off ((1-t)g₁ + t g₂) x)

**⇒ 两步**：

1. **`flatParamActSafe_affine`** 给出内层 = `(1-t)·flatParamActSafe off g₁ x + t·flatParamActSafe off g₂ x`；
2. **`rest` 的归纳假设 (a)**，**以 `p₁ = flatParamActSafe off g₁ x`、`p₂ = flatParamActSafe off g₂ x` 代入**。

**⚠ 而第 2 步要求归纳假设接受任意 `x`——所以 (a) 必须对 `x` 全称，而不只是固定的 `x`。
这一点在第 181／182 轮的递归签名里已经是这样（`(x : Fin m → ℝ)` 是递归参数）。**

**⇒ 所以 (a) 应当可以走通；第 182 轮失败的是【双线性】那个更强的形式，不是 (a)。** -/

/-- ⭐⭐⭐ **`flatParamActSafe` 对【激活】线性**——**参数固定时它是 `∑ w i j * x i + c j`，对 `x` 线性。** -/
theorem flatParamActSafe_linear_activation {N a b : ℕ} (off : ℕ) (g : Fin N → ℝ)
    (p₁ p₂ : Fin a → ℝ) (t : ℝ) :
    flatParamActSafe (N := N) (a := a) (b := b) off g
        (fun i => (1 - t) * p₁ i + t * p₂ i)
      = fun j => (1 - t) * flatParamActSafe (N := N) (a := a) (b := b) off g p₁ j
          + t * flatParamActSafe (N := N) (a := a) (b := b) off g p₂ j := by
  funext j
  simp only [flatParamActSafe]
  have hsplit : ∀ i : Fin a,
      readSlot g (slotOf off b i.val j.val) * ((1 - t) * p₁ i + t * p₂ i)
      = (1 - t) * (readSlot g (slotOf off b i.val j.val) * p₁ i)
        + t * (readSlot g (slotOf off b i.val j.val) * p₂ i) := by
    intro i
    ring
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

/-- ⭐⭐⭐ **`flatChainAct` 对【激活】线性**——**参数固定，只有激活取凸组合。**

**⚠ 这是 (a) 的【前提**：`cons` 支的归纳假设接收的是「凸组合激活」，
而目标需要的是「旧激活」，两者之间正是这条定理。**

**与第 182 轮的双线性失败对照**：**双线性把参数与激活【同时】动，产生双重凸组合；
而 (b) 只动激活，(a) 只动参数，各自归纳是齐的。** -/
theorem flatChainAct_linear_activation {N : ℕ} :
    {m n : ℕ} → (ch : Chain m n) → (off : ℕ) → (g : Fin N → ℝ) → (t : ℝ) →
    (p₁ p₂ : Fin m → ℝ) →
    flatChainAct (N := N) ch off g (fun i => (1 - t) * p₁ i + t * p₂ i)
      = fun j => (1 - t) * flatChainAct (N := N) ch off g p₁ j
          + t * flatChainAct (N := N) ch off g p₂ j
  | _, _, .idf n, off, g, t, p₁, p₂ => by
      funext j
      simp only [flatChainAct_idf]
  | _, _, .cons (m := m') (n := n') l rest, off, g, t, p₁, p₂ => by
      funext j
      simp only [flatChainAct]
      rw [flatParamActSafe_linear_activation (N := N) (a := m') (b := n') off g p₁ p₂ t]
      exact congrFun (flatChainAct_linear_activation rest (off + layerParamCount m' n') g t
        (flatParamActSafe (N := N) (a := m') (b := n') off g p₁)
        (flatParamActSafe (N := N) (a := m') (b := n') off g p₂)) j

/-! ## ⚠ 一个必须记录的反例：两层链对参数【不是】仿射的

## 为什么这条重要

**第 179–183 轮一直在追「仿射像在仿射组合下封闭」，以便给一般可实现性一个前提。
第 181 轮证了单层对参数仿射（`flatParamActSafe_affine`），本轮先证了单层对激活线性
（`flatParamActSafe_linear_activation`），然后试图沿链归纳。**

**⚠ 结论是：归纳【失败**，而失败不是技术问题——**命题本身是假的**。

## 为什么必然为假

**两层的链是**：

    z = w₂ · (w₁ · x + b₁) + b₂

**对参数它是【二次**的（`w₁·w₂` 与 `w₂·b₁` 两项）。
**⇒ 凸组合参数给出的不是凸组合输出，而是多出交叉项。**

## 具体反例（宽度 1、两层、x = 1）

**槽位约定**：第 1 层用 `g 0`（权）与 `g 1`（偏）；第 2 层从 `off = 2` 起，用 `g 2` 与 `g 3`。

| 参数 | `w₁` | `b₁` | `w₂` | `b₂` | 输出 `z` |
|:--|--:|--:|--:|--:|--:|
| `gA = [1,0,1,0]` | 1 | 0 | 1 | 0 | **1** |
| `gB = [2,0,2,0]` | 2 | 0 | 2 | 0 | **4** |
| `½ gA + ½ gB = [1.5,0,1.5,0]` | 1.5 | 0 | 1.5 | 0 | **2.25** |

**而 `½·1 + ½·4 = 2.5`。** **`2.25 ≠ 2.5`。**

**⇒ 「两点的凸组合由参数的凸组合实现」在两层时【不成立】。** -/

/-- **两层的具体链**（层内容无关——`flatChainAct` 从 `g` 读参数，层只决定宽度与深度）。 -/
noncomputable def twoLayerProbeRest : MLayer 1 1 := ⟨fun _ _ => 0, fun _ => 0⟩

/-- **两层的具体链**。 -/
noncomputable def twoLayerChain : Chain 1 1 :=
  Chain.cons twoLayerProbeRest (Chain.cons twoLayerProbeRest (Chain.idf 1))

/-- **参数 `[1,0,1,0]`**——输出 `z = 1`。 -/
def twoLayerG₁ : Fin 4 → ℝ := ![1, 0, 1, 0]

/-- **参数 `[2,0,2,0]`**——输出 `z = 4`。 -/
def twoLayerG₂ : Fin 4 → ℝ := ![2, 0, 2, 0]

/-- **输入 `x = 1`**。 -/
def twoLayerX : Fin 1 → ℝ := ![1]

/-- **凸组合参数下的输出是 `9/4`**。 -/
theorem twoLayer_convex_eval :
    flatChainAct (N := 4) twoLayerChain 0
        (fun i => (1 - (1 / 2 : ℝ)) * twoLayerG₁ i + (1 / 2) * twoLayerG₂ i) twoLayerX 0
      = 9 / 4 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount, twoLayerG₁, twoLayerG₂, twoLayerX]
  norm_num

/-- **两个输出点的凸组合是 `5/2`**。 -/
theorem twoLayer_affine_eval :
    (1 - (1 / 2 : ℝ)) * flatChainAct (N := 4) twoLayerChain 0 twoLayerG₁ twoLayerX 0
      + (1 / 2) * flatChainAct (N := 4) twoLayerChain 0 twoLayerG₂ twoLayerX 0
      = 5 / 2 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount, twoLayerG₁, twoLayerG₂, twoLayerX]
  norm_num

/-- ⭐⭐⭐ **`flatChainAct` 对参数【不是】仿射的**——**两层的数值反例。**

**这条否定了「仿射像在仿射组合下封闭」这条路线（对深度 ≥ 2）。**

**⚠ 它不是缺陷**：**多层网络的输出对参数是【多项式】而【不是】仿射的，
这是网络表达力的来源，也正是「符号 ⇄ 权重」不能靠线性代数一步跨过的原因。** -/
theorem flatChainAct_not_affine :
    ¬ ∀ (ch : Chain 1 1) (off : ℕ) (g₁ g₂ : Fin 4 → ℝ) (t : ℝ) (x : Fin 1 → ℝ),
        flatChainAct (N := 4) ch off (fun i => (1 - t) * g₁ i + t * g₂ i) x
          = fun j => (1 - t) * flatChainAct (N := 4) ch off g₁ x j
              + t * flatChainAct (N := 4) ch off g₂ x j := by
  intro h
  have heq := congrFun (h twoLayerChain 0 twoLayerG₁ twoLayerG₂ (1 / 2) twoLayerX) 0
  rw [twoLayer_convex_eval, twoLayer_affine_eval] at heq
  norm_num at heq

/-! ## ⭐ 精确的边界：仿射性在【深度 1】成立，在【深度 ≥ 2】失败

## 为什么这条边界值得单独陈述

**第 185 轮证明了 `flatChainAct_not_affine`：两层链对参数是二次的，所以凸组合不保凸组合。**

**但那不能读成「仿射性完全没用**——**单层时它【确实】成立，
因为单层就是 `flatParamActSafe`，而第 181 轮证了它对参数仿射。**

**⇒ 正确的陈述是**：

| 深度 | 对参数仿射？ | 依据 |
|:--|:--|:--|
| 0（恒等链） | 是（平凡） | 作用是恒等，与 `g` 无关 |
| **1** | **是** | **`flatParamActSafe_affine`（第 181 轮）** |
| **≥ 2** | **否** | **`flatChainAct_not_affine`（第 185 轮，数值反例）** |

**⚠ 这是「仿射像」这条路线能走多远的【完整答案**：
**它恰好在深度 1 上有效，而深度 1 正是一般多层网络【不】满足的情形。** -/

/-- ⭐⭐⭐ **单层链对参数仿射**——**第 185 轮反例的【正向对照**。

**单层链 `Chain.cons l (Chain.idf n)` 的作用就是 `flatParamActSafe`，
所以它对参数仿射（第 181 轮），对激活线性（第 183 轮）。** -/
theorem flatChainAct_oneLayer_affine {N m n : ℕ} (l : MLayer m n) (off : ℕ)
    (g₁ g₂ : Fin N → ℝ) (t : ℝ) (x : Fin m → ℝ) :
    flatChainAct (N := N) (Chain.cons l (Chain.idf n)) off
        (fun i => (1 - t) * g₁ i + t * g₂ i) x
      = fun j => (1 - t) * flatChainAct (N := N) (Chain.cons l (Chain.idf n)) off g₁ x j
          + t * flatChainAct (N := N) (Chain.cons l (Chain.idf n)) off g₂ x j := by
  funext j
  simp only [flatChainAct]
  exact congrFun (flatParamActSafe_affine (N := N) (a := m) (b := n) off g₁ g₂ t x) j

/-- ⭐⭐ **零层链对参数仿射（平凡）**——**作用是恒等，与 `g` 完全无关。** -/
theorem flatChainAct_zeroLayer_affine {N n : ℕ} (off : ℕ)
    (g₁ g₂ : Fin N → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    flatChainAct (N := N) (Chain.idf n) off
        (fun i => (1 - t) * g₁ i + t * g₂ i) x
      = fun j => (1 - t) * flatChainAct (N := N) (Chain.idf n) off g₁ x j
          + t * flatChainAct (N := N) (Chain.idf n) off g₂ x j := by
  funext j
  simp only [flatChainAct_idf]
  ring

end Lattice.Core
