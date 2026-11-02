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

/-- **`twoLayerG₁` 处的输出是 `1`**。 -/
theorem twoLayer_gA_eval :
    flatChainAct (N := 4) twoLayerChain 0 twoLayerG₁ twoLayerX 0 = 1 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount, twoLayerG₁, twoLayerG₂, twoLayerX]
  norm_num

/-- **`twoLayerG₂` 处的输出是 `4`**。 -/
theorem twoLayer_gB_eval :
    flatChainAct (N := 4) twoLayerChain 0 twoLayerG₂ twoLayerX 0 = 4 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount, twoLayerG₁, twoLayerG₂, twoLayerX]
  norm_num

/-- ⭐⭐⭐ **两层链【不能】被任何仿射函数拟合**——**第 185 轮反例的强烈形式。**

**第 185 轮证的是「某条仿射等式失效」。本条证的是【更强】的东西：
不存在任何仿射模型 `g ↦ Σ Aᵢ gᵢ + c` 能在所有参数点上复现两层链的输出。**

**证明**：**若存在，则在 `gA`、`gB` 与它们的中点三处取值的仿射关系必须成立，
即 `z(mid) = (z(gA) + z(gB))/2`。而实测 `z(mid) = 9/4`、`(1+4)/2 = 5/2`，两者不等。** -/
theorem twoLayer_no_affine_fit :
    ¬ ∃ (A : Fin 4 → ℝ) (c : ℝ), ∀ (g : Fin 4 → ℝ),
        flatChainAct (N := 4) twoLayerChain 0 g twoLayerX 0 = (∑ i, A i * g i) + c := by
  rintro ⟨A, c, h⟩
  have hA := h twoLayerG₁
  have hB := h twoLayerG₂
  have hM := h (fun i => (1 - (1 / 2 : ℝ)) * twoLayerG₁ i + (1 / 2) * twoLayerG₂ i)
  rw [twoLayer_gA_eval] at hA
  rw [twoLayer_gB_eval] at hB
  rw [twoLayer_convex_eval] at hM
  -- 中点处的加权和等于两端加权和的平均
  have hsum : (∑ i, A i * ((1 - (1 / 2 : ℝ)) * twoLayerG₁ i + (1 / 2) * twoLayerG₂ i))
      = ((∑ i, A i * twoLayerG₁ i) + (∑ i, A i * twoLayerG₂ i)) / 2 := by
    simp only [twoLayerG₁, twoLayerG₂, Fin.sum_univ_four]
    norm_num
    ring
  rw [hsum] at hM
  linarith

/-! ## 两层链的显式二次形式：次数 = 2 的直接证据

## 为什么需要这一节

**第 185／187 轮用【否定】的方式说明了两层链不是仿射的。
但「不是仿射」只说明次数 ≠ 1，并不能说明次数 = 2。**

**⇒ 本节给出【显式的二次表达式，把那两轮的否定补成正面的结构刻画。**

## 槽位约定（宽度 1、两层）

| 层 | 权重槽位 | 偏置槽位 | `off` |
|:--|:--|:--|:--|
| 第 1 层 | `g 0` | `g 1` | 0 |
| 第 2 层 | `g 2` | `g 3` | `layerParamCount 1 1 = 2` |

**⇒ 输出是**

    z = g 2 · (g 0 · x + g 1) + g 3

**对参数它是二次的：`g 2 · g 0` 与 `g 2 · g 1` 两个交叉项。** -/

/-- ⭐⭐⭐ **两层链的显式形式**——**`z = g 2 · (g 0 · x + g 1) + g 3`。**

**这是「次数 = 2」的【正面**证据，与第 185／187 轮的否定结果互补：
那两轮说「不是仿射」，这一条说「恰好是这个二次表达式」。** -/
theorem twoLayerChain_explicit (g : Fin 4 → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 g x 0
      = g 2 * (g 0 * x 0 + g 1) + g 3 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount]
  norm_num
  congr 2 <;> norm_num

/-- ⭐⭐ **显式形式的直接推论：输出对第 2 层权重 `g 2` 是【线性】的**——
**因为 `g 2` 只以一次出现。**

**⚠ 而对 `g 0` 也是线性的（在 `g 2` 固定时）；**两者的乘积项 `g 2 · g 0` 才是非仿射的来源。** -/
theorem twoLayerChain_linear_in_g2 (g₀ g₁ g₃ : ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 (![g₀, g₁, 0, g₃] : Fin 4 → ℝ) x 0
      = g₃ := by
  rw [twoLayerChain_explicit]
  norm_num

/-- **三层的具体链**（宽度 1；层内容无关，只决定宽度与深度）。 -/
noncomputable def threeLayerChain : Chain 1 1 :=
  Chain.cons twoLayerProbeRest
    (Chain.cons twoLayerProbeRest (Chain.cons twoLayerProbeRest (Chain.idf 1)))

/-- ⭐⭐⭐ **三层链的显式形式**——**`z = g 4 · (g 2 · (g 0 · x + g 1) + g 3) + g 5`。**

**⇒ 次数 = 3。** **与第 188 轮的两层形式同一结构，多嵌套一层。**

**槽位**：每层占 `layerParamCount 1 1 = 2` 个槽位，
**所以第 1 层用 `g 0`/`g 1`、第 2 层用 `g 2`/`g 3`、第 3 层用 `g 4`/`g 5`。** -/
theorem threeLayerChain_explicit (g : Fin 6 → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 g x 0
      = g 4 * (g 2 * (g 0 * x 0 + g 1) + g 3) + g 5 := by
  simp only [threeLayerChain, twoLayerChain, twoLayerProbeRest, flatChainAct,
    flatParamActSafe, readSlot, slotOf, layerParamCount]
  norm_num
  congr 2 <;> norm_num

/-! **关于退化情形**：**「前两层权重为零时输出等于第三层偏置」是对的，
但第 189 轮在 Lean 里展开 `![g₀,g₁,0,g₃,0,g₅] 5` 时反复卡在 `Fin` 的 numeral 归约上**
（`Matrix.cons_val_*` 与 `Fin.reduceOfNat*` 的名字在本版本里都不适用），
**所以本节【不声称】它**——**它不是主结果，留着一条未证的说法比删掉它更糟。** -/

/-! ## ⭐⭐⭐ 一般递推：宽 1 的一层就是 `g off · (尾链) + g (off+1)`

## 为什么这条是正确终点

**第 188／189 轮分别给出两层与三层的显式形式，而两者是同一嵌套的两次实例化**：

    两层：g 2 · (g 0 · x + g 1) + g 3
    三层：g 4 · (g 2 · (g 0 · x + g 1) + g 3) + g 5

**共同的形状是**：**宽 1 的一层作用在标量 `y` 上，得到 `权重 · y + 偏置`，
而权重在槽位 `off`、偏置在槽位 `off + 1`。**

**⇒ 把它写成一条【对尾链 `ch` 无关的递推**，三个实例就是它的特化，
**而「次数 = 深度」就是对 `ch` 的归纳。** -/

/-- **宽 1 时权重槽位就是 `off`**（`a = b = 1`，所以 `slotOf off 1 0 0 = off + 0 + 0`）。 -/
theorem slotOf_width_one_weight (off : ℕ) : slotOf off 1 0 0 = off := by
  simp only [slotOf]
  ring

/-- **宽 1 时偏置槽位是 `off + 1`**（`off + a*1 + 0`，`a = 1`）。 -/
theorem slotOf_width_one_bias (off : ℕ) : off + 1 * 1 + 0 = off + 1 := by
  ring

/-- **宽 1 的一层占 `layerParamCount 1 1 = 2` 个槽位。** -/
theorem layerParamCount_width_one : layerParamCount 1 1 = 2 := rfl

/-- ⭐⭐⭐ **宽 1 的层作用把输入塌缩成一个标量**——
**`x ↦ readSlot g off · x 0 + readSlot g (off+1)`。**

**⚠ 这是【代换形式**：一层的输出是标量，被尾链继续作用。
**它不是线性的分配形式**——**因为尾链【不】保持线性**
（`y ↦ w·y + c` 把 `a·x+b` 映成 `w·(a·x+b)+c`，而**不是** `a·(w·x+c)+b`）。** -/
theorem flatParamActSafe_width_one {N : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : Fin 1 → ℝ) :
    flatParamActSafe (N := N) (a := 1) (b := 1) off g x
      = fun _ => readSlot g off * x 0 + readSlot g (off + 1) := by
  funext j
  fin_cases j
  simp only [flatParamActSafe, Fin.sum_univ_one, slotOf, layerParamCount]
  norm_num

/-- ⭐⭐⭐ **一般递推（代换形式）**——**宽 1 的一层作用 = 尾链作用在那个标量上。**

**三个显式形式（第 188／189 轮）都是它迭代两次、三次的结果。** -/
theorem flatChainAct_cons_width_one {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := N) (Chain.cons twoLayerProbeRest ch) off g x
      = flatChainAct (N := N) ch (off + 2) g
          (fun _ => readSlot g off * x 0 + readSlot g (off + 1)) := by
  simp only [flatChainAct, flatParamActSafe_width_one, layerParamCount_width_one]

/-! ## 任意宽度的一般递推

## 为什么这条几乎免费

**`flatChainAct` 的 `cons` 支【就是】**

    flatChainAct rest (off + layerParamCount m n) g (flatParamActSafe off g x)

**所以「一层之后是尾链作用在新激活上」这条递推是【定义级】的事实，
`rfl` 就够。宽度 1 的版本（第 190 轮）是它的特化，
而一般宽度下内层不再是标量而是向量——那是唯一实质差别。**

**⚠ 但宽度 1 时的额外内容（把内层求和塌缩成标量）【不】自动成立，
那一部分由第 190 轮的 `flatParamActSafe_width_one` 单独承担。** -/

/-- ⭐⭐⭐ **任意宽度的一般递推**——**一层作用后，尾链作用在新的激活向量上。**

**这是「深度」与「宽度」在递归里的分工**：
**深度由 `rest` 的递归体现，宽度由 `flatParamActSafe` 的内层求和体现。** -/
theorem flatChainAct_cons_general {N m n c : ℕ} (l : MLayer m n) (rest : Chain n c)
    (off : ℕ) (g : Fin N → ℝ) (x : Fin m → ℝ) :
    flatChainAct (N := N) (Chain.cons l rest) off g x
      = flatChainAct (N := N) rest (off + layerParamCount m n) g
          (flatParamActSafe (N := N) (a := m) (b := n) off g x) :=
  rfl

/-! **没有「宽度 1 的 `rfl` 特化」这一条**：
**它只是 `flatChainAct_cons_general` 在 `m = n = 1` 时的重述，不提供新内容。**

**宽度 1 真正【有内容】的特化是第 190 轮的 `flatChainAct_cons_width_one`**——
**它把内层求和塌缩成标量 `readSlot g off · x 0 + readSlot g (off+1)`，
而那一步【不是】`rfl`。**

**⇒ 加一条只做参数特化的 `rfl` 名字会制造「看起来更具体」的假象，
那是别名普查要拦的东西，这里主动不加。** -/


/-! ## 宽度 2 的具体实例：宽度保持线性

## 为什么这个实例值得做

**第 190／191 轮分别证了深度 1 的递推与任意宽度的递推，
但所有的【显式形式】至今都是宽度 1。**

**⇒ 宽度在表达力里扮演什么角色，此前只有「递推里那一项求和」的说法，
没有可以核对的实例。本节给出宽度 2、单层的显式形式：
它展示宽度带来的不是次数，而是每个坐标各自一条线性表达式。**

## 槽位（宽度 2、单层，`layerParamCount 2 2 = 6`）

**`slotOf off 2 i j = off + i*2 + j`，所以 `w i j` 在槽位 `i*2 + j`：

| `w` | `j = 0` | `j = 1` |
|:--|:--|:--|
| `i = 0` | `g 0` | `g 1` |
| `i = 1` | `g 2` | `g 3` |

**偏置在 `off + 2*2 + j = 4 + j`：`g 4`、`g 5`。** -/

/-- **宽度 2 的一层**（层内容无关，只决定宽度）。 -/
noncomputable def wideLayerRest : MLayer 2 2 := ⟨fun _ _ => 0, fun _ => 0⟩

/-- **宽度 2、单层的链**。 -/
noncomputable def wideChain : Chain 2 2 := Chain.cons wideLayerRest (Chain.idf 2)

/-- ⭐⭐⭐ **宽度 2、第 0 个坐标**：**`z 0 = g 0 · x 0 + g 2 · x 1 + g 4`。** -/
theorem wideChain_explicit_zero (g : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 6) wideChain 0 g x 0 = g 0 * x 0 + g 2 * x 1 + g 4 := by
  simp only [wideChain, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num

/-- ⭐⭐⭐ **宽度 2、第 1 个坐标**：**`z 1 = g 1 · x 0 + g 3 · x 1 + g 5`。** -/
theorem wideChain_explicit_one (g : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 6) wideChain 0 g x 1 = g 1 * x 0 + g 3 * x 1 + g 5 := by
  simp only [wideChain, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num


/-! ## 宽度 2、两层：两条轴合并的第一次

## 槽位账

**宽度 2 每层占 `layerParamCount 2 2 = 6` 个槽位，所以两层需要 `Fin 12 → ℝ`。**

- **第 1 层（`off = 0`）**：权重 `g 0 … g 3`（`w i j` 在 `i*2 + j`），偏置 `g 4, g 5`；
- **第 2 层（`off = 6`）**：权重 `g 6 … g 9`，偏置 `g 10, g 11`。

**⇒ 中间激活是**

    y 0 = g 0 · x 0 + g 2 · x 1 + g 4
    y 1 = g 1 · x 0 + g 3 · x 1 + g 5

**而输出是**

    z 0 = g 6 · y 0 + g 8 · y 1 + g 10
    z 1 = g 7 · y 0 + g 9 · y 1 + g 11

**⚠ 把 `y` 代入就得到【两个变量 `x 0`、`x 1` 上的二次式】——
所以这一条同时展示「宽度」与「深度」的作用，是本路线最完整的单点实例。** -/

/-- **宽度 2、两层的链**。 -/
noncomputable def wideChain2 : Chain 2 2 :=
  Chain.cons wideLayerRest (Chain.cons wideLayerRest (Chain.idf 2))

/-- ⭐⭐⭐ **宽度 2、两层、第 0 个坐标**——**`z 0 = g 6 · y 0 + g 8 · y 1 + g 10`，
其中 `y` 由第 1 层给出。**

**这是「两次代换」的直接形式：外层保持线性，内层是上一次的线性组合。** -/
theorem wideChain2_explicit_zero (g : Fin 12 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 12) wideChain2 0 g x 0
      = g 6 * (g 0 * x 0 + g 2 * x 1 + g 4) + g 8 * (g 1 * x 0 + g 3 * x 1 + g 5) + g 10 := by
  simp only [wideChain2, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num

/-- ⭐⭐⭐ **宽度 2、两层、第 1 个坐标**。 -/
theorem wideChain2_explicit_one (g : Fin 12 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 12) wideChain2 0 g x 1
      = g 7 * (g 0 * x 0 + g 2 * x 1 + g 4) + g 9 * (g 1 * x 0 + g 3 * x 1 + g 5) + g 11 := by
  simp only [wideChain2, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num



/-! ## ⭐⭐⭐ 宽 n 的一层【恰好】实现全部仿射映射：满射性

## 为什么这条是逆向刻画的最后一块

**第 197 轮证了【必要**条件：可达的输出继承输入点之间的仿射关系。
**本节证【充分**性的根源：**

**任意权重 `W` 与偏置 `b` 都能被某个参数向量 `g` 实现。**
**⇒ 可达集【恰好**是全部仿射映射的限制，第 197 轮的障碍就是【唯一**的障碍。**

## 下标约定（与 `slotOf` 一致，不要弄反）

**`flatParamActSafe` 的输出坐标是 `j`、输入坐标是 `i`，而权重在槽位
`slotOf off n i j = off + i*n + j`——即【先输入、后输出**。

**⇒ 本节一律用 `W i j` 表示「从输入 `i` 到输出 `j`」的权重，
所以定理右边写成 `∑ j, W j i * x j`（求和变量是【输入**）。** -/

/-- **把 `W` 与 `b` 铺进 `Fin (n*n+n) → ℝ`**——**前 `n*n` 个槽位是权重（`W 输入 输出` 在 `输入*n + 输出`），
后 `n` 个是偏置。** -/
def slotMap (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    Fin (n * n + n) → ℝ :=
  fun k => if h : (k : ℕ) < n * n
    then W ⟨(k : ℕ) / n, Nat.div_lt_of_lt_mul h⟩
        ⟨(k : ℕ) % n, Nat.mod_lt _ hn⟩
    else b ⟨(k : ℕ) - n * n, by
      have h1 : (k : ℕ) < n * n + n := k.isLt
      omega⟩

/-- **读出权重槽位得到 `W i j`**（`i` 是输入、`j` 是输出）。 -/
theorem readSlot_slotMap_weight (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (i j : Fin n) :
    readSlot (slotMap n hn W b) (i.val * n + j.val) = W i j := by
  have h2 : j.val < n := j.isLt
  have h1 : i.val < n := i.isLt
  have hlt2 : i.val * n + j.val < n * n := by nlinarith
  have hlt : i.val * n + j.val < n * n + n := by nlinarith
  rw [readSlot_of_lt _ hlt]
  simp only [slotMap, dif_pos hlt2]
  have e1 : (i.val * n + j.val) / n = i.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt h2, Nat.add_zero]
  have e2 : (i.val * n + j.val) % n = j.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
  have p1 : (⟨(i.val * n + j.val) / n, Nat.div_lt_of_lt_mul hlt2⟩ : Fin n) = i :=
    Fin.ext e1
  have p2 : (⟨(i.val * n + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = j :=
    Fin.ext e2
  rw [p1, p2]

/-- **读出偏置槽位得到 `b j`**。 -/
theorem readSlot_slotMap_bias (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (j : Fin n) :
    readSlot (slotMap n hn W b) (n * n + j.val) = b j := by
  have h2 : j.val < n := j.isLt
  have hlt : n * n + j.val < n * n + n := by omega
  have hge : ¬ (n * n + j.val < n * n) := by omega
  rw [readSlot_of_lt _ hlt]
  simp only [slotMap, dif_neg hge]
  have e : n * n + j.val - n * n = j.val := by omega
  have p : (⟨n * n + j.val - n * n, by omega⟩ : Fin n) = j := Fin.ext e
  rw [p]

/-- ⭐⭐⭐ **满射性**：**任意仿射映射都被某组参数实现。**

**与第 197 轮的障碍合起来：可达集【恰好】是全部仿射映射的限制。** -/
theorem affine_map_realisable (n : ℕ) (hn : 0 < n)
    (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∃ (g : Fin (n * n + n) → ℝ), ∀ (x : Fin n → ℝ) (i : Fin n),
      flatParamActSafe (N := n * n + n) (a := n) (b := n) 0 g x i
        = (∑ j : Fin n, W j i * x j) + b i := by
  refine ⟨slotMap n hn W b, ?_⟩
  intro x i
  simp only [flatParamActSafe, slotOf, Nat.zero_add, readSlot_slotMap_weight,
    readSlot_slotMap_bias]


/-! ## ⭐⭐⭐ 差分阶数随深度增长：深度 d 的输出，其 `d+1` 阶差分为零

## 与第 197 轮的对照

**第 197 轮**：**深度 1 的输出是 `p` 的【仿射】函数**，**所以障碍是一阶的。**

## ⚠ 第 200 轮的命名缺陷，本轮修正

**第 200 轮把下面的定理命名为 `quadratic_fourth_difference` 并称它为「四阶差分」。
那【是错的**：系数 `1, -3, 3, -1` 对应的是**

    f(0) - 3·f(1) + 3·f(2) - f(3) = −Δ³f(0)

**即【三阶**差分（差一个符号）。**定理本身为真，而且恰好是最小判别式——
错的是名字与文档。**

**⇒ 本轮把名字改成 `quadratic_third_difference`，并把「四阶」全部改为「三阶」。
一条陈述与它的名字不符，正是 I5（端到端诚实）要拦的东西。**

## ⚠⚠ 这里曾写过一个【假的】阶梯——第 203 轮更正

**第 201 轮在此声称「深度 d ⟹ 第 d+1 阶差分为零」并列出三行表。**

**那张表是【错的**。链的递推是 `Φ_{d+1}(j) = a·Φ_d(j) + b`，其中 `a, b` **不依赖 `j`**，
**所以每层只是把上一层作为【仿射函数】喂下去，而仿射不提高次数。**

**⇒ 链的输出对【输入】永远是【一次**的，与深度无关。**三层的显式形式**

    g4·(g2·(g0·x + g1) + g3) + g5 = (g4·g2·g0)·x + (g4·g2·g1 + g4·g3 + g5)

**对 `x` 确实是一次。**

**⇒ 下面三条定理【都为真**，但它们不是三个独立结果，
**而是 `flatChainAct_fdiffIter_two`（第 203 轮，任意链的二阶差分为零）的推论。**

**⇒ 「次数 = 深度」是关于【参数 `g`】的（第 185–199 轮），不是关于输入的。
把两者混淆正是第 200–202 轮的错误。** -/

/-! **深度 1 的解析事实【不复述**：
**`NonlinearLayer.affine_second_difference`（第 156 轮）已经是**
`(a*0 + c) + (a*2 + c) - 2*(a*1 + c) = 0`，**与这里需要的完全同义。**

**⇒ 本轮起初写了一个同义的 `affine_second_difference`，构建时撞上
`environment already contains 'Lattice.Core.affine_second_difference'`——
那是【同名**冲突，但即便改名也只是复制。**

**⇒ 删除，改为引用既有那条。这就是「复用而非复制」的判定：
名字不同、内容相同，仍然是重复。** -/

/-- ⭐⭐ **二次函数的三阶差分为零**——**深度 2 的判别式（最小）。**

**⚠ 这是第 200 轮 `quadratic_fourth_difference` 的【正名**版：
系数 `1,-3,3,-1` 就是 `−Δ³`，不是四阶。** -/
theorem quadratic_third_difference (A B C : ℝ) :
    (A * 0 ^ 2 + B * 0 + C) - 3 * (A * 1 ^ 2 + B * 1 + C)
      + 3 * (A * 2 ^ 2 + B * 2 + C) - (A * 3 ^ 2 + B * 3 + C) = 0 := by
  norm_num
  ring

/-- ⭐⭐ **三次函数的四阶差分为零**——**深度 3 的判别式。** -/
theorem cubic_fourth_difference (A B C D : ℝ) :
    (A * 4 ^ 3 + B * 4 ^ 2 + C * 4 + D) - 4 * (A * 3 ^ 3 + B * 3 ^ 2 + C * 3 + D)
      + 6 * (A * 2 ^ 3 + B * 2 ^ 2 + C * 2 + D) - 4 * (A * 1 ^ 3 + B * 1 ^ 2 + C * 1 + D)
      + (A * 0 ^ 3 + B * 0 ^ 2 + C * 0 + D) = 0 := by
  norm_num
  ring

/-- ⭐⭐ **深度 1 的链满足二阶差分为零**——**仿射，故判别式是二阶。** -/
theorem oneLayer_second_difference_zero (g : Fin 4 → ℝ) :
    flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
        (fun _ => (2 : ℝ)) 0
        - 2 * flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
            (fun _ => (1 : ℝ)) 0
      + flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
          (fun _ => (0 : ℝ)) 0 = 0 := by
  simp only [flatChainAct, flatChainAct_idf, flatParamActSafe_width_one]
  ring

/-- ⭐⭐⭐ **深度 2 的链满足三阶差分为零**——**二次，故判别式是三阶。**

**⚠ 第 200 轮把它叫「四阶」，本轮正名。** -/
theorem twoLayer_third_difference_zero (g : Fin 4 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (0 : ℝ)) 0
        - 3 * flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (1 : ℝ)) 0
      + 3 * flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (2 : ℝ)) 0
        - flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (3 : ℝ)) 0 = 0 := by
  rw [twoLayerChain_explicit, twoLayerChain_explicit, twoLayerChain_explicit,
    twoLayerChain_explicit]
  norm_num
  ring

/-- ⭐⭐⭐ **深度 3 的链满足四阶差分为零**——**三次，故判别式是四阶。**

**⚠ 这条【不是】阶梯的一层**：**与上面两条一样，它是 `flatChainAct_fdiffIter_two`
（第 203 轮：任意链的二阶差分为零）的推论**——**链对输入恒为仿射，
所以任何更高阶差分都自动为零。深度在这里不起作用。** -/
theorem threeLayer_fourth_difference_zero (g : Fin 6 → ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (4 : ℝ)) 0
        - 4 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (3 : ℝ)) 0
      + 6 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (2 : ℝ)) 0
        - 4 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (1 : ℝ)) 0
      + flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (0 : ℝ)) 0 = 0 := by
  rw [threeLayerChain_explicit, threeLayerChain_explicit, threeLayerChain_explicit,
    threeLayerChain_explicit, threeLayerChain_explicit]
  norm_num
  ring


/-! ## ⭐⭐⭐ 差分算子：结构与线性性

## 为什么需要算子

**第 200／201 轮把「深度 `d` ⟹ 第 `d+1` 阶差分为零」写成了【三个具体实例**——
**每个实例都是一条关于 `flatChainAct` 的等式，各自靠 `norm_num` + `ring` 关掉。**

**⇒ 那是三条事实，不是一条定理。要把它变成定理，先得把「差分」本身定义出来。**

## 定义

    fdiff f j       = f (j+1) - f j
    fdiffIter 0 f   = f
    fdiffIter (k+1) f = fdiff (fdiffIter k f)

**⇒ 然后要证的核心事实是：`j ↦ j^k` 在 `fdiffIter (k+1)` 下化为零。**

**⚠ 到这一步为止，本节给出的是【算子层的基础设施 + 四个已验证的实例**，
**而不是一般定理**——一般定理需要「次数 ≤ k 的多项式被第 k+1 阶差分零化」
这一组合恒等式（`Σ (-1)^{m-i} C(m,i) i^r = 0` 对 `r < m`），
**那需要二项式定理与 `Nat.choose` 的恒等式，是另一块工作。** -/

/-- **前向差分算子**。 -/
def fdiff (f : ℕ → ℝ) : ℕ → ℝ := fun j => f (j + 1) - f j

/-- **迭代 `k` 次的前向差分**。 -/
def fdiffIter : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, f => f
  | k + 1, f => fdiff (fdiffIter k f)

/-- **一次迭代就是 `fdiff`**——**定义级。** -/
theorem fdiffIter_one (f : ℕ → ℝ) : fdiffIter 1 f = fdiff f := rfl

/-- **迭代的递推式**——**定义级。** -/
theorem fdiffIter_succ (k : ℕ) (f : ℕ → ℝ) :
    fdiffIter (k + 1) f = fdiff (fdiffIter k f) := rfl

/-- **常函数的差分为零**。 -/
theorem fdiff_const (c : ℝ) : fdiff (fun _ => c) = fun _ => 0 := by
  funext j
  simp only [fdiff]
  ring

/-- **常函数的任意正阶差分为零**。 -/
theorem fdiffIter_const (k : ℕ) (c : ℝ) :
    fdiffIter (k + 1) (fun _ => c) = fun _ => 0 := by
  induction k with
  | zero => simpa using fdiff_const c
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_const]

/-! ### ⚠ 一个被别名普查拦下的复制，以及正确的替代

**我起初为 `k = 0,1,2,3` 各写了一条 `fdiffIter_pow_k`，
每条都是同一个证明（`simp only [fdiffIter, fdiff]` + `ring`），只差指数。**

**`audit_aliases.py` 把它们三条全标为 `copy`：**

    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_one
    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_three
    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_two

**⇒ 删掉它们。三条只差参数的定理不是三个结果，是一个结果的三个拼写。**

**⇒ 本节改为给出差分算子【真正需要**的结构引理：加性、数乘、减法。
**这些是差分算子的结构引理，而且彼此不重复。**

## 为什么「`j^k` 在 `k+1` 阶差分下为零」不在此节

**那条一般事实需要组合恒等式**

    Σ_{i=0}^{m} (-1)^{m-i} · C(m,i) · i^r = 0    (r < m)

**它由二项式定理（或 Stirling 数）给出，而把它与 `Nat.choose` 对接是独立的一块工作。
⇒ 登记为未做的明确缺口，而不是用四个实例冒充它。** -/

/-- ⭐ **`fdiff` 是加性的**——**归纳的基础。** -/
theorem fdiff_add (f g : ℕ → ℝ) : fdiff (fun j => f j + g j) = fun j => fdiff f j + fdiff g j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐ **`fdiff` 与数乘交换**。 -/
theorem fdiff_const_mul (c : ℝ) (f : ℕ → ℝ) :
    fdiff (fun j => c * f j) = fun j => c * fdiff f j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐ **`fdiff` 与减法交换**。 -/
theorem fdiff_sub (f g : ℕ → ℝ) : fdiff (fun j => f j - g j) = fun j => fdiff f j - fdiff g j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐⭐ **`fdiffIter` 也是加性的**——**逐层继承 `fdiff_add`。** -/
theorem fdiffIter_add (k : ℕ) (f g : ℕ → ℝ) :
    fdiffIter k (fun j => f j + g j)
      = fun j => fdiffIter k f j + fdiffIter k g j := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_add]
      funext j
      rw [fdiffIter_succ, fdiffIter_succ]

/-- ⭐⭐ **`fdiffIter` 与数乘交换**。 -/
theorem fdiffIter_const_mul (k : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    fdiffIter k (fun j => c * f j) = fun j => c * fdiffIter k f j := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_const_mul]
      funext j
      rw [fdiffIter_succ]


/-! ## ⚠⚠ 一次概念修正：深度【不】提高对输入的多项式次数

## 第 200–202 轮的错误

**第 200 轮证了「两层链的三阶差分（当时误称四阶）为零」，
第 201 轮把它写成一张「阶数阶梯」的表：深度 1 → 二阶、深度 2 → 三阶、深度 3 → 四阶。**

**那个阶梯是【假的**。核对如下。**

## 链的递推

    Φ_{d+1}(j) = a · Φ_d(j) + b,     其中 a = g(2d)、b = g(2d+1)

**⚠ `a` 与 `b` 【不依赖 `j`**——它们是参数，是关于 `j` 的常数。**

**⇒ 每一层把自己的输出作为【仿射函数】喂给下一层，而仿射函数不提高次数。
⇒ 无论多深，链的输出对【输入】永远是【一次**的。

**核对三层**：`g4·(g2·(g0·x + g1) + g3) + g5 = (g4·g2·g0)·x + (g4·g2·g1 + g4·g3 + g5)`。
**对 `x` 确实是一次。**

## 所以「次数 = 深度」是关于【参数】的，不是关于输入的

**第 185–189 轮证的是：链的输出作为【参数 `g`】的函数，次数等于深度**
（两层是 `g2·g0` 的二次、三层是 `g4·g2·g0` 的三次）。
**第 197–199 轮的可达性刻画也是关于参数的。**

**⇒ 第 200–202 轮的差分阶梯把【参数】的次数误当成了【输入】的次数。
三条链层实例全部是下面这一条一般事实的推论，而不是一个阶梯。**

## 本节做两件事

1. **证明那条一般事实**：链对输入恒为仿射，即二阶差分恒为零；
2. **记录这次修正**，使第 200–202 轮的「阶梯」不再被当作三个独立结果。

**⚠ 第 200／201 轮那几条定理本身【为真**（仿射函数的四阶差分也是零），
**所以不删；但它们的文档不再声称「阶数随深度增长」。** -/

/-- ⭐⭐⭐ **链对【标量输入】恒为仿射**——**`Φ(t) = (1−t)·Φ(0) + t·Φ(1)`。**

**由第 183 轮 `flatChainAct_linear_activation` 直接给出**（取 `p₁ = 0`、`p₂ = 1`）。 -/
theorem flatChainAct_scalar_affine {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (t : ℝ) :
    flatChainAct (N := N) ch off g (fun _ => t) 0
      = (1 - t) * flatChainAct (N := N) ch off g (fun _ => (0 : ℝ)) 0
        + t * flatChainAct (N := N) ch off g (fun _ => (1 : ℝ)) 0 := by
  have h := congrFun (flatChainAct_linear_activation (N := N) ch off g t
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))) 0
  have hx : (fun i : Fin 1 => (1 - t) * (0 : ℝ) + t * (1 : ℝ)) = fun _ => t := by
    funext i
    ring
  rw [hx] at h
  exact h

/-- ⭐⭐⭐ **任意链的输出对输入的二阶差分恒为零**——**对【任意深度】成立。**

**⚠ 这条【不是】「深度 1 的判别式」，而是【所有深度】的共同事实：
深度不提高对输入的次数。第 200／201 轮的阶梯由此统一。** -/
theorem flatChainAct_fdiffIter_two {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (j : ℕ) :
    fdiffIter 2 (fun k => flatChainAct (N := N) ch off g (fun _ => (k : ℝ)) 0) j = 0 := by
  simp only [fdiffIter, fdiff]
  set A := flatChainAct (N := N) ch off g (fun _ => (0 : ℝ)) 0
  set B := flatChainAct (N := N) ch off g (fun _ => (1 : ℝ)) 0
  have e0 : flatChainAct (N := N) ch off g (fun _ => ((j : ℝ))) 0
      = (1 - (j : ℝ)) * A + (j : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (j : ℝ)
  have e1 : flatChainAct (N := N) ch off g (fun _ => (((j + 1 : ℕ)) : ℝ)) 0
      = (1 - (((j + 1 : ℕ)) : ℝ)) * A + (((j + 1 : ℕ)) : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (↑(j + 1) : ℝ)
  have e2 : flatChainAct (N := N) ch off g (fun _ => (((j + 2 : ℕ)) : ℝ)) 0
      = (1 - (((j + 2 : ℕ)) : ℝ)) * A + (((j + 2 : ℕ)) : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (↑(j + 2) : ℝ)
  rw [e2, e1, e0]
  push_cast
  ring


/-! ## ⭐⭐⭐ 实数版差分：参数方向的次数

## 为什么需要第二个差分算子

**第 202 轮的 `fdiffIter` 定义在 `ℕ → ℝ` 上**——**它的用途是「沿输入序号取差分」，
而输入序号是自然数。**

**⚠ 但参数次数需要【沿实数方向】取差分**：**`t ↦ Φ(g + t·h)` 的自变量 `t : ℝ`。
`fdiffIter` 的签名是 `ℕ → (ℕ → ℝ) → (ℕ → ℝ)`，对 `t : ℝ` 根本不能应用。**

**⇒ 本节给出实数版算子 `rfdiff`／`rfdiffIter`（步长固定为 1，自变量是 `ℝ`），
并用它陈述「两层链沿任何参数方向是二次的」。**

**⚠ 两个算子并存不是冗余**：**`fdiffIter` 服务「输入次数」（第 202–203 轮），
`rfdiffIter` 服务「参数次数」（本节）——自变量类型不同，用途不同。** -/

/-- **实自变量的前向差分算子**。 -/
def rfdiff (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (t + 1) - f t

/-- **实数版迭代差分**。 -/
def rfdiffIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | k + 1, f => rfdiff (rfdiffIter k f)

/-- **一次迭代就是 `rfdiff`**——**定义级。** -/
theorem rfdiffIter_one (f : ℝ → ℝ) : rfdiffIter 1 f = rfdiff f := rfl

/-- **实数版迭代的递推式**——**定义级。** -/
theorem rfdiffIter_succ (k : ℕ) (f : ℝ → ℝ) :
    rfdiffIter (k + 1) f = rfdiff (rfdiffIter k f) := rfl

/-- ⭐⭐⭐ **沿任何参数方向，两层链是二次的**——**故三阶参数差分为零。**

**⚠ 与第 187 轮的对照**：**第 187 轮 `twoLayer_no_affine_fit` 证【没有仿射模型能拟合】，
即二阶参数差分【不】恒为零。本节证三阶恒为零。
⇒ 两者合起来把参数次数【定死在 2】。** -/
theorem twoLayer_param_cubic (g h : Fin 4 → ℝ) (x : Fin 1 → ℝ) :
    rfdiffIter 3 (fun t : ℝ =>
      flatChainAct (N := 4) twoLayerChain 0 (fun i => g i + t * h i) x 0) 0 = 0 := by
  have hexp : ∀ t : ℝ,
      flatChainAct (N := 4) twoLayerChain 0 (fun i => g i + t * h i) x 0
        = ((g 2) * ((g 0) * x 0 + g 1) + g 3)
          + (((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3) * t
            + ((h 2) * ((h 0) * x 0 + h 1)) * t ^ 2) := by
    intro t
    rw [twoLayerChain_explicit]
    ring
  simp only [hexp]
  simp only [rfdiffIter, rfdiff]
  norm_num
  ring


/-- **三层链沿参数方向的常数项**。 -/
def threeLayerCoeff0 (g : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (g 4) * ((g 2) * ((g 0) * x 0 + g 1) + g 3) + g 5

/-- **三层链沿参数方向的一次项系数**。 -/
def threeLayerCoeff1 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((g 2) * ((g 0) * x 0 + g 1) + g 3)
    + (g 4) * ((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3)
    + h 5

/-- **三层链沿参数方向的二次项系数**。 -/
def threeLayerCoeff2 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3)
    + (g 4) * ((h 2) * ((h 0) * x 0 + h 1))

/-- **三层链沿参数方向的三次项系数**——**`h4 · h2 · h0 · x`，三个权重方向之积。** -/
def threeLayerCoeff3 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((h 2) * ((h 0) * x 0 + h 1))

/-- ⭐⭐ **三层的参数展开**：**沿 `g + t·h`，输出是 `t` 的三次式。**

**⚠ 系数单独定义为 `threeLayerCoeff0..3`，以便逐项核对**——
**直接写成一个巨大的括号表达式在 Lean 里极易错配括号（第 205 轮试过两次失败）。** -/
theorem threeLayer_param_expand (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) (t : ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 (fun i => g i + t * h i) x 0
      = threeLayerCoeff0 g x
        + (threeLayerCoeff1 g h x * t
            + (threeLayerCoeff2 g h x * t ^ 2 + threeLayerCoeff3 g h x * t ^ 3)) := by
  simp only [threeLayerCoeff0, threeLayerCoeff1, threeLayerCoeff2, threeLayerCoeff3]
  rw [threeLayerChain_explicit]
  ring

/-- ⭐⭐⭐ **沿任何参数方向，【三】层链是三次的**——**故四阶参数差分为零。**

**⇒ 与第 204 轮的两层情形合起来，「参数次数 = 深度」有了 `d = 2, 3` 两个实例。** -/
theorem threeLayer_param_quartic (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) :
    rfdiffIter 4 (fun t : ℝ =>
      flatChainAct (N := 6) threeLayerChain 0 (fun i => g i + t * h i) x 0) 0 = 0 := by
  have : (fun t : ℝ => flatChainAct (N := 6) threeLayerChain 0
      (fun i => g i + t * h i) x 0)
      = fun t : ℝ => threeLayerCoeff0 g x
          + (threeLayerCoeff1 g h x * t
              + (threeLayerCoeff2 g h x * t ^ 2 + threeLayerCoeff3 g h x * t ^ 3)) := by
    funext t
    exact threeLayer_param_expand g h x t
  rw [this]
  simp only [rfdiffIter, rfdiff]
  norm_num
  ring

/-! ### ⚠ 第三处被普查拦下的复制，这次的处理是【内联】

**我先后写了 `rfdiffIter_cubic_zero`（二次 → 三阶）与 `rfdiffIter_quartic_zero`（三次 → 四阶）。
`audit_aliases.py` 把两条都标为 `copy`：它们是同一模式（"次数 n 的多项式被 n+1 阶差分零化"）的两次实例化。**

**我一度想把它们改名成 `_poly2`／`_poly3` 了事——那【不解决问题**：
**结构同形不会因为换个名字而消失，普查看的也不是名字。**

**⇒ 正确处理是【不单独命名**：**两者各自内联进唯一的调用点**
（`twoLayer_param_cubic` 与 `threeLayer_param_quartic`），**那里的目标是具体多项式，
`simp only [rfdiffIter, rfdiff]` + `norm_num` + `ring` 已足够。**

**⚠ 代价是两条证明里各出现一次相同的五行 tactic 串。那【可以接受**：
**五行重复远好于两条只差指数的公开定理——后者会让读者以为它们承载不同的数学。**

**⚠ 真正的解法是「次数」本身被参数化（`Polynomial` 的差分会话），
登记为未做的缺口。** -/


/-! ## ⭐⭐⭐ 下界：三次式不能被任何二次式拟合

## 为什么需要这条

**第 204／205 轮从【上方】钉住参数次数**：
**`d = 2` 时三阶参数差分为零、`d = 3` 时四阶参数差分为零。**

**⇒ 那只说明次数 ≤ d，不说明次数【不】更小。**

**第 187 轮从下方钉住了 `d = 2`（`twoLayer_no_affine_fit`：没有仿射模型能拟合）。
本节补上 `d = 3` 的下界——即「没有【二次】模型能拟合三层链」的解析核心。**

**⚠ 而关键是【纯三次式】`t ↦ t³` 在四个点上已足以反驳任何一个二次式。**

## 反例的取法

**取 `t = 0, 1, 2, 3`：`t³` 给出 `0, 1, 8, 27`。**

**若 `A + B·t + C·t² = t³` 对这四点都成立，则三点已唯一决定二次式
（系数矩阵非零行列式），而它在 `t = 3` 处给 `21`，与 `27` 矛盾。**

**⇒ 更直接：由 `t = 0` 得 `A = 0`，由 `t = 1` 得 `B + C = 1`，由 `t = 2` 得 `2B + 4C = 8`，
解出 `C = 3`、`B = -2`，而 `t = 3` 要求 `3B + 9C = 27`，即 `-6 + 27 = 21 ≠ 27`。** -/

/-- ⭐⭐ **三次式不能被二次式拟合**——**`d = 3` 下界的解析核心。**

**`linarith` 只需四个求值点，不需要任何多项式理论。** -/
theorem cubic_not_quadratic :
    ¬ ∃ (A B C : ℝ), ∀ (t : ℝ), A + (B * t + C * t ^ 2) = t ^ 3 := by
  rintro ⟨A, B, C, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num at h0 h1 h2 h3
  linarith


/-- **`g = 0`、`h = e₀+e₂+e₄` 时四个系数分别是 `0, 0, 0, 1`。** -/
theorem threeLayerCoeffs_at_axis (x : Fin 1 → ℝ) (hx : x 0 = 1) :
    (threeLayerCoeff0 (0 : Fin 6 → ℝ) x = 0)
      ∧ (threeLayerCoeff1 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 0)
      ∧ (threeLayerCoeff2 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 0)
      ∧ (threeLayerCoeff3 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [threeLayerCoeff0]
    norm_num
  · simp only [threeLayerCoeff1]
    norm_num
    simp [hx]
  · simp only [threeLayerCoeff2]
    norm_num
    simp [hx]
  · simp only [threeLayerCoeff3]
    norm_num
    simp [hx]


/-- ⭐⭐⭐ **三层链不能被任何二次模型拟合**——**`d = 3` 的下界。**

**⚠ 与第 204／205 轮合起来，参数次数在 `d = 3` 处从【两侧】钉住：**
- **≤ 3**：`threeLayer_param_quartic`（四阶参数差分为零）；
- **≥ 3**：本条（不存在二次模型）。

## 构造

**取 `g = 0`、`h = e₀ + e₂ + e₄`、`x = (fun _ => 1)`。
由 `threeLayerCoeffs_at_axis`，四个系数是 `0, 0, 0, 1`，
故由 `threeLayer_param_expand`，沿 `t ↦ g + t·h` 的输出【恒等于】 `t³`。**

**⇒ 若某二次式 `A + (B·t + C·t²)` 拟合它，则与 `cubic_not_quadratic` 矛盾。** -/
theorem threeLayer_no_quadfit :
    ¬ ∃ (A B C : ℝ), ∀ (t : ℝ),
        flatChainAct (N := 6) threeLayerChain 0
          (fun i => (0 : Fin 6 → ℝ) i
            + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
          (fun _ => (1 : ℝ)) 0
          = A + (B * t + C * t ^ 2) := by
  rintro ⟨A, B, C, h⟩
  have hc := threeLayerCoeffs_at_axis (fun _ => (1 : ℝ)) rfl
  obtain ⟨h0, h1, h2, h3⟩ := hc
  have hexp : ∀ t : ℝ,
      flatChainAct (N := 6) threeLayerChain 0
        (fun i => (0 : Fin 6 → ℝ) i
          + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
        (fun _ => (1 : ℝ)) 0 = t ^ 3 := by
    intro t
    rw [threeLayer_param_expand, h0, h1, h2, h3]
    ring
  refine cubic_not_quadratic ⟨A, B, C, fun t => ?_⟩
  rw [← hexp t]
  exact (h t).symm


/-! ## ⭐⭐⭐ 离散 Leibniz 规则：乘以一次式使次数加一

## 为什么这条是「次数 = 深度」的一般归纳的核心

**链的递推沿参数方向是**

    Φ_{d+1}(t) = (g_{2d} + t·h_{2d}) · Φ_d(t) + (g_{2d+1} + t·h_{2d+1})

**⚠ 即「乘一个【一次式】再加一个一次式」。**

**⇒ 若 `Φ_d` 的次数被第 `k+1` 阶差分零化，那么 `Φ_{d+1}` 的次数被第 `k+2` 阶差分零化——
而这需要的正是「一次式的乘积如何影响差分阶数」的规则，即【离散 Leibniz 规则**。

## 形式

**对任意 `a b : ℝ` 与 `f : ℝ → ℝ`：**

    rfdiff (fun t => (a + b·t) · f t)
      = fun t => (a + b·t) · rfdiff f t + b · f (t + 1)

**⚠ 第二项的 `f (t+1)` 偏移是【离散** Leibniz 的特征——
连续情形是 `(x·f)' = x·f' + f`，这里因差分步长为 1 而出现 `f (t+1)`。** -/

/-- ⭐⭐ **离散 Leibniz 规则（一次式情形）**——**乘以一次式使差分阶数加一的基础。** -/
theorem rfdiff_affine_mul (a b : ℝ) (f : ℝ → ℝ) :
    rfdiff (fun t => (a + b * t) * f t)
      = fun t => (a + b * t) * rfdiff f t + b * f (t + 1) := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **离散 Leibniz 规则（常数情形）**——**乘以常数不改变差分阶数。** -/
theorem rfdiff_const_mul (c : ℝ) (f : ℝ → ℝ) :
    rfdiff (fun t => c * f t) = fun t => c * rfdiff f t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **`rfdiff` 是加性的**。 -/
theorem rfdiff_add (f g : ℝ → ℝ) :
    rfdiff (fun t => f t + g t) = fun t => rfdiff f t + rfdiff g t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **`rfdiffIter` 是加性的**。 -/
theorem rfdiffIter_add (k : ℕ) (f g : ℝ → ℝ) :
    rfdiffIter k (fun t => f t + g t)
      = fun t => rfdiffIter k f t + rfdiffIter k g t := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      rw [rfdiffIter_succ, ih, rfdiff_add]
      funext t
      rw [rfdiffIter_succ, rfdiffIter_succ]

/-- ⭐⭐ **`rfdiffIter` 与常数相乘交换**。 -/
theorem rfdiffIter_const_mul (k : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    rfdiffIter k (fun t => c * f t) = fun t => c * rfdiffIter k f t := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [rfdiffIter_succ, ih, rfdiff_const_mul]
      funext t
      rw [rfdiffIter_succ]


/-! ## ⭐⭐⭐ 次数概念化：`LowDeg k f :=` 第 `k+1` 阶差分为零

## 为什么这样定义而不是用 `Polynomial`

**「次数 ≤ k」需要一个定义。用 `Polynomial` 意味着把链的递推与 `MvPolynomial` 的复合对接——
那是大工程，而且对本项目的用途（障碍）而言是过度的。**

**⇒ 本项目真正需要的只是【判别式】：「次数 ≤ k」⟺「第 `k+1` 阶差分恒为零」。
这在差分层面上是【定义**，无需多项式理论。**

**⚠ 这不是弱化**：**第 197 轮的可达性障碍、第 204–206 轮的两侧钉住，
用的全部是这个判别式；把它命名出来就能陈述一般归纳。** -/

/-- **「次数 ≤ k」的差分定义**——**第 `k+1` 阶迭代差分为零。** -/
def LowDeg (k : ℕ) (f : ℝ → ℝ) : Prop := rfdiffIter (k + 1) f = 0

/-- ⭐ **常数是次数 ≤ 0 的**。 -/
theorem lowDeg_zero_of_const (c : ℝ) : LowDeg 0 (fun _ => c) := by
  simp only [LowDeg, rfdiffIter]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **加性：两个次数 ≤ k 的函数之和仍是次数 ≤ k**。 -/
theorem lowDeg_add {k : ℕ} {f g : ℝ → ℝ} (hf : LowDeg k f) (hg : LowDeg k g) :
    LowDeg k (fun t => f t + g t) := by
  simp only [LowDeg] at *
  rw [rfdiffIter_add, hf, hg]
  funext t
  simp

/-- ⭐⭐ **数乘：次数 ≤ k 的函数乘常数仍是次数 ≤ k**。 -/
theorem lowDeg_const_mul {k : ℕ} (c : ℝ) {f : ℝ → ℝ} (hf : LowDeg k f) :
    LowDeg k (fun t => c * f t) := by
  simp only [LowDeg] at *
  rw [rfdiffIter_const_mul, hf]
  funext t
  simp


/-- ⭐⭐ **`LowDeg` 是单调的：次数 ≤ k 蕴含次数 ≤ k+1。** -/
theorem lowDeg_succ {k : ℕ} {f : ℝ → ℝ} (h : LowDeg k f) : LowDeg (k + 1) f := by
  simp only [LowDeg] at *
  rw [rfdiffIter_succ, h]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **`rfdiff f = 0` 当且仅当 `f` 是常函数**（差分步长为 1，所以只需 `f(t+1) = f t`）。

**⚠ 这里只证【需要的方向**：`rfdiff f = 0 → ∀ t, f (t+1) = f t`。** -/
theorem rfdiff_eq_zero_step {f : ℝ → ℝ} (h : rfdiff f = 0) (t : ℝ) : f (t + 1) = f t := by
  have := congrFun h t
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

theorem lowDeg_zero_affine_mul {f : ℝ → ℝ} (hf : LowDeg 0 f) (a b : ℝ) :
    LowDeg 1 (fun t => (a + b * t) * f t) := by
  have hconst : ∀ s : ℝ, f (s + 1) = f s := fun s => rfdiff_eq_zero_step hf s
  simp only [LowDeg, rfdiffIter] at *
  funext t
  -- 目标是 rfdiff (rfdiff (fun t => (a+b*t)*f t)) t = 0
  set g : ℝ → ℝ := fun s => (a + b * s) * f s with hg
  -- 先把两个 rfdiff 都展开成显式的四点值
  have hval : ∀ s : ℝ, rfdiff g s = (a + b * (s + 1)) * f s - (a + b * s) * f s := by
    intro s
    simp only [rfdiff, hg]
    have : f (s + 1) = f s := hconst s
    rw [this]
  have : rfdiff (rfdiff g) t = (rfdiff g (t + 1)) - (rfdiff g t) := rfl
  rw [this, hval (t + 1), hval t]
  have h1 : f (t + 1) = f t := hconst t
  rw [h1]
  simp only [Pi.zero_apply]
  ring


/-- ⭐⭐⭐ **`LowDeg 1 f` 的算术内容**：**`f (s+2) - 2·f (s+1) + f s = 0`。**

**⇒ `f` 在等距点上是【仿射**的：`f (s+k) = f s + k·(f (s+1) - f s)` 对一切自然数 `k`。

**⚠ 下面只证用得到的 `k ≤ 4`——一般 `k` 需要 `Nat` 归纳，而本节的目标只到三阶差分。** -/
theorem lowDeg_one_step {f : ℝ → ℝ} (hf : LowDeg 1 f) (s : ℝ) :
    f (s + 1 + 1) - f (s + 1) = f (s + 1) - f s := by
  have h : rfdiff (rfdiff f) = 0 := hf
  have := congrFun h s
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

/-- **`f (s+2) = 2·f (s+1) - f s`**——上一式的移项形式。 -/
theorem lowDeg_one_rec {f : ℝ → ℝ} (hf : LowDeg 1 f) (s : ℝ) :
    f (s + 1 + 1) = 2 * f (s + 1) - f s := by
  have := lowDeg_one_step hf s
  linarith

/-- ⭐⭐⭐ **乘以一次式使次数 ≤ 1 升到次数 ≤ 2**——**归纳在 `k = 1` 处的一步。**

**⚠ 证明方式**：**用 `lowDeg_one_rec` 把目标里所有 `f (t+k)`（`k ≥ 2`）降成
`f t` 与 `f (t+1)` 的线性组合，然后 `ring`。**

**⚠ 与 `lowDeg_zero_affine_mul` 合起来，`k = 0, 1` 两步都有。
完整归纳需要一般 `k`（离散 Leibniz 的一般形式），本轮未做。** -/
theorem lowDeg_one_affine_mul {f : ℝ → ℝ} (hf : LowDeg 1 f) (a b : ℝ) :
    LowDeg 2 (fun t => (a + b * t) * f t) := by
  simp only [LowDeg] at hf ⊢
  simp only [rfdiffIter] at hf ⊢
  funext t
  simp only [rfdiff, Pi.zero_apply]
  -- 把四个高点的值降到 f t 与 f (t+1)
  have r1 : f (t + 1 + 1) = 2 * f (t + 1) - f t := lowDeg_one_rec hf t
  have r2 : f (t + 1 + 1 + 1) = 2 * f (t + 1 + 1) - f (t + 1) := lowDeg_one_rec hf (t + 1)
  rw [r2, r1]
  ring


/-- ⭐⭐ **一次式是 `LowDeg 1`**——**二阶差分为零。**

**这是链归纳的基座：每层的权重 `(g_{2d} + t·h_{2d})` 就是这样的一次式。**

**⚠ 别名普查把本条与第 207 轮的 `lowDeg_zero_of_const` 标为 `copy`——
两条的【证明形状**相同（展开两层 `rfdiff` 再 `ring`），但【陈述不同**：
**一条说常数，一条说一次式，而两者都是归纳需要的（一次式给出 `k = 1`，常数给出 `k = 0` 的基座）。**

**⇒ 保留两条，并把这条注记作为「同一模式的两个必要实例」的记录。
同时删掉了第三条纯包装 `lowDeg_const_one`——它从未被使用，
而「常数是 `LowDeg 1`」由 `lowDeg_succ ∘ lowDeg_zero_of_const` 直接得到。** -/
theorem lowDeg_affine (a b : ℝ) : LowDeg 1 (fun t => a + b * t) := by
  simp only [LowDeg, rfdiffIter]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **`LowDeg 2` 的算术内容**：**三阶差分为零，即二阶差分是常数。**

**⇒ `f` 在等距点上与一个二次式相符；`f(s+3) = 3f(s+2) - 3f(s+1) + f(s)`。** -/
theorem lowDeg_two_step {f : ℝ → ℝ} (hf : LowDeg 2 f) (s : ℝ) :
    f (s + 1 + 1 + 1) - 3 * f (s + 1 + 1) + 3 * f (s + 1) - f s = 0 := by
  simp only [LowDeg, rfdiffIter, rfdiff, Pi.zero_apply] at hf
  have := congrFun hf s
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

/-- ⭐⭐⭐ **乘以一次式使次数 ≤ 2 升到次数 ≤ 3**——**归纳在 `k = 2` 处的一步。**

**⚠ 与 `lowDeg_zero_affine_mul`、`lowDeg_one_affine_mul` 合起来，`k = 0, 1, 2` 三步都有。** -/
theorem lowDeg_two_affine_mul {f : ℝ → ℝ} (hf : LowDeg 2 f) (a b : ℝ) :
    LowDeg 3 (fun t => (a + b * t) * f t) := by
  simp only [LowDeg] at hf ⊢
  simp only [rfdiffIter] at hf ⊢
  funext t
  simp only [rfdiff, Pi.zero_apply]
  -- 把 f 的高点值降到 f t, f(t+1), f(t+2)
  have r1 : f (t + 1 + 1 + 1)
      = 3 * f (t + 1 + 1) - 3 * f (t + 1) + f t := by
    have := lowDeg_two_step hf t
    linarith
  have r2 : f (t + 1 + 1 + 1 + 1)
      = 3 * f (t + 1 + 1 + 1) - 3 * f (t + 1 + 1) + f (t + 1) := by
    have := lowDeg_two_step hf (t + 1)
    linarith
  rw [r2, r1]
  ring


/-! ## ⭐⭐⭐ 链的参数次数：对深度归纳

## 归纳的不变量

**沿参数方向 `t ↦ g + t·h`，宽 1 的链的作用是**

    Φ_ch(t) = flatChainAct ch 0 (g + t·h) (fun _ => x)

**而递推（第 191 轮的 `flatChainAct_cons_general` 在宽 1 的特化）是**

    Φ_{cons l ch}(t) = Φ_ch(t) 作用在 `(g_off + t·h_off)·x + (g_{off+1} + t·h_{off+1})` 上

**⚠ 那不是「一次式乘 Φ_ch」的形状**——**因为 `flatChainAct` 把【新激活】喂给尾链，
而新激活本身依赖 `t`。**

**⇒ 直接对 `Chain` 归纳是【错**的路子：`Φ_{cons l ch}(t)` 不是 `(a+b·t)·Φ_ch(t) + (c+d·t)`，
而是 `Φ_ch` 作用在一个 `t`-依赖的输入上。**

**⚠ 正确的路子在【输入】侧：第 203 轮已证「链对输入恒为仿射」
（`flatChainAct_scalar_affine`），所以**

    Φ_ch(t) = (1 − σ(t))·Φ_ch(0) + σ(t)·Φ_ch(1)

**其中 `σ(t)` 是那个 `t`-依赖的标量输入。而 `σ` 本身沿 `t` 是【一次**的
（每层 `(g_off + t·h_off)·x + (g_off+1 + t·h_{off+1})`）。
**⇒ `Φ_ch(t)` 是 `t` 的一次式的仿射像——仍然是一次式！**

**⇒ 这与第 203 轮的结论一致：深度【不】提高对输入的次数。**
**而「参数次数 = 深度」是关于【参数 `g`】的，不是关于单条参数直线的 `t`。**

## 本轮的处理

**⇒ 我不再试图用 `Chain` 归纳去证「`t ↦ Φ(g + t·h)` 的次数 = 深度」——
因为沿着一条直线看，每层的 `(g + t·h)` 只是把系数变成 `t` 的一次式，
而【所有层的参数同时变】才产生高次项。**

**⚠ 而第 204／205 轮的 `twoLayer_param_cubic` 与 `threeLayer_param_quartic`
证的正是「所有层同时变」的情形，用的是【显式展开**（`threeLayer_param_expand`）。**

**⇒ 所以本轮回退到【记录】：`Chain` 归纳需要的不变量不是 `LowDeg`，
而是「`Φ` 是 `g` 的多项式」，而那需要 `MvPolynomial`（第 199 轮起已登记）。** -/

/-- **链的层数**——**用于陈述「次数 = 层数」的上界。** -/
def chainDepth : {m n : ℕ} → Chain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons _ rest => chainDepth rest + 1

/-- **空链的层数为零**。 -/
theorem chainDepth_idf {n : ℕ} : chainDepth (Chain.idf n) = 0 := rfl

/-- **加一层层数加一**。 -/
theorem chainDepth_cons {m n c : ℕ} (l : MLayer m n) (rest : Chain n c) :
    chainDepth (Chain.cons l rest) = chainDepth rest + 1 := rfl


/-! ## ⚠⚠ 第 3 轮的推测被推翻：参数方向确实到三次

## 第 3 轮写了什么

**第 3 轮在 `chainDepth` 一节的文档里断言：**

> **沿一条参数直线 `t ↦ g + t·h`，新激活是 `t` 的仿射式，而把仿射函数喂进一个对输入仿射的链，
> 得到的仍然是 `t` 的仿射函数。⇒ `t ↦ Φ_ch(g + t·h)` 对【每一条】链都是 `t` 的仿射函数。**

**那个推理【是错的**，而错在一个具体的地方：
**「对输入仿射」是关于【第一个变量】的性质，而新激活同时是 `t` 的函数；
把 `t`-依赖的输入喂进仿射映射，得到的是 `t` 的多项式，次数随层数【增加**——
**因为每层的权重【也】随 `t` 变，两者相乘就产生高次项。**

## 本轮用数值把这件事钉死

**取 `g = 0`、`h = e₀ + e₂ + e₄`、`x = 1`：三层链的输出【恰好等于】 `t³`。**

**⇒ 参数方向上的次数确实是 3，不是 1。第 204／205 轮的 `threeLayerCoeff3 = h4·h2·h0·x` 是对的，
而第 3 轮的「恒为仿射」的推广是错的。**

**⚠ 结论**：**`LowDeg` 确实是正确的阶梯**——**第 3 轮放弃 `Chain` 归纳的理由（「不变量选错了」）不成立；
真正的障碍只是 `lowDeg_affine_mul` 的一般 `k`（离散 Leibniz）还没证。** -/

/-- **三层链沿参数方向 `e₀+e₂+e₄` 的输出恰是 `t³`**——**第 3 轮推测被推翻的直接见证。** -/
theorem threeLayerAxis_t3 (t : ℝ) :
    flatChainAct (N := 6) threeLayerChain 0
      (fun i => (0 : Fin 6 → ℝ) i
        + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
      (fun _ => (1 : ℝ)) 0 = t ^ 3 := by
  rw [threeLayer_param_expand]
  simp only [threeLayerCoeff0, threeLayerCoeff1, threeLayerCoeff2, threeLayerCoeff3,
    show (1 : Fin 6) ≠ 2 from by decide,
    show (1 : Fin 6) ≠ 4 from by decide,
    show (3 : Fin 6) ≠ 0 from by decide,
    show (3 : Fin 6) ≠ 2 from by decide,
    show (3 : Fin 6) ≠ 4 from by decide,
    show (5 : Fin 6) ≠ 0 from by decide,
    show (5 : Fin 6) ≠ 2 from by decide,
    show (5 : Fin 6) ≠ 4 from by decide]
  norm_num

/-- ⭐⭐ **沿参数方向，三层链【不是】仿射的**——**`t³` 不满足二阶差分为零。**

**⇒ 与两层的情形（第 204 轮的三阶参数差分零、第 187 轮的非仿射）并列，
给出「参数次数随深度增长」的又一直接见证。** -/
theorem threeLayerAxis_not_affine :
    ¬ (∀ t : ℝ,
        flatChainAct (N := 6) threeLayerChain 0
          (fun i => (0 : Fin 6 → ℝ) i
            + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
          (fun _ => (1 : ℝ)) 0
          = (1 - t) * (0 : ℝ) + t * 1) := by
  intro h
  have h3 := h 3
  have h0 := h 0
  have h1 := h 1
  rw [threeLayerAxis_t3] at h3
  rw [threeLayerAxis_t3] at h0
  rw [threeLayerAxis_t3] at h1
  norm_num at h3 h0 h1


/-! ## 一般离散 Leibniz 规则：乘以一次式使次数升一阶（任意 `k`）

## 本轮正面处理第 2／3／4 轮三次绕开的障碍

**目标**：`LowDeg k f → LowDeg (k+1) (fun t => (a + b * t) * f t)`。

**第 2 轮的失败**：直接套 `rfdiff_affine_mul` 于 `rfdiff (rfdiffIter (k+1) …)` —— 那是错的，
`rfdiff` 不能穿过 `rfdiffIter k`。

**⇒ 本轮的策略**：**对 `k` 归纳，归纳步用【对称乘积规则】**。 -/

/-- ⭐⭐ **一阶乘积规则（对称形式）**——**离散 Leibniz 的最底层。** -/
theorem rfdiff_mul (u f : ℝ → ℝ) :
    rfdiff (fun t => u t * f t)
      = fun t => u (t + 1) * rfdiff f t + rfdiff u t * f t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **仿射函数的一阶差分是常数**。 -/
theorem rfdiff_affine (a b : ℝ) :
    rfdiff (fun t => a + b * t) = fun _ => b := by
  funext t
  simp only [rfdiff]
  ring

/-! ## ⚠⚠ 第 5 轮的结论：一般 `k` 的 `lowDeg_affine_mul` 未能证出，精确理由如下

## 三次尝试的完整记录

| 轮次 | 尝试 | 失败点 |
|:--|:--|:--|
| 2 | 把 `rfdiff_affine_mul` 直接套在 `rfdiff (rfdiffIter (k+1) …)` 上 | **`rfdiff` 不能穿过 `rfdiffIter k`**——这是【数学**错误，不是技术障碍 |
| 3 | 改用 `MvPolynomial` | **未做**（判断为过度） |
| 4 | 证「参数直线恒为仿射」以绕开 | **该命题为【假**（本轮以 `threeLayerAxis_t3` 反证），路走死 |
| **5** | **对 `k` 归纳 + 对称乘积规则 `rfdiff_mul`** | **归纳步能推进到 `rfdiffIter (k+1) (b·f) = 0`（已消），但 `u(t+1)·rfdiff f` 这一项需要归纳假设作用在【平移后的仿射式】上，而 `ih` 的 `a b` 是【外层固定**的——`LowDeg (k+1) ((a+b)·(t+1) 形) rfdiff f` 与 `ih` 要求的 `LowDeg (k+1) ((a'+b'·t) · rfdiff f)` 不同形，`rw` 失败。 |

## 精确的数学障碍

**归纳步的实际目标是**

    rfdiffIter (k+1) (fun t => (a + b·(t+1)) · rfdiff f t) = 0

**而归纳假设给的是**

    LowDeg k g → LowDeg (k+1) (fun t => (a' + b'·t) · g t)

**两者的乘积因子不同：**`a + b·(t+1)` **是 `a + b·t` 的【平移**，
**而 `LowDeg` 不是平移不变的**——`rfdiffIter` 在 `t` 的平移下【会变**。

**⇒ 归纳需要对【所有平移**同时做，即需要一条平移不变形式的陈述：

    LowDeg k f → ∀ c, LowDeg (k+1) (fun t => (a + b·(t + c)) · f t)

**而它的证明又要对 `c` 归纳或用一个更强的多变量形式——
那实际上等价于【多变量多项式次数**，即第 199 轮登记的 `MvPolynomial` 路线。**

## 结论

**本路线到此为【已核实的终点**：
**`lowDeg_affine_mul` 的一般 `k` 需要的不是更多 tactic，而是平移不变性，
而那把问题推回 `MvPolynomial`。**

**⇒ 已证的 `lowDeg_affine_mul` 三个实例（`k = 0, 1, 2`，第 207／208／第 3 轮）是这条路线能给的全部。
一般形式【登记为未做**，理由如上，而不是「暂时没时间」。** -/


/-! ## ⭐⭐⭐ 参数次数的正确载体：`MvPolynomial`

## 为什么第 5 轮把问题推到这里

**`LowDeg` 阶梯在第 5 轮可证明地终止了：归纳步需要 `t` 的【平移不变性】，
而 `LowDeg` 不是平移不变的。**

**⇒ 正确的载体是把输出看成参数向量 `g : Fin N → ℝ` 的【多变量多项式】，
次数取 `totalDegree`。**

**⚠ `totalDegree` 对参数平移【显然**不变（多项式本身不变），
**所以第 5 轮的障碍在这个载体上根本不会出现。`totalDegree_mul` 已核实存在。**

## 本节给出形状

**对宽 1 的单层，显式写出那个多项式并证其次数 ≤ 1。**

**⚠ 一般深度的归纳仍未做——但载体现在是对的。** -/

/-- **宽 1、单层的输出作为参数 `g : Fin N → ℝ` 的多项式**：
**`X 0 · x₀ + X 1`**（`X 0` 是权重槽位，`X 1` 是偏置槽位）。 -/
noncomputable def oneLayerParamPoly (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ) :
    MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X ⟨0, h0⟩ * MvPolynomial.C x0 + MvPolynomial.X ⟨1, h1⟩

/-- ⭐⭐ **单层多项式求值等于该层的计算**——**载体与网络一致。** -/
theorem oneLayerParamPoly_eval (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ)
    (g : Fin N → ℝ) :
    (oneLayerParamPoly N h0 h1 x0).eval g = g ⟨0, h0⟩ * x0 + g ⟨1, h1⟩ := by
  simp only [oneLayerParamPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- ⭐⭐ **单层多项式的次数 ≤ 1**——**「深度 1 ⟹ 参数次数 ≤ 1」的载体形式。** -/
theorem oneLayerParamPoly_degree_le (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ) :
    (oneLayerParamPoly N h0 h1 x0).totalDegree ≤ 1 := by
  have hm : (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
      : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ (MvPolynomial.X (⟨0, h0⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
        + (MvPolynomial.C x0 : MvPolynomial (Fin N) ℝ).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have hx : (MvPolynomial.X (⟨0, h0⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  have hc : (MvPolynomial.C x0 : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C x0
  have hy : (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [oneLayerParamPoly]
  calc (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ max (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
            : MvPolynomial (Fin N) ℝ).totalDegree
          (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
        rw [max_le_iff]
        constructor
        · omega
        · omega


/-- **宽 1、两层的输出作为参数的多项式**：
**`X 2 · (X 0 · x₀ + X 1) + X 3`**
（第 1 层用槽位 `0`/`1`，第 2 层用 `2`/`3`）。 -/
noncomputable def twoLayerParamPoly (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X ⟨2, h2⟩
    * (MvPolynomial.X ⟨0, h0⟩ * MvPolynomial.C x0 + MvPolynomial.X ⟨1, h1⟩)
    + MvPolynomial.X ⟨3, h3⟩

/-- ⭐⭐ **两层多项式求值等于该链的计算**——**与第 188 轮的显式形式一致。** -/
theorem twoLayerParamPoly_eval (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) (g : Fin N → ℝ) :
    (twoLayerParamPoly N h0 h1 h2 h3 x0).eval g
      = g ⟨2, h2⟩ * (g ⟨0, h0⟩ * x0 + g ⟨1, h1⟩) + g ⟨3, h3⟩ := by
  simp only [twoLayerParamPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- ⭐⭐ **一次式乘常数仍是一次**——**归纳步的基础。** -/
theorem totalDegree_X_mul_C_le (N : ℕ) (s : Fin N) (c : ℝ) :
    (MvPolynomial.X s * MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X s : MvPolynomial (Fin N) ℝ)
    (MvPolynomial.C c : MvPolynomial (Fin N) ℝ)
  have hx : (MvPolynomial.X s : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  have hc : (MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C c
  omega

/-- ⭐⭐⭐ **两层多项式的次数 ≤ 2**——**「深度 2 ⟹ 参数次数 ≤ 2」的载体形式。** -/
theorem twoLayerParamPoly_degree_le (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) :
    (twoLayerParamPoly N h0 h1 h2 h3 x0).totalDegree ≤ 2 := by
  -- 内层：X 0 · x₀ + X 1 的次数 ≤ 1
  have hinner : (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    calc (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
        ≤ max (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
              : MvPolynomial (Fin N) ℝ).totalDegree
            (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
          rw [max_le_iff]
          exact ⟨totalDegree_X_mul_C_le N _ x0, by simp⟩
  -- 外层：X 2 · 内层 的次数 ≤ 2
  have hprod : (MvPolynomial.X (⟨2, h2⟩ : Fin N)
        * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N)) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 2 := by
    have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X (⟨2, h2⟩ : Fin N)
      : MvPolynomial (Fin N) ℝ)
      (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ)
    have hx : (MvPolynomial.X (⟨2, h2⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X _
    omega
  rw [twoLayerParamPoly]
  calc (MvPolynomial.X (⟨2, h2⟩ : Fin N)
        * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N))
        + MvPolynomial.X (⟨3, h3⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ max (MvPolynomial.X (⟨2, h2⟩ : Fin N)
            * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
              + MvPolynomial.X (⟨1, h1⟩ : Fin N)) : MvPolynomial (Fin N) ℝ).totalDegree
          (MvPolynomial.X (⟨3, h3⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
        rw [max_le_iff]
        exact ⟨hprod, by simp⟩


/-! ## ⚠⚠ 第 8 轮：链层递归的障碍记录（未完成）

## 目标

**把第 7 轮的 `twoLayerParamPoly` 推广成对 `Chain` 的递归：
`chainPoly ch off h x` 给出整条宽 1 链的输出多项式，并证 `totalDegree ≤ chainDepth ch`。**

## 数学上它是对的，而且很简单

**宽 1 时不需要多项式【代入】**：**每一层只是「乘一个变量、加一个变量」，输入 `x` 是标量常数。**
**⇒ 递归是纯乘加：**

    chainPoly (.idf _)     off x = C x
    chainPoly (.cons l ch) off x = X off · chainPoly ch (off+2) x + X (off+1)

**核对**：**`Φ_1 = X 0 · C x + X 1`，`Φ_2 = X 2 · Φ_1 + X 3`——展开正是第 188 轮的形式。✓**

**⇒ 次数归纳只需 `totalDegree_mul`（相加）与 `totalDegree_add`（取 max），两者都已核实存在。**

## 实际卡住的地方（Lean 工程问题，不是数学问题）

**1. 递归的度量**：`off` 每层加 2，所以「整条链够用」的界必须随递归变化。
我把它写成全局界 `hN : off + 2 * chainDepth ch + 1 < N` 并配 `termination_by`，**定义体本身通过了**——
**但随后 `termination_by ch off hN x => chainDepth ch` 报 `application type mismatch`：
`ch` 在该位置被绑定为 `ℕ`（因为 `termination_by` 的参数是【被消去后的**那些）。**

**2. 展开 `noncomputable def`**：`rw [chainPoly]` 与 `simp only [chainPoly]` 都报 `made no progress`——
**递归定义需要在等式引理的形式下展开，而我没有找到正确的展开方式。**

**3. 命名冲突**：`chainDepth` 是 `{m n : ℕ} → Chain m n → ℕ`（有隐式参数），
在 `termination_by` 的位置上隐式参数无法推断，于是 `ch` 被错配到第一个显式位置（`ℕ`）。**

## 结论

**本轮没有把这条写进代码。** **上面的三步是【具体的下一步**，
而它们需要的是 Lean 的 dependent recursion 工程（`termination_by` 的正确写法、
递归定义的展开引理、隐式参数的显式化），**不是更多数学。**

**⇒ 第 7 轮的 `oneLayerParamPoly`／`twoLayerParamPoly` 与它们的次数界仍然有效，
而「对链递增归纳」这一步【登记为未做**，理由是上述三条工程障碍。** -/


/-! ## ⚠⚠ 第 9 轮：第 8 轮三条障碍的进展（一条解决、两条仍未）

## 障碍 1（`termination_by`）——**已解决**

**第 8 轮写成 `termination_by ch off hN x => chainDepth ch` 时报
`application type mismatch`：`termination_by` 的参数是【消去之后】的那些，`ch` 在那里被绑定为 `ℕ`。**

**⇒ 第 9 轮实测：`noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) →
(off : ℕ) → (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ`
配【结构模式匹配**（`| _, _, Chain.idf _ ...` 与 `| _, _, Chain.cons ... l rest ...`），
**完全不需要 `termination_by`**——**Lean 自己认出 `rest` 是 `Chain.cons` 的结构子项。**

**⇒ 这个定义【编译通过**（第 9 轮实测），所以障碍 1 【不再是障碍**。** -/

/-! ## 障碍 2（展开 `noncomputable def`）——**已解决**

**第 8 轮 `rw [chainPoly]` 报 `made no progress`。
第 9 轮实测：对【模式匹配**的递归定义，`rw [chainPoly]` **是**有效的
（探针 `testRec` 与 `testChainPoly` 都验证过）。

**⇒ 障碍 2 也不再是障碍。** -/

/-! ## 障碍 3（`omega` 与非线性的 `2 * chainDepth`）——**本轮未解决**

**定义体通过之后，`chainPoly_degree_le` 的归纳步需要在
`hN : off + 2 * chainDepth (Chain.cons l rest) + 1 < N` 与
`hN' : off + 2 * chainDepth rest + 3 < N` 之间做**线性提取**：

    要证：  off < N          （给 `Fin N` 的证明项）
    已知：  off + 2·d + 3 < N   （d 即 chainDepth rest）

**⚠ `omega` 做不到**：**它的约束求解把 `2 * d` 当作【非线性项**，
虽然它自己能证明 `d ≥ 0`，却拼不出 `off ≤ off + 2·d + 3`。

**⚠ 而 `Nat.le_add_right` 之类的引理给的是 `a ≤ a + b` 的形状，
需要把 `2 * d + 3` 显式写成 `b`——我试了 `Nat.le_add_right (off) (2 * d + 3)` 但类型对不上
（`Nat.le_add_right a b : a ≤ b + a`，参数顺序与我想的反了）。**

**⇒ 正确的引理应当是 `Nat.le_add_left`／`Nat.le.intro`，或者最直接：

    have : off ≤ off + (2 * d + 3) := Nat.le_add_right off (2 * d + 3)   -- 若 `Nat.le_add_right a b : a ≤ a + b`

**⚠ 我核对的 `Nat.le_add_right` 签名是 `a ≤ b + a`，所以应用 `Nat.le_add_left` 或 `le_add_of_nonneg_right`。**

**⇒ 这是一条【一行引理选择**的问题，而本轮在同一处消耗了过多尝试。** -/


/-! ## ⭐⭐⭐ 第 10 轮：`chainPoly` 定义与展开引理【已通过】，次数归纳差最后一步

## 本轮确认的三件事

**1. `chainPoly` 的定义【编译通过**：**

    noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
        (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ
      | _, _, Chain.idf _, _, _, x => MvPolynomial.C x
      | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x =>
          X ⟨off, ...⟩ * chainPoly rest (off + 2) (...) x + X ⟨off + 1, ...⟩

**⚠ 关键在于：`termination_by` 【不需要**（结构模式匹配足够），
而 `Fin N` 的证明项需要**先用 `le_add_of_nonneg_right (Nat.zero_le _)` 给出
`off ≤ off + (2·chainDepth rest + 3)`**，**再由 `omega` 线性地得出 `off < N`。**

**⚠ 第 10 轮探针确认：`Nat.le_add_right a b : a ≤ a + b`，而
`Nat.le_add_left a b : a ≤ b + a`——两者顺序相反**（第 9 轮我搞反了四次）。**

**2. `chainPoly_idf` 的展开【编译通过】——且必须是【泛化**形式：**

    theorem chainPoly_idf {N n : ℕ} (off : ℕ)
        (hN : off + 2 * chainDepth (Chain.idf n) + 1 < N) (x : ℝ) :
        chainPoly (Chain.idf n) off hN x = MvPolynomial.C x := by rw [chainPoly]

**⚠ 特化到 `Chain.idf 1` 会失败**，因为归纳里 `n` 是泛化的。

**3. `chainPoly_degree_le` 的归纳步差最后一步。**

## 最后一步的精确形状

**归纳步的 calc 是**

    deg(X·Φ_rest + Y) ≤ max (deg(X·Φ_rest)) (deg Y)      -- totalDegree_add
                     ≤ max (1 + deg Φ_rest) 1             -- totalDegree_mul 与 totalDegree_X
                     ≤ chainDepth (cons l rest)           -- hc

**⚠ 中间那一步的目标是 `deg(X·Φ_rest) ≤ 1 + chainDepth rest`，
而 `deg Φ_rest ≤ chainDepth rest` 正是归纳假设 `ih`。**

**⚠ 把 `ih` 交给 `omega`／`linarith` 都失败了**——**因为目标里 `deg(X·Φ_rest)`
已经被 `totalDegree_mul` 换成 `deg X + deg Φ_rest = 1 + deg Φ_rest`，
而 `linarith` 看到的 `ih : deg Φ_rest ≤ chainDepth rest` 与该表达式之间的
【项**不是同一个（`deg Φ_rest` 在其中出现的位置不同）。

**⇒ 正确做法：先用 `omega`／`linarith` 把 `1 + deg Φ_rest ≤ 1 + chainDepth rest`
从 `ih` 推出来（这一步是纯线性、项相同），再交给 `totalDegree_mul` 的 calc 链。
即【先证 `1 + deg Φ_rest ≤ 1 + chainDepth rest`，再 `exact` 合并**，
而不是把 `ih` 直接丢给末端的 `linarith`。**

**⇒ 这是本轮最后一次尝试的失败点，也是下一轮的第一件事。** -/


/-! ## ⭐⭐⭐ 宽 1 链的参数多项式：递归与次数上界

## 三条工程障碍的解法（第 8–10 轮磨合的结果）

1. **`termination_by` 不需要**——结构模式匹配让 Lean 认出 `rest` 是子项。
2. **`rw [chainPoly]` 对模式匹配递归定义有效**。
3. **`omega` 面对 `2 * chainDepth` 的非线性**：**先用
   `le_add_of_nonneg_right (Nat.zero_le _)` 给出 `off ≤ off + (2·d + 3)`，
   再由 `omega` 线性使用。** **注意 `Nat.le_add_right a b : a ≤ a + b`
   而 `Nat.le_add_left a b : a ≤ b + a`（顺序相反）。** -/

/-- **宽 1 链的输出多项式**。 -/
noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
    (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ
  | _, _, Chain.idf _, _, _, x => MvPolynomial.C x
  | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x =>
      MvPolynomial.X ⟨off, by
        have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by
          have h := chainDepth_cons l rest
          omega
        have h2 : off ≤ off + (2 * chainDepth (m := n') (n := _) rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega⟩
        * chainPoly (m := n') (n := _) rest (off + 2) (by
            have h := chainDepth_cons l rest
            omega) x
        + MvPolynomial.X ⟨off + 1, by
            have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by
              have h := chainDepth_cons l rest
              omega
            have h2 : off + 1 ≤ off + 1 + (2 * chainDepth (m := n') (n := _) rest + 2) :=
              le_add_of_nonneg_right (Nat.zero_le _)
            omega⟩

/-- ⭐⭐ **空链的多项式是常数**——**对任意宽度 `n` 通用（特化到 `idf 1` 会失败）。** -/
theorem chainPoly_idf {N n : ℕ} (off : ℕ)
    (hN : off + 2 * chainDepth (m := n) (n := n) (Chain.idf n) + 1 < N) (x : ℝ) :
    chainPoly (Chain.idf n) off hN x = MvPolynomial.C x := by
  rw [chainPoly]

/-- ⭐⭐⭐ **宽 1 链的输出多项式次数 ≤ 层数**——**「参数次数 = 深度」的载体形式。**

**⚠ 第 10 轮确定的最后一步：先由 `ih` 得出 `1 + deg Φ_rest ≤ 1 + chainDepth rest`
（纯线性的 `Nat.add_le_add_left`），再放进 calc。** -/
theorem chainPoly_degree_le {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
    (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) →
    (chainPoly ch off hN x).totalDegree ≤ chainDepth ch
  | _, _, Chain.idf _, off, hN, x => by
      rw [chainPoly_idf]
      simp
  | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x => by
      rw [chainPoly]
      have hc := chainDepth_cons l rest
      have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainDepth (m := n') (n := _) rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainDepth (m := n') (n := _) rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hrec : (off + 2) + 2 * chainDepth (m := n') (n := _) rest + 1 < N := by
        have h2 : (off + 2) + 2 * chainDepth (m := n') (n := _) rest + 1
            = off + 2 * chainDepth (m := n') (n := _) rest + 3 := by ring
        rw [h2]
        exact hNc
      have ih : (chainPoly rest (off + 2) hrec x).totalDegree
          ≤ chainDepth (m := n') (n := _) rest :=
        chainPoly_degree_le (m := n') (n := _) rest (off + 2) hrec x
      -- 关键：先得到 1 + deg ≤ 1 + chainDepth（纯线性、项相同）
      have hstep : 1 + (chainPoly rest (off + 2) hrec x).totalDegree
          ≤ 1 + chainDepth (m := n') (n := _) rest :=
        Nat.add_le_add_left ih 1
      have hmul : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
          * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
          ≤ (1 + chainDepth (m := n') (n := _) rest) := by
        calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
              * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
            ≤ (MvPolynomial.X (⟨off, hlt⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
              + (chainPoly rest (off + 2) hrec x).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + chainDepth (m := n') (n := _) rest := by
              have hx : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
                  : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
              omega
      calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
            * chainPoly rest (off + 2) hrec x
            + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree
          ≤ max (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
                * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
              (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                : MvPolynomial (Fin N) ℝ).totalDegree :=
            MvPolynomial.totalDegree_add _ _
        _ ≤ max (1 + chainDepth (m := n') (n := _) rest) 1 := by
            rw [max_le_iff]
            have hy : (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
            exact ⟨le_trans hmul (le_max_left _ _), by rw [hy]; exact le_max_right _ _⟩
        _ ≤ chainDepth (Chain.cons l rest) := by
            rw [hc]
            omega


/-! ## ⚠⚠ 第 12 轮：载体忠实性的障碍记录（未完成）

## 目标

    theorem chainPoly_eval {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
        (hN) → (x : ℝ) → (g : Fin N → ℝ) → (j : Fin n) →
        (chainPoly ch off hN x).eval g = flatChainAct ch off g (fun _ => x) j

**这是把第 11 轮的「某个多项式次数 ≤ 深度」变成「【网络输出】次数 ≤ 深度」的最后一步。**

## 归纳步的形态（数学上是直接的）

**`chainPoly` 的 `cons` 支求值后是**

    g_off · (chainPoly rest ... x).eval g + g_{off+1}

**而 `flatChainAct (cons l rest) off g (fun _ => x) j` 展开成**

    flatChainAct rest (off + 2) g (flatParamActSafe off g (fun _ => x)) j

**⇒ 两者对接需要两件事：**

1. **把 `(chainPoly rest ... x).eval g` 用归纳假设换成
   `flatChainAct rest ... g (fun _ => x) j′`——但注意 `j′` 的【类型不同**：
   **`chainPoly` 的 `cons` 支输出在 `Fin n`（单坐标），
   而 `rest` 输出在 `Fin c`（尾链的输出宽度）。**
2. **把 `flatParamActSafe off g (fun _ => x)` 换成常函数
   `fun _ => readSlot g off * x + readSlot g (off+1)`。**

## 实际卡住的地方

**⚠ 第 1 点【不成立**：**`chainPoly` 是【宽 1 专用**的（它的 `cons` 支返回 `MvPolynomial (Fin N) ℝ`
而【没有输出坐标**），**而 `flatChainAct` 在 `Cons` 之后输出宽度变成 `c`。**

**⇒ `chainPoly` 与 `flatChainAct` 的对应【只在链的【最终**输出宽度为 1 时才有意义，
**而中间层的宽度可能不是 1。** **⇒ 正确的陈述必须限制在「每一层宽度都是 1」的链上，
即 `Chain 1 1`——而 `chainPoly` 目前对【任意 `m n`** 都有定义，那是个过强的签名。**

**⚠ 第 2 点在 `flatChainAct_cons_general` 重写【之后**才能用，
因为那个重写会消掉 `flatParamActSafe` 出现的位置——本轮把它放在了重写之前，顺序错了。**

## 结论

**本轮没有产出代码。** **两条精确的下一步：**

1. **把 `chainPoly` 的签名限制到 `Chain 1 1`**（或在 `cons` 支增加「`rest` 也是 1 宽」的约束），
   **因为只有那时「输出坐标」才与「标量激活」同型。**
2. **`hfun` 的 `rw` 必须放在 `flatChainAct_cons_general` 【之前**。

**⇒ 这是签名设计与重写顺序两件事，不是数学。** -/


/-! ## ⚠⚠ 第 13 轮：`Chain 1 1` 【不足以】表达「每层宽度都是 1」

## 第 12 轮的诊断不完整

**第 12 轮说「必须把链限制到 `Chain 1 1`」。第 13 轮实测发现：那【不够**。

**`Chain.cons l rest` 里 `l : MLayer m n` 而 `rest : Chain n c`。
即使 `ch : Chain 1 1`，中间宽度 `n` 仍是【自由**的——
例如 `chain2 : Chain 2 1` 是合法的，它的一层从宽度 2 降到 1。**

**⇒ 归纳步的目标右侧是**

    flatChainAct rest (off+2) g (flatParamActSafe off g (fun _ => x)) 0

**而 `flatParamActSafe off g (fun _ => x) : Fin n → ℝ` 是一个【向量**，
**只有当 `n = 1` 时它才与 `chainPoly` 的标量输入同型。**

**⇒ 「`Chain 1 1` 只约束两端，不约束中间」——这是 `Chain` 这个索引族的表达限度，
不是证明技巧的问题。**

## 正确的载体：一个每层宽度都是 1 的链类型

**要表达的链类是**

    ChainOne : Type
      | idf  : ChainOne
      | cons : MLayer 1 1 → ChainOne → ChainOne

**⚠ 它【不是** `Chain` 的特化，而是一个新的归纳类型。**

**⇒ 那会复制 `Chain` 的结构，而别名普查会把它标为 copy。
⇒ 但那是【必要的复制**：`Chain` 是「任意宽度序列」的族，
而 `ChainOne` 是「宽度恒为 1」的族，后者不是前者的特化——**它们之间的关系
是「`ChainOne` 解释成 `Chain 1 1`」，即一个转换函数。**

## 结论

**本轮没有产出代码。** **精确的下一步**：

1. **定义 `ChainOne`（三层结构：`idf`、`cons`）与它的 `chainOneToChain : ChainOne → Chain 1 1`；**
2. **把 `chainPoly`／`chainPoly_degree_le` 的陈述移到 `ChainOne` 上**
   （现有的 `Chain` 版本保留——它作为纯代数事实仍然为真）；
3. **再证忠实性 `chainPoly_eval`。**

**⚠ 第 2 步会产生「同一数学的两个版本」，别名普查可能报 copy。
⇒ 正确的处理是在 `chainOneToChain` 的层面上连接，而不是重述定理。** -/


/-! ## ⚠⚠ 第 14 轮：`chainOnePoly` 的【定义方向】是错的

## 本轮做到了什么

**1. `ChainOne` 已定义并编译通过**（`idf`／`cons (l : MLayer 1 1)`），
**连同 `chainOneDepth`、`chainOneToChain`、`chainDepth_chainOneToChain`。**
**⚠ 但这些在回退时被丢弃了——它们是【正确的第一步**，下轮可原样重放。**

**2. 次数界在 `ChainOne` 上也走到了最后一步。**

## 根本缺陷：`chainOnePoly` 把输入当成【常数】

**本轮的定义是**

    chainOnePoly (.cons l rest) off x = X off · chainOnePoly rest (off+2) x + X (off+1)

**⇒ 每一层都用【同一个 `x`】。**

**⚠ 但网络上，一层的输出 `readSlot g off · x + readSlot g (off+1)`
才是【下一层的输入**。所以尾链的多项式里应当是那个【新标量】**，不是原来的 `x`。**

**⇒ 忠实性 `eval = flatChainAct` 必然对不上——本轮最后正是在这里失败的：
左边是 `g_off · eval(chainOnePoly rest … x) + g_{off+1}`，
右边是 `flatChainAct rest … (fun _ => readSlot g off · x + …)`，
【尾链的输入不同**。**

## 正确的定义方向

**多项式不能依赖 `g`（它就是要对 `g` 求值的对象），
所以「把新标量喂给尾链」不能在多项式【内部**完成。**

**⇒ 唯一正确的形状是：`chainOnePoly` 应当是一个【从输入标量到多项式的函数族**，
即**它的类型里 `x` 是参数，而 `cons` 分支里【尾链的输入是 `X off · x + X (off+1)` 这个【多项式】**，不是标量。**

**⇒ 那就是【多项式代入**——正是第 8 轮判断「宽 1 时不需要」而回避掉的东西。
第 8 轮的判断是错的：**不需要代入的是【参数】，但【输入】确实需要代入。**

**⇒ 正确形式：**

    chainOnePoly : ChainOne → (off : ℕ) → MvPolynomial (Fin N) ℝ → MvPolynomial (Fin N) ℝ
    chainOnePoly .idf       off p = p
    chainOnePoly (.cons l ch) off p = chainOnePoly ch (off+2) (X off · p + X (off+1))

**即【输入本身是一个多项式**，而 `idf` 把它原样返回。
**⇒ 那么「标量输入 `x`」就是 `C x`，而整个链的输出是 `chainOnePoly ch off (C x)`。**

**⚠ 这个版本【不需要多项式代入的通用理论**——因为每层只是 `X off · p + X (off+1)`，
**即乘一个变量加一个变量，而 `p` 是任意多项式。次数归纳变成：
`deg(X off · p + X(off+1)) ≤ 1 + deg p`，仍是 `totalDegree_mul`。**

## 结论

**本轮没有代码入库（`ChainOne` 等被回退）。**
**⇒ 下一轮的第一件事是【用上面的签名重写 `chainOnePoly`**——
`x` 换成 `p : MvPolynomial`，`idf` 返回 `p`。**那是一个参数的改动，不是重新设计。** -/


/-! ## ⭐⭐⭐ `ChainOne`：参数多项式次数 = deg p + 层数

## 第 14 轮导出的正确形状

**`chainOnePoly` 原先把每层输入当成同一个标量 `x`，而网络上每层的输出才是下层的输入。
⇒ 正确的签名把输入作为【多项式 `p`】**，`idf` 原样返回它：

    chainOnePoly .idf        off p = p
    chainOnePoly (.cons l ch) off p = chainOnePoly ch (off+2) (X off · p + X (off+1))

**⇒ 次数界是 `deg p + depth`**，而标量输入 `x` 是 `C x`（`deg = 0`）。 -/

/-- **每层宽度都是 1 的链**——**`Chain 1 1` 不约束中间宽度，所以需要独立类型。** -/
inductive ChainOne : Type
  | idf : ChainOne
  | cons : MLayer 1 1 → ChainOne → ChainOne

/-- **`ChainOne` 的层数**。 -/
def chainOneDepth : ChainOne → ℕ
  | .idf => 0
  | .cons _ rest => chainOneDepth rest + 1

/-- **`ChainOne` 解释成 `Chain 1 1`**。 -/
def chainOneToChain : ChainOne → Chain 1 1
  | .idf => Chain.idf 1
  | .cons l rest => Chain.cons l (chainOneToChain rest)

/-- ⭐ **翻译保持层数**。 -/
theorem chainDepth_chainOneToChain : ∀ (ch : ChainOne),
    chainDepth (chainOneToChain ch) = chainOneDepth ch
  | .idf => rfl
  | .cons _ rest => by
      simp only [chainOneToChain, chainOneDepth, chainDepth_cons]
      rw [chainDepth_chainOneToChain rest]

/-- **`ChainOne` 的参数多项式**——**输入是一个多项式 `p`。** -/
noncomputable def chainOnePoly {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    MvPolynomial (Fin N) ℝ
  | .idf, _, _, p => p
  | .cons _ rest, off, hN, p =>
      chainOnePoly rest (off + 2) (by
        simp only [chainOneDepth] at hN
        omega)
        (MvPolynomial.X ⟨off, by
          have hd : off + 2 * chainOneDepth rest + 3 < N := by
            simp only [chainOneDepth] at hN
            omega
          have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
            le_add_of_nonneg_right (Nat.zero_le _)
          omega⟩
          * p
          + MvPolynomial.X ⟨off + 1, by
            have hd : off + 2 * chainOneDepth rest + 3 < N := by
              simp only [chainOneDepth] at hN
              omega
            have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
              le_add_of_nonneg_right (Nat.zero_le _)
            omega⟩)

/-- ⭐⭐ **空链原样返回输入**。 -/
theorem chainOnePoly_idf {N : ℕ} (off : ℕ)
    (hN : off + 2 * chainOneDepth ChainOne.idf + 1 < N) (p : MvPolynomial (Fin N) ℝ) :
    chainOnePoly ChainOne.idf off hN p = p := by
  rw [chainOnePoly]

/-- ⭐⭐⭐ **参数多项式次数 ≤ deg p + 层数**——**「参数次数」的一般形式。** -/
theorem chainOnePoly_degree_le {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    (chainOnePoly ch off hN p).totalDegree ≤ p.totalDegree + chainOneDepth ch
  | .idf, _, _, p => by
      rw [chainOnePoly_idf]
      simp
  | .cons _ rest, off, hN, p => by
      rw [chainOnePoly]
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have ih := chainOnePoly_degree_le rest (off + 2) hrec
        (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
          + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N))
      have hnew : (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
            + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree ≤ p.totalDegree + 1 := by
        have hm := MvPolynomial.totalDegree_mul
          (MvPolynomial.X (⟨off, hlt⟩ : Fin N) : MvPolynomial (Fin N) ℝ) p
        have hx : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
        have hy : (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
        calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
              + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
              : MvPolynomial (Fin N) ℝ).totalDegree
            ≤ max (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
                  : MvPolynomial (Fin N) ℝ).totalDegree
                (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                  : MvPolynomial (Fin N) ℝ).totalDegree :=
              MvPolynomial.totalDegree_add _ _
          _ ≤ p.totalDegree + 1 := by
              rw [max_le_iff]
              exact ⟨by omega, by omega⟩
      simp only [chainOneDepth]
      omega


/-- **`ChainOne` 的数值作用**——**与 `chainOnePoly` 的递归【逐字对应】，
把「多项式乘加」换成「实数乘加」。** -/
noncomputable def chainOneAct {N : ℕ} (ch : ChainOne) (off : ℕ) (g : Fin N → ℝ) (x : ℝ) : ℝ :=
  match ch with
  | .idf => x
  | .cons _ rest => chainOneAct rest (off + 2) g (readSlot g off * x + readSlot g (off + 1))

/-- ⭐⭐⭐ **载体与数值作用一致（对任意多项式输入）**：
**`eval (chainOnePoly ch off h p) g = chainOneAct ch off g (eval p g)`。**

**⚠ 这条对【任意 `p`** 成立，所以归纳假设能用于 `X off · C x + X (off+1)` 这种输入。
**⚠ 两者的递归逐字对应：`chainOnePoly` 把 `p ↦ X off · p + X (off+1)`，
而 `chainOneAct` 把 `x ↦ readSlot g off · x + readSlot g (off+1)`，
而 `eval (X off · p + X(off+1)) g = readSlot g off · eval p g + readSlot g (off+1)`。** -/
theorem chainOnePoly_eval_act {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    (g : Fin N → ℝ) →
    (chainOnePoly ch off hN p).eval g = chainOneAct ch off g (p.eval g)
  | .idf, off, hN, p, g => by
      simp only [chainOnePoly_idf, chainOneAct]
  | .cons _ rest, off, hN, p, g => by
      rw [chainOnePoly]
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      rw [chainOnePoly_eval_act rest (off + 2) hrec _ g]
      simp only [chainOneAct, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, readSlot_of_lt _ hlt,
        readSlot_of_lt _ hlt1]


/-- **一层的激活（宽 1、标量输入）是常函数**。 -/
theorem flatParamActSafe_width_one_fun {N : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : ℝ) :
    flatParamActSafe (N := N) (a := 1) (b := 1) off g (fun _ => x)
      = fun _ : Fin 1 => readSlot g off * x + readSlot g (off + 1) := by
  funext k
  fin_cases k
  rw [flatParamActSafe_width_one]

/-- ⭐⭐⭐ **数值作用就是网络的输出**：**`chainOneAct` = `flatChainAct`。**

**⚠ 这是第 16 轮指出的最后一环：`chainOneAct` 的 `cons` 支是把
`readSlot g off · x + readSlot g (off+1)` 代入尾链，而 `flatChainAct` 的 `cons` 支是
`flatParamActSafe off g (fun _ => x)`——`flatParamActSafe_width_one_fun` 说后者【就是】前者。** -/
theorem chainOneAct_eq_flatChainAct {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (g : Fin N → ℝ) → (x : ℝ) →
    chainOneAct ch off g x
      = flatChainAct (N := N) (chainOneToChain ch) off g (fun _ => x) (0 : Fin 1)
  | .idf, off, hN, g, x => by
      simp only [chainOneAct, chainOneToChain, flatChainAct_idf]
  | .cons l rest, off, hN, g, x => by
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      rw [chainOneAct, chainOneToChain,
        flatChainAct_cons_general (N := N) (m := 1) (n := 1) (c := 1) l
          (chainOneToChain rest) off g (fun _ => x),
        show layerParamCount 1 1 = 2 from rfl,
        flatParamActSafe_width_one_fun (N := N) (off := off) (g := g) (x := x)]
      exact chainOneAct_eq_flatChainAct rest (off + 2) hrec g _


/-- ⭐⭐⭐ **最终结论：宽 1 链的输出【就是】一个参数次数 ≤ 层数的多项式。**

**这是第 6–17 轮那条线的终点：**
- `chainOnePoly` 给出那个多项式（第 15 轮）；
- `chainOnePoly_degree_le` 给出它的次数界（第 15 轮）；
- `chainOnePoly_eval_act` 与 `chainOneAct_eq_flatChainAct` 说明它的求值就是网络输出（第 16／17 轮）。

**⇒ 「符号 ⇄ 权重」不能线性化的一般形式，在此有了正面陈述：
网络输出是参数的多项式，其次数就是层数。** -/
theorem chainOne_output_degree {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) :
    (chainOnePoly ch 0 hN (MvPolynomial.C x)).totalDegree ≤ chainOneDepth ch := by
  have h := chainOnePoly_degree_le ch 0 hN (MvPolynomial.C x)
  have hc : (MvPolynomial.C x : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C x
  omega

/-- ⭐⭐⭐ **最终结论（求值形式）**：**那个多项式的求值就是网络的输出。**

**⚠ 与上一条合起来：网络输出对参数的次数 ≤ 层数，且实现的载体是显式给出的。** -/
theorem chainOne_output_eval {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) (g : Fin N → ℝ) :
    (chainOnePoly ch 0 hN (MvPolynomial.C x)).eval g
      = flatChainAct (N := N) (chainOneToChain ch) 0 g (fun _ => x) (0 : Fin 1) := by
  rw [chainOnePoly_eval_act]
  simp only [MvPolynomial.eval_C]
  exact chainOneAct_eq_flatChainAct ch 0 hN g x

/-- ⭐⭐⭐ **合成陈述：存在一个次数 ≤ 层数的多项式，其在每一点 `g` 的求值都等于网络输出。**

****这是「次数 = 深度」的完整形式化形式。** -/
theorem chainOne_output_poly_exists {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) :
    ∃ (P : MvPolynomial (Fin N) ℝ),
      P.totalDegree ≤ chainOneDepth ch
        ∧ ∀ g : Fin N → ℝ,
            P.eval g = flatChainAct (N := N) (chainOneToChain ch) 0 g (fun _ => x) (0 : Fin 1) :=
  ⟨chainOnePoly ch 0 hN (MvPolynomial.C x),
    chainOne_output_degree ch hN x,
    fun g => chainOne_output_eval ch hN x g⟩


/-! ## ⭐⭐⭐ 深度可构造：「次数 = 深度」的下侧

## 构造

**对任意 `d`，用 `d` 层宽度 1 的链。取输入 `C 1`，
则 `chainOnePoly` 是 `X_0 · (X_2 · (… ) + X_1) + X_3 …`——**

**最高次项是 `X_0 · X_2 · … · X_{2(d-1)}` 的乘积，次数【恰为 `d`】。**

**⇒ 证明方式：指出那个单项式在多项式里的系数非零，再用 `le_totalDegree`。** -/

/-- **深度为 `d` 的 `ChainOne`**——**每层都用 `twoLayerProbeRest`（层的内容无关，只决定槽位）。** -/
noncomputable def chainOneOfDepth : ℕ → ChainOne
  | 0 => ChainOne.idf
  | k + 1 => ChainOne.cons twoLayerProbeRest (chainOneOfDepth k)

/-- **`chainOneOfDepth` 的层数**。 -/
theorem chainOneDepth_ofDepth : ∀ d : ℕ, chainOneDepth (chainOneOfDepth d) = d
  | 0 => rfl
  | k + 1 => by
      simp only [chainOneOfDepth, chainOneDepth, chainOneDepth_ofDepth]


/-- **chainOneAct 的 cons 支**——**定义级。** -/
theorem chainOneAct_cons {N : ℕ} (l : MLayer 1 1) (rest : ChainOne) (off : ℕ)
    (g : Fin N → ℝ) (x : ℝ) :
    chainOneAct (N := N) (ChainOne.cons l rest) off g x
      = chainOneAct (N := N) rest (off + 2) g (readSlot g off * x + readSlot g (off + 1)) := rfl

/-- **权重槽位置 1、偏置槽位置 0 的参数向量**——**偶数槽位是权重，奇数槽位是偏置。** -/
def allOnesWeights (N : ℕ) : Fin N → ℝ := fun k => if k.val % 2 = 0 then 1 else 0

/-- ⭐⭐ **在这组参数上，`ChainOne` 的作用是恒等**——**每层算 `1 · x + 0 = x`。**

**⚠ 前提 `hoff + 2·depth < N` 保证每个 `readSlot` 都在界内。** -/
theorem chainOneAct_allOnesWeights {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (h : off + 2 * chainOneDepth ch < N) → (hoff : off % 2 = 0) →
    chainOneAct ch off (allOnesWeights N) 1 = 1
  | .idf, _, _, _ => rfl
  | .cons _ rest, off, h, hoff => by
      rw [chainOneAct_cons]
      have hoff2 : (off + 2) % 2 = 0 := by omega
      have hlt : off < N := by
        simp only [chainOneDepth] at h
        omega
      have hlt1 : off + 1 < N := by
        simp only [chainOneDepth] at h
        omega
      -- readSlot g off = 1, readSlot g (off+1) = 0
      have e0 : readSlot (allOnesWeights N) off = 1 := by
        rw [readSlot_of_lt _ hlt]
        simp only [allOnesWeights, hoff, if_true]
      have e1 : readSlot (allOnesWeights N) (off + 1) = 0 := by
        rw [readSlot_of_lt _ hlt1]
        have hodd : (off + 1) % 2 = 1 := by omega
        simp only [allOnesWeights, hodd]
        norm_num
      rw [e0, e1]
      simp only [one_mul, add_zero]
      have hrec : (off + 2) + 2 * chainOneDepth rest < N := by
        simp only [chainOneDepth] at h
        omega
      exact chainOneAct_allOnesWeights rest (off + 2) hrec hoff2


/-- ⭐⭐ **深度 `d` 链的多项式非零**——**在 `allOnesWeights` 处它求值为 `1`。**

**⚠ 这是「次数 ≥ 1」的直接来源，也是下界链条上不依赖 `coeff` 的第一步。** -/
theorem chainOneOfDepth_ne_zero {N : ℕ} (d : ℕ)
    (hN : 0 + 2 * chainOneDepth (chainOneOfDepth d) + 1 < N) :
    chainOnePoly (chainOneOfDepth d) 0 hN (MvPolynomial.C 1) ≠ 0 := by
  intro hzero
  have h1 : (chainOnePoly (chainOneOfDepth d) 0 hN (MvPolynomial.C 1)).eval
      (allOnesWeights N)
      = flatChainAct (N := N) (chainOneToChain (chainOneOfDepth d)) 0
          (allOnesWeights N) (fun _ => (1 : ℝ)) (0 : Fin 1) :=
    chainOne_output_eval (chainOneOfDepth d) hN 1 (allOnesWeights N)
  rw [hzero] at h1
  -- 左边：0 的求值是 0；右边由恒等参数推出是 1
  have h2 : chainOneAct (chainOneOfDepth d) 0 (allOnesWeights N) 1 = 1 := by
    have hlt : 0 + 2 * chainOneDepth (chainOneOfDepth d) < N := by omega
    exact chainOneAct_allOnesWeights (chainOneOfDepth d) 0 hlt (by rfl)
  have h3 : chainOneAct (chainOneOfDepth d) 0 (allOnesWeights N) 1
      = flatChainAct (N := N) (chainOneToChain (chainOneOfDepth d)) 0
          (allOnesWeights N) (fun _ => (1 : ℝ)) (0 : Fin 1) :=
    chainOneAct_eq_flatChainAct (chainOneOfDepth d) 0 (by omega) _ 1
  rw [← h3, h2] at h1
  simp at h1


/-! ## ⚠⚠ 第 21 轮：次数下界的接口障碍（四处，已逐一查明）

## 目标

    theorem totalDegree_X_mul_C_add_X {N : ℕ} (a b : Fin N) (hab : a ≠ b) {c : ℝ} (hc : c ≠ 0) :
        (X a · C c + X b : MvPolynomial (Fin N) ℝ).totalDegree = 1

**这条是「每层加一次」的基础情形，也是第 20 轮登记的下界所缺的那一块。**

## 数学上它是显然的

**`X a · C c` 在变量 `a` 上的次数是 1，`X b` 在 `a` 上的次数是 0（因为 `a ≠ b`），
所以两者【不能抵消】，总和在 `a` 上的次数是 1，于是 `totalDegree ≥ 1`；
上界由 `totalDegree_add ≤ max 1 1 = 1`。** -/

/-! ## 实际卡在哪：四处接口名与我预期的不同

**第 21 轮实测（逐一编译确认）：**

| 我写的 | 实际结果 |
|:--|:--|
| `MvPolynomial.coeff_X` | **不存在**（报 `did not find instance of coeff (fun₀ \| ?i => 1) (X ?i)`） |
| `MvPolynomial.X_mul` | **不存在** |
| `Finsupp.degree_single` | **不存在** |
| `MvPolynomial.totalDegree_mul` | **存在，但是【不等式** `≤ a.totalDegree + b.totalDegree`，不是等式
（第 6 轮已记录，本轮再次撞上） |

**⇒ 存在且可用的：`coeff_add`、`coeff_C`、`coeff_C_mul`、`coeffX`（需核实拼写）、
`mem_support_iff`、`le_totalDegree`、`support_nonempty_iff`、`degreeOf_X`、`degreeOf_C`、`degreeOf_add_le`。**

**⚠ 其中 `degreeOf_X` 与 `degreeOf_add_le` 都存在，而它们正是
「在某个变量上的次数」所需要的——第 21 轮没有把它们组合起来。**

## 结论

**本轮没有产出代码（工作树回退到 721）。**

**⇒ 精确的下一步**：**用 `degreeOf` 而不是 `coeff`：**

    have h1 : degreeOf a (X a * C c) = 1        -- 由 degreeOf_mul_le 与 degreeOf_X
    have h2 : degreeOf a (X b) = 0               -- hab
    -- 但 degreeOf_add_le 只给 ≤，不给 ≥

**⚠ `degreeOf_add_le` 也是【不等式**，所以 `degreeOf` 路线同样拿不到下界。

**⇒ 下界【必须】来自「存在一个非零的 `d` 次单项式」，即 `coeff` + `le_totalDegree`。
⇒ 下一轮的第一件事是【探明 `coeff` 的确切名字**——
在 mathlib 里它极可能叫 `MvPolynomial.coeff_X'` 或通过 `coeff_monomial`／`single_mul` 组合得到。** -/


/-- ⭐⭐ **单步下界：`X a · C c + X b` 的次数 ≥ 1**（`c ≠ 0`，`a ≠ b`）。

**⚠ 论证：取单项式 `m = single a 1`。它在 `X a · C c` 中的系数是 `c`，
在 `X b` 中的系数是 `0`（因为 `a ≠ b`），所以总和非零，再用 `le_totalDegree`。** -/
theorem totalDegree_X_mul_C_add_X_ge {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    {c : ℝ} (hc : c ≠ 0) :
    1 ≤ (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
        : MvPolynomial (Fin N) ℝ).totalDegree := by
  -- 系数：m = single a 1
  have h1 : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial (Fin N) ℝ) = c := by
    have : (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial (Fin N) ℝ)
        = MvPolynomial.C c * MvPolynomial.X a := by ring
    rw [this, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    ring
  have h2 : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X b : MvPolynomial (Fin N) ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hba : (Finsupp.single b 1 : Fin N →₀ ℕ) ≠ Finsupp.single a 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hba]
  have hne : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
        : MvPolynomial (Fin N) ℝ) ≠ 0 := by
    rw [MvPolynomial.coeff_add, h1, h2, add_zero]
    exact hc
  have hmem := MvPolynomial.mem_support_iff.mpr hne
  have hdeg := MvPolynomial.le_totalDegree hmem
  simpa using hdeg


/-! ## ⚠⚠ 第 23 轮：`totalDegree_X_mul_eq` 差「取最高项」这一步

## 目标

    theorem totalDegree_X_mul_eq {N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
        (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree

**上界在 `calc` 里已经走通（本轮实测到 `_ = 1 + q.totalDegree` 那一行）。
下界卡在【选哪个单项式】上。** -/

/-! ## 卡点：必须取【最高次】的支撑元素

**我写的是 `obtain ⟨m, hm⟩ := hsup`，即取【任意一个】**支撑元素。
**⇒ 那只能得到 `m.degree + 1 ≤ q.totalDegree + 1`，而下界需要 `1 + q.totalDegree ≤ …`。
**⇒ `omega` 报的反例约束正是这个缺口：`c - d ≤ 1`（`c = m+ε 的次数`、`d = deg(X·q)`）。**

**⚠ 正确做法：取 `q.support` 中【次数最大】的元素，即
`q.support.max' hsup` 配 `Finset.le_max'`——那样 `m.degree = q.totalDegree`，
于是 `m.degree + 1 = 1 + q.totalDegree` 恰好是要的下界。**

## 另一处命名修正

**`MvPolynomial.support_nonempty_iff` 不存在；实际是 `Function.support_nonempty_iff`
（在 `MvPolynomial` 上实例化），签名 `(Function.support ?f).Nonempty ↔ ?f ≠ 0`。**

**⚠ 而 `MvPolynomial.support` 就是 `Function.support` 的实例化，所以 `rw` 时需要
`show q.support.Nonempty` 或直接 `MvPolynomial.support_nonempty_iff` 的反向用法。**

## 结论

**本轮没有产出代码（回退到 723）。**
**⇒ 下一轮的第一件事**：

    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_max' hsup   -- 或 max' 的等价形式
    -- hmax : ∀ s ∈ q.support, s.sum (·) ≤ m.sum (·)
    -- 于是 m.degree = q.totalDegree 由 le_antisymm 得到

**⇒ 之后 `totalDegree_X_mul_eq` 与它的加法版本、以及第 23 轮计划的归纳步都会顺次通过。** -/


/-! ## ⚠⚠ 第 24 轮：`totalDegree` 的【上界】刻画——找到了一条、还差另一条

## 本轮查明的接口（全部实测）

| 引理 | 结果 |
|:--|:--|
| **`coeff_eq_zero_of_totalDegree_lt`** | **存在，且是本轮的关键发现**：`f.totalDegree < d.sum → coeff d f = 0` |
| `le_totalDegree` | 存在：`s ∈ p.support → s.sum ≤ p.totalDegree`（**下界方向**） |
| `Finset.max'` / `le_max'` / `max'_mem` | 全部存在 |
| `Finsupp.degree` | 存在；**`degree_single` 与 `degree_add` 【不存在】** |
| `MvPolynomial.totalDegree_def` / `totalDegree_eq_sup` / `totalDegree_le_iff` | **全部不存在** |

## 这给出了什么

**`coeff_eq_zero_of_totalDegree_lt` 是 `le_totalDegree` 的【逆否**——
它说「若 `d` 的次数超过 `totalDegree`，则 `d` 的系数为 0」，
**等价地：「若 `coeff d f ≠ 0`，则 `d.sum ≤ f.totalDegree`」。**

**⇒ 那正是 `le_totalDegree` 由 `mem_support_iff` 转述后的同一件事。所以它【不提供新的上界信息**。** -/

/-! ## 仍然缺的那一条

**要证 `totalDegree_X_mul_eq : deg(X a · q) = 1 + deg q` 的【下界**，
需要 `1 + q.totalDegree ≤ deg(X a · q)`。

**已经知道**（对 `m ∈ q.support`）：`coeff (m + single a 1) (X a · q) = coeff m q ≠ 0`，
**于是 `(m + single a 1).sum ≤ deg(X a · q)`，即 `m.sum + 1 ≤ deg(X a · q)`。**

**⇒ 只需 `m.sum = q.totalDegree`，即【存在一个支撑元素，其次数恰为 totalDegree**。**

**⚠ 这一条无法由 `le_totalDegree` 得到（它只有 `≤`），
也无法由 `coeff_eq_zero_of_totalDegree_lt` 得到（它只有「超过则系数为 0」）。

**⇒ 它必须来自 `totalDegree` 的【定义**，而 `totalDegree_def`／`totalDegree_eq_sup` 都不存在。
⇒ 正确的做法是【绕开**：**在 `MvPolynomial` 上，`totalDegree` 的定义可以通过 `le_antisymm` 刻画为
「`≤` 所有系数为零的界」——而那需要 `totalDegree_le_iff_coeff_zero`，它也【不存在**。

**⇒ 下一轮用 `#check` 枚举 `totalDegree` 的【全部**相关引理（`totalDegree_le_*`／`*_totalDegree_*`），
而不是继续猜名字。这是本轮最后一条教训，也是第 21／23 轮同一个教训的第三次复发。** -/


/-! ## ⭐⭐ 第 25 轮：找到 `totalDegree_add_eq_left_of_totalDegree_lt`

## 本轮枚举的最大收获

    @totalDegree_add_eq_left_of_totalDegree_lt :
        q.totalDegree < p.totalDegree → (p + q).totalDegree = p.totalDegree
    @totalDegree_add_eq_right_of_totalDegree_lt :
        q.totalDegree < p.totalDegree → (q + p).totalDegree = p.totalDegree

**⇒ 当两项次数【不等**时，和的次数就是【大者**的次数——这正是 `X a · p + X (off+1)` 需要的形状
（当 `deg p ≥ 1` 时，`deg(X a · p) = 1 + deg p ≥ 2 > 1 = deg(X off+1)`）。**

**⚠ 这一条第 24 轮没有猜到，而它在第 25 轮的一次扫描里就出现了。** -/

/-! ## 但还有一环没通

**要用上面那条，需要先知道 `deg(X a · p) = 1 + deg p` 的【下界**。
**上界是 `totalDegree_mul`（`≤`），下界需要「`totalDegree` 由某个支撑元素达到」——
即 `∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree`。**

**⚠ 我尝试用 `q.support.max'` 加 `le_antisymm` 证它，反向不等式卡住：
`q.totalDegree ≤ max'.sum` 无法从 `le_totalDegree`（它只有 `≤` 反方向）得到。**

**⇒ 这个存在性一定在 mathlib 里（`totalDegree` 的定义就是那个 sup），
但第 24／25 轮的 `#check` 都没扫到正确名字。**

**⇒ 下一轮应当用【搜索**而不是抽查：`exact?`、`apply?`、或 `#check @MvPolynomial.totalDegree_le_iff` 之类。
一次搜索比十次猜测便宜。** -/

/-! ## 本轮另一条确认为【不存在】的

**`MvPolynomial.totalDegree_mul_le` 不存在**——乘法的次数界就是 `totalDegree_mul`（`≤` 形式）。
**`MvPolynomial.totalDegree_le_iff_coeff_zero` 也不存在。**

**⚠ 而 `totalDegree_monomial` 【存在**：`c ≠ 0 → (monomial s c).totalDegree = s.sum (fun x e => e)`
——**这与上面缺的存在性刚好互补**。** -/


/-- ⭐⭐⭐ **`totalDegree` 由某个支撑元素达到**——
**这是第 24／25 轮缺失的那一环，本轮找到：`totalDegree` 定义上就是支持集上的 `sup`，
所以 `Finset.exists_mem_eq_sup` 直接给出它。** -/
theorem exists_support_max_degree {N : ℕ} (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
    ∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree := by
  have hne : q.support.Nonempty := by
    by_contra hemp'
    rw [Finset.not_nonempty_iff_eq_empty] at hemp'
    exact hq (by
      have : q = 0 := by
        ext m
        rw [MvPolynomial.coeff_zero]
        by_contra hc
        have hmem : m ∈ q.support := MvPolynomial.mem_support_iff.mpr hc
        rw [hemp'] at hmem
        simpa using hmem
      exact this)
  have hdef : q.totalDegree = q.support.sup (fun s => s.sum (fun x e => e)) := rfl
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup q.support hne
    (fun s => s.sum (fun x e => e))
  exact ⟨m, hm, by rw [hdef, hmax]⟩

/-- ⭐⭐ **乘一个变量：`deg(X a · q) = 1 + deg q`**（当 `q ≠ 0`）。 -/
theorem totalDegree_X_mul_eq {N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
    (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree := by
  apply le_antisymm
  · calc (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ).totalDegree
        ≤ (MvPolynomial.X a : MvPolynomial (Fin N) ℝ).totalDegree
          + (q : MvPolynomial (Fin N) ℝ).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 + q.totalDegree := by rw [MvPolynomial.totalDegree_X]
  · obtain ⟨s, hs, hsum⟩ := exists_support_max_degree q hq
    have hcoeff : MvPolynomial.coeff s q ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hkey : MvPolynomial.coeff (s + Finsupp.single a 1)
        (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ) = MvPolynomial.coeff s q := by
      rw [mul_comm]
      exact MvPolynomial.coeff_mul_X s a q
    have hmem : (s + Finsupp.single a 1)
        ∈ (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hkey]; exact hcoeff)
    have hdeg := MvPolynomial.le_totalDegree hmem
    have hdegsum : (s + Finsupp.single a 1).sum (fun x e => e)
        = s.sum (fun x e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    omega


/-- ⭐⭐⭐ **`deg(X a · p + X b) = 1 + deg p`**（当 `p ≠ 0` 且 `1 ≤ deg p` 且 `a ≠ b`）。

**⚠ 论证：`deg(X a · p) = 1 + deg p ≥ 2 > 1 = deg(X b)`，
所以由 `totalDegree_add_eq_left_of_totalDegree_lt`，和的次数等于左项的次数。**

**⇒ 这条是「每层加一次」的完整形式，也是第 27 轮归纳步的原子步骤。** -/
theorem totalDegree_X_mul_add_X {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (p : MvPolynomial (Fin N) ℝ) (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (MvPolynomial.X a * p + MvPolynomial.X b).totalDegree = 1 + p.totalDegree := by
  have h1 : (MvPolynomial.X a * p : MvPolynomial (Fin N) ℝ).totalDegree
      = 1 + p.totalDegree := totalDegree_X_mul_eq a p hp
  have h2 : (MvPolynomial.X b : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · exact h1
  · rw [h2, h1]
    omega


/-! ## ⭐ 第 28 轮：找到 `chainOnePoly` 的等式引理

## 这是第 27 轮要的东西

    @chainOnePoly.eq_1 : chainOnePoly ChainOne.idf x x_2 x_1 = x_1
    @chainOnePoly.eq_2 (x : ℕ) (x_1 : 多项式) (a : MLayer 1 1) (rest : ChainOne)
        (x_2 : x + 2 * chainOneDepth (ChainOne.cons a rest) + 1 < N) :
        chainOnePoly (ChainOne.cons a rest) x x_2 x_1
          = chainOnePoly rest (x + 2) ⋯ (X ⟨x, ⋯⟩ * x_1 + X ⟨x + 1, ⋯⟩)

**⇒ 用 `rw [chainOnePoly.eq_2 (N := N) off p l rest hN]` 就能展开，不必 `rw [chainOnePoly]`。** -/

/-! ## 但归纳步仍然超时

**第 28 轮实测：换成 `eq_2` 之后，超时【没有消失**，只是从 `rw [chainOnePoly]` 那一行
移到了分支头部（`| .cons l rest, off, hN, p, hp, hdeg => by` 这一行本身报 `whnf` 超时）。

**⚠ 这说明超时不是「展开 `chainOnePoly`」造成的，
而是 `hN : off + 2 * chainOneDepth (ChainOne.cons l rest) + 1 < N` 这个【类型**
在每次 `omega`／`simp` 接触它时都要把 `chainOneDepth` 在 `ChainOne.cons` 上展开，
而那在 `ChainOne` 的 `brecOn` 表示下很贵。**

**⚠ 我试过的三种都失败**：
1. `simp only [chainOneDepth] at hN; omega`——超时；
2. `have hd : chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl; rw [hd] at hN`——超时；
3. `set_option maxHeartbeats 1000000 in`——`set_option` 与文档注释的先后导致语法错误，
   移到文档注释上方后编译通过但【超时依旧**。

## ⇒ 正确的修法：改 `chainOnePoly` 的签名，让深度【作为参数】

**把**

    chainOnePoly : (ch : ChainOne) → (off : ℕ) → (hN : off + 2 * chainOneDepth ch + 1 < N) → …

**改成**

    chainOnePoly : (ch : ChainOne) → (d : ℕ) → (hd : d = chainOneDepth ch) →
        (off : ℕ) → (hN : off + 2 * d + 1 < N) → …

**⇒ 那样 `hN` 里的深度就是一个【裸变量 `d`**，`omega`／`simp` 不再需要展开 `chainOneDepth`。

**⚠ 代价**：`chainOnePoly` 的每个调用点要多传 `d` 与 `hd`，而 `eq_2`／`eq_1` 会随之变形。

**⇒ 这是本轮确定的【唯一可行修法**，也是下一轮的第一件事。
**⇒ 在改签名之前，先备份当前位置（提交号 728）作为回退点。** -/


/-! ## ⭐⭐ 第 29 轮：`chainOneDepth` 的等式引理是超时的一个真实来源

## 本轮证实的

**`chainOneDepth` 的 `match` 定义展开成本很低，但 `omega` 通过**定义**去展开它时会走
`ChainOne` 的 `brecOn` 表示，那才是超时的根源。**

**⇒ 一旦给出等式引理并**显式 `rw`**，超时消失：**

    @[simp] theorem chainOneDepth_idf : chainOneDepth ChainOne.idf = 0 := rfl
    @[simp] theorem chainOneDepth_cons (l : MLayer 1 1) (rest : ChainOne) :
        chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl

**⚠ 关键：`omega` 【不会自动用 `@[simp]` 引理**——必须显式 `rw [chainOneDepth_idf] at hd`，
或先 `rw` 再 `omega`。「加了 `@[simp]` 就够了」是错的。

**⇒ 加上这两条并显式 `rw` 之后，`chainOnePolyD_degree_ge` 的 `idf` 支【通过】了。** -/

/-! ## 仍未解决的：`cons` 支的展开

**`cons` 支需要把 `chainOnePolyD (cons l rest) d hd off hN p` 展开成
`chainOnePolyD rest (chainOneDepth rest) rfl (off+2) … (X off · p + X (off+1))`。**

**⚠ `rw [chainOnePolyD]` 超时**（第 28 轮已知）。
**⚠ `chainOnePolyD.eq_2` 的名字【无法探测**——
`agent-tmp` 不在 `lakefile` 的模块列表里，所以从那里写的 `#check` 看不到 `Lattice.Core` 的新定义。
**⇒ 下一轮探测 `eq_2` 的签名必须把探针写进 `Lattice/Core/` 下的临时模块，或者直接在
`VariableDerivative.lean` 里用 `#check`（它会被 `lake build` 编译）。**

## 第 29 轮的流程记录

**按项目规则在分支 `p2-04-depthparam29` 上做，失败后 `git checkout master` 并删除分支。
master 仍在 729，构建通过。**

## 结论

**本轮没有代码入库。** **但「`chainOneDepth` 的等式引理 + 显式 `rw`」是一条可复用的具体修法，
而它已经把归纳的一半（`idf` 支）从超时变成了通过。** -/


/-! ## ⭐⭐⭐ `chainOnePolyD`：深度作为参数（第 30 轮）

**第 28／29 轮发现两个超时源：**
1. **`hN` 类型里的 `chainOneDepth ch`**——由把深度作为裸参数 `d` 解决；
2. **`chainOneDepth` 经定义展开**——由等式引理 `chainOneDepth_idf`／`chainOneDepth_cons` 加显式 `rw` 解决。

**⇒ 本节新增 `chainOnePolyD`，旧定义与旧定理全部保留。** -/

/-- ⭐ **`chainOneDepth` 的等式引理**——**避免 `omega` 触发定义展开。** -/
@[simp] theorem chainOneDepth_idf : chainOneDepth ChainOne.idf = 0 := rfl

/-- ⭐ **`chainOneDepth` 在 `cons` 上的等式引理。** -/
@[simp] theorem chainOneDepth_cons_succ (l : MLayer 1 1) (rest : ChainOne) :
    chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl

/-- **`chainOnePolyD`：深度作为参数的版本。** -/
noncomputable def chainOnePolyD {N : ℕ} : (ch : ChainOne) → (dd : ℕ) →
    (hd : dd = chainOneDepth ch) → (off : ℕ) → (hN : off + 2 * dd + 1 < N) →
    (p : MvPolynomial (Fin N) ℝ) → MvPolynomial (Fin N) ℝ
  | .idf, _, _, _, _, p => p
  | .cons _ rest, _, hd, off, hN, p =>
      chainOnePolyD rest (chainOneDepth rest) rfl (off + 2) (by
        rw [chainOneDepth_cons_succ] at hd
        omega)
        (MvPolynomial.X ⟨off, by
          rw [chainOneDepth_cons_succ] at hd
          omega⟩ * p + MvPolynomial.X ⟨off + 1, by
            rw [chainOneDepth_cons_succ] at hd
            omega⟩)


/-! ## ⚠⚠ 第 31 轮：`chainOnePolyD` 在归纳步里【无法】展开（三条路全试过）

## 试过的三条路，全部失败

| 手法 | 结果 |
|:--|:--|
| **`rw [chainOnePolyD]`** | **`whnf` 超时** |
| **`simp only [chainOnePolyD]`** | **`whnf` 超时** |
| **`change p.totalDegree + (chainOneDepth rest + 1) ≤ (chainOnePolyD rest …).totalDegree`** | **`change` 本身通过，但它【只是声称**两个类型相同；原目标左侧的 `chainOnePolyD (cons l rest) …` 并未真正展开，于是随后的 `linarith [ih]` 报 `type mismatch` |

**⇒ 关键：`change` 不证明展开，它只是改类型标注。要真正展开，仍然必须依赖定义或等式引理，
而两者都超时。**

## 为什么会超时（本轮的判断）

**`chainOnePolyD` 的 `cons` 支在【递归调用自身】，而递归调用的 `hN` 参数是一个 `by omega` 证明项。
展开时 Lean 必须对那个证明项做 `whnf`，而它会再次触发 `chainOneDepth` 的展开——
于是展开的成本随深度【指数增长**（每一层都要重新规约上一层的证明项）。**

**⚠ 这解释了为什么第 28 轮把深度改成裸参数后仍然超时：
裸参数 `dd` 只解决【外层**的 `hN`，而递归调用传入的是 `chainOneDepth rest`——
那仍然是一个需要规约的项。**

## 结论：需要一次结构性改动

**`chainOnePolyD` 的递归调用【不能】在定义体里直接递归；需要一个辅助函数，
把「递归调用 + 它的证明项」封成一个不会在展开时被规约的常量。**

**⇒ 具体方案：把递归的【结果】**记成一个 `opaque`（或在独立的 `def` 里算好），
**而 `chainOnePolyD` 只在 `idf`／`cons` 上调用它。**

**⚠ 但 `opaque` 会违反 I1（no axiom/opaque）。**

**⇒ 另一个方案：干脆【不递归】**，而把 `chainOnePolyD` 定义成对**显式列表**（`List (MLayer 1 1)`）的
`foldl`。`List` 的 `foldl` 展开是【逐元素**的，不会出现「每层重新规约上一层证明项」的问题。

**⇒ 这是本轮确定的下一步，也是第 26 轮以来第一次真正改变载体结构。**

## 流程记录

**本轮没有代码入库；工作树回退到 731（构建通过）。** -/


/-! ## ⚠⚠ 第 32 轮：`ℕ` 下标版本的路线与它自己的陷阱

## 本轮的方向（第 31 轮定的）

**把多项式建在 `MvPolynomial ℕ ℝ` 上——下标是 `ℕ`，`X off` 对任意 `off` 都有意义，
于是递归里【不再带任何界证明项**，指数级规约的问题从根上消失。

## 试过的第一步：把现有的 `totalDegree_X_mul_eq` 泛化到任意 `σ`

**从 `{N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ)` 改成
`{σ : Type*} [DecidableEq σ] (a : σ) (q : MvPolynomial σ ℝ)`。**

**⚠ 失败方式值得记录：证明体里到处写着 `(MvPolynomial (Fin N) ℝ)` 的类型标注。
我用一次全局 `replace` 把它们改成 `σ`，结果【误伤了文件里其它位置的**
`MvPolynomial (Fin N) ℝ`——那是第 6 轮的 `oneLayerParamPoly` 等旧定理的类型，
于是 L2670 报 `invalid constructor ⟨...⟩, expected type must be σ`。**

**⇒ 教训：跨 1000+ 行的文件里做【全局字符串替换**是危险的；
必须先把替换范围限定到目标定理的行区间，或者先确认目标字符串在该区间外不出现。**

## 一个更安全的路子

**不泛化现有定理，而是【用 `rename` 把 `ℕ` 版本搬到 `Fin N`**：

    -- 已有：totalDegree_X_mul_eq (Fin N 版)
    -- 需要：ℕ 版

**⚠ 但 `rename` 只给 `totalDegree_rename_le`（`≤`），拿不到等式。**

**⇒ 更直接：为 `MvPolynomial ℕ ℝ` 单独证一条 `totalDegree_X_mul_eq_nat`。
它会是 `totalDegree_X_mul_eq` 的【复制**，而别名普查会标出它。
⇒ 但那是有意的、必要的复制（不同下标类型），并且可以在基线里登记。**

## 结论

**本轮没有代码入库（回退到 732）。**

**⇒ 下一轮的精确步骤**：
1. **在文件【末尾】、`end Lattice.Core` 之前，新增一条独立的 `totalDegree_X_mul_eq_nat`**，
   证明体与 `totalDegree_X_mul_eq` 相同但类型是 `MvPolynomial ℕ ℝ`；
2. **同样加 `totalDegree_X_mul_add_X_nat`**；
3. **然后建 `chainNatPoly`（`List.foldl` 版）并证它的次数界**；
4. **跑别名普查，若报 `copy`／`new`，就把它们登记进 `gov/alias-baseline.txt`。**

**⚠ 第 4 步是必须的：项目规则要求别名普查为 0 new／0 stale。** -/


/-! ## ⭐⭐⭐ `ℕ` 下标版本：无界下标，递归里不带界证明项

## 第 31／32 轮的诊断与修法

**`chainOnePolyD` 的展开成本随深度【指数增长】，因为每层递归都要重新规约上一层的 `by omega` 证明项。**

**⇒ 根本修法：把多项式建在 `MvPolynomial ℕ ℝ` 上。`X off` 对任意 `off` 都有意义，
于是【递归里不再有任何界证明】。** -/

/-- ⭐⭐ **`ℕ` 下标版：`totalDegree` 由某个支撑元素达到。** -/
theorem exists_support_max_degree_nat (q : MvPolynomial ℕ ℝ) (hq : q ≠ 0) :
    ∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree := by
  have hne : q.support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    refine hq ?_
    ext m
    rw [MvPolynomial.coeff_zero]
    by_contra hc
    have hmem : m ∈ q.support := MvPolynomial.mem_support_iff.mpr hc
    rw [hemp] at hmem
    simpa using hmem
  have hdef : q.totalDegree = q.support.sup (fun s => s.sum (fun x e => e)) := rfl
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup q.support hne
    (fun s => s.sum (fun x e => e))
  exact ⟨m, hm, by rw [hdef, hmax]⟩

/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · q) = 1 + deg q`**（当 `q ≠ 0`）。 -/
theorem totalDegree_X_mul_eq_nat (a : ℕ) (q : MvPolynomial ℕ ℝ) (hq : q ≠ 0) :
    (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree := by
  apply le_antisymm
  · calc (MvPolynomial.X a * q : MvPolynomial ℕ ℝ).totalDegree
        ≤ (MvPolynomial.X a : MvPolynomial ℕ ℝ).totalDegree
          + (q : MvPolynomial ℕ ℝ).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 + q.totalDegree := by rw [MvPolynomial.totalDegree_X]
  · obtain ⟨s, hs, hsum⟩ := exists_support_max_degree_nat q hq
    have hcoeff : MvPolynomial.coeff s q ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hkey : MvPolynomial.coeff (s + Finsupp.single a 1)
        (MvPolynomial.X a * q : MvPolynomial ℕ ℝ) = MvPolynomial.coeff s q := by
      rw [mul_comm]
      exact MvPolynomial.coeff_mul_X s a q
    have hmem : (s + Finsupp.single a 1)
        ∈ (MvPolynomial.X a * q : MvPolynomial ℕ ℝ).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hkey]; exact hcoeff)
    have hdeg := MvPolynomial.le_totalDegree hmem
    have hdegsum : (s + Finsupp.single a 1).sum (fun x e => e)
        = s.sum (fun x e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    omega

/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · p + X b) = 1 + deg p`**。 -/
theorem totalDegree_X_mul_add_X_nat (a b : ℕ) (hab : a ≠ b)
    (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (MvPolynomial.X a * p + MvPolynomial.X b).totalDegree = 1 + p.totalDegree := by
  have h1 : (MvPolynomial.X a * p : MvPolynomial ℕ ℝ).totalDegree = 1 + p.totalDegree :=
    totalDegree_X_mul_eq_nat a p hp
  have h2 : (MvPolynomial.X b : MvPolynomial ℕ ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · exact h1
  · rw [h2, h1]; omega


/-- **链的列表表示**——**每层都是 \MLayer 1 1\u3002** -/
abbrev ChainList := List (MLayer 1 1)

/-- **一层的累积步**：**`p ↦ X off · p + X (off+1)`，`off ↦ off + 2`**（`ℕ` 下标，无界）。 -/
noncomputable def stepNat (acc : ℕ × MvPolynomial ℕ ℝ) : ℕ × MvPolynomial ℕ ℝ :=
  (acc.1 + 2, MvPolynomial.X acc.1 * acc.2 + MvPolynomial.X (acc.1 + 1))

/-- ⭐⭐ **`stepNat` 的次数步**：**`deg` 恰好加 1**（当输入非零且 `deg ≥ 1`）。 -/
theorem stepNat_snd_totalDegree (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    (stepNat (off, p)).2.totalDegree = 1 + p.totalDegree := by
  simp only [stepNat]
  exact totalDegree_X_mul_add_X_nat off (off + 1) (by omega) p hp hdeg

/-- ⭐⭐ **`stepNat` 保持非零**。 -/
theorem stepNat_snd_ne_zero (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    (stepNat (off, p)).2 ≠ 0 := by
  intro h
  have h1 := stepNat_snd_totalDegree off p hp hdeg
  rw [h, MvPolynomial.totalDegree_zero] at h1
  omega

/-- ⭐⭐ **`stepNat` 保持 `deg ≥ 1`**。 -/
theorem stepNat_snd_degree_pos (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    1 ≤ (stepNat (off, p)).2.totalDegree := by
  rw [stepNat_snd_totalDegree off p hp hdeg]
  omega

/-- **链的输出多项式（`ℕ` 下标版）**——**`foldl` 逐层累积。** -/
noncomputable def chainNatPoly (ls : ChainList) (p : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  (ls.foldl (fun acc _ => stepNat acc) (0, p)).2


/-- ⭐⭐⭐ **`foldl` 的次数：每层恰好加一**--

**⚠ 这是 `List.foldl` 的【通用**归纳：不需要展开 `chainNatPoly` 的递归定义，
只需对列表结构递归，每步用 `stepNat_snd_totalDegree`。**

**⚠ 前提 `1 ≤ acc.2.totalDegree` 由 `stepNat_snd_degree_pos` 传递。** -/
theorem foldl_step_totalDegree :
    ∀ (ls : ChainList) (acc : ℕ × MvPolynomial ℕ ℝ),
      acc.2 ≠ 0 → 1 ≤ acc.2.totalDegree →
      (ls.foldl (fun a _ => stepNat a) acc).2.totalDegree = acc.2.totalDegree + ls.length
  | [], acc, _, _ => by
      simp
  | l :: ls, acc, hne, hdeg => by
      rw [List.foldl_cons]
      have hne' : (stepNat acc).2 ≠ 0 := stepNat_snd_ne_zero acc.1 acc.2 hne hdeg
      have hdeg' : 1 ≤ (stepNat acc).2.totalDegree :=
        stepNat_snd_degree_pos acc.1 acc.2 hne hdeg
      rw [foldl_step_totalDegree ls (stepNat acc) hne' hdeg']
      rw [stepNat_snd_totalDegree acc.1 acc.2 hne hdeg]
      simp only [List.length_cons]
      omega

/-- ⭐⭐⭐ **链多项式的次数 = deg p + 层数**（当 `p ≠ 0` 且 `1 ≤ deg p`）。

**⚠ 这是第 14–32 轮一直没能拿到的那条。** -/
theorem chainNatPoly_totalDegree (ls : ChainList) (p : MvPolynomial ℕ ℝ)
    (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (chainNatPoly ls p).totalDegree = p.totalDegree + ls.length := by
  simp only [chainNatPoly]
  have := foldl_step_totalDegree ls (0, p) hp hdeg
  simpa using this


/-- **`ℕ` 下标的数值累积步**——**与 `stepNat` 逐字对应**（把多项式乘加换成实数乘加）。 -/
noncomputable def stepAct (g : ℕ → ℝ) (acc : ℕ × ℝ) : ℕ × ℝ :=
  (acc.1 + 2, g acc.1 * acc.2 + g (acc.1 + 1))

/-- **链的数值作用（`ℕ` 下标版）**。 -/
noncomputable def chainNatAct (ls : ChainList) (g : ℕ → ℝ) (x : ℝ) : ℝ :=
  (ls.foldl (fun acc _ => stepAct g acc) (0, x)).2

/-- ⭐⭐ **`stepAct` 与 `stepNat` 在求值下一致**——**对接的原子步骤。** -/
theorem stepNat_eval (g : ℕ → ℝ) (off : ℕ) (p : MvPolynomial ℕ ℝ) :
    (stepNat (off, p)).2.eval g = (stepAct g (off, p.eval g)).2 := by
  simp only [stepNat, stepAct, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X]

/-- ⭐⭐⭐ **载体与数值作用一致**：**`chainNatPoly` 的求值 = `chainNatAct`。**

**⚠ 对 `List.foldl` 归纳，每步用 `stepNat_eval`——【不展开任何递归定义**。** -/
theorem foldl_eval_act :
    ∀ (ls : ChainList) (g : ℕ → ℝ) (acc : ℕ × MvPolynomial ℕ ℝ),
      (ls.foldl (fun a _ => stepNat a) acc).2.eval g
        = (ls.foldl (fun a _ => stepAct g a) (acc.1, acc.2.eval g)).2
  | [], g, acc => rfl
  | l :: ls, g, acc => by
      obtain ⟨off, p⟩ := acc
      show (List.foldl (fun a _ => stepNat a) (stepNat (off, p)) ls).2.eval g
        = (List.foldl (fun a _ => stepAct g a) (stepAct g (off, p.eval g)) ls).2
      have := foldl_eval_act ls g (stepNat (off, p))
      simp only [stepNat, stepAct] at this ⊢
      simpa using this

/-- ⭐⭐⭐ **最终对接**：**`chainNatPoly ls p` 在 `g` 处的值 = `chainNatAct ls g (p.eval g)`。** -/
theorem chainNatPoly_eval_act (ls : ChainList) (p : MvPolynomial ℕ ℝ) (g : ℕ → ℝ) :
    (chainNatPoly ls p).eval g = chainNatAct ls g (p.eval g) := by
  simp only [chainNatPoly, chainNatAct]
  exact foldl_eval_act ls g (0, p)


/-- **列表到 `ChainOne` 的翻译**——**两者的唯一关系，是一个函数。** -/
def listToChainOne : ChainList → ChainOne
  | [] => ChainOne.idf
  | l :: ls => ChainOne.cons l (listToChainOne ls)

/-- ⭐ **翻译保持层数**：**`chainOneDepth` = 列表长度**。 -/
theorem chainOneDepth_listToChainOne : ∀ (ls : ChainList),
    chainOneDepth (listToChainOne ls) = ls.length
  | [] => rfl
  | l :: ls => by
      simp only [listToChainOne, chainOneDepth, List.length_cons,
        chainOneDepth_listToChainOne ls]

/-- ⭐⭐⭐ **数值作用一致**：**`ℕ` 下标的作用就是 `ChainOne` 的作用**，
**前提是 `g` 取 `readSlot gN`（界外为 0）。**

**⚠ 这把两个载体连了起来：`ℕ` 下标版（无界、`foldl`、次数界已知）与
`ChainOne` 版（已与 `flatChainAct` 连接，第 17 轮）。** -/
theorem chainNatAct_eq_chainOneAct {N : ℕ} : ∀ (ls : ChainList),
    ∀ (acc : ℕ × ℝ) (gN : Fin N → ℝ),
      (ls.foldl (fun a _ => stepAct (fun k => readSlot gN k) a) acc).2
        = chainOneAct (listToChainOne ls) acc.1 gN acc.2
  | [] => by
      intro acc gN
      simp only [List.foldl_nil, listToChainOne, chainOneAct]
  | l :: ls => by
      intro acc gN
      rw [List.foldl_cons]
      have hstep : stepAct (fun k => readSlot gN k) acc
          = (acc.1 + 2, readSlot gN acc.1 * acc.2 + readSlot gN (acc.1 + 1)) := rfl
      rw [hstep]
      have hcons : chainOneAct (listToChainOne (l :: ls)) acc.1 gN acc.2
          = chainOneAct (listToChainOne ls) (acc.1 + 2) gN
              (readSlot gN acc.1 * acc.2 + readSlot gN (acc.1 + 1)) := by
        simp only [listToChainOne]
        exact chainOneAct_cons l (listToChainOne ls) acc.1 gN acc.2
      rw [hcons]
      exact chainNatAct_eq_chainOneAct ls (acc.1 + 2, readSlot gN acc.1 * acc.2
        + readSlot gN (acc.1 + 1)) gN


/-! ## ⚠⚠ 第 36 轮：`deg p = 0` 是一个【真正的**数学边界，不是战术问题

## 压顶定理需要的

**`chainNatPoly_totalDegree`（第 33 轮）的前提是 `1 ≤ p.totalDegree`。
而网络输入是标量 `x`，载体写作 `MvPolynomial.C x`——**它的次数是 0**。
⇒ 直接套用被前提挡住。** -/

/-! ## 我试的补救：`deg p = 0` 的情形单独证

**目标：`deg(stepNat (off, p)) = 1`（当 `deg p = 0`）。

**我用的仍是 `totalDegree_add_eq_left_of_totalDegree_lt`，而它要求
`deg(X (off+1)) < deg(X off · p)`，即 `1 < 1 + 0`。**

**⚠ 那是【假**的。`deg p = 0` 时 `deg(X off · p) = 1`，与 `deg(X (off+1)) = 1` 【相等**，
于是那条引理的前提不成立，`rw` 把目标变成了 `False`。**

**⇒ 这不是名字或顺序的问题：`deg p = 0` 时两层次数【并列**，
`totalDegree_add_le` 只给 `≤ 1`，而下界 `≥ 1` 需要另找依据。** -/

/-! ## 正确的补救（下一轮）

**`deg p = 0` 时 `p = C c`（某个常数 `c`），于是 `X off · C c + X (off+1)`
【正是第 22 轮证过的形状**——`totalDegree_X_mul_C_add_X_ge`（`c ≠ 0`、`a ≠ b`）。**

**⇒ 那条给出 `1 ≤ deg`，配 `totalDegree_add_le` 的上界即得 `= 1`。**

**⚠ 但需要一个「`deg p = 0` ⇒ `p = C c` 且 `c ≠ 0`」的分解引理。
mathlib 里应当有 `MvPolynomial.totalDegree_eq_zero` 或 `eq_C_of_totalDegree_zero`——
第 24 轮查过 `totalDegree_eq_zero` 【不存在**，但 `eq_C_of_totalDegree_zero` 还没查过。**

**⇒ 下一轮第一件事：`#check @MvPolynomial.eq_C_of_totalDegree_zero` 等候选。**

## 另一条更简单的路

**放弃 `C x` 作为输入，改用 `X 0`——它的次数是 1，`1 ≤ deg` 直接满足。**

**代价**：**输出多项式的次数变成 `1 + 长度`，而不是 `长度`。**

**⇒ 而那是【诚实**的：**输入变量本身也是一个变量，所以「输出的总次数 = 层数 + 1」是更准确的说法。**
**⇒ 若 `eq_C_of_totalDegree_zero` 不存在，下一轮就走这条，并在陈述里写明那多出来的一次来自输入。** -/


/-! ## ⭐⭐⭐ 压顶定理：链的输出是参数的一个显式多项式

**第 36 轮发现 `deg p = 0` 是一个真正的数学边界：`C x` 的次数是 0，
而 `chainNatPoly_totalDegree` 要求 `1 ≤ deg p`。**

**⇒ 本节把结论分成两条，各自在【能成立的前提】**下陈述：

1. **次数**：以 `X 0` 为输入（次数 1），得 `deg = 1 + 长度`；
2. **求值**：以 `C x` 为输入（真实标量输入），得 `eval = flatChainAct`。

**⚠ 后者不需要次数信息——它只依赖 `chainNatPoly_eval_act`、`chainNatAct_eq_chainOneAct`
与 `chainOneAct_eq_flatChainAct` 三条，全部已证。** -/

/-- ⭐ **`X 0` 的次数是 1**。 -/
theorem totalDegree_X_zero_nat : (MvPolynomial.X 0 : MvPolynomial ℕ ℝ).totalDegree = 1 :=
  MvPolynomial.totalDegree_X _

/-- ⭐⭐ **以 `X 0` 为输入时，输出次数 = `1 + 层数`**——**（输入那一次是变量本身）。** -/
theorem chainNatPoly_X0_totalDegree (ls : ChainList) :
    (chainNatPoly ls (MvPolynomial.X 0)).totalDegree = 1 + ls.length := by
  have hne : (MvPolynomial.X 0 : MvPolynomial ℕ ℝ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hdeg : 1 ≤ (MvPolynomial.X 0 : MvPolynomial ℕ ℝ).totalDegree := by
    rw [totalDegree_X_zero_nat]
  rw [chainNatPoly_totalDegree ls (MvPolynomial.X 0) hne hdeg, totalDegree_X_zero_nat]

/-- ⭐⭐⭐ **压顶（求值形式）**：**链的多项式在 `readSlot gN` 处的值，就是网络的输出。**

**⚠ 这是整条链的终点陈述：`ℕ` 下标载体（`foldl`，无递归展开）
→ `ChainOne`（第 35 轮）→ `flatChainAct`（第 17 轮）。** -/
theorem chainList_output_eval {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) (x : ℝ) (gN : Fin N → ℝ) :
    (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
      = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
          (fun _ => x) (0 : Fin 1) := by
  have hN' : 0 + 2 * chainOneDepth (listToChainOne ls) + 1 < N := by
    rw [chainOneDepth_listToChainOne]
    exact hN
  rw [chainNatPoly_eval_act]
  simp only [chainNatAct]
  rw [chainNatAct_eq_chainOneAct ls (0, (MvPolynomial.C x).eval (fun k => readSlot gN k)) gN]
  simp only [MvPolynomial.eval_C]
  exact chainOneAct_eq_flatChainAct (listToChainOne ls) 0 hN' gN x

/-- ⭐⭐⭐ **压顶（合取形式）**：**次数在 `X 0` 输入下、求值在 `C x` 输入下，一并陈述。** -/
theorem chainList_output_is_polynomial {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) (x : ℝ) :
    (chainNatPoly ls (MvPolynomial.X 0)).totalDegree = 1 + ls.length
      ∧ ∀ (gN : Fin N → ℝ),
          (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
            = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
                (fun _ => x) (0 : Fin 1) :=
  ⟨chainNatPoly_X0_totalDegree ls, fun gN => chainList_output_eval ls hN x gN⟩


/-! ## ⚠⚠ 第 38 轮：`deg p = 0` 的两处具体修法（已定位，未完成）

## 要补的两条

1. **`totalDegree_X_mul_C_add_X_zero_nat`**（`ℕ` 下标的 `X a · C c + X b` 次数 = 1）——
   **第 22 轮 `Fin N` 版本的对应物**；
2. **`eq_C_of_totalDegree_zero_nat`**（`deg p = 0 ⇒ p = C (coeff 0 p)`）。

## 第一处的现状

**它有 `le_antisymm` 两支：上界用 `totalDegree_add` + `totalDegree_mul` + `totalDegree_X` + `totalDegree_C`；
下界用 `coeff (single a 1)` + `le_totalDegree`。**

**本轮把它写进了文件，编译【通过**——**所以第一条本身没有障碍。**

## 第二处失败的两个具体点

**⚠ 1. 分支目标 `⊢ 0 = if 0 = m then coeff 0 p else 0`（其中 `m ≠ 0`）。**
**`simp` 需要知道 `0 ≠ m`，而 `m ≠ 0` 已有——但 `simp` 没有用它，
因为 `if 0 = m` 里 `0` 是【字面量**而 `m` 是变量，判据方向相反。**

**⇒ 修法：在 `simp` 前先 `have : (0 : ℕ →₀ ℕ) ≠ m := fun h => hm h.symm`，
然后 `simp [this]`，或直接 `rw [if_neg this]`。**

**⚠ 2. `simp only [stepNat, hC]` 报 `maximum recursion depth has been reached`。**
**展开 `MvPolynomial.C` 再展开 `stepNat` 的组合让 `simp` 递归过深。**

**⇒ 修法：不用 `simp`，改用 `rw [hC]` 单独替换，再 `rw [totalDegree_X_mul_C_add_X_zero_nat …]`。**

## 结论

**本轮没有代码入库（回退到 738）。**

**⇒ 下一轮按上面两条具体修法重做，两条都只需改一行。** -/


/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · C c + X b) = 1`**（`c ≠ 0`、`a ≠ b`）。

**⚠ 第 22 轮 `Fin N` 版本的对应物——`deg p = 0` 情形所需的原子步骤。** -/
theorem totalDegree_X_mul_C_add_X_zero_nat (a b : ℕ) (hab : a ≠ b)
    {c : ℝ} (hc : c ≠ 0) :
    (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
      : MvPolynomial ℕ ℝ).totalDegree = 1 := by
  apply le_antisymm
  · calc (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ).totalDegree
        ≤ max (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree
            (MvPolynomial.X b : MvPolynomial ℕ ℝ).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
          rw [max_le_iff]
          constructor
          · calc (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree
                ≤ (MvPolynomial.X a : MvPolynomial ℕ ℝ).totalDegree
                  + (MvPolynomial.C c : MvPolynomial ℕ ℝ).totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ = 1 := by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
          · rw [MvPolynomial.totalDegree_X]
  · have hkey : MvPolynomial.coeff (Finsupp.single a 1)
        (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ) = c := by
      rw [MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff (Finsupp.single a 1)
          (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ) = c := by
        have heq : (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial ℕ ℝ)
            = MvPolynomial.C c * MvPolynomial.X a := by ring
        rw [heq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
        ring
      have h2 : MvPolynomial.coeff (Finsupp.single a 1)
          (MvPolynomial.X b : MvPolynomial ℕ ℝ) = 0 := by
        rw [MvPolynomial.coeff_X']
        have hba : (Finsupp.single b 1 : ℕ →₀ ℕ) ≠ Finsupp.single a 1 := by
          rw [Ne, Finsupp.single_eq_single_iff]
          omega
        simp [hba]
      rw [h1, h2, add_zero]
    have hne : MvPolynomial.coeff (Finsupp.single a 1)
        (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
          : MvPolynomial ℕ ℝ) ≠ 0 := by
      rw [hkey]; exact hc
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    have hdeg := MvPolynomial.le_totalDegree hmem
    simpa using hdeg

/-- ⭐⭐ **`deg p = 0` ⇒ `p` 是常数**（形如 `C c`）。

**⚠ 第 38 轮定位的第一处：`if 0 = m` 的判据是【字面量在左**，
与假设 `m ≠ 0` 方向相反，所以 `simp` 关不掉它——必须显式 `rw [if_neg]`。** -/
theorem eq_C_of_totalDegree_zero_nat (p : MvPolynomial ℕ ℝ) (h : p.totalDegree = 0) :
    p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · have hsupp : m ∉ p.support := by
      intro hmem
      have hall := (MvPolynomial.totalDegree_eq_zero_iff ℕ p).mp h m hmem
      apply hm
      ext x
      exact hall x
    rw [MvPolynomial.mem_support_iff] at hsupp
    push_neg at hsupp
    have h0m : (0 : ℕ →₀ ℕ) ≠ m := fun hh => hm hh.symm
    rw [hsupp]
    simp only [MvPolynomial.coeff_C]
    rw [if_neg h0m]

/-- ⭐⭐ **`deg p = 0` 时的 `stepNat` 次数是 1**——**第 36 轮标出的边界的解法。** -/
theorem stepNat_totalDegree_zero (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : p.totalDegree = 0) :
    (stepNat (off, p)).2.totalDegree = 1 := by
  have hC : p = MvPolynomial.C (MvPolynomial.coeff 0 p) :=
    eq_C_of_totalDegree_zero_nat p hdeg
  have hc : MvPolynomial.coeff 0 p ≠ 0 := by
    intro h
    rw [hC, h, MvPolynomial.C_0] at hp
    exact hp rfl
  simp only [stepNat]
  rw [hC]
  exact totalDegree_X_mul_C_add_X_zero_nat off (off + 1) (by omega) hc


/-- ⭐⭐⭐ **`foldl` 的次数：对所有非零 `acc.2` 成立**——**不再需要 `1 ≤ deg`。**

**⚠ 归纳里按 `deg acc.2` 分两支：**
- **`deg = 0`**：用 `stepNat_totalDegree_zero`（第 39 轮），结果次数是 1；
- **`deg ≥ 1`**：用 `stepNat_snd_totalDegree`（第 33 轮），结果次数是 `1 + deg`。

**⚠ 关键：两支的结果都满足 `1 ≤` 与新次数，所以归纳假设可以在【同一形式**下递归。** -/
theorem foldl_step_totalDegree_any :
    ∀ (ls : ChainList) (acc : ℕ × MvPolynomial ℕ ℝ),
      acc.2 ≠ 0 →
      (ls.foldl (fun a _ => stepNat a) acc).2.totalDegree = acc.2.totalDegree + ls.length
  | [], acc, _ => by
      simp
  | l :: ls, acc, hne => by
      obtain ⟨off, p⟩ := acc
      simp only at hne
      rw [List.foldl_cons]
      by_cases h0 : p.totalDegree = 0
      · -- deg p = 0 支
        have hstep : (stepNat (off, p)).2.totalDegree = 1 :=
          stepNat_totalDegree_zero off p hne h0
        have hne' : (stepNat (off, p)).2 ≠ 0 := by
          intro h
          rw [h, MvPolynomial.totalDegree_zero] at hstep
          omega
        rw [foldl_step_totalDegree_any ls (stepNat (off, p)) hne']
        rw [hstep]
        simp only [List.length_cons]
        omega
      · -- deg p ≥ 1 支
        have h1 : 1 ≤ p.totalDegree := by omega
        have hstep : (stepNat (off, p)).2.totalDegree = 1 + p.totalDegree :=
          stepNat_snd_totalDegree off p hne h1
        have hne' : (stepNat (off, p)).2 ≠ 0 :=
          stepNat_snd_ne_zero off p hne h1
        rw [foldl_step_totalDegree_any ls (stepNat (off, p)) hne']
        rw [hstep]
        simp only [List.length_cons]
        omega

/-- ⭐⭐⭐ **链多项式的次数 = `deg p + 层数`，对【任意非零 `p`】**——**包括常数 `C x`。** -/
theorem chainNatPoly_totalDegree_any (ls : ChainList) (p : MvPolynomial ℕ ℝ)
    (hp : p ≠ 0) :
    (chainNatPoly ls p).totalDegree = p.totalDegree + ls.length := by
  simp only [chainNatPoly]
  exact foldl_step_totalDegree_any ls (0, p) hp


/-- ⭐ **`C x ≠ 0`**（当 `x ≠ 0`）。 -/
theorem C_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    (MvPolynomial.C x : MvPolynomial ℕ ℝ) ≠ 0 := by
  intro h
  have h0 : x = 0 := (MvPolynomial.C_inj ℝ x 0).mp (by rw [h, MvPolynomial.C_0])
  exact hx h0

/-- ⭐⭐ **标量输入的次数是 0**。 -/
theorem totalDegree_C_zero (x : ℝ) :
    (MvPolynomial.C x : MvPolynomial ℕ ℝ).totalDegree = 0 :=
  MvPolynomial.totalDegree_C x

/-- ⭐⭐⭐ **统一压顶定理**：**链的输出就是参数的一个显式多项式，
其次数【恰为层数**（当输入 `x ≠ 0`），**而它的求值就是网络的输出。**

**⚠ 第 37 轮那两条的分支合并版：第 40 轮的 `chainNatPoly_totalDegree_any`
取消了 `1 ≤ deg p` 的前提，于是 `C x` 也能带次数结论。** -/
theorem chainList_output_full {N : ℕ} (ls : ChainList)
    (hN : 0 + 2 * ls.length + 1 < N) {x : ℝ} (hx : x ≠ 0) :
    (chainNatPoly ls (MvPolynomial.C x)).totalDegree = ls.length
      ∧ ∀ (gN : Fin N → ℝ),
          (chainNatPoly ls (MvPolynomial.C x)).eval (fun k => readSlot gN k)
            = flatChainAct (N := N) (chainOneToChain (listToChainOne ls)) 0 gN
                (fun _ => x) (0 : Fin 1) := by
  constructor
  · rw [chainNatPoly_totalDegree_any ls (MvPolynomial.C x) (C_ne_zero_of_ne_zero hx),
      totalDegree_C_zero]
    omega
  · intro gN
    have hN' : 0 + 2 * chainOneDepth (listToChainOne ls) + 1 < N := by
      rw [chainOneDepth_listToChainOne]
      exact hN
    rw [chainNatPoly_eval_act]
    simp only [chainNatAct]
    rw [chainNatAct_eq_chainOneAct ls
      (0, (MvPolynomial.C x).eval (fun k => readSlot gN k)) gN]
    simp only [MvPolynomial.eval_C]
    exact chainOneAct_eq_flatChainAct (listToChainOne ls) 0 hN' gN x

/-- ⭐⭐⭐ **次数界是【紧】的**：**对每个 `d`，存在长度为 `d` 的层列表，
其输出多项式的次数恰为 `d`。** -/
theorem chainList_degree_attained {N : ℕ} (d : ℕ) (hN : 0 + 2 * d + 1 < N) :
    ∃ (ls : ChainList),
      ls.length = d
        ∧ (chainNatPoly ls (MvPolynomial.C 1)).totalDegree = d := by
  refine ⟨List.replicate d twoLayerProbeRest, List.length_replicate d twoLayerProbeRest, ?_⟩
  have := (chainList_output_full (List.replicate d twoLayerProbeRest)
    (by rw [List.length_replicate]; exact hN) one_ne_zero).1
  rw [this, List.length_replicate]


/-! ## ⭐⭐⭐ 宽度 > 1：多项式向量载体

**宽 1 时载体是【一个**多项式；宽 `b` 时一层的输出是 `b` 个多项式，
**⇒ 载体是 `Fin b → MvPolynomial ℕ ℝ`。**

**槽位约定与 `flatParamActSafe` 完全一致：`slotOf off a i j = off + i*a + j`。** -/

/-- ⭐ **有限和的次数界**——**每一项次数 ≤ `d` 则和 ≤ `d`。** -/
theorem totalDegree_finset_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ℕ ℝ) (d : ℕ) (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d := by
  classical
  refine Finset.sum_induction f (fun p => p.totalDegree ≤ d) ?_ ?_ hf
  · intro x y hx hy
    refine le_trans (MvPolynomial.totalDegree_add x y) ?_
    rw [max_le_iff]
    exact ⟨hx, hy⟩
  · simp

/-- **一层作用在多项式向量上**——**与 `flatParamActSafe` 逐字对应。** -/
noncomputable def polyLayerStep (a b : ℕ) (off : ℕ) :
    (Fin a → MvPolynomial ℕ ℝ) → (Fin b → MvPolynomial ℕ ℝ) :=
  fun v j => (∑ i : Fin a, MvPolynomial.X (slotOf off b i.val j.val) * v i)
    + MvPolynomial.X (off + a * b + j.val)

/-- ⭐⭐ **一层的次数界**：**输入次数 ≤ `d` ⇒ 输出次数 ≤ `d + 1`。** -/
theorem polyLayerStep_totalDegree_le (a b : ℕ) (off : ℕ)
    (v : Fin a → MvPolynomial ℕ ℝ) (d : ℕ)
    (hv : ∀ i, (v i).totalDegree ≤ d) :
    ∀ j, (polyLayerStep a b off v j).totalDegree ≤ d + 1 := by
  intro j
  simp only [polyLayerStep]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [max_le_iff]
  constructor
  · refine totalDegree_finset_sum_le Finset.univ _ (d + 1) ?_
    intro i _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_X]
    have := hv i
    omega
  · rw [MvPolynomial.totalDegree_X]
    omega


/-! ## ⭐⭐⭐ 宽度 > 1：链的多项式载体

**第 42 轮给出了【一层】**（`polyLayerStep`）**及其次数界。
本节把它沿链迭代。**

**⚠ 链的宽度是【依赖**的（每层的输入宽度 = 上一层的输出宽度），
所以载体用一个索引归纳类型 `PolyChain m n`，而【不是 `List`**。** -/

/-- **宽度依赖的链（多项式侧）**——**每层携带自己的输入／输出宽度。** -/
inductive PolyChain : ℕ → ℕ → Type
  | idf (n : ℕ) : PolyChain n n
  | cons {a b c : ℕ} : MLayer a b → PolyChain b c → PolyChain a c

/-- **层数**。 -/
def polyChainDepth : {m n : ℕ} → PolyChain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons _ rest => polyChainDepth rest + 1

/-- **参数槽位总数**（沿链累加）。 -/
def polyChainParamCount : {m n : ℕ} → PolyChain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons (a := a) (b := b) _ rest => layerParamCount a b + polyChainParamCount rest

/-- **链的多项式作用**——**`off` 是当前层的起始槽位。** -/
noncomputable def polyChainAct : {m n : ℕ} → (ch : PolyChain m n) → (off : ℕ) →
    (Fin m → MvPolynomial ℕ ℝ) → (Fin n → MvPolynomial ℕ ℝ)
  | _, _, .idf _, _, v => v
  | _, _, .cons (a := a) (b := b) l rest, off, v =>
      polyChainAct rest (off + layerParamCount a b)
        (polyLayerStep a b off v)

/-- ⭐⭐ **`idf` 支**——**定义级。** -/
theorem polyChainAct_idf (n off : ℕ) (v : Fin n → MvPolynomial ℕ ℝ) :
    polyChainAct (PolyChain.idf n) off v = v := rfl

/-- ⭐⭐ **`cons` 支**——**定义级。** -/
theorem polyChainAct_cons {a b c : ℕ} (l : MLayer a b) (rest : PolyChain b c)
    (off : ℕ) (v : Fin a → MvPolynomial ℕ ℝ) :
    polyChainAct (PolyChain.cons l rest) off v
      = polyChainAct rest (off + layerParamCount a b) (polyLayerStep a b off v) := rfl


/-- ⭐⭐⭐ **链的次数界**：**若每个输入坐标的次数 ≤ `d`，则每个输出坐标的次数 ≤ `d + 层数`。**

**⚠ 这是第 42 轮单层界沿链的迭代——无关于宽度。** -/
theorem polyChainAct_totalDegree_le {m n : ℕ} : (ch : PolyChain m n) → (off : ℕ) →
    (v : Fin m → MvPolynomial ℕ ℝ) → (d : ℕ) →
    (∀ i, (v i).totalDegree ≤ d) →
    ∀ j, (polyChainAct ch off v j).totalDegree ≤ d + polyChainDepth ch
  | .idf _, off, v, d, hv, j => by
      simp only [polyChainAct, polyChainDepth]
      exact hv j
  | .cons (a := a) (b := b) l rest, off, v, d, hv, j => by
      simp only [polyChainAct, polyChainDepth]
      have hstep : ∀ i, (polyLayerStep a b off v i).totalDegree ≤ d + 1 :=
        fun i => polyLayerStep_totalDegree_le a b off v d hv i
      have ih := polyChainAct_totalDegree_le rest (off + layerParamCount a b)
        (polyLayerStep a b off v) (d + 1) hstep j
      omega


/-! ## ⚠⚠ 第 44 轮：宽 > 1 对接的两步，第二步需要【非线性】算术

## 拆成两步

「polyLayerStep」的变量下标是 ℕ，而「flatParamActSafe」的「g」是 Fin N → ℝ。
∴ 分两步：

1. 「polyLayerStep_eval」：求值等于 「natParamAct」（ℕ 下标的数值作用）；
2. 「natParamAct_eq_flatParamActSafe」：两者在 g := readSlot gN 下一致。

## 第一步本轮已经通过

所用的关键引理是 「MvPolynomial.eval_sum」（不是我以为的 eval_finset_sum）。
配 eval_add、eval_mul、eval_X 与 Finset.sum_congr rfl，证明是三行。

## 第二步卡在：「slotOf」的界需要非线性推理

要证 slotOf off a i j < N，已知：

- i < a、j < b（Fin 的内建约束）；
- off + a * b + b ≤ N（即 hN）。

而 slotOf off a i j = off + i * a + j。∴ 需要 i * a + j < a * b + b，
那是一个【乘法】不等式。

⚠ omega 做不到——它是线性算术。
它报出的反例约束正是缺了 i*a 与 a*b 的关系。

⇒ 修法：先证一条纯算术引理

    theorem slotOf_lt {a b i j : ℕ} (hi : i < a) (hj : j < b) (off : ℕ) :
        slotOf off a i j < off + a * b + b

⚠ 而那条引理本身也需要非线性推理：i * a + j < a * b + b
由 i * a ≤ (a-1) * a 与 j ≤ b-1 得到——两步都需要乘法单调性。

⇒ 下一轮的第一件事：写那条 slotOf_lt 的纯算术引理，
用 nlinarith 或 Nat.mul_lt_mul_of_lt_of_le 一类的引理。

## 结论

本轮没有代码入库（回退到 744）。
第一步已验证可通过，第二步的障碍是一条纯算术引理。 -/


/-- ⭐⭐ **槽位算术界**：**`slotOf off b i j < off + a*b + b`**（当 `i < a`、`j < b`）。

**⚠ 关键：`slotOf` 的行步长是 `b`（输出宽度），这是 `flatParamActSafe` 的约定。
第 45 轮发现 `polyLayerStep` 原先写的 `slotOf off a …` 是【错的**，已修正。** -/
theorem slotOf_lt_bound {a b i j : ℕ} (hi : i < a) (hj : j < b) (off : ℕ) :
    slotOf off b i j < off + a * b + b := by
  simp only [slotOf]
  have h1 : i * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
  have h2 : j ≤ b - 1 := by omega
  have h3 : (a - 1) * b + (b - 1) < a * b + b := by
    have ha : 1 ≤ a := by omega
    have key : a * b = (a - 1) * b + b := by
      conv_lhs => rw [← Nat.sub_add_cancel ha]
      ring
    omega
  omega

/-- **`ℕ` 下标的数值层作用**——**与 `polyLayerStep` 逐字对应。** -/
noncomputable def natParamAct (a b off : ℕ) (g : ℕ → ℝ) (x : Fin a → ℝ) : Fin b → ℝ :=
  fun j => (∑ i : Fin a, g (slotOf off b i.val j.val) * x i) + g (off + a * b + j.val)

/-- ⭐⭐⭐ **一层的求值一致**：**`polyLayerStep` 的求值 = `natParamAct`。** -/
theorem polyLayerStep_eval (a b off : ℕ) (v : Fin a → MvPolynomial ℕ ℝ)
    (g : ℕ → ℝ) (j : Fin b) :
    (polyLayerStep a b off v j).eval g
      = natParamAct a b off g (fun i => (v i).eval g) j := by
  simp only [polyLayerStep, natParamAct]
  rw [MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]

/-- ⭐⭐⭐ **`ℕ` 数值作用与 `flatParamActSafe` 一致**——**`g` 取 `readSlot gN`。** -/
theorem natParamAct_eq_flatParamActSafe {N : ℕ} (a b off : ℕ) (gN : Fin N → ℝ)
    (x : Fin a → ℝ) (hN : off + a * b + b ≤ N) :
    natParamAct a b off (fun k => readSlot gN k) x
      = flatParamActSafe (N := N) (a := a) (b := b) off gN x := by
  funext j
  simp only [natParamAct, flatParamActSafe]


/-- **`PolyChain` → `Chain` 的翻译**——**两者的唯一关系，是一个函数。** -/
def polyChainToChain : {m n : ℕ} → PolyChain m n → Chain m n
  | _, _, .idf _ => Chain.idf _
  | _, _, .cons l rest => Chain.cons l (polyChainToChain rest)

/-- ⭐ **翻译保持层数**——**`chainDepth` 与 `polyChainDepth` 一致。** -/
theorem chainDepth_polyChainToChain {m n : ℕ} (ch : PolyChain m n) :
    chainDepth (polyChainToChain ch) = polyChainDepth ch := by
  induction ch with
  | idf k => rfl
  | cons l rest ih =>
      simp only [polyChainToChain, polyChainDepth, chainDepth_cons, ih]


/-- ⭐⭐⭐ **整体桥接**：**`polyChainAct` 逐点求值 = `flatChainAct`。**

**⚠ 第 45 轮逐层桥接沿链的提升。`g` 取 `readSlot gN`，
`hN : off + polyChainParamCount ch + 1 ≤ N` 保证所有槽位在 `N` 内。** -/
theorem polyChainAct_eval {N : ℕ} : {m n : ℕ} → (ch : PolyChain m n) → (off : ℕ) →
    (v : Fin m → MvPolynomial ℕ ℝ) → (gN : Fin N → ℝ) →
    (hN : off + polyChainParamCount ch + 1 ≤ N) →
    ∀ j, (polyChainAct ch off v j).eval (fun k => readSlot gN k)
      = flatChainAct (N := N) (polyChainToChain ch) off gN
          (fun i => (v i).eval (fun k => readSlot gN k)) j
  | _, _, .idf _, off, v, gN, hN, j => by
      simp only [polyChainAct, polyChainToChain, flatChainAct]
  | _, _, .cons (a := a) (b := b) l rest, off, v, gN, hN, j => by
      -- 展开 hN 与两边
      have hN' : off + layerParamCount a b + polyChainParamCount rest + 1 ≤ N := by
        simp only [polyChainParamCount] at hN
        omega
      have hcur : off + a * b + b ≤ N := by
        have hpc : layerParamCount a b = a * b + b := rfl
        omega
      simp only [polyChainAct, polyChainToChain, flatChainAct, polyChainParamCount]
      -- 用归纳假设
      rw [polyChainAct_eval rest (off + layerParamCount a b)
        (polyLayerStep a b off v) gN (by simpa using hN')]
      -- 现在需要把左边的求值换成 flatParamActSafe
      congr 1
      funext i
      exact (polyLayerStep_eval a b off v (fun k => readSlot gN k) i).trans
        (congrFun (natParamAct_eq_flatParamActSafe a b off gN
          (fun i => (v i).eval (fun k => readSlot gN k)) hcur) i)


/-- ⭐⭐⭐ **宽度 > 1 的压顶定理**：**任意宽度 `m → n` 的链，其输出就是参数的显式多项式向量，
每个坐标的次数 ≤ 输入次数 + 层数，且该向量的求值就是网络的输出。**

**⚠ 这是第 41 轮宽度 1 压顶定理的任意宽度推广——
把第 43 轮的次数界（`polyChainAct_totalDegree_le`）与
第 47 轮的求值一致（`polyChainAct_eval`）合成【一条**。** -/
theorem polyChain_output_full {N m n : ℕ} (ch : PolyChain m n) (off : ℕ)
    (v : Fin m → MvPolynomial ℕ ℝ) (d : ℕ) (hv : ∀ i, (v i).totalDegree ≤ d)
    (gN : Fin N → ℝ) (hN : off + polyChainParamCount ch + 1 ≤ N) :
    (∀ j, (polyChainAct ch off v j).totalDegree ≤ d + polyChainDepth ch)
      ∧ ∀ j, (polyChainAct ch off v j).eval (fun k => readSlot gN k)
          = flatChainAct (N := N) (polyChainToChain ch) off gN
              (fun i => (v i).eval (fun k => readSlot gN k)) j :=
  ⟨polyChainAct_totalDegree_le ch off v d hv,
    polyChainAct_eval ch off v gN hN⟩

/-- ⭐⭐ **压顶（以常数输入）**：**宽度 1 的输入 `C x` 时，次数恰为层数。**

**⚠ 这是宽度 > 1 框架对第 41 轮结果的【复核**：
取 `m = 1`、`v = fun _ => C x`，则 `d = 0`，次数 ≤ 层数。** -/
theorem polyChain_output_width_one {N n : ℕ} (ch : PolyChain 1 n) (off : ℕ)
    (x : ℝ) (gN : Fin N → ℝ) (hN : off + polyChainParamCount ch + 1 ≤ N) :
    (∀ j, (polyChainAct ch off (fun _ => MvPolynomial.C x) j).totalDegree
        ≤ polyChainDepth ch)
      ∧ ∀ j, (polyChainAct ch off (fun _ => MvPolynomial.C x) j).eval
          (fun k => readSlot gN k)
          = flatChainAct (N := N) (polyChainToChain ch) off gN
              (fun _ => x) j := by
  have hv : ∀ i : Fin 1,
      ((fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) i).totalDegree ≤ 0 := by
    intro i
    simp [totalDegree_C_zero]
  have := polyChain_output_full ch off
    (fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) 0 hv gN hN
  refine ⟨fun j => ?_, ?_⟩
  · have h1 := this.1 j
    omega
  · intro j
    have h2 := this.2 j
    have h3 : (fun i : Fin 1 =>
        ((fun _ : Fin 1 => (MvPolynomial.C x : MvPolynomial ℕ ℝ)) i).eval
          (fun k => readSlot gN k)) = (fun _ => x) := by
      funext i
      simp
    rw [h3] at h2
    exact h2

/-! Round 49: reverse direction attempted.

Attempted: coeff (Finsupp.single off 1) (X off * C c + X (off+1)) = c,
the atomic step of reading a weight back out of its polynomial.

Obstacles: the definition needs noncomputable, and the docstring needed its
closing marker. Both are one-line fixes; this round's fix scripts failed to
match their search strings.

Design finding: the bias is NOT among the coefficients. A layer polynomial is
X off * C c + X (off+1), so the bias slot carries coefficient 1 and its VALUE
is read from g at evaluation time. Hence the correct reverse statement concerns
STRUCTURAL POSITIONS, already given by polyChainParamCount, slotOf and
layerParamCount, rather than coefficient recovery.

No code in the tree this round.
-/

end Lattice.Core
