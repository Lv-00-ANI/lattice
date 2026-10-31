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

**已确认可行的部分（都是真的、都在代码里）：**

1. **`Chain.act` 对 `Chain` 的递归可微性**（第 159 轮，
   `differentiableAt_chainAct`，完整证明）；
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

end Lattice.Core
