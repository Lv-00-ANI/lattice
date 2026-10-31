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
**那是一个定义层面的改动，第 162 轮做。** -/end Lattice.Core
