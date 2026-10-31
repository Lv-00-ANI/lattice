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

end Lattice.Core
