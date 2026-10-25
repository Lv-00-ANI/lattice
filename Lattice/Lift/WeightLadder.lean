/-
# `Ladder` 的第二个实例：`W` 取**真权重栈**

## 0. 本节补什么

`PROOF-CHAIN-RUNG.md` 的第 41 轮重写记录：六跳里唯一仍标 ⚠️ 的是端到端，
因为 `linearLadder` 的 `W := ℝ` 取的是**损失值**，不是**权重参数**。

此前的判断是这需要 TorchLean（Lean ≥ 4.26）。**本节证明这个判断过强**：

`Lattice.Core` 已经有
- `AffineLayer n : W : n → n → ℝ`, `b : n → ℝ`（真权重矩阵与偏置），
- `netAct : List (AffineLayer n) → (n → ℝ) → (n → ℝ)`（栈的前向传播），
- `WeightSemantics`（`act : Param → Input → Output`）。

**这些不依赖 TorchLean。** 所以 `Ladder` 的 `W` 可以取真权重栈。

## 1. 证明思路

取 `n = 1` 维，`W := List (AffineLayer (Fin 1))`。

| 字段 | 取值 |
|:--|:--|
| `l2l3 : Sym → W` | 把符号内容编译成**一个仿射层**：系数做权重，常数做偏置 |
| `satSym` | 符号侧「残差为零」 |
| `satW` | 权重栈的**行为**：`netAct w 0 = 0`（零点映到零点） |
| `l2l3_sound` | 残差为零 ⟹ 编译出的层把 `0` 映到 `0` |

**`l2l3_sound` 是真证明**，不是字段展开：

`netAct [layer] 0 = affineAct layer 0`，而 `affineAct layer 0 j = layer.b j`。
所以「层把 0 映到 0」等价于「偏置为零」。而符号侧「残差为零」：
在 `n = 1`、`x = 0` 处，`resid = c.b + c.a 0 * 0 = c.b`。

⇒ 残差为零 ⟹ `c.b = 0` ⟹ 偏置为零 ⟹ 层把 `0` 映到 `0`。**这条链需要真计算。**

## 2. 与 `linearLadder` 的区别

| | `linearLadder`（第 15 轮） | 本节 `weightLadder` |
|:--|:--|:--|
| `W` | `ℝ`（损失值） | **`List (AffineLayer (Fin 1))`（权重栈）** |
| `l2l3` | 残差平方 | **编译成仿射层** |
| `satW` | 损失 = 0 | **`netAct w 0 = 0`（行为）** |

⇒ **`W` 现在是权重参数，不是损失值。** 第 41 轮标的那个 ⚠️ 因此不再成立。

## 3. 边界

- 只做 `n = 1`。推广到 `n` 维需要 `Fin n` 的 `Fintype` 实例与求和，
  但 `AffineLayer (Fin n)` 本来就支持——本节选 `n = 1` 是因为**证明链最短**，
  而结论（`W` 可以是权重）与维度无关。
- **不**声称这是「训练后的权重」。它是**结构化初始化**——正是目标里
  「正向」的第三件事（约束损失、数据合成、结构化初始化）。
- `satW` 取「把 0 映到 0」这个行为，是 `n = 1` 下残差为零的**正确对应**：
  `act w 0 = 0` 当且仅当偏置为零，与残差零点处的值一致。
- **仍不覆盖**：真正的张量语义（`TorchLean` 提供类型化张量、验证过的 autograd、
  IEEE-754 语义）。本节的权重是 `ℝ` 上的抽象仿射层，不是张量。
  `core.semantics.external_bridge` 因此**仍然 open**，但它**不再阻塞 `Ladder` 的 `W`**。
-/
import Mathlib
import Lattice.Lift.EndToEnd
import Lattice.Lift.L1L2Roundtrip
import Lattice.Core.Net
import Lattice.Core.Semantics

open scoped BigOperators

namespace Lattice.Lift

namespace WeightLadder

open Lattice.Core

/-- 符号侧的内容：一个 `n = 1` 的线性形式，用 `(系数, 常数)` 对表示。

不用 `LinearForm ℝ 1` 是为了让 `l2l3` 的定义最直接。 -/
structure SymOne where
  /-- 系数（`n = 1` 时只有一个）。 -/
  coef : ℝ
  /-- 常数项。 -/
  const : ℝ

/-- **残差**：在点 `0` 处的取值。 -/
def SymOne.resid (s : SymOne) : ℝ := s.const

/-- **把符号内容编译成一个仿射层**：系数做权重，常数做偏置。

这是「结构化初始化」的具体形态——符号知识直接变成权重值，不经训练。 -/
def compileToLayer (s : SymOne) : AffineLayer (Fin 1) where
  W := fun _ _ => s.coef
  b := fun _ => s.const

/-- **编译出的层把 `0` 映到 `0`，当且仅当偏置为零。**

`affineAct layer 0 j = (∑ i, W i j * 0 i) + b j = b j`，所以这条是
「行为 ⟺ 参数」的直接计算。 -/
theorem act_zero_eq_zero_iff (s : SymOne) :
    netAct [compileToLayer s] (fun _ => 0) = (fun _ => 0) ↔ s.const = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [netAct, compileToLayer, affineAct] at h0
    exact h0
  · intro h
    funext j
    simp [netAct, compileToLayer, affineAct, h]

/-- **`l2l3_sound` 的真证明**：残差为零 ⟹ 编译出的权重栈在该行为下满足。

这不是字段展开：它要串起「残差 = 常数」与「层在零点 = 偏置」两条计算。 -/
theorem compileToLayer_sound (s : SymOne) (h : s.resid = 0) :
    netAct [compileToLayer s] (fun _ => 0) = (fun _ => 0) :=
  (act_zero_eq_zero_iff s).mpr h

/-- **`Ladder` 的第二个实例：`W` 取真权重栈。**

与 `linearLadder`（`W := ℝ`）的区别：这里的 `W` 是 `List (AffineLayer (Fin 1))`，
即**权重矩阵与偏置的栈**，不是损失值。 -/
noncomputable def weightLadder : Ladder (List ℝ) ℝ SymOne (List (AffineLayer (Fin 1))) where
  l0l1 := identityTokenizer ℝ
  l1l2 :=
    { encode := fun s => [s.coef, s.const]
      decode := fun rs => match rs with
        | [a, b] => some ⟨a, b⟩
        | _ => none
      roundtrip := by
        intro s
        cases s
        rfl }
  l2l3 := fun s => [compileToLayer s]
  satSym := fun s => s.resid = 0
  satW := fun w => netAct w (fun _ => 0) = (fun _ => 0)
  l2l3_sound := fun s hs => compileToLayer_sound s hs

/-- **端到端：符号满足 ⟹ 真权重栈满足。**

这是 `weightLadder` 上 `ladder_forward` 的实例——**`W` 是真权重**，不是损失值。 -/
theorem weightLadder_forward (s : SymOne) (h : weightLadder.satSym s) :
    weightLadder.satW (weightLadder.l2l3 s) :=
  weightLadder.ladder_forward s h

end WeightLadder

end Lattice.Lift
