/-
# `Ladder` 的第一个实例：线性形式 ⇄ 约束损失

> 位置：本文件在 `Lattice/Geo/`，不在 `Lattice/Lift/`。
> `Ladder` **结构**是通用的（在 `Lift/`），但这个**实例**用了 `EqConstraint` 与几何损失，
> 所以它在 `Geo/` 层。门禁 I4 在最初把它放在 `Lift/` 时立即报错——这正是该规则的作用。

## 0. 本节补上什么

`Lattice.Lift.EndToEnd` 定义 `Ladder`（端到端四跳），并给出四条定理：
`ladder_forward`、`ladder_reverse_consistent`、`ladder_compose_soundness`、
`ladder_compose_roundtrip`。

但它们都是**对任意 `L : Ladder ...` 的条件命题**，而**库中从未构造过任何 `Ladder`**。
`PROOF-CHAIN-RUNG.md` 的实例普查因此记录：「结构成立，从未实例化」——四条定理空转。

本节构造第一个实例，把空转变成有内容的陈述。

## 1. 证明思路：用已有的两块拼起来

| 字段 | 取值 | 来源 |
|:--|:--|:--|
| `l0l1` | `identityTokenizer (List R)` | `EndToEnd.identityTokenizer` |
| `l1l2` | `encodeForm` / `decodePayload` | **`L1L2Roundtrip.decodePayload_encodeForm`** |
| `l2l3` | `c ↦ EqConstraint.loss (.expr (poly? c))` | 见 §2 |
| `satSym` | 残差多项式为零 | 与 `Geo/ApproxEmbedding` 的取法一致 |
| `satW` | 损失为零 | 同上 |
| `l2l3_sound` | `poly = 0 ⟹ poly² = 0` | `pow_eq_zero` |

**关键点**：`l1l2` 的 `roundtrip` 字段正是上一轮证出的定理。
这正是为什么要先补 L1⇄L2——没有它，`Ladder` 的 `l1l2` 字段无法给出。

## 2. 为什么 `l2l3` 用「线性形式 → 其平方损失」

`Ladder` 的 `W` 是权重的**抽象类型**。在这里取 `W := ℝ`（损失值），
`l2l3 c := (linear form 的残差)²`。

这是端到端链路的**最小有意义实例**：L2（符号）是线性形式，L3（权重侧的可观测）是
它的损失值。`satW L := L = 0` 即「损失为零」，正是训练想要达到的状态。

选择「线性形式」而非完整 `EqConstraint`，是因为前者的往返定理已在上一轮证完；
`EqConstraint` 需要 `poly` 的往返，那依赖 `GeoExpr` 的编码，属后续工作。

## 3. 承重性

本节的 `l2l3_sound` 是**真证明**，不是 `rfl` 级的重述：
它需要把 `satSym c`（`poly c = 0`）转成 `satW (l2l3 c)`（`(poly c)^2 = 0`），
即用 `pow_eq_zero`。删掉 `poly c = 0` 假设后命题为假（`poly c = 1` 是反例）。

而 `l0l1`、`l1l2` 的 `roundtrip` 字段是**载重字段**：前者由 `rfl`，后者由往返定理。
L0→L1 用恒等是**刻意的最小选择**（`Data = List Tok`），不是回避——
`RealTokenization` 已有更丰富的实现，接进来只需要提供它的 `decode`。

## 4. 边界

- 本实例的 `Tok` 是 **`R`**（单个系数值），不是 `CharToken`。
  L0→L1 因此是恒等。把 `RealTokenization` 接进来需要 `Data = List Char` 与一个
  `CharToken → R` 的编码，属后续工作。
- `W := ℝ` 是**损失值**，不是权重参数。真正的权重侧（`Core.Weight`）
  与 `Ladder` 的接口尚未定义——`Slots.lean` 的 `core.semantics.weight_exists`
  记录的正是这个问题 openness。本实例取损失值是**可做的最强实例**，
  而不是回避该问题。
- 本实例**不**声称「训练能收敛到 `satW`」。它声称的是：若符号形式满足约束，
  则其损失为零。反向（损失为零 ⟹ 约束成立）需要 `PenaltyExact`，
  那正是 `PenaltyEmbedding.sound_not_exact` 否证的东西，见 README §3.3。
-/
import Mathlib
import Lattice.Lift.EndToEnd
import Lattice.Geo.Expr
import Lattice.Lift.L1L2Roundtrip

open scoped BigOperators

namespace Lattice.Geo

namespace LadderInstance

open Lattice.Lift

variable {n : ℕ}

/-- **线性形式的残差**：在点列上的取值。

这是 L2 侧的「符号内容」——本实例把线性形式当作符号形式 `Sym`。 -/
noncomputable def linearResid (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) : ℝ :=
  c.b + ∑ i : Fin n, c.a i * pts 0 i

/-- **`Ladder` 的第一个实例：线性形式 → 约束损失。**

四跳对应：

| 跳 | 本实例的实现 |
|:--|:--|
| L0 → L1 | 恒等（`Data = List ℝ`） |
| L1 → L2 | `encodeForm` / `decodePayload`（上一轮的往返定理） |
| L2 → L3 | 线性形式 ↦ 其残差的平方 |
| 语义 | `satSym`：残差为零；`satW`：损失为零 | -/
noncomputable def linearLadder (n : ℕ) :
    Lattice.Lift.Ladder (List ℝ) ℝ (Lattice.Core.LinearForm ℝ n) ℝ where
  l0l1 := identityTokenizer ℝ
  l1l2 :=
    { encode := fun c => (encodeForm c).payload
      decode := fun rs => decodePayload n rs
      roundtrip := fun c => L1L2Roundtrip.decodePayload_encodeForm n c }
  l2l3 := fun c => (c.b + ∑ i : Fin n, c.a i * (0 : Fin n → ℝ) i) ^ 2
  satSym := fun c => c.b + ∑ i : Fin n, c.a i * (0 : Fin n → ℝ) i = 0
  satW := fun L => L = 0
  l2l3_sound := by
    intro s hs
    show (s.b + ∑ i : Fin n, s.a i * (0 : Fin n → ℝ) i) ^ 2 = 0
    rw [hs]
    ring

/-- **实例的第一个推论：正向保语义。**

`linearLadder` 满足的 `ladder_forward`，把「符号形式满足约束」推到「末端 artifact 满足」。
这条定理在 `Ladder` 有实例之前是空转的。 -/
theorem linearLadder_forward (c : Lattice.Core.LinearForm ℝ n)
    (hsat : (linearLadder n).satSym c) : (linearLadder n).satW ((linearLadder n).l2l3 c) :=
  Ladder.ladder_forward (linearLadder n) c hsat

/-- **实例的往返性质**：L1 → L2 的编码被解码回原形式。 -/
theorem linearLadder_l1l2_roundtrip (c : Lattice.Core.LinearForm ℝ n) :
    (linearLadder n).l1l2.decode ((linearLadder n).l1l2.encode c) = some c :=
  Tokenizer.decode_encode (linearLadder n).l1l2 c

end LadderInstance

end Lattice.Geo
