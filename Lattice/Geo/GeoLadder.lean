/-
# 把几何约束接到 `Ladder` 上：第一个跨到 Geo 层的实例

## 0. 本节补什么

第 108 轮盘点发现一个**结构性缺口**：

| `Ladder` 实例 | 符号侧是 Geo 类型吗 |
|:--|:--:|
| `weightLadder` | ❌ |
| `weightLadderN` | ❌ |
| `weightLadderNondeg` | ❌ |
| `linearLadder` | ❌（Core 的 `LinearForm`） |

**⇒ 没有任何 `Ladder` 实例的符号侧是 Geo 层的类型。**

**而目标说的链路是**：数据 → token → **符号模型（几何约束层）** → 权重。
**几何层是 L2，但 `Ladder` 的实例全部在 Core/Lift 内部打转。**

⇒ **端到端的演示从未真正穿过 Geo 层。**

## 1. 证明思路与两次修正

### 1.1 第一次尝试：用 `decodePayload` 做 L1→L2

**失败**：`decodePayload n : List ℝ → Option (LinearForm ℝ n)`——
它的目标是 `LinearForm`，**不是 `EqConstraint`**。两者类型不同，无法直接接。

**这是真实约束，不是实现细节**：L1⇄L2 的既有往返定理是**为线性形式写的**，
而几何约束不是线性形式。

### 1.2 正确做法：既跨层，也补上适配器

**第 108 轮**交付时只做了前半：证明 Geo 层的类型可以占据 `Ladder` 的符号位，
`l1l2` 用恒等 tokenizer 占位。

**第 144–150 轮**补上后半：`EqConstraint` 现在有真正的 tokenizer，`Tok := ℕ ⊕ ℝ`。

| 轮次 | 成果 |
|:--|:--|
| 144 | `SExpr ⇄ List ℕ`（结构精确往返） |
| 147 | `GeoExpr → List EqTok`（实数进入 token 流） |
| 148 | `decExpr_enc_nil`：表达式五构造子往返 |
| 149 | `decCon_enc_nil`：约束四构造子往返 |
| **150** | **`geoLadder` 的 `l1l2` 用上它** |

**根因值得记住**：`Ladder` 的 `Tok` 被 `l0l1` 与 `l1l2` 共享。当 `Tok = EqConstraint n` 时，
`l1l2 : Tokenizer (EqConstraint n) (EqConstraint n)` 的任何实例都只能是「换个包装再拿回来」——
**往返义务本身把内容压成了恒等**。换成 `EqTok` 才解开这个约束。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `compileConstraint` | 约束 ↦ 损失函数（`poly²`） |
| **`compileConstraint_sound`** | **`poly = 0 ⟹ 损失 ≤ 0`** |
| **`geoLadder`** | **符号侧是 `EqConstraint` 的 `Ladder`** |
| **`geoLadder_forward`** | **端到端：约束满足 ⟹ 损失为零** |
| **`ladder_crosses_geo_layer`** | **首个跨到 Geo 层的实例** |
| **`l1l2_is_real_tokenizer`** | **`l1l2` 的 `encode` 真的产出 token 列表** |

## 3. 边界（必须明说）

- **`Data = EqConstraint n`**：`Tok` 被两跳共享，所以把 `Tok` 从 `EqConstraint n` 换成
  `EqTok` 之后，`l0l1` 也必须是 `Tokenizer Data EqTok`。本节取 `Data = EqConstraint n`，
  **即一个数据项就是一个约束**，于是 `l0l1` 与 `l1l2` 是同一个映射。
  **多约束数据集尚未支持**：那需要 `Tokenizer (List (EqConstraint n)) EqTok`，
  其列表解码的 fuel 记账（每个约束自定界，但需要 fuel 单调性）是独立的一步。
- **`l2l3` 给出损失函数，不是仿射层**：`EqConstraint` 的损失依赖配置点，
  不属于 `AffineLayer`。**这是几何约束与仿射权重的真实差别。**
- 符号侧用 `EqConstraint`（规范化形式）而非 12 个 `GeoConstraint` 构造子。
- **不改**任何既有 `Ladder` 实例。
-/
import Mathlib
import Lattice.Runtime.EndToEnd
import Lattice.Geo.Loss
import Lattice.Geo.EqConstraintTokens
import Lattice.Geo.EqConstraintListTokens

open scoped BigOperators

namespace Lattice.Geo

namespace GeoLadder

variable {n : ℕ}

/-! ## 一、把 `EqConstraint` 编译成损失 -/

/-- **`EqConstraint` 的损失**：`poly²`。 -/
noncomputable def constraintLoss (c : EqConstraint n) (pts : ℕ → Pt n) : ℝ :=
  (EqConstraint.poly c pts) ^ 2

/-- **编译**：约束 ↦ 损失函数。 -/
noncomputable def compileConstraint (c : EqConstraint n) : (ℕ → Pt n) → ℝ :=
  fun pts => constraintLoss c pts

/-- **`l2l3_sound`**：约束成立 ⟹ 损失为零。

`poly = 0 ⟹ poly² = 0 ≤ 0`。**一行，因为 `EqConstraint` 有统一的 `poly`**——
这正是选择规范化形式而非 12 个构造子的理由。 -/
theorem compileConstraint_sound (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : EqConstraint.poly c pts = 0) :
    compileConstraint c pts ≤ 0 := by
  unfold compileConstraint constraintLoss
  rw [h]
  norm_num

/-! ## 二、跨到 Geo 层的 `Ladder` 实例 -/

/-- **符号侧是 `EqConstraint` 的 `Ladder`**。

| 跳 | 内容 |
|:--|:--|
| L0→L1 | 与 L1→L2 同一映射（`Data = EqConstraint n`，见 §3 边界） |
| **L1→L2** | **真 tokenizer：`encCon` / `decCon`（第 149 轮）** |
| **L2→L3** | **约束 ↦ 损失函数（本节）** |
| `satSym` | `poly c pts = 0`（符号侧：约束成立） |
| `satW` | `L pts ≤ 0`（**损失侧**：损失为零） |

### ⚠ 这个 `Ladder` 的 `W` 是**损失**，不是权重

`Lattice.Lift.Ladder` 对第四个参数 `W` 是**泛型**的，它的文档把这个位置称作
「a weight artifact」。本节把 `W` 取成 `((ℕ → Pt n) → ℝ)`——**一个损失函数**。

**类型上合法，语义上是范畴错误**：目标是「数据 ⇄ token ⇄ 符号模型 ⇄ **权重**」，
而损失不是权重。**所以 `geoLadder` 是一条「损失侧」的 `Ladder`，不是权重侧的。**

**为什么它不能改成真正的权重**：`EqConstraint` 的 `poly` 是**多项式**，
它的零点集一般不是仿射子空间。本库已经有定理 `Geo/WeightSideLadder.lean` 的
`no_affine_represents_sphere`：`d > 0` 时**不存在**仿射层以球面为零集。
**所以多项式约束在一般情形下没有仿射权重表示**——这不是没做，是分类的结果
（见 `Geo/WeightSideLadder.lean` §六 对 12 个构造子的划分）。

**真正走到权重的实例只有两个**：`samePoint`（`Geo/WeightSideLadder.lean`）与
`midpoint`（同文件 §六）。**它们在 `l2l3` 里产出 `List (AffineLayer (Fin n))`。**

⇒ **读本文件时不要把 `satW` 读成「权重接受」；它是「损失为零」。**
这个区别在本库是承重的：`satW` 一旦被读成权重侧，`geoLadder_forward` 就成了
「约束成立 ⟹ 权重正确」的假声称，而它实际说的是「约束成立 ⟹ 损失为零」。

**L1→L2 不再是恒等**：第 108 轮的占位实现已被第 144–153 轮的工作替换。
`Tok := EqTok := ℕ ⊕ ℝ` 让实数进入 token 流，`decCon_enc_nil` 提供单约束往返，
**`decList_enc`（第 153 轮）提供多约束列表往返**。

**四跳现在是四种不同的载体**：数据集 → token 流 → 符号约束 → 损失函数。
`l0l1` 与 `l1l2` **不再相同**——前者编列表，后者编单个约束。

**与既有实例的区别：符号侧第一次是 Geo 层的类型。** -/
noncomputable def geoLadder (pts : ℕ → Pt n) :
    Lattice.Lift.Ladder (List (EqConstraint n)) Lattice.Geo.EqTok.EqTok (EqConstraint n)
      ((ℕ → Pt n) → ℝ) where
  l0l1 := Lattice.Geo.EqConstraintListTokens.eqConstraintListTokenizer
  l1l2 := Lattice.Geo.EqConstraintTokens.eqConstraintTokenizer
  l2l3 := compileConstraint
  satSym := fun c => EqConstraint.poly c pts = 0
  satW := fun L => L pts ≤ 0
  l2l3_sound := by
    intro c hc
    exact compileConstraint_sound c pts hc

/-! ## 三、端到端 -/

/-- **端到端**：约束在 `pts` 处成立 ⟹ 编译出的损失在 `pts` 处为零。

**这是本节真正交付的东西**：`Ladder` 的端到端定理第一次以 **Geo 层的类型**为符号侧运行。 -/
theorem geoLadder_forward (pts : ℕ → Pt n) (c : EqConstraint n)
    (h : (geoLadder pts).satSym c) :
    (geoLadder pts).satW ((geoLadder pts).l2l3 c) :=
  Lattice.Lift.Ladder.ladder_forward (geoLadder pts) c h

/-- **首个跨到 Geo 层的实例**：存在一个 `Ladder`，其符号侧是 `EqConstraint`。 -/
theorem ladder_crosses_geo_layer (pts : ℕ → Pt n) :
    ∃ L : Lattice.Lift.Ladder (List (EqConstraint n)) Lattice.Geo.EqTok.EqTok (EqConstraint n)
        ((ℕ → Pt n) → ℝ),
      ∀ c : EqConstraint n, L.satSym c → L.satW (L.l2l3 c) :=
  ⟨geoLadder pts, fun c h => Lattice.Lift.Ladder.ladder_forward (geoLadder pts) c h⟩

/-- **L1→L2 的真适配器已经接上**：`geoLadder` 的 `l1l2` 编码一个约束到 `EqTok` 流并往返。

第 108 轮此处记录的是「恒等 tokenizer 占位」；第 144–150 轮的六轮工作把它换成了真的编码器：

| 轮次 | 成果 |
|:--|:--|
| 144 | `SExpr ⇄ List ℕ` |
| 147 | `GeoExpr → List EqTok` |
| 148 | `decExpr_enc_nil`：表达式五构造子往返 |
| 149 | `decCon_enc_nil`：约束四构造子往返 |
| **150** | **本 `Ladder` 的 `l1l2` 用上它** |

**这条定理不是重言式**：它把 `l1l2` 的 `encode` 展开成具体的 token 列表。 -/
theorem l1l2_is_real_tokenizer (pts : ℕ → Pt n) :
    (geoLadder pts).l1l2.encode (.samePoint 3 4) =
      [Sum.inl Lattice.Geo.EqConstraintToken.cSamePoint, Sum.inl 3, Sum.inl 4] := rfl

end GeoLadder

end Lattice.Geo
