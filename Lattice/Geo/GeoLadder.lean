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

### 1.2 正确做法：只声明跨层的那一跳

**本节的交付目标不是「造一条完整的四跳 Ladder」，而是「证明 Geo 层的类型可以占据 `Ladder` 的符号位」。**

因此 `l1l2` 用**恒等 tokenizer**（`EqConstraint` 直接当 token 看），
**这不回避问题，而是把「L1→L2 需要一个适配器」这件事显式记录下来**（见 §3）。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `compileConstraint` | 约束 ↦ 损失函数（`poly²`） |
| **`compileConstraint_sound`** | **`poly = 0 ⟹ 损失 ≤ 0`** |
| **`geoLadder`** | **符号侧是 `EqConstraint` 的 `Ladder`** |
| **`geoLadder_forward`** | **端到端：约束满足 ⟹ 损失为零** |
| **`ladder_crosses_geo_layer`** | **首个跨到 Geo 层的实例** |
| `l1l2_adapter_needed` | **未做的一步，显式记录** |

## 3. 边界（必须明说）

- **`l1l2` 用恒等 tokenizer**：`EqConstraint` 被当作 token 直接传递。
  **L1→L2 的真适配器未做**——既有往返定理是为 `LinearForm` 写的，几何约束需要新的适配器。
  **这是本节未完成的部分，`l1l2_adapter_needed` 记录它。**
- **`l2l3` 给出损失函数，不是仿射层**：`EqConstraint` 的损失依赖配置点，
  不属于 `AffineLayer`。**这是几何约束与仿射权重的真实差别。**
- 符号侧用 `EqConstraint`（规范化形式）而非 12 个 `GeoConstraint` 构造子。
- **不改**任何既有 `Ladder` 实例。
-/
import Mathlib
import Lattice.Lift.EndToEnd
import Lattice.Geo.Loss

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
| L0→L1 | 恒等（`Data = List (EqConstraint n)`） |
| L1→L2 | 恒等（见 §3 边界：真适配器未做） |
| **L2→L3** | **约束 ↦ 损失函数（本节）** |
| `satSym` | `poly c pts = 0`（符号侧：约束成立） |
| `satW` | `L pts ≤ 0`（权重侧：损失为零） |

**与既有实例的区别：符号侧第一次是 Geo 层的类型。** -/
noncomputable def geoLadder (pts : ℕ → Pt n) :
    Lattice.Lift.Ladder (List (EqConstraint n)) (EqConstraint n) (EqConstraint n)
      ((ℕ → Pt n) → ℝ) where
  l0l1 := Lattice.Lift.identityTokenizer (EqConstraint n)
  l1l2 :=
    { encode := fun c => [c]
      decode := fun ts => ts.head?
      roundtrip := fun _ => rfl }
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
    ∃ L : Lattice.Lift.Ladder (List (EqConstraint n)) (EqConstraint n) (EqConstraint n)
        ((ℕ → Pt n) → ℝ),
      ∀ c : EqConstraint n, L.satSym c → L.satW (L.l2l3 c) :=
  ⟨geoLadder pts, fun c h => Lattice.Lift.Ladder.ladder_forward (geoLadder pts) c h⟩

/-- **未做的一步，显式记录**：L1→L2 的真适配器。

`Lift/L1L2Roundtrip.lean` 的往返定理是为 `LinearForm ℝ n` 写的：

```
decodePayload : List ℝ → Option (LinearForm ℝ n)
```

**它的目标类型不是 `EqConstraint`**，所以几何约束无法直接使用那条往返。
要接上，需要一个 `EqConstraint ⇄ token 列表` 的 tokenizer 及其往返定理——
**那是独立工作，本节用恒等 tokenizer 占位并记录。** -/
theorem l1l2_adapter_needed : True := trivial

end GeoLadder

end Lattice.Geo
