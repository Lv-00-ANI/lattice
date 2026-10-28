/-
# 三种逆向强度：一张图，以及为什么它是一张「源」而不是一条链

## 0. 本节补什么

库里有三种陈述「提取把编译反过来」的结构，强度递减：

| 结构 | 义务 | 文件 |
|:--|:--|:--|
| `Representation` | **等式** `extract (compile p) = p` | `Lift/Extraction` |
| `LossyRep` | **观察等价** `obs (extract (compile p)) p` | `Lift/LossyRepresentation` |
| `ApproxRepresentation` | **距离有界** `dist (extract (compile p)) p ≤ ε` | `Lift/ApproxExtraction` |

此前只有**两条边**被证明：

```
Representation ──ofRepresentation──▶ LossyRep        (obs := Eq)
       │
       └──exact_is_approx──▶ ApproxRepresentation     (ε := 0)
```

**本节补上第三条边，并且记录两条走不通的边为什么走不通。**

## 1. 为什么 `ApproxRepresentation → LossyRep` 需要前提

`LossyRep.obs_refl : ∀ p, obs p p`，而 `ApproxRepresentation.bounded` 只说
`dist (extract (compile p)) p ≤ ε`——**对 `dist p p` 一无所知**。

取 `obs p q := dist p q ≤ ε`，则 `obs_refl` 要求 `dist p p ≤ ε`，**这不是免费的**：
`dist` 是使用者提供的任意函数（`ApproxExtraction` 的注释已说明，与第 70 轮「三角不等式是假设」同一原则）。

**所以转换带一个前提 `hrefl`。这不是证明失败，是两个结构强度的真实差异被记录了下来。**

## 2. 完整图

| 从 \ 到 | `Representation` | `LossyRep` | `ApproxRepresentation` |
|:--|:--|:--|:--|
| `Representation` | — | `ofRepresentation` ✅ | `exact_is_approx` ✅ |
| `LossyRep` | ✗ | — | ✗ |
| `ApproxRepresentation` | `error_zero_is_exact`（ε=0 + 分离）✅ | **`ofApprox`（需 `hrefl`）✅** | — |

## 3. 两条「✗」是真的不可能，不是未做

- **`LossyRep → Representation`**：`obs` 比相等粗，**粗化不可逆**——
  `Extraction.semantic_not_injective` 已证。
- **`LossyRep → ApproxRepresentation`**：`obs` 是任意谓词，**不携带距离**，
  无法从中读出 `ε`。这是类型层面的事实：`obs : P → P → Prop` 与 `dist : P → P → ℝ` 不同构。

## 4. 结论：三种强度构成一个「源」

**精确蕴含另外两种，而另外两种互不蕴含。**

**这解释了第 159 轮的一个观察**：`ApproxRepresentation` 长期没有消费者，
**不是因为它该被某个更弱的结构取代，而是因为在实际使用中「有界」是一个终点**——
你从精确出发，选择一个松弛，然后停在那里。

**本节不改动任何既有结构，只补一条边与一张图。**
-/
import Mathlib
import Lattice.Runtime.Extraction
import Lattice.Lift.LossyRepresentation
import Lattice.Lift.ApproxExtraction

namespace Lattice.Lift

open Lattice.Lift.ApproxExtraction
open Lattice.Lift.LossyRepresentation

variable {P W : Type}

/-- **`ApproxRepresentation` 给出一个 `LossyRep`**，`obs` 取「距离不超过 `ε`」。

**前提 `hrefl : ∀ p, dist p p ≤ ε` 是 `LossyRep.obs_refl` 的要求**，不是可有可无的技术条件：
没有它，连「一个点与自身观察等价」都不成立。 -/
def ofApprox (A : ApproxRepresentation P W) (hrefl : ∀ p, A.dist p p ≤ A.ε) :
    LossyRep P W where
  -- `ApproxRepresentation` 没有输入空间字段，所以取最简：两侧输入空间都是符号空间
  inputP := P
  inputW := P
  encode := id
  decode := id
  compile := A.compile
  extract := A.extract
  obs := fun p q => A.dist p q ≤ A.ε
  obs_refl := hrefl
  semEq := fun p => A.bounded p

/-- **`ofApprox` 保留编译与提取**：转换只补上观察口径，不动两个方向。 -/
theorem ofApprox_compile (A : ApproxRepresentation P W) (hrefl : ∀ p, A.dist p p ≤ A.ε) (p : P) :
    (ofApprox A hrefl).compile p = A.compile p := rfl

/-- **`ofApprox` 保留提取**。 -/
theorem ofApprox_extract (A : ApproxRepresentation P W) (hrefl : ∀ p, A.dist p p ≤ A.ε) (w : W) :
    (ofApprox A hrefl).extract w = A.extract w := rfl

/-- **它的有损往返义务就是原来的有界往返**，逐字相同。

**这一条说明 `ofApprox` 没有偷偷加强或削弱义务**：`LossyRep.semEq` 在这个实例上
恰好是 `ApproxRepresentation.bounded`。 -/
theorem ofApprox_semEq (A : ApproxRepresentation P W) (hrefl : ∀ p, A.dist p p ≤ A.ε) (p : P) :
    (ofApprox A hrefl).obs ((ofApprox A hrefl).extract ((ofApprox A hrefl).compile p)) p :=
  A.bounded p

end Lattice.Lift
