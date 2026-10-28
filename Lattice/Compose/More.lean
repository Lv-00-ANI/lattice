/-
# `Compose/More` —— `parallel` 与 `choice`

## 0. 两处契约缺口，本节都写成了显式假设

`DIRECTORY-DESIGN.md` §6 给的签名是

```lean
def parallel (f g : Primitive) : Primitive
def choice   (f g : Primitive) : Primitive
```

### 缺口一：`choice` 无法按 `f.pre` 派发

第一版写成 `if h : f.pre x then f.run x else g.run x`。**这不可类型化**：`f.pre x` 是一个任意 `Prop`，
Lean 需要 `Decidable (f.pre x)` 才能 `if`，而 `Primitive` 契约**不提供**它
（`pre : Input → Prop`，没有可判定性字段）。实测会报 `failed to synthesize Decidable (f.pre x)`。

**所以 `choice` 的派发必须由调用方给出**——一个 `Bool` 谓词 `sel`。
**这与 §2.2「组合是用户的事」完全一致**：库不替你决定走哪一支。

### 缺口二：`choice` 需要两个分支有同一个 `pre`

若 `f.pre` 与 `g.pre` 不同，则「选 `g`」时 `f.sound` 用不上，而 `g.sound` 需要 `g.pre`——
而 `pre` 只能写一个。**所以 `choice` 要求 `f.pre ↔ g.pre`**，作为显式假设 `hpre`。

**这两条都不是削弱**：它们把「`choice` 到底需要什么」写出来了，而原设计把它们藏在了没有的字段里。

## 1. 交付

| 声明 | 内容 |
|:--|:--|
| **`parallel`** | 两者各跑一次，输入输出成对 |
| `parallel_sound` / `parallel_strength` / `parallel_coverage` | 定律 |
| **`choice`** | **派发由 `sel : Input → Bool` 决定**，要求 `hpre : f.pre ↔ g.pre`、`hio : f.Output = g.Output` |
| `choice_sound` | 两支都 sound ⟹ `choice` sound |

## 2. 强度与覆盖

- `parallel`：强度 **min**（两者都成功才叫成功），覆盖 **交**。
- `choice`：强度 **min**，覆盖 **并**——任一支能处理就算能处理。**这是唯一一处覆盖取并**，
  理由：`choice` 把两支的覆盖面加起来，而 `compose`/`parallel` 要求**都**适用。

## 3. 边界

- **不做 `optional`**：它可以由 `choice` + `identity` 导出，而单独写会重复一遍上面两个缺口
  （「还是跳过」同样要 `pre` 与可判定性）。**导出而非复制。**
- **不做 `iterate`**：需要终止测度 + 循环不变式，§6 只给一行。
  **没有测度的「循环」在 Lean 里不终止**，写成一行实现必然是错的。下一轮单独做。
- **不做 `Registry`/`Matrix`**：组合子未齐时登记的是不完整集合。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

/-! ## 一、并行 -/

/-- **并行**：两个 primitive 各跑一次，输入与输出都成对。

强度取 `min`（**两个都成功才叫成功**），覆盖取交（两个都适用的情形才适用）。 -/
def parallel (f g : Primitive) : Primitive where
  Input := f.Input × g.Input
  Output := f.Output × g.Output
  pre := fun p => f.pre p.1 ∧ g.pre p.2
  post := fun p q => f.post p.1 q.1 ∧ g.post p.2 q.2
  run := fun p => (f.run p.1).bind (fun y => (g.run p.2).map (fun z => (y, z)))
  sound := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := f.sound p.1 hp.1
    obtain ⟨z, hz, hpz⟩ := g.sound p.2 hp.2
    exact ⟨(y, z), by simp only [Option.bind, hy, hz, Option.map], hpy, hpz⟩
  strength := f.strength.min g.strength
  coverage := f.coverage.inter g.coverage
  frame := fun p q => f.frame p.1 q.1 ∧ g.frame p.2 q.2

/-- **并行保持正确性。** -/
theorem parallel_sound (f g : Primitive) (p : f.Input × g.Input)
    (hp : f.pre p.1 ∧ g.pre p.2) :
    ∃ q, (parallel f g).run p = some q ∧ (parallel f g).post p q :=
  (parallel f g).sound p hp

/-- **并行的强度取最小。** -/
theorem parallel_strength (f g : Primitive) :
    (parallel f g).strength = f.strength.min g.strength := rfl

/-- **并行的覆盖取交。** -/
theorem parallel_coverage (f g : Primitive) :
    (parallel f g).coverage = f.coverage.inter g.coverage := rfl

/-! ## 二、二选一（派发由调用方给出） -/

/-! ## 二、`choice`：**本轮未完成，阻塞点是 `Eq` cast 管道，不是数学**

### 设计已定，两处契约缺口已查明

**缺口一（已证）**：`choice` 不能按 `f.pre` 派发。`f.pre x` 是任意 `Prop`，Lean 需要
`Decidable (f.pre x)` 才能 `if`，而 `Primitive` 契约没有可判定性字段。**所以派发必须由调用方给
`Bsel : Input → Bool`**——这与 §2.2「组合是用户的事」一致。

**缺口二（已证）**：两支必须共享 `Input` 与 `Output`。`f.Input` 与 `g.Input` 是两个独立类型字段，
所以 `g.pre x`（`x : f.Input`）通不过类型检查——**与 `compose` 需要适配器是同一件事**。
要写成显式等式 `hin : g.Input = f.Input`、`hio : g.Output = f.Output`。

### 阻塞点

`choice` 的 `Output` 只能取一支（`f.Output`），于是 `g` 支的输出必须经 `hio` 搬运：

```lean
post := fun x z => (sel x = true → f.post x z)
                 ∧ (sel x = false → g.post (hin.symm ▸ x) (hio.symm ▸ z))
```

`g.sound` 给出的见证是 `z₀ : g.Output`，返回时要做 `hio ▸ z₀ : f.Output`，于是 `post` 要求
`g.post … (hio.symm ▸ (hio ▸ z₀))`。**而 `hio.symm ▸ (hio ▸ z₀)` 不是 `rfl` 相等**——
`hio` 是变量，两次 `Eq.rec` 卡住；`simpa` 也不化简。实测报

```
type mismatch: hpz has type g.post (⋯ ▸ x) z
             but is expected to have type g.post (⋯ ▸ x) (⋯ ▸ hio ▸ z)
```

**正确做法是让 `hio`/`hin` 在证明里被 `subst`/`cases` 消掉**，这样根本没有 cast。
但 `Input`/`Output` 是 `Primitive` 的**字段**，`cases hio` 不会重写 `f` 与 `g` 本身；
需要先 `cases f; cases g`，而它们含证明项——**那要把 `Primitive` 拆成「纯数据 + 证明」两半**，
或者给 `irreducible`/`subsingleton` 实例。**这是下一轮的活，不是这一轮能顺手做完的。**

### 替代路径（也记在这里）

把 `Primitive` 的 `Input/Output` 从**字段**改成**参数**（`Primitive (I O : Type)`），
则 `choice`/`compose` 都不需要任何等式与 cast。**但那与 §4 的结构冲突，需要一次裁决。**

**所以 `choice` 的阻塞点其实是「`Primitive` 的类型参数该是字段还是参数」这个设计问题。**
它不是编码问题，编码只是把它暴露出来。 -/

end Lattice.Compose
