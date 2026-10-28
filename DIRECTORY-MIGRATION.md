# 目录重构：P0 已完成，以及**动手前必须先解决的四个矛盾**

> **状态**：P0（契约 + 组合子 + `run` 层定律）已落地并通过全部门禁。
> **未搬任何现有模块**——那是有意的：下面四个矛盾不解决，P2 的搬动会**有损**。

## 0. P0 交付了什么

| 文件 | 内容 |
|:--|:--|
| `Lattice/Compose/Primitive.lean` | `Strength`（格 + `min` + 单调性定理）、`Coverage`、`Primitive`（§4 的七个字段） |
| `Lattice/Compose/Combinators.lean` | `compose`（带适配器）、`compose_sound`、`compose_run`、`compose_run_assoc`、`identity`、`identity_compose_run`、`compose_strength`、`compose_coverage` |
| `Lattice/Compose.lean` | 聚合器 |
| `gov/gate.py` | `LAYER_OF` 加 `Lattice/Compose`（rank 6）；rank 表加 `compose` |

**本目录不 import 任何既有模块**，所以它对 816 个现有模块零影响。这是 P0 能先落地契约的原因。

## 1. 矛盾一：§6 的 `compose` 签名**不可类型化**（已在代码中修正）

```lean
def compose (f g : Primitive) (h : ∀ x y, f.post x y → g.pre y) : Primitive
```

`f.Output` 与 `g.Input` 是两个**独立的 `Type` 字段**，结构里没有任何东西强制它们相等。实测报错：

```
error: application type mismatch
  g.pre y
argument y has type f.Output : Type
but is expected to have type g.Input : Type
```

§7 第 1 条说「所有 `Input/Output` 都是 `Kernel` 类型」——**那不等于同一个类型**。
§7 第 5 条自己说了「缺边用显式适配器」，所以正确签名必须带适配器：

```lean
def compose (f g : Primitive) (adapt : f.Output → g.Input)
    (h : ∀ x y, f.post x y → g.pre (adapt y)) : Primitive
```

**已按修正后签名实现。** 请把 §6 的签名更新为带 `adapt` 的版本。

## 2. 矛盾二：`Lib` 的位置自相矛盾，涉及 **244 个文件**

- §9 的依赖链把 `lib` 放在 **rank 0**（最底，只高于 `top`）；
- §10 说 `Lib/*` → **保持 `Lib`**。

实测：**`Lib` 里有 244 个文件 import `Lift`，16 个 import `Core`**（`grep '^import Lattice\.'`）。
当前 rank 是 `core 0 < lift 2 < lib 3`，所以今天这是合法的。

**按 §9 的新 rank，`lib` 在 0 而 `lift`/`core` 在 2/1，这 244 个 import 全部变成向上依赖。**

**所以 P2 必须二选一**，而设计文档没选：

| 选项 | 后果 |
|:--|:--|
| (a) 把这 244 个文件移出 `Lib` | `Lib` 变成纯数学；但那 244 个是有内容的定理（`Lib/Chain`、`Lib/Editing` 等），搬家是**有损的大手术** |
| (b) 让 `Lib` 保持在链路之上（沿用今天的 `core < lift < lib`） | 与 §9 的 rank 表冲突，需要改 §9 而不是改树 |

### 裁决（第 228 轮）：取 **(b)**，`Lib` **保持今天的 rank 3**（`core < lift < lib < geo`）

`DIRECTORY-DESIGN.md` §9 的 rank 表**已修订**：`lib` **不放在 0**，保持 **3**（在 `core`/`lift` 之上、`geo` 之下）。第一版试过把它抬到 9，I4 立刻报 **14 处**违规——`Geo` 依赖 `Lib`，抬到 `geo` 之上就翻了。

**理由不是「搬家太贵」，而是职责**：`Lib` 要负责两类内容——

1. **无法迁移的**：依赖链路内多个层、又无法干净切分的（`Lib/Chain`、`Lib/Editing`、`Lib/Linear` 等）；
2. **后续新增的同类**：将来需要同时看见 `Kernel`/`Runtime`/`Domains` 的新内容。

把 `Lib` 钉在底层会逼这些内容被硬塞或拆碎，**那是有损的**，而且「新东西该放哪」会没有答案。

**代价必须记账**：`lib 9` 意味着 `Lib` 可以 import `Primitives` 与 `Compose`。
**所以 `Lib` 里的定理不能被当作「独立于架构的数学」引用**——它们可能依赖链路。
强度审计里 `Lib` 的定理按它**实际 import 的层**计，不按「数学库」计。

**⇒ 矛盾二已闭，P2 的 `Lib` 部分不再是阻塞项。**

## 3. 矛盾三：§2.6「Primitives 之间零 import」与 §10 的映射冲突，且破坏前向链

§10 把 `Geo/NetLoss`、`Geo/PenaltyLoss`、`Geo/ConstraintDescent` 都映射到 `Primitives/Train`。
但**第 220 轮的前向链 capstone 正是 `ConstraintDescent` 用 `NetLoss` 与 `PenaltyLoss`**：

```
ConstraintDescent.lean:
  import Lattice.Geo.NetLoss
  import Lattice.Geo.PenaltyLoss
```

按 §2.6，它们在同一个 `Primitives/Train` 里**不能互相 import**。**那 capstone 就不能留在一个文件里。**

**必须二选一**：

| 选项 | 后果 |
|:--|:--|
| (a) 三者合并成一个 primitive（`lossAndDescent`） | 违背「一个 primitive 只做一件事」 |
| (b) capstone 搬到 `Compose` | 正确，但 `Compose` 需要 `Primitives/Train` 的两个 primitive 加一个适配器——**而 capstone 的陈述会变**（它现在是「一步梯度步使约束成立」，搬到 `Compose` 后要写成组合的 `post`） |

**(b) 与设计一致，但它意味着 capstone 的陈述**要重写**，不是搬文件。**

## 4. 矛盾四：§11.2 的「`Kernel/Types` 先 `abbrev` 指向现有类型」只能做到一部分

§2.5 要 `Kernel/Types` 持有 `Model`/`Profile`/`Program`/`Weights`/`ConstraintSet`/`MergeRecord` 等。
但 §9 把 `kernel` 放在 rank 1，而今天：

| 类型 | 今天在哪 | rank | `Kernel`(1) 能否 alias |
|:--|:--|--:|:--|
| `AffineLayer`、`netAct` | `Core` | 0 | **能** |
| `LayerProgram` | `Lift` | 2 | **不能** |
| `GeoConstraint`、`ConstraintSet` | `Geo` | 4 | **不能** |
| `MergeRecord` | `Semantics` | **audit(5)** | **不能** |

**所以 P0 的 `Kernel/Types` 只能 alias `Core` 的那一小部分。** 其余必须等 P2/P3 把定义真正搬过来。
**§11.2 的顺序（P0 先建 Types，P2 再搬）在这一点上是反的**：`Kernel/Types` 的完成依赖 P2 的搬动。

## 5. 修正后的阶段顺序

| 阶段 | 先决条件 | 内容 |
|:--|:--|:--|
| **P0** | — | **✅ 已完成**：`Compose` 契约 + 组合子 + `run` 层定律 |
| **P1** | P0 | `parallel`/`choice`/`optional`/`iterate`；`Compose/Laws`、`Matrix`、`Registry`；**先做 `Compose` 的其余组合子，不搬树** |
| **P1.5** | 矛盾二、三、四**有裁决** | 只改设计文档，不改树 |
| **P2** | P1.5 | 按裁决搬 `Lift`/`Geo`；每搬一组即 `lake build` |
| **P3** | P2 | `Core → Kernel`、`Audit → Evidence`、`check_primitive_independence.py` |
| **P4** | P3 | 删别名、`PRIMITIVE-INDEX`、文档 |

**关键改动**：把「解决四个矛盾」立成 **P1.5**，放在任何搬动之前。原设计把 P0 放在最前、
把矛盾留到 P2 才发现，**那时已经动过树了**。

## 6. 本轮**没有**做什么

- **没有 `git mv` 任何文件。** 一个也没有。
- **没有注册任何 primitive。** `Registry`/`Matrix` 是 P1。
- **没有改 `Lattice.lean` 的公开面。** §3 要求它只 import `Kernel + Primitives + Compose`，
  而那要等 P2 之后才可能成立。
- **没有写 `CInterface/`。** 它是 P5，且依赖 `Primitive` 面稳定。

## 7. 门禁

`lake build Lattice` 通过；`gate.py` I1–I8 全绿；`Lattice/Compose` 已进 `LAYER_OF`（rank 6）。
**P0 对既有 816 个模块零 import 影响**，所以这次重构的每一步都可独立回滚。
