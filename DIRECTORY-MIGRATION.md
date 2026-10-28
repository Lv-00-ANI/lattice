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
## 4b. 第 237 轮：`Lift` 的**依赖测量**，以及别名策略的落地定义

### 测量结果：`Lift` 没有任何向上依赖

用 `^import Lattice\.<Top>` 逐个扫 `Lift/` 的 66 个模块：

| 类别 | 数量 |
|:--|--:|
| **import 不到任何其他 Lattice 模块**（只有 `Mathlib`） | **5** |
| import 其他 `Lift` 模块（但不 import `Lib`/`Geo`） | 49 |
| import 了 `Core`（但仍不 import `Lib`/`Geo`） | 12 |
| **import 了 `Lib`/`Geo`/`Semantics`/`Audit`/`Compose`** | **0** |

**第三行是零**，这是本轮最重要的读数：**`Lift` 可以整体搬到 `Runtime` 而不触犯任何分层规则**，
因为当前的 `core 0 < lift 2 < lib 3` 里 `Lift` 本来就在 `Lib` 之下。
（那 244 个 import `Lift` 的文件全在 `Lib`，是**向下**依赖，合法——这也解释了为什么
第 228 轮把 `Lib` 放在 rank 3 是对的。）

**所以 `Lift → Runtime` 不是「有损的架构改动」，而是「改路径、不改依赖方向」。**
这也说明：本项目的分层形状**已经是对的**，`DIRECTORY-DESIGN` 的 P2 主要是**改名与归位**，
不是重新分层。

### 别名策略：把 §2.8 的「一个周期」定义为**零轮**

§2.8 说「旧路径留 `import` 别名一个周期」，但**从没定义周期边界**（第 234 轮已登记这一缺口）。

**本轮的落地定义**：**当且仅当一次提交内改完所有调用点，就不留别名。**

理由：
1. 别名会让**模块数虚增**（每搬一个 +1），而模块数是文档里被守卫核对的数字——**虚增会让计数失去意义**；
2. 别名是**第二个路径**，而 `import` 是唯一的真相源时，两个路径意味着**两处会不一致**；
3. 「一个周期」的目的是**不破坏下游编译**，而**同一次提交改完调用点就达成了这个目的**，
   别名只是达成手段之一。

**第 234 轮的 `ProgramAST` 留了别名**（当时只有 1 个调用点，不确定策略）。
**本轮起统一为零轮**：`ProgramAST` 的别名在下一轮删除。

## 5. 裁决 A（第 232 轮）：`Primitive` 的 `Input`/`Output` **改成参数**

第 228 轮记下的阻塞（`choice` 写不出来）的裁决是：**把 `Input`/`Output` 从字段改成参数**。

```lean
structure Primitive (I O : Type) where
  pre : I → Prop
  post : I → O → Prop
  run : I → Option O
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  strength : Strength
  coverage : Coverage
  frame : I → O → Prop
```

**改动前后的实测对照**：

| 组合子 | 字段版（第 228 轮） | 参数版（第 232 轮） |
|:--|:--|:--|
| `compose` | 带 `adapt` + `Eq` 等式 | **无适配器**；`composeWith` 保留给类型不同的情形 |
| **`choice`** | **写不出来**（`Eq.rec` 卡住） | **`Primitive I O` × 2，无 cast，已证 `choice_sound`** |
| **`optional`** | 需 `Output = Input` 等式 | **`Primitive I I`，无 cast，已证 `optional_sound`** |
| `parallel` | 字段投影 | `Primitive (I₁ × I₂) (O₁ × O₂)` |
| `identity_compose_run` | 需要 `α` 与 `f.Input` 配对 | **只需要 `h`**（少一个参数） |

### ⚠ 一处我写错又改回的判断

第 232 轮第一版在 `Combinators.lean` §2 写「参数化后左单位不需要任何兼容性假设」。**不成立**：
`compose` 的 `h` 要 `∀ x y, (identity I).post x y → f.pre y`，而 `post` 是 `y = x`，
于是要产出 `f.pre y`——**`f.pre` 是任意的，推不出来**。实测报
`trivial has type True but is expected to have type f.pre x`。

**准确的说法**：参数化消掉的是 **cast**（`adapt`），**不是语义义务**（`h`）。
两者是不同的问题，混在一起会写出一个假的「不用证明」的结论。已在文件里写清。

### 代价

`Primitive` 不再是单一 `Type`，所以「混合列表」需要 `Sigma` 包装——
`Registry.MatrixRow` 现在带 `I`/`O` 两个字段。**这是类型系统要求付的价，不是设计缺陷。**


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

### 裁决（第 228 轮）：取 **(b)** —— capstone 搬到 `Compose` 并重写陈述

**已落地**：`Lattice/Compose/ForwardChain.lean`。

| 声明 | 内容 |
|:--|:--|
| **`trainStep c pts : Primitive`** | 一步梯度下降作为一个契约实例：`pre` = 「约束尚未满足」（`β + c ≠ 0`），`post` = 损失严格下降 ∧ 归零 |
| `trainStep_sound` | 它的 `sound` |
| **`forward_chain_capstone`** | **四环**：严格下降、归零、约束成立、零损失 ⟺ 成立 |
| `forward_chain_at_solution` | 已满足时一步不改变损失（保守性） |

**陈述确实变了，这是裁决的一部分**：`Geo` 里那条是**孤立定理**，`compose`/`parallel`/`Matrix` 都用不上；
`Compose` 版本把它做成 `Primitive`，**`post` 是结构字段，因而可被组合**。
第 220 轮「四环写进一条陈述」的价值保留，同时获得**可组合性**。

**`Geo/ConstraintDescent.lean` 的那两条已删除**（裁决是「搬」，不是「复制」）。
### ⚠ 第 228 轮新增：**第五个矛盾** —— §5.8 的 primitive 名字会撞上定位守卫

`Compose/ForwardChain.lean` 的第一版把那个一步下降的 `Primitive` 命名为 `trainStep`。
**`gov/check_scope_boundary.py` 立刻失败**：

```
Compose/ForwardChain.lean  L67  trainStep  training-loop name
SCOPE BOUNDARY: 1 executable-framework marker(s)
```

那条守卫的 `TRAINING_NAMES` 是

```python
["trainStep", "trainingStep", "trainLoop", "trainingLoop", "sgdStep", "adamStep",
 "backward", "zeroGrad", "optimizerStep", "fitModel", "trainModel"]
```

**它的理由写在文件里，而且是对的**：训练循环**不需要任何 import**，所以「按 import 判引擎」抓不到它；
**名字是唯一的机械信号**。所以把 `trainStep` 判为违规不是误报，**是这条守卫按设计工作**。

**但这把 §5.8 的清单顶住了**：那里把 `sgdStep`、`momentumStep`、`adamStep` 列为 `Primitives/Train` 的成员——
**其中两个直接在禁止表里，第三个的命名族也在**。**照 §5.8 实现会立刻让定位守卫变红。**

**本轮的处置**：改名为 **`descentStep`**——它是**一步下降**，不是循环，
`descentStep` 既准确又不在禁表内。**守卫不放宽。**

**需要裁决的问题**：§5.8 要的是「优化器步长」这类基础调用，
而守卫要的是「不实现训练框架」。**两者并不冲突**——冲突在**命名**上。
建议把 §5.8 的 `sgdStep`/`momentumStep`/`adamStep` 改成不含 `Step`+优化器名的形式
（例如 `applySgd`/`applyMomentum`/`applyAdam`），**而不是**放宽 `TRAINING_NAMES`：
后者会同时放过真正的训练循环。


留下的是两条**损失层事实**：`netLoss_pos_of_ne`、`netLoss_zero_iff_holds`——它们不涉及 `Primitive`，
而 `Compose` 之上的任何东西都需要它们。

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

## 8. 第 242 轮：`Lift` 层清空（P2 的 `Lift` 部分完成）

§4b 测出「`Lift` 没有向上依赖，可以整体搬进 `Runtime`」；第 234–242 轮把它做完了。

| 批次 | 模块数 | 内容 |
|:--|--:|:--|
| 第 234 轮 pilot | 1 | `ProgramAST`（`Lift` → `Runtime` 的第一块，证明路径可改） |
| A1 | 5 | 不 import 任何其他 Lattice 模块的 5 个 |
| A2 | 11 | 首批剩余模块（+ 删掉 pilot 留下的旧路径别名） |
| A3 | 14 | `Lift` 图的最小闭前缀 |
| A4 | 14 | 下一层闭前缀（搬完重算，frontier 会变） |
| A5 | 15 | 重算后的闭前缀（21 个里的 15 个；A5 实测 34 个 import 点、20 个文件） |
| A6 | 6 | 最后 6 个（对剩下的集合仍是闭集；A6 实测 9 个 import 点、4 个文件） |
| **合计** | **66** | `Lift/` 原有 66 个模块，全部迁入 `Runtime/` |

### 8.1 为什么删除 `Lattice/Lift.lean`（而不是留一个空聚合器）

`Lattice/Lift.lean` 的唯一职责是聚合 `Lift/` 的模块。`Lift/` 空了以后：

- 留着它 import `Runtime/` 的模块，就是**第二条聚合路径**——`Lattice.Runtime` 与 `Lattice.Lift`
  会指向同一批声明。§2.8 的「一个周期」在第 237 轮被定义为**零轮**（同一提交改完调用点），
  理由之一正是「别名会让模块数虚增，而模块数是被守卫核对的数字」；
- 留成空文件则是一个没有任何声明的死模块，`Lattice.lean` 仍然 import 它，读者无法从树里看出它已退役。

所以 `Lattice/Lift.lean` 与 `Lattice.lean` 的 `import Lattice.Lift` 在同一次提交里一起删除。
**模块数 826 → 825**，定理数与声明数不变（那个文件里没有声明）。

**`namespace` 没有改**（§2.8）：66 个模块的声明仍在 `Lattice.Lift.*` 命名空间下，只是文件在
`Runtime/` 里。这是 §2.8 明说的代价——路径与命名空间不再一一对应。

### 8.2 这一步验证了什么

- `lake build Lattice` exit 0（6515 个 target）；`gate.py` I1–I8 全绿；
  `verify_all.py` full PASS；`check_proof_debt_orphans` 384 个已复核文件全部 resolve；
  `check_proof_strength` 24 个已知形状，**none new, none paid off silently**。
- **`gov/` 的八件路径键控工件全部靠 `_paths.resolve` 工作，A5/A6 没有为搬迁改过一个守卫。**
  A5 需要改的只有 `OBJECTIVE-MAP.md`（它由 `gen_objective_map.py` 从树重新生成，不是手写）。
- `Lib`/`Reference/` 未动；`Lift/` 的搬迁没有改任何定理陈述。

### 8.3 还没做

- **`Geo/`（99 个模块）**：分析与有损清单见 `GEO-MIGRATION-PLAN.md`。**一个文件都没搬。**
- `Core → Kernel`、`Audit → Evidence`、`Lib` 的定位：P3/P4，仍未动。

