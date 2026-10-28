import Lattice.Primitives.MultistepLoop
import Lattice.Primitives.TokenizeStrategy
import Lattice.Primitives.TokenizerPattern
import Lattice.Primitives.WeightDescent

/-!
# `Lattice.Primitives` —— 基础调用层（**rank 2**，在 `Domains` 之下）

## 为什么它在 `Domains` **下面**，而 §9 说在上面

`DIRECTORY-DESIGN.md` §9 的链是 `domains 3 < primitives 4`。**测量否定了它。**

`PRIMITIVES-RANK-ANALYSIS.md` 逐个量了 §10 想放进 `Primitives` 的模块在 `Domains` 内部的入度：

| §10 行 | 最差入度 |
|:--|--:|
| `Train` | 2 |
| **`Repair`** | **8**（`Loop`） |
| `Verify` / `Model` | 1 |

**「被领域实例调用的基础调用」如果放在实例之上，那些调用就变成向上依赖。** 「使用」就是 import，
被调用者必须在调用者之下。**所以 §9 把方向写反了，本层因此是 rank 2。**

## 为什么只有 4 个模块

判据：**在 `Domains` 内部入度 0、且不 import 任何 `Domains` 模块**。101 个里只有这四个通过。
其余 95 个都是消费者——`Constraint` 入度 25、`Loss` 20、`Loop` 8。
**把它们搬进来会让本层依赖 `Domains`，那就不是基础调用了。**

## 边界

- **`Kernel` 层仍未建立**，`runtime 2 == primitives 2` 目前同秩。
- **`CInterface` 不存在。**
- **这 4 个模块的 namespace 未改**（§2.8），所以没有定理改名。
-/