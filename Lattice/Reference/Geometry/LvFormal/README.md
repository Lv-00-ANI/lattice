# `Lattice/Reference/Geometry/LvFormal/` —— 归档参考实现（**不参与构建**）

## 这一子树是什么

**早期轮次写下的参考形式化：LvFormal 几何理论的古典公理化（Hilbert 五组公理）、
`Theory/` 下的一批理论草案、以及 `Interop/`、`Basic/` 的路径占位。**

**它们记录了**当时**打算证明什么（定理名、注释、对应 `.lv` 规格文件的路径），
但**多数从未编译通过** —— 例如 `Theory/ConstraintPropagation.lean`（标注 Round 6）里
`subst h` 遮蔽了 `by_cases` 引入的假设名，导致 `function expected`。**

## `Reference/` 不是整块归档 —— 这一点必须说清

**`Lattice/Reference/` 有两部分，地位相反：**

| 部分 | 地位 | 谁依赖它 |
|:--|:--|:--|
| **`Geometry/Constraints`、`Geometry/Geometry`、`ConstraintsRoot`、`GeometryRoot`** | **在用** —— 构建干净（`ConstraintsRoot` = BUILD 0） | **`Domains`、`Plugins`、`Semantics`、`Usage`、`Compose`、`Evidence` 里 28 个在用模块** |
| **`Geometry/LvFormal/`（本目录）** | **归档** —— 103 个模块，`Theory/` 里约 50 个不编译，17 个含 `sorry`/`axiom` | **流水线里没有任何东西** |

**=> 所以「`Reference` 是归档」与「`Reference` 是在用的」**都错**。
**归档的边界是 `LvFormal/` 这一子树，不是整个 `Reference/`。**

## 本子树**不**参与构建

**`Lattice.lean` 不导入它；`gov/check_layer_reachability.py` 跳过整个 `Reference/`（那是测量口径，不是归档断言）；
`gov/check_reference_archive.py` 显式检查本子树没有被接进任何构建入口。**

**把约 50 个不编译的模块接进 `lake build Lattice` 只会让构建永远为红，
从而让整个构建状态失去信息量。**

## 重要的一条：本目录**不是**待办清单

**不要在归档目录上「补编译」。** 这些文件的现状是**历史记录**，不是**当前缺口**。
若其中某条定理现在值得证明，正确做法是**在 `Lib/` 或 `Core/` 里按当前标准重写**，
而不是去修一份 200 轮前的草案 —— 修好它也不接入任何东西。

**第 186 轮（P3-3）曾试图给整个 `Reference/` 建聚合器并逐个编译 209 个文件，那是方向错误：
它把「归档」误当成「未完成的层」。本文件与 `gov/check_reference_archive.py` 即为防止该错误再次发生。**

## 当前实测状态（历史快照，不是任务）

| 项 | 数 |
|:--|--:|
| **本子树下 `.lean` 文件** | **103** |
| **`Theory/`** | **93** |
| **其中含 `sorry` 或 `axiom`** | **17** |
| **其中无法编译** | **约 50（一次全量构建报出 1276 处错误）** |

**=> 这些数字的唯一用途是：如果有人问「归档里还剩多少没写」，答案在这里；
而不是「有多少要做」。**
