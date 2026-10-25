

import Lattice.Lib.Chain.RealNumericChainOrder_parts.A
import Lattice.Lib.Chain.RealNumericChainOrder_parts.B
import Lattice.Lib.Chain.RealNumericChainOrder_parts.C


/-!
# LATTICE / 数域方向（W9, 模块 1/8）：**数值链序** —— 数域的**序结构**与嵌入链

## 本文件建立什么

数域链 `ℕ → ℤ → ℚ → ℝ` 的**序嵌入**（order embedding）及其**保序性**，
其中每条嵌入映射**显式给出**（不是靠类型类隐式合成）。

具体建立：

1. `natCastEmbed`、`intCastEmbed`、`ratCastEmbed`、`natToRat`、`natToReal`、`intToReal`
   —— 六条**显式嵌入映射**（`def`，给定函数体）；
2. 上述每条都是 `StrictMono`（**严格**保序，不只是保序）；
3. `natToInt_strictMono` 等**复合链的严格单调性**；
4. **反射性**：`(m:ℝ) < (n:ℝ) → m < n`（保序**且**反射序 —— 这才是"嵌入"的完整内容）；
5. ⭐ **离散性在链中的保持**：`ℕ` 的「没有介于 `0` 与 `1` 之间的元素」
   在嵌入到 `ℝ` 后**仍然可检出**——这是"序嵌入保有离散性"的实质陈述；
6. ⚠ **诚实边界**：`ℚ` **不是**离散的（本文件给出 `rat_not_discrete` 反例：
   `0 < q < 1` 总有更近的 `q/2`），故"链上每一层都离散"是**假命题**——本文件显式否定它。

## 依赖什么

仅 `import Mathlib`。不 import 本仓库任何模块（避免与并发写入的模块冲突）。

## 不做什么（诚实边界）

- **不构造** `ℝ`（用 mathlib 的 `ℝ` 与 `ℚ`-cast，不重新定义 Dedekind 分割/Cauchy 序列）；
- **不证** `ℝ` 的完备性、`ℚ` 在 `ℝ` 中稠密 —— 这些是 mathlib 已有内容，
  本文件只在"**嵌入链的序性质**"这一层做功；
- **不声称** `ℕ ⊂ ℤ ⊂ ℚ ⊂ ℝ` 是**集合论包含**：mathlib 里它们是**互不相同的类型**，
  本文件给的是**显式映射** + **保序/反射序**，这正是"嵌入"一词在类型论下的正确读法；
- ⚠ **不声称**每一层都离散（见第 6 条：`ℚ` 反例）。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.NumericChainOrder
