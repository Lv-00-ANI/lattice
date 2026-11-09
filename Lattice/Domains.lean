import Lattice.Reference.Geometry.ConstraintsRoot
import Lattice.Reference.Geometry.GeometryRoot
import Lattice.Reference.Geometry.Geometry.Encode.CIC
import Lattice.Reference.Geometry.Geometry.Encode.Tags

/-!
# `Lattice.Domains` —— 领域实例层（Geo 搬迁的第一站）

按 `DIRECTORY-DESIGN.md` §3，`Domains/` 放领域实例。它是 `Geo/` 的搬迁目标之一。

## 为什么是 rank 3（与 `lib` 同级）

第 242 轮**传递**测量（不是直接 import）：99 个 `Geo` 模块里

| 需要的 rank | 模块数 |
|--:|--:|
| 0 | 11 |
| 2 | 8 |
| **3** | **80** |

**80 个传递依赖 `Lib`**，所以它们只能落在 rank >= 3。
`Kernel`（rank 1）装不下——那正是 §10 的 `Kernel/Constraints` 行被推翻的原因。

## 为什么这一批是「rank 0」的 11 个

这 11 个在任何 rank 都合法，所以搬动**不可能**产生新的向上依赖。**先搬不可能错的。**

## 为什么暂时是平铺，而不是 `Domains/Geometry`

§10 把它们分到 `Domains/Geometry`、`Domains/Constraints`、`Primitives/*`，
但那个划分取决于 `GEO-MIGRATION-PLAN.md` §3 的三条路线（A/B/C）——**尚未裁决**。
平铺是**正确的中间态**；之后的子划分是同层内的 `git mv`。
-/