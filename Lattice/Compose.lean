import Lattice.Compose.Primitive
import Lattice.Compose.More
import Lattice.Compose.ForwardChain
import Lattice.Compose.Registry
import Lattice.Compose.Iterate
import Lattice.Compose.Steps
import Lattice.Compose.PrimitiveShape
import Lattice.Compose.AssocLaws
import Lattice.Compose.AdapterMatrix
import Lattice.Compose.Combinators
import Lattice.Compose.ComposeObligation
import Lattice.Compose.Proofs
import Lattice.Compose.Showcase.FullChain
import Lattice.Compose.Showcase.L1L2

/-!
# `Lattice.Compose` —— 组合子（P0 骨架）

按 `DIRECTORY-DESIGN.md` §3，`Compose/` 只放组合子，不放流程：
`Primitive` 契约 + `compose` / `identity` 及其 `run` 层定律。

**P0 只建到这一步**：`parallel` / `choice` / `optional` / `iterate` 的 `Input`/`Output` 是积与和类型，
`sound` 的写法各不相同，属于 P1。`Registry` 与 `Matrix` 也属于 P1。

**本目录不 import 任何既有模块**，所以它对 816 个现有模块零影响——这是 P0 能在不动树的情况下
先落地契约的原因。
-/
