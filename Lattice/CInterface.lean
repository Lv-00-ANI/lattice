import Lattice.CInterface.ABI
import Lattice.CInterface.ContractBoundary
import Lattice.CInterface.Conformance
import Lattice.CInterface.LayoutBytes
import Lattice.CInterface.Serialization

/-!
# `Lattice.CInterface` —— Lean 侧的 C 契约（**规格，不是 C 代码**）

`DIRECTORY-DESIGN.md` §8.1：本层只定义 C 接口形状，**C 实现最后**。

## 已建

- `ABI.lean`：11 个 primitive 的 C 签名 / 错误码 / 所有权描述子，加四条表一致性定理（无重名符号、`ok` 可表示、无 `void` 返回、名字表与表一致）。

## 未建

- `Layout.lean`、`Serialization.lean`、`Conformance.lean`。
  §8.1 要求的布局对象里，`Model`/`Profile`/`Program`/`Certificate` 四个里**三个在活树里不存在**（第 15 轮实测），所以 `Layout` 只能对**已存在**的类型写，那是下一步。
- **没有证明** C 实现与 Lean 语义一致——那需要真写 C 并做 conformance 向量对照（P6）。
-/
