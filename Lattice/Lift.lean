import Lattice.Lift.QuantErrorPropagation
import Lattice.Lift.RectangularRepresentation
import Lattice.Lift.SaturationQuantization
import Lattice.Lift.StackError
import Lattice.Lift.WeightLadderFullWidthInstance
import Lattice.Lift.WeightSymbolRepresentation

/-!
# `Lattice.Lift` —— 链路层（P2 搬迁完成后仅剩的模块）

`DIRECTORY-DESIGN.md` §3 的 P2 把表示/编译/量化/代码生成/tokenizer 的模块逐批搬进
`Lattice/Runtime/`。**本聚合器只 import 仍在 `Lift/` 下的模块**；搬走的模块由
`Lattice/Runtime.lean` 聚合，避免同一个声明有两条 import 路径。

本文件随最后一批搬空后删除；删除时 `Lattice.lean` 的 `import Lattice.Lift` 一并去掉。
-/
