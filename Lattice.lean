import Lattice.Core
import Lattice.Runtime
import Lattice.Slots
import Lattice.Domains
import Lattice.Geo
import Lattice.Lib
import Lattice.Audit
import Lattice.Usage
import Lattice.Semantics

/-!
# LATTICE

符号 <-> 权重表示转换框架的 Lean 4 形式化。

## 分层

* `Lattice.Core`    -- 语言层：语法、语义、满足关系、修复、权重接口（唯一权威语义）
* `Lattice.Runtime` -- 链路层：L0 <-> L1 <-> L2 <-> L3（第 242 轮起，原 `Lattice.Lift` 的 66 个模块全在这里）
* `Lattice.Slots`   -- 空位层：未证但承重的命题，只声明不证明
* `Lattice.Geo`     -- 约束几何与精确惩罚
* `Lattice.Lib`     -- 应用库：各主题的实例与定理

## 不变量

1. 无 `axiom` / `sorry` / `admit` / `opaque`
2. 同一语义概念只在一处定义
3. 未证但承重的命题写成显式前提 `(h : P)`，不藏进 environment
4. 标为 `EndToEnd` 的定理必须真的用到它声称连接的每一层
-/