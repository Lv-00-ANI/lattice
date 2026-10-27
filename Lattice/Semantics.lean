import Lattice.Semantics.Stage1

/-!
# 语义信息主线：阶段划分与聚合

对应 `SEMANTICS-MAINLINE.md` §5 的三阶段。每个阶段一个模块。

| 模块 | 阶段 | 内容 |
|:--|:--|:--|
| `Lattice.Semantics.Stage1` | 阶段 1 | 语义域、词表、几何、继承（约束几何实例） |

**import 必须在文件最前面**，所以本说明放在它之后——`Lean` 不接受
模块文档块在 `import` 之前。
-/