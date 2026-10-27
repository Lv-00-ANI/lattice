import Lattice.Semantics.Stage1
import Lattice.Semantics.VocabEdit

/-!
# 语义信息主线：阶段划分与聚合

对应 `SEMANTICS-MAINLINE.md` §5 的三阶段。每个阶段一个模块。

| 模块 | 阶段 | 内容 |
|:--|:--|:--|
| `Lattice.Semantics.Stage1` | 阶段 1 | 语义域、词表、几何、继承（约束几何实例） |
| `Lattice.Semantics.VocabEdit` | 阶段 1.5 | 词表编辑：置换/增删精确，合并/拆分有损 |

**import 必须在文件最前面**，所以本说明放在它之后——`Lean` 不接受
模块文档块在 `import` 之前。
-/