import Lattice.Core.Data.Basic
import Lattice.Core.Data.Equiv
import Lattice.Core.Data.Encode
import Lattice.Core.Data.Decode
import Lattice.Core.Data.Bridge
import Lattice.Core.Data.Token
import Lattice.Core.Data.Models

/-!
# 数据层：表示链的源头

**表示链是 `数据 ⇄ token ⇄ 符号模型 ⇄ 权重`。本目录给出链条的**起点**，
并把「数据」从一个假设变成一个具体的、可编码的、带证明的类型。**

## 分文件的理由

**加法顺序是 `Basic → Equiv → Encode → Decode → Bridge → Token → Models`：每一层只依赖前面的层。
把它们塞进一个文件会让「哪条引理依赖哪个表示」变成隐式的，
而本项目的纪律是「证明链彻底梳理干净」。**

## 七个文件各自证明什么

| 文件 | 内容 | 关键定理 |
|:--|:--|:--|
| `Basic` | `Sample`/`Index`/`Data` 与 `DataValid` | `corpus_width_append` |
| `Equiv` | `DataEquiv` 三条等价律 | `dataEquiv_iff_eq` |
| `Encode` | `Data → CIC Term` | **`encode_sound`** |
| `Decode` | `CIC Term → Option Data` | **`decode_encode_shape`** |
| `Bridge` | `Data → IRSkeleton` | **`encode_comm_shapes`**、`nodup_shapesOfCorpus` |
| `Token` | `Token` 与 `tokenize` | `token_count`（在 `Models`） |
| `Models` | 端到端 | **`data_models`** |

## 诚实的边界

**编码是**有损**的：数值不进 term，只进形状。**
**⇒ `decode_encode_shape` 说的是「形状可逆」，不是「数据可逆」；把后者写成定理会是假的。**
**⇒ `Bridge.encode_comm_shapes` 只覆盖张量侧；关系侧的对齐需要展开 `parseWithRelations`，
那是下一轮的工作。**
-/
