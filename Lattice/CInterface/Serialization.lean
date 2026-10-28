/-
# `CInterface/Serialization` —— **词级**序列化契约（不是字节级）

## 为什么是「词」而不是「字节」

`DIRECTORY-DESIGN.md` §8.1 要「token/weight/profile 的字节格式」。实测：

- **`token` 与 `weight` 的载体存在**：token 是 `List Int`，权重是 `AffineLayer (Fin k)`
  （`W : Fin k → Fin k → ℝ`、`b : Fin k → ℝ`）；
- **`profile` 不存在**（第 15 轮：23 个具名类型里 17 个没有）。

而**字节**这一步卡在 `ℝ` 上：`ℝ` 在 Lean 里是抽象的，**没有可计算的字节表示**。
把它接到 IEEE-754 需要一个**模型**（`Lib/Quantization/RealIEEE754` 里有），
但那是**另一条**证明链，且需要 `ℝ → Float` 的舍入约定。**所以本文件不写字节。**

## 已证：布局的总长度

`layerWords_length`：`k` 宽的仿射层恰好 `k * k + k` 个词。
**这是 C 侧缓冲的大小**，不是估计。

## 定义形式的三次尝试（写给下一轮）

| 轮 | 定义 | 结果 |
|--:|:--|:--|
| 17 | `flatMap`（行主序摊平） | 长度公式**试了六次**才过（`.sum` 与 `.length` 的错位、`map_const'` 不匹配、`← List.map_map` 不匹配），最后靠**对行列表归纳** |
| 18 | `Fin.divNat`/`Fin.modNat` 索引 `Fin (k*k)` | **长度变成两次 `length_map`，不需要归纳**——本文件采用它 |
| 18 | 同上，但要取回引理 | ❌ **没过**：`List.getElem_append_left` 的证明参数形式不匹配，且注入性要**依赖重写**（`rw [h] at h₁` 报 motive 不 type correct） |

⭐ **教训**：**换定义形式比死磕证明便宜**——`divNat` 让长度从六次失败变成两行。
而**取回引理**是另一回事：它需要在**同一条 list 的两个不同索引**上取元素，
那要求先有 `List.getElem_append_left/right` 的正确调用形式，再用 `congrArg` 避免依赖重写。

## ⚠ 本文件**没有**证明的东西（已登记）

- **`layerWords` 的单射性未证**。那是格式契约的另一半——「词序列相同 ⟹ 层相同」。
  它由两条取回引理得到（第 `i*k+j` 个是 `W i j`，第 `k*k+j` 个是 `b j`），而那两条**没有写成**。
  第 18 轮试过：`List.getElem_append_left` 与 `List.getElem_append_right` 的 `rw` 形式不匹配，
  且随后的注入性证明需要在**依赖索引**上重写，`rw` 报 *motive is not type correct*。
- **字节级**（字节序、对齐、填充、`ℝ` 的二进制表示）**未做**。
- **`Conformance`**（`#eval` 向量与 C 对照）**未做**。

**`sorry` 不可接受，所以宁可缺一半也不写假的。** 缺口的确切位置写在上面——下一轮从那两行开始。 -/
import Mathlib
import Lattice.Core.Net

namespace Lattice.CInterface.Serialization

open Lattice.Core

/-- **一层的词序列**：`k*k` 个权重（行主序，索引 `i*k+j` 处是 `W i j`），再接 `k` 个偏置。

长度是 `k * k + k`，见 `layerWords_length`。 -/
noncomputable def layerWords {k : ℕ} (L : AffineLayer (Fin k)) : List ℝ :=
  (List.finRange (k * k)).map (fun idx => L.W (Fin.divNat idx) (Fin.modNat idx)) ++
    (List.finRange k).map (fun j => L.b j)

/-- ⭐ **参数数公式**：`k` 宽的仿射层恰好 `k * k + k` 个词。

**这是布局的总长度**，不是估计——C 侧的缓冲大小由它决定。 -/
theorem layerWords_length {k : ℕ} (L : AffineLayer (Fin k)) :
    (layerWords L).length = k * k + k := by
  unfold layerWords
  rw [List.length_append, List.length_map, List.length_map, List.length_finRange,
      List.length_finRange]

/-- **退化情形**：`k = 0` 时词序列为空，与 `k * k + k = 0` 一致。 -/
theorem layerWords_zero (L : AffineLayer (Fin 0)) : layerWords L = [] := by
  unfold layerWords
  simp

end Lattice.CInterface.Serialization
