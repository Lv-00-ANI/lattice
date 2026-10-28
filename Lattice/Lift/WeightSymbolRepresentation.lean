/-
# `权重 ⇄ 符号`：一个**精确**的双向表示（不是有损，不是近似）

## 0. 这一节补的是什么

目标把 `符号 ⇄ 权重` 这一跳称为唯一的真难点。库里的现状是：

- **正向**（符号 → 权重）有 `layerOfListFull`（第 165 轮）：`n*n` 个系数按行主序，然后 `n` 个偏置；
- **逆向**（权重 → 符号）有 `listOfLayer`（第 166 轮）与它的往返 `roundtrip`（第 168 轮）；
- **但两者从来没有被放进同一个结构里**，所以「双向」在库中不是一个定理。

**这一节把它们装进 `Representation`，于是逆向是 `extract`、往返是 `roundtrip`，双向被机器检查。**

## 1. 为什么用 `Representation` 而不是 `Ladder`

**`Ladder` 没有逆向字段**：

```lean
structure Ladder (Data Tok Sym W : Type) where
  l0l1 : Tokenizer Data Tok
  l1l2 : Tokenizer Sym Tok
  l2l3 : Sym → W            -- 只有正向
  satSym : Sym → Prop
  satW : W → Prop
  l2l3_sound : ∀ s, satSym s → satW (l2l3 s)
```

**`Ladder` 是正向链**（data → token → 符号 → 权重），它在定义上就没有 `W → Sym`。
所以「`WeightWadderN` 缺权重→符号这一跳」**不是那个实例的疏漏，是 `Ladder` 这个结构不表达逆向**。

逆向的载体是 `Representation`：

```lean
compile : P → W
extract : W → P
roundtrip : ∀ p, extract (compile p) = p
```

**这就是「提取回符号」。本节交付的是这个，并且是精确的（`= `，不是 `dist ≤ ε`）。**

## 2. 长度前提怎么处理：放进类型

`listOfLayer` 只在 `s.length = n*n + n` 时才是 `layerOfListFull` 的逆。两条路：

1. 让 `roundtrip` 带前提——但 `Representation.roundtrip` 要求 `∀ p`，无量词内的前提；
2. **把长度放进类型**：`P := { s : List ℝ // s.length = n*n + n }`。

**选 2。** 这不是回避：一个 `n × n` 权重矩阵加上 `n` 个偏置，其符号侧**本来就是定长的**。
把它写成裸 `List ℝ` 只是丢掉了一个约束，再从外部补回来。

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `weightSymbolRep` | **精确双向表示**：`compile := layerOfListFull`，`extract := listOfLayer`，`roundtrip` 已证 |
| `weightSymbolRep_roundtrip` | 展开形式：`extract (compile p) = p` |
| `weightSymbolRep_coeff` | **读回系数**：第 `i*n+j` 项确实是 `W i j` |
| `weightSymbolRep_bias` | **读回偏置**：第 `n*n+j` 项确实是 `b j` |
| `weightSymbolRep_exact` | **这是精确的双向表示**（与 `sound_not_exact` 那条被否证的一般精确性主张区分开） |

## 4. 边界（必须明说）

- **`n = 0` 被排除**（`hn : 0 < n`）：`Fin 0` 是空类型，`k % 0` 无意义。
- **本节不声称**「任意权重张量都能精确提取回符号」。它说的是：**这一类编码器
  （满宽、行主序、带偏置）与它的逆构成精确双向**。一般张量的提取仍是有损/近似的，
  见 `ApproxRepresentation` 与 `LossyRep`——**三档编码强度并存，不是一个取代另一个**。
- **`encode`/`decode` 取 `id`**：它们表达的是「点如何呈现给两侧」，对同一个 `Fin n → ℝ` 点，
  两侧看到的是同一个东西。**这不是偷懒**：`Representation` 要求这两者只是为了允许两侧
  的输入空间不同（例如 token 化），这里恰好相同。
- 本节**不改** `Ladder`、`WeightWadderN`、`WeightWadderFullWidth`、`WeightWadderInverse`
  的任何既有定理。
-/
import Mathlib
import Lattice.Runtime.Extraction
import Lattice.Lift.WeightLadderInverse

namespace FullWidth

open Lattice.Core Lattice.Lift

variable {n : ℕ}

/-- **精确的双向表示**：符号侧是定长列表，权重侧是满宽仿射层。

`roundtrip` 用的是第 168 轮的 `roundtrip` 定理，不是假设。 -/
noncomputable def weightSymbolRep (hn : 0 < n) :
    Representation { s : List ℝ // s.length = n * n + n } (AffineLayer (Fin n)) where
  inputP := Fin n → ℝ
  inputW := Fin n → ℝ
  encode := id
  decode := id
  compile := fun p => layerOfListFull (n := n) p.val
  extract := fun L => ⟨listOfLayer hn L, listOfLayer_length hn L⟩
  roundtrip := by
    intro p
    apply Subtype.ext
    exact roundtrip hn p.val p.property

/-- **往返**：提取确实是编译的逆。 -/
theorem weightSymbolRep_roundtrip (hn : 0 < n) (p : { s : List ℝ // s.length = n * n + n }) :
    (weightSymbolRep hn).extract ((weightSymbolRep hn).compile p) = p :=
  (weightSymbolRep hn).roundtrip p

/-- **读回的值就是原来的列表**：往返在 `val` 上取原样。 -/
theorem weightSymbolRep_val_roundtrip (hn : 0 < n) (s : List ℝ)
    (hlen : s.length = n * n + n) :
    ((weightSymbolRep hn).extract ((weightSymbolRep hn).compile ⟨s, hlen⟩)).val = s := by
  rw [weightSymbolRep_roundtrip]

/-- **读回系数**：逆读出的第 `i*n + j` 项就是编译进去的 `W i j`。

这条把「提取」与权重矩阵的**分量**连起来，而不是只说两个列表相等。 -/
theorem weightSymbolRep_coeff (hn : 0 < n) (s : List ℝ) (hlen : s.length = n * n + n)
    (i j : Fin n) :
    ((weightSymbolRep hn).extract ((weightSymbolRep hn).compile ⟨s, hlen⟩)).val.getD
        (i.val * n + j.val) 0 =
      (layerOfListFull (n := n) s).W i j := by
  rw [weightSymbolRep_val_roundtrip]
  exact (layerOfListFull_W s i j).symm

/-- **读回偏置**：逆读出的第 `n*n + j` 项就是编译进去的 `b j`。 -/
theorem weightSymbolRep_bias (hn : 0 < n) (s : List ℝ) (hlen : s.length = n * n + n)
    (j : Fin n) :
    ((weightSymbolRep hn).extract ((weightSymbolRep hn).compile ⟨s, hlen⟩)).val.getD
        (n * n + j.val) 0 =
      (layerOfListFull (n := n) s).b j := by
  rw [weightSymbolRep_val_roundtrip]
  exact (layerOfListFull_b s j).symm

/-- **这是精确的双向表示**，不是有损也不是近似。

与 `sound_not_exact`（第 79 轮否证的一般精确性主张）**不冲突**：那一条说的是
「任意表示都存在损失为零的提取」，**它是假的**；这一条说的是
**这一类编码器的提取没有损失**，因为编码器是满宽、可逆的。 -/
theorem weightSymbolRep_exact (hn : 0 < n)
    (p : { s : List ℝ // s.length = n * n + n }) :
    ∃ (R : Representation { s : List ℝ // s.length = n * n + n } (AffineLayer (Fin n))),
      R.extract (R.compile p) = p ∧ R.compile p = (weightSymbolRep hn).compile p :=
  ⟨weightSymbolRep hn, weightSymbolRep_roundtrip hn p, rfl⟩

/-- **非平凡性**：这个表示不是恒等——`n = 2` 时两个不同的符号列表给出不同的层。

`n` 在这里固定为 `2`，因为两个具体列表的长度必须与 `n*n + n` 对上。 -/
theorem weightSymbolRep_nontrivial :
    (weightSymbolRep (n := 2) (by norm_num)).compile
        ⟨[1, 2, 3, 4, 0, 0], by norm_num⟩ ≠
      (weightSymbolRep (n := 2) (by norm_num)).compile
        ⟨[0, 0, 0, 0, 0, 0], by norm_num⟩ := by
  intro h
  have hW := congrArg (fun L => (L : AffineLayer (Fin 2)).W 0 1) h
  simp only [weightSymbolRep, layerOfListFull] at hW
  norm_num at hW

end FullWidth
