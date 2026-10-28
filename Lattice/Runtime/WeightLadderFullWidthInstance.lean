/-
# 满宽编码器的 `Ladder` 实例：与秩一版并存，而不是替换它

## 0. 为什么是「并存」

`Lift/WeightLadderN.lean` 的 `weightLadderN` 用**秩一**的 `layerOfList`：

```lean
W := fun i _ => (s.take n).getD i.val 0     -- 第二下标被忽略
```

第 165 轮证明了这样得到的 `W` **每行相同**、**不是单射**，所以它没有左逆。
第 168 轮给出了满宽版 `layerOfListFull` 与它的精确逆 `listOfLayer`（含往返定理），
第 168 轮又把它装进 `weightSymbolRep`（一个**精确** `Representation`）。

**但 `weightLadderN` 仍然用秩一版。** 本节补上满宽版的 `Ladder`，**不删不改** `weightLadderN`：

- `weightLadderN` 的 `act_zero_of_all_zero` 依赖**秩一的偏置位置**（`s.drop n`）；
  换成满宽会同时改前提，那是**另一个定理**，不是同一个定理的改进。
- **秩一版作为否证证据保留**（第 165 轮的 `old_rank_one_at_two` / `old_not_injective`）。
  删掉它，那两个定理就没有对象了。

## 1. 本节交付

| 声明 | 内容 |
|:--|:--|
| `act_zero_of_all_zero_full` | 满宽层的零点性质（假设与秩一版相同：整列表全零） |
| `weightLadderNFullWidth` | **`Ladder` 实例**，`l2l3 := layerOfListFull` |
| `weightLadderNFullWidth_forward` | 端到端：全零 ⟹ 满宽权重栈把零点映零 |
| `weightLadderNFullWidth_has_inverse` | **满宽版有精确逆**——这是秩一版做不到的 |

## 2. 与秩一版的实质区别

满宽版的偏置在 `s[n*n + j]`，秩一版在 `s[n + j]`。所以：

- **秩一版的 3 个参数（`n` 个 `W` 列 + `n` 个 `b`）只为 `n×n + n` 个自由度中的 `2n` 个提供了位置**，
  其余 `n*n - n` 个自由度无处存放——这就是它不单射的原因；
- **满宽版用它该有的 `n*n + n` 个位置**，所以可逆。

`weightLadderNFullWidth_has_inverse` 把这一点写成定理：**存在** `listOfLayer` 把编译出的层
还原成原列表（在长度匹配时）。

## 3. 边界

- **本节不声明 `weightLadderN` 已弃用**。两者都注册在库里，用途不同：
  秩一是**否证的载体**，满宽是**可逆的载体**。
- **`n = 0` 时 `layerOfListFull` 退化为空层**（`Fin 0` 无元素，`b` 也是空函数）。
  往返定理要求 `0 < n`，所以 `weightLadderNFullWidth_has_inverse` 带 `hn : 0 < n`。
- 本节**不改** `WeightLadderN`、`WeightLadderFullWidth`、`WeightLadderInverse` 的任何既有定理。
-/
import Mathlib
import Lattice.Runtime.EndToEnd
import Lattice.Runtime.WeightLadderFullWidth
import Lattice.Runtime.WeightLadderInverse
import Lattice.Runtime.WeightLadderN

namespace Lattice.Lift.FullWidthLadder

open Lattice.Core

/-- **满宽编码器的零点性质**：列表全零 ⟹ 编译出的满宽层把零点映零点。

与 `WeightLadderN.act_zero_of_all_zero` 的**假设相同**（整列表全零），
区别只在结论里用的是满宽层。证明走 `act_zero_apply`（`affineAct p 0 j = p.b j`）后
直接读 `s[n*n + j]`。 -/
theorem act_zero_of_all_zero_full {n : ℕ} (s : List ℝ) (h : ∀ x ∈ s, x = 0) :
    affineAct (FullWidth.layerOfListFull (n := n) s) (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
  funext j
  rw [Lattice.Lift.WeightLadderN.act_zero_apply]
  show s.getD (n * n + j.val) 0 = 0
  by_cases hlt : n * n + j.val < s.length
  · rw [List.getD_eq_getElem _ _ hlt]
    exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ (by omega)]

/-- **满宽版的 `Ladder`**：`l2l3` 用 `layerOfListFull` 而不是秩一的 `layerOfList`。

`satSym` / `satW` 与 `weightLadderN` **逐字相同**——变的只有编码器。
**这正是要展示的**：同一对谓词下，换一个不丢信息的编码器，结论就从「不可逆」变成「可逆」。 -/
noncomputable def weightLadderNFullWidth (n : ℕ) :
    Ladder (List ℝ) ℝ (List ℝ) (List (AffineLayer (Fin n))) where
  l0l1 := identityTokenizer ℝ
  l1l2 := identityTokenizer ℝ
  l2l3 := fun s => [FullWidth.layerOfListFull (n := n) s]
  satSym := fun s => ∀ x ∈ s, x = 0
  satW := fun w => netAct w (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ))
  l2l3_sound := by
    intro s hs
    exact act_zero_of_all_zero_full (n := n) s hs

/-- **端到端**：符号内容全零 ⟹ 满宽权重栈把零点映零。维数 `n` 任意。 -/
theorem weightLadderNFullWidth_forward (n : ℕ) (s : List ℝ)
    (h : (weightLadderNFullWidth n).satSym s) :
    (weightLadderNFullWidth n).satW ((weightLadderNFullWidth n).l2l3 s) :=
  (weightLadderNFullWidth n).ladder_forward s h

/-- **满宽版有精确逆**——秩一版做不到的那件事。

`listOfLayer` 把 `layerOfListFull s` 还原成 `s`（当 `s.length = n*n + n`）。
所以 `l2l3` 把符号列表**无损**地送进权重侧，逆向由此存在。

**这与 `weightLadderN` 的对比是本节的要点**：`weightLadderN` 的 `l2l3` 丢掉了
`n*n - n` 个自由度，所以那里不存在这样的定理，也不可能存在。 -/
theorem weightLadderNFullWidth_has_inverse {n : ℕ} (hn : 0 < n) (s : List ℝ)
    (hlen : s.length = n * n + n) :
    FullWidth.listOfLayer hn (FullWidth.layerOfListFull (n := n) s) = s :=
  FullWidth.roundtrip hn s hlen

/-- **`l2l3` 读的是列表的哪些位置**：满宽版用满 `n*n + n` 个位置。

这一条把「为什么它可逆」写成可检查的事实：系数在 `i*n + j`，偏置在 `n*n + j`，
两个区间不重叠且覆盖 `[0, n*n + n)`。 -/
theorem weightLadderNFullWidth_l2l3_reads {n : ℕ} (s : List ℝ) (i j : Fin n) :
    ((weightLadderNFullWidth n).l2l3 s).head?.map
        (fun L => L.W i j) = some (s.getD (i.val * n + j.val) 0) ∧
      ((weightLadderNFullWidth n).l2l3 s).head?.map
        (fun L => L.b j) = some (s.getD (n * n + j.val) 0) :=
  ⟨rfl, rfl⟩

end Lattice.Lift.FullWidthLadder
