/-
# 第 119 轮探针结论：`match` 归约的正确 tactic 顺序

本文是一个**只含注释的 Lean 文件**：它不含任何声明，因此对构建、对任何定理都零影响。
存在它的唯一理由是让下一次尝试不必从零开始。

## 0. 五次失败，第 119 轮才定位到原因

第 109 / 111 / 113 / 118 / 119 轮**五次尝试**补 `ConstraintTokenizer` 的二元节点往返。
前四次失败时不知道卡在哪；第 119 轮用一个只含 `Nat` 与 `List` 的探针把它定位成了
**一个具体的 tactic 顺序问题**。

## 1. `dec` 在 `tagAdd :: (y :: rest)` 上求值需要三步归约

| 步骤 | 障碍 | 解法 |
|--:|:--|:--|
| 1 | `fuel + 1` 不是构造子形态，`match` 不动 | 传字面 `k + 1`，或先 `rw` 成 `(k+1)+1` |
| 2 | `if 2 = tagCoord` 里的 `tagCoord` 是 `def`，不展开 | **`simp only [tagAdd_eq, tagCoord_eq, tagConst_eq]`** |
| 3 | 剩余的数值 `if` | `norm_num` |

**第 2 步是五次失败的关键。** 第 118 轮用的是 `simp only [if_pos rfl]` 和
`simp only [Nat.add_one, Nat.reduceAdd, ...]`，**这些受限集合排除了 `tagX_eq` 那些 `@[simp]` 引理，
而它们正是让 `if` 归约的东西。**

## 2. 探针里已经编译通过的形态

    theorem add_step (k y : Nat) (rest : List Nat) :
        dec (k + 1) (tagAdd :: (y :: rest)) = <展开后的 match> := by
      rw [dec.eq_def]
      simp only [tagAdd_eq, tagCoord_eq, tagConst_eq]
      norm_num

**结尾不要加 `rfl`**（第 119 轮加过，报 "no goals to be solved"）。

## 3. 还缺什么

`add_step` 只处理**字面 `tagAdd :: (y :: rest)`**。真实目标里的列表是
`enc a ++ enc b ++ suffix`，**语法上不是 `y :: rest`**，所以不能直接 `rw [add_step]`。

第 119 轮试过但没成功的方向：

| 方向 | 问题 |
|:--|:--|
| 加辅助引理 `dec_add_step_of (L) (hne : L ≠ [])` | 辅助引理必须定义在 `dec_add_step` 之后、使用处之前，需要调整定理顺序 |
| 对 `enc a` 做 `cases` | `enc a` 依赖 `a`，需先对 `a` 做 `cases`，与归纳假设冲突 |
| 走 `enc_is_cons` 存在性引理 | 给出的 `y`/`rest` 重写进目标后与归纳假设形态不匹配 |

## 4. 下一步的正确起点：调换 `dec` 的参数顺序

建议改成 `dec : List Nat → Nat → Option (...)`（**列表在前，fuel 在后**）。

理由：`dec` 的模式匹配在**列表**上（`[]` / `[_]` / `t :: d :: rest`），fuel 只作上界。
**列表在前时，对 `enc a ++ ...` 做 `cases` 才能生效**；
第 119 轮的全部困难都来自「列表在第二个位置，无法对其做 `cases`」。

这与第 112 轮是同一课：第 111 轮诊断出「换表示」是出路，第 112 轮换了 `dec` 的**返回类型**，
一次成功。**这次该换的是参数顺序。**

## 5. 本文的边界

- **不含任何声明**，对构建与既有定理零影响。
- 第 119 轮结束时 `ConstraintTokenizer` 的状态与第 112 轮结束相同：叶子层完成，二元层开放。
- 探针文件在 `agent-tmp/probe_dec_bin*.lean`，不纳入构建。
-/
