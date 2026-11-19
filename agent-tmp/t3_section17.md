
---

## 17. 第 976 轮：**P1-8 闭合**，以及十二轮究竟缺了什么

### 17.1 结果是可计算的

**审计的措辞是：**

> **`decode : ℕ → Option IRSkeleton`，对**不是**任何骨架的码返回 `none`。**

**两个方向现在都有定理，且**解码器可计算**（不是 `Classical.choose`）：**

| 方向 | 定理 | 位置 |
|:--|:--|:--|
| **码 → 骨架** | **`decodeSkeletonStrict_code : decodeSkeletonStrict (skeletonCode k) = some k`** | `Core/IR/DecodeStrictAll.lean` |
| **非码 → `none`** | **`decodeSkeletonStrict_none_of_not_code`** | 同上 |
| **忠实（中间形式）** | **`decodeSkeletonStrict_faithful : decodeSkeletonStrict n = some k → skeletonCode k = n`** | 同上 |

**`decodeSkeletonStrict n := strictly decodeSkeleton skeletonCode n`，而**

```lean
def strictly (f : ℕ → Option α) (enc : α → ℕ) (n : ℕ) : Option α :=
  match f n with
  | some a => if enc a = n then some a else none
  | none   => none
```

**即「解码后按编码回验，码不符即丢弃」。**

### 17.2 十二轮真正缺的那一步

**§1–§16 全部在攻**终止性**：`decodeListCode` 的递归落在 `(unpair n).2` 上，
而 Mathlib 只给 `≤` 而非 `<`；项目里的严格版本带 `2 ≤ n` 前提（§3.2）。**

**=> 那些障碍是真实的，但它们只属于**「手写一个忠实解码器」**这条路。**

**而第 973 轮的 `decodeTensorShape_not_faithful` 揭示了一件更基础的事：**

> **现有解码器**根本不看码的第二分量**（`tensorShapeCode t = Nat.pair (… + 1) 0` 的第二分量恒为 `0`）。**

**=> 所以缺的不是算术，而是**一道回验**。**

**=> 加上这道回验（`strictly`）之后：**
- **忠实性成为**定义的三行推论**（`strictly_faithful`，**零前提**）；**
- **「不丢码」只需各层已有的 `_code` 定理（`strictly_of_code`，一条通用定理覆盖六层）。**

### 17.3 代价，以及为什么不隐藏它

**`strictly` 在每次成功解码时**再跑一遍编码器**，故比手写守卫慢一个常数倍。**

**=> 这是**用时间换可证明性**的显式取舍。**
**=> 若将来某个调用点对常数敏感，应在那里手写守卫并重证忠实性；
本文件第 1–16 节记录的正是那条路的代价。**

### 17.4 对前 16 节的处置

**不删除。它们记录了**真实的**数学障碍（`unpair` 的严格界、`Nodup`/`List.find?` 的形式问题、
`walk_*` 的归纳假设形状），这些障碍在手写路线下依然成立。**

**=> 但它们**不再是 P1-8 的前置条件**。读法：**

| 想做的事 | 读哪几节 |
|:--|:--|
| **直接拿到 P1-8 的结论** | **只看 §17** |
| **手写一个更快的忠实解码器** | **§1–§5（终止性）+ §3.2（已有的 `unpair_snd_lt`）** |
| **理解 `decodeRelations` 为何那么长** | **§7 + §9–§16** |

### 17.5 一条方法论教训（写给下一个轮次）

**这份文档开头那句「代码未写」存活了 **770 轮**（第 206 轮代码就已经写好了），
并在第 972 轮**实际误导了我**：我据此打算重新实现一个已存在的解码器。**

**=> 教训：设计文档的状态行必须**在状态改变时同步更新**，
否则它比没有文档更危险——它会把「已解决」显示成「未解决」。**

**=> 本项目现在的做法：`PLAN-STAGES.md` 是**唯一**可执行的台账，
任何设计文档若与它冲突，以台账为准并**更新设计文档的状态行**。**
