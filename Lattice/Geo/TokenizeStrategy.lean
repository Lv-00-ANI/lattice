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

## 5. 第 120 轮：参数顺序调换**可行**，但撞上了另一个更基础的障碍

第 120 轮按 §4 的建议把 `dec` 改成 `List ℕ → ℕ → Option (...)`，**叶子层与 `dec` 的归约立刻通了**：

    dec_leaf : dec (enc (.leaf k)) (fuel + 2) = some (.leaf k, 2)     -- 编译通过
    dec (0 :: rest) (f + 2) 的 match 归约                              -- 编译通过

**参数调换是正确的**：`rw [dec.eq_def]; simp` 在列表在前时一次成功，不再需要
`simp only [tagX_eq, ...]` 这类技巧。

### 5.1 但二元层卡在 `omega` 的一个具体局限上

归纳步需要从 `h : 1 + encLen a + encLen b ≤ fuel` 得到 `2 ≤ fuel`。**`omega` 做不到**：

    example (a : Nat) : 2 ≤ 1 + a := by omega
    -- error: No usable constraints found.

**`omega` 无法证明不含假设的纯算术事实**——它需要至少一条前提才能启动。而
`obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩` 里的目标正是纯算术。

### 5.2 第 120 轮试过、但没走通的写法

| 写法 | 结果 |
|:--|:--|
| `omega` 直接证 `2 ≤ 1 + a + b` | ❌ No usable constraints found |
| `calc 2 ≤ 1 + a + b := by omega` | ❌ 同上（calc 的第一步仍是纯算术） |
| `Nat.le_add_right` + `Nat.le_trans` | ❌ 引理签名与目标形态不匹配，试了三种 |
| `Nat.succ_le_succ` 两次 | ❌ `1 + a + b` 需要先 `rw` 成 `Nat.succ (a+b)`，那条 `rfl` 不成立 |

### 5.3 下一次的正确起点

**不要要求 `omega` 证明纯算术事实，而是把那条事实本身写成一条 `Nat` 引理**，用最原始的组合子证：

    theorem one_add_add_le_two_add (a b : Nat) : 1 + a + b + 1 ≥ 2

或者更直接：**把 fuel 的上界假设写成 `encLen e + 1 ≤ fuel`**（而不是 `encLen e ≤ fuel`），
于是归纳步里的算术变成「已知 `1 + a + b ≤ fuel` 推出 `a + 1 ≤ fuel`」——**两个都带假设，`omega` 就能工作**。

**这是第 111 → 112 轮同一模式的第三次**：撞墙之后不要硬推，**改一个恒等价的表述**。

## 6. 第 121 轮：上面这个建议**是错的**，而且错在数学上

第 121 轮照着 §5.3 把上界改成 `encLen e + 1 ≤ fuel`，然后发现**证明进行不下去**。
排查到最后，`decide` 给出了决定性证据：

    example : 3 ≤ 1 + (1 + (0:Nat) + (0:Nat)) := by decide
    -- error: tactic 'decide' proved that the proposition is FALSE

`1 + (1 + 0 + 0) = 2`，**所以 `3 ≤ 2` 是假的**。

### 6.1 错误在哪

`dec` 消费的 token 数**恰好等于 `encLen e`**：

| 构造子 | `encLen` | `dec` 实际消费 |
|:--|--:|--:|
| `coord` | 3 | **3** |
| `const` | 2 | **2** |
| `add`/`sub`/`mul` | `1 + \|a\| + \|b\|` | **同** |

**所以正确的上界就是 `encLen e ≤ fuel`，不能加 1。** 加了 1 之后叶子层要求
`2 + 1 = 3 ≤ fuel`，而 `dec` 在 `fuel = 2` 时明明能成功——**这是一个自设的、不可满足的约束**。

### 6.2 由此得到的教训（本轮最有价值的部分）

**`omega` 在 §5.3 那些"失败"上其实是对的**：它在拒绝一个**假命题**。
第 120 轮的探针把 `omega` 报告成"有缺陷"，是因为**我一直没有用 `decide` 在小数值上核对命题本身的真假**。

> **当 `omega` 说"证不出来"时，第一件事应该是用 `decide` 在一个小实例上验证命题是否为真，
> 而不是怀疑 `omega`。**

第 120 轮记录了「`omega` 无法证明不含假设的纯算术事实」，**这个描述是对的**，
但**它对那些具体目标的"不能证明"是对的**——那些目标里有一部分确实是假的。

### 6.3 下一次的正确起点

回到 `encLen e ≤ fuel`，让 `omega` 在**有假设**的上下文里工作：

    obtain ⟨f, hf⟩ : ∃ f, fuel = f + encLen e := ...     -- 保留 encLen，不展开成算术
    subst hf                                              -- 然后 dec 的 fuel 就是字面形态

**关键差别**：第 120 轮把 `fuel` 分解成 `f + 2` 这种**与 `encLen` 无关的常数**，
于是归纳步要证 `encLen a ≤ f + 1`，而 `f` 与 `encLen a` 之间没有已知关系。
**分解成 `f + encLen e` 则直接给出需要的形态。**

## 7. 第 122 轮：找到了真正缺失的那条引理，但没能把它用进证明

### 7.1 缺失的引理：`encLen_ge_two`

第 109–121 轮的二元节点归纳步都要从 `h : 1 + encLen a + encLen b ≤ fuel` 推出 `2 ≤ fuel`。
第 122 轮**先用 `decide` 验证这个推理是否为真**，结果是：

```
example : (2 : Nat) ≤ 1 + 0 + 0 := by decide
-- error: tactic 'decide' proved that the proposition is FALSE
```

**⇒ 这个推理本身是假的。** 缺的正是一条下界引理：

    theorem encLen_ge_two (e : SExpr n) : 2 ≤ encLen e

**这条引理在各 `dec` 版本下都成立**（`coord` 给 3、`const` 给 2、二元节点是 `1 + 左 + 右`），
**但十二轮里没有一轮陈述过它。**

### 7.2 为什么还是没证成

加了下界引理之后算术通了，但 `dec` 的 `match` 归约又成了障碍：

| 尝试 | 结果 |
|:--|:--|
| `rw [dec.eq_def]; simp` | `maximum recursion depth` —— `eq_def` 里仍含 `dec`，无限展开 |
| `simp only [Nat.add_one, if_pos rfl]` | `simp made no progress` |
| `simp only [Nat.add_one, tags...]; rw [if_pos rfl]` | 未走到这一步 |

**根源**：`dec.eq_def` 展开成 `match x, x_1 with`，要归约需要 `x` 和 `x_1` **同时**是构造子形态；
而 `simp` 一旦看到 `dec.eq_def` 就会重新展开内部的 `dec`，因此递归不收敛。

### 7.3 下一次的正确起点

**不要用 `dec.eq_def`。** 改为**手动写 `dec` 的方程引理**（`dec` 在 tag-0 分支上的具体值），
把"展开"变成"重写"：

    @[simp] theorem dec_add_eq (fuel : Nat) (a b : List Nat) :
        dec (0 :: (a ++ b)) (fuel + 1) = <展开后的 match>

这样 `simp` 看到的是**一条重写规则**，而不是一个会递归展开的定义。

## 8. 第 123 轮：③ 的解法找到并验证通过了，但整体仍未闭合

第 122 轮把障碍分解成三个子问题。第 123 轮只做 ③（`dec` 的归约），**并把它解决了**。

### 8.1 已验证的解法：手写方程引理（不用 `dec.eq_def`）

```lean
@[simp] theorem dec_bin_eq (k : Nat) (d : Nat) (rest : List Nat) :
    dec (0 :: (d :: rest)) (k + 1) =
      (match dec (d :: rest) k with
       | some (x, c₁) =>
           match dec ((d :: rest).drop c₁) k with
           | some (z, c₂) => some (.bin x z, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rfl
```

**这条在探针里编译通过**。关键性质：

| 项 | `dec.eq_def` | 手写引理 |
|:--|:--|:--|
| 证明 | 自动生成，含 `match x, x_1` | **`rfl`**，因为 `k+1` 已是构造子形态 |
| 用作重写 | 会递归展开内部的 `dec`，不收敛 | **只重写一次，收敛** |
| 匹配条件 | 要求两个参数都已是构造子 | 只要列表是 `0 :: d :: rest` |

**这是子问题 ③ 的答案。**

### 8.2 还差的一步：把任意非空列表喂进去

`dec_bin_eq` 要求列表字面是 `0 :: (d :: rest)`，而真实目标是
`0 :: (enc a ++ enc b ++ suffix)`——**`enc a ++ ...` 是 cons，但语法上不是**。

第 123 轮写了 `dec_bin_eq'`（对任意 `L : List Nat`, `L ≠ []` 成立，由 `cases L` 证），
它编译通过并把目标推到只剩最后三个重写：

```
rw [dec_bin_eq' ...]
rw [iha ...]
rw [ihb ...]
```

**但这三步之间的 `List.drop` 与 `enc_length` 配合没有调通**，第 123 轮结束时仍未闭合。

### 8.3 下一次的正确起点

**三个子问题里两个已解决：**

| 子问题 | 状态 | 出处 |
|:--|:--|:--|
| ① 参数顺序（列表在前） | ✅ 已解决 | 第 120 轮 |
| ② `encLen_ge_two` | ✅ 已解决 | 第 122 轮 |
| ③ `dec` 的归约（手写方程引理） | ✅ **已解决** | **第 123 轮** |
| ④ 把 ③ 用到 `enc a ++ ...` 上 | ⚠️ **唯一剩余** | — |

**下一次尝试只需要处理 ④**，而且 ④ 是纯重写顺序问题：`dec_bin_eq'` 之后，
目标里的 `dec (enc a ++ (enc b ++ suffix)) (f+1)` 必须与 `iha` 的结论
`dec (enc a ++ (enc b ++ suffix)) (f+1) = some (a, encLen a)` **逐字匹配**——
所以 `rw [iha]` 之前不能有任何改变该子项的步骤。

## 9. 第 124 轮：④ 的障碍被精确定位成一个**括号形态**问题

第 124 轮做第 10 次尝试，把目标推到了只剩一处形态不匹配：

```
当前目标：  dec (0 :: (enc a ++ enc b) ++ suffix) (f + 2) = ...
需要形态：  dec (0 :: (enc a ++ (enc b ++ suffix))) (f + 1 + 1) = ...
```

**原因是运算符优先级**：Lean 把 `0 :: enc a ++ enc b ++ suffix` 解析成
`0 :: ((enc a ++ enc b) ++ suffix)`——`::` 比 `++` 结合更紧。
而 `dec` 的方程引理要的是 `0 :: (y :: rest)` 形态，其中 `y :: rest` 必须是**已经结合好的列表**。

### 9.1 需要的引理与方向

`List.cons_append : (a :: l₁) ++ l₂ = a :: (l₁ ++ l₂)`，

**但目标里已经是 `0 :: (X ++ Y)`，需要的是反向**：把 `0 :: ((enc a ++ enc b) ++ suffix)`
变成 `(0 :: (enc a ++ enc b)) ++ suffix` 再变回 cons——**这条路径绕**。

**更直接的做法**：先 `rw [List.append_assoc]` 把 `(enc a ++ enc b) ++ suffix` 化成
`enc a ++ (enc b ++ suffix)`（这一步第 124 轮做了，但没有先解开 `0 ::` 的括号），
**再做 `dec_bin_eq'`**。

### 9.2 第 124 轮实际做到哪一步

| 步骤 | 状态 |
|:--|:--|
| `encLen_ge_two`（第 122 轮那条）**改用归纳假设** | ✅ 这是本轮发现的一个错误：第 122 轮写的版本用 `two_le_one_add`，**而 `2 ≤ 1 + x` 在 `x = 0` 时是假的** |
| 叶子分支 | ✅ 通过 |
| `dec_bin_eq'` 的应用 | ✅ 通过 |
| `iha` 的应用 | ✅ 通过 |
| 最后一步的括号形态 | ❌ **未调通** |

**注意 9.2 的第一行**：第 122 轮记录的 `encLen_ge_two` **证明是错的**（用了假命题），
本轮的修正是**用归纳假设**：

```lean
theorem encLen_ge_two (e : E) : 2 ≤ encLen e := by
  induction e with
  | leaf k => show 2 ≤ 2; exact Nat.le_refl 2
  | bin a b iha ihb =>
      show 2 ≤ 1 + encLen a + encLen b
      have h1 : 2 ≤ encLen a := iha
      have h2 : 2 ≤ encLen b := ihb
      omega
```

**这条修正后编译通过。** §8.1 的记录因此需要更新：第 122 轮写的那版**不成立**。

## 10. 本文的边界

- **不含任何声明**，对构建与既有定理零影响。
- 第 119–124 轮结束时 `ConstraintTokenizer` 的状态与第 112 轮结束相同：
  **叶子层完成，二元层开放**。
- 探针文件在 `agent-tmp/probe_*.lean`，不纳入构建。
- **§5.3 的建议已被 §6 推翻，不要照着做。** §6.3 是替代方案。
- **§7.1 的陈述正确但证明需要 §9.2 的修正版**（用归纳假设，不用 `2 ≤ 1 + x`）。
- **§8.1 的手写方程引理是可复用的成果**，已在探针里编译通过。
- **§9.1 的括号形态是 ④ 的唯一剩余障碍。**
- **第 120 轮的探针证明了参数调换是对的**（`dec_leaf` 编译通过），所以下一次不必再验证这一部分。
-/