# T3-CIC 设计记录（第 169 轮）

> **状态：设计完成，递归解码的终止性未解决。`Extract.lean` 未入库。**
> **本轮已完成的：往返定理的形态、两条解码路线、障碍的精确位置。**

---

## 1. T3 要求什么

```
extract : CICWeights → Option Term
extract_compile : extract (compile t) ≡β t
```

**规划的要求很具体，而且是对树里一处真实缺陷的纠正：**

> **「必须是定理，不是结构字段；避免 `Representation.roundtrip` 式投影」**

**`Representation.roundtrip` 是结构的一个**字段**，所以它按 `rfl` 成立、什么也没说。**
**⇒ T3 必须把往返做成关于**两个分别定义的函数**的定理。**

---

## 2. 为什么用 `Option`

**`extract` 定义在**所有**权重向量上，而绝大多数向量不是码。**
**⇒ `Option Term`：能解码给 `some t`，不能给 `none`。**

**⇒ 全函数性保留，部分性显式，而不是藏在一个默认值后面。**

---

## 3. 往返定理的形态（已确定）

**`termCode` 是 `Nat.pair tag payload`，所以解码是 `Nat.unpair` 后按 tag 分类。**

**由于 `termCode_injective`（第 168 轮已证）已经给出编码单射，**往返的数学内容是确定的**：**

```
decodeCode_termCode : ∀ t, decodeCode (termCode t) = some t
extract_compile     : ∀ t, extract (compile t) = some t
```

**且 `some t` 比 `≡β t` **更强**——它不拖进 `Reduction`。**

**⇒ T3 与 `Reduction` 无关：它是「权重记住项」这个语法事实。**
**恢复出的项是否**范式**，是 C1-7 的问题。**

---

## 4. 两条解码路线，与各自的障碍

### 路线 A：按 tag 结构递归（`decodeLevel` / `decodeSortKind` / `decodeCode`）

**自然、可计算，与 `termCode` 的结构一一对应。**

**障碍：终止性。**

**递归调用作用在 `(Nat.unpair m).1` 与 `(Nat.unpair m).2` 上，而**
**`Nat.unpair_lt : 1 ≤ n → (Nat.unpair n).1 < n` 只给**第一个**分量的界。**

**第二个分量**没有**同等形式的界——`Nat.unpair n).2` 可以比 `n` 小但证明需要**
**`Nat.unpair_right_le` 一类的引理，并且 `termination_by n` 的 `decreasing_by` 需要**
**同时处理两个分量。**

**第 169 轮在此处四次触发 `omega could not prove the goal`，随后出现 kernel 声明错误——**
**说明 `termination_by` 与 `decreasing_by` 的组合写法不对，而不只是算术不够。**

### 路线 B：`Classical.choose` 取 `termCode` 的逆

**最短：`if h : ∃ t, termCode t = n then some (choose h) else none`，**
**配合 `termCode_injective` 立刻得到 `decodeCode_termCode`。**

**障碍：`dif_pos` 需要 `Decidable` 实例，而更根本的问题是——**

**它**丢失可计算性**。**

**⇒ T3 的价值恰恰在于 `extract` 是一个**真的能跑的逆**。**
**一个用选择公理定义的 `extract` 虽然能让定理通过，却把「权重 ⇄ 符号」这条链的**逆向**做成了不可执行的东西。**

**⇒ 路线 B 不可接受，即使它更容易证。**

---

## 5. 下一轮的确切动作

**走路线 A，并把终止性写对：**

1. **先用一条**独立引理**把 `Nat.unpair` 两个分量的界都拿出来：**

   ```lean
   theorem unpair_fst_lt (n : ℕ) (h : 0 < n) : (Nat.unpair n).1 < n
   theorem unpair_snd_lt (n : ℕ) (h : 1 < n) : (Nat.unpair n).2 < n
   ```

   **第一条是 `Nat.unpair_lt`；第二条需要单独证。**

2. **`termination_by` 用 `n`，`decreasing_by` 里显式 `exact unpair_fst_lt _ _` 而不是 `omega`。**

3. **三个解码器分别证，不要再写一个大的 `decodeCode`。**

**⇒ 障碍已精确定位到 `decreasing_by`，而不是编码设计。**

---

## 8. 第 170 轮：四条**已确证**的事实，与一条**未证**的界

### 确证的

| # | 事实 | 状态 |
|--:|:--|:--|
| **1** | **`Nat.pair` 是**平方配对**：`pair a b = if a < b then b*b + a else a*a + a + b`** | **`#print` 确认** |
| **2** | **`Nat.pair 0 0 = 0`、`pair 0 1 = 1`、`pair 1 0 = 2`** | **`#eval` 确认** |
| **3** | **`Nat.unpair_left_le : (unpair n).1 ≤ n`、`Nat.unpair_right_le : (unpair n).2 ≤ n`** | **`#check` 确认** |
| **4** | **`Nat.unpair_lt : 1 ≤ n → (unpair n).1 < n`** | **`#check` 确认，且 `unpair_fst_lt` 随之得证** |

### 未证的

**`unpair_snd_lt : 0 < n → (unpair n).2 < n`。**

**七次尝试全部失败，最后一次的错误是 `linarith failed to find a contradiction`。**

**失败的原因是**证明策略**而不是事实：**

**`b ≤ n` 已知（事实 3，非严格），要升成 `b < n` 必须排除 `b = n`。**
**而 `b = n` 时，`n = pair a b` 展开（事实 1）为 `b*b + a` 或 `a*a + a + b`，两者都 `> n`——**
**但把这条链写成 `nlinarith` 能吃的形式，需要同时提供 `1 ≤ n`、`a < n`、`b = n` 与展开式，**
**而 `split_ifs at hp` 会破坏 `hp` 的形状，导致前提丢一个。**

**⇒ 下一轮的正确写法：**不**用 `split_ifs at hp`；而是**

```lean
rcases Nat.lt_or_ge a b with hlt | hge
· -- n = b*b + a
  have : n = b * b + a := by rw [Nat.pair, if_pos hlt] at hp; omega
  ...
· -- n = a*a + a + b
  have : n = a * a + a + b := by rw [Nat.pair, if_neg (by omega)] at hp; omega
  ...
```

**即**先按 `a < b` 分类，再用 `rw` 把 `hp` 换成显式等式**，而不是让 `split_ifs` 在处理 `hp` 时丢失前提。**

### 一条可能更省事的路

**事实 2 说明 `pair 0 0 = 0`。**

**⇒ 在**编码**里避免 `pair 0 _`：把每个 tag 从 `1` 开始，或者给每个码加 `1`。**
**这样任何**合法码**都 `> 0`，而 `0 < n` 的前提在解码时**总是**成立，`unpair_snd_lt` 的证明就只在 `0 < n` 下需要。**

**这不改变单射性（`termCode_injective` 不受影响），只让终止性证明的前提更干净。**

**⇒ 两条路都记下来，下一轮先试第二条（更省），不行再走第一条。**

---

## 6. 本轮**未**做

- **`Extract.lean` 未入库：递归解码的终止性未解决；删除而非留半成品。**
- **树的状态：`BUILD=0`，工作树干净。**
- **`subst_shift_law` 仍是唯一登记的未证义务。**

---

## 7. 与第 168 轮的关系

**第 168 轮的 `termCode_injective` **直接**给了 T3 的数学内容：**
**既然 `termCode` 是单射，那么「从码恢复项」是**唯一确定的**，剩下的只是把恢复过程写成可计算函数。**

**⇒ T3 的难度**不在**数学，而在 Lean 里写一个终止的递归解码器。**
**这一点值得记下来：前四轮（165–168）卡在编码设计，第五轮（169）卡在实现细节。**

---

## 9. 第 171 轮：`unpair_snd_lt` 的**前提本身是错的**

### 用 `#eval` 一次就查清了

```lean
#eval (List.range 30).map (fun n => ((Nat.unpair n).2, n))
-- [(0,0), (1,1), (0,2), (1,3), (2,4), ...]
```

**⇒ `n = 0` 时第二分量是 `0`（`0 < 0` 假），`n = 1` 时是 `1`（`1 < 1` 假）。**

**⇒ `unpair_snd_lt : 0 < n → (unpair n).2 < n` **本身是假的**。**

### 修正后立刻证出

```lean
theorem unpair_snd_lt {n : ℕ} (h : 2 ≤ n) : (Nat.unpair n).2 < n := by
  set a := (Nat.unpair n).1
  set b := (Nat.unpair n).2
  have hp : Nat.pair a b = n := Nat.pair_unpair n
  rcases Nat.lt_or_ge a b with hlt | hge
  · have he : n = b * b + a := by rw [Nat.pair, if_pos hlt] at hp; omega
    nlinarith
  · have he : n = a * a + a + b := by rw [Nat.pair, if_neg (by omega)] at hp; omega
    nlinarith
```

**⇒ 两次 `nlinarith` 闭合。**

**⇒ 第 169、170 轮的**八次**尝试全部失败，原因不是策略，而是**陈述错了**。**
**而 `#eval` 花了一次调用就查出来了。**

### 这印证了一条已有的纪律

**第 148 轮定的规矩是「写下陈述之前先在具体值上求值」。**
**第 171 轮把它用在了 `Nat.unpair` 的具体取值上，一次 `#eval` 就否证了**八轮**的工作假设。**

**⇒ 这条规矩的适用范围比之前以为的更宽：不只对**项**成立，对**辅助引理的假设**也成立。**

### 剩下的唯一障碍：`decreasing_by` 的上下文

**`unpair_snd_lt` 需要 `2 ≤ n`，而 `decreasing_by` 里拿不到这个前提：**

- **`match` 写法：`simp_wf` 之后目标仍缺 `2 ≤ n`，`omega` 报 `could not prove the goal`；**
- **`if` 写法：`deferred`，报 `failed to synthesize`（`Decidable` 实例）。**

**⇒ 下一轮的写法：在 `decreasing_by` 块里**显式构造** `2 ≤ n`，**
**用 `Nat.pair_unpair` 与 `match` 给出的等式（如 `n = Nat.pair 1 m`）作 `have`，再喂给 `unpair_snd_lt`。**

**具体地：**

```lean
decreasing_by
  · -- goal: (Nat.unpair m).2 < levelCode-code n, with n = Nat.pair 1 m
    have hn : n = Nat.pair 1 m := (Nat.pair_unpair n).symm.trans (by rw [hpat])
    have : 2 ≤ n := by omega
    exact unpair_snd_lt this
```

**其中 `hpat` 是 `match` 生成的 `(Nat.unpair n).1 = 1` 一类的等式。**

**⇒ 障碍已精确到「如何在 `decreasing_by` 里取出 `match` 生成的等式」。**
