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
