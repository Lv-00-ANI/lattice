# `layerWords_injective`：第 22 轮把卡点缩小到**一条 `omega` 目标**

> **第 22 轮。** 本文档记录对 `CInterface/Serialization` 的两条取回引理与单射的第二次尝试。
> **本轮没有代码改动**（尝试被回滚）。但**卡点从「不知道怎么写」变成了「一条具体的 `omega` 目标」**。

---

## 1. 第 18 轮留下的三个障碍

| 障碍 | 当时的错误 |
|:--|:--|
| `List.getElem_append_left` 不匹配 | `rw` 找不到 `(?l ++ ?l')[?i]` |
| 同上，`_right` | 同上 |
| 单射 | `rw [h] at h₁` → **`motive is not type correct`** |

---

## 2. 本轮读调用点得到的三条结论（**这些都成立，且已验证**）

### 2.1 `getElem_append_left` 不需要先转 `get_eq_getElem`

我先按 mathlib 的用法（`ModelTheory/Encoding.lean`：`rw [get_eq_getElem, getElem_append_left, getElem_map]`）
加了 `get_eq_getElem`，Lean 报 **`did not find instance of ?l.get ?i`**——说明
**`List.getD_eq_getElem` 之后目标已经是 `[i]` 记法**，再加 `get_eq_getElem` 反而把目标改回去了。

**结论：`rw [List.getElem_append_left (by …), List.getElem_map, List.getElem_finRange]` 就是对的形状。**

### 2.2 单射用**解码器**，不用依赖重写

第 18 轮 `rw [h] at h₁` 失败的根因是**那条等式的索引依赖 `L`**。
改成：

```lean
noncomputable def wordsLayer {k : ℕ} (w : List ℝ) : AffineLayer (Fin k) where
  W i j := w.getD (i.val * k + j.val) 0
  b j   := w.getD (k * k + j.val) 0

theorem layerWords_injective {k : ℕ} : Function.injective (layerWords (k := k)) := by
  intro L₁ L₂ h
  have h' := congrArg (wordsLayer (k := k)) h
  rwa [wordsLayer_layerWords, wordsLayer_layerWords] at h'
```

**`congrArg` 作用在列表相等上，得到的两个等式全是层的等式**——没有依赖重写。
（`congrArg` 必须写 `(wordsLayer (k := k))`，否则 `β` 无法推断，报 *don't know how to synthesize implicit argument 'β'*。）

### 2.3 `Nat.mul_add_div` / `Nat.mul_add_mod` 要求**乘数在前**

我的项是 `i.val * k + j.val`，而两个引理的形状是 **`k * x + y`**。
所以必须先 `rw [Nat.mul_comm i.val k]`，否则报
**`did not find instance of (k * ?x + ?y) / k`**。

### 2.4 侧条件需要的是 **`W` 段**的长度，不是总长度

`getElem_append_left` 的侧条件是 `i*k + j < (W 段).length = k * k`，
而我第一版给的是 `idxW_lt : i*k + j < k*k + k`（总长度）→ **`type mismatch`**。
`idxW_lt` 必须收紧成 `< k * k`。

---

## 3. 唯一剩下的卡点：**一条 `omega` 目标**

收紧 `idxW_lt` 之后，最后一个未过的目标是它的 `calc` 最后一步：

```lean
theorem idxW_lt {k : ℕ} (i j : Fin k) : i.val * k + j.val < k * k := by
  have hi : i.val + 1 ≤ k := by have := i.isLt; omega
  have hj : j.val < k := j.isLt
  calc i.val * k + j.val < i.val * k + k := by omega
    _ = (i.val + 1) * k := by ring
    _ ≤ k * k := Nat.mul_le_mul_right k hi
```

**报错**：`omega could not prove the goal`，上下文里只有 `a := ↑k * ↑k`，
提示 `omega` 拿到的目标**不是**我以为的那个。

**下一次的确切起点**：把那条 `calc` 拆成三条**独立的 `have`** 各带显式 `show`，
用 `#check` 确认 `Nat.mul_le_mul_right` 的**参数顺序**（它是 `a ≤ b → a * c ≤ b * c`，
所以 `Nat.mul_le_mul_right k hi` 里 `k` 是**乘数**，`hi : i.val + 1 ≤ k` 是被乘的不等式——
**这条我可能一直是反的**）。或者干脆改用
`nlinarith [i.isLt, j.isLt]`（把 `ℕ` 先 `cast` 到 `ℤ`）。

**这是本会话里第三次「卡点缩到一条引理的一句话」**（前两次：`pi_norm_le_iff_of_nonneg` 的用法、
`Ls` 的 sup-范数提升）。**前者下一次就过了。**

---

## 4. 为什么本轮仍然不发布

能编译的版本只差**一条 `idxW_lt`**。但：

- 若把 `idxW_lt` 写成**未证的假设**，`layerWords_injective` 就是**假造的无损性**——
  那正是本项目一直在清的那种东西；
- 若不写取回引理、只留 `layerWords_length`，那就是**第 18 轮已有的内容**，本轮零新增。

**所以回滚，留下 §2 那四条已验证的结论。** 它们不是感想——**每一条都是 Lean 的报错逼出来的**，
而且**下一条命令就能用**。

---

## 5. 本轮的净产出

- ✅ **四条已验证的技术结论**（§2.1–2.4），全部可直接用于下一次尝试；
- ✅ **卡点缩小**：从「不知道怎么写」到「一条 `omega` 目标 + 一条可能反了的参数顺序」；
- ❌ **代码**：零（回滚）。

**`register` 计数不变**——这一条没有关闭。
