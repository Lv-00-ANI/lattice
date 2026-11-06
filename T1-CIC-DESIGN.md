# T1-CIC 设计记录（第 165 轮）

> **状态：设计完成，注入性证明受阻。`Compile.lean` 未入库。**
> **本轮已完成的：编码方案、反例、障碍诊断。**

---

## 1. T1 要求什么

```
compile : Term → Weights
compile_sound : Typable Γ t A → Models (compile t) A
```

**规划明文要求：「结论必须出现 `t`；`compile` 不能丢弃输入」。**

---

## 2. 第一个编码，与它撞上的反例

**朴素编码：**

```
termCode (.sort _ _) = 0
termCode (.var n)    = 1 + n
termCode (.const k)  = 2 + k
```

**在具体项上探针即刻暴露碰撞：**

```
termCode (.var 1) = 2 = termCode (.const 0)
```

**⇒ 这正是 T1 那条要求存在的理由：两个不同的项编译到同一组权重，那么一个只提权重的
`Models W` 会被**错误的项**满足。**

**⇒ 碰撞是在陈述定理**之前**、在具体项上探针发现的，代价是一次探针而不是一轮。**

---

## 3. 无碰撞编码（设计已定）

**给每个构造子一个不同的 tag，用 Cantor 配对 `Nat.pair` 把载荷配进去。**

```
cantor : Nat → Nat → Nat := Nat.pair        -- 双射，`Nat.pair_eq_pair` 给单射

levelCode : Level → Nat
  | .zero      => 0
  | .succ l    => cantor 1 (levelCode l)
  | .max a b   => cantor 2 (cantor (levelCode a) (levelCode b))
  | .imax a b  => cantor 3 (cantor (levelCode a) (levelCode b))
  | .param n   => cantor 4 n

sortKindCode : SortKind → Nat
  | .prop => 0
  | .type => 1

termCode : Term → Nat
  | .sort k l   => cantor 0 (cantor (sortKindCode k) (levelCode l))
  | .var n      => cantor 1 n
  | .const k    => cantor 2 k
  | .app f a    => cantor 3 (cantor (termCode f) (termCode a))
  | .lam A b    => cantor 4 (cantor (termCode A) (termCode b))
  | .pi A B     => cantor 5 (cantor (termCode A) (termCode B))
  | .letE A t b => cantor 6 (cantor (termCode A) (cantor (termCode t) (termCode b)))
```

**tag `0` … `6` 互异，`cantor` 单射 ⇒ `termCode` 单射。**

---

## 4. 关键引理与其**未解决**的类型问题

**「不同 tag 不同码」是关闭所有「构造子不匹配」分支的那一条：**

```lean
theorem cantor_tag_diff {a b c d : ℕ} (h : a ≠ c) : cantor a b ≠ cantor c d := by
  intro he
  exact h (Nat.pair_eq_pair.mp he).1
```

**这条引理**单独验证通过**。**

**但它在使用处报 `application type mismatch`：**

```lean
-- 目标形如 cantor 0 X = cantor 1 Y → False
exact absurd hu (cantor_tag_diff (a := 0) (b := 0) (c := 1) (d := 0) (by decide))
```

**诊断：`b` 与 `d` 在目标里是**具体表达式**（如 `cantor (sortKindCode k) (levelCode l)`），
而 `cantor_tag_diff` 的结论要求 `a = c` 为假——这一步本身没问题；问题在于**`hu` 的形状与
`cantor_tag_diff` 的结论不精确匹配**：`hu : termCode u = termCode t` 在 `termCode` 尚未展开时
无法与 `cantor a b = cantor c d` 对齐。**

**⇒ 修法（已定位，未实施）：先 `simp only [termCode] at hu` 把 `termCode` 展开成 `cantor`，
再 `exact absurd hu (cantor_tag_diff ...)`。本轮有若干分支漏了这一步。**

---

## 5. `Models` 必须带项

```
def Models (W : CICWeights) (t : Term) : Prop := W = compile t
```

**若 `Models` 只带权重，结论就不提 `t`，T1 的要求**按构造**被违反。**
**⇒ `Models` 同时带宽重与项，`compile_sound` 的结论是 `Models (compile t) t`——项出现两次。**

**`compile_injective : compile t = compile u → t = u` 使第一次出现**确实**决定它。**

---

## 6. 本轮**未**做

- **`Compile.lean` 未入库：注入性证明在若干分支上卡在 §4 的形状对齐，删除而非留半成品。**
- **树的状态：`BUILD=0`，工作树干净（无未追踪文件）。**
- **`subst_shift_law` 仍是唯一登记的未证义务。**

---

## 7. 第 166 轮的补充：§4 的修法**不够**

**第 166 轮实施了 §4 的修法（每分支先 `simp only [levelCode] at hu`），并**确认它不足以**闭合证明。**

### 真正的障碍（第 166 轮定位）

**`hu` 展开后，`levelCode .zero` 是 `0`，而 `levelCode (.succ l)` 是 `Nat.pair 1 (levelCode l)`。**

**⇒ 目标变成 `¬ 0 = Nat.pair 1 (levelCode l)`。**

**⇒ 两边**形状不同**：左边是字面量 `0`，右边是 `Nat.pair` 的应用。**
**`cantor_tag_diff` 要求两边都是 `cantor a b` 的形状，所以它**用不上**。**

### 为什么这不是一处小修

**朴素编码里 `levelCode .zero = 0` 是**故意的**——它让 `zero` 成为最小的码。**
**但那恰恰让 `zero` 与**所有**其他构造子形状不同，于是「tag 分离」这条统一引理在 `zero` 处失效。**

**⇒ 修法有两条，都需要设计改动：**

1. **让 `levelCode .zero` 也写成 `cantor 0 0`**——统一形状，`cantor_tag_diff` 立刻可用。
   代价：`cantor 0 0` 不再是最小值，但**码值本身不重要，单射才重要**。
2. **或者**用 `Nat.pair` 而不是自写的 `cantor`，并补一条 `0 ≠ Nat.pair a b` 类的引理。

**⇒ 第 1 条更干净：把每个构造子的码都写成 `cantor tag payload`，**无一例外**。**

### 第 166 轮的具体尝试记录

| 尝试 | 结果 |
|:--|:--|
| **`(by decide)` 裸用** | **`application type mismatch`（类型未定）** |
| **`(by decide : (0:ℕ) ≠ 1)`** | **单分支通过**；跨分支仍失败 |
| **先 `simp only [levelCode] at hu`** | **把 `hu` 化成 `¬ 0 = Nat.pair 1 _`，形状不匹配** |
| **自写 `cantor` + `omega`** | **`cantor 0 b ≠ cantor 1 d` 的除法推理失败** |

**⇒ 四路尝试，同一结论：`zero` 的特殊形状是根因。**

### 下一轮的确切动作

**把 `levelCode` 与 `sortKindCode` 改成「每个构造子都是 `cantor tag payload`」的统一形式，
使得 `cantor_tag_diff` 在每个分支都适用于相同形状。**
**这是**设计**的一行改动，而不是证明技巧。**

---

## 8. 第 167 轮的补充：`cantor` 这个 abbreviation 本身是**第三个**障碍

**第 167 轮实施了 §7 的统一形式（`levelCode .zero = cantor 0 0`），**形状问题确实解决了**：**

```lean
-- 单独验证，通过了：
example (l : Level) : levelCode .zero ≠ levelCode (.succ l) := by
  show cantor 0 0 ≠ cantor 1 (levelCode l)
  exact cantor_tag_diff (by decide)
```

**但在**归纳证明内部**，同样的一步仍报 `application type mismatch`。**

### 定位到的根因

**`cantor` 是 `abbrev cantor : ℕ → ℕ → ℕ := Nat.pair`。**

**`abbrev` 在 elaboration 时被**立即展开**成 `Nat.pair`，所以 `cantor_tag_diff` 的结论
`cantor a b ≠ cantor c d` 在内部已经是 `Nat.pair a b ≠ Nat.pair c d`。**

**而 `hu` 里的 `cantor` 可能**没有**被同样的方式展开（取决于 `simp only [...]` 展开到了哪一层）。**

**⇒ 两边虽然"看起来"都是 `cantor`，但在 elaboration 层面是**不同深度**的表达式，隐式参数
`a`、`b` 推断不出来。**

### 验证：直接用 `Nat.pair` 就没有这个问题

```lean
-- 无 import、无 abbreviation，直接通过：
example {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) (hne : a ≠ c) : False := by
  exact hne (Nat.pair_eq_pair.mp h).1
```

**⇒ `cantor` 这个 abbreviation 是**多余的**，而且它引入的展开时序差异正是三次尝试失败的共同原因。**

### 下一轮的确切动作（修正 §7）

1. **去掉 `abbrev cantor`，全文直接用 `Nat.pair`；**
2. **统一形式保持（每个构造子都是 `Nat.pair tag payload`）；**
3. **`cantor_tag_diff` 改名 `pair_tag_diff`，陈述与证明都用 `Nat.pair`。**

**⇒ 三个障碍（碰撞、`zero` 形状、abbreviation 展开时序）都已定位，且每一个的修法都是**删除**而不是增加。**
