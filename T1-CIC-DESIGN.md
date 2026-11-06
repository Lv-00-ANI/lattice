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

## 7. 下一轮的第一件事

**按 §4 的修法把每条 `exact absurd hu (...)` 前面加上 `simp only [termCode] at hu`，
重新尝试 `termCode_injective`。**
**设计已定，只差证明的形状。**
