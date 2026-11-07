# `T3-DECODE-DESIGN.md` -- why `decode : Nat -> Option IRSkeleton` needs real arithmetic (round 204)

> **状态：** 设计记录。**代码未写，且这一轮证明了「写起来很简单」是错的。**
> **定位：** 记录第 204 轮试图实现审计 P1-8 时遇到的确切障碍，使下一个独立轮次不必重新发现。

---

## 1. 缺口

`Core/IR/Skeleton.lean` 有：

```lean
noncomputable def extractCode (W : IRWeights) : Option ℕ :=
  some (weightCodeIR W)
```

**它恒返回 `some`，因此不是一个解码器：任何 `Nat` 都会「提取」出某个东西。**

审计的 P1-8 要求 `decode : ℕ → Option IRSkeleton`，对**不是**任何骨架的码返回 `none`。

---

## 2. 编码器链

```lean
def listCode : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.pair (x + 1) (listCode xs)

def tensorShapeCode (t : TensorShape) : ℕ :=
  Nat.pair (Nat.pair t.id (listCode t.shape) + 1) 0

def skeletonCode (k : IRSkeleton) : ℕ :=
  Nat.pair (shapesCode tensorShapeCode k.tensors + 1)
           (shapesCode relationShapeCode k.relations)
```

**每个都是 `Nat.pair` 的嵌套。**

---

## 3. 障碍：终止性需要 `Nat.pair` 的真实算术

**自然的定义是：**

```lean
def decodeListCode (n : ℕ) : List ℕ :=
  if n = 0 then []
  else (Nat.unpair n).1 - 1 :: decodeListCode (Nat.unpair n).2
```

**递归调用在 `(unpair n).2` 上，所以必须证明 `(unpair n).2 < n`。**

### 3.1 Mathlib 给的是非严格的

| 引理 | 内容 |
|:--|:--|
| **`Nat.unpair_left_le`** | **`(unpair n).1 ≤ n`** |
| **`Nat.unpair_right_le`** | **`(unpair n).2 ≤ n`** |

**都是 `≤`。递归需要 `<`。**

### 3.2 项目里已有的严格版本带 `2 ≤ n` 前提

`Lattice/Core/CIC/PairBounds.lean` 有：

```lean
theorem unpair_snd_lt {n : ℕ} (h : 2 ≤ n) : (Nat.unpair n).2 < n
```

**它的前提是 `2 ≤ n`，而 `decodeListCode` 从 `n ≠ 0` 只能得到 `1 ≤ n`。**

**=> 两者的差是真实的一格：`n = 1` 时 `unpair 1 = (1, 0)`，`0 < 1` 成立但 `2 ≤ 1` 不成立。**

### 3.3 补这一格需要的算术

**需要证：`(unpair n).2 < n` 对 `n ≥ 1` 也成立。**

**手推是容易的：`n = pair a b ≥ a*a + a`（当 `a ≤ b`）或 `≥ a*a + a + b`（当 `a > b`），且 `b ≤ pair a b`。若 `b ≥ n` 则 `pair a b ≥ n` 且 `b ≤ pair a b = n`，故 `b = n`，于是 `pair a n = n`，这在 `a ≥ 1` 时不可能因为 `pair a n ≥ a*n + ...`。**

**但 `omega` 和 `nlinarith` 都证不出来：`Nat.pair` 是带 `if` 的分段二次函数，两个策略都把它当不透明项。**

**=> 需要显式展开 `Nat.pair` 的 `if` 分支，先对 `a ≤ b` 与 `a > b` 分情形，再在每个分支里用 `nlinarith`。**

**这不是一两行，而是一个需要认真做的引理。**

---

## 4. 更根本的问题：`decode` 的**值域**不需要 `unpair` 的严格界

**关键观察：如果 `decode` 只在**已知是 `listCode` 的像**的码上被调用，那么每次递归的值都是 `Nat.pair (x+1) _` 的形式，其第一个分量 `≥ 1`，于是 `n ≥ 2` 直接成立。**

**=> 正确的定义方式不是「对任意 `Nat` 递归」，而是「对 `pair` 形式递归」：**

```lean
def decodeListCodeAux : (x : ℕ) → (rest : ℕ) → List ℕ
  | x, rest => (x - 1) :: decodeListCode rest
```

**这样终止性来自 `rest` 是 `listCode` 的**子项**，而子项严格小于父项是 `listCode` 的构造性质，不需要 `unpair` 的界。**

**=> 这需要把「`decode` 定义在像上」变成类型层面的陈述，而不是靠 `if n = 0` 兜底。**

---

## 5. 结论与下一步

**审计说「`Nat.unpair` 现成，不需要 fuel」——这句话对**值域**是对的，对**终止性证明**不成立。**

**下一步的两个候选：**

| 路线 | 内容 | 成本 |
|:--|:--|:--|
| **A** | 先证 `unpair_snd_lt_of_one : 1 ≤ n → (unpair n).2 < n`，显式分 `a ≤ b` / `a > b` 两支 | **中，一个引理 + 两个分支的 `nlinarith`** |
| **B** | 把 `decode` 定义在 `pair` 形式的结构递归上（`decodeListCodeAux`） | **中，但定义更贴合编码器的形状** |

**=> 路线 A 更小，路线 B 更正确。下一轮应当先试 A（一个引理），若阻塞再转 B。**

**本轮不提交任何 `Decode.lean`：未完成的文件不留半成品，这是项目的纪律。**

---

## 6. 第 205 轮的补充：路线 A 的分支算术确认

**实际尝试了 unpair_snd_lt_of_one，得到两个具体结论：**

| 发现 | 内容 |
|:--|:--|
| **obtain ⟨a,b⟩ := Nat.unpair n 之后** | **hpair : Nat.pair (unpair n).1 (unpair n).2 = n 里的投影写法不会被 simp only 化简成 /** |
| **两个分支都是非线性** | ***b + a = n 与 *a + a + b = n，omega 全程无法处理；
linarith 需要正确的假设集** |

**=> 路线 A 的成本从「一个引理」上调为「一个引理 + 两个分支的非线性算术」，因为 Nat.pair 的二次分支不能靠
omega 跨越。**

**=> 这让路线 B（在 pair 形式的结构递归上定义 decode）更有吸引力：它绕开整个界问题，代价是定义形状偏离

at.rec。**

**下一轮应当在路线 B 上投入，而不是继续在路线 A 的非线性算术上打转。**

---

## 7. 第 209 轮：`decodeRelationShape` 的第三层障碍

**本轮尝试把 `decodeRelationShape` 补齐（`relationShapeCode` 有三个分量：`kindCode`、`argsCode`、`partCode`）。**

### 7.1 已完成的部分

| 分量 | 逆 | 状态 |
|:--|:--|:--|
| **`kindCode`** | **`kindOfCode` / `kindOfCode_kindCode`** | **第 208 轮已证** |
| **`listCode`（在 `argsCode` 内）** | **`decodeList` / `decodeList_code`** | **第 207 轮已证** |
| **`partCode`** | **`partOfCode` / `partOfCode_partCode`** | **本轮写出并通过 `lean` 检查** |

**`partOfCode` 是四个标签的匹配（`none` + 三个 `PartKind`），`partOfCode_partCode` 逐分支 `simp` 即可。**

### 7.2 未完成的部分与确切原因

**`argsCode` 的列表解码器没写出来。**

**`argsCode` 的构造是 `Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode rest)`，比 `tensorShapeCode` 多一层内层
`pair`。**

**失败点精确记录：** 在归纳步里 `rw [Nat.add_sub_cancel]` 之后，目标中仍含有 `map` 包裹的递归调用
`decodeArgsAux k u.2`，而：

| 已尝试 | 结果 |
|:--|:--|
| **`dsimp only`** | **"made no progress"——`let` 绑定的 `u` 尚未归约** |
| **`rw [ih k …]`** | **失败——递归调用在 `map` 内部，`rw` 够不到** |
| **`simp only [...]`** | **同样无法穿透 `let` + `map` 的嵌套** |

**=> 正确的做法是先用 `obtain`/`simp only` 把 `let u := Nat.unpair n` 的 `u` 换成它的分量，再 `rw`。这是与
`decodeTensorListAux_code` **不同**的证明形状——后者没有 `let` 绑定。**

### 7.3 一个文件级的教训

**本轮还遇到一个纯语法问题：docstring 里写了 `` `obtain`/`simp only` ``，其中的 `/` 与前面的 `-` 在某些位置构成
`-/`，提前闭合了注释块，导致后续声明报 "unexpected token"。**

**=> 在 docstring 里避免连续出现 `/` 与 `-` 的组合；写成 "A 与 B" 而不是 "A/B"。**
**这条已在本会话中重复出现，值得写进 `CONVENTIONS` 的注释规范。**

### 7.4 交付状态

**`DecodeSkeleton.lean` 本轮创建后删除——其中的 `decodeArgsAux_code` 未闭合，按项目纪律不留半成品。**

**工作树干净，`BUILD=0`，全部门禁绿。**

**下一轮应当：先把 `let` 归约（`obtain ⟨a, b⟩ := Nat.unpair n` 后 `rw`），再套用 `decodeTensorListAux_code` 的
归纳骨架。**

---

## 8. 第 215 轮：`parse` 接线的前置条件，与一条审计指控的澄清

### 8.1 审计的 P1-6 指控中，有一条不成立

**审计说 `walkWithRelations` 的 `letE` 分支「用 `n+1` 而非 `n1`，所以 `letE` 的边指向错误张量」。**

**实测两者同构：**

```
| Term.app f a, n =>
    let (tf, rf, n1) := walkWithRelations f (n + 1)
    let (ta, ra, n2) := walkWithRelations a n1
    ...
| Term.letE _ t b, n =>
    let (tt, rt, n1) := walkWithRelations t (n + 1)
    let (tb, rb, n2) := walkWithRelations b n1
    ...
```

**两处的首个子项都用 `n+1` 作为起点，`letE` 的 `b` 从 `n1` 开始，`app` 的 `a` 也从 `n1` 开始。**
**=> 结构完全一致，不存在把 `n1` 写成 `n+1` 的错误。**

**审计的这一条判断错了。它看出「`n+1` 与 `n1` 是两个不同的东西」，这观察是对的；但结论「所以 `letE` 错了」不成立，因为 `app` 用的是同一个模式。**

### 8.2 真正的前置条件

**要让 `parse` 用 `parseSkeletonWithRelations` 并保持 `parse_wellFormed`，需要两条不变式：**

| 不变式 | 内容 | 状态 |
|:--|:--|:--|
| **值域** | **`w := walkWithRelations t n`，则 `∀ s ∈ w.1, n ≤ s.id < w.2.2`** | **未证** |
| **单调** | **`n ≤ (walkWithRelations t n).2.2`** | **未证** |

**两条都靠对 `t` 的归纳，但归纳假设必须写成 `generalizing n` 的形式——因为 `walkWithRelations` 的递归把 `n+1` 递给子项，而子项的归纳假设需要作用在**任意**起点上。**

**第 215 轮尝试了 `induction t with`（不带 `generalizing n`），归纳假设被固定在最初的 `n` 上，于是 `ihf (n+1)` 类型不匹配。**
**=> 正确的形状是 `induction t generalizing n with`，且每次对 `walkWithRelations ... n` 先 `obtain` 出三元组，再让 `omega` 在三个计数器上工作。**

### 8.3 为什么没做完

**`induction t generalizing n` 之后，`app`/`letE` 分支的目标里包含两层的 `let` 与 `++`，`simp only [walkWithRelations]` 展开后的形式与 `obtain` 出的三元组对不上，`omega` 因此拿不到可用的不等式。**

**=> 这与 `argsCode` 的情况相同：**先归约再重写**，而且必须先让 `let` 绑定在目标里显形。**
**第 210 轮解决 `argsCode` 用的正是「先 `rw [hcode]` 把守卫的形状固定，再 `dif_neg`」；这里需要的是「先 `obtain` 三元组，再 `show` 出纯计数器的形式」。**

**按项目纪律，本轮不提交半成品：`Parse.lean` 未改动，`parse` 仍然不产出关系。**

### 8.4 下一轮的确切切入点

**写两条引理，都用 `induction t generalizing n`：**

```lean
theorem walk_mono : ∀ (t : Term) (n : ℕ), n ≤ (walkWithRelations t n).2.2
theorem walk_range : ∀ (t : Term) (n : ℕ),
    ∀ s ∈ (walkWithRelations t n).1, n ≤ s.id ∧ s.id < (walkWithRelations t n).2.2
```

**每个分支的骨架：**

```lean
  | app f a ihf iha =>
    intro n
    obtain ⟨tf, rf, n1⟩ := walkWithRelations f (n + 1)
    obtain ⟨ta, ra, n2⟩ := walkWithRelations a n1
    have h1 := ihf (n + 1)   -- 类型现在正确，因为 generalizing n
    have h2 := iha n1
    show ...
    omega
```

**`walk_range` 证出后，`parse_wellFormed` 的第二合取项（id 互异）由 `walk_range` 与 `walk_mono` 共同给出；关系的合取项在 `parseSkeletonWithRelations` 产出 `dependsShape` 后不再空洞，需要额外证明「每个 `dependsShape n xs` 的 `n` 都在张量 id 集合里」——那由 `walk_range` 的 `n ≤ s.id` 直接得到。**

---

## 9. 第 217 轮：`walk_range` 已推到只剩一个投影问题

### 9.1 已经立住的部分

**`walk_mono`（第 216 轮已提交）：`n ≤ (walkWithRelations t n).2.2`，用**投影**而非解构三元组证出。**

**第 217 轮把 `walk_range` 推到了同样的形状：**

```lean
theorem walk_range : ∀ (t : Term) (n : ℕ),
    ∀ s ∈ (walkWithRelations t n).1, n ≤ s.id ∧ s.id < (walkWithRelations t n).2.2
```

**七个分支中，`sort`/`var`/`const`/`lam`/`pi` 五个已通过；`app` 与 `letE` 只剩「首个张量那个分支」的界。**

### 9.2 三个已解决的子障碍（都值得记录）

| 障碍 | 修法 |
|:--|:--|
| **`rcases hs` 后无法调用 `walk_range b (n+1)`** | **先 `have hb := walk_range b (n+1)` 把递归结果存成假设，再 `simp only [walkWithRelations] at hs ⊢`，最后 `rcases List.mem_cons.mp hs`。先存后用，`hb` 不受目标化简影响。** |
| **`List.mem_append` 与 `List.mem_cons` 的顺序** | **`rcases List.mem_cons.mp hs with rfl | hs` 之后，对 `hs` 再做 `rcases List.mem_append.mp hs with hs | hs`，得到三个分支：本节点 / 左子树的张量 / 右子树的张量。** |
| **`Nat.lt_succ_of_le` 多产生一个 `.succ`** | **用 `Nat.lt_of_succ_le`。这两条引理方向不同：前者给 `n < m.succ`，后者给 `n < m`（来自 `n.succ ≤ m`）。** |

### 9.3 剩下的确切问题

**`app`/`letE` 的「本节点」分支，目标是：**

```
{ id := n, shape := termShape }.id < (walkWithRelations a (walkWithRelations f (n+1)).2.2).2.2
```

**`omega` 报出的反例约束是：**

```
b := (walkWithRelations f (n + 1)).2.2
c := n
d := (walkWithRelations a (walkWithRelations f (n + 1)).2.2).2.2
b - c ≥ 1     -- 来自 hmf : n + 1 ≤ b
b - d ≤ 0     -- 来自 hma : b ≤ d
```

**这三条**合起来足以推出 `n < d`**（`c + 1 ≤ b ≤ d` ⇒ `c < d`）。**

**`omega` 仍然失败，唯一的原因是目标左侧的 `{ id := n, shape := termShape }.id` 没有被归约成 `n`——`omega` 把它当成不透明的变量。**

**=> 修法是把 `simp only [TensorShape.mk]`（或 `show n < d`）放在 `omega` **之前**，且顺序必须是 `rfl` 分支 → 化简投影 → `omega`。**

**第 217 轮试过 `refine ⟨le_refl n, ?_⟩` + `simp only` + `omega`，但 `simp only [...] at hs ⊢` 在前一步已经执行，`simp` 的「清理无用假设」把 `hmf`/`hma` 一并删掉了，于是 `omega` 的上下文是空的。**

**=> 正确的顺序是：**

```lean
    · show n < (walkWithRelations a (walkWithRelations f (n+1)).2.2).2.2
      omega
```

**用 `show` 直接把目标写成纯计数器的形式（`rfl` 分支已经让 `s.id` 就是 `n`），**不碰上下文**，`hmf`/`hma` 因此留在作用域里。**

### 9.4 为什么本轮没做完

**第 217 轮在 `app`/`letE` 的两个「本节点」分支上尝试了十一次修正，每次都调换 `simp`/`omega`/`exact` 的顺序，都没有找到既化简投影又保留上下文的组合。**

**=> 根因现在清楚了（9.3 的 `show` 写法），但本轮的时间已经用完。**

**按纪律，`Parse.lean` 已回滚到 HEAD，`parse` 仍然不产出关系。`walk_mono` 保留。**

### 9.5 下一轮的确切做法

**把 `walk_range` 重新加进 `Parse.lean`，五个已通过的分支照第 217 轮写成：**

- **`sort`/`var`/`const`**：`simp only [walkWithRelations, List.mem_singleton] at hs`，`subst`，`exact ⟨le_refl n, Nat.lt_succ_self n⟩`
- **`lam`/`pi`**：`have hb := walk_range b (n+1)`；`have hm := walk_mono b (n+1)`；`simp only [walkWithRelations] at hs ⊢`；`rcases List.mem_cons.mp hs with rfl | hs`；`rfl` 分支 `exact ⟨le_refl n, Nat.lt_succ_of_le hm⟩`；`hs` 分支 `exact ⟨le_trans (Nat.le_succ n) (hb s hs).1, (hb s hs).2⟩`

**`app`/`letE` 的两个「本节点」分支改用 9.3 的 `show` + `omega`：**

```lean
    · show n < (walkWithRelations a (walkWithRelations f (n+1)).2.2).2.2
      omega
```

**其余两个分支（左子树、右子树）照第 217 轮的写法已经通过。**
