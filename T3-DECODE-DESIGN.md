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

---

## 10. 第 219 轮：`walk_nodup` 的真正障碍是**两个归纳假设**

### 10.1 决定性发现

**`walk_nodup` 的所有失败尝试都源于同一件事：`Term.lam`/`Term.pi`/`Term.letE` 分支的 `induction` 给出**两个**归纳假设，而不是一个。**

**`trace_state` 的输出：**

```
ih      : ∀ (n : ℕ), (List.map (fun x => x.id) (walkWithRelations kk n).1).Nodup
a_ih✝   : ∀ (n : ℕ), (List.map (fun x => x.id) (walkWithRelations b n).1).Nodup
n       : ℕ
⊢ (List.map (fun x => x.id) (walkWithRelations (kk.lam b) n).1).Nodup
```

**`ih` 属于**被绑定的类型** `kk`，`a_ih✝` 才属于**子项** `b`。**

**=> 第 217–219 轮的 `ih (n+1)` 全部用错了假设，这就是「类型不匹配」的真正来源。**

**`walk_mono` 与 `walk_range` 之所以没撞上这个坑，是因为它们用的是**定义式递归**（`| Term.lam _ b, n => by ...`），那个写法里 `b` 是直接的模式变量，没有对应的归纳假设。**

### 10.2 正确的写法

**用位置占位符跳过第一个假设，给第二个显式命名：**

```lean
  | Term.lam kk b _ ihb =>
    intro n
    have hb : ((walkWithRelations b (n+1)).1.map (·.id)).Nodup := ihb (n+1)
```

**验证：这一改法让**类型不匹配消失**（第 219 轮实测）。**

### 10.3 剩下的最后一步

**`lam` 分支的目标是 `{id := n, shape := termShape}.id ∉ (walkWithRelations b (n+1)).1.map (·.id)`，展开成：**

```
∀ s ∈ (walkWithRelations b (n+1)).1, ¬({id := n, shape := termShape}.id = s)
```

**`walk_range b (n+1) s hs` 给出 `n + 1 ≤ s.id`，与 `n = s.id` 矛盾。**

**问题：`omega` 需要把 `s` 的 `TensorShape.mk` 投影展开成 `n`，而在 `∀ s ∈ ..., ¬(...)` 这种**嵌套量词**里，`simp only [TensorShape.mk]` 与 `omega` 的配合需要显式给出。**

**第 219 轮试过：**

| 写法 | 结果 |
|:--|:--|
| **`obtain ⟨s, hs, hid⟩ := List.mem_map.mp hc` 然后 `omega`** | **`omega` 拿不到 `hid`** |
| **先 `simp only [TensorShape.mk] at h` 再 `omega`** | **同上** |
| **`simp only at hid`** | **"simp made no progress"** |

**=> 修法应当是把 `hid` 显式喂给 `omega`：**

```lean
    obtain ⟨s, hs, hid⟩ := List.mem_map.mp hc
    have h := hr s hs
    simp only [TensorShape.mk] at h
    omega
```

**这里的 `hid : s.id = n`（不是 `s.id` 的投影形式），`h : n + 1 ≤ s.id`，两条合起来在 `omega` 里应当立刻矛盾。**
**若仍失败，说明 `hid` 的左侧也是投影形式，需要先 `simp only [TensorShape.mk] at hid`，再 `omega`。**

### 10.4 三条不变式的状态

| 不变式 | 状态 |
|:--|:--|
| **`walk_mono`** | **已证（第 216 轮），定义式递归** |
| **`walk_range`** | **已证（第 218 轮），定义式递归** |
| **`walk_nodup`** | **未证；必须用 `induction`，且必须用第二个归纳假设** |

### 10.5 为什么第 219 轮没做完

**第 219 轮在 `lam` 分支上做了十二次修正。前十一都在用错误的归纳假设 `ih`（10.1 的根因），第十二次改用 `ihb` 后类型不匹配消失，只剩 `omega` 与投影的配合。**

**=> 根因已定位、修法已写明，但本轮时间用完。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。`walk_mono` 与 `walk_range` 保留。**

---

## 11. 第 220 轮：`walk_nodup` 的目标形状已完全确定，以及一条更短的替代路线

### 11.1 目标形状（`trace_state` 实测）

**`lam` 分支在 `refine List.nodup_cons.mpr ⟨?_, hb⟩` 之后，第一个目标精确是：**

```
⊢ n ∉ List.map (fun x => x.id) (walkWithRelations b (n + 1)).1
```

**它是一个**否定**（`∉`），不是等式。**

**第 220 轮试过的展开方式与结果：**

| 写法 | 结果 |
|:--|:--|
| **`intro hc; obtain ⟨s, hs, hid⟩ := List.mem_map.mp hc; omega`** | **`omega` 报反例约束 `a - c ≥ 1`（`a := s.id`, `c := n`），即它**已经有** `n+1 ≤ s.id`，但仍失败** |
| **`simp only [List.mem_map, not_exists, not_and]` 然后 `intro s hs hid; omega`** | **同上** |
| **`show ¬ (n = s.id)`** | **类型不匹配（方向不对）** |
| **`simp only [List.mem_map] at hc` 后再 `omega`** | **"simp made no progress"** |

**关键：`omega` 的反例约束显示它**已经拿到** `s.id ≥ n + 1`，也就是说 `hr` 被正确使用了。**
**它仍然失败，说明目标的否定形式里 `n` 与 `s.id` 的关系没有被 `omega` 的线性算术引擎识别为矛盾——因为 `n` 在目标里是**目标左侧的固定项**，而 `s.id` 是**存在量词绑定**的。**

**=> 纯算术部分单独验证过：**

```lean
example (n m : ℕ) (hr : n + 1 <= m) (hn : m = n) : False := by omega
```

**这条**通过**。所以问题不在算术，而在**量词结构**：`omega` 在 `∀ s, ... → s.id = n → False` 里无法把 `s` 的假设串起来。**

### 11.2 更短的替代路线：先证计数引理

**如果 `walkWithRelations` 满足**

```lean
theorem walk_count : ∀ (t : Term) (n : ℕ),
    (walkWithRelations t n).1.length + n = (walkWithRelations t n).2.2
```

**那么结合 `walk_range`（每个 id 在 `[n, 最终)`）就能推出 `Nodup`：数量恰好等于区间长度，且 id 全在区间内。**

**第 220 轮实测这条引理的三个**叶子**分支都通过：**

```lean
  | Term.sort k l => simp [walkWithRelations]; omega      -- 1 + n = n + 1
```

**四个递归分支失败，原因是 `simp only [walkWithRelations]` 在目标上重新引入 `let` 三元组，与 `have h := ih (n+1)` 的展开形式对不上。**

**=> 这与 `walk_nodup` 的障碍同源：**目标必须用 `show` 写成与假设同构的形式**，而不是靠 `simp` 展开。**

### 11.3 下一轮的确切做法

**先证 `walk_count`，每个递归分支用 `show` 而不是 `simp`：**

```lean
  | Term.lam kk b ih =>
    have h := ih (n + 1)
    show 1 + (walkWithRelations b (n + 1)).1.length + n = (walkWithRelations b (n + 1)).2.2
    omega
```

**（`lam` 的 walk 是 `⟨mk n termShape :: tb, dependsShape n [n+1] :: rb, n1⟩`，所以长度是 `tb.length + 1`。）**

**`app`/`letE` 同样写出 `(tf ++ ta).length + 1 + n = n2` 的 `show`，再 `omega`。**

**`walk_count` 证出后，`walk_nodup` 可以从「数量 = 区间长度」+「每个 id 在区间内」推出——这需要 `List.Nodup` 的一个标准引理（`List.nodup_iff_nth_le` 或 `List.Nodup` 与 `List.range` 的关系），而不再需要处理嵌套量词。**

### 11.4 为什么第 220 轮没做完

**第 220 轮在 `walk_nodup` 的 `lam` 分支上又做了五次展开尝试（11.1 的表），并在 `walk_count` 上做了两次，都卡在同一个「`simp` 展开后与假设不同构」的问题上。**

**=> 根因和修法都已写明（`show` 而非 `simp`），本轮时间用完。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。`walk_mono` 与 `walk_range` 保留。**

---

## 12. 第 221 轮：`walk_nodup`/`walk_count` 的 `ih` 签名与直觉不符，以及一条绕开它们的路

### 12.1 实测的 `ih` 签名

**`walk_mono` 与 `walk_range` 用的是**定义式递归**（`| Term.lam _ b, n => by ...`），在那里 `b` 是模式变量，`walk_mono b (n+1)` 直接可用。**

**`walk_count` 与 `walk_nodup` 必须用 **`induction`**（因为要在归纳过程中引用 `walk_range`），而 `induction` 给出的 `ih` 签名并不是 `∀ n, P n` 的简单形式。**

**第 221 轮实测：**

- **`letI := ih` 通过**（说明 `ih` 是可用的函数）
- **但 `have h : (walkWithRelations b (n+1)).1.length + (n+1) = (walkWithRelations b (n+1)).2.2 := ih (n+1)` 报类型不匹配**

**=> `ih` 能接受一个参数并返回一个等式，但返回的等式的**具体形式**与手写的目标不一致（很可能是 `Nat` 加法结合方向或 `n+1` 与 `1+n` 的差异）。**

**=> 修法：不手写 `h` 的类型，而是让 Lean 推断，再用 `omega` 处理：**

```lean
    have h := ih (n + 1)
    simp only [walkWithRelations, List.length_cons] at h ⊢
    omega
```

**这条在第 221 轮**仍然失败**，`omega` 报的反例约束里出现了 `a - b - c - d ≥ 2` 这类无法闭合的组合——说明 `h` 被 `simp at h` 改写成了某个未预期的形式。**

### 12.2 一条真正绕开这两条引理的路

**观察：`WellFormed` 的两个合取项里，`Nodup` 是为了让张量 id 互异。而第 203 轮已经证明过 `termTensors_nodup`：**

```lean
theorem termTensors_nodup (t : Term) : ((termTensors t).map (·.id)).Nodup
```

**它用的是 `List.range` 分配 id，证明只需 `List.nodup_range`。**

**=> 所以正确的架构不是「让 `parse` 用 `walkWithRelations`」，而是：**

| 层 | 用什么 |
|:--|:--|
| **张量列表与 id** | **`termTensors`（`List.range`，`Nodup` 已证）** |
| **关系列表** | **`dependsShape n [n+1]` 的列表，其中 `n` 正是 `termTensors` 分配的那个 id** |

**`walkWithRelations` 的价值在于它把「哪个节点依赖哪个子节点」算出来了；但它的**张量分配**与
`termTensors` 是同一个方案（前序遍历，第 i 个节点拿 id i），只是写法不同。**

**=> 因此可以保留 `walkWithRelations` 的关系产出，而用 `termTensors` 的张量产出，两者的一致性由
`walk_count` 或一条「两者长度相等且 id 相同」的引理桥接。**

**那条桥接引理比 `walk_nodup` 弱，因为它不需要 `Nodup`——`termTensors` 已经提供了。**

### 12.3 下一轮的做法

**先证一条最弱的桥接引理：**

```lean
theorem walk_tensors_eq (t : Term) (n : ℕ) :
    (walkWithRelations t n).1.map (·.id) = (List.range ((walkWithRelations t n).2.2 - n)).map (fun i => i + n)
```

**若这条成立，则 `parse` 可以直接用 `termTensors` 的张量列表 + `walkWithRelations` 的关系列表，`WellFormed` 由
`termTensors_nodup` 给出。**

**这条引理的难度与 `walk_count` 相当（都要对 `t` 归纳），但它的**结论**是 `parse` 真正需要的形式，而且不需要
`omega` 处理数组区间，只需要 `List.map` 与 `List.range` 的重写。**

### 12.4 为什么第 221 轮没做完

**第 221 轮在 `walk_count` 上做了八次尝试，每次都在 `ih` 的返回类型或 `simp at h` 的改写形式上卡住。**

**=> 根因已定位（`ih` 的签名与手写目标形式不符），但修法尚未找到。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。`walk_mono` 与 `walk_range` 保留。**

---

## 13. 第 222 轮：`walk_tensors_eq` 的机制已验证，剩下一个 `List.range` 分段引理

### 13.1 关键机制：又是第二个归纳假设

**第 222 轮把第 219/221 轮的教训用在 `walk_tensors_eq` 上，`lam` 分支的 `rw [h]` **一次成功**：**

```lean
  | Term.lam kk b _ ihb =>
    have h := ihb (n+1)
    simp only [walkWithRelations, List.map_cons]
    rw [h]
```

**若写成 `| Term.lam kk b ih =>`（不跳过第一个），`ih` 属于被绑定的类型 `kk`，`rw` 会报「找不到模式」。**

**=> 这三次（第 219、221、222 轮）都撞在同一件事上，说明它是 `Term.lam`/`Term.pi`/`Term.letE` 分支的**固定规律**：**
**`induction` 为每个子项生成一个假设，而 binder 的类型也是一个子项，所以**第一个假设属于 binder，第二个才属于 body**。**

### 13.2 叶子分支

**三个叶子在 `walk_tensors_eq` 下的目标是：**

```
[n] = (List.range 1).map (fun i => i + n)
```

**`simp [List.range_succ]` 可以直接闭合**（它对第二条引理无用，但对叶子有效）。**

**`List.range 1` 的展开**不是 `simp` 的默认行为**，必须显式给出 `List.range_succ`。**

### 13.3 剩下的 `shift_range`

**`lam` 的收尾需要一个纯列表引理：**

```lean
theorem shift_range : ∀ (k n : ℕ),
    (n :: (List.range k).map (fun i => i + (n+1))) = (List.range (k+1)).map (fun i => i + n)
```

**它的含义是：walk 在 `lam` 分支上把 `n` 放在最前、把子树的 id 整体加一，等价于从 `n` 开始按顺序编号。**

**第 222 轮把它推到了 `succ` 分支的展开式：**

```
⊢ n :: (map (+ (n+1)) (range k) ++ (k + (n+1)) :: map (+ (n+1)) [])
    = map (+ n) (range k) ++ (k + n) :: map (+ n) [] ++ (k + 1 + n) :: map (+ n) []
```

**剩余的三处：**
1. **`map ... []` 应化为 `[]`（`simp` 可做）**
2. **`(k + (n+1))` 与 `(k + 1 + n)` 的加法重排（`Nat.add_assoc` + `Nat.add_comm`）**
3. **`n :: (... ++ [...])` 与 `n :: ... ++ ...` 的 `append` 分配**

**=> 修法是把这三步显式写出来，而不是交给 `congr 1` + `simp`——第 222 轮用 `congr 1` 后目标形状未被正确分解。**

### 13.4 下一轮的做法

**把 `shift_range` 的 `succ` 分支拆成两段：**

```lean
  | succ k ih =>
    intro n
    rw [List.range_succ, List.range_succ]
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.singleton_append, List.append_nil]
    rw [← ih n]
    -- now both sides start with `n :: ...`; peel the head and close the tails by `congr 1` + `Nat.add_assoc`
    congr 2
    ext i
    omega
```

**关键是 `List.map_nil` 和 `List.append_nil` 必须显式出现在 `simp only` 里——`map ... []` 不化归是第 222 轮卡住的原因之一。**

### 13.5 为什么第 222 轮没做完

**第 222 轮在 `shift_range` 上做了五次尝试，最后一次把目标推到了可读的形式（13.3），但 `congr 1` 未能正确分解。**

**=> 修法已写明（显式 `simpa` 链 + `congr 2` + `ext`），本轮时间用完。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。`walk_mono` 与 `walk_range` 保留。**

---

## 14. 第 224 轮：`walk_count` 不足以桥接 `termTensors`，需要一条新引理

### 14.1 本轮的两条否定结论

**第 224 轮试了两条路，都走不通，但都给出了精确的否定理由：**

| 路线 | 结论 |
|:--|:--|
| **用 `walk_count` + `walk_range` 直接推 `Nodup`** | **论证是**循环的**：`[n, n+len)` 内 `len` 个元素互异，需要先知道它们互异。`omega` 报的反例约束正是这一点。** |
| **用 `walk_tensors_eq`（id 列表恰好等于 `range` 的像）** | **只剩 `shift_range` 一个列表引理，但它需要 `List.ext_getElem` + 三段区间分析；第 224 轮做到 `ext` 后 `split` 的 `omega` 拿不到分支信息。** |

### 14.2 `shift_range` 已被推到最后一格

**它的 `succ` 分支已经化简到：**

```
⊢ map (· + n) (range k) ++ [k + n, k + (n+1)] = map (· + n) (range (k+2))
```

**右边 = `map (· + n) (range k) ++ [k + n] ++ [k + 1 + n]`，与左边只差 `k + (n+1)` 与 `k + 1 + n`。**

**=> 修法：对 `k + 2` 做两次 `List.range_succ`（或用 `range_add_one` 类引理），然后 `simp [Nat.add_assoc]`。**

**第 224 轮试过 `rw [show k + 2 = (k+1) + 1 from rfl]`，`rfl` 不成立（`k+1+1` 与 `k+2` 定义上不同），应当用 `by omega` 或 `Nat.add_assoc`。**

### 14.3 一条更短的桥接需要的新引理

**第 224 轮试了第三条路：用 `termTensors`（`List.range` 分配，`Nodup` 已证）作张量列表，`walkWithRelations`
只取关系。这需要 `tensorCount t = (walkWithRelations t 0).2.2`。**

**`walk_count t 0` 已给出 `(walkWithRelations t 0).1.length + 0 = (walkWithRelations t 0).2.2`，所以只需**

```lean
theorem tensorCount_walk : ∀ (t : Term), (walkWithRelations t 0).1.length = tensorCount t
```

**第 224 轮把它推到 `lam` 分支，剩下：**

```
⊢ (walkWithRelations b 1).1.length + 1 = 1 + tensorCount b
```

**这需要一条`起始计数器不影响长度`的引理：**

```lean
theorem walk_length_indep : ∀ (t : Term) (n m : ℕ),
    (walkWithRelations t n).1.length = (walkWithRelations t m).1.length
```

**=> 它比 `shift_range` 简单，因为只涉及 `List.length`，不涉及 `List.map` 或元素相等。**

**=> 下一轮应当证这条，然后用 `walk_count` 得到 `tensorCount_walk`，再用 `termTensors_nodup` 完成
`parse_wellFormed`。**

### 14.4 为什么第 224 轮没做完

**第 224 轮在三条路线上各做了若干次尝试：直接推 `Nodup`（发现循环）、`shift_range`（推到最后一格）、
`tensorCount_walk`（推到需要 `walk_length_indep`）。**

**=> 三条路的**精确阻塞点**都已定位，`walk_length_indep` 是本轮新发现的、也是最短的下一步。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。`walk_mono`、`walk_range`、`walk_count` 保留。**

---

## 15. 第 226 轮：`Nodup` 的正确路线是**严格递增**，不是计数

### 15.1 为什么计数路线走不通

**第 224 轮已经确认：`walk_range`（每个 id 在 `[n, 最终计数)` 内）加上 `walk_count`（数量 = 最终计数 - n）
**不足以**推出 `Nodup`，因为「`len` 个元素落在长度 `len` 的区间内」本身就要求它们互异——**这是循环的**。**

**第 226 轮又试了 `tensorCount_walk` 那条路（用 `termTensors` 的张量 + `walkWithRelations` 的关系），同样卡在
`(walkWithRelations b 1).1.length` 与 `(walkWithRelations b 0).1.length` 的对齐上，需要额外 `generalize`。**

### 15.2 正确路线：id 严格递增

**walk 是**前序遍历**：先访问当前节点（拿 id `n`），再访问子节点（从 `n+1` 起）。因此 id 列表**严格递增**，
而严格递增的列表必然 `Nodup`。**

```lean
theorem walk_increasing : ∀ (t : Term) : ∀ n : ℕ,
    ((walkWithRelations t n).1.map (·.id)).Pairwise (· < ·)
```

**转换成 `Nodup` 的方法（第 226 轮验证通过）：**

```lean
exact List.Pairwise.imp (fun {a b} (hab : a < b) => Nat.ne_of_lt hab) h
```

**注意 `List.Pairwise.imp` 的参数是隐式的 `{a b}`，用 `fun a b hab => ...` 会类型不匹配。**

### 15.3 已通过的两个分支：`lam` 与 `pi`

**两者结构相同，第 226 轮**完整通过**：**

```lean
  | Term.lam kk b _ ihb =>
    intro n
    simp only [walkWithRelations, List.map_cons]
    refine List.pairwise_cons.mpr ⟨?_, ihb (n+1)⟩
    intro x hx
    obtain ⟨s, hs, hid⟩ := List.mem_map.mp hx
    have hr := walk_range b (n+1) s hs
    simp only [TensorShape.mk] at hr
    subst hid
    exact hr.1
```

**三个关键点：**
1. **`_ ihb` —— 第二个归纳假设（第 219/222/225/226 轮反复确认）**
2. **`subst hid` —— `hid : x = s.id` 的方向使 `rw` 失败，`subst` 才能替换**
3. **`simp only [TensorShape.mk] at hr` —— 先把 `s.id` 化成 `n`，再 `exact hr.1`**

### 15.4 `app` 的结构与阻塞点

**`app` 的 id 列表是 `n :: (l1 ++ l2)`，所以需要三层：**

```
pairwise_cons(n, l1 ++ l2)  ←  拆分首元素
  × pairwise_append(l1, l2)  ←  拆分成两段
  × 跨段的 ∀ a ∈ l1, ∀ b ∈ l2, a < b
```

**第 226 轮把 `List.pairwise_append` 放进 `simp only`，但它在 `n :: (l1 ++ l2)` 上不适用（目标外层还是
`Pairwise (n :: ...)`），`simp` 因此只做了部分展开，`refine ⟨...⟩` 失败。**

**=> 正确的写法是分两步：**

```lean
    simp only [walkWithRelations, List.map_cons, List.map_append]
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · -- head < every element of l1 ++ l2
      intro x hx
      ...
    · -- the tail is Pairwise
      rw [List.pairwise_append]
      refine ⟨ihf (n+1), iha (walkWithRelations f (n+1)).2.2, ?_⟩
      intro x hx y hy
      ...
```

**关键是 `pairwise_cons` 在 `pairwise_append` **之前**，而 `pairwise_append` 作用在**尾部**而不是整体。**

### 15.5 为什么第 226 轮没做完

**第 226 轮在 `walk_nodup` 上做了八次尝试，`lam`/`pi` 完整通过，`app` 卡在 `pairwise_cons` 与
`pairwise_append` 的嵌套顺序上。**

**=> 修法已明确（15.4 的两步写法），本轮时间用完。**

**按纪律，`Parse.lean` 未改动，`parse` 仍然不产出关系。**

### 15.6 一条副产物：`tensorCount_walk` 的部分进展

**第 226 轮在 `tensorCount_walk` 上发现：`lam` 分支需要 `show (walkWithRelations b (0+1)).1.length + 1 =
1 + tensorCount b` 然后 `norm_num`——因为 `simp` 不会把 `0 + 1` 化成 `1`。**

**这条修正本身是对的，但它不解决 `pi`/`app`/`letE`，所以没有单独提交。**

---

## 16. 第 234 轮：`readOf_fillWith` 的三条路线与各自的精确障碍

### 16.1 目标

```lean
theorem readOf_fillWith {k : IRSkeleton} {f : (s : TensorShape) → Fin s.shape.prod → ℝ}
    {t : Tensor} (ht : t ∈ fillWith k f) {i : ℕ} (hi : i < t.shape.prod) :
    readOf (fillWith k f) t.id [i] = f ⟨t.id, t.shape⟩ ⟨i, hi⟩
```

### 16.2 路线一：通用的「find 返回已知元素」

```lean
theorem find?_eq_some_of_unique {α} (l : List α) (p : α → Bool) (x : α)
    (hx : x ∈ l) (huniq : ∀ y ∈ l, p y = true → y = x) : l.find? p = some x
```

**第 234 轮把它推到了 `cons` 分支的 `false` 情形，剩下的子目标是 `x ∈ tl` 的提取：`rcases hx with hh | hx'` 在 `x = h :: tl` 的两种情形上，`rfl` 方向与 `Nodup` 的用法不匹配，`subst hh` 又在 `h` 与 `x` 的类型相同时才可用。**
**=> 需要 `Or.elim` 显式处理，且 `h : h ∈ h :: tl` 的证明要用 `List.mem_cons_self` 而非 `simp`。**

### 16.3 路线二：`Nodup` 推出 id 单射

```lean
theorem fillWith_id_unique {k} {f} (hnd : (k.tensors.map (·.id)).Nodup)
    {u t : Tensor} (hu : u ∈ fillWith k f) (ht : t ∈ fillWith k f)
    (hid : u.id = t.id) : u = t
```

**第 234 轮试了三种写法：**

| 写法 | 障碍 |
|:--|:--|
| **`List.Nodup.injective`** | **不是字段记法；`@List.Nodup.injective` 也不存在** |
| **`List.idxOf`** | **不存在于本树** |
| **对 `k.tensors` 手动归纳** | **`hnd` 在归纳过程中被固定，`simp only [List.map_cons, List.nodup_cons] at hnd` 报 "made no progress"——需要 `generalizing` 或先 `revert`** |

**=> 第三条路最接近成功：`key` 引理的结构是对的（`cons` 分支的四种情形都覆盖了），只是 `hnd` 的可得性需要重排。**

### 16.4 路线三：让 `fillWith` 携带 `Nodup` 的证据

**若 `fillWith` 的类型里带 `(hnd : (k.tensors.map (·.id)).Nodup)`，则 16.3 的前提不需要从外部传入。**
**但这会把 `fillWith` 从「任意骨架」收窄到「良构骨架」，而 `WellFormed` 已经提供 `Nodup`，所以这不算损失。**

**=> 下一轮的最短路径：把 `hnd` 作为 `fillWith` 的显式参数（或从 `WellFormed k` 导出），再用 16.3 的 `key` 引理。**

### 16.5 为什么第 234 轮没做完

**三条路线各做了 3–6 次尝试，都停在「前提不可得」或「`rcases` 方向」这类细节上，而没有停在数学上。**

**=> 共同点：`Nodup` 与 `List.find?` 的交互需要把「元素唯一」这件事**在正确的形式上**喂给下一步，而 `simp only` 与 `rcases` 在这两处都会把形式改掉。**

**按纪律，`Materialize.lean` 未改动，`fillWith` 与 `fillWith_zero`（第 233 轮）保留，`readOf_fillWith` 仍只是文件里的记录。**
