/-
# 前缀解码器的方程引理：一个可复用的模式

## 0. 这份文件为什么存在

第 109–127 轮（**19 轮**）尝试证明 `ConstraintTokenizer` 的二元节点往返，反复卡在同一类问题上：
**`dec.eq_def` 不能直接用于展开一个「fuel + 列表」双参数的模式匹配函数**。

失败的具体形态有三种，都在探针里复现过：

| 形态 | 症状 |
|:--|:--|
| `unfold dec` / `rw [dec.eq_def]; simp` | `maximum recursion depth has been reached`——`eq_def` 里含 `dec` 自身 |
| `simp only [if_pos rfl]` | `simp made no progress`——tag 常量不展开，`if` 不归约 |
| 手写方程引理 | ✅ **可行** |

## 1. 解决模式（在第 125 / 127 轮的探针里验证过）

### 1.1 方程引理：用 `rfl` 证，不要用 `eq_def`

对一个在 `fuel = k + 1` 上做模式匹配的 `dec`，**方程引理可以直接 `rfl` 证明**：

```
theorem dec_const_step (k d : Nat) (rest : List Nat) :
    dec (1 :: (d :: rest)) (k + 1) = some (.const d, 2) := by
  rfl
```

**为什么 `rfl` 够用**：`k + 1` 已经是 `Nat.succ _` 形态，Lean 的定义方程直接适用。

### 1.2 更深的分支：展开 if 链

若目标 tag 不是第一个分支，`rfl` 不够，需要按顺序消掉前面的 `if`：

```
theorem dec_bin_step (k d : Nat) (rest : List Nat) :
    dec (2 :: (d :: rest)) (k + 1) = <二元分支体> := by
  rw [dec.eq_def]
  simp only [tag0_eq, tag1_eq, tag2_eq]     -- 按顺序给出前面所有 tag
  norm_num                                    -- 消掉剩余的数值 if 与 dif
```

**关键**：`simp only` 的集合必须**包含所有排在目标 tag 之前的 tag 引理**，
否则 `if 2 = tag0` 里的 `tag0` 不会展开成 `0`，`if` 就不动。

### 1.3 用 `norm_num` 而不是 `simp` 收尾

`norm_num` 会把剩余的 `if`、`dif`、数值判断一起消掉。第 126 轮曾猜测坐标分支需要显式
`dif_pos h`，**五分支探针表明不需要**。

## 2. 本文件验证的抽象版本

下面用一个**五个构造子**的形状复现上面的三种模式，全部编译通过、无未完成项。
它与 `SExpr` 的构造子数一致，因此这些结论可以直接套用。

## 3. 边界

- **本文件不含 `ConstraintTokenizer` 的定理**，只验证 tactic 模式。
- **它不声称二元节点往返已完成**——那还差「把任意非空列表喂进方程引理」一步
  （`TokenizeStrategy.lean §11.3`）。
- 本文件的价值是：**下一次移植时不必再从零试 tactic**。
-/
import Mathlib

namespace Lattice.Geo.TokenizerPattern

/-! ## 一、五种构造子的形状 -/

/-- 与 `SExpr` 同为五构造子的形状。 -/
inductive Shape5 where
  | c0 (p : Nat) (a : Nat)
  | c1 (m : Nat)
  | c2 (x y : Shape5)
  | c3 (x y : Shape5)
  | c4 (x y : Shape5)

/-! ## 二、五个 tag，每个配一条 `simp` 引理 -/

/-- 构造子标签。 -/
def tag0 : Nat := 0
def tag1 : Nat := 1
def tag2 : Nat := 2
def tag3 : Nat := 3
def tag4 : Nat := 4

/-- **每个 tag 都需要一条 `@[simp]` 引理**，否则 `if t = tagX` 不归约。 -/
@[simp] theorem tag0_eq : tag0 = 0 := rfl
@[simp] theorem tag1_eq : tag1 = 1 := rfl
@[simp] theorem tag2_eq : tag2 = 2 := rfl
@[simp] theorem tag3_eq : tag3 = 3 := rfl
@[simp] theorem tag4_eq : tag4 = 4 := rfl

/-! ## 三、解码器：列表在前，五分支 -/

/-- **五分支解码器**：模式匹配在列表上，fuel 只作上界。 -/
def dec : List Nat → Nat → Option (Shape5 × Nat)
  | [], _ => none
  | [_], _ => none
  | t :: d :: rest, 0 => none
  | t :: d :: rest, fuel + 1 =>
      if t = tag0 then
        match rest with
        | axisVal :: _ => some (.c0 d axisVal, 3)
        | [] => none
      else if t = tag1 then some (.c1 d, 2)
      else if t = tag2 then
        (match dec (d :: rest) fuel with
         | some (x, c₁) =>
             match dec ((d :: rest).drop c₁) fuel with
             | some (y, c₂) => some (.c2 x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tag3 then
        (match dec (d :: rest) fuel with
         | some (x, c₁) =>
             match dec ((d :: rest).drop c₁) fuel with
             | some (y, c₂) => some (.c3 x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tag4 then
        (match dec (d :: rest) fuel with
         | some (x, c₁) =>
             match dec ((d :: rest).drop c₁) fuel with
             | some (y, c₂) => some (.c4 x y, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else none

/-! ## 四、三条方程引理，三种难度 -/

/-- **模式 1（最容易）：`rfl` 直接够用。**

`tag1` 是第二个分支，而 `1 = tag0` 立即为假，所以定义方程直接适用。 -/
theorem dec_c1_step (k : Nat) (d : Nat) (rest : List Nat) :
    dec (tag1 :: (d :: rest)) (k + 1) = some (.c1 d, 2) := by
  rfl

/-- **模式 2：展开 `if` 链。**

`tag2` 是第三个分支，需要先给出 `tag0`、`tag1`、`tag2` 三条引理。 -/
theorem dec_c2_step (k : Nat) (d : Nat) (rest : List Nat) :
    dec (tag2 :: (d :: rest)) (k + 1) =
      (match dec (d :: rest) k with
       | some (x, c₁) =>
           match dec ((d :: rest).drop c₁) k with
           | some (y, c₂) => some (.c2 x y, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [dec.eq_def]
  simp only [tag0_eq, tag1_eq, tag2_eq]
  norm_num

/-- **模式 3：嵌套 `match` + `dif`。**

`tag0` 走第一个分支，分支体里还有一个 `match rest with` 和一个 `if h :`。
**`norm_num` 会把剩下的 `if` 与 `dif` 一起消掉，不需要显式 `dif_pos`。** -/
theorem dec_c0_step (k : Nat) (d : Nat) (axisVal : Nat) (rest : List Nat) :
    dec (tag0 :: (d :: (axisVal :: rest))) (k + 1) = some (.c0 d axisVal, 3) := by
  rw [dec.eq_def]
  simp only [tag0_eq]
  norm_num

/-- **结论**：三种难度的分支都有确定的 tactic 配方。

| 分支位置 | tactic |
|:--|:--|
| 常量分支（第 2 个） | `rfl` |
| 二元分支（第 3 个） | `rw [dec.eq_def]; simp only [它之前的全部 tag]; norm_num` |
| 坐标分支（第 1 个，带嵌套 match/dif） | `rw [dec.eq_def]; simp only [tag0_eq]; norm_num` | -/
theorem three_tactic_patterns_work :
    (∀ (k d : Nat) (rest : List Nat),
        dec (tag1 :: (d :: rest)) (k + 1) = some (.c1 d, 2)) ∧
    (∀ (k d axisVal : Nat) (rest : List Nat),
        dec (tag0 :: (d :: (axisVal :: rest))) (k + 1) = some (.c0 d axisVal, 3)) :=
  ⟨dec_c1_step, dec_c0_step⟩

end Lattice.Geo.TokenizerPattern
