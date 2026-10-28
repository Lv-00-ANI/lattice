/-
# `EqConstraint` 的结构 tokenizer：前缀编码与解码

## 0. 本节补什么

第 108 轮交付 `geoLadder` 时记录了开放项：**L1→L2 用了恒等 tokenizer**，
因为 `L1L2Roundtrip` 的往返定理落点是 `LinearForm`，不是 `EqConstraint`。

第 109 轮尝试补它，三次设计都失败（见 `STATE-FINAL §3.6.2d`）。

**本轮先用一个不含本项目定义的最小文件把模式试通**，确认可行后再套用。

## 1. 试通的模式

**关键发现**：`dec` 必须**在一个递减的结构参数上递归**，且递归调用不能再传计算出来的长度。

```
dec : ℕ → List ℕ → Option (SExpr × List ℕ)        -- fuel 在前
```

第 109 轮失败的形态是 `dec (rest.length) rest`——**传的是计算值，不是结构子项**，
Lean 拒绝。本轮改成在 `t :: d :: rest` 上做模式匹配，递归时用 `List.length (d :: rest)`，
**这仍然不是结构子项**，所以本节**只证明不需要递归的那一部分**（叶子）。

**这个边界必须说清**：叶子往返成立，二元节点的往返需要 fuel 的算术引理，本节未做。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `SExpr` | 可序列化的表达式形状（常量用标记） |
| `enc` | 前缀编码 |
| `dec` | 带 fuel 的解码器 |
| **`dec_enc_const`** | **常量往返** |
| **`dec_enc_coord`** | **坐标往返** |
| `structure_survives_tokens` | 汇总 |

## 3. 边界

- **常量用标记代替值**：`GeoExpr.const (c : ℝ)` 的 `ℝ` 值无法编码成 `ℕ` token
  （第 87 轮可计算性问题的同一根源）。**编码的是结构，不是常量值。**
- **只证叶子往返**。二元节点需要 fuel 的算术（`dec (n+2) (a ++ b)` 的分解），
  **本节未做**，`binary_not_done` 记录它。
- **不接进 `geoLadder`**：那需要 `Sym := SExpr` 且 `satSym` 重新定义。
-/
import Mathlib
import Lattice.Domains.Constraints.Expr

namespace Lattice.Geo

namespace ConstraintTokenizer

variable {n : ℕ}

/-! ## 一、可序列化的表达式形状 -/

/-- **可序列化的表达式**：与 `GeoExpr` 同构，常量用标记。 -/
inductive SExpr (n : ℕ) : Type where
  /-- 坐标引用。 -/
  | coord (p : ℕ) (axis : Fin n)
  /-- 常量标记（真实值在外部保存）。 -/
  | const (mark : ℕ)
  /-- 加法。 -/
  | add (e₁ e₂ : SExpr n)
  /-- 减法。 -/
  | sub (e₁ e₂ : SExpr n)
  /-- 乘法。 -/
  | mul (e₁ e₂ : SExpr n)

/-! ## 二、编码 -/

/-- 构造子标签。 -/
def tagCoord : ℕ := 0
def tagConst : ℕ := 1
def tagAdd : ℕ := 2
def tagSub : ℕ := 3
def tagMul : ℕ := 4

@[simp] theorem tagCoord_eq : tagCoord = 0 := rfl
@[simp] theorem tagConst_eq : tagConst = 1 := rfl
@[simp] theorem tagAdd_eq : tagAdd = 2 := rfl
@[simp] theorem tagSub_eq : tagSub = 3 := rfl
@[simp] theorem tagMul_eq : tagMul = 4 := rfl

/-- **前缀编码**。坐标携带两个数，常量携带标记，二元节点带一个标签。 -/
def enc : SExpr n → List ℕ
  | .coord p axis => [tagCoord, p, axis.val]
  | .const m => [tagConst, m]
  | .add e₁ e₂ => tagAdd :: (enc e₁ ++ enc e₂)
  | .sub e₁ e₂ => tagSub :: (enc e₁ ++ enc e₂)
  | .mul e₁ e₂ => tagMul :: (enc e₁ ++ enc e₂)

/-! ## 三、解码器（返回消费数） -/

/-- **编码长度的计算式**：与 `enc` 同构的 `ℕ` 函数。

**为什么需要它**：解码器要判断「还剩多少」，而那个数必须由结构算出来，
不能用 `(enc e).length`（那会让递归在计算长度上进行，第 111 轮已证明 Lean 不接受）。 -/
def encLen : SExpr n → ℕ
  | .coord _ _ => 3
  | .const _ => 2
  | .add e₁ e₂ => 1 + encLen e₁ + encLen e₂
  | .sub e₁ e₂ => 1 + encLen e₁ + encLen e₂
  | .mul e₁ e₂ => 1 + encLen e₁ + encLen e₂

/-- **编码长度 = `encLen`**：这是把「结构」与「token 数」连起来的桥。 -/
theorem enc_length (e : SExpr n) : (enc e).length = encLen e := by
  induction e with
  | coord p axis => rfl
  | const m => rfl
  | add a b iha ihb =>
      show (tagAdd :: (enc a ++ enc b)).length = 1 + encLen a + encLen b
      simp only [List.length_cons, List.length_append, iha, ihb, encLen]
      omega
  | sub a b iha ihb =>
      show (tagSub :: (enc a ++ enc b)).length = 1 + encLen a + encLen b
      simp only [List.length_cons, List.length_append, iha, ihb, encLen]
      omega
  | mul a b iha ihb =>
      show (tagMul :: (enc a ++ enc b)).length = 1 + encLen a + encLen b
      simp only [List.length_cons, List.length_append, iha, ihb, encLen]
      omega

/-- **删除前缀**：从 `enc a ++ enc b` 删掉 `|enc a|` 个，正好得到 `enc b`。

**这是二元节点往返的关键**：解码完左子树后，剩下的一定是右子树的编码。 -/
theorem drop_enc_append (a b : SExpr n) :
    (enc a ++ enc b).drop (enc a).length = enc b := by
  simp

/-- **解码器：返回消费的 token 数，而不是剩余列表。**

**这是第 111 轮诊断给出的路线 1**：把剩余列表换成消费数后，
「不增长」变成 `ℕ` 上的性质而不是结构性质，终止性因此自动通过。 -/
def dec : ℕ → List ℕ → Option (SExpr n × ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | fuel + 1, t :: d :: rest =>
      if t = tagCoord then
        match rest with
        | axisVal :: _ =>
            if h : axisVal < n then some (.coord d ⟨axisVal, h⟩, 3) else none
        | [] => none
      else if t = tagConst then some (.const d, 2)
      else if t = tagAdd then
        (match dec fuel (d :: rest) with
         | some (e₁, c₁) =>
             match dec fuel ((d :: rest).drop c₁) with
             | some (e₂, c₂) => some (.add e₁ e₂, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tagSub then
        (match dec fuel (d :: rest) with
         | some (e₁, c₁) =>
             match dec fuel ((d :: rest).drop c₁) with
             | some (e₂, c₂) => some (.sub e₁ e₂, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else if t = tagMul then
        (match dec fuel (d :: rest) with
         | some (e₁, c₁) =>
             match dec fuel ((d :: rest).drop c₁) with
             | some (e₂, c₂) => some (.mul e₁ e₂, 1 + c₁ + c₂)
             | none => none
         | none => none)
      else none

/-! ## 四、往返 -/

/-- **常量往返**：消费 2 个 token，还原标记。 -/
theorem dec_enc_const (m fuel : ℕ) :
    dec (n := n) (fuel + 1) (enc (n := n) (.const m)) = some (.const m, 2) := by
  show dec (n := n) (fuel + 1) (tagConst :: (m :: [])) = some (.const m, 2)
  unfold dec
  simp

/-- **坐标往返**：消费 3 个 token，还原坐标。 -/
theorem dec_enc_coord (p : ℕ) (axis : Fin n) (fuel : ℕ) :
    dec (n := n) (fuel + 1) (enc (n := n) (.coord p axis)) =
      some (.coord p axis, 3) := by
  show dec (n := n) (fuel + 1) (tagCoord :: (p :: (axis.val :: []))) =
    some (.coord p axis, 3)
  unfold dec
  simp only [dif_pos axis.isLt]
  simp

/-! ## 五、结论 -/

/-- **结构经 token 流无损（叶子层）**：坐标与常量都能被编码后还原，且消费数精确。

**这是第 109–111 轮四次失败之后真正交付的部分**：
在「返回消费数」的形态上，终止性自动通过，叶子往返与二元节点的桥引理都成立。

### 本轮的进展

| 项 | 状态 |
|:--|:--|
| `encLen` + `enc_length` | ✅ 编码长度由结构算出 |
| `drop_enc_append` | ✅ **二元节点的桥**：删掉左子树后正好是右子树 |
| `dec` | ✅ 终止性自动通过（第 111 轮诊断的路线 1） |
| 叶子往返 | ✅ |
| **二元节点往返** | ⚠️ 桥已就位，归纳步未写（需要 fuel 的算术，见下） |

**`drop_enc_append` 是本轮最实质的收获**：它正是第 111 轮说「不能由结构归纳得到」的那条引理，
**在本形态下它变成一行 `simp`。** -/
theorem structure_survives_tokens (p : ℕ) (axis : Fin n) (m fuel : ℕ) :
    dec (n := n) (fuel + 1) (enc (n := n) (.coord p axis)) = some (.coord p axis, 3) ∧
    dec (n := n) (fuel + 1) (enc (n := n) (.const m)) = some (.const m, 2) :=
  ⟨dec_enc_coord p axis fuel, dec_enc_const m fuel⟩

/-! ## 五、二元节点：方程引理与完整往返

**第 112 轮此处曾留一条 `binary_induction_not_done : True`，记录「二元节点的归纳本轮未做」。**
**第 144 轮做完了**（见本节末尾的 `structure_survives_tokens_full`），
所以那条空定理和它的注释都已删除：一个陈述为 `True` 的「定理」不是记录，是不占位的名字。 -/

/-- **`enc e` 非空**：每个构造子的编码都以 `tagX ::` 开头。 -/
theorem enc_ne_nil (e : SExpr n) : enc (n := n) e ≠ [] :=
  match e with
  | .coord _ _ => List.cons_ne_nil _ _
  | .const _ => List.cons_ne_nil _ _
  | .add _ _ => List.cons_ne_nil _ _
  | .sub _ _ => List.cons_ne_nil _ _
  | .mul _ _ => List.cons_ne_nil _ _

/-- **每个 `encLen` 至少是 2**（第 122 轮用 `decide` 发现这条从未被陈述）。 -/
theorem encLen_ge_two (e : SExpr n) : 2 ≤ encLen e := by
  induction e with
  | coord p axis => show 2 ≤ 3; omega
  | const m => show 2 ≤ 2; exact Nat.le_refl 2
  | add a b iha ihb => show 2 ≤ 1 + encLen a + encLen b; omega
  | sub a b iha ihb => show 2 ≤ 1 + encLen a + encLen b; omega
  | mul a b iha ihb => show 2 ≤ 1 + encLen a + encLen b; omega

/-- **add 分支的方程引理**（字面 cons 形态）。

**两个必要条件**（第 140 / 141 轮实测）：
1. 右侧绑定变量名必须是 `e₁`、`e₂`，与 `dec.eq_def` 生成的完全一致；
2. `norm_num` 之后需要 `rfl` 闭合 `List.drop c₁ (d :: rest)` 的呈现差异。 -/
theorem dec_add_step (k : ℕ) (d : ℕ) (rest : List ℕ) :
    dec (n := n) (k + 1) (tagAdd :: (d :: rest)) =
      (match dec (n := n) k (d :: rest) with
       | some (e₁, c₁) =>
           match dec (n := n) k ((d :: rest).drop c₁) with
           | some (e₂, c₂) => some (.add e₁ e₂, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [dec.eq_def]
  simp only [tagAdd_eq, tagCoord_eq, tagConst_eq]
  norm_num

/-- **sub 分支的方程引理**（字面 cons 形态）。

**两个必要条件**（第 140 / 141 轮实测）：
1. 右侧绑定变量名必须是 `e₁`、`e₂`，与 `dec.eq_def` 生成的完全一致；
2. `norm_num` 之后需要 `rfl` 闭合 `List.drop c₁ (d :: rest)` 的呈现差异。 -/
theorem dec_sub_step (k : ℕ) (d : ℕ) (rest : List ℕ) :
    dec (n := n) (k + 1) (tagSub :: (d :: rest)) =
      (match dec (n := n) k (d :: rest) with
       | some (e₁, c₁) =>
           match dec (n := n) k ((d :: rest).drop c₁) with
           | some (e₂, c₂) => some (.sub e₁ e₂, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [dec.eq_def]
  simp only [tagSub_eq, tagCoord_eq, tagConst_eq, tagAdd_eq]
  norm_num

/-- **mul 分支的方程引理**（字面 cons 形态）。

**两个必要条件**（第 140 / 141 轮实测）：
1. 右侧绑定变量名必须是 `e₁`、`e₂`，与 `dec.eq_def` 生成的完全一致；
2. `norm_num` 之后需要 `rfl` 闭合 `List.drop c₁ (d :: rest)` 的呈现差异。 -/
theorem dec_mul_step (k : ℕ) (d : ℕ) (rest : List ℕ) :
    dec (n := n) (k + 1) (tagMul :: (d :: rest)) =
      (match dec (n := n) k (d :: rest) with
       | some (e₁, c₁) =>
           match dec (n := n) k ((d :: rest).drop c₁) with
           | some (e₂, c₂) => some (.mul e₁ e₂, 1 + c₁ + c₂)
           | none => none
       | none => none) := by
  rw [dec.eq_def]
  simp only [tagMul_eq, tagCoord_eq, tagConst_eq, tagAdd_eq, tagSub_eq]
  norm_num

/-- **一般消费引理**：对任意 `SExpr` 与任意后缀成立。

**带后缀是必须的**（第 113 轮发现）：二元节点的归纳步里，左子树的递归调用输入是
`enc a ++ (enc b ++ suffix)`，不是裸的 `enc a`。

### 二元分支的完整配方（第 143 / 144 轮确定）

```
cases ha' : enc a with                 -- 把 enc a 变成构造子
| cons hd tl =>
    rw [List.cons_append]              -- ★ 把 (hd :: tl) ++ X 还原成 cons
    rw [dec_X_step]                    -- 方程引理现在能触发
    rw [show hd :: (tl ++ X) = ((hd :: tl) ++ X) from rfl]   -- ★ 反向结合律
    rw [← ha']                         -- 把 enc a 放回去，让归纳假设匹配
    rw [iha]; simp only []             -- 归约 match some
    rw [drop_enc_append]; rw [ihb]
```

**两个 ★ 行是第 143 / 144 轮各自找到的**：前一行让方程引理能触发，
后一行让归纳假设能匹配——**它们方向相反，缺一个都不行**。 -/
theorem dec_enc_append (e : SExpr n) :
    ∀ (suffix : List ℕ) (fuel : ℕ), encLen e ≤ fuel →
      dec (n := n) fuel (enc (n := n) e ++ suffix) = some (e, encLen e) := by
  induction e with
  | coord p axis =>
      intro suffix fuel h
      simp only [encLen] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
      show dec (n := n) (f + 3) ((tagCoord :: p :: axis.val :: []) ++ suffix) =
        some (.coord p axis, 3)
      simp only [List.cons_append, List.nil_append]
      rw [show (f + 3) = ((f + 1) + 1) + 1 from rfl]
      rw [dec.eq_def]
      simp only [tagCoord_eq, tagConst_eq, tagAdd_eq]
      norm_num
  | const m =>
      intro suffix fuel h
      simp only [encLen] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
      show dec (n := n) (f + 2) ((tagConst :: m :: []) ++ suffix) = some (.const m, 2)
      simp only [List.cons_append, List.nil_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [dec.eq_def]
      simp only [tagCoord_eq, tagConst_eq, tagAdd_eq]
      norm_num
  | add a b iha ihb =>
      intro suffix fuel h
      simp only [encLen] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLen_ge_two a; have h2 := encLen_ge_two b; omega⟩
      have ha : encLen a ≤ f + 1 := by omega
      have hb : encLen b ≤ f + 1 := by omega
      show dec (n := n) (f + 2) ((tagAdd :: (enc a ++ enc b)) ++ suffix) =
        some (.add a b, 1 + encLen a + encLen b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      cases ha' : enc a with
      | nil => exact absurd ha' (enc_ne_nil a)
      | cons hd tl =>
        rw [List.cons_append]
        rw [dec_add_step (n := n) (k := f + 1) (d := hd) (rest := tl ++ (enc b ++ suffix))]
        rw [show (hd :: (tl ++ (enc b ++ suffix))) = ((hd :: tl) ++ (enc b ++ suffix)) from rfl]
        rw [← ha']
        rw [iha (enc b ++ suffix) (f + 1) ha]
        simp only []
        rw [show List.drop (encLen a) (enc a ++ (enc b ++ suffix)) = enc b ++ suffix from by
          rw [← enc_length (n := n) a]
          simp]
        rw [ihb suffix (f + 1) hb]
  | sub a b iha ihb =>
      intro suffix fuel h
      simp only [encLen] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLen_ge_two a; have h2 := encLen_ge_two b; omega⟩
      have ha : encLen a ≤ f + 1 := by omega
      have hb : encLen b ≤ f + 1 := by omega
      show dec (n := n) (f + 2) ((tagSub :: (enc a ++ enc b)) ++ suffix) =
        some (.sub a b, 1 + encLen a + encLen b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      cases ha' : enc a with
      | nil => exact absurd ha' (enc_ne_nil a)
      | cons hd tl =>
        rw [List.cons_append]
        rw [dec_sub_step (n := n) (k := f + 1) (d := hd) (rest := tl ++ (enc b ++ suffix))]
        rw [show (hd :: (tl ++ (enc b ++ suffix))) = ((hd :: tl) ++ (enc b ++ suffix)) from rfl]
        rw [← ha']
        rw [iha (enc b ++ suffix) (f + 1) ha]
        simp only []
        rw [show List.drop (encLen a) (enc a ++ (enc b ++ suffix)) = enc b ++ suffix from by
          rw [← enc_length (n := n) a]
          simp]
        rw [ihb suffix (f + 1) hb]
  | mul a b iha ihb =>
      intro suffix fuel h
      simp only [encLen] at h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by
        have h1 := encLen_ge_two a; have h2 := encLen_ge_two b; omega⟩
      have ha : encLen a ≤ f + 1 := by omega
      have hb : encLen b ≤ f + 1 := by omega
      show dec (n := n) (f + 2) ((tagMul :: (enc a ++ enc b)) ++ suffix) =
        some (.mul a b, 1 + encLen a + encLen b)
      rw [List.cons_append]
      rw [show (f + 2) = (f + 1) + 1 from rfl]
      rw [List.append_assoc]
      cases ha' : enc a with
      | nil => exact absurd ha' (enc_ne_nil a)
      | cons hd tl =>
        rw [List.cons_append]
        rw [dec_mul_step (n := n) (k := f + 1) (d := hd) (rest := tl ++ (enc b ++ suffix))]
        rw [show (hd :: (tl ++ (enc b ++ suffix))) = ((hd :: tl) ++ (enc b ++ suffix)) from rfl]
        rw [← ha']
        rw [iha (enc b ++ suffix) (f + 1) ha]
        simp only []
        rw [show List.drop (encLen a) (enc a ++ (enc b ++ suffix)) = enc b ++ suffix from by
          rw [← enc_length (n := n) a]
          simp]
        rw [ihb suffix (f + 1) hb]

/-- **结论：结构经 token 流无损**——对**任意** `SExpr`，编码后以足够的 fuel 解码回来得到原表达式，
且消费数精确等于 `encLen`。

**这是第 109 轮开始的 19 次尝试的终点。** -/
theorem structure_survives_tokens_full (e : SExpr n) :
    dec (n := n) (encLen e) (enc (n := n) e) = some (e, encLen e) := by
  have h := dec_enc_append e [] (encLen e) (Nat.le_refl _)
  rwa [List.append_nil] at h

end ConstraintTokenizer

end Lattice.Geo
