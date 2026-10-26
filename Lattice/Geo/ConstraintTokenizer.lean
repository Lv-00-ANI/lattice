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
import Lattice.Geo.Expr

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

/-- **未做的一步**：二元节点的往返归纳。

`drop_enc_append` 给出了「删掉左子树后剩下右子树」，
但归纳步还需要「`dec fuel` 在左子树编码上恰好消费 `encLen` 个 token」——
那是另一条需要对 `dec` 做归纳的引理。**本轮未做。** -/
theorem binary_induction_not_done : True := trivial

end ConstraintTokenizer

end Lattice.Geo
