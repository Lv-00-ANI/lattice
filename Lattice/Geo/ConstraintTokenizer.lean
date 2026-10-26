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

/-! ## 三、解码器（带 fuel） -/

/-- **解码器**：`fuel` 在前，避免在计算长度上递归。

fuel 不足时返回 `none`——这是正确行为，不是缺陷。 -/
def dec : ℕ → List ℕ → Option (SExpr n × List ℕ)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | _ + 1, t :: d :: rest =>
      if t = tagCoord then
        match rest with
        | axisVal :: rest' =>
            if h : axisVal < n then some (.coord d ⟨axisVal, h⟩, rest') else none
        | [] => none
      else if t = tagConst then some (.const d, rest)
      else none

/-! ## 四、往返（不需要递归的部分） -/

/-- **常量往返**：标记被还原，且不残留 token。 -/
theorem dec_enc_const (m fuel : ℕ) :
    dec (n := n) (fuel + 2) (enc (n := n) (.const m)) = some (.const m, []) := by
  show dec (n := n) (fuel + 2) (1 :: (m :: [])) = some (.const m, [])
  unfold dec
  simp

/-- **坐标往返**：`axis.val < n` 恒成立，故还原。 -/
theorem dec_enc_coord (p : ℕ) (axis : Fin n) (fuel : ℕ) :
    dec (n := n) (fuel + 2) (enc (n := n) (.coord p axis)) =
      some (.coord p axis, []) := by
  show dec (n := n) (fuel + 2) (0 :: (p :: (axis.val :: []))) =
    some (.coord p axis, [])
  unfold dec
  simp only [dif_pos axis.isLt]
  simp

/-! ## 五、结论 -/

/-- **结构经 token 流无损（叶子层）**：坐标与常量都能被编码后还原。

**这是第 109 轮失败之后真正交付的部分**：前缀编解码器的**叶子往返**成立。 -/
theorem structure_survives_tokens (p : ℕ) (axis : Fin n) (m fuel : ℕ) :
    dec (n := n) (fuel + 2) (enc (n := n) (.coord p axis)) = some (.coord p axis, []) ∧
    dec (n := n) (fuel + 2) (enc (n := n) (.const m)) = some (.const m, []) :=
  ⟨dec_enc_coord p axis fuel, dec_enc_const m fuel⟩

/-- **未做的一步，显式记录**：二元节点的往返。

需要「`dec` 在 `a ++ b` 上分解」的算术引理，而 `dec` 的递归调用参数是计算长度，
所以那条引理不能由结构归纳直接得到。**第 109 轮卡住的正是这里，本节仍未解决。** -/
theorem binary_not_done : True := trivial

end ConstraintTokenizer

end Lattice.Geo
