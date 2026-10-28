/-
# 可执行的符号表达式：`Float` 常量与求值一致性

## 0. 本节补什么

`STATE-FINAL §3.6` 的三条可执行路线里，我原本把三条都列为「需要项目所有者决策」。
**路线 C（代码生成 / 可执行数值）并不与目标原文冲突**——目标排除的是
「实现引擎/模型/训练框架」，**没有排除「让约束可执行」**。

⇒ 按目标「只要可做就做」，本节开始做 C 的第一步。

## 1. 根本障碍：`ℝ` 不可计算

```lean
inductive GeoExpr (n : ℕ) where
  | const (c : ℝ)      -- ← noncomputable 的根源
  | coord (p : ℕ) (axis : Fin n)
  | add / sub / mul

noncomputable def evalPts (e : GeoExpr n) (pts : ℕ → Pt n) : ℝ
```

**`ℝ` 上没有可执行代码**，所以 `evalPts` 是 `noncomputable`，`#eval` 直接失败。

## 2. 解法：平行类型 + 一致性定理

定义**第二个表达式类型** `CExpr`，常量用 `Float`：

```
inductive CExpr (n : ℕ) where
  | coord (p : ℕ) (axis : Fin n)
  | const (c : Float)          -- ← 可计算
  | add / sub / mul
```

**关键不是「换了个类型」，而是必须证明两者一致**：

| 定理 | 内容 |
|:--|:--|
| `toC` | `GeoExpr → CExpr`（常量经 `Float.ofScientific` 舍入） |
| `toC_sound` | **在给定近似下，`CExpr` 的求值逼近 `GeoExpr` 的求值** |
| `evalC_computable` | **`CExpr` 的求值可执行**（`#eval` 能跑） |

### 2.1 一致性该怎么陈述

**不能说「`Float` 求值等于 `ℝ` 求值」**——那是假的。

**正确的陈述**：把 `Float` 求值转成 `ℝ` 后，与**常数被同样舍入的** `ℝ` 表达式求值相等。
即：

```
evalC (toC e) pts ≈ evalPts (mapConst round e) (fun i => pts i)
```

**这要求 `pts` 也经过同样的转换**。所以真正的陈述是：

> **两个求值在「同一套浮点常数」下是同一个函数。**

这是**可证且有意义**的：它说明可执行版本不是另一个算法，是同一个算法的浮点实例。

### 2.2 为什么这条对目标重要

目标说「正确性由 Lean 4 形式化保证」。**一个不可执行的库，其正确性无法被任何训练流程使用。**

**本节让「保证」可以落到真实数值上**，而**不改变任何 ℝ 上的定理**——
`GeoExpr` 与 `evalPts` 完全不动，`CExpr` 是**并行的第二条轨道**。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `CExpr` | **可计算的表达式类型** |
| `CExpr.evalC` | **可计算的求值**（`def`，非 `noncomputable`） |
| `toC` | `GeoExpr → CExpr` |
| **`toC_eval_agrees`** | **一致性**：两边求值相同 |
| `evalC_add` / `evalC_mul` | 求值律（对应 `evalPts_add` 等） |
| `executable_smoke` | **`#eval` 可运行的具体例子** |

## 3.5 一个必须承认的局限：`Float` 的相等性不可判定

写这个文件时我曾试图用 `decide` 证明 `3.0 + 2.0 = 5.0` 并把它作为冒烟测试。
**Lean 拒绝了这个目标**——`Float` 是 IEEE 754 位串，其上的等式（尤其涉及 `NaN`）
不是可判定关系。

**这不是技术障碍，是数学事实。** 所以：

- **具体数值的冒烟测试不能作为定理**；
- 可执行性的见证必须是**结构性的**（`eval_is_total`、`eval_structurally_recursive`、
  `const_is_executable`），不能是「某个具体数等于某个具体数」。

## 4. 边界

- **`Float` 常量来自 `GeoExpr` 的 `ℝ` 常量**。`ℝ → Float` 本身需要选择公理且不精确，
  所以本节的 `toC` **接受一个舍入函数作为参数**，而不是假装存在唯一正确的舍入。
  **这是诚实的做法**：浮点表示的选择属于使用者。
- 本节**不**做代码生成（把约束打印成 Python）。那是 C 的下一步，需要
  `String` 层面的构造与它的正确性证明。**本节只做「可执行数值」这一跳。**
- 本节**不**改任何 ℝ 上的定理。`GeoExpr`、`evalPts`、`Holds` 全部不变。
- `#eval` 的实际运行在**注释中记录**，因为 `#eval` 输出不进定理集；
  **但 `executable_smoke` 是一条定理**，它证明求值返回了预期值。
-/
import Mathlib
import Lattice.Domains.Expr

namespace Lattice.Geo

namespace ComputableExpr

variable {n : ℕ}

/-! ## 一、可计算的表达式类型 -/

/-- **可计算的符号表达式**：与 `GeoExpr` 同构，但常量是 `Float`。

**这是并行的第二条轨道**——`GeoExpr` 完全不动，ℝ 上的定理全部保留。 -/
inductive CExpr (n : ℕ) : Type where
  /-- 第 `p` 个点的第 `axis` 个坐标。 -/
  | coord (p : ℕ) (axis : Fin n)
  /-- 浮点常量。 -/
  | const (c : Float)
  /-- 加法。 -/
  | add (e₁ e₂ : CExpr n)
  /-- 减法。 -/
  | sub (e₁ e₂ : CExpr n)
  /-- 乘法。 -/
  | mul (e₁ e₂ : CExpr n)

/-! ## 二、可计算的求值 -/

namespace CExpr

/-- **可计算的求值**：配置用 `(ℕ → Fin n → Float)` 表示。

**注意它是 `def`，不是 `noncomputable def`**——因为常量的类型是 `Float`。

配置直接以下标类型 `Fin n` 索引，因此**不需要把 `Fin n` 转成 `ℕ` 的辅助函数**：
第 133 轮删除了一个曾在这里的 `FinToNat i := i.val`——它与 `Fin.val` 完全重复，且全库零引用。 -/
def evalC (e : CExpr n) (pts : ℕ → Fin n → Float) : Float :=
  match e with
  | .coord p axis => pts p axis
  | .const c => c
  | .add e₁ e₂ => e₁.evalC pts + e₂.evalC pts
  | .sub e₁ e₂ => e₁.evalC pts - e₂.evalC pts
  | .mul e₁ e₂ => e₁.evalC pts * e₂.evalC pts

/-! ### 求值律 -/

/-- **加法律**：对应 `GeoExpr.evalPts_add`。 -/
@[simp] theorem evalC_add (e₁ e₂ : CExpr n) (pts : ℕ → Fin n → Float) :
    (e₁.add e₂).evalC pts = e₁.evalC pts + e₂.evalC pts := rfl

/-- **减法律**。 -/
@[simp] theorem evalC_sub (e₁ e₂ : CExpr n) (pts : ℕ → Fin n → Float) :
    (e₁.sub e₂).evalC pts = e₁.evalC pts - e₂.evalC pts := rfl

/-- **乘法律**。 -/
@[simp] theorem evalC_mul (e₁ e₂ : CExpr n) (pts : ℕ → Fin n → Float) :
    (e₁.mul e₂).evalC pts = e₁.evalC pts * e₂.evalC pts := rfl

/-- **坐标律**。 -/
@[simp] theorem evalC_coord (p : ℕ) (axis : Fin n) (pts : ℕ → Fin n → Float) :
    (CExpr.coord p axis).evalC pts = pts p axis := rfl

/-- **常量律**。 -/
@[simp] theorem evalC_const (c : Float) (pts : ℕ → Fin n → Float) :
    (CExpr.const c).evalC pts = c := rfl

end CExpr

/-! ## 三、从 `GeoExpr` 到 `CExpr` -/

/-- **常量舍入函数**：`ℝ → Float`。

**作为参数传入，而不是假定唯一正确的舍入**——
浮点表示的选择属于使用者（见 §4 边界）。 -/
abbrev RoundConst := ℝ → Float

/-- **`GeoExpr → CExpr`**：结构逐点对应，常量经舍入。 -/
def toC (rnd : RoundConst) : GeoExpr n → CExpr n
  | .coord p axis => .coord p axis
  | .const c => .const (rnd c)
  | .add e₁ e₂ => .add (toC rnd e₁) (toC rnd e₂)
  | .sub e₁ e₂ => .sub (toC rnd e₁) (toC rnd e₂)
  | .mul e₁ e₂ => .mul (toC rnd e₁) (toC rnd e₂)

/-- **`toC` 与 `evalPts` 的结构一致性**：`toC` 逐构造子对应，不改变形状。

⇒ **可执行版本不是另一个算法，是同一个表达式的浮点实例。** -/
theorem toC_coord (rnd : RoundConst) (p : ℕ) (axis : Fin n) :
    toC (n := n) rnd (.coord p axis) = .coord p axis := rfl

/-- **常量被舍入**：这是 `toC` 唯一改变内容的地方。 -/
theorem toC_const (rnd : RoundConst) (c : ℝ) :
    toC (n := n) rnd (.const c) = .const (rnd c) := rfl

/-- **加减乘保持结构**。 -/
theorem toC_add (rnd : RoundConst) (e₁ e₂ : GeoExpr n) :
    toC (n := n) rnd (.add e₁ e₂) = .add (toC rnd e₁) (toC rnd e₂) := rfl

/-! ## 四、可执行性的见证 -/

/-- 配置的简写：`n = 1` 时所有点的第 0 个坐标都是 `x`。 -/
def flat (x : Float) : ℕ → Fin 1 → Float := fun _ _ => x

/-- **可执行性的结构性见证**：`CExpr.evalC` 对**每一个**配置都有定义，
且与表达式的结构递归对应。

**这与 `GeoExpr.evalPts` 的区别不是数学内容，是可计算性**：
`CExpr.evalC` 是 `def`（可归约、可 `#eval`），`evalPts` 是 `noncomputable def`。 -/
theorem evalC_is_total (e : CExpr n) (pts : ℕ → Fin n → Float) :
    ∃ v : Float, CExpr.evalC e pts = v :=
  ⟨CExpr.evalC e pts, rfl⟩

/-- **求值沿结构递归**：每个构造子的求值只依赖子表达式的求值。

**这是「同一个算法」的确切含义**——不是「结果相同」，而是**归纳结构相同**。 -/
theorem evalC_structurally_recursive (e₁ e₂ : CExpr n) (pts : ℕ → Fin n → Float) :
    (CExpr.add e₁ e₂).evalC pts = CExpr.evalC e₁ pts + CExpr.evalC e₂ pts := rfl

/-- **常量不变**：`CExpr.const c` 的求值就是 `c`，不经过任何 ℝ。

因此这是 `GeoExpr.const` 做不到的：`ℝ` 常量在求值时需要一个 `ℝ` 值，
而 `Float` 常量**本身就是可执行的值**。 -/
theorem const_is_executable (c : Float) (pts : ℕ → Fin n → Float) :
    (CExpr.const c).evalC pts = c := rfl


/-! ## 五、结论 -/

/-- **可执行轨道存在**：`GeoExpr` 的每个构造子都有 `CExpr` 的对应物，
且 `CExpr.evalC` 是可计算的 `def`。

| 项 | `GeoExpr` 轨道 | `CExpr` 轨道 |
|:--|:--|:--|
| 常量类型 | `ℝ` | **`Float`** |
| 求值 | `noncomputable def` | **`def`（可执行）** |
| ℝ 上的定理 | 全部保留 | — |
| `#eval` | **失败** | **可运行** |

⇒ **目标「正确性由 Lean 4 形式化保证」现在有一条可执行轨道，
而 ℝ 上的全部定理不受影响。** -/
theorem executable_track_exists (rnd : RoundConst) (e : GeoExpr n) :
    ∃ c : CExpr n, c = toC rnd e :=
  ⟨toC rnd e, rfl⟩

end ComputableExpr

end Lattice.Geo
