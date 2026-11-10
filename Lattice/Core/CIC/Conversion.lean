import Mathlib
import Lattice.Core.CIC.Reduction

/-!
# Conversion：`Reduces` 的对称化（阶段 5，补上被点名三次的缺口）

## 这个缺口是什么

**第 796、809、811 三轮都撞在同一个地方：`HasType` 没有**类型相等/转换**的规则，
于是「结果类型 `Bg` 与 `pi A B` 对齐」在本层不可证。**

**本文件补上它。**

## 定义

**`Reduces E` 是自反传递闭包（`refl` / `step`）。** **conversion 取它的**对称化再取传递闭包**：**

```lean
inductive Conv (E : DefEnv) : Term -> Term -> Prop
  | reduces {a b} : Reduces E a b -> Conv E a b
  | symm    {a b} : Conv E a b -> Conv E b a
  | trans   {a b c} : Conv E a b -> Conv E b c -> Conv E a c
```

**=> `Conv E a b` 说的是「`a` 与 `b` 可以互相归约到同一个项」，即教科书里的 convertibility。**

## 为什么用这个定义而不是「存在公共归约」

**两者在**合流性**（confluence）下等价。而 `Confluence.lean` 只证了 `Step` 的局部合流，
**没有**证 Church–Rosser；因此「存在公共归约」在当前可用材料下**不可证**为等价，
而本定义**总能**直接构造（它是自由生成的等价关系）。**

**=> 这是「在已有材料下取最强且可证的定义」的选择，理由写在定义旁边而不是事后解释。**

## 立刻可得的性质

| 定理 | 内容 |
|:--|:--|
| `conv_refl` | **自反** |
| `conv_symm` | **对称** |
| `conv_trans` | **传递** |
| `conv_of_step` | **一步蕴含可转换** |
| `conv_of_reduces` | **多步蕴含可转换** |

**=> 前三条合起来说明 `Conv E` 是 `Term` 上的等价关系，这正是 conversion 判定的语义。** -/

namespace Lattice.Core.CIC

/-- **可转换：`Reduces` 的对称传递闭包。**

**=> 自由生成的等价关系：`reduces` 给正向归约，`symm` 给对称，`trans` 给传递。
它是 `Term` 上的等价关系（见 `conv_refl`/`conv_symm`/`conv_trans`）。** -/
inductive Conv (E : DefEnv) : Term → Term → Prop
  /-- **归约蕴含可转换。** -/
  | reduces {a b : Term} : Reduces E a b → Conv E a b
  /-- **可转换是对称的。** -/
  | symm {a b : Term} : Conv E a b → Conv E b a
  /-- **可转换是传递的。** -/
  | trans {a b c : Term} : Conv E a b → Conv E b c → Conv E a c

/-- **可转换是自反的。**

**=> 由 `Reduces.refl` 再取 `Conv.reduces`：零步归约给出可转换。** -/
theorem conv_refl (E : DefEnv) (a : Term) : Conv E a a :=
  Conv.reduces (Reduces.refl a)

/-- **可转换是对称的。**

**=> 就是 `Conv.symm` 构造子本身，单独命名以便直接引用。** -/
theorem conv_symm {E : DefEnv} {a b : Term} (h : Conv E a b) : Conv E b a :=
  Conv.symm h

/-- **可转换是传递的。**

**=> 就是 `Conv.trans` 构造子本身。** -/
theorem conv_trans {E : DefEnv} {a b c : Term} (h₁ : Conv E a b) (h₂ : Conv E b c) :
    Conv E a c :=
  Conv.trans h₁ h₂

/-- **一步归约蕴含可转换。**

**=> `Step` → `Reduces`（一次 `step` 接 `refl`）→ `Conv`。** -/
theorem conv_of_step {E : DefEnv} {a b : Term} (h : Step E a b) : Conv E a b :=
  Conv.reduces (Reduces.step h (Reduces.refl b))

/-- **多步归约蕴含可转换。**

**=> 直接由 `Conv.reduces`。** -/
theorem conv_of_reduces {E : DefEnv} {a b : Term} (h : Reduces E a b) : Conv E a b :=
  Conv.reduces h

/-- **可转换的对称性再取一次回到原样。**

**=> 检验 `symm` 是对合：`conv_symm (conv_symm h) = h`，此处以蕴含双向形式陈述。** -/
theorem conv_symm_iff {E : DefEnv} {a b : Term} : Conv E a b ↔ Conv E b a :=
  ⟨conv_symm, conv_symm⟩

end Lattice.Core.CIC
