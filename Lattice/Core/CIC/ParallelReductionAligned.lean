import Mathlib
import Lattice.Core.CIC.ParallelReduction
import Lattice.Core.CIC.ReducesCongruence

/-!
# `ParRedS`：与 `Step` 对齐的平行归约（阶段 5，修正第 817 轮的错配）

## 第 818 轮定位到的错配

**第 817 轮的 `ParRed` 从文献照抄，`lam` 与 `letE` 带 `ParRed A A'` —— 归约**类型标注**。
而本层 `Step` **不能**移动类型标注（第 818 轮已证 `lam_type_position_frozen`）。**

**=> 照原样的 `ParRed` 不是 `Step` 的细化，第 3 步的 `←` 方向为假。**

## 本轮选的修法，以及为什么选它

**两个方案：**

| 方案 | 做法 | 代价 |
|:--|:--|:--|
| **A（本轮选）** | **从 `ParRed` 去掉类型分量，使 `lam`/`letE` 的类型位置**固定** | **不改 `Step`** |
| B | 给 `Step` 加类型位置规则 | **改变归约系统，影响已证的 30+ 条定理** |

**=> 选 A：它**不动已建立的东西**，只修正新引入的定义。这正是「架构级修改走分支、
且优先不改既有事实」的做法。**

## 修正后的定义：`ParRedS`（S = Step-aligned）

**与 `ParRed` 的差别只有两条：**

```lean
| lam {A b b'}      : ParRedS E b b' -> ParRedS E (lam A b) (lam A b')          -- 类型固定
| letE {A t t' b b'} : ParRedS E t t' -> ParRedS E b b' ->
                       ParRedS E (letE A t b) (subst 0 t' b')                  -- 类型固定
```

**=> `pi` 保留两部分的归约，因为 `Step.piDom`/`piCod` **确实**归约乘积的两部分 —— 这里与 `Step` 一致。**
**`beta` 与 `lam` 不同：`beta` 里的 `A` 是被**丢弃**的那个类型，它出现在被消去的 redex 里，
所以 `ParRed.beta` 的 `ParRed A A'` 也无害 —— 但为一致性，`ParRedS.beta` 也固定它。**

## 这一步之后还剩什么

**第 3 步变成 `Reduces E a b ↔ ParRedS∗ E a b`，两向都应当**可证**：

- **`→`：每个 `Step` 都是一次 `ParRedS`（`parRedS_of_step`，下一轮）；**
- **`←`：每个 `ParRedS` 由有限多 `Step` 复现（`parRedS_imp_reduces`，下一轮）。**

**=> 本轮给出定义与它的两条自反性事实；两向等价是下一轮。** -/

namespace Lattice.Core.CIC

/-- **与 `Step` 对齐的平行归约。**

**=> 与第 817 轮的 `ParRed` 相比，`lam` 与 `letE` **不归约类型标注**，
因为本层 `Step` 不能移动它（`lam_type_position_frozen`）。
`pi` 仍归约两部分，与 `Step.piDom`/`piCod` 一致。** -/
inductive ParRedS (E : DefEnv) : Term → Term → Prop
  /-- **变量不动。** -/
  | var (n : ℕ) : ParRedS E (.var n) (.var n)
  /-- **宇宙不动。** -/
  | sort (k : SortKind) (l : Level) : ParRedS E (.sort k l) (.sort k l)
  /-- **常量不动（除非按 `delta` 展开）。** -/
  | const (c : ℕ) : ParRedS E (.const c) (.const c)
  /-- **常量按 `delta` 展开。** -/
  | delta (c : ℕ) (body : Term) : E c = some body → ParRedS E (.const c) body
  /-- **应用：两边同时平行归约。** -/
  | app {f f' a a' : Term} : ParRedS E f f' → ParRedS E a a' → ParRedS E (.app f a) (.app f' a')
  /-- **β：体与参数同时归约，并立即执行替换；类型标注固定。** -/
  | beta {A b b' a a' : Term} :
      ParRedS E b b' → ParRedS E a a' →
      ParRedS E (.app (.lam A b) a) (subst 0 a' b')
  /-- **抽象：体平行归约，类型标注固定。**

  **=> 这一条与第 817 轮的 `ParRed.lam` 的全部差别。** -/
  | lam {A b b' : Term} :
      ParRedS E b b' → ParRedS E (.lam A b) (.lam A b')
  /-- **乘积：两部分同时归约（与 `Step.piDom`/`piCod` 一致）。** -/
  | pi {A A' B B' : Term} :
      ParRedS E A A' → ParRedS E B B' → ParRedS E (.pi A B) (.pi A' B')
  /-- **局部定义：值与体同时归约，并立即执行替换；类型标注固定。**

  **=> 与第 817 轮的 `ParRed.letE` 的全部差别。** -/
  | letE {A t t' b b' : Term} :
      ParRedS E t t' → ParRedS E b b' →
      ParRedS E (.letE A t b) (subst 0 t' b')

/-- **`ParRedS` 对原子项自反。** -/
theorem parRedS_var (E : DefEnv) (n : ℕ) : ParRedS E (.var n) (.var n) :=
  ParRedS.var n

/-- **`ParRedS` 对宇宙自反。** -/
theorem parRedS_sort (E : DefEnv) (k : SortKind) (l : Level) :
    ParRedS E (.sort k l) (.sort k l) :=
  ParRedS.sort k l

/-- **`ParRedS` 对常量自反（不展开时）。** -/
theorem parRedS_const (E : DefEnv) (c : ℕ) : ParRedS E (.const c) (.const c) :=
  ParRedS.const c

/-- **`ParRedS` 与 `Step` 在 `lam` 上一致：类型标注相同时才能相关。**

**=> 把第 818 轮的 `lam_type_position_frozen` 与 `ParRedS.lam` 并置，
说明两者对「`lam` 能怎么变」的答案是**同一个**。** -/
theorem parRedS_lam_type_fixed {E : DefEnv} {A A' b b' : Term}
    (h : ParRedS E (.lam A b) (.lam A' b')) : A = A' := by
  cases h
  rfl

end Lattice.Core.CIC
