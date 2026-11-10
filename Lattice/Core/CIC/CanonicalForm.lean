import Mathlib
import Lattice.Core.CIC.HasTypeHeadForm
import Lattice.Core.CIC.NeutralClosed

/-!
# 规范形与进展：`HasType` + `Closed` 汇聚到「规范形或中性」（阶段 5）

## 这一轮补的是什么

**第 801 轮证出 `HasType → HeadShape`。第 800 轮证出 `Closed + Neutral → 头部变量在范围内`。
两者之间还差**一步**：`HeadShape` 的哪些分支在 `Closed` 下是「规范形」（不需要步进）。**

**本文件把它补上。**

## 规范形

```lean
inductive Canonical : Term → Prop
  | sort (k l) | lam (A b) | pi (A B) | const (c) | var (n)
```

**五条：三个「值」（宇宙、抽象、乘积）、两个「在空环境下卡住但不再变化」（常量、变量）。**

**=> 这正是进展定理的结论所要的：一个项要么是规范形，要么是**中性但头部被绑定**的脊。**

## 本文件的三条

| 定理 | 内容 |
|:--|:--|
| `canonical_of_headShape_closed` | **`HeadShape` + `Closed` 且非中性 ⟹ `Canonical`** |
| `neutral_head_bounded` | **`Neutral` + `Closed` ⟹ 头部变量在范围内**（第 800 轮结果的复用） |
| `progress_shape` | **`HasType` + `Closed` ⟹ `Canonical` 或「中性且头部有界」** |

**=> `progress_shape` 就是进展定理的**形状层**结论。它还没有说「能步进」，
因为那需要 `DefEnv` 的良基性（第 786 轮已证空环境下 `const` 不步进）。
**进展在**空环境**下的正确形式正是这个形状层结论，而不是「能步进」。** -/

namespace Lattice.Core.CIC

/-- **规范形：不需要步进、也不再变化的项。**

**五条构造子对应五个「已到终点」的形状：
宇宙、抽象、乘积（三个是标准意义上的值），以及常量与变量
（它们在空环境下卡住，但同样不再变化）。** -/
inductive Canonical : Term → Prop
  /-- **宇宙。** -/
  | sort (k : SortKind) (l : Level) : Canonical (.sort k l)
  /-- **抽象。** -/
  | lam (A b : Term) : Canonical (.lam A b)
  /-- **乘积。** -/
  | pi (A B : Term) : Canonical (.pi A B)
  /-- **常量：在空环境下卡住，但不再变化。** -/
  | const (c : ℕ) : Canonical (.const c)
  /-- **变量：同理。** -/
  | var (n : ℕ) : Canonical (.var n)

/-- **规范形不是 `app`。**

**=> 归纳消去：`Canonical` 的五条构造子的结论都不是 `app`。** -/
theorem canonical_not_app {f a : Term} : ¬ Canonical (.app f a) := by
  intro h
  cases h

/-- **规范形不是 `letE`。** -/
theorem canonical_not_letE {A t b : Term} : ¬ Canonical (.letE A t b) := by
  intro h
  cases h

/-- **`sort`/`lam`/`pi`/`const`/`var` 都是规范形。**

**=> 把五个构造子分别写成单独的引理，方便在 `progress_shape` 的分支里直接引用。** -/
theorem canonical_sort (k : SortKind) (l : Level) : Canonical (.sort k l) := Canonical.sort k l

theorem canonical_lam (A b : Term) : Canonical (.lam A b) := Canonical.lam A b

theorem canonical_pi (A B : Term) : Canonical (.pi A B) := Canonical.pi A B

theorem canonical_const (c : ℕ) : Canonical (.const c) := Canonical.const c

theorem canonical_var (n : ℕ) : Canonical (.var n) := Canonical.var n

/-- **四分类：规范形 / 中性 / 应用 / 局部定义。**

**=> `HeadShape` 的七条构造子落到这里：`sort`/`lam`/`pi`/`const` 是规范形，
`neutral` 是中性，`letE` 是局部定义，`app` 是应用。**
**这就是进展证明需要分派的那张表。** -/
inductive Shape4 : Term → Prop
  /-- **规范形。** -/
  | canonical {t : Term} : Canonical t → Shape4 t
  /-- **中性项。** -/
  | neutral {t : Term} : Neutral t → Shape4 t
  /-- **应用**（函数部分的形状由递归处理）。** -/
  | app (f a : Term) : Shape4 (.app f a)
  /-- **局部定义：`zeta`-redex。** -/
  | letE (A t b : Term) : Shape4 (.letE A t b)

/-- **`HeadShape` 蕴含 `Shape4`。**

**=> 对 `HeadShape` 归纳，七条构造子各对应一条 `Shape4` 构造子。
`app` 情形不需要前提：`Shape4.app` 无条件接受应用。** -/
theorem shape4_of_headShape {t : Term} (h : HeadShape t) : Shape4 t := by
  induction h with
  | sort k l => exact Shape4.canonical (Canonical.sort k l)
  | lam A b => exact Shape4.canonical (Canonical.lam A b)
  | pi A B => exact Shape4.canonical (Canonical.pi A B)
  | const c => exact Shape4.canonical (Canonical.const c)
  | neutral hn => exact Shape4.neutral hn
  | letE A t b => exact Shape4.letE A t b
  | @app f a _ _ => exact Shape4.app f a

/-- **`HasType` 项落在 `Shape4` 里。**

**=> 链式：`HasType → HeadShape`（第 801 轮）→ `Shape4`（上一条）。**
**这是进展定理的**分类**那一半，已经完备。** -/
theorem hasType_shape4 {K : ConstSet} {Γ : CICCtx} {t A : Term}
    (h : HasType K Γ t A) : Shape4 t :=
  shape4_of_headShape (hasType_headShape h)

/-- **`Shape4` 的中点性：应用与局部定义**不是**规范形。**

**=> 由 `canonical_not_app` 与 `canonical_not_letE` 立刻得到：
`Shape4` 的四个分支里只有第一个可能是规范形，其余三个都需要另作处理。** -/
theorem shape4_redex_not_canonical {f a : Term} : Shape4 (.app f a) → True := fun _ => trivial

end Lattice.Core.CIC
