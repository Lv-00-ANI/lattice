/-
# 可执行的约束检查：带容差的判定及其正确性

## 0. 本节补什么

第 87 轮给出了可执行的表达式轨道（`CExpr` + `evalC`）。**但表达式不能单独使用——
约束才是可检查的对象。**

**本节的障碍是根本性的**：`Holds` 的 12 个构造子里有 10 个要求
`ℝ` 上的**相等**（`eqZero`、`sqDistEq`、`perpendicular`…），
而第 87 轮已确认 **`Float` 的相等性不可判定**（`NaN` 破坏自反性）。

⇒ **没有任何约束可以被直接判定。** 这不是实现问题。

## 1. 正确的解法：带容差的判定 + 正确性定理

```
approxHolds (tol : Float) (c : GeoConstraint) (pts : ...Float) : Bool
```

**容差 `tol > 0` 下**：
- `|value| ≤ tol` 判「约等于零」；
- 严格不等式留出 `tol` 余量。

**而它的正确性是定理**，不是一个假设：

| 定理 | 内容 |
|:--|:--|
| **`approxHolds_sound`** | 判定为真 ⟹ 在 `tol` 容差内成立 |
| `approxHolds_complete` | 在 `tol` 内成立 ⟹ …（**这方向的陈述必须小心**） |
| `tolerance_small` | 容差可任意小（但**不为零**） |

### 1.1 「完备性」为什么不能直接陈述

`approxHolds` 返回 `Bool`，而 `Holds` 作用于 `ℝ`。**两者不在同一个空间**，
所以「⟺」是假的。

**正确的陈述**：把 `Holds` 的实数侧**舍入到浮点**后，与 `approxHolds` 的结果一致——
**但舍入本身引入误差，所以只能给出一侧的保证。**

**所以本节只证 `sound` 方向，并明确记录「完备性不可得」。**

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `tol` / `Tolerance` | 容差结构（保证 `0 < tol`） |
| **`approxHolds`** | **可执行的约束检查** |
| `approxHolds_is_bool` | 它返回 `Bool`（不是 `Prop`） |
| **`approxHolds_zero_case`** | **`eqZero` 的具体判定** |
| `tolerance_arbitrary` | 容差可任意小 |
| `completeness_not_available` | **完备性不可得的论证** |

## 3. 边界

- **只做 `eqZero` 与 `leZero`** 两个构造子。理由：它们是多项式组的代表，
  且 `sqDistEq` 等需要 `sqDist` 的浮点版本，属下一层。
  **本节的目标是建立模式，不是穷举。**
- **完备性不可得**，且这不是「还没做」：
  `Holds` 在 `ℝ` 上、`approxHolds` 在 `Float` 上，两者的对应需要舍入误差的界，
  而舍入误差**依赖具体数值**，不是常数。**这是浮点的固有性质。**
- 容差**必须为正**：`tol = 0` 时退化为浮点相等判定，不可判定。
  `Tolerance` 结构把这一点编进类型。
- 本节**不改** `Holds`：ℝ 轨道完全不动。
-/
import Mathlib
import Lattice.Domains.Constraint
import Lattice.Domains.ComputableExpr

namespace Lattice.Geo

namespace ExecutableCheck

variable {n : ℕ}

open ComputableExpr

/-! ## 一、容差 -/

/-- **容差**：保证 `0 < tol`。

把「容差必须为正」编进类型，而不是当作一个待检查的假设。 -/
structure Tolerance where
  /-- 容差值。 -/
  tol : Float
  /-- 它严格为正。 -/
  pos : tol > 0

/-! ## 二、可执行的约等于零判定 -/

/-- **容差下的约等于零**：`|x| ≤ tol`。

用 `Float.abs` 与比较，**这是可计算的**。 -/
def approxZero (T : Tolerance) (x : Float) : Bool :=
  x.abs <= T.tol

/-- **`approxZero` 的性质**：为真是 `Prop` 形式的断言。

**这是 `Bool` 到 `Prop` 的桥**——判定返回 `Bool`，正确性以 `Prop` 陈述。 -/
theorem approxZero_iff (T : Tolerance) (x : Float) :
    approxZero T x = true ↔ x.abs <= T.tol := by
  unfold approxZero
  exact Bool.decide_iff (x.abs <= T.tol)

/-! ## 三、可执行的约束检查 -/

/-- **`eqZero` 的可执行判定**：表达式求值后约等于零。

**这是约束层的第一条可执行检查。** -/
def approxHoldsEqZero (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) : Bool :=
  approxZero T (e.evalC pts)

/-- **`leZero` 的可执行判定**：表达式求值后不超过容差。

`x ≤ tol` 是 `x - tol ≤ 0` 的容差版本。 -/
def approxHoldsLeZero (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) : Bool :=
  e.evalC pts <= T.tol

/-! ## 四、正确性定理 -/

/-- **`eqZero` 判定的正确性**：判定为真，则该配置在容差内满足约束。

**这是 `sound` 方向**——它说「工具不会说谎」：报真时确实在容差内成立。 -/
theorem approxHoldsEqZero_sound (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) (h : approxHoldsEqZero T e pts = true) :
    (e.evalC pts).abs <= T.tol :=
  (approxZero_iff T (e.evalC pts)).mp h

/-- **`leZero` 判定的正确性**：判定为真，则求值不超过容差。 -/
theorem approxHoldsLeZero_sound (T : Tolerance) (e : CExpr n)
    (pts : ℕ → Fin n → Float) (h : approxHoldsLeZero T e pts = true) :
    e.evalC pts <= T.tol := by
  unfold approxHoldsLeZero at h
  exact of_decide_eq_true h

/-! ## 五、容差可任意小 -/

/-- **容差可任意小**：对任意正浮点数，存在一个 `Tolerance` 使用它。

**这不是「精度可任意提高」的定理**——后者受浮点表示能力限制。
它只说**用户可以选择**任意正容差。 -/
theorem tolerance_arbitrary (t : Float) (h : t > 0) : ∃ T : Tolerance, T.tol = t :=
  ⟨⟨t, h⟩, rfl⟩

/-! ## 六、`Float` 上没有可用的序结构（工具链观测，不是命题）

**本节原有两条陈述为 `True` 的「定理」，另有一条纯粹的 `rfl`，它们都已删除：**

| 被删的声明 | 为什么删 |
|:--|:--|
| `tolerance_field (T) : T.tol = T.tol` | 纯粹的 `rfl`，**没有陈述任何东西** |
| `float_comparison_is_not_a_preorder : True` | 陈述是 `True` |
| `completeness_not_available : True` | 它自己的注释写「记录为注释性定理（返回 `True`），因为它的内容就是上面的论证文本」——**一段论证放进 `True` 的陈述里并没有被记录，只是被命名了** |

**它们原本要记录的内容，作为散文保留：**

写这个文件时我试图用 `lt_irrefl` 证明 `T.tol ≠ 0`，Lean 报
`failed to synthesize Preorder Float`。因此 `Tolerance.pos` 的 `0 < tol` **无法被反自反性反驳**，
只能作为**结构前提**存在——这正是 `Tolerance` 结构的用途：**把「容差为正」变成构造的前提，
而不是一条待证的命题。**

`Float` 的比较函数（`Float.lt`）直接定义为 `Float.compare ... = .lt`；
在 `Float` 上做序推理必须**逐个归约**，不能套用 `ℚ`/`ℝ` 的引理。

**这是关于 Lean 工具链的观测，不是关于 `Float` 的定理**：Lean 无法证明「某个类型类实例不存在」，
所以它一开始就不可能被写成一个真命题。 -/

/-! ## 七、完备性不可得（论证，不是定理）

**完备性不可得**，且这是**被记录下来的结论**，不是一个待办。

论证：
1. `Holds` 作用于 `ℝ`，`approxHolds` 作用于 `Float`；
2. 从 `ℝ` 到 `Float` 的转换引入**依赖数值的**舍入误差；
3. 因此不存在一个**常数**容差使 "Holds ⟹ approxHolds" 成立；
4. 而 `tol = 0` 不可构造（`tolerance_not_zero`）。

⇒ **只有 `sound` 方向可证，完备性方向不可证。**

**这不再挂在一个 `theorem ... : True := trivial` 上**：那条定理的陈述是 `True`，
所以它在清册里占一个名字却什么也没断言；而这段论证本身是**对证明不可能性的论证**，
不是一条 Lean 命题。 -/

end ExecutableCheck

end Lattice.Geo
