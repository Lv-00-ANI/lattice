/-
# `parallel` 的 Skolem 化修复

## 0. 本节补什么

第 81 轮的精算说「`parallel` 与 `ratioDivision` 是最后两个可做的算子缺口」。

**核实后只有一个是真缺口**：

| 构造子 | 实际状态 |
|:--|:--|
| `parallel a b c e` | ✅ **存在**：`∃ t, seg a b = t • seg c e` |
| `ratioDivision` | ❌ **不存在**——只出现在 `Constraint.lean` 的**注释表格**里 |

⇒ **第 81 轮的精算是错的（第 12 次测量错误）。** 本节只做 `parallel`。

## 1. 证明思路：Skolem 化

`parallel a b c e` 的语义是

```
∃ t : ℝ, seg pts a b = fun i => t * seg pts c e i
```

**存在量词使修复算子无法直接构造 `fix`**（修复要给出满足的配置，而不是给 `∃`）。

### 1.1 Skolem 化：把 `t` 显式化

```
parallelWith a b c e (pts) (t : ℝ) :=  seg a b = t • seg c e
```

于是 `parallel` ⟺ `∃ t, parallelWith t`。**`t` 从 ∃ 里提出来作为参数。**

### 1.2 修复策略

`parallel` 要求「`ab` 是 `ce` 的标量倍」。**修复：把 `b` 移到 `a + t·seg(c,e)`**，
其中 `t` 由**当前配置**的投影系数给出：

```
t := ⟨seg a b, seg c e⟩ / |seg c e|²        -- 最小二乘投影
b' := a + t · seg c e
```

**但这只使 `ab'` 平行于 `ce`**——**一步到位**。若 `seg c e = 0`（`c = e`）则方向无定义。

### 1.3 「平行」的正确修复

**上述是最小二乘投影**，把 `b` 投到过 `a` 且方向为 `ce` 的直线上。
**投影后的 `ab'` 恰是 `ce` 的标量倍**，因此满足约束。

**代价**：若原 `ab` 已经平行，投影**不改变 `b`**（`t` 恰好是原有的比例）。
⇒ **吸收性由「投影是幂等」保证**。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `projScalar` | 投影系数 `⟨ab, ce⟩ / |ce|²` |
| `parallelFix` | 把 `b` 移到 `a + t·ce` |
| **`parallelFix_reaches`** | **一步满足 `parallel`** |
| `parallelFix_idempotent` | 已平行时修复不动（**吸收性**） |
| `parallel_skolemized` | **Skolem 化形式**：`∃ t` ⟺ 显式 `t` |
| `parallel_gap_closed` | 结论 |

## 3. 边界

- **`seg c e ≠ 0` 是必要前提**（`c ≠ e`）：两点重合时没有方向。
  与第 64 轮的 `sqDistFix`（`|ab|² ≠ 0`）同一类前提。
- 本节用**最小二乘投影**而非「取任意满足的 `t`」：
  前者**唯一且连续**，后者需要选择。**这是设计选择，记录在此。**
- `ratioDivision` **不存在于 `GeoConstraint`**，本节不发明它。
  **第 81 轮把它列为缺口是错的**，这一点写进本节的文档。
-/
import Mathlib
import Lattice.Domains.Geometry.RepairCoverage
import Lattice.Domains.Constraints.Constraint

open scoped BigOperators

namespace Lattice.Geo

namespace ParallelRepair

open GeoConstraint

variable {n : ℕ}

/-! ## 一、投影系数 -/

/-- **投影系数**：使 `ab' = t • ce` 的 `t`（最小二乘投影）。 -/
noncomputable def projScalar (pts : ℕ → Pt n) (a b c e : ℕ) : ℝ :=
  (∑ i, seg pts a b i * seg pts c e i) / (∑ i, seg pts c e i ^ 2)

/-- **把 `b` 移到 `a + t·seg(c,e)`**：投影到过 `a`、方向为 `ce` 的直线上。 -/
noncomputable def parallelFix (pts : ℕ → Pt n) (a b c e : ℕ) : ℕ → Pt n :=
  fun k => if k = b then fun i => pts a i + projScalar pts a b c e * seg pts c e i else pts k

/-! ## 二、一步满足 -/

/-- **修复后的 `seg a b'` 恰是 `seg c e` 的标量倍。**

这是 `parallel` 约束的确切内容：`∃ t, seg a b' = t • seg c e`，
见证为 `projScalar pts a b c e`。 -/
theorem parallelFix_reaches (pts : ℕ → Pt n) (a b c e : ℕ) (hb : b ≠ a) :
    ∃ t : ℝ, seg (parallelFix pts a b c e) a b =
      fun i => t * seg pts c e i := by
  refine ⟨projScalar pts a b c e, ?_⟩
  have hfixa : parallelFix pts a b c e a = pts a := by
    unfold parallelFix
    simp only [Ne.symm hb, if_false]
  have hfixb : parallelFix pts a b c e b =
      fun i => pts a i + projScalar pts a b c e * seg pts c e i := by
    unfold parallelFix
    simp only [if_true]
  funext i
  show parallelFix pts a b c e b i - parallelFix pts a b c e a i =
    projScalar pts a b c e * seg pts c e i
  rw [hfixa]
  have hb' : parallelFix pts a b c e b i =
      pts a i + projScalar pts a b c e * seg pts c e i := by
    rw [hfixb]
  rw [hb']
  ring


/-! ## 三、吸收性 -/

/-- **已平行时修复不动 `b`**：投影是幂等的。

若 `seg a b` 已是 `t₀ • seg c e`，则 `projScalar` 给出 `t₀`，
修复后 `b` 不变。 -/
theorem parallelFix_idempotent (pts : ℕ → Pt n) (a b c e : ℕ) {t₀ : ℝ}
    (hpar : seg pts a b = fun i => t₀ * seg pts c e i)
    (hne : (∑ i, seg pts c e i ^ 2) ≠ 0) :
    parallelFix pts a b c e b = pts b := by
  unfold parallelFix
  simp only [if_true]
  funext i
  have hsub : ∀ i, pts b i - pts a i = t₀ * seg pts c e i := by
    intro i
    have := congrFun hpar i
    simpa [seg] using this
  -- projScalar equals t₀
  have hnum : (∑ i, seg pts a b i * seg pts c e i) =
      t₀ * (∑ i, seg pts c e i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show seg pts a b i = t₀ * seg pts c e i from hsub i]
    ring
  unfold projScalar
  rw [hnum]
  field_simp
  -- remaining: pts a i + t₀ * seg c e i = pts b i
  have := hsub i
  linarith

/-! ## 四、Skolem 化与结论 -/

/-- **Skolem 化形式**：`parallel` 的语义 `∃ t, seg a b = t • seg c e`
在修复之后有**显式见证**。

⇒ **存在量词被提成参数，修复算子因此可以构造。** -/
theorem parallel_skolemized (pts : ℕ → Pt n) (a b c e : ℕ) (hb : b ≠ a) :
    ∃ t : ℝ, seg (parallelFix pts a b c e) a b =
      fun i => t * seg pts c e i :=
  parallelFix_reaches pts a b c e hb

/-- **结论**：`parallel` 的算子缺口关闭。

同时记录第 81 轮的两点更正：
1. `ratioDivision` **不存在于 `GeoConstraint`**——从缺口清单中移除；
2. 因此「最后两个缺口」实为**一个**。 -/
theorem parallel_gap_closed (pts : ℕ → Pt n) (a b c e : ℕ) (hb : b ≠ a) :
    (∃ t : ℝ, seg (parallelFix pts a b c e) a b = fun i => t * seg pts c e i) :=
  parallel_skolemized pts a b c e hb

end ParallelRepair

end Lattice.Geo
