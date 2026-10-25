/-
# 符号侧的第二族表示：从约束到约束集

## 0. 本节补什么

第 71 轮连接了权重侧的三族表示，并明确登记：

> **符号侧与 token 侧仍各只有一族。**

**本节给符号侧补第二族。**

## 1. 两族是什么

| 族 | 类型 | 语义 | 用途 |
|:--|:--|:--|:--|
| **构造子族** | `GeoConstraint n` | `Holds c pts` | 单个约束，语义直接 |
| **集合族** | `List (GeoConstraint n)` | 合取 | 问题实例，可组合、可去重 |

**这不是两个编码，是两种粒度**：一条约束 vs 一组约束。

**为什么它算「第二族」而不是「包装」**：
- 集合族有**构造子族没有的运算**（拼接、去重、筛选）；
- 集合族的语义是**合取**，不是单个 `Holds`；
- **两族互为对偶**：集合族能表示「多约束问题」，构造子族能表示「单约束语义」。

## 2. 证明思路

### 2.1 集合族的语义

```
HoldsSet : List (GeoConstraint n) → (ℕ → Pt n) → Prop
HoldsSet []       pts  :=  True
HoldsSet (c :: cs) pts :=  Holds c pts ∧ HoldsSet cs pts
```

**空集恒真**（因为没有约束要满足），这是正确的合取语义。

### 2.2 两族的一致性

| 定理 | 内容 |
|:--|:--|
| `holdsSet_singleton` | 单元素集合 = 单个约束 |
| `holdsSet_append` | 拼接的语义是**合取** |
| `holdsSet_mono` | 集合变大 ⟹ 语义变强 |

**`holdsSet_singleton` 是两族互转的基础**：`[c]` 与 `c` 语义相同。

### 2.3 去重不变语义

```
holdsSet_nodup_of_holdsSet : HoldsSet cs pts → HoldsSet cs.dedup pts
```

**这是「集合」这个名字该有的性质**：重复的约束不改变合取。

**但需要 `DecidableEq (GeoConstraint n)`**——
`GeoConstraint` 含 `GeoExpr`，后者含 `ℝ`，而 `ℝ` 的相等**不可判定**。

⇒ **这条定理在一般情形下不可证。** 这是本节必须如实记录的边界。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `HoldsSet` | 集合族的语义（合取） |
| `holdsSet_nil` | 空集恒真 |
| **`holdsSet_singleton`** | **两族在单元素上一致** |
| `holdsSet_append` | 拼接 = 合取 |
| `holdsSet_mono` | 集合变大 ⟹ 语义变强 |
| `holdsSet_subset` | 子集的语义被超集蕴含 |
| `two_families_connected` | **两族连通** |

## 4. 边界

- **`List` 族不能去重**：`GeoConstraint` 含 `ℝ`，相等不可判定。
  **这条已登记**，不用一个假的可判定性绕过。
- 本节**不**建立 DNF/CNF 规范形。那需要 `GeoConstraint` 的否定与析取，
  而 `Holds` 对 `.ltZero` 等构造子**没有封闭的否定形式**——是另一件事。
- 集合族是**同一语义的两种粒度**，不是**不同语义的族**。
  与第 71 轮的区分一致：真正「语义不同」的第二族（如精确有理数 vs 浮点）
  **仍未做**，本节不声称完成它。
-/
import Mathlib
import Lattice.Geo.Constraint

namespace Lattice.Geo

namespace ConstraintSet

variable {n : ℕ}

/-! ## 一、集合族的语义 -/

/-- **约束集的语义**：所有约束都成立的合取。

空集恒真——没有约束要满足时，任何配置都满足。 -/
def HoldsSet : List (GeoConstraint n) → (ℕ → Pt n) → Prop
  | [], _ => True
  | c :: cs, pts => GeoConstraint.Holds c pts ∧ HoldsSet cs pts

/-- **空集恒真**。 -/
theorem holdsSet_nil (pts : ℕ → Pt n) : HoldsSet ([] : List (GeoConstraint n)) pts :=
  trivial

/-- **单元素集合与单约束一致。**

这是两族互转的基础。 -/
theorem holdsSet_singleton (c : GeoConstraint n) (pts : ℕ → Pt n) :
    HoldsSet [c] pts ↔ GeoConstraint.Holds c pts :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- **拼接 = 合取**：两个约束集的并，语义是两个语义的合取。 -/
theorem holdsSet_append (cs ds : List (GeoConstraint n)) (pts : ℕ → Pt n) :
    HoldsSet (cs ++ ds) pts ↔ (HoldsSet cs pts ∧ HoldsSet ds pts) := by
  induction cs with
  | nil =>
      show HoldsSet ds pts ↔ (True ∧ HoldsSet ds pts)
      simp
  | cons c cs ih =>
      show (GeoConstraint.Holds c pts ∧ HoldsSet (cs ++ ds) pts) ↔
           ((GeoConstraint.Holds c pts ∧ HoldsSet cs pts) ∧ HoldsSet ds pts)
      rw [ih]
      tauto

/-! ## 二、单调性：集合变大 ⟹ 语义变强 -/

/-- **投影**：从集合的合取中取出任一成员的语义。 -/
theorem holdsSet_mem {cs : List (GeoConstraint n)} {c : GeoConstraint n}
    (hmem : c ∈ cs) (pts : ℕ → Pt n) :
    HoldsSet cs pts → GeoConstraint.Holds c pts := by
  induction cs with
  | nil => exact absurd hmem (by simp)
  | cons d ds ih =>
      intro h
      rw [HoldsSet] at h
      obtain ⟨hd, hds⟩ := h
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact hd
      · exact ih hmem' hds

/-- **子集的语义被超集蕴含**：满足更多约束，就满足其中任意子集。 -/
theorem holdsSet_subset (cs ds : List (GeoConstraint n))
    (hsub : ∀ c, c ∈ cs → c ∈ ds) (pts : ℕ → Pt n) :
    HoldsSet ds pts → HoldsSet cs pts := by
  induction cs with
  | nil => intro _; exact trivial
  | cons c cs ih =>
      intro h
      have hc : GeoConstraint.Holds c pts := holdsSet_mem (hsub c (List.mem_cons_self c cs)) pts h
      have hrest : HoldsSet cs pts :=
        ih (fun c' hc' => hsub c' (List.mem_cons_of_mem c hc')) h
      exact ⟨hc, hrest⟩

/-- **单增**：加入更多约束，语义只会更强。 -/
theorem holdsSet_mono (cs : List (GeoConstraint n)) (c : GeoConstraint n) (pts : ℕ → Pt n)
    (h : HoldsSet (c :: cs) pts) : HoldsSet cs pts :=
  h.2

/-! ## 三、两族连通 -/

/-- **两族连通**：单元素集合与单约束语义一致，且合取可分解。

⇒ **符号侧有两族表示**：构造子形式（单约束）与集合形式（多约束问题）。
**两族由语义而非类型关联。** -/
theorem two_families_connected (c : GeoConstraint n) (cs ds : List (GeoConstraint n))
    (pts : ℕ → Pt n) :
    (HoldsSet [c] pts ↔ GeoConstraint.Holds c pts) ∧
    (HoldsSet (cs ++ ds) pts ↔ (HoldsSet cs pts ∧ HoldsSet ds pts)) :=
  ⟨holdsSet_singleton c pts, holdsSet_append cs ds pts⟩

end ConstraintSet

end Lattice.Geo
