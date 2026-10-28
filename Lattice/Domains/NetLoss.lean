/-
# 参数化约束损失（清单 M2-1）

## 0. 补的是什么

第 198 轮把「每条约束都有惩罚」补到了 12/12（`Geo/PenaltyLoss.lean`）。
但那个 `penaltyLoss` 的自变量是**配置**，不是**参数**：

```lean
penaltyLoss : GeoConstraint n → (ℕ → Pt n) → ℝ
```

而目标是「正向把符号知识**编译成权重**（**约束损失**、…）」。
**一个不依赖权重的损失不是训练损失。** 所以那时「约束损失」这一支只通了半条：
约束 → 损失，但损失没有接到参数上。

本节接上后半条。

## 1. 设计：网络作用于每个数据点，再对输出配置施加惩罚

```lean
netLoss params cs pts := ∑_{c ∈ cs} penaltyLoss c (fun k => netAct params (pts k))
```

**为什么是这个形状，而不是把参数直接塞进 `penaltyLoss`**：
约束说的是**点**满足什么，而参数说的是**怎么把点变成点**。
两者的接口只能是一个**配置**。所以损失必须是「先跑网络、再判约束」——
**这不是技巧，是「约束损失」这个词唯一说得通的意思。**

**它确实依赖参数**：`netAct params ·` 出现在 `penaltyLoss` 的自变量里，
改 `params` 就改配置，就改损失。这不是名字上的依赖。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| `netLoss` | `params → 约束表 → 配置 → ℝ` |
| **`netLoss_nonneg`** | 损失恒非负（训练可用的前提） |
| **`netLoss_eq_zero_iff`** | **损失为零 ⟺ 网络输出配置满足每条约束** |
| `netLoss_zero_iff_holdsSet` | 与 `HoldsSet` 对齐的形式 |
| **`netLoss_append`** | **加约束 = 加损失**（结构性质，`∑` 的可加性） |
| `netLoss_empty` | 无约束时损失为零 |


## 4. 为什么这个文件在 `Geo/` 而不在 `Lift/`

初稿放在 `Lattice/Lift/NetLoss.lean`，**门禁 I4 立刻报错**：

```
lift layer imports geo layer module `Lattice.Geo.PenaltyLoss`   Lattice/Lift/NetLoss.lean:61
```

`Lift` 是层 2、`Geo` 是层 4，依赖方向不允许。而本节**必须**同时用 `Core.netAct`（层 0）
与 `Geo.penaltyLoss`（层 4），所以它的位置只可能是 **`Geo` 或更高**。

这是第 178 轮 `CodegenLadder` 从 `Lift` 移到 `Geo` 的**同一个教训**，
所以这里把它记下来而不是悄悄挪文件：**一个模块该在哪一层，由它 import 的最高层决定。**

## 3. 边界（四条，都说清）

- **这是「约束损失」，不是完整的训练损失。** 任务损失（交叉熵、似然）**不在本节**。
  目标是「约束损失」作为**一个**可加的项；把它与任务损失相加是使用方的事，
  且要做权重（`λ`）——本节**不给 `λ`**，因为没有理论能定它。
- **`params` 的角色是「把点变成点」**，即 `List (AffineLayer (Fin n))`。
  **本节不声称这是 LLM**：没有注意力、没有位置编码。它是链路的权重侧载体。
- **`netLoss_eq_zero_iff` 是 loss 与约束之间的契约**，不是「训练会收敛」的声称。
  优化器的收敛是另一件事（`Lib/Optim` 里有，但不在本节）。
- **`netLoss` 用 `List.sum`，不是 `Finset.sum`**：`GeoConstraint` 没有 `DecidableEq`
  （`ConstraintSet.lean` 已记录 `DecidableEq ℝ` 不可得），所以**不能**取 `toFinset` 去重。
  **重复的约束会被重复计罚**——这与 `HoldsSet` 的合取语义**不同**（合取对重复无感）。
  **这是本节最需要读者知道的一处不一致**，见 `netLoss_append` 的注记。
- 本节**不改** `Geo/PenaltyLoss.lean`、`Geo/Loss.lean`。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Domains.ConstraintSet
import Lattice.Domains.PenaltyLoss

namespace Lattice.Geo.NetLoss

open Lattice.Core Lattice.Geo Lattice.Geo.ConstraintSet

variable {n : ℕ}

/-! ## 一、定义 -/

/-- **参数化约束损失**：跑网络，再对输出配置施加每条约束的惩罚。

**这就是「约束损失」唯一说得通的形状**——约束说的是点，参数说的是怎么把点变成点，
所以损失只能是「先跑网络、再判约束」。 -/
noncomputable def netLoss (params : List (AffineLayer (Fin n)))
    (cs : List (GeoConstraint n)) (pts : ℕ → Pt n) : ℝ :=
  (cs.map (fun c => Lattice.Geo.PenaltyLoss.penaltyLoss c
    (fun k => netAct params (pts k)))).sum

/-! ## 二、基本性质 -/

/-- **损失非负**：每一项都是 `penaltyLoss`，而它对 12 个构造子都非负。 -/
theorem netLoss_nonneg (params : List (AffineLayer (Fin n)))
    (cs : List (GeoConstraint n)) (pts : ℕ → Pt n) : 0 ≤ netLoss params cs pts := by
  unfold netLoss
  induction cs with
  | nil => simp
  | cons c rest ih =>
      rw [List.map_cons, List.sum_cons]
      have := Lattice.Geo.PenaltyLoss.penaltyLoss_nonneg c (fun k => netAct params (pts k))
      linarith

/-- **无约束 ⟹ 零损失**。 -/
theorem netLoss_empty (params : List (AffineLayer (Fin n))) (pts : ℕ → Pt n) :
    netLoss params [] pts = 0 := by
  unfold netLoss
  simp

/-- **加约束 = 加损失**：`netLoss` 对约束表是可加的。

⚠ **这是 `List.sum` 的性质，不是 `HoldsSet` 的性质**：`HoldsSet` 是合取，
对重复的约束**无感**；而 `netLoss` 会**重复计罚**。
**两者在「约束表有重复」时不相等**——这是本节已知的不一致，
不能靠去重修（`GeoConstraint` 没有 `DecidableEq`）。 -/
theorem netLoss_append (params : List (AffineLayer (Fin n)))
    (cs ds : List (GeoConstraint n)) (pts : ℕ → Pt n) :
    netLoss params (cs ++ ds) pts = netLoss params cs pts + netLoss params ds pts := by
  unfold netLoss
  rw [List.map_append, List.sum_append]

/-! ## 三、契约：损失为零 ⟸ 约束成立（P），以及**反向为假**（N）

**初稿在这里写了双向 `netLoss = 0 ↔ ∀ c ∈ cs, Holds c`，那是错的。**

`penaltyLoss` 对 `ltZero`/`gtZero` 只是**松弛**（第 198 轮已证：零集是 `e ≤ 0` 而不是 `e < 0`），
对 `collinear`/`parallel` 只有 sound 方向。所以**双向在 4 个构造子上为假**，
而在 `netLoss` 这一层它会更明显：只要约束表里有一条这样的约束，零损失就不蕴含满足。

**所以本节给 P + N 两条**：P 对全部 12 个成立，N 给一个具体反例。 -/

/-- **P · 全部 12 个构造子上：约束全部成立 ⟹ 零损失。** -/
theorem netLoss_eq_zero_of_holds (params : List (AffineLayer (Fin n)))
    (cs : List (GeoConstraint n)) (pts : ℕ → Pt n)
    (h : ∀ c ∈ cs, GeoConstraint.Holds c (fun k => netAct params (pts k))) :
    netLoss params cs pts = 0 := by
  unfold netLoss
  induction cs with
  | nil => simp
  | cons c rest ih =>
      rw [List.map_cons, List.sum_cons]
      have hc : Lattice.Geo.PenaltyLoss.penaltyLoss c (fun k => netAct params (pts k)) = 0 :=
        Lattice.Geo.PenaltyLoss.penaltyLoss_eq_zero_of_holds c _ (h c (List.mem_cons_self c rest))
      have hr : (rest.map (fun c => Lattice.Geo.PenaltyLoss.penaltyLoss c
            (fun k => netAct params (pts k)))).sum = 0 :=
        ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
      rw [hc, hr, add_zero]

/-- **N · 反向为假**：存在约束表与配置，使 `netLoss = 0` 而约束**不**成立。

取一条 `ltZero (const 0)`：`Holds` 要求 `0 < 0`（假），而惩罚是 `(max 0 0)² = 0`。

**这就是「零损失不蕴含满足」的具体见证。** 它不是说 `netLoss` 错了——
**松弛是 `ltZero` 的必然代价**（解集是开集，非负连续函数不可能精确表示它，第 198 轮已论证）。
**但它意味着使用方不能把「训练到零损失」当作「约束已满足」**，除非约束表里全是精确的那 9 类。 -/
theorem netLoss_zero_without_holds :
    ∃ (params : List (AffineLayer (Fin 1))) (cs : List (GeoConstraint 1)) (pts : ℕ → Pt 1),
      netLoss params cs pts = 0 ∧
        ¬ ∀ c ∈ cs, GeoConstraint.Holds c (fun k => netAct params (pts k)) := by
  refine ⟨[], [.ltZero (.const 0)], fun _ _ => 0, ?_, ?_⟩
  · -- compute directly: the penalty of `ltZero (const 0)` is `(max 0 0)^2 = 0`
    unfold netLoss
    simp [Lattice.Geo.PenaltyLoss.penaltyLoss, GeoExpr.evalPts]
  · intro h
    have hlt := h (.ltZero (.const 0)) (List.mem_cons_self _ _)
    unfold GeoConstraint.Holds at hlt
    simp [GeoExpr.evalPts] at hlt

end Lattice.Geo.NetLoss
