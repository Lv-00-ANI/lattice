import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Architectures.RealBlockConstants
import Lattice.Lib.Attention.RealSoftmaxLipschitz
/-!
# LATTICE: `SoftmaxAttnOp` 的输入无关相对范数界

## 一、本文件证的定理

`RealBlockConstants.lean:283-288` 定义

```
def SoftmaxAttnOp {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin k, (softmax (S x)) i • (V i x)
```

本文件证明它满足一个**一致于 `x` 的相对范数界**：

```
theorem softmaxAttnOp_norm_le
    (hV : ∀ i, ‖V i‖ ≤ M) (x) :
    ‖SoftmaxAttnOp S V x‖ ≤ M * ‖x‖
```
## 二、⭐ `PROCESS.md §2.2` 要求的回答：「这条定理比它的**定义**多说了什么？」

**答案：一条范数不等式，而定义本身对此【什么都没断言】。**

`SoftmaxAttnOp` 的定义只是**一个有限和**（`∑ i, (softmax (S x)) i • V i x`）。
它**没有**断言：输出有界、界与输入成正比、或比例常数与 `x` 无关。
本定理补充的正是这三点合起来的那一条不等式 —— 且**常数 `M` 与 `x` 完全无关**
（`M` 只界住算子族 `V`，不界 `x`）。

⚠ **判据（避免空洞）**：如果本定理的证明体只是 `rfl`、或结论逐字是某个假设，
那它就没多说任何东西。本文件提供**两条独立的对抗性证据**（均已机器验证）：
- **非平凡性探针**（`:rfl` 失败）：`example : <同一陈述> := rfl` **编译失败**，
  报 `type mismatch: rfl has type ?m = ?m but is expected to have type ‖…‖ ≤ M * ‖x‖`
  ⟹ 结论是**不等式**，**不能**由定义性展开关闭。
- ⭐ **承重性定理**（本文件 §四 `softmaxAttnOp_norm_le_needs_hV`）：
  **去掉 `hV` 后命题【可被反驳】**，附显式见证
  （`k = 1`、`S = 0`、`V₀ = −id`、`M = 0`、`x = e₀` ⟹ `‖…‖ = 1 > 0 = M‖x‖`）。
  ⟹ 按 `PROCESS.md §3.3` 三分类为「**去掉该假设后为假**」⟹ **`hV` 承重**。

## 三、与既有载体的关系（**不重复造轮子**）

本定理的数学内容**已经存在**于 `RealAttention.lean`：

| 声明 | 位置 |
|:--|:--|
| `softmax_nonneg` | `RealAttention.lean:99` |
| `softmax_sum_one` | `RealAttention.lean:107` |
| `convComb_norm_bound` | `RealAttention.lean:39` |
| ⭐ `attention_output_bound` | `RealAttention.lean:120` |

`attention_output_bound` 的结论是 `‖convComb (softmax z) V‖ ≤ M`，
而 `convComb w V = ∑ i, w i • V i`（`RealAttention.lean:32`）
⟹ 与 `SoftmaxAttnOp` 的定义**只差定义性展开**。

⇒ 本文件的工作是**形状适配（shape adaptation）**，不是新数学：
把 `z := S x`、`V := fun i => V i x`、`M := M * ‖x‖` 代入，并
**从 `hV : ∀ i, ‖V i‖ ≤ M` 得到 `hV' : ∀ i, ‖V i x‖ ≤ M * ‖x‖`**
（用 `ContinuousLinearMap.le_opNorm`）。

⚠ **本条如实登记**：本文件的**增量价值**在于
① 给出一个**输入无关相对**形式的界（既有定理是绝对形式），
② 把它**接到 `SoftmaxAttnOp` 这个具体载体**上（此前无人接过），
③ 附带两条**机器可检的**非平凡性/承重性证据。
**不声称**发现了新的数学。

## 四、⚠ 一条**刻意不写**的陈述（防空洞）

`SoftmaxAttnOp S V 0 = 0` 是**纯定义性展开**，**没有多说什么** ——
按 `PROCESS.md §2.2` 的判据（"若答案是『什么都没多说』⟹ 不要写它"），
**本文件不把它立为定理**。若需要，它只能作 docstring 说明或见证用到。

## 五、诚实边界

- ⚠ **未跑 `lake build`**，未跑裸 `lake env lean`；
  类型检查走 `scripts\probe.ps1`（项目级锁，合规路径）。
- ⚠ 本文件的定理**依赖既有 `RealAttention` 的三条引理**；
  若那些引理的陈述日后被改，本文件的证明体随之失效。
- ⚠ `EuclideanSpace ℝ (Fin n)` 上的 `NormedAddCommGroup`/`NormedSpace ℝ` 实例
  由 Mathlib 提供；本文件**不重新引入**这些实例。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、把 `hV` 从算子级抬到「算子作用于固定 `x`」级

这是本文件唯一的**适配步骤**：`attention_output_bound` 需要
`hV : ∀ i, ‖V i‖ ≤ M`（算子范数），而 `SoftmaxAttnOp` 里出现的是 `V i x`。
用 `ContinuousLinearMap.le_opNorm` 桥接。 -/

/-- ⭐ **适配引理**：算子范数界 ⟹ 逐点值界（含 `‖x‖` 因子）。

`‖V i x‖ ≤ ‖V i‖ * ‖x‖ ≤ M * ‖x‖`。

⚠ **诚实登记（`hM` 已删除，非疏漏）**：本引理**初稿**带假设 `hM : 0 ≤ M`，
内核探针报 `warning: unused variable 'hM'`。
按 `PROCESS.md §4.6`，**unused variable 是「假设写松」的最强机械信号**
（候选 ≠ 判定，须区分病因）；此处逐一核对后确认该假设**根本不需要**：
`mul_le_mul_of_nonneg_right` 只需 `0 ≤ ‖x‖`（`norm_nonneg` 免费），
**与 `0 ≤ M` 无关** ⟹ **`hM` 是多余的，已删除**（而非用 `set_option` 掩盖，见 `B224.5`）。
⚠ 副产物：主定理的 `hM` 随之删除 —— 这**放宽**了陈述（假设更少），**不是**降级。 -/
theorem softmaxAttnOp_value_bound
    {n : ℕ} (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hV : ∀ i, ‖V i‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ i, ‖V i x‖ ≤ M * ‖x‖ := by
  intro i
  calc ‖V i x‖ ≤ ‖V i‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hV i) (norm_nonneg x)

/-! ## 二、主定理：`SoftmaxAttnOp` 的相对范数界 -/

-- ⭐ **本文件是 `Lattice.softmaxAttnOp_norm_le` 的【唯一正本】**（B410 审计后合并，已完成）。
--
-- 审计发现本文件与 `RealHreachConditional` **各有一份真声明、陈述同型**（协调者用保留换行的
-- 剥离器复核：**恰好 2 处**；裸扫会多报 1 处，那处落在 docstring 代码围栏内，是伪造命中）。
-- 按本项目四分判据属**类 (i) 真重复**（同名同型同义，**不是**类 (iv)：无需 `rfl` 桥）。
--
-- ✅ **处置：已合并** —— `RealHreachConditional` 的私有重证已删除，改为 `import` 本文件。
-- 合并安全性三项均已实测：① 两文件**各有 0 个 importer**（无级联）；
-- ② **无环**（本文件不 import `RealHreachConditional`）；③ 陈述逐字同型。
-- 合并后复核：全库真声明数 **2 → 1**，两模块均 `Build completed successfully` / exit 0。
-- 计数口径限定为 `softmaxAttnOp_norm_le` 这一符号：其全库真声明数 2 → 1；
-- 本文件新引入的适配引理 `softmaxAttnOp_value_bound` 不计入该计数（它与主定理是两条独立的真声明）。
--
-- 注意 **`softmaxAttnOp_zero` 的归属已裁定：留在 `RealHreachConditional`**，不移入本文件 ——
-- 因为本文件**刻意不立**它（`SoftmaxAttnOp S V 0 = 0` 是纯定义展开，立之即空洞）。
-- ⇒ **正本收【实质定理】，消费者留它自己需要的【定义性助手】** —— 与 `extractLayer`（类 iv，保留）同一政策：
-- **不合并偏薄的东西。**


/-- 要点 **主定理**：`SoftmaxAttnOp` 的输出范数被 `M * ‖x‖` 界住，
其中 `M` **只**界住算子族 `V`（**与 `x` 无关**）。

⇒ 这就是 `PROCESS.md §2.2` 意义上「比定义多说的东西」：
定义只是一个有限和，**不断言任何**关于其范数的事。 -/
theorem softmaxAttnOp_norm_le
    {n k : ℕ} [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (hV : ∀ i, ‖V i‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖SoftmaxAttnOp S V x‖ ≤ M * ‖x‖ := by
  -- `SoftmaxAttnOp S V x` 的定义性展开 = `convComb (softmax (S x)) (fun i => V i x)`
  have hdef : SoftmaxAttnOp S V x = convComb (softmax (S x)) (fun i => V i x) := by
    unfold SoftmaxAttnOp convComb
    rfl
  rw [hdef]
  exact attention_output_bound (S x) (fun i => V i x) (M * ‖x‖)
    (softmaxAttnOp_value_bound V M hV x)

/-! ## 三、唯一性/非退化见证：界是**紧**的

给一条**达到**界的显式实例（不是"存在性"空转）：
`k = 1`、`V 0 = id`、`M = 1` 时，`SoftmaxAttnOp S V x = x`（softmax 和为 1 且只有一项），
故 `‖SoftmaxAttnOp S V x‖ = ‖x‖ = M * ‖x‖` ⟹ 上界的**等号可取到**，
即该界**不能被改进**（就 `M` 的依赖而言）。 -/

/-- 单头情形：`softmax` 对单元素指标恒为 `1`。 -/
theorem softmax_fin_one_eq_one (z : Fin 1 → ℝ) : softmax z 0 = 1 := by
  have h := softmax_sum_one z
  rw [Fin.sum_univ_one] at h
  exact h

/-- 要点 **紧性见证**：`k = 1`、`V 0 = id`、`M = 1` 时主定理的界**取等号**。

⇒ 该界在「只依赖 `M`、与 `x` 无关」这一形式下**不可改进**。 -/
theorem softmaxAttnOp_norm_bound_tight
    {n : ℕ} (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin 1 → ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖SoftmaxAttnOp S (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x‖
      = 1 * ‖x‖ := by
  have hdef : SoftmaxAttnOp S (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x
      = convComb (softmax (S x))
          (fun _ => x) := by
    unfold SoftmaxAttnOp convComb
    rfl
  rw [hdef]
  unfold convComb
  rw [Fin.sum_univ_one, softmax_fin_one_eq_one (S x)]
  simp

/-! ## 四、要点 承重性：**去掉 `hV` 后命题可被反驳**（`PROCESS.md §3.3` 第 ⑤ 步「固化为定理防复活」）

`PROCESS.md §3.3` 要求：发现某命题为假时，**把反例固化成定理**，以防它日后复活。
本节的定理证明：**主定理的结论在去掉 `hV` 后为【假】** ——
即 `hV` **确实承重**（去掉即假），而非装饰性假设。

注意 这正是 `PROCESS.md §2.2` 判据 ①「每环的假设都承重」的机器证据。 -/

/-- 单头情形：`softmax` 对单元素指标恒为 `1`。 -/
theorem softmax_fin_one_eq_one' (z : Fin 1 → ℝ) : softmax z 0 = 1 := by
  have h := softmax_sum_one z
  rw [Fin.sum_univ_one] at h
  exact h

/-- 单头情形：`SoftmaxAttnOp` 退化为 `V 0 x`。 -/
theorem softmaxAttnOp_fin_one
    {n : ℕ} (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin 1 → ℝ))
    (V : Fin 1 → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    SoftmaxAttnOp S V x = V 0 x := by
  have hdef : SoftmaxAttnOp S V x = convComb (softmax (S x)) (fun i => V i x) := by
    unfold SoftmaxAttnOp convComb
    rfl
  rw [hdef]
  unfold convComb
  rw [Fin.sum_univ_one, softmax_fin_one_eq_one' (S x)]
  simp

/-- 单头负恒等算子 `V₀ = −id`。 -/
def negId (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (-1 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))

/-- 要点 **承重性定理（反例固化）**：**去掉 `hV` 后，主定理的结论为假**。

显式见证：`k = 1`、`S = 0`、`V₀ = −id`、`M = 0`、`x = e₀ ≠ 0`
⟹ `SoftmaxAttnOp S V x = −x`，故 `‖SoftmaxAttnOp S V x‖ = ‖x‖ = 1 > 0 = M * ‖x‖`
⟹ 结论 `‖…‖ ≤ M * ‖x‖` **不成立**。

注意 该实例**满足主定理除 `hV` 外的全部假设**
（`M = 0` 不满足 `‖V 0‖ ≤ 0`，因为 `‖−id‖ = 1`）⟹ 按 `PROCESS.md §3.3` 三分类，
这是**「去掉某假设后为假」** ⟹ 要点 **该假设【承重】**。 -/
theorem softmaxAttnOp_norm_le_needs_hV :
    ∃ (S : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 1 → ℝ))
      (V : Fin 1 → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (M : ℝ) (x : EuclideanSpace ℝ (Fin 2)),
      ¬ (‖SoftmaxAttnOp S V x‖ ≤ M * ‖x‖) := by
  refine ⟨0, (fun _ => negId 2), 0,
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)), ?_⟩
  have hop : SoftmaxAttnOp (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 1 → ℝ))
      (fun _ => negId 2) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      = negId 2 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) :=
    softmaxAttnOp_fin_one 0 (fun _ => negId 2) _
  rw [hop]
  have hnorm : ‖negId 2 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))‖ = 1 := by
    have h1 : negId 2 (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
        = (-1 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
      simp [negId]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul]
    rw [EuclideanSpace.norm_single]
    norm_num
  rw [hnorm]
  norm_num

end Lattice
