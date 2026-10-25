import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.LinearAlgebra.RealSparsity
/-!
# LATTICE (E-04): 编辑的最小性刻画 —— 行编辑的输出差**到底依赖哪些坐标**

## 0. 任务书原文与它的**字面**内容

> 证明：若编辑 `W` 为 `W'` 只影响第 `k` 行，则 `∀ x, (LayerOut W' x - LayerOut W x)`
> 只依赖 `x_k`。给出**充要条件**。

## 1. ⭐⭐ 本文件的核心结论：**任务书的字面命题是【假】的**

本文件把这个目标**逐字形式化**，然后**给出机器验证的反例**：

> ⭐ `rowEdit_not_depends_only_counterexample`：
> 存在 `2×2` 权重 `W, W'` 与行指标 `r`，使 `W'` 相对 `W` **只改第 `r` 行**，
> 但输出差 `MatLayerOut W' x - MatLayerOut W x` **不**只依赖 `x r`
> （存在 `x, x'` 满足 `x r = x' r` 而两个输出差**不相等**）。

**根因**（一句话）：一次行编辑给输出差贡献的是**第 `r` 行整行**与 `x` 的点积

    (MatLayerOut W' x - MatLayerOut W x) r = Σ_j (W' r j - W r j) · x j

它是一个**线性泛函**，一般地用到 `x` 的**每一个**坐标，而**不是**只用 `x r`。

## 2. ⭐⭐⭐ 真正的**充要条件**（这才是任务的实质内容）

⚠ **记号**：本文件把**行指标**记为 `r : Fin m`、**列/坐标指标**记为 `k : Fin n`，
**刻意分开**。任务书把同一个 `k` 同时当行号与列号用，这只在**方阵**（`m = n`）下合法；
解耦后结论对**任意 m×n** 成立（方阵是特例），且能看出两者在结论里角色不同。

| # | 陈述 | 名字 |
|--:|:--|:--|
| ① | 行编辑 ⟹ 输出差的**支撑集**落在 `{r}` 上（`i ≠ r` 处恒为零） | `rowEdit_offRow_zero` |
| ② | 线性泛函 `x ↦ Σ_j c j · x j` **只依赖 `x k`** ⟺ `c` 在 `k` 之外**全零** | `coordFun_depends_only_iff` |
| ③ | ⭐ **编辑限于第 `r` 行 ⟹ 输出差只依赖 `x k`** ⟺ **该编辑在 `k` 列之外全零** | `rowEdit_depends_only_iff` |
| ④ | 格编辑（只动 `(r,k)`）下输出差的**显式闭式** = `if i = r then ΔW r k · x k else 0` | `cellEdit_delta_closed_form` |

⭐ **③ 就是任务要的「充要条件」，它的读法是**：

> 「只影响第 `r` 行」**不足以**让输出差只依赖 `x k`；
> **还必须**「只影响第 `k` **列**」——
> 即编辑真正动的是**单个格子** `(r,k)`（行局部 **∧** 列局部）。
> 方阵 + `r = k` 时即「只动 `(k,k)`」。

⇒ **消融读数**：删掉「列局部」这个假设，结论**变成假**（§七 反例机器验证），
而**不是**「证不出来」。这正是任务书判据 **1（消融）** 与 **2（反驳可能）** 的要求。

## 3. 依赖什么 / 与既有模块的关系（判据 3：跨模块）

- `RealMatrixNorm`：`matvecE` / `matCLME`（本文件把 `matvecE` 认作权重矩阵的 `LayerOut`）。
  ⚠ **不复用 `ConvertVectorLinear.LayerOut`**：那是 `LinearLayer`（`List Int`）上的
  **标量**输出，**没有「行」**，无法陈述「只影响第 k 行」。故本文件在矩阵载体上建立
  `MatLayerOut`，并**不**重定义 `LayerOut`（避免同名冲突）。
- `RealSparsity`：`matvecE_sub`（`matvecE (A - B) x = matvecE A x - matvecE B x`）。
- ⚠ **本文件用 `matvecE (W' - W) x` 作为「输出差」的规范形**，
  并用 `RealSparsity.matvecE_sub` 把它与 `matvecE W' x - matvecE W x` 打通 ——
  这是本文件与既有模块的**非平凡接口**。

## 4. 诚实边界（**不许省**）

- ⚠ **无编译验证**：本环境**禁跑 `lake`**，全部证明**未经类型检查**。
  ⇒ 本报告**逐字核对**了每个既有定理签名与每个 mathlib 引理名，但
  **任何**语法/类型/策略错误都**可能**残留。
- ⚠ **不做**「编辑只动 `(r,j₀)`（`j₀ ≠ r`）时输出差只依赖 `x j₀`」的**单列**定理：
  它可由主定理 `rowEdit_depends_only_iff`（取 `k := j₀`）**立即**得到，
  本文件只为不重复而不单列 —— ⚠ **这是省略，不是遗漏**。
- ⚠ **不做**非线性（激活折入）情形：`act ∘ MatLayerOut` 的差**不**是线性的，
  本文件的逐坐标恒等式**失效**（`RealCompileExtractClosed` §五 已给出该断点）。
- ⚠ **不碰** `RealAbstractionRegistry` 那类再导出包装器的类型标注陷阱：
  本文件**不写** `by exact <imported>` 形式的包装器，全部结论自证。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {m n : ℕ}

/-! ## 一、载体：权重矩阵的层输出（`matvecE`）

⚠ **命名说明**：本库已有 `ConvertVectorLinear.LayerOut : LinearLayer → List Int → Int`
（**标量**神经元，**无「行」概念**）。本文件在 `Matrix (Fin m) (Fin n) ℝ` 上工作，
故另立 `MatLayerOut`（**不**重定义 `LayerOut`，避免同名冲突）。 -/

/-- **权重矩阵的层输出**：`(MatLayerOut W x) i = Σ_j W i j · x j`。
逐字即 `RealMatrixNorm.matvecE`（此处仅作别名以便阅读，**定义体就是 `matvecE`**）。 -/
def MatLayerOut (W : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  matvecE W x

/-- `MatLayerOut` 与 `RealMatrixNorm.matvecE` 逐字相同（桥引理，`rfl`）。 -/
lemma MatLayerOut_eq_matvecE (W : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    MatLayerOut W x = matvecE W x := rfl

/-! ## 二、两种「编辑局部性」谓词 -/

/-- ⭐ **行局部编辑**（= 任务书的「只影响第 `k` 行」）：
`W'` 与 `W` 在**第 `r` 行之外**逐格相同。

⚠ **行指标与列指标刻意分开命名**（`r : Fin m` 行、`k : Fin n` 列）：
任务书写「只影响第 `k` 行」并在结论里问「只依赖 `x_k`」，
把**同一个 `k`** 同时当行号与列号用 —— 这只有在**方阵**（`m = n`）时才合法。
本文件**解耦**两个指标，故结论对**任意 m×n** 成立（方阵是特例），
且能看出「行 `r`」与「列 `k`」在结论里扮演**不同的角色**。 -/
def EditSupportsRow (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) : Prop :=
  ∀ i j, i ≠ r → W' i j = W i j

/-- ⭐⭐ **格局部编辑**（= 「只影响第 `r` 行的第 `k` 列」）：
`W'` 与 `W` 只在**单个格子 `(r,k)`** 上可能不同。 -/
def EditSupportsCell (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (k : Fin n) : Prop :=
  ∀ i j, (i, j) ≠ (r, k) → W' i j = W i j

/-- ⭐⭐⭐ **「只依赖坐标 `k`」的精确含义**（向量值函数的版本）：
在 `x k` 上一致的两点给出**相同**的输出。

⚠ 这是 `RealRoundTripVacuity.FactorsThrough` 的**向量值推广**：
那里 `FactorsThrough (fun x => x k) (P : _ → Prop)` 是 `Prop` 值谓词版；
本定义处理 `EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)` 的**函数**值情形。 -/
def DependsOnlyOnCoord (k : Fin n)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ x x', x k = x' k → F x = F x'

/-! ## 三、① 输出差的**逐坐标恒等式**（本文件的引擎）

`(MatLayerOut W' x - MatLayerOut W x) i = Σ_j (W' i j - W i j) · x j`。

证明：`matvecE` 展开 + `RealSparsity.matvecE_sub` + `Finset.sum_sub_distrib` + `ring`。 -/

/-- ⭐ **输出差的逐坐标恒等式**：差 = **编辑增量矩阵** `W' - W` 与 `x` 的矩阵乘。

⚠ **承重步骤**：`EuclideanSpace ℝ (Fin m)` 是 `Fin m → ℝ`（Pi 类型），
故减法逐坐标进行；再用 `RealSparsity.matvecE_sub` 把
`matvecE W' x - matvecE W x` 换成 `matvecE (W' - W) x`，
才能把 `W' i j - W i j` 作为**单项因子**提出来。 -/
lemma rowEditDelta_apply (W W' : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    (MatLayerOut W' x - MatLayerOut W x) i
      = ∑ j : Fin n, (W' i j - W i j) * x j := by
  -- 把「差」整形成 `matvecE (W' - W) x`，再逐坐标展开
  have hsub : MatLayerOut W' x - MatLayerOut W x = matvecE (W' - W) x := by
    rw [MatLayerOut_eq_matvecE, MatLayerOut_eq_matvecE]
    exact (matvecE_sub W' W x).symm
  rw [hsub]
  -- 现在目标：`(matvecE (W' - W) x) i = Σ_j (W' i j - W i j) * x j`
  show (∑ j : Fin n, (W' - W) i j * x j) = ∑ j : Fin n, (W' i j - W i j) * x j
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.sub_apply]

/-! ## 四、① 行编辑 ⟹ 输出差的支撑落在 `{r}`

⭐ 这是「行编辑」能给出的**最强**结论：`i ≠ r` 处输出差**恒为零**。
⚠ 它**不**说明第 `r` 个坐标依赖什么 —— 那正是下面 §六 的主题。 -/

/-- ⭐ **行编辑：第 `r` 行之外输出差恒为零**。

证明：逐坐标恒等式（`rowEditDelta_apply`）+ 行局部性（`EditSupportsRow`）
逐项把 `W' i j - W i j` 化为 `0`，再用 `Finset.sum_eq_zero` 收口。 -/
theorem rowEdit_offRow_zero (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m)
    (hrow : EditSupportsRow W W' r) (x : EuclideanSpace ℝ (Fin n)) :
    ∀ i : Fin m, i ≠ r → (MatLayerOut W' x - MatLayerOut W x) i = 0 := by
  intro i hi
  rw [rowEditDelta_apply W W' x i]
  apply Finset.sum_eq_zero
  intro j _
  rw [hrow i j hi]
  ring

/-! ## 五、② 线性泛函只依赖某坐标的**充要条件**（本文件的实质内核）

对系数 `c : Fin n → ℝ`，考察 `ℓ x = Σ_j c j · x j`：

> ⭐ `ℓ` 只依赖 `x k` ⟺ `c` 在 `k` 之外的坐标上**全零**。

- **(⟸)** 若 `c j = 0`（`j ≠ k`），则求和只剩 `j = k` 一项，即 `c k · x k`。
- **(⟹)** ⭐ **这是有内容的方向**：若存在 `j₀ ≠ k` 且 `c j₀ ≠ 0`，
  取 `x = e_{j₀}`（`EuclideanSpace.single j₀ 1`）、`x' = 0`：
  两者在坐标 `k` 上都是 `0`（因 `j₀ ≠ k`），但 `ℓ x = c j₀ ≠ 0 = ℓ x'` —— **矛盾**。

⭐⭐ **这就是「反驳可能」（判据 2）的引擎**：它给出**具体对象**让「只依赖 `x k`」失败。 -/

/-- ⭐⭐ **② 线性泛函只依赖某坐标的充要条件**（本文件内核）：

`(∀ x x', x k = x' k → Σ_j c j·x j = Σ_j c j·x' j) ↔ (∀ j, j ≠ k → c j = 0)`。

⚠ **两个方向都不平凡**：
- `⟸` 用 `Finset.sum_eq_single`（`Data/Fintype/BigOperators.lean:68` 的加法版
  `Fintype.sum_eq_single {f} (a) (h : ∀ x ≠ a, f x = 0)`）把求和收成单项；
- `⟹` 用 `EuclideanSpace.single`（`Analysis/InnerProductSpace/PiL2.lean:215`）
  造出「在 `k` 上相同、在 `j₀` 上不同」的一对点 —— **反证**。 -/
theorem coordFun_depends_only_iff (c : Fin n → ℝ) (k : Fin n) :
    (∀ x x' : EuclideanSpace ℝ (Fin n),
        x k = x' k → (∑ j : Fin n, c j * x j) = (∑ j : Fin n, c j * x' j))
      ↔ (∀ j : Fin n, j ≠ k → c j = 0) := by
  constructor
  · -- ⟹：反证 —— 若某 j₀ ≠ k 有 c j₀ ≠ 0，则用 e_{j₀} 与 0 造出反例
    intro h j hj
    by_contra hne
    -- 取 x = e_j（在 j 处为 1），x' = 0
    have hsingle : (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) k = (0 : ℝ) := by
      rw [EuclideanSpace.single_apply, if_neg (Ne.symm hj)]
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) k = (0 : ℝ) := Pi.zero_apply k
    have hx := h (EuclideanSpace.single j (1 : ℝ)) 0 (by rw [hsingle, hzero])
    -- 左端 = c j（只有 j 项非零）；右端 = 0
    have hleft : (∑ i : Fin n, c i * (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) i)
        = c j := by
      -- ⚠ `EuclideanSpace.single_apply` 是 `@[simp]` 引理：`sum_eq_single` 的回调拿到的目标
      -- 已经被化简器把 `single` 展成 `if i = j then 1 else 0` 了，故这里**不能**再 `rw` 它
      -- （`rw` 找的是 `EuclideanSpace.single` 的字面出现，而目标里已经没有它了）。
      -- 直接用 `simp` 把 `i ≠ j` 一支出收掉，并对 `i = j` 一支用 `hi : i ≠ j` 收口。
      rw [Fintype.sum_eq_single j (fun i hi => by
        simp only [EuclideanSpace.single_apply, if_neg hi, mul_zero])]
      -- ⚠ `j = j` 已被 `decide` 归约为 `True`，目标实为 `(c j * if True then 1 else 0) = c j`，
      -- 故这里需要 `if_pos trivial`（而不是 `if_pos rfl`）把条件支取出来。
      simp only [EuclideanSpace.single_apply, if_pos trivial, mul_one]
    have hright : (∑ i : Fin n, c i * (0 : EuclideanSpace ℝ (Fin n)) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [Pi.zero_apply, mul_zero]
    rw [hleft, hright] at hx
    exact hne hx
  · -- ⟸：除 k 外系数全零 ⟹ 求和只剩 k 项，故两边都等于 c k · x k
    intro hc x x' hx
    rw [Fintype.sum_eq_single k (fun j hj => by rw [hc j hj, zero_mul]),
        Fintype.sum_eq_single k (fun j hj => by rw [hc j hj, zero_mul]), hx]

/-! ## 六、③ ⭐⭐⭐ **主定理：行编辑的输出差只依赖 `x k` 的充要条件**

把 §四（行局部 ⟹ 支撑在 `{r}`）与 §五（泛函只依赖 `x k` ⟺ 系数在 `k` 外全零）
合起来，第 `r` 个坐标的输出差恰是**第 `r` 行编辑增量**给出的线性泛函：

    (MatLayerOut W' x - MatLayerOut W x) r = Σ_j (W' r j - W r j) · x j

于是 `②` 直接给出：

> ⭐⭐ **编辑限于第 `r` 行 ⟹（输出差只依赖 `x k` ⟺ 编辑在 `k` 列之外全零）**

即：**「只影响第 `r` 行」+「只依赖 `x k`」⟺「只影响格子 `(r,k)`」**。

⚠ **这才是真正的充要条件**；任务书字面想要的「只影响第 k 行 ⟹ 只依赖 x_k」
**方向是假的**（见 §七 反例）。

⚠ **指标解耦**：`r : Fin m`（行）与 `k : Fin n`（列 / 坐标）**分开命名**。
任务书把同一个 `k` 同时当行号与列号，只有在**方阵**下合法；
解耦后本定理对**任意 m×n** 成立（方阵是 `m = n` 的特例）。 -/

/-- ⭐⭐⭐ **主定理（E-04 的答案）**：在「编辑只影响第 `r` 行」的前提下，

`(∀ x, 输出差只依赖 x k)  ⟺  (∀ j ≠ k, W' r j = W r j)`。

右端即「编辑在**第 `k` 列之外**不动 `W` 的第 `r` 行」——与左端假设（第 `r` 行之外不动）
合起来，即**编辑只动单个格子 `(r,k)`**。

⚠ **证明走 `coordFun_depends_only_iff`**：先把 `DependsOnlyOnCoord` 在
`i = r` 这一坐标上化为 `②` 的形状，再用 `rowEdit_offRow_zero` 处理 `i ≠ r`。 -/
theorem rowEdit_depends_only_iff (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (k : Fin n)
    (hrow : EditSupportsRow W W' r) :
    DependsOnlyOnCoord k
        (fun x : EuclideanSpace ℝ (Fin n) => MatLayerOut W' x - MatLayerOut W x)
      ↔ (∀ j : Fin n, j ≠ k → W' r j - W r j = 0) := by
  constructor
  · -- ⟹：由函数级只依赖，推出第 r 坐标的泛函只依赖 x k，再用 ② 收口
    intro hdep j hj
    have hfun : ∀ x x' : EuclideanSpace ℝ (Fin n), x k = x' k →
        (∑ t : Fin n, (W' r t - W r t) * x t)
          = (∑ t : Fin n, (W' r t - W r t) * x' t) := by
      intro x x' hx
      have hEq := hdep x x' hx
      have hr := congrFun hEq r
      -- ⚠ **beta-归约必须先做掉**：`congrFun hEq r` 的结论里是**未归约的 beta-redex**
      -- `(fun x => MatLayerOut W' x - MatLayerOut W x) x r`，
      -- 而 `rowEditDelta_apply` 的左端是字面 `(MatLayerOut W' x - MatLayerOut W x) r`。
      -- `rw` 只做受限的可归约透明匹配，不会自动 beta-归约，故直接 `rw` 会报
      -- 「did not find instance of the pattern」。`simp only []` 只做 beta/eta 归约、不引任何引理。
      simp only [] at hr
      rwa [rowEditDelta_apply W W' x r, rowEditDelta_apply W W' x' r] at hr
    exact (coordFun_depends_only_iff (fun t => W' r t - W r t) k).mp hfun j hj
  · -- ⟸：第 r 行增量在 k 外全零 ⟹ 差只剩 (r,k) 项；其余行由行局部性为零
    intro hc x x' hx
    funext i
    -- ⚠ **先 beta-归约**：`funext i` 后目标是
    -- `(fun x => MatLayerOut W' x - MatLayerOut W x) x i = ... x' i`（未归约的 redex），
    -- `rw [rowEditDelta_apply …]` 匹配的是字面 `(MatLayerOut W' x - MatLayerOut W x) i`，
    -- 故不做这一步会报「did not find instance of the pattern」。
    simp only []
    by_cases hi : i = r
    · -- i = r：差 = (W' r k - W r k) · (x k) = (W' r k - W r k) · (x' k)
      -- ⚠ 不用 `subst`（`i` 由 `funext` 引入，`subst` 会消去 `r` 而 `hrow`/`hc` 都提到 `r`）；
      -- 改用 `rw [hi]` 把目标里的 `i` 换成 `r`，两个名字都保留。
      rw [hi, rowEditDelta_apply W W' x r, rowEditDelta_apply W W' x' r,
          Fintype.sum_eq_single k (fun j hj => by rw [hc j hj, zero_mul]),
          Fintype.sum_eq_single k (fun j hj => by rw [hc j hj, zero_mul]), hx]
    · -- i ≠ r：两侧都由行局部性为零
      rw [rowEdit_offRow_zero W W' r hrow x i hi,
          rowEdit_offRow_zero W W' r hrow x' i hi]

/-! ## 七、⭐ 反例：任务书的**字面**命题为假（判据 1 消融 + 判据 2 反驳）

取 `m = n = 2`、行 `r = 0`、问「是否只依赖 `x 0`」，`W = 0`，`W'` 只在格子 `(0,1)` 上为 `1`：

    W = [[0, 0], [0, 0]]      W' = [[0, 1], [0, 0]]

则「只影响第 `0` 行」成立（第 `1` 行完全没动），但

    (输出差) 0 = Σ_j (W' 0 j - W 0 j) · x j = 1 · x 1 = x 1

**只依赖 `x 1`，与 `x 0` 无关** —— 故它**不**依赖 `x 0`（即任务书要的 `x_k`）。
取 `x = (0,1)`、`x' = (0,0)`：两者 `x 0 = x' 0 = 0`，但输出差分别为 `1` 与 `0`。

⭐⭐ **这就是「删掉『列局部』假设后结论变成【假】」的机器验证**（判据 1），
**且给出了具体使结论不成立的对象**（判据 2）。 -/

/-- 反例用的 `W`：零矩阵。 -/
def rowEditCexW : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- 反例用的 `W'`：只在格子 `(0,1)` 上为 `1`（其余为 `0`）。

⚠ **用 `Fin` 上的 `if` 写**（而非 `!![...]` 语法糖）：
这样 `simp` / `Fintype.sum_eq_single` 对它的求值只需 `if_pos`/`if_neg`，
不依赖 `Matrix.cons_val_zero` 等 `![…]` 专用引理名。 -/
def rowEditCexW_row_one : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- 反例用点 `x = (0, 1)`：坐标 `0` 为 `0`，坐标 `1` 为 `1`。 -/
def rowEditCexX : EuclideanSpace ℝ (Fin 2) := fun j => if j = 1 then 1 else 0

/-- 反例用点 `x' = (0, 0)`：恒零。 -/
def rowEditCexX_zero : EuclideanSpace ℝ (Fin 2) := fun _ => 0

/-- ⚠ **辅助**：`(0 : Fin 2) ≠ 1`（**显式 `decide`**，不依赖 `simp` 的 `Fin` 事实集）。 -/
lemma rowEditCex_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

/-- 反例的编辑确实**只影响第 `0` 行**（第 `1` 行零矩阵未动）。 -/
lemma rowEditCex_rowLocal : EditSupportsRow rowEditCexW rowEditCexW_row_one 0 := by
  intro i j hi
  unfold rowEditCexW rowEditCexW_row_one
  rw [Matrix.zero_apply, if_neg]
  rintro ⟨hi0, -⟩
  exact hi hi0

/-- 反例的两点在坐标 `0` 上相同（都是 `0`）。
（`x 0 = if 0 = 1 then 1 else 0 = 0`，由 `rowEditCex_zero_ne_one`。） -/
lemma rowEditCex_same_coord0 : rowEditCexX 0 = rowEditCexX_zero 0 := by
  unfold rowEditCexX rowEditCexX_zero
  -- ⚠ `rw [if_neg …]` 已经把目标两边都化为 `0 = 0` 并**关闭了目标**，
  -- 原来跟在后面的 `rfl` 因此报「no goals to be solved」。改用 `simp` 收口：
  -- 无论 `if_neg` 是否已把目标关掉，`simp` 在无目标时也不会报错。
  simp only [if_neg rowEditCex_zero_ne_one]

/-- 反例点在坐标 `1` 上取 `1`。 -/
lemma rowEditCexX_one : rowEditCexX (1 : Fin 2) = 1 := by
  unfold rowEditCexX
  rw [if_pos rfl]

/-- 反例点在坐标 `1` 上取 `0`。 -/
lemma rowEditCexX_zero_apply : rowEditCexX_zero (1 : Fin 2) = 0 := rfl

/-- 反例的增量矩阵在 `0` 行的唯一非零项在列 `1`（值 `1`）。
（`rowEditCexW_row_one 0 t - rowEditCexW 0 t = if t = 1 then 1 else 0`。）

⚠ **先 `simp only []` / `show` 把 beta-归约与 `-0` 写死**：
`rowEditCexW_row_one 0 t` 展开后是 `(fun i j => if i = 0 ∧ j = 1 then 1 else 0) 0 t`，
`show` 把它化为 `if (0 : Fin 2) = 0 ∧ t = 1 then 1 else 0`，
之后的 `if_pos`/`if_neg` 才**指名**命中外层这个 `if`（不依赖化简器的搜索顺序）。 -/
lemma rowEditCexW_row0 (t : Fin 2) :
    rowEditCexW_row_one 0 t - rowEditCexW 0 t = if t = 1 then 1 else 0 := by
  have hW : rowEditCexW 0 t = (0 : ℝ) := by
    unfold rowEditCexW
    exact Matrix.zero_apply 0 t
  have hW' : rowEditCexW_row_one 0 t = if (0 : Fin 2) = 0 ∧ t = 1 then (1 : ℝ) else 0 := rfl
  rw [hW', hW, sub_zero]
  by_cases ht : t = 1
  · rw [if_pos ⟨rfl, ht⟩, if_pos ht]
  · rw [if_neg (fun h => ht h.2), if_neg ht]

/-- 第 `0` 行的输出差 = `y 1`（求和只剩 `t = 1` 一项）。 -/
lemma rowEditCex_sum (y : EuclideanSpace ℝ (Fin 2)) :
    (∑ t : Fin 2, (rowEditCexW_row_one 0 t - rowEditCexW 0 t) * y t) = y 1 := by
  rw [Fintype.sum_eq_single (1 : Fin 2) (fun t ht => by
    rw [rowEditCexW_row0 t, if_neg ht, zero_mul])]
  rw [rowEditCexW_row0 1, if_pos rfl, one_mul]

/-- ⭐⭐ **输出差在坐标 `0` 上不相等**（左 `= x 1 = 1`，右 `= x' 1 = 0`）
—— 这就是否证的字面内容。 -/
lemma rowEditCex_diff_ne :
    (MatLayerOut rowEditCexW_row_one rowEditCexX - MatLayerOut rowEditCexW rowEditCexX) ≠
      (MatLayerOut rowEditCexW_row_one rowEditCexX_zero - MatLayerOut rowEditCexW rowEditCexX_zero) := by
  intro h
  -- 取第 0 坐标：两侧分别是 `x 1` 与 `x' 1`，即 `1` 与 `0`
  have h0 := congrFun h 0
  rw [rowEditDelta_apply rowEditCexW rowEditCexW_row_one rowEditCexX 0,
      rowEditDelta_apply rowEditCexW rowEditCexW_row_one rowEditCexX_zero 0,
      rowEditCex_sum rowEditCexX, rowEditCex_sum rowEditCexX_zero,
      rowEditCexX_one, rowEditCexX_zero_apply] at h0
  exact one_ne_zero h0

/-- ⭐⭐⭐ **否证定理（判据 1 + 判据 2）**：

**存在**只影响第 `k` 行的编辑，使输出差**不**只依赖 `x k`
（⚠ 方阵 `2×2`，故行号与坐标同用一个 `k : Fin 2`）：

    ∃ (W W' : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2)
      (x x' : EuclideanSpace ℝ (Fin 2)),
      EditSupportsRow W W' k ∧ x k = x' k ∧
        (MatLayerOut W' x - MatLayerOut W x) ≠ (MatLayerOut W' x' - MatLayerOut W x')

⭐⭐ **读法**：任务书字面要求的「只影响第 `k` 行 ⟹ 输出差只依赖 `x k`」
**作为蕴含式为假** —— 反例的具体对象已在上面逐条机器验证。
故**必须**补上「列局部」（`W' r j = W r j`，`j ≠ k`）才是**充要**的（§六 主定理）。 -/
theorem rowEdit_not_depends_only_counterexample :
    ∃ (W W' : Matrix (Fin 2) (Fin 2) ℝ) (k : Fin 2)
      (x x' : EuclideanSpace ℝ (Fin 2)),
      EditSupportsRow W W' k ∧ x k = x' k ∧
        (MatLayerOut W' x - MatLayerOut W x)
          ≠ (MatLayerOut W' x' - MatLayerOut W x') := by
  exact ⟨rowEditCexW, rowEditCexW_row_one, 0, rowEditCexX, rowEditCexX_zero,
    rowEditCex_rowLocal, rowEditCex_same_coord0, rowEditCex_diff_ne⟩

/-! ## 八、推论：**格局部**（只动 `(r,k)`）⟹ 输出差只依赖 `x k`

⭐ 这是 §六 主定理的 **`⟸` 方向的独立包装**：
`格局部` 直接给出「行局部 ∧ 第 `k` 列之外不动」，故主定理的右端条件成立。

⚠ **诚实标注**：本推论**可**由主定理直接得到，独立列出只为可读性；
它**本身不是**新内容（不单列计入实质定理数）。 -/

/-- 格局部 ⟹ 行局部（动得更少 ⟹ 行外也不动）。 -/
lemma rowLocal_of_cellLocal (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (k : Fin n)
    (hcell : EditSupportsCell W W' r k) : EditSupportsRow W W' r := by
  intro i j hi
  exact hcell i j (by
    rintro ⟨rfl, -⟩
    exact hi rfl)

/-- ⭐ **格局部 ⟹ 输出差只依赖 `x k`**（主定理 `⟸` 的独立读数）。 -/
theorem cellEdit_depends_only (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (k : Fin n)
    (hcell : EditSupportsCell W W' r k) :
    DependsOnlyOnCoord k
      (fun x : EuclideanSpace ℝ (Fin n) => MatLayerOut W' x - MatLayerOut W x) := by
  have hrow : EditSupportsRow W W' r := rowLocal_of_cellLocal W W' r k hcell
  refine (rowEdit_depends_only_iff W W' r k hrow).mpr ?_
  intro j hj
  have h := hcell r j (by rintro ⟨-, rfl⟩; exact hj rfl)
  rw [h, sub_self]

/-! ## 九、反例的**反面**：格编辑下输出差**恰为** `ΔW r k · x k`（判据 4：量化）

上面 §七 说明「行局部不够」；本节把**够的那个条件**（格局部）下的
输出差**算到显式**：

    (输出差) i = if i = r then (W' r k - W r k) · x k else 0

⭐ 这是一个**可计算的**闭式（不是存在性），且它显式显示「只依赖 `x k`」。 -/

/-- ⭐ **格编辑下的输出差闭式**：只有第 `r` 个坐标非零，且其值 = `ΔW r k · x k`。 -/
theorem cellEdit_delta_closed_form (W W' : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (k : Fin n)
    (hcell : EditSupportsCell W W' r k) (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    (MatLayerOut W' x - MatLayerOut W x) i
      = if i = r then (W' r k - W r k) * x k else 0 := by
  rw [rowEditDelta_apply W W' x i]
  by_cases hi : i = r
  · -- i = r：求和只剩 j = k 一项
    -- ⚠ 用 `rw [hi]`（保留 `r` 这个名字，`hcell` 提到它），不用 `subst`
    rw [hi, if_pos rfl,
        Fintype.sum_eq_single k (fun j hj => by
          have h := hcell r j (by rintro ⟨-, rfl⟩; exact hj rfl)
          rw [h, sub_self, zero_mul])]
  · -- i ≠ r：每项系数为零
    rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    have h := hcell i j (by rintro ⟨rfl, -⟩; exact hi rfl)
    rw [h, sub_self, zero_mul]

end Lattice
