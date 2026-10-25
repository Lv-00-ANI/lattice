import Mathlib
import Lattice.Lib.Editing.RealOperatorSplit
import Lattice.Lib.Chain.RealLimitDiscrete
import Lattice.Lib.Editing.RealOpContract
import Lattice.Lib.Architectures.RealSiluSplit
import Lattice.Lib.Architectures.RealSiluRemainder
import Lattice.Lib.Architectures.RealSiluQuant
/-!
# LATTICE: RealOperatorSplitBridge —— 把 `theory/op-split` 接到 `Lattice` 命名空间

## 为什么需要这个文件（接线实测）

`theory/op-split` 的 6 个模块（`RealOperatorSplit`、`RealLimitDiscrete`、`RealOpContract`、
`RealSiluSplit`、`RealSiluRemainder`、`RealSiluQuant`）在合并前是**一个完全封闭的孤岛**：

```
    OperatorSplit → LimitDiscrete → OpContract
                         ↓
           SiluSplit → SiluRemainder → SiluQuant
                         │
                ⚠️ 零条边连到 main
```

实测（grep 全库）：`UnknownOp` / `residualOp` / `LimitDiscrete` / `OpContract` / `PolyApproxOn`
在 main 上**出现 0 次**；这 6 个模块也**不 import 任何 main 模块**。
⟹ **谁也用不了它** —— 「怎么用」的问题，实质是「怎么接线」的问题。

## 本文件做什么（**策略 S1：保持独立命名空间**）

**不修改** op-split 的 6 个文件（**一字未动**它们的 namespace 与证明体），
而是在 main 侧**新增**本桥接文件，做两件事：

  1. **`import`** 这 6 个模块 ⟹ 从此 `Lattice` 能看见它们；
  2. 把要用的结论**重述到 `Lattice` 命名空间**（下称「别名」）⟹ main 的读者
     不必记 `RealLimitDiscrete.LimitDiscrete` 这类冗长全限定名。

选择 S1 的理由：LATTICE 有「**不修改既有文件**」的先例 ——
`RealFenchelEReal` 明确写「**不修改** `RealFenchelMoreau`/`RealConjugateDuality`
（一字未动）……本文件是**独立的新权威**」。且改名会**破坏 op-split 的证明体**（需重编译）。

## ⭐ 归属声明（**必须**）

> ⚠ 本文件**所接的 6 个被 import 模块**（`RealOperatorSplit` / `RealLimitDiscrete` /
> `RealOpContract` / `RealSiluSplit` / `RealSiluRemainder` / `RealSiluQuant`）
> **全部由作者 `yjh051108` 所写**，经【从远端仓库拉取】获得（分支 `theory/op-split` @ `6428184`）。
> **本仓库不是该分支的作者**，仅对其作过只读审阅。
> 详见 `agent-workspace/branches/op-split-compare/ATTRIBUTION.md`。
> ⇒ 凡引用上述 6 个模块的定理，**须注明作者 `yjh051108`**，
> **不得表述为「本项目已有的成果」**。本文件（`RealOperatorSplitBridge`）的别名部分是本仓库新增。

## ⭐ 用途（接线后三类）

| 类 | 用途 | 本文件的别名 |
|:--|:--|:--|
| **A 通用工具** | `LimitDiscrete`（不依赖拓扑的近似收敛谓词）、`add_congr`（可组合性） | ✅ 已提供 |
| **B 需实例化** | 落到 SiLU/GELU：「用多项式替换激活」的误差界 | ⚠ 见文末「未做」 |
| **C 作为框架** | `UnknownOp` 统一「显式假设」、`OpContract` 形式化「待实现」 | ✅ 已提供 |

⭐ **最有前途的是 A 的 `add_congr`**：main 有 `RealChain` / `RealBlockLipschitz` / `RealModelChain`
这类**精确** Lipschitz 组合，但**没有对应的「近似版」**；
`add_congr` 是通向「多层网络**近似**误差传播」的唯一桥。

## ⭐⭐ 与 mathlib n 阶 Taylor 的接点（**本文件的第二个作用**）

用户笔记把「op-split 需要 n 阶 Taylor 余项，而 main 的 `RealTaylorMultivariate`
**只有一/二阶**」定为**最硬阻塞点**，并判定：「若 mathlib 有 n 阶 ⟹ 是**接线**（要点 1 级）；
若没有 ⟹ 是**新理论开发**（要点 3 级）」。

**实测答案：mathlib 有** —— `taylor_mean_remainder_bound`
（`Mathlib/Analysis/Calculus/Taylor.lean:299`）：

    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n !

`n` **任意**，`C` 是 `n+1` 阶导的界。另有 `exists_taylor_mean_remainder_bound`（`:340`）
自动给出 `C`（不需手给导数界）。

⚠ **一处常数差（必须登记）**：op-split 要的分母是 `(n+1)!`，mathlib 给的是 `n!`
⟹ **mathlib 的界松 `n+1` 倍**；取 `M := C * (n + 1)` 即**逐字**得到 op-split 的形式
（本文件 §2 用 `Nat.cast_add_one_ne_zero` 把这一步的**非零性**核验为定理）。

⇒ 要点 **结论：第 4 项是「接线」（要点 1 级），不是「新理论开发」（要点 3 级）** ⟹ 五层路线**可行**。
本文件 §2 即这条接线的一步。

## 诚实边界（**标注**）

1. ⭐ **本文件不新增数学** —— 除 §2 的 `taylor_denom_correction` 外，全部是
   **`abbrev`/别名与重述**（definitionally equal），**未做**新证明。
   §2 那条也只是**算术改写**（`(n+1)! = (n+1) * n!` 的分母对齐），不是分析内容。
2. ⭐ **本文件不解决 SiLU 实例化** —— 把 §1 的 `AddCongr` 用到真实激活/层
   （`RealActComplete` / `RealSymbolToWeightNonlinear`）**未做**，属**后续工作**。
3. ⭐ **`mul_congr`（乘法组合性）未做** —— op-split 只有 `add_congr`，
   而层与层之间是**乘法/复合**；没有 `mul_congr`，T2 **无法**从单层传到多层。
   这是 op-split 从「孤立框架」变成「可用工具」的**关键一步**，**留待**后续。
4. ⭐ **本文件不把 op-split 的公理读成定理** —— 「一切非线性皆 T2」是**用户公理**，
   且定量界的 `Z^(n+1)/(n+1)!` 形式**只对光滑激活**成立（ReLU 不成立）。
   本文件**不证**、也不隐含这些。
5. ⭐ **未做**：本文件的别名**不覆盖** op-split 的全部 25 条声明，
   只覆盖用途 A/C 所需的入口；其余仍可用全限定名访问。
-/

namespace Lattice

/-! ## §1 用途 A/C：把 op-split 的通用装置接到 `Lattice`

这些别名是 **`abbrev`**（而非 `def`），因此与原名**定义上相等**，
`Lattice.LimitDiscrete` 与 `RealLimitDiscrete.LimitDiscrete` 可互换使用。 -/

/-- **别名**：未命名算子（作者 `yjh051108`，`RealOperatorSplit`）。

「未命名算子」的载体：给「暂时说不清是什么」的部分一个一等公民身份。
⚠ 它不是 `sorry` 占位符 —— 它是**真实存在的函数**，只是名字待补。 -/
abbrev UnknownOp := RealOperatorSplit.UnknownOp

/-- **别名**：残差算子 `U x = f x - D x`（作者 `yjh051108`，`RealOperatorSplit`）。

关键一步：把「逆向编译失败的部分」从**否定性事实**（「逆不回去」）
变成**肯定性对象**（「这是那个差」）。 -/
abbrev residualOp := @RealOperatorSplit.residualOp

/-- **别名**：T1 分解恒等式（作者 `yjh051108`）。

⭐ 诚实标注：这是**恒等式**（`add_sub_cancel` 一行），**不是**存在性结果；
其作用是给「未解释的部分」一个显式名字。 -/
abbrev t1_decompose := @RealOperatorSplit.t1_decompose

/-- **别名**：极限离散等效 —— 不依赖拓扑的近似收敛谓词（作者 `yjh051108`）。

两字段：误差有界 + 界趋于 0。用裸 `ℝ`-值距离，**不用 `MetricSpace`**。
⭐ 这是用途 A 的核心工具。 -/
abbrev LimitDiscrete := @RealLimitDiscrete.LimitDiscrete

/-- **别名**：近似收敛在**加法**下封闭（作者 `yjh051108`）。

⭐⭐ **这是通向「多层网络近似误差传播」的唯一桥**：
main 有精确 Lipschitz 组合（`RealChain` / `RealModelChain`），但没有「近似版」。

⚠ 它要求把距离的三角不等式作为**显式前提**传入（`hdist_add`）——
诚实设计，不假设 `dist` 是度量。 -/
abbrev add_congr := @RealLimitDiscrete.add_congr

/-- **别名**：T1↔T2 桥（作者 `yjh051108`）。已知 `D` 精确时，`D+U ≡lim D+Uₙ`。 -/
abbrev t1_t2_bridge := @RealLimitDiscrete.t1_t2_bridge

/-- **别名**：算子契约 —— 入库对象（作者 `yjh051108`，`RealOpContract`）。

⭐ 用途 C：它是「实现侧后置」的**形式化载体** ——
`semantic := none` 合法，即「**先入库、后补名**」。
⚠ 它**不解决**「契约无实现对象」这一缺口，只是把「待实现」**形式化**了。 -/
abbrev OpContract := RealOpContract.OpContract

/-- **别名**：语义等式义务（作者 `yjh051108`）。`semantic = none` 时**自动为真**。 -/
abbrev DefEq := @RealOpContract.DefEq

/-- **别名**：多项式在紧致区间对 σ 的逼近 + 余项 `εₙ → 0`（作者 `yjh051108`，`RealSiluSplit`）。 -/
abbrev PolyApproxOn := @RealSiluSplit.PolyApproxOn

/-! ## §2 ⭐ 与 mathlib n 阶 Taylor 的接线（**阻塞点的解除**）

用户笔记的**头号阻塞点**是：op-split 需要 **n 阶** Taylor 余项，
而 main 的 `RealTaylorMultivariate` **只有一/二阶**（实测：8 条声明，
`first_order_taylor` / `first_order_taylor_mvt` / `second_order_taylor` /
`quadratic_remainder_bound` / `taylor_quadratic_lower_bound` …，无 n 阶）。

**mathlib 有 n 阶**（`Analysis/Calculus/Taylor.lean:299`，逐字）：

    theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
        (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
        (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
        ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n !

⚠ **常数口径差**：op-split 的形式分母是 `(n+1)!`，mathlib 给 `n!`
⟹ **mathlib 松 `n+1` 倍**。取 `M := C * (n+1)` 即对齐。
下面把这一步的**唯一非平凡点**（分母换算的非零性）核验成定理。 -/

/-- ⭐ **分母对齐的非零性核验**（把 mathlib 的 `n!` 口径换成 op-split 的 `(n+1)!` 口径）。

op-split 的 `RealSiluRemainder.eps_pow_fact_to_zero` 里要按 `ε / M` 取阈值，
而 `RealSiluSplit.mul_split_limit_discrete` 专门分支处理了 `M = 0` 的退化情形
（`by_cases hM0 : M = 0`）—— 漏了会在 `M = 0` 时除零失败。

本定理把「`C * (n + 1)` 这一口径换算在 `C` 一侧是合法的」这一点的**非零性**钉住：
`(n + 1 : ℝ) ≠ 0`，故 `M := C * (n+1)` 与 `C` 同号、不引入退化。
即：**从容差口径换算不引入新的退化分支**。 -/
theorem taylor_denom_correction (n : ℕ) : (n + 1 : ℝ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

/-- ⭐ **口径换算恒等**：`(n+1)! = (n+1) * n!` —— op-split 的分母与 mathlib 的分母之比。

这把「`M := C * (n+1)` 即得 op-split 形式」这一步**逐字**钉住：
`C * Z^(n+1) / n! = (C*(n+1)) * Z^(n+1) / (n+1)!`。
⚠ 本式是**算术改写**（结合 `taylor_denom_correction` 的非零性），
**不是**分析内容；分析内容由 mathlib `taylor_mean_remainder_bound` 提供。 -/
theorem taylor_denom_ratio (n : ℕ) :
    ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- ⭐ **口径换算（除法形式）**：给定 `h : C = M / (n+1)`，
则 mathlib 的 `C * Z^(n+1) / n!` 等于 op-split 的 `M * Z^(n+1) / (n+1)!`。

这是 §2 的**落点**：取 `M := C * (n+1)` 时，两者的余项界**逐字相同**。
⚠ 本式**只做**分母口径对齐；「σ 光滑」与「`n+1` 阶导一致有界」仍是
mathlib 定理的**显式前提**（`hf` / `hC`），本文件**不证**它们。 -/
theorem taylor_denom_bridge (C Z M : ℝ) (n : ℕ) (hC : C = M / (n + 1 : ℝ)) :
    C * Z ^ (n + 1) / (n.factorial : ℝ)
      = M * Z ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  subst hC
  rw [taylor_denom_ratio n]
  have hne : ((n + 1 : ℝ)) ≠ 0 := taylor_denom_correction n
  field_simp

/-! ## §3 未做（**留待**后续工作）

以下**明确未做**，不得读作已完成：

1. ⭐ **把 §1 的 `AddCongr` 用到真实激活/层** —— 需要「SiLU 在 `|z| ≤ Z` 上
   `n+1` 阶导一致有界」这一前提，再代入 `mul_split_limit_discrete`。
   **未做**（属 B 类用途）。
2. ⭐ **补 `mul_congr`（乘法组合性）** —— op-split 只有 `add_congr`，
   而层与层之间是**乘法/复合**。**没有它，误差无法从单层传到多层**，
   而多层正是 main 的核心交付（`RealModelChain`）。**未做**，是**关键**的下一步。
3. ⭐ **实例化到 SiLU/GELU-tanh** —— 使 `σ` 从抽象函数参数变成具体激活。
   `RealGeluExact` 已有「精确式 vs tanh 逼近」的差界，与 `LimitDiscrete` 框架
   是**同一件事的具体版与抽象版**。**未做**。
4. ⭐ **把 `RealTaylorMultivariate` 与 mathlib n 阶余项对接** ——
   §2 只做到**口径对齐**；真正的 `ContDiffOn` / 导数界前提**未接**。
5. ⭐ **`e25` / `e26` / `e25_s3_split`** 是被 import 模块 docstring 里的
   **工程编号（仓库外）**，本仓库**不证**其存在（已在那 6 个文件里**标注**）。

## 参考文献

- `Mathlib/Analysis/Calculus/Taylor.lean:299` — `taylor_mean_remainder_bound`（n 阶，任意 n）
- `Mathlib/Analysis/Calculus/Taylor.lean:340` — `exists_taylor_mean_remainder_bound`（自动给 C）
- `RealTaylorMultivariate` — main 的 Taylor：**只有一/二阶**（8 条声明）
- `RealCompileExtractClosed:79` — 「一般非线性下编译-提取可逆」**已证为假**
- `RealFenchelEReal` — 「**不修改**既有文件、独立新权威」的**先例**
-/

end Lattice
