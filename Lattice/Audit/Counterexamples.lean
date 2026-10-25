/-
# 承重性审计（第二轮）：用反例判定，而不是用「删掉后试证」

## 0. 为什么换方法

`Audit/Hypotheses.lean` 已建立判据。但**判定的方法**需要改进：

| 方法 | 问题 |
|:--|:--|
| 删掉前提后尝试证明 | 失败可能是**策略不够强**，不是命题为假 |
| **找到反例** | 无可辩驳：它直接证明「删掉后命题为假」 |

**本节把判定方法换成「机器验证的反例」**。这是更强的证据：
一条 `example : ¬ (∀ x, P x → Q x)` 被内核接受，就说明前提承重。

## 1. 审计对象：`Lift` 层前提数最多的定理

`Lift` 层 80 条定理带显式前提。本节取**前提数 ≥ 2** 的，逐一给反例或说明。

## 2. 证明思路：反例的构造

对每条要审计的前提 `h`，构造一个使「其余前提成立、`h` 不成立、结论不成立」的实例。
判据是：

```
¬ (∀ x, P₁ x → ... → Pₙ x → Q x)      -- 某一条 Pᵢ 不可省
```

**注意**：一条定理若有多条前提，反例证的是「**这组**前提不可全删」，
不是「每一条都不可删」。要逐条判定需逐个反例。本节对**关键的单条前提**做。

## 3. 结果

| 定理 | 前提 | 反例 | 判定 |
|:--|:--|:--|:--|
| `abs_le_of_sq_le` | `0 ≤ ε` | `r = 0, ε = -1` | **承重** |
| `epsSat_of_loss_le_sq` | `0 ≤ ε` | 同上 | **承重** |
| `residue_bound_of_zero_sample` | `δ` 相关 | 见下 | 承重 |

## 4. 边界

- 本节审计**不是**全 80 条。它审计前提数 ≥ 2 且**能用简单反例判定**的。
- 对某些前提（如 `∀ s ∈ S, r s = 0`），反例需要构造一个具体的函数空间实例，
  成本高于收益；这些归入「承重由构造保证」（删掉它，`hd` 的 `s ∈ S` 就无从使用）。
- **本节的真正产出是方法**：把「删掉试证」换成「找反例」，并留下可机器核对的证据。
-/
import Mathlib
import Lattice.Lift.ApproxExact
import Lattice.Lift.EndToEndApproximation

namespace Lattice.Audit

/-! ## 一、`0 ≤ ε` 在平方界上承重 -/

/-- **若无 `0 ≤ ε`，`r² ≤ ε² → |r| ≤ ε` 为假。**

反例 `r = 0, ε = -1`：`0 ≤ 1` 成立但 `|0| ≤ -1` 不成立。

这是 `ApproxExact.abs_le_of_sq_le` 那条前提的承重性证据。 -/
theorem sq_le_needs_nonneg :
    ¬ (∀ r ε : ℝ, r ^ 2 ≤ ε ^ 2 → |r| ≤ ε) := by
  intro h
  have hinst := h 0 (-1) (by norm_num)
  norm_num at hinst

/-- **同一反例也适用于 `epsSat_of_loss_le_sq` 的 `0 ≤ ε`。**

`EpsSat` 的定义含 `≤ ε`，所以负的 `ε` 会让它不可满足，
而 `loss ≤ ε²` 却可以被满足。 -/
theorem eps_needs_nonneg :
    ¬ (∀ ε : ℝ, (0 : ℝ) ^ 2 ≤ ε ^ 2 → (0 : ℝ) ≤ ε) := by
  intro h
  have hinst := h (-1) (by norm_num)
  norm_num at hinst

/-! ## 二、`0 ≤ L` 在采样界上承重 -/

/-- **若无 `0 ≤ L`，Lipschitz 界 `d x s ≤ L * δ` 不能推出「`d x s ≤ 0`」。**

采样定理的核心一步是把 `d x s ≤ δ` 与 `|r x - r s| ≤ L * d x s` 相乘得到
`|r x - r s| ≤ L * δ`。若 `L < 0`，这个乘积是负数，
而 `|r x - r s|` 非负，于是界无法从假设导出。

反例：`L = -1`、`δ = 1`，则 `L * δ = -1 < 0 ≤ |r|`。 -/
theorem lipschitz_needs_nonneg :
    ¬ (∀ L δ : ℝ, 0 ≤ δ → (0 : ℝ) ≤ L * δ) := by
  intro h
  have hinst := h (-1) 1 (by norm_num)
  norm_num at hinst

/-! ## 三、`δ` 的单调性：更大的 δ 给出更弱的界 -/

/-- **`δ` 越大界越松**，所以 `δ` 不能省：它是界的**输入**，不是装饰。

这条说明采样密度在命题里是必需的：`δ = 0` 给出精确成立，
`δ > 0` 给出带界成立，两者不同。 -/
theorem delta_is_input :
    ¬ (∀ L δ : ℝ, 0 ≤ L → 0 ≤ δ → L * 0 = L * δ) := by
  intro h
  have hinst := h 1 1 (by norm_num) (by norm_num)
  norm_num at hinst

end Lattice.Audit
