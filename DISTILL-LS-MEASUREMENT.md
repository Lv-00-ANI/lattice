# `#15` 的测量：`Ls` 那条桥的零件**已经存在**，缺的是一步 sup-范数提升

> **第 21 轮。** 本文档记录对 `chain_distill_bound_lipschitz` 的 `register` 条目所做的测量与两次尝试。
> **本轮没有代码改动。** 尝试被回滚——理由见 §4。

---

## 1. 那条 `register` 说的是什么

`Lib/LearningTheory/RealDistill.lean:181` 的 `chain_distill_bound_lipschitz` 里，
`Ls : ℕ → ℝ` 是**自由函数**，前提 `hLt`/`hLs` 只说「每层是 `Ls i`-Lipschitz」。
doc 自己写着「**诚实假设**：师生层共享常数上界 `Ls i`（若不同取 max）」。

**所以 `Ls` 从未由权重导出。** `register` 要的桥是：「由网络结构（权重范数）导出逐层常数」。

---

## 2. 测量：零件已经在树里

| 已有 | 位置 | 形式 |
|:--|:--|:--|
| **`affineAct_lipschitz`** | `Runtime/StackError.lean:120` | **逐分量**：`(∀ i, |u i − v i| ≤ δ) → ∀ j, |affineAct L u j − affineAct L v j| ≤ layerMag L · δ` |
| **`layerMag_nonneg`** | 同上 `:106` | `0 ≤ layerMag L` |
| `netAct_lipschitz` | 同上 `:411` | 栈版 |
| `affineAct_abs_le` | 同上 `:146` | 同输入、不同层的界 |

`affineAct` 出现在 **16 个文件**里（`Runtime/StackError.lean` 用了 131 次），但**没有一处**把
`affineAct_lipschitz` 提升到 `‖·‖`。

**所以缺的不是数学，是两步搬运**：

1. **逐分量 → sup 范数**：`‖affineAct L u − affineAct L v‖ ≤ layerMag L · ‖u − v‖`；
2. **师生取 max**：`Ls i := max (layerMag (Wt i)) (layerMag (Ws i))`。

第 2 步是物流（`le_max_left`/`le_max_right` + `mul_le_mul_of_nonneg_right`），**没有风险**。
第 1 步是唯一的卡点。

---

## 3. 第 1 步为什么卡住（四次尝试，全部失败）

前提都成立：`hδ : 0 ≤ ‖u − v‖` 由 `norm_nonneg`；
`hcoord : ∀ i, |u i − v i| ≤ ‖u − v‖` 由 **`norm_le_pi_norm`**（这个名字存在，且可直接用）。
于是 `affineAct_lipschitz` 给出 `∀ j, |…| ≤ layerMag L · ‖u − v‖`。

**卡在最后一步：从逐分量界得到 `‖·‖` 界。** 试过：

| 尝试 | 结果 |
|:--|:--|
| `pi_norm_le_iff_of_nonneg (by positivity)` | `typeclass instance problem is stuck: (i : ?m) → SeminormedAddGroup (?m i)`——**族的类型没被推断** |
| `rw [Pi.norm_def]; exact ciSup_le …` | `typeclass instance problem is stuck: Nonempty ?m`——同上 |
| `pi_norm_le_iff.mpr key` | **`unknown identifier`**——这个名字不存在 |
| `pi_norm_le_iff_of_nonneg (f := …) …` | **`invalid argument name 'f'`**——它的隐式参数**不叫 `f`** |

实测确认 `pi_norm_le_iff_of_nonneg` **确实存在**（在 mathlib 的
`Analysis/Analytic/Constructions.lean` 一带），但它的**参数名与隐式参数形状**与我猜的不同，
而 `grep` 没能在该文件里定位到 `theorem pi_norm_le_iff_of_nonneg` 那一行（可能是 `lemma`
或带属性，也可能是同名不同文件）。

⭐ **下一步的确切起点**：在 mathlib 里 `#check @pi_norm_le_iff_of_nonneg`，看清它的
**显式/隐式参数顺序**，或者改用
`Finset.sup_le` + `Pi.norm_def`（把 `Fin n` 写成显式类型标注，
避免族的推断问题）。**两条路都只需一次 `#check`。**

---

## 4. 为什么本轮**不**发布那两个文件

我可以写出**能编译**的半成品：

- `affineAct_lipschitz_norm` 留成一条**未证**的假设 → 那就是假造；
- 或者把 `chain_distill_affine` 的 `Ls` 推导**跳过**，只把既有定理重述一遍 → **零新内容**。

**两者都不是本项目的标准。** 而且 `#15` 的**价值全在第 1 步**：没有它，`Ls` 仍然是自由参数。

**所以回滚，把测量留下。** 这份测量把「零件已经存在、只差一步、而那一步的确切障碍是
`pi_norm_le_iff_of_nonneg` 的参数形状」写清楚了——**下一次尝试不必重新发现这些**。

⚠ **这也是本会话第三次在同一类事情上止损**（第 18 轮的 `layerWords_injective`、本轮的 sup-范数提升）：
**判断一条引理值不值得再一轮，本身是工作量的一部分**，而「发布一个看起来完整的文件」永远比
「留下一份精确的未完成记录」更糟。

---

## 5. 本轮的净产出

- ✅ **测量**：零件清单与位置（§2），**这是可复用的**；
- ✅ **障碍定位**：四次失败的确切报错（§3），**下一次一次 `#check` 就能过**；
- ❌ **代码**：零（回滚）。

**`register` 计数不变（96）**——因为这一条**没有关闭**，也不该被记为关闭。

---

## 6. ⭐ 后记：**第五次尝试成功了**

上面 §3 列的四种写法全部失败之后，我没有停在那里——**去 mathlib 源码里看别人怎么用这个引理**，
发现它的用法**一律是**

``lean
rw [pi_norm_le_iff_of_nonneg h]
intro i
``

而不是 |>.mpr。**w 能从目标里推断那个隐含的 ，而项级的 |>.mpr 不能**——
这正是四次失败的唯一成因。

改用 w 之后一次通过，Lattice/Lib/LearningTheory/DistillLip.lean 现在包含：

| 定理 | 内容 |
|:--|:--|
| **ffineAct_lipschitz_norm** | ‖affineAct L u − affineAct L v‖ ≤ layerMag L · ‖u − v‖——逐分量提升到 sup 范数 |
| **chain_distill_affine** | **Ls i := max (layerMag (Wt i)) (layerMag (Ws i))**，即 Ls **由权重导出** |

**所以 §4 那段「不发布」的判断在当时是对的（手上确实只有半成品），而结论需要更新**：
这一条 egister **已关闭**，egister 96 → 95。

⭐ **可迁移的教训**：**卡在一条 mathlib 引理上时，去读它的调用点，而不是猜它的参数形状。**
四次猜参数 vs 一次读调用点。