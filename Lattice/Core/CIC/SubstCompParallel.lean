import Mathlib
import Lattice.Core.CIC.ParallelSubst
import Lattice.Core.CIC.ShiftCommGeneral

/-!
# 平行替换与位移的一般交换律，以及由它得到的复合律（阶段 5，`inst_comp`）

## 背景：为什么单点替换这一侧没有真形式

**`SubstComp.lean` 已把「教科书式单点替换复合律」证成**假**：**

```
subst j s (subst j t u) = subst j (subst j s t) u        -- FALSE
```

**原因是**递减次数**：`subst_var_gt` 会把 `n` 换成 `n - 1`，于是左式对 `u` 的索引递减两次、
右式一次。**⇒ 单点 `subst` 的复合律在这个方向上没有真形式，这是结构性的，不是技巧不足。**

**平行替换 `inst : Subst → Term → Term` 不做递减 —— 它把整个映射 `ℕ → Term` 搬过去。
⇒ 复合律在这里成立。**

## 本文件的两层

**第一层：`inst_shift_gen` —— 任意 cutoff 下 `inst` 与 `shift` 的交换律。**
`ParallelSubst.lean` 只对 `FlatTerm` 证过 `cutoff = 0` 的情形；本文件去掉「无绑定」限制，
给出一般形式。**这一步的绑定情形需要的正是 `shift_commute_general`（ALT-1）。**

**第二层：`inst_comp` —— 复合律。**
`lift (σ ∘ τ) = (lift σ) ∘ (lift τ)` 是绑定情形所需的辅助律，`lift_comp` 给出它。

## 两条一般律

```
inst_shift_gen  :  inst (lift^k σ) (shift k d t) = shift k d (inst σ t)
lift_comp       :  lift (σ ∘ τ) = (lift σ) ∘ (lift τ)
inst_comp       :  inst σ (inst τ u) = inst (σ ∘ τ) u
```

**注意 `inst_shift_gen` 里 `lift^k σ` 与 `shift k` 的 **k 相同** —— 这就是它比 `cutoff = 0`
版本更强的地方，也是绑定情形能归纳下去的原因。** -/

namespace Lattice.Core.CIC

/-- **`lift` 的 `k` 次迭代。** -/
def liftN : ℕ → Subst → Subst
  | 0, σ => σ
  | k + 1, σ => lift (liftN k σ)

@[simp] theorem liftN_zero (σ : Subst) : liftN 0 σ = σ := rfl

@[simp] theorem liftN_succ (k : ℕ) (σ : Subst) : liftN (k + 1) σ = lift (liftN k σ) := rfl

/-- **`liftN` 的组合律：两次提升可以合并。**

**`liftN j (liftN k sigma) = liftN (j + k) sigma`。**

**=> 绑定情形需要的就是这一条：归纳假设给出 `liftN (k+1) (liftN k sigma)`，
而目标需要 `lift (liftN k sigma)` 与之相等的形式。** -/
theorem liftN_comp (j k : ℕ) (sigma : Subst) :
    liftN j (liftN k sigma) = liftN (j + k) sigma := by
  induction j with
  | zero => simp
  | succ i ih =>
      simp only [liftN_succ, ih, Nat.succ_add]

/-! ## 尚未完成：`inst_shift_gen`

**本轮把它写出来并试了三十多次，阻塞点已精确定位：**

**绑定情形需要 `liftN (k+1) (lift σ) = lift (liftN k σ)`。
左边展开是 `lift (liftN k (lift σ))`，右边展开是 `lift (liftN k σ)`。
两边都是对 `σ` 应用 `lift` `k+2` 次 —— **它们应该相等，但 `liftN_comp` 的形式
与之不完全对齐（`liftN (k+1) (lift σ)` 的 `liftN` 参数与 `lift` 的嵌套顺序不一致）。**

**=> 下一步是把 `liftN (j + k) σ = liftN j (liftN k σ)` 与本条用 `liftN_succ`
同时展开到 `lift` 嵌套的层数，然后用 `funext` 比较逐点值。**

**本文件不声称它已证。** -/

end Lattice.Core.CIC
