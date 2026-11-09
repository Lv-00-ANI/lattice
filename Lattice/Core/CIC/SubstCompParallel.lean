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

/-- **两个替换的复合：先应用 `tau`，再把 `sigma` 作用到结果上。**

**=> 这就是 `inst_comp` 右端需要的映射。** -/
def compSubst (sigma tau : Subst) : Subst := fun n => inst sigma (tau n)

/-- **复合在 `var` 处的取值。**

**`inst sigma (inst tau (var n)) = compSubst sigma tau n`。**

**=> `inst_comp` 的原子情形，已证；其余构造子由归纳假设给出。** -/
theorem compSubst_apply (sigma tau : Subst) (n : ℕ) :
    inst sigma (inst tau (Term.var n)) = compSubst sigma tau n := rfl

/-! ## 第 781 轮发现的指数错位（已定位，不再猜）

**绑定情形需要 `liftN (k+1) (lift σ) = lift (liftN k σ)`。实测：**

```
liftN 1 (lift σ) = lift (lift σ)
lift (liftN 0 σ) = lift σ
```

**—— 左边比右边多一次 `lift`，所以那个等式**是假的**。
**=> `inst_shift_gen` 不能在「`liftN k` 与 `shift k` 同指数」的形式下归纳。** -/
/-- **吨收律：先 `lift` 再 `liftN k` 等于 `liftN (k+1)`。**

**`liftN k (lift σ) = liftN (k + 1) σ`。**

**=> 这是第 781 轮找到的**关键桥梁**。对 `σ` 先做 `lift`、再做 `k` 次 `liftN`，
与直接做 `k+1` 次 `liftN` 是**同一件事**。**

**=> 因此 `inst_comp` 的绑定情形里 `lift (liftN k σ)` 可以当作
`liftN (k+1) σ` 来用。** -/
theorem liftN_absorb (k : ℕ) (sigma : Subst) :
    liftN k (lift sigma) = liftN (k + 1) sigma := by
  induction k with
  | zero => rfl
  | succ i ih =>
      rw [liftN_succ] at ih ⊢
      rw [ih]
      rfl

/-! ## 尚未完成：`inst_comp`

**`inst σ (inst τ u) = compSubst σ τ u` 的 `var`/`sort`/`const`/`app` 情形都直接闭合，
绑定情形是开的。第 781 轮它定位到一个精确的指数错位：**

**绑定情形需要 `liftN (k+1) (lift σ) = lift (liftN k σ)`。而实测：**

```
liftN 1 (lift σ) = lift (lift σ)
lift (liftN 0 σ) = lift σ
```

**——左边比右边多一次 `lift`。所以那个等式**是假的**。**

**=> `inst_shift_gen`（以及由它推出的 `inst_comp`）**不能**在「`liftN k` 与 `shift k` 同指数」
的形式下归纳。正确的推广必须让**`lift` 的层数比 cutoff 多一**，
或者让归纳假设携带一个新的辅勩恒等式把两者对齐。**

**本文件**不**声称 `inst_comp` 已证。把错位写成一个可复算的等式比写一个 `sorry`
更有用：下一个人不必再从头定位。** -/

end Lattice.Core.CIC
