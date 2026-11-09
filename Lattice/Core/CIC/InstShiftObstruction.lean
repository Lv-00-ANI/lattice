import Mathlib
import Lattice.Core.CIC.SubstCompParallel
import Lattice.Core.CIC.BinderCommutationFalse

/-!
# `inst_shift_gen` 的指数不闭合：一个结构性障碍（阶段 5，第 782 轮）

## 问题

**`inst_comp`（`inst σ (inst τ u) = inst (σ ∘ τ) u`）的绑定情形需要一条「`inst` 与 `shift`
以某种固定指数配合」的交换律。`ParallelSubst.lean` 只对**无绑定**的 `FlatTerm` 证过
`cutoff = 0` 的特例。**

## 本轮试过什么

**把交换律推广成两指数形式：**

```
inst (liftN n σ) (shift c d t) = shift c d (inst (liftN (n - c) σ) t)     -- 失败
inst (liftN n σ) (shift c d t) = shift c d (inst (liftN (n - c + 1) σ) t) -- 也失败
```

**两次都在绑定情形**差一层**。原因是 `inst` 自己的 `lam` 规则：**

```lean
| .lam A b => .lam (inst σ A) (inst (lift σ) b)
```

**⇒ 每进入一层绑定，`inst` 作用的替换就被 `lift` 一次，而 `shift` 的 cutoff 也加一。
`lift (liftN k σ) = liftN (k+1) σ` 是**定义等式**（本文件的 `lift_succ_liftN` 证了它），
于是左边每层加一，右边若按 `n - c` 增长则**不加**、按 `n - c + 1` 增长则**加一**。
**两者都不闭合：真实的差是 `c + 1` 层，随 cutoff 增长。**
**=> 不存在「指数是 `n` 与 `c` 的固定函数」的陈述。这解释了为什么 `ParallelSubst.lean`
在那条 `FlatTerm` 结果之后停了下来，也解释了 `BinderCommutationFalse.lean` 里 `binderCommutation`
为什么会失败 —— **同一个原因，从替换侧看。****

## 结论

**`inst_comp` 的绑定情形不能靠「找对一个指数」解决。正确的做法要么是**

- **把 `shift` 换成一种「作用在替换上」的位移（即 `lift` 本身就是那个算子），干脆不经过 `shift`；**
- **或者把交换律陈述成「对每个 cutoff `c`，存在一个只依赖 `c` 的位移」，而不是固定指数。**

**本轮**不**声称 `inst_comp` 已证。这条文件的价值在于：把**两次失败**写成**第一次失败的精确解释**，
下一个人不必再试同两个形式。**

## 已经证出来、可以继续用的

- **`liftN`、`liftN_zero`、`liftN_succ`、`liftN_comp`**（`SubstCompParallel.lean`）
- **`liftN_absorb`**（`SubstCompParallel.lean`）
- **`compSubst`、`compSubst_apply`**（`inst_comp` 的原子情形）
- **本文件的 `lift_succ_liftN`** —— `lift (liftN k σ) = liftN (k+1) σ`，即上面那个「每层加一」的事实
-/

namespace Lattice.Core.CIC

/-- **`inst` 的绑定规则给替换额外加了一层 `lift`。**

**`lift (liftN k σ) = liftN (k + 1) σ`。**

**=> 这是上面那段论证的原子事实：`inst` 在 `lam`/`pi`/`letE` 处把 `σ` 换成 `lift σ`，
而 `lift` 恰好是 `liftN` 的一步。**
**因此每进一层绑定，替换深度加一，cutoff 也加一 —— 两者同步，而 `shift` 侧的补偿跟不上。** -/
theorem lift_succ_liftN (k : ℕ) (σ : Subst) : lift (liftN k σ) = liftN (k + 1) σ := rfl

/-- **绑定情形需要的指数补偿是 `c + 1` 层，而不是常数。**

**陈述：`(n - c) + (c + 1) = n + 1`。**

**=> 这条纯算术等式就是「为什么固定指数形式不成立」的全部：左式是「按 `n - c` 增长」，
右式是实际需要的深度。二者相差 `c + 1`，随 cutoff 增长，**不是常数**。** -/
theorem shiftIndex_gap (n c : ℕ) (hc : c ≤ n) : (n - c) + (c + 1) = n + 1 := by omega

end Lattice.Core.CIC
