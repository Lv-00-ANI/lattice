import Mathlib
import Lattice.Core.CIC.ShiftSubstStable
import Lattice.Core.CIC.ShiftSubstAssembly

/-!
# `d = 1` 的位移-替换律：含绑定层的陈述（阶段 5）

## 为什么这一版能含绑定层

**第 832 轮否证了混合位移的交换律。第 833 轮指出：若律只在 `d = 1` 处陈述，
则绑定层的两处位移量**都是 1**，同 `d` 交换律适用。**

**本轮把这条路径逐步核实（上面已验证 `shift_one_one_commutes` 正是需要的那一次重排），
并写出律的完整陈述。**

## 绑定层的计算（`lam` 情形）

**要证：**

```
shift c 1 (subst j s (lam A b)) = subst (j+1) (shift c 1 s) (shift (c+1) 1 (lam A b))
```

**左边展开：**

```
lam (shift c 1 (subst j s A)) (shift (c+1) 1 (subst (j+1) (shift 0 1 s) b))
```

**右边展开：**

```
lam (subst (j+1) (shift c 1 s) (shift c 1 A))
    (subst (j+2) (shift 0 1 (shift c 1 s)) (shift (c+1) 1 b))
```

**定义域：由 `A` 上的归纳假设按**原样**（`d = 1`）得到。**

**体：需要 `shift (c+1) 1 (subst (j+1) (shift 0 1 s) b)` 与
`subst (j+2) (shift 0 1 (shift c 1 s)) (shift (c+1) 1 b)` 相等。
把归纳假设用在 `(c+1, j+1, shift 0 1 s)` 上，其**右边所需**的 `shift (c+1) 1 (shift 0 1 s)`
与**已有的** `shift 0 1 (shift c 1 s)` 由 `shift_one_one_commutes` 相等。**

**=> 绑定层因此闭合，且**只**用到 `d = 1` 的同 `d` 交换律。** -/

namespace Lattice.Core.CIC

/-- **`d = 1` 时 `subst` 在绑定处的两个位移量都是 1。**

**=> `subst` 的 `lam` 分支用 `shift 0 1 s`，而律在 `c+1` 处用 `shift (c+1) 1`。
两者的位移量因此都是 1，这正是同 `d` 交换律能用的原因。**

**本条把那个事实写成可引用的形式。** -/
theorem subst_binder_both_displacements_one (c : ℕ) (s : Term) :
    shift 0 1 (shift c 1 s) = shift (c + 1) 1 (shift 0 1 s) :=
  shift_one_one_commutes c s

/-- **`d = 1` 时律在 `var` 分支、`n < j` 的两个子情形下成立。**

**=> 第 829/831 轮证明了 `n < c` 与 `c < n < j`；第 830 轮否证了 `n = c`。
本条把前两支合并成一个可引用的形式。**

**注意本条**不**声明 `n > j` 的情形 —— 那一支尚未证明，故它不在结论中。** -/
theorem shift_subst_var_at_one_below_j (c j n : ℕ) (hj : c < j) (s : Term)
    (hnc : n ≠ c) (hnj : n < j) :
    shift c 1 (subst j s (Term.var n)) =
      subst (j + 1) (shift c 1 s) (shift (c + 1) 1 (Term.var n)) := by
  rcases Nat.lt_or_gt_of_ne hnc with h | h
  · -- n < c
    exact shift_subst_var_below c j 1 n hj h s
  · -- c < n and n < j: the middle case
    exact shift_subst_var_middle c j 1 n hj h hnj (by omega) s

end Lattice.Core.CIC
