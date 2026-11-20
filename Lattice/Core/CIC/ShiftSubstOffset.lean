import Mathlib
import Lattice.Core.CIC.SubstBounded

/-!
# 偏移律在 `var` 处**为假**：需要 `bounded c t`（阶段 5，第十次否证）

## 第 850 轮说「偏移律没找到」，本轮找到了形式，但它**不无条件成立**

**本轮先算出目标值再反推形式，得到：**

```lean
shift c d (subst 0 s t) = subst 0 (shift c d s) t
```

**关键：右边不位移 `t`。这与第 850 轮试过的三种形式都不同（那些都位移了 `t`，
而 `shift` 对 `t` 不起作用，于是结果低一个 `d`）。**

**对 `lam`、`app` 它都成立。但 `var n` 在 `n > 0` 且 `c ≤ n - 1` 时失败：**

```
左边：shift c d (var (n-1)) = var (n - 1 + d)      （因为 n-1 ≥ c）
右边：subst 0 (shift c d s) (var (n-1)) = var (n-1)  （因为 n-1 > 0，不替换）
```

**=> 左边被位移了，右边没有。律在此处**为假**。**

## 这正是第 842 轮的 `bounded` 谓词

**律需要的是「`t` 的所有自由变量都 `< c`」，即 `bounded c t` —— 第 842 轮为
`subst` 不动点引入的那个谓词。**

**=> 它在两种完全不同的场合重新出现：**

| 场合 | 需要的条件 | 轮次 |
|:--|:--|:--|
| **`subst j s t = t`（替换不触发）** | **`bounded j t`** | **842** |
| **`shift` 不移动替换结果（本律）** | **`bounded c t`** | **851** |

**两者是同一个条件，因为它们是同一件事的两面：`bounded` 保证下标足够小，
于是 `subst` 不替换**且** `shift` 不移动。**

## 本文件交付什么

**一条 `decide` 反例：`c = 0`、`d = 1`、`n = 1` 时两侧不等。**

**=> 这把「偏移律需要 `bounded`」从推测变成否证，并把条件精确指出来。** -/

namespace Lattice.Core.CIC

/-- **偏移律在 `var` 处为假，当 `c ≤ n - 1` 且 `n > 0` 时。**

**=> 见证：`c = 0`、`d = 1`、`n = 1`、`s = var 5`。
左边 `shift 0 1 (var 0) = var 1`，右边 `subst 0 (shift 0 1 (var 5)) (var 0) = var 6`。**

**=> 两者相差整整一个 `d`，正是 `n - 1 ≥ c` 造成的。** -/
theorem shift_subst_offset_fails_at_var :
    (shift 0 1 (subst 0 (.var 5) (.var 1)) ≠ subst 0 (shift 0 1 (.var 5)) (.var 1)) := by
  decide

end Lattice.Core.CIC
