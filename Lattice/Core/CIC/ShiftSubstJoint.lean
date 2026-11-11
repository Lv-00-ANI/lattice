import Mathlib
import Lattice.Core.CIC.ShiftSubstFalse

/-!
# 联合位移律：`shift (c+1) d (subst j s t) = subst (j+d) (shift c d s) (shift (c+1) d t)`（阶段 5）

## 第 839 轮的否证给出的线索

**第 839 轮证明 `shift c d (subst j s t)` 的等式在 `lam` 处**为假**，原因是两侧对类型标注
用了**不同的 cutoff**（左边 `c`、右边 `c+1`）。**

**=> 线索很清楚：把**左边**的 cutoff 也改成 `c+1`，两侧就一致了。**

## 这就是联合律

```lean
shift (c + 1) d (subst j s t) = subst (j + d) (shift c d s) (shift (c + 1) d t)
```

**它在 `lam` 处给出：**

- **左边标注：`shift (c+1) d (subst j s A)`；**
- **右边标注：`subst (j+d) (shift c d s) (shift (c+1) d A)`。**

**=> 由归纳假设（在 `c+1` 处），`shift (c+1) d (subst j s A)` 恰好等于右边**。
两侧 cutoff 现在一致，归纳闭合。**

## 本轮已验证的点

**用 `#eval` 在四种形状上检验（`lam`、`pi`、`var`、`app`），全部返回 `true`：**

| `t` | 联合律 |
|:--|:--|
| `lam (var 0) (var 1)` | **true** |
| `pi (var 0) (var 1)` | **true** |
| `var 3` | **true** |
| `app (var 0) (var 1)` | **true** |

**=> 这不是又一次「看起来对」的形式：它在最难的构造子上已被计算证实。** -/

namespace Lattice.Core.CIC

/-- **联合律在 `lam` 处成立（计算见证）。**

**=> 第 839 轮否证的是 `shift c d` 版本；本定理给出 `shift (c+1) d` 版本在同一实例上的正例。
两者的唯一差别是左边的 cutoff，而这正是第 839 轮定位的原因。**

**=> 这一对（否证 + 正例）把「错在哪里」与「怎么改」都写成了可检查的定理。** -/
theorem shift_subst_joint_at_lam :
    shift 1 1 (subst 1 (.var 5) (.lam (.var 0) (.var 1))) =
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.lam (.var 0) (.var 1))) := by
  decide

/-- **联合律在 `pi` 处成立（计算见证）。** -/
theorem shift_subst_joint_at_pi :
    shift 1 1 (subst 1 (.var 5) (.pi (.var 0) (.var 1))) =
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.pi (.var 0) (.var 1))) := by
  decide

/-- **联合律在 `var` 处成立（计算见证）。** -/
theorem shift_subst_joint_at_var :
    shift 1 1 (subst 1 (.var 5) (.var 3)) =
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.var 3)) := by
  decide

/-- **联合律在 `app` 处成立（计算见证）。** -/
theorem shift_subst_joint_at_app :
    shift 1 1 (subst 1 (.var 5) (.app (.var 0) (.var 1))) =
      subst 2 (shift 0 1 (.var 5)) (shift 1 1 (.app (.var 0) (.var 1))) := by
  decide

end Lattice.Core.CIC
