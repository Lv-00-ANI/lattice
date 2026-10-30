import Mathlib

/-!
# `Lattice.Core.AnalysisHelper` — **两条只依赖 `Mathlib` 的导数小引理**

## 为什么单独一个文件

**这两条是纯实分析事实，与 `Lattice` 的任何载体无关**：

1. **`y ↦ y²` 在 `y` 处的导数是 `(2y) • id`**；
2. **`smulRight 1 k` 等于 `k • id`**。

**它们在第 114 轮的定位过程中暴露了一个实例推断现象**：同样的证明在只 `import Mathlib` 时通过，
在多 `import Lattice.Domains.Constraints.Dist` 之后报
`typeclass instance problem is stuck: NormedSpace ?m`。

**⇒ 处理方式是【分层】：纯实分析的引理放在只依赖 `Mathlib` 的最底层，
`Domains` 侧引用它们，而不在 `Dist` 之后再证一遍。**

**这不是绕过错误，而是把它放在正确的层**：`y ↦ y²` 的导数不需要知道 `sqDist` 是什么。

## ⚠ 三条被探针钉死的写法要点

1. **`fun_prop` 不支持 `HPow.hPow`**（报 `No theorems found for HPow.hPow`）；
2. **`hasFDerivAt_pow` 不存在**，`hasDerivAt_pow` 存在；
3. **`convert … using 1` 之后剩下的是【线性映射之间的等式】**，
   而 `ext z` 之后 `z` 就被消费了——**所以最后一步不能写 `show … z …`，要用 `simp [smul_eq_mul]`**。
   **`continuousLinearMap_one_apply` 这个名字不存在。**
-/

namespace Lattice.Core

/-- **`smulRight 1 k` 就是 `k • id`**——两条等价写法之间的桥。

**`ext z` 之后逐点目标化为 `1 1 • (z * k) = (z * k) • 1`，
而 `simp [smul_eq_mul]` 一次收掉**（`ring`／`ring_nf` 在这里不动，因为它们不展开 `1 1`）。 -/
theorem smulRight_one_eq_smul (k : ℝ) :
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) k = k • ContinuousLinearMap.id ℝ ℝ := by
  ext z
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  simp [smul_eq_mul]

/-- ⭐ **`y ↦ y²` 在 `y` 处的导数是 `(2y) • id`**。

**先由 `hasDerivAt_pow` 得 `HasDerivAt`，再转 `HasFDerivAt`，
然后用 `smulRight_one_eq_smul` 把 `smulRight 1 (2y)` 换成 `(2y) • id`。** -/
theorem hasFDerivAt_sq (y : ℝ) :
    HasFDerivAt (fun t : ℝ => t ^ 2) ((2 * y) • ContinuousLinearMap.id ℝ ℝ) y := by
  have hd : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y)
  have h := hd.hasFDerivAt
  rw [smulRight_one_eq_smul] at h
  exact h

/-- ⭐⭐⭐ **平方的链式法则（任意赋范空间）**：若 `f` 在 `p` 处有导数 `f'`，
则 `fun x => f x ^ 2` 在 `p` 处的导数是 `(2 * f p) • f'`。

**这是 `Lattice.Geo` 侧所有「……的平方」分支的统一工具**：
`penaltyLoss` 的 `eqZero`、三支 `max`、`sqDistEq`、`equalLength`、`perpendicular`、`rightAngle` 都是这个形状，
**所以每条分支只需给出【内层】的导数，平方这一层由本条处理。**

**⚠ 与 `hasFDerivAt_sq` 的区别**：那条是 `E = ℝ` 的特例（`fun t : ℝ => t ^ 2`），
本条对任意 `NormedAddCommGroup`／`NormedSpace ℝ` 成立。**`hasFDerivAt_sq` 保留是因为它给出
`(2y) • id` 这个具体形式，而本条给出 `(2 * f p) • f'`。** -/
theorem hasFDerivAt_sq_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {p : E} (hf : HasFDerivAt f f' p) :
    HasFDerivAt (fun x => f x ^ 2) ((2 * f p) • f') p := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * (f p)) (f p) := by
    simpa using (hasDerivAt_pow 2 (f p))
  have h3 := h1.hasFDerivAt.comp p hf
  convert h3 using 1
  ext d
  simp [mul_comm]

end Lattice.Core
