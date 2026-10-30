import Mathlib

/-!
# `Lattice.Lib.Penalty.BilinearLocallyLipschitz` — **双线性项的扰动界**

## 为什么单独一个文件

`Domains/Constraints/PenaltyLoss.lean` 里 `collinear` 与 `parallel` 两个分支走 `minorDefect`：

```lean
noncomputable def minorDefect (u v : Pt n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (u i * v j - u j * v i) ^ 2
```

**每一项都是一个双线性形式 `uᵢ · vⱼ − uⱼ · vᵢ` 的平方。** 而同文件里其他 10 个分支都是
**(线性形式)²**，由 `Lib/Penalty/QuadraticLocallyLipschitz` 的 `sq_lipschitz_on_bounded` 直接处理。

⇒ **本文件补上双线性那一层**：先把「双线性项在两端扰动下变化多少」证出一条通用的界，
再把它套上平方。**两条都是纯代数，不依赖几何载体。**

## 与 `PolyLipschitz.bilinearSum_lipschitz` 的区别

`Domains/Geometry/PolyLipschitz` 已有一条 `bilinearSum_lipschitz`，但它的陈述绑在几何载体上：

```lean
|(∑ i, (pts b i - pts a i) * (pts e i - pts c i))
  - (∑ i, (pts' b i - pts' a i) * (pts' e i - pts' c i))| ≤ (8 * n * B) * rho n k pts pts'
```

**它要求 `pts : ℕ → Pt n`、前缀界 `k`、以及 `rho` 这个特定度量。**
而 `minorDefect` 需要的是**任意两个向量 `u v : Pt n`** 的版本。

**两者的证明是同一个插项**：

```
u i * v j - u' i * v' j = u i * (v j - v' j) + (u i - u' i) * v' j
```

**所以本文件给出它能推广到的那条**，`PolyLipschitz` 那条保持原样（它的下游是 `EqConstraint.poly`）。
**这不是重复，是把同一恒等式放在更低的层、更一般的陈述上**——**而 `PolyLipschitz` 那条本可以由本文件推出来，
只是那会破坏它现有的 `rho` 接口。** **这一点写在 `PolyLipschitz` 的 TODO 里更合适，本轮不做。**
-/

namespace Lattice.Lib.Penalty

/-- ⭐ **双线性项的扰动界**：`|a·b − a'·b'| ≤ |a|·|b − b'| + |a − a'|·|b'|`。

这是**插项恒等式** `a·b − a'·b' = a·(b − b') + (a − a')·b'` 的直接推论，
**两端各带一个界**（`Ma` 界 `|a|`、`Mb` 界 `|b'|`），**这正是「双线性比线性多一倍」的地方**：
线性项只需一端有界，双线性项两端都要。

⚠ **`Ma` 与 `Mb` 交叉**：`Ma` 配 `δb`、`Mb` 配 `δa`。**写反了界仍然成立但更松，而松的界会一路传下去。** -/
theorem bilinear_sub_le {a a' b b' Ma Mb δa δb : ℝ}
    (hMa : |a| ≤ Ma) (hMb : |b'| ≤ Mb)
    (hδa : |a - a'| ≤ δa) (hδb : |b - b'| ≤ δb) :
    |a * b - a' * b'| ≤ Ma * δb + Mb * δa := by
  have hfac : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  have h3 : |a| * |b - b'| ≤ Ma * δb :=
    mul_le_mul hMa hδb (abs_nonneg _) (le_trans (abs_nonneg a) hMa)
  have h4 : |a - a'| * |b'| ≤ δa * Mb :=
    mul_le_mul hδa hMb (abs_nonneg _) (le_trans (abs_nonneg (a - a')) hδa)
  calc |a * b - a' * b'|
      = |a * (b - b') + (a - a') * b'| := by rw [hfac]
    _ ≤ |a * (b - b')| + |(a - a') * b'| := abs_add _ _
    _ = |a| * |b - b'| + |a - a'| * |b'| := by rw [abs_mul, abs_mul]
    _ ≤ Ma * δb + δa * Mb := add_le_add h3 h4
    _ = Ma * δb + Mb * δa := by ring

theorem bilinear_sq_sub_le {a a' b b' Ma Mb δa δb R : ℝ}
    (hMa : |a| ≤ Ma) (hMb : |b'| ≤ Mb)
    (hδa : |a - a'| ≤ δa) (hδb : |b - b'| ≤ δb)
    (hP : |a * b| ≤ R) (hQ : |a' * b'| ≤ R) :
    |(a * b) ^ 2 - (a' * b') ^ 2| ≤ 2 * R * (Ma * δb + Mb * δa) := by
  have hdiff := bilinear_sub_le hMa hMb hδa hδb
  have hfac : (a * b) ^ 2 - (a' * b') ^ 2 = (a * b - a' * b') * (a * b + a' * b') := by ring
  have hsum : |a * b + a' * b'| ≤ 2 * R := by
    calc |a * b + a' * b'| ≤ |a * b| + |a' * b'| := abs_add _ _
      _ ≤ R + R := add_le_add hP hQ
      _ = 2 * R := by ring
  have hMa0 : 0 ≤ Ma := le_trans (abs_nonneg a) hMa
  have hMb0 : 0 ≤ Mb := le_trans (abs_nonneg b') hMb
  have hδa0 : 0 ≤ δa := le_trans (abs_nonneg (a - a')) hδa
  have hδb0 : 0 ≤ δb := le_trans (abs_nonneg (b - b')) hδb
  have hR0 : 0 ≤ 2 * R := by
    have := abs_nonneg (a * b)
    linarith
  calc |(a * b) ^ 2 - (a' * b') ^ 2|
      = |(a * b - a' * b') * (a * b + a' * b')| := by rw [hfac]
    _ = |a * b - a' * b'| * |a * b + a' * b'| := abs_mul _ _
    _ ≤ (Ma * δb + Mb * δa) * (2 * R) :=
        mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = 2 * R * (Ma * δb + Mb * δa) := by ring

end Lattice.Lib.Penalty
