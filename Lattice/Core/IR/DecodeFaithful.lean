import Mathlib
import Lattice.Core.IR.Decode

/-!
# **P1-8 的反方向被**证否**：现有解码器不忠实**（阶段 N）

## 审计要求的反方向，与它的真实状态

**审计的 P1-8 要求 `decode : ℕ → Option IRSkeleton`，对**不是**任何骨架的码返回 `none`。**

**第 972 轮查明：`decodeSkeleton` 与它的辅助解码器**早已存在**，
且 `decodeTensorShape_code`（码能解回张量）已证。**

**=> 但那只是**正向**。反方向是：**

```
decodeTensorShape n = some t  →  tensorShapeCode t = n        （忠实性）
```

**若它成立，「像外返 `none`」自动成立。**

## 本文件把这个反方向**证否**

**结构观察，不需要任何算术：**

| 事实 | 内容 |
|:--|:--|
| **编码的形状** | **`tensorShapeCode t = Nat.pair (… + 1) 0`，其**第二分量恒为 `0`** |
| **解码的检查** | **`decodeTensorShape` 只看 `code ≠ 0` 与 `(unpair code).1 ≠ 0`，**完全不检查第二分量** |

**=> 于是取 `n = Nat.pair 1 1`（第二分量 = `1` ≠ `0`），它**不是**码，但解码返回 `some`。**

**=> 由 `Nat.pair_eq_pair`，若 `tensorShapeCode t = Nat.pair 1 1` 则 `0 = 1`，矛盾。**

## 这个否证为什么重要

**它纠正了第 972 轮我的判断「P1-8 已交付」。**
**=> 事实上：**正向已交付，反向被证否**——现有解码器是**宽松**的（lenient），
它把一批非码也解成 `some`。**

**=> 所以 O-2 的真正内容不是「跑一遍迁移」，而是：
**要么把解码器改严（需要判定「一个 `ℕ` 是否由 `pair (…+1) 0` 构成」，可做），
要么承认规格只能由非可计算解码器满足（第 972 轮被我误删的 `Classical.choose` 方案）。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`decodeTensorShape_lenient`** | **⭐⭐ 第一分量非零即返回 `some`** |
| **`decodeTensorShape_not_faithful`** | **⭐⭐⭐ 忠实性**被证否**（本文件的核心）** | -/

namespace Lattice.Core.IR

/-- **⭐⭐ **宽松性**：只要第一分量非零，`decodeTensorShape (pair a b)` 就返回 `some`。**

**=> 它对 `b` **不做任何检查**，而编码的第二分量恒为 `0`。
这就是不忠实的根源。** -/
theorem decodeTensorShape_lenient (a b : ℕ) (ha : a ≠ 0) :
    ∃ t : TensorShape, decodeTensorShape (Nat.pair a b) = some t := by
  have hne : Nat.pair a b ≠ 0 := by
    have hle := Nat.left_le_pair a b
    omega
  unfold decodeTensorShape
  rw [if_neg hne]
  have hu : Nat.unpair (Nat.pair a b) = (a, b) := Nat.unpair_pair a b
  simp only [hu]
  rw [if_neg ha]
  exact ⟨_, rfl⟩

/-- **⭐⭐⭐ 忠实性**被证否**。

**=> 存在一个 `n`（取 `Nat.pair 1 1`）与一个 `t`，使 `decodeTensorShape n = some t`
但 `tensorShapeCode t ≠ n`。**

**=> 因此审计 P1-8 的「像外返 `none`」**对现有解码器不成立**。** -/
theorem decodeTensorShape_not_faithful :
    ¬ (∀ (n : ℕ) (t : TensorShape), decodeTensorShape n = some t → tensorShapeCode t = n) := by
  intro hf
  obtain ⟨t, ht⟩ := decodeTensorShape_lenient 1 1 (by norm_num)
  have hcode : tensorShapeCode t = Nat.pair 1 1 := hf (Nat.pair 1 1) t ht
  obtain ⟨tid, shape⟩ := t
  simp only [tensorShapeCode] at hcode
  obtain ⟨-, h2⟩ := Nat.pair_eq_pair.mp hcode
  exact absurd h2 (by norm_num)

end Lattice.Core.IR
