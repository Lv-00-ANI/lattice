/-
# 整层量化的**真实实例**：`LossyRep` 从一维提升到层

## 0. 为什么需要这一节

「逆向」侧此前只有一个**标量**的有损实例：`RoundingBackend.roundingLossy : LossyRep ℤ ℤ`，
即 `x ↦ x/2` 再乘回 2，误差 ≤ 1。

**在 LLM 里量化不是标量的事**：它作用在**整个张量**上（逐层、逐通道、逐元素）。
所以「量化」在库里此前**不是一个层的性质**，只是一个数的性质。

本节把那个标量结果**逐分量提升**到整层。**证明没有独立内容**——它叫三次
`roundtrip_error_le_one`。这就是「定理级复用」的实质：整层量化的正确性**就是**
一维结果在每个分量上成立，而不是另一套理论。

## 1. 模型

```lean
abbrev IntLayer (m n : ℕ) := (Fin m → Fin n → ℤ) × (Fin n → ℤ)

quant   L := (fun i j => L.1 i j / 2, fun j => L.2 j / 2)     -- 丢最低位
dequant L := (fun i j => 2 * L.1 i j, fun j => 2 * L.2 j)     -- 乘回
obsEntrywise p q := (∀ i j, |p.1 i j - q.1 i j| ≤ 1) ∧ (∀ j, |p.2 j - q.2 j| ≤ 1)
```

**为什么用 `ℤ` 而不是 `ℝ`**：`ℝ` 上 `x/2 * 2 = x` **精确**，那就不是量化了。
量化的本质是**丢低位**，而丢低位只在离散网格上发生。

**为什么 `obs` 是逐分量而不是范数**：范数界会把一个坏分量藏在一堆好分量后面，
而量化器的失效模式恰恰是**某一个**分量舍入错或饱和。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| `IntLayer` | 整数层：权重矩阵 + 偏置向量 |
| `quant` / `dequant` | 丢低位 / 乘回 |
| `obsEntrywise` | 逐分量误差 ≤ 1 |
| `obsEntrywise_refl` | 该口径自反（`LossyRep` 要求） |
| `dequant_quant_error` | **每个分量误差 ≤ 1**（复用一维结果） |
| **`layerQuantization`** | **`LossyRep (IntLayer m n) (IntLayer m n)` 的真实实例** |
| `layerQuantization_nontrivial` | 它真的丢信息（存在两点观测等价但不相等） |
| `layerQuantization_refines_scalar` | `m = n = 1` 时与标量版一致 |

## 3. 边界

- **`2` 只是参数**：换成 `2 ^ bits` 只需把 `roundtrip_error_le_one` 换成对应位宽的版本；
  本节用 `2` 是因为库里已有那条定理。**推广留作接口**，不在这里发明一组新引理。
- **`obsEntrywise` 只界住单分量误差**，不界住**层的作用**（即 `affineAct` 的输出误差）。
  后者需要 Lipschitz 常数与输入范数，属 `RealFloatSharpBridge` 一类的工作，
  **本节不声称**它能由逐分量界直接得到。
- **不支持饱和（clipping）**：真实量化器会把值截到 `[-2^b, 2^b)`，那时误差界不再成立，
  而**这正是量化失真的主要来源**。本节只证「丢低位」这一种，且明确说明。
- 本节**不改** `RoundingBackend`、`LossyRepresentation` 的任何既有定理。
-/
import Mathlib
import Lattice.Runtime.LossyRepresentation
import Lattice.Runtime.RoundingBackend

namespace Lattice.Lift.IntQuant

open Lattice.Lift.LossyRepresentation

variable {m n : ℕ}

/-- **整数层**：权重矩阵与偏置向量都是 `ℤ`。

真实部署把权重量化到定点网格；「丢低位」的诚实抽象就是整数带余除法，
而 `RoundingBackend.roundingLossy` 已经在一维上证明了它。 -/
abbrev IntLayer (m n : ℕ) := (Fin m → Fin n → ℤ) × (Fin n → ℤ)

/-- **量化**：每个分量除以 2（丢最低位）。 -/
def quant : IntLayer m n → IntLayer m n :=
  fun L => (fun i j => L.1 i j / 2, fun j => L.2 j / 2)

/-- **反量化**：乘回 2。 -/
def dequant : IntLayer m n → IntLayer m n :=
  fun L => (fun i j => 2 * L.1 i j, fun j => 2 * L.2 j)

/-- **观察口径**：每个分量误差 ≤ 1。

**逐分量而非范数**：范数界会把一个坏分量藏在一堆好分量后面，而量化器的失效模式
恰恰是**某一个**分量饱和或舍入错。 -/
def obsEntrywise (p q : IntLayer m n) : Prop :=
  (∀ i j, |p.1 i j - q.1 i j| ≤ 1) ∧ (∀ j, |p.2 j - q.2 j| ≤ 1)

/-- 该口径自反（`LossyRep.obs_refl` 要求的）。 -/
theorem obsEntrywise_refl (p : IntLayer m n) : obsEntrywise p p := by
  refine ⟨?_, ?_⟩
  · intro i j; simp
  · intro j; simp

/-- **每个分量的误差不超过 1**——**直接复用一维的 `roundtrip_error_le_one`**，不重新证一遍。

这是「定理级复用」的实质：整层量化的正确性没有独立内容，它就是一维结果在每个分量上成立。 -/
theorem dequant_quant_error (L : IntLayer m n) : obsEntrywise (dequant (quant L)) L := by
  refine ⟨?_, ?_⟩
  · intro i j
    exact Lattice.Lift.RoundingBackend.roundtrip_error_le_one (L.1 i j)
  · intro j
    exact Lattice.Lift.RoundingBackend.roundtrip_error_le_one (L.2 j)

/-- **整层量化的 `LossyRep` 实例**：编译是 `quant`，提取是 `dequant`，口径是逐分量误差 ≤ 1。

`semEq` 就是 `dequant_quant_error`——**没有新证明**。 -/
noncomputable def layerQuantization : LossyRep (IntLayer m n) (IntLayer m n) where
  inputP := Fin n → ℤ
  inputW := Fin n → ℤ
  encode := id
  decode := id
  compile := quant
  extract := dequant
  obs := obsEntrywise
  obs_refl := obsEntrywise_refl
  semEq := dequant_quant_error

/-- **这个实例的往返义务是逐分量成立的**：展开形式，供引用。 -/
theorem layerQuantization_roundtrip (L : IntLayer m n) :
    obsEntrywise (dequant (quant L)) L :=
  layerQuantization.semEq L

/-- **它真的丢信息**：存在两个不同的层在观测口径下等价。

取同一层的所有分量都在 `0` 与 `1` 之间的对比——两个相邻整数除以 2 后相同，
乘回 2 后也相同，所以**提取无法区分它们**。这就是「有损」的见证。 -/
theorem layerQuantization_nontrivial :
    ∃ p q : IntLayer 1 1, p ≠ q ∧ obsEntrywise (dequant (quant p)) (dequant (quant q)) := by
  refine ⟨(fun _ _ => 0, fun _ => 0), (fun _ _ => 1, fun _ => 1), ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun L : IntLayer 1 1 => L.1 0 0) h
    simp at h1
  · refine ⟨?_, ?_⟩
    · intro i j
      show |2 * ((fun _ _ => 0 : Fin 1 → Fin 1 → ℤ) i j / 2) -
            2 * ((fun _ _ => 1 : Fin 1 → Fin 1 → ℤ) i j / 2)| ≤ 1
      simp
    · intro j
      show |2 * ((fun _ => (0 : ℤ)) j / 2) - 2 * ((fun _ => (1 : ℤ)) j / 2)| ≤ 1
      simp

/-- **`m = n = 1` 时与标量版一致**：本节的 `quant` 在单分量上就是 `RoundingBackend.compileZ`。

这是「提升而非重写」的机器检查形式。 -/
theorem layerQuantization_refines_scalar (x : ℤ) :
    (quant (m := 1) (n := 1) (fun _ _ => x, fun _ => x)).1 0 0 =
      Lattice.Lift.RoundingBackend.compileZ x :=
  rfl

end Lattice.Lift.IntQuant
