/-
# 非退化性的实例：`Nondegenerate` 并非空洞

## 0. 本节补什么

第 114 轮盘查发现 `Geo/Nondegenerate.lean` 定义了两个谓词：

```
Nondegenerate a b v         :=  ∃ i : Fin n, seg a b i v ≠ 0
PerpNondegenerate a b c e v :=  Nondegenerate a b v ∧ Nondegenerate c e v
```

**`PerpNondegenerate` 只出现在它自己的定义文件里（1 个文件），
`Nondegenerate` 只在 import 与定义处出现。**

⇒ **两者都没有实例，也没有在定义文件之外被消费。** 与第 103 轮的 `DeltaDense` 同形态。

第 114 轮尝试补实例失败（`bump` 的应用形状没接对），删除了文件。

## 1. 第 115 轮：先把签名查清

第 114 轮失败的根因是**猜签名**。本轮先 `#check`：

```
bump         : (k n : ℕ) → Fin k → Fin n → Fin (k * n) → ℝ
seg_bump_far : seg a b i (v + t • bump k n b i) = seg a b i v + t      -- b ≠ a
```

**关键**：`seg_bump_far` 的自变量是 `v + t • bump k n b i`，**不是裸的 `bump`**。

⇒ 取 `v := 0`、`t := 1`，则 `0 + 1 • bump = bump`，需要一条 `funext`。

**这就是第 114 轮卡住的地方**：`funext` 之后 `simp` 没有把 `0 + 1 • x` 化成 `x`。
本轮**先把那条等式单独立成引理**（`zero_add_one_smul`）。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `zero_add_one_smul` | **`0 + 1 • v = v`**（第 114 轮卡住的那一步） |
| **`nondegenerate_of_bump`** | **单位脉冲使 `Nondegenerate` 成立** |
| **`nondegenerate_exists`** | **存在满足的配置** |
| **`perpNondegenerate_exists`** | **存在满足 `PerpNondegenerate` 的配置** |
| `nondegenerate_not_vacuous` | **存在不满足的配置**（区分力） |

## 3. 边界

- 本节**不改**定义，只补实例。
- **存在性与非恒真同等重要**：只证"存在满足的"说明不了谓词有内容，
  还要证"存在不满足的"。
- `k ≥ 2`、`n ≥ 1` 是存在性定理的前提（需要两个不同的点与一个坐标）。
- 本节**不接** `perp_gradient_nonzero` 的前提（那是连接层面的事）。
-/
import Mathlib
import Lattice.Domains.Perturb
import Lattice.Domains.Nondegenerate

open scoped BigOperators

namespace Lattice.Geo

namespace NondegenerateInstance

variable {k n : ℕ}

/-! ## 一、第 114 轮卡住的那一步 -/

/-- **`0 + 1 • v = v`**：第 114 轮在 `funext` 之后没能化简的一步。

单独立成引理，因为它是实例构造的**唯一**技术障碍。 -/
theorem zero_add_one_smul (v : Fin (k * n) → ℝ) :
    (fun _ => (0 : ℝ)) + (1 : ℝ) • v = v := by
  funext j
  simp

/-! ## 二、单位脉冲给出非退化 -/

/-- **单位脉冲使 `Nondegenerate` 成立**（当 `b ≠ a`）。

由 `seg_bump_far` 取 `v := 0`、`t := 1`：`seg a b i (bump k n b i) = 0 + 1 ≠ 0`。 -/
theorem nondegenerate_of_bump (a b : Fin k) (i : Fin n) (hba : b ≠ a) :
    Nondegenerate a b (bump k n b i) := by
  refine ⟨i, ?_⟩
  have h := seg_bump_far (k := k) (n := n) a b i 1 (fun _ => (0 : ℝ)) hba
  have hzero : seg (n := n) a b i (fun _ => (0 : ℝ)) = 0 := by
    unfold seg unflatten
    simp
  have hv : (fun _ => (0 : ℝ)) + (1 : ℝ) • (bump k n b i) = bump k n b i :=
    zero_add_one_smul (k := k) (n := n) (bump k n b i)
  rw [← hv, h, hzero]
  norm_num

/-! ## 三、存在性 -/

/-- **存在满足 `Nondegenerate` 的配置**（需要两个不同的点与一个坐标）。 -/
theorem nondegenerate_exists (hk : 1 < k) (hkn : 0 < n) :
    ∃ (a b : Fin k) (v : Fin (k * n) → ℝ), Nondegenerate a b v := by
  have h0 : 0 < k := Nat.lt_trans Nat.zero_lt_one hk
  refine ⟨⟨0, h0⟩, ⟨1, hk⟩, bump k n ⟨1, hk⟩ ⟨0, hkn⟩, ?_⟩
  exact nondegenerate_of_bump (n := n) ⟨0, h0⟩ ⟨1, hk⟩ ⟨0, hkn⟩ (by simp)

/-- **存在满足 `PerpNondegenerate` 的配置。**

**本节是这个谓词第一次被满足**——第 114 轮发现它只出现在定义文件里。 -/
theorem perpNondegenerate_exists (hk : 1 < k) (hkn : 0 < n) :
    ∃ (a b c e : Fin k) (v : Fin (k * n) → ℝ), PerpNondegenerate a b c e v := by
  have h0 : 0 < k := Nat.lt_trans Nat.zero_lt_one hk
  refine ⟨⟨0, h0⟩, ⟨1, hk⟩, ⟨0, h0⟩, ⟨1, hk⟩, bump k n ⟨1, hk⟩ ⟨0, hkn⟩, ?_, ?_⟩
  · exact nondegenerate_of_bump (n := n) ⟨0, h0⟩ ⟨1, hk⟩ ⟨0, hkn⟩ (by simp)
  · exact nondegenerate_of_bump (n := n) ⟨0, h0⟩ ⟨1, hk⟩ ⟨0, hkn⟩ (by simp)

/-! ## 四、区分力 -/

/-- **存在不满足 `Nondegenerate` 的配置**：全零配置的每一段都退化为点。

⇒ **`Nondegenerate` 不是恒真的谓词**——它在区分。 -/
theorem nondegenerate_not_vacuous (a b : Fin k) :
    ¬ Nondegenerate (n := n) a b (fun _ => (0 : ℝ)) := by
  rintro ⟨j, hj⟩
  unfold seg unflatten at hj
  simp at hj

/-- **结论**：`Nondegenerate` 与 `PerpNondegenerate` 都有实例，且都不是恒真。

| 谓词 | 有实例 | 非恒真 |
|:--|:--:|:--:|
| `Nondegenerate` | ✅ `nondegenerate_exists` | ✅ `nondegenerate_not_vacuous` |
| `PerpNondegenerate` | ✅ `perpNondegenerate_exists` | （由 `Nondegenerate` 推出） |

**这补上了第 114 轮盘查发现的「定义无见证」缺口。** -/
theorem nondegenerate_has_content (hk : 1 < k) (hkn : 0 < n)
    (a b : Fin k) (i : Fin n) (hba : b ≠ a) :
    (∃ (a' b' : Fin k) (v : Fin (k * n) → ℝ), Nondegenerate a' b' v) ∧
    Nondegenerate a b (bump k n b i) ∧
    ¬ Nondegenerate (n := n) a b (fun _ => (0 : ℝ)) :=
  ⟨nondegenerate_exists hk hkn,
   nondegenerate_of_bump a b i hba,
   nondegenerate_not_vacuous a b⟩

end NondegenerateInstance

end Lattice.Geo
