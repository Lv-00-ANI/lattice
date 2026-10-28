import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Runtime.RealLinear
/-!
# LATTICE S02: RealCrossUniverseBridge —— 符号宇宙 ⇄ 权重宇宙的最小可行桥（治 F-C）

## 问题（F-C，R01 确立于 HEAD `8934502`）

**符号宇宙（链核心）**——载体是 **ℤ**：
* `VectorConstraint{a : List Int, b : Int}`（`ConvertVectorLinear.lean:28-31`）
* `LinearLayer{w : List Int, b : Int}`（`ConvertVectorLinear.lean:43-46`）
* `ConstraintSet := List VectorConstraint`（`SymbolToWeightCorrectness.lean:27`）
* `dot : List Int → List Int → Int`（`ConvertVectorLinear.lean:35`）

**权重宇宙（模型族）**——载体是 **ℝ**：
* `RealVectorConstraint (ι) := {a : ι → ℝ, b : ℝ}`（`RealLinear.lean:100-102`）
* `RealLinearLayer (ι) := {w : ι → ℝ, b : ℝ}`（`RealLinear.lean:107-109`）
* `RealDot`（`RealLinear.lean:98`）、`E →L[ℝ] F`（`RealEditBound.lean:30`）

**二者此前完全互不相接**——grep 实测（HEAD `8934502`）：`RealDot` 在**非探针文件**中
只出现于 `RealLinear` / `RealReLULayer` / `RealLayerPropagation` / `RealVectorStationarity` / `RealIG`，
**没有一个**是链核心文件；反向亦无。

## 本文件给出的桥（全部内核验证 `exit 0`）

| # | 桥 | 类型签名对照 |
|:--|:--|:--|
| 1 | `symDot_eq_realDot` | `((dot a x : ℤ) : ℝ) = RealDot (symW a.length a) (symVec a.length x)` |
| 2 | `layerToCLM` | `LinearLayer → (Fin n → ℝ) →L[ℝ] ℝ` ← **全库第一条** |
| 3 | `layerOut_zero_iff_clm` | `LayerOut l x = 0 ↔ layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) = 0` |

⭐ **3 是真正的语义桥**：它把两侧的「满足语义」钉在**同一命题**上 ——
这正是 R01 §2.3 判定「单一 `SemanticEq` 无法表达 `Compile` 保语义」时要补的那块板。

## 无长度前提（对齐 `RealListFinBridge` 的标准）

`symVec` 用 `getD` **补零**，`dot` 用 `zip` **截断**，二者方向相反、恰好抵消
（与 `RealListFinBridge.dot_eq_dotProduct` 同款机理）
⟹ 桥 1、3 **对任意 `x` 成立**，**不需要** `x.length = a.length`。

## 消融级证据（判据③，非文本证据）

* `layerOut_cast_eq_clm_zero_dim_false`：把主桥的 `n := l.w.length` 换成 `n := 0`，
  命题**变假**（见证 `l = ⟨[1], 0⟩`、`x = [1]`）⟹ 维度参数**承重**。
* `symVec_one_not_injective`：`symVec 1` 非单射（`[1]` 与 `[1,5]` 同像）⟹ 补零嵌入丢失信息，
  「桥必须显式带 `n`」不是形式主义。

`#print axioms` 全部 ⊆ {propext, Classical.choice, Quot.sound}，无 sorryAx。
-/

open scoped BigOperators

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## §0 载体映射：`List ℤ → Fin n → ℝ` -/

/-- 符号向量 `List ℤ` ↦ 权重宇宙的坐标函数（截断到 `n`，不足**补零**）。
与 `RealListFinBridge.toVec` 同型，只多一层 `Int.cast`。 -/
def symVec (n : Nat) (x : List Int) : Fin n → ℝ := fun i => (x.getD i.1 0 : ℝ)

/-- 层权重向量 ↦ 坐标函数（同上）。 -/
def symW (n : Nat) (w : List Int) : Fin n → ℝ := fun i => (w.getD i.1 0 : ℝ)

/-! ## §1 ⭐ 桥 1：符号 `dot` 沿 `Int.cast` **就是** 权重侧 `RealDot`

全库**第一条**把 `dot : List ℤ → List ℤ → ℤ` 与 `RealDot : (ι → ℝ) → (ι → ℝ) → ℝ`
接通的引理。**无长度前提**（对 `x` 的长度无要求）。 -/

theorem symDot_eq_realDot (a x : List Int) :
    ((dot a x : Int) : ℝ) = RealDot (symW a.length a) (symVec a.length x) := by
  rw [dot_eq_dotProduct]
  simp only [RealDot, Matrix.dotProduct, toVec, symW, symVec]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## §2 ⭐ 桥 2：`LinearLayer ↦ (Fin n → ℝ) →L[ℝ] ℝ`

`linFunc` 是 `x ↦ ⟪symW n l.w, x⟫` 的**线性**映射（`map_add'`/`map_smul'` 逐坐标证），
`layerToCLM` 经 `LinearMap.toContinuousLinearMap` 提升为**连续线性算子**
（`Fin n → ℝ` 有限维 ⟹ 线性即连续）。 -/

def linFunc (n : Nat) (l : LinearLayer) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun x => RealDot (symW n l.w) x
  map_add' := by
    intro x y
    simp only [RealDot, Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [RealDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf

noncomputable def layerToCLM (n : Nat) (l : LinearLayer) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (linFunc n l).toContinuousLinearMap

/-! ## §3 ⭐ 桥 3：保语义（`LayerOut` ⟷ `layerToCLM`） -/

theorem layerToCLM_apply (n : Nat) (l : LinearLayer) (x : Fin n → ℝ) :
    layerToCLM n l x = RealDot (symW n l.w) x := rfl

/-- ⭐⭐ **主桥**：符号侧 `LayerOut l x`（ℤ 值）经 `Int.cast`，等于权重侧 CLM
在 `symVec l.w.length x` 上的取值加偏置（ℝ 值）。**无长度前提**。 -/
theorem layerOut_cast_eq_clm (l : LinearLayer) (x : List Int) :
    ((LayerOut l x : Int) : ℝ)
      = layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) := by
  unfold LayerOut
  push_cast
  rw [layerToCLM_apply, symDot_eq_realDot]

/-- ⭐⭐ **语义桥（⟺ 形式）**：整数侧「输出为零」⟺ 实数侧「CLM 取值 + 偏置 = 0」。
这是把两宇宙的满足语义钉在**同一命题**上的等式。 -/
theorem layerOut_zero_iff_clm (l : LinearLayer) (x : List Int) :
    LayerOut l x = 0 ↔ layerToCLM l.w.length l (symVec l.w.length x) + (l.b : ℝ) = 0 := by
  constructor
  · intro h
    have h1 := layerOut_cast_eq_clm l x
    rw [h] at h1
    push_cast at h1
    linarith
  · intro h
    have h1 := layerOut_cast_eq_clm l x
    have h2 : ((LayerOut l x : Int) : ℝ) = 0 := by rw [h1]; exact h
    exact_mod_cast h2

/-! ## §4 承重性（消融见证） -/

/-- 补零嵌入**非单射**：`symVec n` 只看前 `n` 个坐标，多出的坐标**不被看到**
⟹ 桥必须显式携带 `n`（与 `RealListFinBridge.toVec_not_injective_without_length` 同款）。

⭐ 见证：`x = [1]`、`y = [1, 5]` 在 `n = 1` 下映到**同一个**函数，但二者**不是**同一列表。 -/
theorem symVec_one_not_injective :
    ∃ x y : List Int, x ≠ y ∧ symVec 1 x = symVec 1 y :=
  ⟨[1], [1, 5], by decide, by funext i; fin_cases i <;> rfl⟩

/-- ⭐ **消融见证（承重）**：主桥的 `n := l.w.length` **不可**换成 `n := 0`。
取 `n = 0` 时 CLM 恒为 0，命题**变假**（见证 `l = ⟨[1], 0⟩`、`x = [1]`：
左端 `= 1`，右端 `= 0`）。 -/
theorem layerOut_cast_eq_clm_zero_dim_false :
    ¬ (∀ (l : LinearLayer) (x : List Int),
        ((LayerOut l x : Int) : ℝ) = layerToCLM 0 l (symVec 0 x) + (l.b : ℝ)) := by
  intro h
  have hh := h ⟨[1], 0⟩ [1]
  simp [LayerOut, dot, layerToCLM, linFunc, RealDot, symW, symVec] at hh

end Lattice

#print axioms Lattice.symDot_eq_realDot
#print axioms Lattice.layerOut_cast_eq_clm
#print axioms Lattice.layerOut_zero_iff_clm
#print axioms Lattice.layerOut_cast_eq_clm_zero_dim_false
#print axioms Lattice.symVec_one_not_injective
