import Mathlib
import Lattice.Lib.Architectures.RealNormSharpConstant
import Lattice.Lib.Architectures.RealNormLipschitz
import Lattice.Lib.Architectures.RealRMSNorm
import Lattice.Lib.Architectures.RealRMSNormSharpness
/-!
# LATTICE: RMSNorm 的 Lipschitz 界 —— 从 `EuclideanSpace ℝ (Fin n)` **推广**到**任意实内积空间**

## 推广了什么（精确陈述对比）

**原定理**（`RealRMSNormSharpness.lean:94`，`rmsNormE` 专用版）：
```
theorem rmsNormE_sqrt_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖rmsNormE x - rmsNormE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖
```
**新定理**（`rmsNormGeneral_lipschitz`，任意实内积空间 + 自由尺度）：
```
theorem rmsNormGeneral_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) (x y : E) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖rmsNormGeneral a x - rmsNormGeneral a y‖ ≤ (a / c) * ‖x - y‖
```

## 关键判断：`√n` 的**真实角色**（本推广的核心）

`RealNormSharpConstant.lean:165-166` 的定义体是
`rmsNormE x = (Real.sqrt n) • ((1 / ‖x‖) • x)` ——
**`√n` 是 `rmsNormE` 自己的一个显式标量因子**，**不是**从任何内积恒等式推导出来的、
也**不是**"内积空间的维数"这一范畴论量（真正的维数 `finrank` 在定义体里根本没出现）。

⇒ 因此 `√n` **不是本质障碍**：推广的正确做法不是"显式传入维数尺度"，而是把那个标量
**抽象成自由参数 `a : ℝ`**，即研究一般实内积空间上的映射 `x ↦ a • (x/‖x‖)`；原 `rmsNormE`
就是 `a := √n` 的那一个特例。`√n` 在此**只是常数的取值**，不是结构的一部分。

⇒ 顺带说明：**一般内积空间没有 `Fin n` 坐标、"维数"可以是无穷**，所以任何"传入 `N : ℝ` 当维数"
的写法都会引入一个**与空间结构无关的外来参数**；把它写成自由参数 `a` 才是诚实的推广
（`a` 可以是任何实数，不需要"是一个维数的平方根"）。

## 定理清单

1. `rmsNormGeneral`（定义）：一般实内积空间上的尺度化单位化映射 `x ↦ a • (x/‖x‖)`。
2. `rmsNormGeneral_lipschitz`（**核心推广**）：`(a/c)`-Lipschitz（`a ≥ 0`、`‖·‖ ≥ c > 0`）。
3. `rmsNormGeneral_neg` / `rmsNormGeneral_antipodal_norm` / `rmsNormGeneral_sharp_attained`：
   换号性与**对径取等** —— `(a, −a)` 型非零目的空间上常数 `a/c` **可达**（`a ≥ 0`）。
4. `rmsNormGeneral_constant_lower_bound`：任意有效常数 `K ≥ a/c`（由取等点对给出下界），
   与 2 合起来说明 `a/c` 是**真正常数**。
5. `rmsNormGeneral_two_div_not_attained`：`a > 0` 时保守界 `(2a/c)` 在取等点对上**严格**。
6. `rmsNormE_eq_rmsNormGeneral` / `rmsNormGeneral_sqrt_eq_rmsNormE`：`a = √n` 回收 ——
   `rmsNormE = rmsNormGeneral (√n)`（**逐点为 `rfl`**，函数层需 `funext`）。
7. `rmsNormGeneral_recovers_rmsNormE` / `rmsNormGeneral_sharp_recovers_rmsNormE`（**特例回收**）：
   把一般定理**实例化**回 `EuclideanSpace ℝ (Fin n)`、`a := √n`，**逐字**得到原定理
   `rmsNormE_sqrt_lipschitz` 与 `rmsNormE_sharp_attained` 的陈述。
   ⚠ 这两条是**新增的回收定理**，**原文件 `RealRMSNormSharpness.lean` 未被改动一个字**
   （原定理及其原证明体完整保留，见「诚实边界」最后一条）。

## 是否严格更强

**是，严格更强。** 原有的 `rmsNormE_sqrt_lipschitz` 需要：固定 `n : ℕ`、类型恰为
`EuclideanSpace ℝ (Fin n)`、尺度恰为 `√n`（由定义体固定，**不可调**）。
新的 `rmsNormGeneral_lipschitz` 对：**任意**实内积空间 `E`（可为无穷维、可为抽象 Hilbert 空间、
可取 `E = ℝ →₀ ℝ` 的完备化等 `Fin n` 之外的任何对象）、**任意**尺度 `a ≥ 0` 成立。

**具体例子（原定理做不到、新定理做得到）：**
取 `E = ℂ`（视作 `ℝ` 上的二维内积空间，`inner z w = (z * conj w).re`），尺度 `a = 3`，
`c = 1`，`x = 1`，`y = Complex.I`（两者范数均为 1），则 `a = 3` **不是任何自然数维数的平方根**，
且 `E` 并非 `EuclideanSpace ℝ (Fin n)` 的任何 defeq 形式（mathlib 中 `ℂ` 与
`EuclideanSpace ℝ (Fin 2)` 是不同但等距的类型，原定理**无法直接作用于 `ℂ`**）。
新定理直接给出 `‖rmsNormGeneral 3 x − rmsNormGeneral 3 y‖ ≤ 3 * ‖x − y‖`
（且经 `rmsNormGeneral_sharp_pair_exists` 可知界可达，见下）。
更一般地：**任何无穷维实内积空间**上原定理连类型都写不出来。

## 诚实边界

- **未处理**：`E = {0}` 这类"只有零向量"的空间上 `x/‖x‖` 无定义 —— 本文件中所有取等/
  下界定理都**显式要求存在非零向量**（`∃ z : E, z ≠ 0`），**不是被掩盖的 gap**；
  而**上界**定理 `rmsNormGeneral_lipschitz` 在退化空间上为**真空真**（前提 `c ≤ ‖x‖` 与 `c > 0`
  不可能同时满足），这一点已在定理 docstring 中标注。
- **未处理**：`a < 0`。取 `a < 0` 时结论 `≤ (a/c)·‖x−y‖` 的右端为负而左端非负，
  在 `x - y ≠ 0` 时**假**；这是**本质的**，故 `ha : 0 ≤ a` 不可省（docstring 已标注）。
  ⚠ 但 `a = 0` **包含在内**（此时映射是常值 `0`，`0 ≤ 0 * ‖x−y‖` 成立）。
- **未处理**：带仿射项 `γ`/`β` 与 `ε` 的变体（与 `RealRMSNormSharpness` 口径一致：不做）。
- **未处理**：`EuclideanSpace` 的**代数**性质（坐标、`Finset` 和、中心化 `ctr`）**未**推广 ——
  那些依赖 `Fin n` 坐标，本文件只推广**范数/Lipschitz** 层面的结论。
- **本文件不修改 `RealRMSNormSharpness.lean`**：原定理 `rmsNormE_sqrt_lipschitz` 及其原证明体
  **完整保留在原处**（新旧并存，符合库内"常数收紧不删旧版"的先例）。
  第 7 节的回收定理表明原定理是推广版的**推论**，若日后要把原定理证明体改写成
  `exact rmsNormGeneral_recovers_rmsNormE …`，那是**独立的后续动作**，本文件不代为执行。
- 全程无 sorry/axiom/admit/native_decide；未使用 `field_simp` 收尾。
-/

noncomputable section

namespace Lattice

/-! ## 一、定义：一般实内积空间上的尺度化单位化映射 -/

/-- **`rmsNormGeneral a x`**：一般实内积空间 `E` 上的"尺度化单位化"映射
    `x ↦ a • (x / ‖x‖)`（`‖x‖ = 0` 时取 `a • 0 = 0`）。

    · 在 `E = EuclideanSpace ℝ (Fin n)`、`a = √n` 时**逐字**退化为
      `RealNormSharpConstant.rmsNormE`（见 `rmsNormE_eq_rmsNormGeneral`），
      故本定义是 `rmsNormE` 的**推广**而非新对象；
    · `a` 是**自由标量**：`√n` 在原定义里只是一个可替换的常数（见文件头「关键判断」）。 -/
def rmsNormGeneral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (x : E) : E :=
  a • ((1 / ‖x‖) • x)

/-! ## 二、核心推广：`(a/c)`-Lipschitz -/

/-- **`rmsNormGeneral_lipschitz`（核心推广）**：一般实内积空间上，`rmsNormGeneral a` 在
    范数下界 `‖x‖, ‖y‖ ≥ c > 0` 上是 **(a/c)-Lipschitz**。

    这是 `RealRMSNormSharpness.rmsNormE_sqrt_lipschitz` 的**推广**：
    后者要求类型恰为 `EuclideanSpace ℝ (Fin n)` 且尺度恰为 `√n`
    （`√n` 被 `rmsNormE` 的定义体写死），本定理把两者都放开 ——
    **类型**换成任意实内积空间 `E`，**尺度**换成任意 `a ≥ 0`。

    ⚠ `ha : 0 ≤ a` 不可省：`a < 0` 时右端为负而左端非负，结论在 `x ≠ y` 时**假**。
    ⚠ `a = 0` 包含在内（此时映射常值 `0`，界为 `0 ≤ 0`）。
    ⚠ 退化空间 `E = {0}` 上本定理**真空真**（`0 < c ≤ ‖x‖` 不可满足）。 -/
theorem rmsNormGeneral_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) (x y : E) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖rmsNormGeneral a x - rmsNormGeneral a y‖ ≤ (a / c) * ‖x - y‖ := by
  have hdiff : rmsNormGeneral a x - rmsNormGeneral a y
      = a • ((1 / ‖x‖) • x - (1 / ‖y‖) • y) := by
    unfold rmsNormGeneral
    rw [← smul_sub]
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ a * ((1 / c) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (unit_normalize_lipschitz_sharp x y c hc hx hy) ha
    _ = (a / c) * ‖x - y‖ := by ring

/-! ## 三、换号性与对径取等（常数可达） -/

/-- 换号性：`rmsNormGeneral a (−x) = −rmsNormGeneral a x`。 -/
lemma rmsNormGeneral_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (x : E) :
    rmsNormGeneral a (-x) = -rmsNormGeneral a x := by
  unfold rmsNormGeneral
  rw [norm_neg, smul_neg, smul_neg]

/-- `‖x‖ = c` 时 `‖rmsNormGeneral a x‖ = |a|`（`a ≥ 0` 时即 `a`）。 -/
lemma norm_rmsNormGeneral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (ha : 0 ≤ a) (x : E) (c : ℝ) (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormGeneral a x‖ = a := by
  have hxpos : 0 < ‖x‖ := by rw [hx]; exact hc
  unfold rmsNormGeneral
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hxpos)),
    hx, one_div, inv_mul_cancel₀ (ne_of_gt hc), mul_one]

/-- 对径点对的像距：`‖rmsNormGeneral a x − rmsNormGeneral a (−x)‖ = 2a`
    （`‖x‖ = c`，`a ≥ 0`）。 -/
lemma rmsNormGeneral_antipodal_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 ≤ a) (x : E) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormGeneral a x - rmsNormGeneral a (-x)‖ = 2 * a := by
  rw [rmsNormGeneral_neg]
  have hsub : rmsNormGeneral a x - -rmsNormGeneral a x = (2 : ℝ) • rmsNormGeneral a x := by
    rw [sub_neg_eq_add, two_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, norm_rmsNormGeneral a ha x c hc hx]
  norm_num

/-- `‖x‖ = c` 时 `‖x − (−x)‖ = 2c`（一般内积空间版；原专用版见 `norm_sub_neg`）。
    ⚠ 需要 `[InnerProductSpace ℝ E]`（比 `[NormedAddCommGroup E]` 强）：
    证明用 `(2 : ℝ) • x`，在纯赋范群上没有 `ℝ`-模结构。 -/
lemma norm_sub_neg_general {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (c : ℝ) (hx : ‖x‖ = c) :
    ‖x - (-x)‖ = 2 * c := by
  have hsub : x - (-x) = (2 : ℝ) • x := by rw [sub_neg_eq_add, two_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, hx]
  norm_num

/-- **`rmsNormGeneral_sharp_attained`（取等）**：一般实内积空间中，任何范数为 `c` 的 `x`
    与它的对径点 `−x` **精确达到**常数 `a/c`：
    `‖F x − F(−x)‖ = (a/c)·‖x − (−x)‖`（`a ≥ 0`、`0 < c`、`‖x‖ = c`）。

    这是 `RealRMSNormSharpness.rmsNormE_sharp_attained` 的推广。 -/
theorem rmsNormGeneral_sharp_attained {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 ≤ a) (x : E) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormGeneral a x - rmsNormGeneral a (-x)‖ = (a / c) * ‖x - (-x)‖ := by
  rw [rmsNormGeneral_antipodal_norm a ha x c hc hx, norm_sub_neg_general x c hx]
  have hval : (a / c) * (2 * c) = 2 * a := by
    field_simp
    ring
  rw [hval]

/-- **存在范数为 `c` 的向量**（`n > 0` 的 `Fin n` 情形；见 `RealRMSNormSharpness.exists_norm_eq`）。
    ⚠ 名字写**裸名** `exists_norm_eq`：本文件与 `RealRMSNormSharpness` 同在 `Lattice` 命名空间，
    而 `RealRMSNormSharpness` 是**模块名不是命名空间** ⟹ 限定形式 `RealRMSNormSharpness.exists_norm_eq`
    **不在作用域**（实测报 `unknown identifier`）。 -/
lemma exists_norm_eq_general {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 < c) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = c :=
  exists_norm_eq hn c hc

/-- **取等点对存在**：任意实内积空间中只要**有非零向量**，对每个 `c > 0` 就存在范数为 `c`
    的 `x`，使其与 `−x` 精确达到 `a/c`（`a ≥ 0`）。
    ⚠ 前提 `∃ z, z ≠ 0` 是**本质的**：零空间里不存在范数为 `c > 0` 的向量。 -/
theorem rmsNormGeneral_sharp_pair_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hne : ∃ z : E, z ≠ 0) (a : ℝ) (ha : 0 ≤ a)
    (c : ℝ) (hc : 0 < c) :
    ∃ x : E, ‖x‖ = c ∧
      ‖rmsNormGeneral a x - rmsNormGeneral a (-x)‖ = (a / c) * ‖x - (-x)‖ := by
  obtain ⟨z, hz⟩ := hne
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨(c / ‖z‖) • z, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (le_of_lt hc) (norm_nonneg _))]
    exact div_mul_cancel₀ c (ne_of_gt hzpos)
  · exact rmsNormGeneral_sharp_attained a ha _ c hc (by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (le_of_lt hc) (norm_nonneg _))]
      exact div_mul_cancel₀ c (ne_of_gt hzpos))

/-! ## 四、常数下界与 `2a/c` 的非紧性 -/

/-- **`rmsNormGeneral_constant_lower_bound`**：取等点对给出任意有效 Lipschitz 常数的下界
    `K ≥ a/c`（`a ≥ 0`，`‖x‖ = c`，且 `K` 对**所有** `y` 成立）。
    与 `rmsNormGeneral_lipschitz` 合起来说明 `a/c` 是**真正常数**。 -/
theorem rmsNormGeneral_constant_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 ≤ a) (x : E) (c K : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c)
    (hK : ∀ y : E, ‖rmsNormGeneral a x - rmsNormGeneral a y‖ ≤ K * ‖x - y‖) :
    a / c ≤ K := by
  have h := hK (-x)
  have h2 : ‖x - (-x)‖ = 2 * c := norm_sub_neg_general x c hx
  rw [rmsNormGeneral_antipodal_norm a ha x c hc hx, h2] at h
  rw [div_le_iff₀ hc]
  nlinarith [h]

/-- **`rmsNormGeneral_two_div_not_attained`**：`a > 0` 时保守界 `(2a/c)` 在取等点对上
    **严格**（`2a < 4a`），故 `2a/c` 不是紧界 —— 真常数 `≤ a/c`。
    （原库对应结论：`RealNormSharpConstant.rmsNorm_two_sqrt_not_attained`。） -/
theorem rmsNormGeneral_two_div_not_attained {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 < a) (x : E) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormGeneral a x - rmsNormGeneral a (-x)‖ < (2 * a / c) * ‖x - (-x)‖ := by
  rw [rmsNormGeneral_antipodal_norm a (le_of_lt ha) x c hc hx, norm_sub_neg_general x c hx]
  have hval : (2 * a / c) * (2 * c) = 4 * a := by
    field_simp
    ring
  rw [hval]
  linarith

/-! ## 五、特例回收：`a = √n` 与 `EuclideanSpace ℝ (Fin n)` -/

/-- **`rmsNormE_eq_rmsNormGeneral`（定义层回收，逐点）**：在 `EuclideanSpace ℝ (Fin n)` 上、
    取 `a = √n`，推广定义**逐字**退化为既有的 `RealNormSharpConstant.rmsNormE`。
    **`rfl` 可证**（两侧定义体在 `a := √n`、`E := EuclideanSpace ℝ (Fin n)` 下是同一项）——
    ⚠ 这是"新定理严格强于原定理"的**机器可查证据**，而非文字论证。 -/
theorem rmsNormE_eq_rmsNormGeneral {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    rmsNormE x = rmsNormGeneral (Real.sqrt n) x := rfl

/-- **`rmsNormGeneral_sqrt_eq_rmsNormE`（函数层回收）**：上一条的 `funext` 形式。
    ⚠ **不是 `rfl`**：`rmsNormE` 的 `n` 是**隐式**参数（写成 `rmsNormE x`），
    而 `rmsNormGeneral (Real.sqrt n)` 需显式给出 `E`，两者的**隐式参数结构不同**
    ⟹ 命题是"两个函数外延相等"，需 `funext` 而不能靠 defeq 直接闭合。
    （这一点**经探针实测**：`Real.sqrt n` 在 `n : ℕ` 处**无需 `↑n` 转换**即可精化，
    真因是隐式参数的 eta 结构，不是类型转换。） -/
theorem rmsNormGeneral_sqrt_eq_rmsNormE (n : ℕ) :
    rmsNormGeneral (E := EuclideanSpace ℝ (Fin n)) (Real.sqrt n) = rmsNormE (n := n) :=
  funext fun x => (rmsNormE_eq_rmsNormGeneral x).symm

/-- **`rmsNormGeneral_recovers_rmsNormE`（定理层回收，主要特例）**：把核心推广
    `rmsNormGeneral_lipschitz` 实例化到 `E = EuclideanSpace ℝ (Fin n)`、`a = √n`
    （用 `Real.sqrt_nonneg` 提供 `0 ≤ a`），**逐字**得到既有定理
    `RealRMSNormSharpness.rmsNormE_sqrt_lipschitz` 的陈述。

    ⚠ 这说明原定理是推广版的**特例**（`a : ℝ` 自由 ⟹ 取 `a := √n`）。
    ⚠ 原定理本身**未在 `RealRMSNormSharpness.lean` 中被改动**；本定理是**新增的回收**。 -/
theorem rmsNormGeneral_recovers_rmsNormE {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖rmsNormE x - rmsNormE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖ := by
  have h := rmsNormGeneral_lipschitz (Real.sqrt n) (Real.sqrt_nonneg n) x y c hc hx hy
  rwa [← rmsNormE_eq_rmsNormGeneral x, ← rmsNormE_eq_rmsNormGeneral y] at h

/-- **`rmsNormGeneral_sharp_recovers_rmsNormE`（取等回收）**：同样实例化
    `rmsNormGeneral_sharp_attained`，得到既有 `rmsNormE_sharp_attained` 的陈述。 -/
theorem rmsNormGeneral_sharp_recovers_rmsNormE {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormE x - rmsNormE (-x)‖ = (Real.sqrt n / c) * ‖x - (-x)‖ := by
  have h := rmsNormGeneral_sharp_attained (Real.sqrt n) (Real.sqrt_nonneg n) x c hc hx
  rwa [← rmsNormE_eq_rmsNormGeneral x, ← rmsNormE_eq_rmsNormGeneral (-x)] at h

/-- **`rmsNormGeneral_constant_lower_bound_recovers_rmsNormE`**：常数下界的回收
    （对应 `RealNormSharpConstant.rmsNorm_constant_lower_bound` 的结论形状）。 -/
theorem rmsNormGeneral_constant_lower_bound_recovers_rmsNormE {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (c K : ℝ) (hc : 0 < c) (hx : ‖x‖ = c)
    (hK : ∀ y : EuclideanSpace ℝ (Fin n), ‖rmsNormE x - rmsNormE y‖ ≤ K * ‖x - y‖) :
    Real.sqrt n / c ≤ K := by
  refine rmsNormGeneral_constant_lower_bound (Real.sqrt n) (Real.sqrt_nonneg n) x c K hc hx ?_
  intro y
  have h := hK y
  rwa [rmsNormE_eq_rmsNormGeneral x, rmsNormE_eq_rmsNormGeneral y] at h

/-! ## 六、非紧性对照：原文件的 `2√n/c` 界在推广版里成为 `2a/c`

`RealNormLipschitz` 的保守界 `(2√n/c)` 在推广坐标下是 `(2a/c)`（`a = √n`），
而 `rmsNormGeneral_two_div_not_attained` 说明它在取等点对上严格；
`rmsNormGeneral_lipschitz` 给出紧的 `(a/c)`。两者关系与专用版一致，
但**不再绑定任何维数** —— 这正说明 `√n` 的角色自始至终只是那个自由标量 `a`。 -/

/-- **`rmsNormGeneral_lipschitz_sharp_compare`（比较）**：`a > 0` 时
    · 上界：`(a/c)` 成立；
    · 严格性：`(a/c) < (2a/c)`。
    即推广版的常数被完全定死为 `a/c`，与维数无关。 -/
theorem rmsNormGeneral_lipschitz_sharp_compare {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 < c) :
    (∀ x y : E, c ≤ ‖x‖ → c ≤ ‖y‖ →
        ‖rmsNormGeneral a x - rmsNormGeneral a y‖ ≤ (a / c) * ‖x - y‖) ∧
    (a / c < 2 * a / c) := by
  refine ⟨fun x y hx hy =>
    rmsNormGeneral_lipschitz a (le_of_lt ha) x y c hc hx hy, ?_⟩
  have h1 : 0 < a / c := div_pos ha hc
  have h2 : 2 * a / c - a / c = a / c := by ring
  linarith

end Lattice
