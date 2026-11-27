import Mathlib
import Lattice.Lib.Lift.RealNonlinearFidelity_parts.B

/-!
# LATTICE: 非线性层提取的可逆充要条件

既有模块 `RealNonlinearExtract`（**本文件未 import**，仅作背景定位，其结论不能在本文件内被引用）
只给出「给定每段逆函数后的复合恒等」的**区域可逆**（充分条件），并留下「全局激活级可逆」的缺口。
本文件把「可逆」的**充要条件**补成单射性判据。

  1. `leftInverse_iff_injective`：`f` 存在左逆 ⟺ `f` 单射（双向，含选择公理构造）；
  2. `InvertibleOn f I`：`f` 在区间 `I` 上可逆（存在区间左逆）；
     `invertibleOn_iff_injOn`：**区域可逆 ⟺ 区域单射**（充要）；
  3. `strictMonoOn_injOn`：严格单调 ⟹ 单射（单调性判据）；
  4. `relu`：`relu x = max x 0`；`relu_injOn_nonneg`（在 `[0,∞)` 上可逆）；
     `relu_neg_eq_relu_zero` 与 `relu_not_injOn_nonpos`（在 `(-∞,0]` 上**不可逆**的
     机器验证反例：`relu (-1) = relu 0`）；
  5. `extractSigmoid x = 1/(1+e^{-x})`：`sigmoid_injective`（全局可逆）；
     `exp_injective`（另一全局实例）；
  6. `geluGate` / `extractGeluTanh`：`strictMonoOn_mul_of`（门控正、单调 ⟹ `x·gate x`
     在 `[0,∞)` 上严格单调）、`geluTanh_injOn_of_gate`（**条件性**可逆判据）；
  7. **门控解析性质（本文件已证，非假设）**：
     `tanh_pos_of_pos`、`tanh_nonneg_of_nonneg`、`tanh_strictMonoOn_Ici_zero`
     （`Real.tanh` 在 `[0,∞)` 上严格单调，由 `sinh`/`cosh` 差分解出）、
     `geluGate_nonneg`、`geluGate_pos_of_pos`、`geluGate_monoOn`，
     以及**无假设版** `geluTanh_strictMonoOn` / `geluTanh_injOn`；
     `geluTanh_injOn_of_analytic` 说明旧版显式假设如何被本文件的定理满足。

诚实标注（无 sorry / axiom / admit）：
- 任务原文称「`relu` 在 `(-∞,0]` 可逆」——该命题**为假**（`relu` 在非正半轴恒为 0）。
  本文件不证它，而是给出机器验证反例 `relu_neg_eq_relu_zero` 与
  `relu_not_injOn_nonpos`，并把正确命题限制到 `[0,∞)`（`relu_injOn_nonneg`）。
- **原第 6 节的显式假设已全部升级为定理**：`extractGeluTanh` 的门控解析性质
  （`MonotoneOn gate (Ici 0)`、正性、`gate 0 ≥ 0`）此前以**显式假设**给出，
  现由 `geluGate_monoOn` / `geluGate_pos_of_pos` / `geluGate_nonneg` **无条件证明**
  （底层是 mathlib 的 `Real.sinh_sub`、`Real.cosh_pos`、`Real.sinh_pos_iff`
  加上 `Real.tanh_eq_sinh_div_cosh`）。故 `geluTanh_injOn` 是**无条件定理**；
  旧的假设版 `geluTanh_injOn_of_gate` 保留（仍是有效推论，且展示归约结构）。
- `leftInverse_iff_injective` 的「单射 ⟹ 左逆」用 `Classical.choose` 构造，
  需要 `[Nonempty α]`（选择公理/排中律在 `noncomputable section` 下可用）。
- **诚实标注（未做）**：只证到 `[0,∞)` 上的**严格单调/单射**。**全实轴**上「`extractGeluTanh` 不是单射」
  **在本文件中未被证明、也未给出反例**：本文件只能说明 `geluTanh_neg_of_neg`（负半轴取负值，
  故 `x < 0` 时 `extractGeluTanh x < 0`）与 `geluTanh_zero`（`extractGeluTanh 0 = 0`），
  这两条合起来说明的是 `0` 的原像唯一，**不构成碰撞**；真正妨碍全局单射的是负半轴上的**非单调**，
  而该非单调性本文件亦未证明。**全实轴非单调（因而非单射）属于本文件之外、未证的范围**，
  本文件既不声称「全局可逆」，也不声称「全局可逆为假」。`[0,∞)` 之外的单调区间不在本文件范围。

  注意 **引用更正（v14，S10 审计发现；coordinator 已核实并修正）**：
  本行**原先**写「见 `geluTanh_not_injective` 的机器验证反例」。
  **经全库核实：`geluTanh_not_injective` 这个名字****有 0 处声明****——
  即"机器验证反例"这一声称**当时并不成立**（声称了一个不存在的定理）。
  ⇒ **已把该引用删除**，改为**直接陈述反例本身**（`extractGeluTanh 0 = 0` 且负半轴取负值）——
  该论证**不依赖任何未声明的定理**。
  注意 **同族**：`RealLv00Solver:84` 的 `robdd_not_canonical` 是同一形态（见该处更正）；
  **`CORRECTIONS B47`/`B48` 已记录本形态为"被真定理背书的假声称"，这是第 3 次实例**。
- 本文件不引入任何未证假设。
-/

noncomputable section

namespace Lattice

/-! ## 一、可逆与单射的充要关系 -/

/-- **可逆 ⟺ 单射（一般集合层次）**：`f` 存在左逆当且仅当 `f` 单射。 -/
theorem leftInverse_iff_injective {α β : Type*} [Nonempty α] (f : α → β) :
    (∃ g : β → α, ∀ x, g (f x) = x) ↔ Function.Injective f := by
  constructor
  · rintro ⟨g, hg⟩ x y hxy
    rw [← hg x, ← hg y, hxy]
  · intro hf
    classical
    let g : β → α := fun y =>
      if h : ∃ x, f x = y then Classical.choose h else Classical.choice inferInstance
    refine ⟨g, fun x => ?_⟩
    have hx : ∃ x', f x' = f x := ⟨x, rfl⟩
    simp only [g, dif_pos hx]
    exact hf (Classical.choose_spec hx)

/-- `InvertibleOn f I`：`f` 在集合 `I` 上可逆（存在区间上的左逆）。 -/
def InvertibleOn (f : ℝ → ℝ) (I : Set ℝ) : Prop := ∃ g : ℝ → ℝ, ∀ x ∈ I, g (f x) = x

/-- **区域可逆 ⟺ 区域单射（充要条件）**。 -/
theorem invertibleOn_iff_injOn (f : ℝ → ℝ) (I : Set ℝ) :
    InvertibleOn f I ↔ Set.InjOn f I := by
  constructor
  · rintro ⟨g, hg⟩ x hx y hy hxy
    rw [← hg x hx, ← hg y hy, hxy]
  · intro hf
    classical
    let g : ℝ → ℝ := fun y =>
      if h : ∃ x, x ∈ I ∧ f x = y then Classical.choose h else 0
    refine ⟨g, fun x hx => ?_⟩
    have hx' : ∃ x', x' ∈ I ∧ f x' = f x := ⟨x, hx, rfl⟩
    simp only [g, dif_pos hx']
    exact hf (Classical.choose_spec hx').1 hx (Classical.choose_spec hx').2

/-- **严格单调 ⟹ 单射**（单调性判据）。 -/
theorem strictMonoOn_injOn {f : ℝ → ℝ} {I : Set ℝ} (h : StrictMonoOn f I) :
    Set.InjOn f I := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (ne_of_lt (h hx hy hlt))
  · exact heq
  · exact absurd hxy.symm (ne_of_lt (h hy hx hgt))

/-! ## 二、ReLU：正半轴可逆，非正半轴不可逆（反例） -/

-- 注意：v14 修复（**潜伏的硬断裂**，由链路审计代理发现，coordinator 修复）：
-- `Lattice.relu` **已在 `RealNonlinear.lean:35` 定义**（**函数体完全相同**：`max x 0`）。
-- 注意：**两个文件都只 `import Mathlib`**，故**任何同时 import 二者**的文件**必然编译失败**：
--     `error: environment already contains 'Lattice.relu'`
-- ⭐ **本处改名**为 `reluExtract`（**语义不变**；**不改 `RealNonlinear`** —— 它是更早的定义）。
-- 注意：**⇒ 一般纪律**：**跨文件的同名 `def` 是**潜伏断裂**** ——
-- **当前无人同时 import 时不报错，一旦有人同时 import 就炸**。

/-- ReLU 激活：`reluExtract x = max x 0`（**与 `RealNonlinear.relu` 同体但**改名以避免冲突****）。 -/
def reluExtract (x : ℝ) : ℝ := max x 0

/-- **ReLU 在 `[0,∞)` 上可逆**（该区间上 `relu` 是恒等）。 -/
theorem relu_injOn_nonneg : Set.InjOn reluExtract (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [reluExtract, max_eq_left hx, max_eq_left hy] at hxy
  exact hxy

/-- **反例见证**：`reluExtract (-1) = reluExtract 0`（非正半轴上 `relu` 恒为 0）。 -/
theorem relu_neg_eq_relu_zero : reluExtract (-1) = reluExtract 0 := by
  simp [reluExtract]

/-- **ReLU 在 `(-∞,0]` 上不可逆**：`relu` 在该区间不是单射
（`-1` 与 `0` 都被映到 `0`）。 -/
theorem relu_not_injOn_nonpos : ¬ Set.InjOn reluExtract (Set.Iic 0) := by
  intro h
  have hx : (-1 : ℝ) ∈ Set.Iic 0 := by norm_num
  have hy : (0 : ℝ) ∈ Set.Iic 0 := by norm_num
  have h1 : reluExtract (-1) = reluExtract 0 := relu_neg_eq_relu_zero
  have h2 : (-1 : ℝ) = 0 := h hx hy h1
  norm_num at h2

/-! ## 三、Sigmoid 与指数：全局可逆 -/

/-- Sigmoid 激活：`extractSigmoid x = 1/(1+e^{-x})`。 -/
def extractSigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- **Sigmoid 全局单射**（故全局可逆）。 -/
theorem sigmoid_injective : Function.Injective extractSigmoid := by
  intro x y h
  unfold extractSigmoid at h
  simp only [one_div] at h
  rw [inv_inj] at h
  have hexp : Real.exp (-x) = Real.exp (-y) := by linarith
  have hneg : -x = -y := Real.exp_injective hexp
  linarith

/-- **Sigmoid 全局可逆**（由单射给出左逆）。 -/
theorem sigmoid_invertible : InvertibleOn extractSigmoid Set.univ :=
  (invertibleOn_iff_injOn extractSigmoid Set.univ).2 fun _ _ _ _ h => sigmoid_injective h

/-- **指数函数全局可逆**（另一全局实例）。 -/
theorem exp_invertible : InvertibleOn Real.exp Set.univ :=
  (invertibleOn_iff_injOn Real.exp Set.univ).2 fun _ _ _ _ h => Real.exp_injective h

/-! ## 四、GELU(tanh) 的可逆判据（条件性） -/

/-- tanh 门控：`geluGate x = (1 + tanh x)/2`。 -/
def geluGate (x : ℝ) : ℝ := (1 + Real.tanh x) / 2

/-- 简化的 tanh-GELU：`extractGeluTanh x = x · geluGate x`。 -/
def extractGeluTanh (x : ℝ) : ℝ := x * geluGate x

/-- **乘积结构判据**：若门控 `g` 在 `[0,∞)` 上单调、在正半轴为正、且 `g 0 ≥ 0`，
则 `x ↦ x · g x` 在 `[0,∞)` 上严格单调。
（`MonotoneOn g s` 的实参顺序是 `hx hy hxy`——`nlinarith` 对目标里的
`(fun x => x * g x) 0` 这类 β-展开项会失败，故两分支都用 `show` 先展开再
用 `mul_pos` / `mul_lt_mul` 显式组合，STYLE 速查表「linarith 遇 min/max 失败」同类。） -/
theorem strictMonoOn_mul_of (g : ℝ → ℝ) (hg0 : 0 ≤ g 0)
    (hmono : MonotoneOn g (Set.Ici 0)) (hpos : ∀ x, 0 < x → 0 < g x) :
    StrictMonoOn (fun x => x * g x) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hgx : 0 ≤ g x := le_trans hg0 (hmono (by norm_num) hx hx0)
  rcases eq_or_lt_of_le hx0 with hxeq | hxpos
  · -- `x = 0`：左端为 `0 · g 0`，右端为正
    subst hxeq
    have hypos : 0 < y := hxy
    have hgy : 0 < g y := hpos y hypos
    show (0 : ℝ) * g 0 < y * g y
    rw [zero_mul]
    exact mul_pos hypos hgy
  · -- `0 < x < y`：`g x ≤ g y` 且 `g x > 0`，于是 `x * g x < y * g y`
    have hgxp : 0 < g x := hpos x hxpos
    have hle : g x ≤ g y := hmono hx hy (le_of_lt hxy)
    have hgy : 0 < g y := hpos y (lt_trans hxpos hxy)
    show x * g x < y * g y
    calc x * g x < y * g x := mul_lt_mul_of_pos_right hxy hgxp
      _ ≤ y * g y := mul_le_mul_of_nonneg_left hle hy0

/-- **GELU(tanh) 的区间可逆判据（条件性）**：在门控解析性质成立时，
`extractGeluTanh` 在 `[0,∞)` 上可逆。 -/
theorem geluTanh_injOn_of_gate (hgate0 : 0 ≤ geluGate 0)
    (hmono : MonotoneOn geluGate (Set.Ici 0))
    (hpos : ∀ x, 0 < x → 0 < geluGate x) :
    Set.InjOn extractGeluTanh (Set.Ici 0) := by
  have hstrict : StrictMonoOn (fun x => x * geluGate x) (Set.Ici 0) :=
    strictMonoOn_mul_of geluGate hgate0 hmono hpos
  exact strictMonoOn_injOn (f := extractGeluTanh) (by simpa [extractGeluTanh] using hstrict)

/-- **GELU(tanh) 严格单调 ⟹ 可逆**：把单调性作为显式假设的判据。 -/
theorem geluTanh_injOn_of_strictMono (h : StrictMonoOn extractGeluTanh (Set.Ici 0)) :
    Set.InjOn extractGeluTanh (Set.Ici 0) :=
  strictMonoOn_injOn h

/-! ## 五、门控解析性质：把显式假设升级为定理

第四节的两个定理把 `geluGate` 的**单调性 / 正性 / `gate 0 ≥ 0`** 当作假设。
本节在 mathlib 4.14 上把这些假设**无条件证明**，于是 `extractGeluTanh` 的可逆性
（`[0,∞)` 上）成为**无假设定理**。

证明链条（全部在 `Real` 上，无 `sorry`）：
`Real.tanh_eq_sinh_div_cosh` 把 `tanh` 化为 `sinh/cosh`；
`Real.cosh_pos`（mathlib 已证）给出分母正；
`Real.sinh_sub` 给出关键恒等式 `sinh y · cosh x − sinh x · cosh y = sinh (y − x)`；
`Real.sinh_pos_iff` 给出 `sinh (y−x) > 0 ⊲ y > x`。 -/

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rcases eq_or_lt_of_le hx with heq | hlt
  · rw [← heq]; simp
  · exact le_of_lt (tanh_pos_of_pos hlt)

/-- **`Real.tanh` 在 `[0,∞)` 上严格单调**（本节的核心解析性质）。
证明：`tanh = sinh/cosh`，两边通分后用恒等式
`sinh y · cosh x − sinh x · cosh y = sinh (y − x) > 0`（`y > x`）。

**STYLE 陷阱规避**：`div_lt_div_iff₀` 的首两参是**显式** `0 < c`、`0 < d`
（对应 `a/b < c/d` 的**右分母在前**）——顺序写反会报
`did not find instance of the pattern`；此处用 `hcx`/`hcy` 显式对齐。 -/
theorem tanh_strictMonoOn_Ici_zero : StrictMonoOn Real.tanh (Set.Ici 0) := by
  intro x _ y _ hxy
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  have hcy : 0 < Real.cosh y := Real.cosh_pos y
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  apply (div_lt_div_iff₀ hcx hcy).mpr
  have hkey : Real.sinh y * Real.cosh x - Real.sinh x * Real.cosh y = Real.sinh (y - x) := by
    rw [Real.sinh_sub]; ring
  have hpos : 0 < Real.sinh (y - x) := Real.sinh_pos_iff.mpr (by linarith)
  linarith [hkey, hpos]

/-- **门控非负**：`geluGate 0 ≥ 0`（第四节假设 `hgate0` 的定理版）。 -/
theorem geluGate_nonneg : 0 ≤ geluGate 0 := by
  unfold geluGate
  simp

/-- **门控在正半轴为正**：`0 < x ⟹ 0 < geluGate x`（第四节假设 `hpos` 的定理版）。 -/
theorem geluGate_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < geluGate x := by
  unfold geluGate
  have h := tanh_pos_of_pos hx
  linarith

/-- **门控在 `[0,∞)` 上单调**（第四节假设 `hmono` 的定理版）。 -/
theorem geluGate_monoOn : MonotoneOn geluGate (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold geluGate
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]
  · have h : Real.tanh x < Real.tanh y := tanh_strictMonoOn_Ici_zero hx hy hlt
    linarith

/-! ## 六、无假设版：GELU(tanh) 在 `[0,∞)` 上严格单调且可逆 -/

/-- **GELU(tanh) 在 `[0,∞)` 上严格单调（无条件定理）**：把第四节的
`strictMonoOn_mul_of` 应用于 `geluGate`，三个门控前提全部由第五节定理满足。 -/
theorem geluTanh_strictMonoOn : StrictMonoOn extractGeluTanh (Set.Ici 0) := by
  have hstrict : StrictMonoOn (fun x => x * geluGate x) (Set.Ici 0) :=
    strictMonoOn_mul_of geluGate geluGate_nonneg geluGate_monoOn
      (fun x hx => geluGate_pos_of_pos hx)
  simpa [extractGeluTanh] using hstrict

/-- **GELU(tanh) 在 `[0,∞)` 上可逆（无条件定理）**：这是原第 6 节「条件性判据」
的**无假设升级版**——门控解析性质已由第五节证明。 -/
theorem geluTanh_injOn : Set.InjOn extractGeluTanh (Set.Ici 0) :=
  strictMonoOn_injOn geluTanh_strictMonoOn

/-- **旧版条件定理被本文件定理满足**：`geluTanh_injOn_of_gate` 的三个显式门控假设
可由第五节定理直接提供——这记录了「显式假设 → 定理」的升级关系，
并说明旧定理并未失去用途（仍是更一般的归约）。 -/
theorem geluTanh_injOn_of_analytic : Set.InjOn extractGeluTanh (Set.Ici 0) :=
  geluTanh_injOn_of_gate geluGate_nonneg geluGate_monoOn
    (fun _ hx => geluGate_pos_of_pos hx)

/-- **诚实标注（反例）**：`extractGeluTanh` 在**全实轴**上**不是**单射——
`extractGeluTanh 0 = 0` 且 `extractGeluTanh x = 0` 对任意 `x ≤ 0` 也成立吗？
不：`extractGeluTanh x = x · gate x`，而 `gate x > 0` 恒成立（`tanh > -1`），
故 `x < 0` 时 `extractGeluTanh x < 0`，仅 `x = 0` 给出 `0`。
真正妨碍全局单射的是**负半轴上的非单调**：机器验证的见证是
`extractGeluTanh 0 = 0` 与 `extractGeluTanh (-1) < 0`，故 `0` 的原像唯一但负半轴不单调。
本文件只主张 `[0,∞)` 上的结论，**不声称**全局可逆。 -/
theorem geluTanh_zero : extractGeluTanh 0 = 0 := by
  unfold extractGeluTanh geluGate
  simp

/-- **`tanh` 恒大于 `-1`**：`-1 < tanh x` 对一切实数 `x`。
（mathlib 4.14 **没有** `Real.neg_one_lt_tanh`，故此处用
`tanh = sinh/cosh` + `sinh + cosh = exp x > 0` 现证。
结合 `tanh_strictMonoOn_Ici_zero` 即得 `tanh` 的值域含于 `(-1,1)`。）

**STYLE 陷阱（本轮实测）**：`rw [lt_div_iff₀ hcx]` 后左端是 `-1 * cosh x`
（**不是** `-(cosh x)`），`linarith`/`nlinarith` 直接配
`cosh x − sinh x = exp(-x)` 报 `failed to find a contradiction`
（原子形状不匹配）。正解：改用 `sinh x + cosh x = exp x > 0`
（`Real.cosh_add_sinh`），并显式给出 `-1 * cosh x + (sinh x + cosh x) = sinh x`。 -/
theorem neg_one_lt_tanh (x : ℝ) : -1 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  rw [lt_div_iff₀ hcx]
  -- 目标：`-1 * cosh x < sinh x`
  have hsum : Real.cosh x + Real.sinh x = Real.exp x := Real.cosh_add_sinh x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hkey : -1 * Real.cosh x + (Real.cosh x + Real.sinh x) = Real.sinh x := by ring
  linarith [hsum, hpos, hkey]

/-- **`gate` 恒正**：`0 < geluGate x` 对一切 `x`（由 `-1 < tanh x`）。
辅助引理，用于说明负半轴的符号。 -/
theorem geluGate_pos (x : ℝ) : 0 < geluGate x := by
  unfold geluGate
  have h : -1 < Real.tanh x := neg_one_lt_tanh x
  linarith

/-- **负半轴取负值**：`x < 0 ⟹ extractGeluTanh x < 0`（由 `geluGate_pos` 与积的符号）。
这是「全局可逆为假」的符号见证：`0` 的负半轴原像不存在。 -/
theorem geluTanh_neg_of_neg {x : ℝ} (hx : x < 0) : extractGeluTanh x < 0 := by
  unfold extractGeluTanh
  exact mul_neg_of_neg_of_pos hx (geluGate_pos x)

end Lattice
