import Mathlib

/-!
# LATTICE: 严格凸/凹函数的**等号刻画工具箱**

全库各处（排序、对数幂、信息论不等式、Jensen、KL 等号刻画）反复出现同一模式：

> 「严格凸/凹函数在加权组合处**取等** ⟹ 各点相等」

此前这段推理在多个文件里被手工重复（每次都要 `by_contra` + 严格不等式 + `linarith`）。
本文件把它收敛到**唯一权威位置**：一个定义桥、三条等号引擎、三个具体函数的等号情形。

## 本文件建立

1. `strictConvexOn_eq_iff_lt`：定义桥 —— 把 `StrictConvexOn ℝ s f` 展开成
   `Convex ℝ s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ a b > 0, a + b = 1 → f (a•x + b•y) < a•f x + b•f y`
   （即定义的 `Iff.rfl`），供不想记定义体的证明直接 `rw`/`simp`。
2. `strictConvexOn_imp_convexOn`：`StrictConvexOn ℝ s f → ConvexOn ℝ s f`
   （严格性 ⟹ 非严格性；`x = y` 的退化情形用 `add_smul` + `a + b = 1` 化掉）。
3. `eq_of_strictConvexOn_combo_eq`（**核心引擎**）：严格凸函数在两点加权组合处取等 ⟹ 两点相等。
4. `eq_of_strictConcaveOn_combo_eq`：对偶（严格凹）版本。
5. `eq_of_strictConvexOn_sum_eq`：Jensen 求和的等号 ⟹ 所有点相等
   （走 mathlib `StrictConvexOn.map_sum_eq_iff`）。
6. `log_combo_eq_iff`：`Real.log` 的两点严格凹等号情形
   `a·log x + b·log y = log(a·x + b·y) ⟺ x = y`（`0 < a,b`、`a + b = 1`、`0 < x,y`）。
7. `mulLog_combo_eq_iff`：`x ↦ x·log x` 的两点严格凸等号情形
   `(a·x + b·y)·log(a·x + b·y) = a·(x·log x) + b·(y·log y) ⟺ x = y`
   （`0 < a,b`、`a + b = 1`、`0 ≤ x,y`；用 `Real.strictConvexOn_mul_log` 在 `Set.Ici 0` 上）。
8. `strictMono_injective` / `strictAnti_injective`：严格单调 ⟹ 单射的薄封装。

## 实现路线（`log_combo_eq_iff` 为何用初等证法）

`log_combo_eq_iff` 的严格性也可以用 mathlib 的 `strictConcaveOn_log_Ioi` + 引擎 4，
但该引理在本仓 mathlib 快照里位于**根命名空间**（其文件只用 `open Real`，没有
`namespace Real`），引用形式易受命名空间变动影响。为保证对 mathlib 版本迁移稳健，
本文件改用**初等反证**：令 `m = a·x + b·y`，`log x = log(x/m) + log m`，
把等号归结为 `a·log(x/m) + b·log(y/m) = 0`；再由 `log z ≤ z − 1`（逐项乘正权）
得左端 `≤ a·(x/m − 1) + b·(y/m − 1) = 0`，故每项 `= 0`，
用 `Real.log_lt_sub_one_of_pos` 的等号刻画 `log_eq_sub_one_iff_of_pos` 得 `x/m = y/m = 1`。
（引擎 4 仍然照常交付，供其它严格凹函数复用。）

## 诚实边界（`诚实` / `标注` / `未做`）

- **`未做`**：加权求和版的等号刻画在**权重含 0** 时的精细形式
  （「只把正权重的点拉平」，即 `StrictConvexOn.map_sum_eq_iff'` 的逐点叙述）
  未在本文件重复封装；mathlib 已有 `StrictConvexOn.map_sum_eq_iff'` 可直接用。
- **`未做`**：条件期望版 / 连续（积分、测度）概率版的 Jensen 等号刻画未做；
  本文件只处理**有限和**。
- **`未做`**：`StrictConvexOn` 在高维（`E` 为一般实向量空间）的等号刻画未做；
  本文件的引擎 3/4 把 `E` 特化为 `ℝ`（`s : Set ℝ`），因为下游（排序、对数幂、
  两点信息不等式）全部是实轴上的两点情形。
- **`标注`**：`mulLog_combo_eq_iff` 在 `x = 0` 或 `y = 0` 时依赖 Lean 的约定
  `Real.log 0 = 0`，此时 `x·log x = 0`（连续延拓值）；`Real.strictConvexOn_mul_log`
  正是在 `Set.Ici 0`（含 0）上断言严格凸，故该端点被正确覆盖。
- `strictMono_injective` / `strictAnti_injective` 只是 mathlib `StrictMono.injective` /
  `StrictAnti.injective` 的薄封装（统一命名，避免各文件重复定义同义引理）。

模型无关：定义桥与引擎对任意 `s : Set ℝ`、`f : ℝ → ℝ` 成立。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 1. 定义桥 -/

/-- **严格凸性展开桥**：`StrictConvexOn ℝ s f` 与「`Convex ℝ s` 加上严格的中点不等式」
等价（即数学定义的逐项展开）。

这是 `StrictConvexOn` 的**定义体**本身（`Iff.rfl`），提供它是为了让下游证明
不必记住定义中的绑定结构即可 `rw [strictConvexOn_eq_iff_lt] at h`。 -/
theorem strictConvexOn_eq_iff_lt {s : Set ℝ} {f : ℝ → ℝ} :
    StrictConvexOn ℝ s f ↔ Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y →
      ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
        f (a • x + b • y) < a • f x + b • f y :=
  Iff.rfl

/-- **严格凸 ⟹ 凸**：`StrictConvexOn ℝ s f → ConvexOn ℝ s f`。

证明：逐点比较 `ConvexOn` 的弱不等式与 `StrictConvexOn` 的强不等式；
`x = y` 的退化情形用 `a • x + b • x = (a + b) • x = x` 化去（`add_smul` + `hab`），
此时两侧同为 `f x`。 -/
theorem strictConvexOn_imp_convexOn {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) : ConvexOn ℝ s f := by
  -- `StrictConvexOn` 是 `def` 别名（`Convex 𝕜 s ∧ ...`），点号 `.1`/`.2` 取不到分量，
  -- 须先 `obtain` 拆开合取。`a b` 是隐式绑定，也须显式给出。
  obtain ⟨hconv, hstrict⟩ := hf
  refine ⟨hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  -- `ConvexOn` 只给 `0 ≤ a`、`0 ≤ b`，而 `StrictConvexOn` 需要 `0 < a`、`0 < b`。
  -- `a = 0`（⟹ `b = 1`）或 `b = 0`（⟹ `a = 1`）时两侧都退化为同一个值，
  -- 弱不等式平凡成立；只有 `a, b > 0` 的非退化情形才需要严格凸。
  rcases eq_or_ne a 0 with ha0 | ha0
  · -- `a = 0`：由 `hab` 得 `b = 1`，两侧同为 `f y`。
    subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases eq_or_ne b 0 with hb0 | hb0
  · -- `b = 0`：由 `hab` 得 `a = 1`，两侧同为 `f x`。
    subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simp
  · -- 非退化情形：`0 < a`、`0 < b`。
    have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases eq_or_ne x y with rfl | hne
    · have h1 : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
      have h2 : a • f x + b • f x = f x := by rw [← add_smul, hab, one_smul]
      rw [h1, h2]
    · exact le_of_lt (hstrict hx hy hne ha' hb' hab)

/-! ## 2. 等号引擎 -/

/-- **核心引擎（严格凸版）**：严格凸函数在两点加权组合处取等，则两点相等。

证明：`by_contra` 得 `x ≠ y`，由 `hf.2` 得严格 `<`，与等号假设矛盾
（`lt_irrefl`）。

这是全库「某不等式取等 ⟹ 结构相等」的公共引擎的最一般形式；
`log_combo_eq_iff` / `mulLog_combo_eq_iff` 都是它的实例。 -/
theorem eq_of_strictConvexOn_combo_eq {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (heq : f (a • x + b • y) = a • f x + b • f y) : x = y := by
  obtain ⟨-, hstrict⟩ := hf
  by_contra hne
  have hlt := hstrict (x := x) (y := y) (a := a) (b := b) hx hy hne ha hb hab
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- **核心引擎（严格凹版）**：严格凹函数在两点加权组合处取等，则两点相等。

与 `eq_of_strictConvexOn_combo_eq` 对偶（严格 `<` 的方向相反，写法同形）。 -/
theorem eq_of_strictConcaveOn_combo_eq {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConcaveOn ℝ s f) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (heq : a • f x + b • f y = f (a • x + b • y)) : x = y := by
  obtain ⟨-, hstrict⟩ := hf
  by_contra hne
  have hlt := hstrict (x := x) (y := y) (a := a) (b := b) hx hy hne ha hb hab
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- **Jensen 等号引擎（严格凸版）**：`f` 在 `s` 上严格凸、权重 `w` 在非空 `t` 上严格正
且 `Σ_{i∈t} w i = 1`、`p i ∈ s` 时，

`f (Σ_{i∈t} w i • p i) = Σ_{i∈t} w i • f (p i)  ⟹  ∀ i ∈ t, ∀ j ∈ t, p i = p j`。

证明：走 mathlib `StrictConvexOn.map_sum_eq_iff`（它给出
`p j = Σ i, w i • p i`），再对 `i, j` 同时代换。
参数 `ht : t.Nonempty` 由调用方提供以保证「非空权重归一」的语义完整性
（本证明本身不消耗它）。 -/
theorem eq_of_strictConvexOn_sum_eq {ι : Type*} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : StrictConvexOn ℝ s f) {t : Finset ι} (ht : t.Nonempty) (w p : ι → ℝ)
    (hw : ∀ i ∈ t, 0 < w i) (h1 : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (heq : f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)) :
    ∀ i ∈ t, ∀ j ∈ t, p i = p j := by
  -- `StrictConvexOn.map_sum_eq_iff` 给出的是 `↔`，需取 `.mp` 方向。
  have h := (hf.map_sum_eq_iff (t := t) hw h1 hmem).mp heq
  intro i hi j hj
  rw [h i hi, h j hj]

/-! ## 3. 具体函数的等号情形 -/

/-- **`log z = z − 1` 的等号刻画**：`0 < z` ⟹ `Real.log z = z − 1 ⟺ z = 1`。

证明：`z ≠ 1` 时 `Real.log_lt_sub_one_of_pos` 给出严格 `<`，与等号矛盾；
`z = 1` 时两边同为 `0`。这是 `log z ≤ z − 1` 的等号情形，
在 `log_combo_eq_iff` 中把「两项非正且和为 0」收紧为「`x/m = 1`」。 -/
lemma log_eq_sub_one_iff_of_pos {z : ℝ} (hz : 0 < z) :
    Real.log z = z - 1 ↔ z = 1 := by
  constructor
  · intro h
    by_contra hz1
    have hlt := Real.log_lt_sub_one_of_pos hz hz1
    linarith
  · rintro rfl
    simp

/-- **`Real.log` 的严格凹等号情形**（初等证法）：

`0 < a`、`0 < b`、`a + b = 1`、`0 < x`、`0 < y` ⟹

`a·log x + b·log y = log(a·x + b·y)  ⟺  x = y`。

证明：令 `m = a·x + b·y > 0`。`log x = log(x/m) + log m`（`x = (x/m)·m`），
故等号等价于 `a·log(x/m) + b·log(y/m) = 0`。由 `Real.log_le_sub_one_of_pos` 逐项乘正权，
左端 `≤ a·(x/m − 1) + b·(y/m − 1) = (a·(x/m) + b·(y/m)) − (a + b) = 1 − 1 = 0`；
又两块 `a·(log(x/m) − (x/m − 1)) ≤ 0`、`b·(log(y/m) − (y/m − 1)) ≤ 0` 且和为 0，
故各自为 0，从而 `log(x/m) = x/m − 1`，用 `log_eq_sub_one_iff_of_pos` 得 `x/m = 1`，
同理 `y/m = 1`，所以 `x = m = y`。

**`诚实`**：本证明**不**依赖 `strictConcaveOn_log_Ioi` 的命名空间，故对 mathlib
版本迁移稳健（引擎 4 `eq_of_strictConcaveOn_combo_eq` 仍独立交付）。 -/
theorem log_combo_eq_iff {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) :
    a * Real.log x + b * Real.log y = Real.log (a * x + b * y) ↔ x = y := by
  set m : ℝ := a * x + b * y with hm
  have hmpos : 0 < m := by
    rw [hm]
    positivity
  have hxlog : Real.log x = Real.log (x / m) + Real.log m := by
    have hsplit : x = (x / m) * m := by rw [div_mul_cancel₀ x (ne_of_gt hmpos)]
    conv_lhs => rw [hsplit]
    rw [Real.log_mul (ne_of_gt (div_pos hx hmpos)) (ne_of_gt hmpos)]
  have hylog : Real.log y = Real.log (y / m) + Real.log m := by
    have hsplit : y = (y / m) * m := by rw [div_mul_cancel₀ y (ne_of_gt hmpos)]
    conv_lhs => rw [hsplit]
    rw [Real.log_mul (ne_of_gt (div_pos hy hmpos)) (ne_of_gt hmpos)]
  have hsum : a * (x / m) + b * (y / m) = 1 := by
    have h1 : a * (x / m) + b * (y / m) = (a * x + b * y) / m := by ring
    rw [h1, ← hm, div_self (ne_of_gt hmpos)]
  -- 等号差分解：`LHS − log m = a·log(x/m) + b·log(y/m)`
  have key : a * Real.log x + b * Real.log y - Real.log m
      = a * Real.log (x / m) + b * Real.log (y / m) := by
    rw [hxlog, hylog]
    have hexp : a * (Real.log (x / m) + Real.log m)
          + b * (Real.log (y / m) + Real.log m) - Real.log m
        = (a * Real.log (x / m) + b * Real.log (y / m)) + (a + b - 1) * Real.log m := by
      ring
    rw [hexp, hab]
    ring
  constructor
  · intro h
    have hzero : a * Real.log (x / m) + b * Real.log (y / m) = 0 := by
      have hk := key
      rw [h] at hk
      -- `key` 的左端是 `a·log x + b·log y − log m`；用 `h` 代换后即成
      -- `log m − log m = ...`，`ring_nf` 化掉后直接读出结论。
      rw [sub_self] at hk
      exact hk.symm
    have hb1 : a * (Real.log (x / m) - (x / m - 1)) ≤ 0 := by
      have hle := Real.log_le_sub_one_of_pos (div_pos hx hmpos)
      have := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
      linarith
    have hb2 : b * (Real.log (y / m) - (y / m - 1)) ≤ 0 := by
      have hle := Real.log_le_sub_one_of_pos (div_pos hy hmpos)
      have := mul_le_mul_of_nonneg_left hle (le_of_lt hb)
      linarith
    have htot : a * (Real.log (x / m) - (x / m - 1))
        + b * (Real.log (y / m) - (y / m - 1)) = 0 := by
      have h1 : a * (x / m - 1) + b * (y / m - 1) = 0 := by linarith [hsum, hab]
      linarith [hzero, h1]
    have h1z : a * (Real.log (x / m) - (x / m - 1)) = 0 := by linarith [hb1, hb2, htot]
    have h2z : b * (Real.log (y / m) - (y / m - 1)) = 0 := by linarith [hb1, hb2, htot]
    have ht1 : x / m = 1 := by
      have hz : Real.log (x / m) - (x / m - 1) = 0 := by
        rcases mul_eq_zero.mp h1z with h | h
        · exact absurd h (ne_of_gt ha)
        · exact h
      have hlog : Real.log (x / m) = x / m - 1 := by linarith
      exact (log_eq_sub_one_iff_of_pos (div_pos hx hmpos)).mp hlog
    have hu1 : y / m = 1 := by
      have hz : Real.log (y / m) - (y / m - 1) = 0 := by
        rcases mul_eq_zero.mp h2z with h | h
        · exact absurd h (ne_of_gt hb)
        · exact h
      have hlog : Real.log (y / m) = y / m - 1 := by linarith
      exact (log_eq_sub_one_iff_of_pos (div_pos hy hmpos)).mp hlog
    have hxm : x = m := by
      have h1 : x = (x / m) * m := by rw [div_mul_cancel₀ x (ne_of_gt hmpos)]
      rw [ht1] at h1
      simpa using h1
    have hym : y = m := by
      have h1 : y = (y / m) * m := by rw [div_mul_cancel₀ y (ne_of_gt hmpos)]
      rw [hu1] at h1
      simpa using h1
    rw [hxm, hym]
  · -- 反向：`x = y` 时两侧都是 `x·log x`。`m` 由 `set` 引入，
    -- 先证 `m = x`（`a·x + b·x = (a+b)·x = x`）再整体代换。
    rintro rfl
    have hmx : m = x := by
      rw [hm, ← add_mul, hab, one_mul]
    rw [hmx]
    have h2 : a * Real.log x + b * Real.log x = Real.log x := by
      rw [← add_mul, hab, one_mul]
    rw [h2]

/-- **`x ↦ x·log x` 的严格凸等号情形**：

`0 < a`、`0 < b`、`a + b = 1`、`0 ≤ x`、`0 ≤ y` ⟹

`(a·x + b·y)·log(a·x + b·y) = a·(x·log x) + b·(y·log y)  ⟺  x = y`。

证明：由 mathlib `Real.strictConvexOn_mul_log`（断言 `fun z ↦ z·log z` 在 `Set.Ici 0`
上严格凸，含端点 `0`，依赖约定 `Real.log 0 = 0`）配合核心引擎
`eq_of_strictConvexOn_combo_eq`；`Set.Ici 0` 的成员由 `Set.mem_Ici.mpr` 给出。

**`标注`**：端点 `0` 处使用 Lean/`Real.log` 的连续延拓约定 `log 0 = 0`，
故 `0·log 0 = 0` 被正确覆盖。 -/
theorem mulLog_combo_eq_iff {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (a * x + b * y) * Real.log (a * x + b * y)
      = a * (x * Real.log x) + b * (y * Real.log y) ↔ x = y := by
  constructor
  · intro h
    have h' : (fun z : ℝ => z * Real.log z) (a • x + b • y)
        = a • (fun z : ℝ => z * Real.log z) x + b • (fun z : ℝ => z * Real.log z) y := by
      simpa only [smul_eq_mul] using h
    exact eq_of_strictConvexOn_combo_eq Real.strictConvexOn_mul_log
      (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) ha hb hab h'
  · -- 反向：`x = y` 时左端 `(a·x+b·x)·log(a·x+b·x)` 与右端 `a·(x·log x)+b·(x·log x)`
    -- 都归约为 `x·log x`。
    rintro rfl
    have h1 : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
    rw [h1]
    have h2 : a * (x * Real.log x) + b * (x * Real.log x) = x * Real.log x := by
      rw [← add_mul, hab, one_mul]
    rw [h2]

/-! ## 4. 严格单调 ⟹ 单射 -/

/-- **严格单调 ⟹ 单射**：`StrictMono f → Function.Injective f`。

mathlib 的 `StrictMono.injective` 的薄封装（统一名，避免各文件重复定义同义引理）。 -/
theorem strictMono_injective {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    (hf : StrictMono f) : Function.Injective f :=
  hf.injective

/-- **严格单调递减 ⟹ 单射**：`StrictAnti f → Function.Injective f`。

mathlib 的 `StrictAnti.injective` 的薄封装。 -/
theorem strictAnti_injective {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    (hf : StrictAnti f) : Function.Injective f :=
  hf.injective

end Lattice
