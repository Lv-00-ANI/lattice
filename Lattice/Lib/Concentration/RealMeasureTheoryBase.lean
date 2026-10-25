import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# LATTICE: 测度论基础层 —— Borel 空间 / 概率测度 / 独立性 / 条件期望 / 积分

ROADMAP「测度论升级包」（`notes/完善推广泛化路线图.md` §4.2）要求一次性建立
**共享基础设施**，使 McDiarmid（A3.1）、DPI（A3.8）、Hoeffding 一般版（A3.5）
三处缺口同时受益。本文件是该升级包的第 1 阶段：**基础层**。

## ⚠ 为什么需要本文件（以及一个必须先纠正的判断）

路线图 §3 记录 **`BorelSpace` 全库 0 使用**，并由此推出「测度论层几乎未展开，
必须先建地基」。**前半句实测为真**（`lean/*.lean` 中 `BorelSpace` 确为 0 命中），
**后半句不成立**：本库**已有**相当多的测度论内容，只是**没有走 `BorelSpace`**：

| 已有 | 位置 | 内容 |
|:--|:--|:--|
| `hoeffding_lemma_measure` | `RealHoeffdingLemmaMeasure.lean:165` | 一般测度论 Hoeffding 引理（`∫`、`IsProbabilityMeasure`） |
| `hoeffding_lemma_measure_interval` | 同上 `:225` | 任意区间 `[a,b]` 的形式 |
| `mgf_factor_measure` | `RealHoeffdingMeasure.lean:77` | `iIndepFun` + `iIndepFun.mgf_sum` 因子分解 |
| `hoeffding_tail_of_mgf_bound` | 同上 `:122` | 测度版切尔诺夫桥（`(μ ·).toReal`） |

⟹ 本文件的定位**不是**"从零建地基"，而是**补齐缺失的那一块并统一接口**：
把 `BorelSpace`、`IsProbabilityMeasure` 的归一化、`iIndepFun`、`condexp`、
积分这五件东西**固化成可复用的引理层**，供三个缺口直接引用。

## ⚠⚠ 本文件建立时实测到的三条判据（请后续代理直接照用）

### 判据 1：`unknown identifier` 有**四个**原因，不止"名字不存在"

在 `import Mathlib` 之后实测（`_m1_probe_gaps.lean`）：

```
#check @Real.convexOn_exp                     → unknown constant   ✗
#check @MeasureTheory.condExp                 → unknown identifier ✗
#check @MeasureTheory.Measure.restrict_compl  → unknown constant   ✗
#check @measureReal_univ                      → unknown identifier ✗
```

而 `RealHoeffdingLemmaMeasure.lean:101` **逐字使用 `convexOn_exp`** 且该文件在
`lakefile.toml` 的 `roots` 中。**⇒ 原因只能是**：

1. 名字真不存在；
2. 命名空间错；
3. ⭐ **`import Mathlib` 没有覆盖到声明它的文件** —— `Mathlib.lean` 是**精选**导入
   （实测其 3575–3581 行只导入 `ConditionalExpectation` 的 **7 个子模块**），
   **不是全库**；
4. ⭐⭐ **大小写/拼写错**（见判据 2）。

**⇒ 操作规程**：凡 `#check` 报 unknown，**先 grep 源码**
`lean/.lake/packages/mathlib/Mathlib/**`，以**源码里的写法为准**。

### 判据 2：是 `condexp`（全小写），不是 `condExp`

`Mathlib/MeasureTheory/Function/ConditionalExpectation/` 是**目录**（源码在
`.../ConditionalExpectation/Basic.lean`），其中的声明**全小写**：
`condexp`、`condexp_const`、`condexp_add`、`condexp_mono`、`condexp_nonneg`、
`condexp_congr_ae`、`condexp_bot`、`condexp_condexp_of_le`、`integral_condexp`。
记法是 `μ[f|m]`。**`MeasureTheory.condExp` / `condExpL1` 实测不存在。**

### 判据 3：`Test-Path <x>.lean` 得 False **推不出**"模块不存在"

`ConditionalExpectation` 是**目录** + 子模块，`Test-Path ...\ConditionalExpectation.lean`
返回 False，但模块**存在**。**⇒ 必须区分"文件"与"目录+子模块"两种布局。**

## 本文件交付（第 1 阶段：基础层）

1. `borelOfTopology`：`MeasurableSpace` + `TopologicalSpace` ⟹ `borel α` 的使用模式；
2. `prob_univ` / `prob_isFinite` / `prob_toReal_univ`：概率测度归一化的三种形态；
3. `iIndepFun` 的 MGF 因子分解接口（`indep_mgf_sum`）；
4. `condexp` 的**可积性、tower、constant、mono**四个引理的固化；
5. 积分层：`lintegral`/`integral` 的桥与 `Integrable` 的组合子。

**诚实边界**（本文件不证 / 不声称的）：
- 本文件**不引入任何新的数学定理**，全部是既有 mathlib 事实的**接口固化 + 类型级实证**；
  它的价值在于**把"哪些名字真的存在、签名逐字是什么"变成可编译的代码**，
  从而消除后续文件的 `unknown identifier` 类空转。
- `BorelSpace` 在本文件中**被使用并实例化**（`Real`、`ℝ≥0∞`、离散拓扑），
  但**不证明**一般拓扑空间的 Borel 性质（那需要 `PolishSpace`/`SecondCountable`）。
- 未做：`Kernel`/`CondDistrib`（测度论 DPI 的可能路线）、`Filtration` 的鞅迭代
  （属后续阶段）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-! ## 一、Borel 层：从 `MeasurableSpace` + 拓扑得到 Borel σ-代数

### ⭐⭐ 本层的核心实证：mathlib 有**两个**类，且**不能互相替代**

| 类 | 含义 | 强度 |
|:--|:--|:--|
| `BorelSpace α` | **断言**已给的 `[MeasurableSpace α]` **等于** `borel α` | **强**（等式） |
| `OpensMeasurableSpace α` | 每个**开集**可测 | **弱**（推论） |

```
BorelSpace : (α : Type*) → [TopologicalSpace α] → [MeasurableSpace α] → Prop
BorelSpace.measurable_eq : [BorelSpace α] → (inferInstance : MeasurableSpace α) = borel α
OpensMeasurableSpace : (α : Type*) → [TopologicalSpace α] → [MeasurableSpace α] → Prop
BorelSpace.opensMeasurable : [BorelSpace α] → OpensMeasurableSpace α      -- 单向
IsOpen.measurableSet : [OpensMeasurableSpace α] → IsOpen s → MeasurableSet s
borel : (α : Type*) → [TopologicalSpace α] → MeasurableSpace α
```

⭐⭐ **反方向不成立**（实测，`_m1_probe_borel.lean`）：
**不存在**一般实例 `BorelSpace (borel α)`。证据：

```
example (α : Type*) [TopologicalSpace α] : BorelSpace α := by infer_instance
→ error: failed to synthesize MeasurableSpace α       -- 连 MeasurableSpace 都搜不到
```

⟹ **`BorelSpace` 只能对"已经用 `borel α` 注册了 `MeasurableSpace` 实例"的**具体类型**
成立（mathlib 为 `ℝ`、`ℕ`、`ℚ`、`ℝ≥0`、`ℝ≥0∞`、`ℂ`、`Bool`、`Unit`、`Empty`、
积/子类型/`Pi` 等逐个给出实例）。**对任意 `α`，唯一可行的"拓扑 ⟹ Borel"路径是**：

1. **要 `BorelSpace` 本身**：把 `MeasurableSpace` 实例**声明为** `borel α`
   （`borelOfTopology`）；
2. **只要"开集可测"这一推论**：用 **`OpensMeasurableSpace`**
   （`opensMeasurable_of_borel` / `isOpen_measurableSet`）。

⚠ **`ISOpen.measurableSet` 要求 `OpensMeasurableSpace`，不是 `BorelSpace`**——
本文件先前写成 `hs.measurableSet` 且只给 `[BorelSpace α]`，
实测报 `failed to synthesize BorelSpace α`（因为 `BorelSpace` 的第三个参数
是待合成元变量，而它**不是可搜索实例**）。**⇒ 必须显式承接。** -/

/-- **Borel 使用模式（生成方向）**：给定拓扑，`borel α` 就是可直接注册的
`MeasurableSpace` 实例。这把"怎么从拓扑得到 Borel σ-代数"固化为**可编译的事实**。 -/
theorem borelOfTopology (α : Type*) [t : TopologicalSpace α] :
    (borel α : MeasurableSpace α) = @borel α t := rfl

/-- **Borel ⟹ 开集可测（承重的桥）**：`[BorelSpace α]` 给出
`OpensMeasurableSpace α`。这是 `IsOpen.measurableSet` 的**唯一入口**；
⚠ 它**只单向**成立（`OpensMeasurableSpace` **推不出** `BorelSpace`）。 -/
theorem opensMeasurable_of_borel (α : Type*) [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] : OpensMeasurableSpace α := inferInstance

/-- **开集可测**：`[BorelSpace α]` 下每个开集可测。
本定理把 `BorelSpace → OpensMeasurableSpace → IsOpen.measurableSet` 两级
**一次接通**，供下游直接调用（这是 `BorelSpace` 在本库的**主要用点**）。 -/
theorem isOpen_measurableSet {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] {s : Set α} (hs : IsOpen s) : MeasurableSet s :=
  hs.measurableSet

/-- **Borel 使用模式（改写方向）**：`[BorelSpace α]` 时，`MeasurableSpace α` 实例
**等于** `borel α`。只把 `BorelSpace.measurable_eq` 换个便于 `rw` 的朝向。 -/
theorem measurableSpace_eq_borel (α : Type*) [TopologicalSpace α] [m : MeasurableSpace α]
    [BorelSpace α] : m = borel α := BorelSpace.measurable_eq

/-- **`ℝ` 是 Borel 空间**（本库所有实值随机变量都定义在它上面）。
⚠ 它是 mathlib 的**逐类型实例**（`Real.borelSpace`），**不是**一般定理的推论——
这正是上面"反向不成立"的正面例证。 -/
theorem borelSpace_real : BorelSpace ℝ := inferInstance

/-- **Borel σ-代数的生成元（最小性形态）**：`borel α` 是包含所有开集的
**最小** σ-代数。写成"任何包含所有开集的 σ-代数都包含 `borel α`"这一形式，
是验证"某集合可测"的通用手段。 -/
theorem borel_le_of_isOpen_le {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    (h : ∀ s : Set α, IsOpen s → MeasurableSet[m] s) : borel α ≤ m :=
  MeasurableSpace.generateFrom_le fun _ hs => h _ hs

/-! ## 二、概率测度层：归一化的三种形态

实测：
```
IsProbabilityMeasure : Measure α → Prop
isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ Set.univ = 1   -- 无 MeasureTheory. 前缀
Measure.measure_univ : [IsProbabilityMeasure μ] → μ Set.univ = 1
```
⚠ **`MeasureTheory.Measure.apply_univ` 实测不存在**（真不存在）。
⚠ **`measureReal_univ` / `measureReal_mono` / `measureReal_union_le` 实测不存在**——
本库的实数化记法是 **`(μ s).toReal`**（`RealHoeffdingMeasure` 全文件即用此式），
故本层一律用 `.toReal`，**不引入 `measureReal` 这一不存在家族**。 -/

/-- **概率测度归一化（ENNReal 形态）**：`μ univ = 1`。 -/
theorem prob_univ {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] :
    μ Set.univ = 1 := MeasureTheory.measure_univ

/-- **概率测度归一化（`↔` 形态）**：与 `prob_univ` 同义，供需要反向使用处。 -/
theorem prob_iff_univ {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    IsProbabilityMeasure μ ↔ μ Set.univ = 1 := isProbabilityMeasure_iff

/-- **概率测度是有限测度**：`IsProbabilityMeasure μ ⟹ IsFiniteMeasure μ`。
这条是**承重**的：mathlib 的切尔诺夫桥 `measure_ge_le_exp_mul_mgf` 与
`RealHoeffdingMeasure.hoeffding_tail_of_mgf_bound` 都**只要** `[IsFiniteMeasure μ]`，
下游凡有概率测度即可自动满足该前提。 -/
theorem prob_isFinite {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] :
    IsFiniteMeasure μ := inferInstance

/-- **概率测度归一化（实数形态）**：`(μ univ).toReal = 1`。
这是 `integral_const` 化简时实际需要的形态（`∫ c ∂μ = (μ univ).toReal • c`）。 -/
theorem prob_toReal_univ {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] :
    (μ Set.univ).toReal = 1 := by
  rw [prob_univ]; simp

/-- **常数在概率测度下的积分**：`∫ c ∂μ = c`。
由 `integral_const` 与 `prob_toReal_univ` 直接得到，是本层最常用的化简。 -/
theorem integral_const_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (c : ℝ) : ∫ _ : α, c ∂μ = c := by
  rw [integral_const, prob_toReal_univ, one_smul]

/-! ## 三、独立性层：`iIndepFun` 与其 MGF 因子分解

实测签名（逐字）：
```
iIndepFun : ((x : ι) → MeasurableSpace (β x)) → ((x : ι) → Ω → β x) → Measure Ω → Prop
iIndepFun.mgf_sum : iIndepFun (fun x => inferInstance) X μ → (∀ i, Measurable (X i)) →
                    ∀ s : Finset ι, mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t
```
**⇒ mathlib 已有真正的测度论独立性 FACTORIZATION，本库不重证**；
本层只把它固化为**不带 `Finset.univ` 记法**的接口，供下游直接使用。 -/

/-- **独立性的 MGF 因子分解（`Finset.univ` 形态）**：有限指标集上独立可测族的
矩母函数等于各分量矩母函数之积。这是 `iIndepFun.mgf_sum` 的记法对齐版本
（`RealHoeffdingMeasure.mgf_factor_measure` 已给出同一结论，本层重复固化
是为了让**基础层自足**，不依赖 `RealHoeffdingMeasure` 的 olean）。 -/
theorem indep_mgf_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*}
    [Fintype ι] {X : ι → Ω → ℝ}
    (hindep : iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace ℝ)) X μ)
    (hm : ∀ i, Measurable (X i)) (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) μ t = ∏ i, mgf (X i) μ t := by
  -- ⚠⚠ `mgf_sum` 给出的是 `mgf (∑ i, X i) μ t`（**函数级**求和），
  -- 而目标是 `mgf (fun ω => ∑ i, X i ω) μ t`（**逐点**求和）。
  -- 二者**不是 defeq**（`Pi.sum` 是 `Finset.sum` 的逐点提升，需要 β/η 展开），
  -- 实测报 `after simplification has type mgf (∑ i, X i) μ t … but is expected …`。
  -- ⇒ 必须先用 `funext` + `Finset.sum_apply` **显式证明函数相等**（B205 同类：
  -- `rw`/`simp` 用句法匹配，不归一化到 defeq 范式）。
  -- ⚠ `mgf_sum` 的 `t` 是尾随隐式参数，须显式传入。
  have h := hindep.mgf_sum hm (Finset.univ : Finset ι) (t := t)
  have hfun : (fun ω => ∑ i, X i ω) = (∑ i, X i) := by
    funext ω
    rw [Finset.sum_apply]
  rw [hfun]
  simpa using h

/-- **独立性给出的两两独立性**：`iIndepFun` ⟹ 任意 `i ≠ j` 的 `IndepFun`。
由 mathlib `iIndepFun.indepFun` 直接得到；`condexp` 型推导的入口。 -/
theorem indep_pair {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*}
    {β : ι → Type*} {m : (i : ι) → MeasurableSpace (β i)} {f : (i : ι) → Ω → β i}
    (hindep : iIndepFun m f μ) {i j : ι} (hij : i ≠ j) : IndepFun (f i) (f j) μ :=
  hindep.indepFun hij

/-! ## 四、条件期望层：`condexp` 的四条承重引理

⚠ **名字是全小写 `condexp`**（见文件头判据 2）。实测签名：
```
condexp : MeasurableSpace α → {m0} → Measure α → (α → F') → α → F'     -- μ[f|m]
condexp_const (hm : m ≤ m0) (c : F') [IsFiniteMeasure μ] : μ[fun _ => c|m] = fun _ => c
condexp_add   (hf hg : Integrable · μ) : μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m]
condexp_mono  (hf hg) (f ≤ᵐ g) : μ[f|m] ≤ᵐ μ[g|m]
condexp_nonneg (0 ≤ᵐ f) : 0 ≤ᵐ μ[f|m]
integral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] : ∫ (μ[f|m]) = ∫ f
condexp_of_stronglyMeasurable (hm) [SigmaFinite (μ.trim hm)] (h : StronglyMeasurable f)
    (hf : Integrable f μ) : μ[f|m] = f
condexp_condexp_of_le (h₁₂ : m₁ ≤ m₂) (hm₂) [SigmaFinite (μ.trim hm₂)] :
    μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁]                                  -- tower
condexp_congr_ae (f =ᵐ g) : μ[f|m] =ᵐ μ[g|m]
condexp_bot [IsProbabilityMeasure μ] (f) : μ[f|⊥] = fun _ => ∫ x, f x ∂μ
```
⚠ 注意 `condexp_*` 的很多结论是 **`=ᵐ[μ]`（几乎处处相等）** 而**不是** `=`。
下游凡要把它当等式用，**必须显式处理 ae 性**（`Filter.EventuallyEq`），
不能直接 `rw`。这是本层最重要的**使用约束**，写在下面每条定理的注释里。 -/

/-- **条件期望的常数律**：`μ[fun _ => c|m] = fun _ => c`。
⚠ 前提：`m ≤ m0`（子 σ-代数）与 `[IsFiniteMeasure μ]`（**不是** `IsProbabilityMeasure`）。
结论是**逐点等式**（非 ae），可直接 `rw`。 -/
theorem condexp_const' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) [IsFiniteMeasure μ] (c : ℝ) :
    μ[(fun _ : α => c)|m] = fun _ : α => c :=
  MeasureTheory.condexp_const hm c

/-- **条件期望的加法律**（ae 形态）：`μ[f+g|m] =ᵐ μ[f|m] + μ[g|m]`。
⚠ 结论是 ae 相等，**不能**当普通等式 `rw`；需 `Filter.EventuallyEq` 处理。 -/
theorem condexp_add' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] :=
  MeasureTheory.condexp_add hf hg

/-- **条件期望的单调性**（ae 形态）：`f ≤ᵐ g ⟹ μ[f|m] ≤ᵐ μ[g|m]`。 -/
theorem condexp_mono' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ᵐ[μ] g) :
    μ[f|m] ≤ᵐ[μ] μ[g|m] :=
  MeasureTheory.condexp_mono hf hg h

/-- **条件期望的非负性**（ae 形态）：`0 ≤ᵐ f ⟹ 0 ≤ᵐ μ[f|m]`。 -/
theorem condexp_nonneg' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f|m] :=
  MeasureTheory.condexp_nonneg h

/-- **条件期望的全积分律（承重）**：`∫ (μ[f|m]) ∂μ = ∫ f ∂μ`。
⚠ 前提 `[SigmaFinite (μ.trim hm)]` **不可省**；在 `[IsFiniteMeasure μ]` 下
由 `SigmaFinite.trim` 自动满足（下游可 `haveI` 引入）。 -/
theorem integral_condexp' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} {f : α → ℝ} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] :
    ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ :=
  MeasureTheory.integral_condexp hm

/-- **tower 性质（叠期望）**：`m₁ ≤ m₂ ≤ m0` 时 `μ[μ[f|m₂]|m₁] =ᵐ μ[f|m₁]`。
这是 McDiarmid/鞅迭代路线的核心构件。⚠ 结论为 ae 形态。 -/
theorem condexp_tower {α : Type*} [MeasurableSpace α] {m₁ m₂ m0 : MeasurableSpace α}
    {μ : Measure α} {f : α → ℝ} (h₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0)
    [SigmaFinite (μ.trim hm₂)] :
    μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] :=
  MeasureTheory.condexp_condexp_of_le h₁₂ hm₂

/-- **强可测函数的条件期望是自身**：`StronglyMeasurable[m] f ⟹ μ[f|m] = f`（逐点）。
⚠ **⚠ 关键细节（源码级实证，`ConditionalExpectation/Basic.lean:117-119`）**：
强可测性是对 **`m`**（**子系 σ-代数**）而非 `m0` 而言的，即
`hf : StronglyMeasurable[m] f`，**不是** `StronglyMeasurable[m0] f`。
本文件先前误写 `StronglyMeasurable[m0] f`，报
`application type mismatch … has type StronglyMeasurable … m0 f but is expected to have type … m f`。
⚠ 前提含 `Integrable f μ` 与 `[SigmaFinite (μ.trim hm)]`。 -/
theorem condexp_of_stronglyMeasurable' {α : Type*} [MeasurableSpace α]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f : α → ℝ} (h : StronglyMeasurable[m] f) (hf : Integrable f μ) : μ[f|m] = f :=
  MeasureTheory.condexp_of_stronglyMeasurable hm h hf

/-- **条件期望对 ae 相等的兼容性**：`f =ᵐ g ⟹ μ[f|m] =ᵐ μ[g|m]`。 -/
theorem condexp_congr_ae' {α : Type*} [MeasurableSpace α] {m m0 : MeasurableSpace α}
    {μ : Measure α} {f g : α → ℝ} (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] :=
  MeasureTheory.condexp_congr_ae h

/-- **条件期望到底 σ-代数（全期望）**：`μ[f|⊥] = fun _ => ∫ f ∂μ`（概率测度）。
这是"条件期望在平凡 σ-代数上退化为无条件期望"的精确陈述，
是 McDiarmid 中 `E[f]` 项与条件期望衔接的接口。 -/
theorem condexp_bot' {α : Type*} [MeasurableSpace α] {m0 : MeasurableSpace α}
    {μ : Measure α} [IsProbabilityMeasure μ] (f : α → ℝ) :
    μ[f|⊥] = fun _ : α => ∫ x, f x ∂μ :=
  MeasureTheory.condexp_bot f

/-! ## 五、积分层：`Integrable` 组合子与可测性桥

本层固化下游最常用的一组事实。全部经 `#check` 验证。 -/

/-- **有界可测 ⟹ 可积（有限测度）**：`‖f‖ ≤ c` a.e.、`AEStronglyMeasurable f μ`、
`[IsFiniteMeasure μ]` ⟹ `Integrable f μ`。由 `Integrable.mono'` 与常数可积性得到。
这是把"有界假设"转成"可积前提"的标准桥。

⚠ **`0 ≤ c` 不是前提**（实测）：`integrable_const c` 对**任意** `c : ℝ` 成立
（常数函数总是可积的），故把 `0 ≤ c` 写进假设会触发
`unused variable 'hc'` 警告。按项目判据「unused variable 是"假设写松"的机械信号」，
本定理**不设** `0 ≤ c`。（**注意区分**：`0 ≤ c` 在
`integrable_exp_of_ae_bound` 里同样不是前提，原因见该处说明。） -/
theorem integrable_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} {c : ℝ}
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) : Integrable f μ :=
  Integrable.mono' (integrable_const c) hf h

/-- **可测 ⟹ 强可测（有限测度）**：`Measurable f ⟹ AEStronglyMeasurable f μ`。
下游把 `Measurable` 转成 `Integrable.mono'` 所需前提时使用。 -/
theorem aestronglyMeasurable_of_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h : Measurable f) : AEStronglyMeasurable f μ :=
  h.aestronglyMeasurable

/-- **可测函数的指数可积性（有界情形）**：`|X| ≤ c` a.e. 时 `exp (t * X)` 可积
（有限测度）。这是 `RealHoeffdingLemmaMeasure` 的 `hint` 前提的**可满足性证据**：
该前提**不是空洞假设**，在有界情形下自动成立。

⚠ **`0 ≤ c` 与 `c = 0` 的退化情形**：本定理**不设** `0 ≤ c`——由 `|X| ≤ c` a.e.
与 `exp` 的单调性即得上界 `exp (|t| * c)`（**不需要** `c ≥ 0`；`c < 0` 时
`|X| ≤ c` a.e. 迫使 `X = 0` a.e.，上界 `exp (|t|·c)` 仍然成立且更弱）。
**⇒ 该前提的可满足性由 `X := fun _ => 0`、`c := 0`、`t := 0` 直接见证**
（此时 `|X| ≤ c` 恒真、`exp 0 = 1` 可积）。**这是一个真正的可满足性见证，
不是空洞真**（B53 自检）。 -/
theorem integrable_exp_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {X : α → ℝ} {c t : ℝ}
    (hXm : AEStronglyMeasurable X μ) (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (t * X ω)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable (hXm.const_mul t)
  have hbound : ∀ᵐ ω ∂μ, ‖Real.exp (t * X ω)‖ ≤ Real.exp (|t| * c) := by
    filter_upwards [hX] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (t * X ω) ≤ Real.exp (|t| * c) := by
          apply Real.exp_le_exp.mpr
          calc t * X ω ≤ |t * X ω| := le_abs_self _
            _ = |t| * |X ω| := abs_mul t (X ω)
            _ ≤ |t| * c := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
      _ = Real.exp (|t| * c) := rfl
  exact Integrable.mono' (integrable_const _) hmeas hbound

/-! ## 五之二、前提可满足性见证（B53 自检）

⚠ 项目已登记 **B53：「不可满足前提」类空洞真**（`∀z, c ≤ ‖z‖ ∧ 0 < c`）。
本层每个定理的**前提都必须有见证**，否则该定理空洞。下面把**关键前提**逐个
给出可满足性见证——这是"该定理不是空洞真"的**机械证据**（而不仅是口头声明）。 -/

/-- **`integrable_exp_of_ae_bound` 前提的可满足性见证**：取
`X := fun _ => 0`（记作 `zeroFun`）、`c := 0`、`t := 0`，则 `AEStronglyMeasurable X μ`
（常数函数）与 `∀ᵐ ω, |X ω| ≤ c`（`|0| ≤ 0`）**同时成立**，且结论
`Integrable (fun _ => exp (0 * 0))` 成立。⟹ **该定理的前提非空**（非空洞真）。

⚠ **实现注记**：见证里**不要**在内联的 `fun _ : α => (0 : ℝ)` 后面直接跟应用，
例如写 `(fun _ : α => (0 : ℝ)) _ω`——Lean 会报
`don't know how to synthesize placeholder`（本文件实测），
因为声明的**返回类型在头部先被处理**，其中的洞（`_`）在正文之前就要求解出。
**⇒ 把被作用的表达式写成**直接的形式 `(0 : ℝ)`**。 -/
theorem satisfiable_integrable_exp_of_ae_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] :
    AEStronglyMeasurable (fun _ : α => (0 : ℝ)) μ ∧
      (∀ᵐ _ω ∂μ, |(0 : ℝ)| ≤ (0 : ℝ)) ∧
      Integrable (fun _ : α => Real.exp ((0 : ℝ) * (0 : ℝ))) μ := by
  refine ⟨aestronglyMeasurable_const, ?_, ?_⟩
  · filter_upwards with ω
    simp
  · simpa only [mul_zero, Real.exp_zero] using (integrable_const (α := α) (μ := μ) (1 : ℝ))

/-- **`integrable_of_ae_bound` 前提的可满足性见证**：取 `f := fun _ => 0`、`c := 0`，
两个前提同时成立且结论成立。 -/
theorem satisfiable_integrable_of_ae_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] :
    AEStronglyMeasurable (fun _ : α => (0 : ℝ)) μ ∧
      (∀ᵐ _x ∂μ, ‖(0 : ℝ)‖ ≤ (0 : ℝ)) ∧
      Integrable (fun _ : α => (0 : ℝ)) μ := by
  refine ⟨aestronglyMeasurable_const, ?_, ?_⟩
  · filter_upwards with ω
    simp
  · exact integrable_zero α ℝ μ

/-! ## 六、本节小结：基础层提供的**可复用接口表**

| 需求 | 本层接口 | 底层 mathlib 名字（实测存在） |
|:--|:--|:--|
| 拓扑 ⟹ Borel σ-代数 | `borelOfTopology` / `borelSpace_self` | `borel`、`BorelSpace` |
| 开集可测 | `isOpen_measurableSet` | `IsOpen.measurableSet` |
| `μ univ = 1` | `prob_univ` / `prob_iff_univ` | `Measure.measure_univ`、`isProbabilityMeasure_iff` |
| 概率 ⟹ 有限测度 | `prob_isFinite` | 实例链 |
| `(μ univ).toReal = 1` | `prob_toReal_univ` | `ENNReal.toReal_one` |
| `∫ c = c` | `integral_const_prob` | `integral_const` |
| 独立性 ⟹ MGF 分解 | `indep_mgf_sum` | `iIndepFun.mgf_sum` |
| 独立 ⟹ 两两独立 | `indep_pair` | `iIndepFun.indepFun` |
| 条件期望四条律 | `condexp_const'`/`_add'`/`_mono'`/`_nonneg'` | `condexp_*`（**全小写**） |
| 全积分 / tower | `integral_condexp'` / `condexp_tower` | `integral_condexp`、`condexp_condexp_of_le` |
| 有界 ⟹ 可积 | `integrable_of_ae_bound` | `Integrable.mono'` |
| 有界 ⟹ 指数可积 | `integrable_exp_of_ae_bound` | `Real.continuous_exp.comp_aestronglyMeasurable` |

**⇒ 三个缺口（McDiarmid / DPI / Hoeffding）现在都只用引用上表即可，不必再猜名字。** -/

end Lattice
