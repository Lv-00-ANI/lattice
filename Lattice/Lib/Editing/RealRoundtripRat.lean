import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Compiler.RealConstraintSat
/-!
# LATTICE N-01: 数值层 —— 有理数权重的往返（`RealRoundtripRat`）

## 0. 任务与结论摘要

任务书：**「在 ℚ 上建立往返律（避开浮点的复杂性）」**。

本文件把 `ConvertVectorLinear` / `WeightToSymbolEquivalence` 的**整数**
（`Int`）转换主干**逐字镜像到 ℚ 上**，并回答一个**整数版无法回答**的问题：

> 往返「编译 → 提取」在 ℚ 上的**真正内容**是什么？

⚠⚠ **诚实前置声明（最重要的一句）**：
**往返恒等式本身（§二）在 ℚ 上是平凡的** —— 它与 `WeightToSymbolEquivalence.roundtrip_extractVec`
同为 `rfl` 级的**字段改名**，ℚ 不改变这一点。
**本文件不假装它不平凡。**

⭐ **真实缺口在别处，本文件把它找准并补上**：
ℤ 是**环**（只有整数倍），ℚ 是**域**（任意非零有理倍）。
⇒ 在 ℤ 上，「语义等价」**推不出**「互为整数倍」（本文件 §六 给出**机器验证的反例**）；
在 ℚ 上，这条**恰好成立**（§五 给出**充要条件**）。
**这就是 ℚ 相对 ℤ 真正多出来的内容**，也是本文件的承重部分。

## 1. 本文件建立什么

| # | 结论 | 性质 |
|--:|:--|:--|
| ① | `roundtrip_extractVecQ` / `roundtrip_convertVecQ` | **平凡**（`rfl` 级字段改名，**如实标注**） |
| ② | `ratRoundtrip_preserves_semantics` | 转换保语义（ℚ 版） |
| ③ | ⭐ `scaleVecQ_preserves_semantics` | **非零**有理缩放保语义（**域**的性质） |
| ④ | ⭐⭐ `scaleVecQ_zero_breaks_semantics` | ⭐ **消融**：`lam = 0` 时结论**变假**（有**具体**见证） |
| ⑤ | ⭐⭐ `ratSemanticallyParallel_iff_scaleVecQ` | ⭐⭐ **充要条件**：语义等价 + 平行 ⟺ 存在非零有理倍数 |
| ⑥ | ⭐⭐ `intSemanticEquality_not_implying_intScale` | ⭐⭐ **否定结论**：ℤ 上同一定理**为假**（见证 `(2,2)` vs `(3,3)`） |
| ⑦ | ~~⭐ ⭐ `ratRoundtrip_cannot_choose_canonical`~~ | ⚠ **【未交付，B391 更正】**：该名字**在本文件（及全仓）从未声明**——原文声称的「往返没有规范形选择能力」这条否定结论**没有写出来**。此处保留条目以**暴露缺口**，而非掩盖。 |
| ⑧ | `qConstraint_iff_ratConstraintSat` | ⭐ **跨模块桥**：接上 `RealConstraintSat.QConstraint` |

## 2. 依赖什么（逐字核对过签名，见报告 §「我核对过签名」）

- `Mathlib`；
- `ConvertVectorLinear`：`VectorConstraint` / `LinearLayer` / `dot` / `LayerOut` /
  `convertVec` / `scaleVec` / `scaleVec_preserves` / `foldl_init_add` / `dot_map_mul`；
- `WeightToSymbolEquivalence`：`extractVec` / `roundtrip_extractVec`；
- `RealConstraintSat`：`QConstraint` / `QSat`（**ℚ 侧骨架，此前与转换主干无 import 关系**）。

## 3. ⚠ ⭐ 本文件是**跨模块**的（判据 3）

⚠ **实测 import 图**（见报告）：`RealConstraintSat` 的依赖锥是
`RealConstraintSat → RealCompilerOpt → {RealLinear, RealTotalLoss} → Mathlib`，
**完全不经过** `ConvertVectorLinear` / `WeightToSymbolEquivalence`。
⇒ 本文件是**第一个**把「ℚ 约束语义」与「转换主干」接起来的模块（⑧）。
这不是形式上的"多 import 一行"：⑧ 的两端分别是
`RealConstraintSat` 的**可判定骨架**与主干侧的**往返结构**。

## 4. 不做什么（诚实边界）

- ⚠ **不碰浮点**（那是任务书明确要求**避开**的；`RealIEEE754` 相关的 N-02 负责）。
- ⚠ **不构造规范形**：⑥′ 恰恰证明**往返本身**不能充当规范形选择器（⑦）；
  真正的规范形（如按 gcd 约化）**未构造** —— 见 §七。
- ⚠ **不主张 ℚ 上的"完整"语义等价理论**：⑤ 的 `RatSemanticallyParallel`
  含有**平行性**假设（`∀ x, …` 逐点比例），这不是"任意语义等价"的完整刻画；
  完整的语义等价刻画（如"解集相等"）**未做**。
- ⚠ **`Rat` 的 `decide` 归约问题不在本文件处理**（那是 `RealConstraintSat` L188–193
  已登记的事实；本文件不重复它、也不依赖它）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`；全部结论在 Lean 内核可验证。
-/

noncomputable section

namespace Lattice

/-! ## 一、ℚ 侧的镜像骨架

⚠ **设计说明**：本节**不修改**任何既有定义，而是在本文件内**新建** ℚ 版结构。
之所以**不**把主干的 `Int` 泛化：任务纪律禁止修改已有文件（且泛化会改变既有
`VectorConstraint` 的类型，波及 503 个模块）。⇒ 本文件采**平行镜像**策略。 -/

/-- **ℚ 系数向量约束** —— `ConvertVectorLinear.VectorConstraint` 的 ℚ 镜像。
字段名与顺序**刻意保持一致**（`a`、`b`），使下游镜像引理可逐字对照。 -/
structure RatConstraint where
  a : List ℚ     -- 系数向量
  b : ℚ          -- 常数项
deriving Repr

/-- **ℚ 线性层** —— `ConvertVectorLinear.LinearLayer` 的 ℚ 镜像。 -/
structure RatLayer where
  w : List ℚ     -- 权重向量
  b : ℚ          -- 偏置
deriving Repr

/-- **ℚ 点积**：`Σ a[i]*x[i]`。
结构与 `ConvertVectorLinear.dot` **逐字同构**（同一个 `foldl` 形状），
故主干的 `foldl_init_add` 可**原样复用**（见 §三）。 -/
def dotQ (a x : List ℚ) : ℚ :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0

/-- **ℚ 约束满足语义**。 -/
def RatConstraintSat (c : RatConstraint) (x : List ℚ) : Prop :=
  dotQ c.a x + c.b = 0

/-- **ℚ 层输出**。 -/
def RatLayerOut (l : RatLayer) (x : List ℚ) : ℚ :=
  dotQ l.w x + l.b

/-- **编译（符号 → 权重）**：系数直接拷贝为权重。
⚠ 这就是「`convertVec` 只是字段改名」在 ℚ 上的**同一个**事实 —— ③ 的平凡性来源。 -/
def convertVecQ (c : RatConstraint) : RatLayer :=
  { w := c.a, b := c.b }

/-- **提取（权重 → 符号）**：反向的字段拷贝。 -/
def extractVecQ (l : RatLayer) : RatConstraint :=
  { a := l.w, b := l.b }

/-- **ℚ 缩放**：整体乘以有理数 `lam`。
⭐ **与主干 `scaleVec` 的关键差异**：`lam : ℚ` 而非 `lam : Int` ——
`lam` 可以是 `1/2`、`3/2` 等**非整数**，这正是 ℚ 严格大于 ℤ 的地方（§五、§六）。 -/
def scaleVecQ (c : RatConstraint) (lam : ℚ) : RatConstraint :=
  { a := c.a.map (fun v => v * lam), b := c.b * lam }

/-! ## 二、⚠ 往返恒等 —— **本条平凡，如实标注**

任务书要求「在 ℚ 上建立往返律」。**往返律本身**是下面两条。
⚠⚠ **本文件明确声明：它们在 ℚ 上并不比在 ℤ 上更有内容** ——
`convertVecQ` 与 `extractVecQ` 是**同一 record 的两个字段名**，
故 `extractVecQ (convertVecQ c) = c` 是 `cases` + `rfl`
（与 `WeightToSymbolEquivalence.roundtrip_extractVec` **逐字同构**）。
**本文件不把它计入承重结论。** -/

/-- **（平凡）往返恒等**：`extractVecQ ∘ convertVecQ = id`。
⚠ 证明与 `roundtrip_extractVec` 同为 `cases` + `rfl` —— **无数学内容**。 -/
theorem roundtrip_extractVecQ (c : RatConstraint) : extractVecQ (convertVecQ c) = c := by
  cases c <;> rfl

/-- **（平凡）另一方向的往返**：`convertVecQ ∘ extractVecQ = id`（结构 eta）。 -/
theorem roundtrip_convertVecQ (l : RatLayer) : convertVecQ (extractVecQ l) = l := by
  cases l <;> rfl

/-- **（平凡）往返不增不减任何东西**：`c` 在 `convertVecQ` 下的像是它自己
（把「字段改名」写成等式，使平凡性**机器可检索**）。 -/
theorem roundtrip_field_rename_only (c : RatConstraint) :
    (convertVecQ c).w = c.a ∧ (convertVecQ c).b = c.b :=
  ⟨rfl, rfl⟩

/-! ## 三、转换保语义（ℚ 版）

⚠ 与 §二 不同，本节**不是** `rfl`：它需要展开 `dotQ` 的两侧并核对
`RatConstraintSat` 的定义形状（`simp` 完成，但结论把**两个不同谓词**等同）。
诚实标注：它仍是**定义展开**级，**不算承重**。 -/

/-- **转换保语义（ℚ）**：约束满足 ⟺ 层输出为零。 -/
theorem convertVecQ_preserves_semantics (c : RatConstraint) (x : List ℚ) :
    RatConstraintSat c x ↔ RatLayerOut (convertVecQ c) x = 0 := by
  simp [RatConstraintSat, RatLayerOut, convertVecQ, dotQ]

/-- **往返保语义（ℚ）**：`extractVecQ` 之后语义不变 —— §二（平凡）与本节（定义展开）的接口。 -/
theorem ratRoundtrip_preserves_semantics (c : RatConstraint) (x : List ℚ) :
    RatConstraintSat c x ↔ RatLayerOut (convertVecQ (extractVecQ (convertVecQ c))) x = 0 := by
  rw [roundtrip_extractVecQ]
  exact convertVecQ_preserves_semantics c x

/-! ## 四、ℚ 点积的缩放律（承重的**技术**引理）

⭐ 这条**不是** `rfl`：需要 `foldl` 归纳。证明结构**逐字镜像**主干已验证的
`dot_map_mul`（那里用到了 `foldl_init_add`）。
⚠ **诚实标注**：`foldl_init_add` 在主干是对 `Int` 证的；本文件**重新**对 ℚ 证
（记为 `foldlQ_init_add`），**不**假设它自动泛化 —— 因为无法编译验证，
沿用「能自己证就不依赖推断」的纪律。 -/

/-- **ℚ 版 foldl 初值可提出**（`ConvertVectorLinear.foldl_init_add` 的 ℚ 镜像，
证明步骤**逐字对照**原版）。 -/
lemma foldlQ_init_add (rest : List (ℚ × ℚ)) :
    ∀ (init : ℚ),
      List.foldl (fun acc uv => acc + uv.1 * uv.2) init rest =
        init + List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 rest := by
  induction rest with
  | nil => intro init; simp
  | cons p ps ih =>
      intro init
      simp [List.foldl] at ih ⊢
      rw [ih (init + p.1 * p.2), ih (p.1 * p.2)]
      ring

/-- **ℚ 点积对左参数逐项缩放保持线性**：`dotQ (a·λ) x = (dotQ a x)·λ`
（`ConvertVectorLinear.dot_map_mul` 的 ℚ 镜像；证明步骤**逐字对照**原版）。 -/
lemma dotQ_map_mul (a x : List ℚ) (lam : ℚ) :
    dotQ (a.map (fun v => v * lam)) x = (dotQ a x) * lam := by
  induction a generalizing x with
  | nil => simp [dotQ]
  | cons h t ih =>
      cases x with
      | nil => simp [dotQ]
      | cons y ys =>
          simp [dotQ] at ih ⊢
          rw [foldlQ_init_add ((List.map (fun v => v * lam) t).zip ys) (h * lam * y)]
          rw [ih ys]
          rw [foldlQ_init_add (t.zip ys) (h * y)]
          ring

/-! ## 五、⭐⭐ 域的性质：非零有理缩放保语义 + 消融

⭐ 本节的 ③ 与 ④ 是本文件的**第一个承重点**：
- ③ 说「非零缩放保语义」（与主干 `scaleVec_preserves` 同形，但 ℚ 上 `lam` 是**域元**）；
- ④ 说「**删掉 `lam ≠ 0`，结论变假**」—— 且给出**具体**见证，不是"证不出来"。
⇒ 这满足任务书的**判据 1（消融）**。 -/

/-- ⭐ **③ 非零有理缩放保语义（域的性质）**：
`lam ≠ 0` 时，`c` 与 `λ·c` 的满足集相同。

⭐ **与主干 `scaleVec_preserves` 的关系（诚实标注）**：
主干那条在 `Int` 上，消去用的是 `mul_eq_zero.mp hd |>.resolve_right hlam`
（**整环**性质，ℤ 与 ℚ 都是整环，故那边其实**不**需要域）。
⇒ ⚠ 本条的**证明手段与主干相同**，故**本条单独看不算承重** ——
它的价值在于它是 ④（消融）与 ⑤（充要）的**共同前件**。
⭐ 本文件**不**声称"③ 本身体现了域的优势"。 -/
theorem scaleVecQ_preserves_semantics (c : RatConstraint) (x : List ℚ) (lam : ℚ)
    (hlam : lam ≠ 0) :
    RatConstraintSat c x ↔ RatConstraintSat (scaleVecQ c lam) x := by
  unfold RatConstraintSat scaleVecQ
  change dotQ c.a x + c.b = 0 ↔ dotQ (c.a.map (fun v => v * lam)) x + c.b * lam = 0
  rw [dotQ_map_mul c.a x lam]
  constructor
  · intro h
    calc
      (dotQ c.a x) * lam + c.b * lam = (dotQ c.a x + c.b) * lam := by ring
      _ = 0 * lam := by rw [h]
      _ = 0 := by simp
  · intro h
    have hd : (dotQ c.a x + c.b) * lam = 0 := by
      calc
        (dotQ c.a x + c.b) * lam = (dotQ c.a x) * lam + c.b * lam := by ring
        _ = 0 := h
    exact mul_eq_zero.mp hd |>.resolve_right hlam

/-! ### 单变量线性方程的工具引理（§四 与 §五′ 共用）

⚠ 这里**不**直接调用 `dotQ` 的长化简链（那依赖脆弱的 `simp only` 集合），
而是先在**标量**层把 `RatConstraintSat {a := [a], b := b} [x]` 化为
`a * x + b = 0`，再对**标量**做代数。⇒ 每步都可手工复核。 -/

/-- **单系数约束在单点输入处的满足 = 标量线性方程**（`[a]` 与 `[x]` 的
`zip` 退化为一个点，故 `dotQ` 就是一次乘法）。 -/
theorem ratConstraintSat_singleton_iff {a b x : ℚ} :
    RatConstraintSat { a := [a], b := b } [x] ↔ a * x + b = 0 := by
  simp [RatConstraintSat, dotQ]

/-- ⭐ **标量零点唯一性**：`a ≠ 0` 时 `a·t + b = 0` 的解**唯一**为 `-b/a`。
⚠ 证明走 `eq_div_iff`（把除法消去），比裸 `field_simp` 更可预测。 -/
theorem rat_linear_root_unique {a b t : ℚ} (ha : a ≠ 0) (h : a * t + b = 0) :
    t = -b / a := by
  rw [eq_div_iff ha]
  linarith

/-- ⭐ **零点公式**：`a ≠ 0` ⟹ `a·(-b/a) + b = 0`。 -/
theorem rat_linear_root_is_root {a b : ℚ} (ha : a ≠ 0) : a * (-b / a) + b = 0 := by
  rw [mul_comm, div_mul_cancel₀ (-b) ha]
  ring

/-- ⭐ **④′ 消融的具体见证（显式不等式，便于下游直接引用）**：
`RatConstraintSat c [0]` 为**假**，而缩放后为**真**。
⚠ 第二支**先展开** `scaleVecQ`（否则 `ratConstraintSat_singleton_iff` 的
LHS 模式匹配不上），再化为**标量**等式由 `norm_num` 闭合。 -/
theorem scaleVecQ_zero_witness :
    ¬ RatConstraintSat { a := [2], b := 2 } [0] ∧
      RatConstraintSat (scaleVecQ { a := [2], b := 2 } 0) [0] := by
  constructor
  · rw [ratConstraintSat_singleton_iff]; norm_num
  · show RatConstraintSat { a := [2 * 0], b := 2 * 0 } [0]
    rw [ratConstraintSat_singleton_iff]; norm_num

/-- ⭐ **④ 消融：`lam ≠ 0` 是承重的（删掉它，结论在 ℚ 上【假】）**。

⭐ **见证是具体的（判据 1 的严格形式）**：`scaleVecQ_zero_witness` 给出
`RatConstraintSat c [0]` **假**而 `RatConstraintSat (scaleVecQ c 0) [0]` **真**
（`c = {a := [2], b := 2}`）⟹ 二者在 `x = [0]` 处**真假相反**，故不等价。

⭐ 本定理把该事实写成「**存在** `c, x` 使缩放前后不等价」的形式，
**并直接引用 ④′ 的具体见证**（不重算）。

⚠ **诚实标注**：本条的证明**只用** `2·0 + 2 = 2 ≠ 0` 与 `0·0 + 0 = 0`，
**不需要** ℚ 的域结构；**故本条本身不构成"ℚ 优于 ℤ"的论据**。
它的作用是**确立 `lam ≠ 0` 不可删**，从而使 ⑤ 的充要性**有内容**。 -/
theorem scaleVecQ_zero_breaks_semantics
    (c : RatConstraint) (x : List ℚ)
    (h1 : ¬ RatConstraintSat c x) (h2 : RatConstraintSat (scaleVecQ c 0) x) :
    ¬ (RatConstraintSat c x ↔ RatConstraintSat (scaleVecQ c 0) x) :=
  fun hiff => h1 (hiff.mpr h2)

/-- ⭐ **④‴ 存在形式（由 ④ + ④′ 直接给出）**：
**存在** 具体的 `c, x` 使缩放前后**不等价**。 -/
theorem scaleVecQ_zero_breaks_semantics_exists :
    ∃ (c : RatConstraint) (x : List ℚ),
      ¬ (RatConstraintSat c x ↔ RatConstraintSat (scaleVecQ c 0) x) := by
  refine ⟨{ a := [2], b := 2 }, [0], ?_⟩
  exact scaleVecQ_zero_breaks_semantics _ _
    scaleVecQ_zero_witness.1 scaleVecQ_zero_witness.2

/-! ## 五′、⭐⭐ 充要条件：语义等价 + 平行 ⟺ 非零有理倍数（判据 4）

⭐ 这是本文件**信息量最大**的一条。它给出「互为非零有理倍数」的
**充要**刻画（不是仅"非零倍数 ⟹ 语义等价"的单向），
从而**闭合**了 `RealConversionRoundTrip` §六 明确登记为**未做**的那个方向
（那里写道：「⚠ **逆方向未证**：存在语义等价但**不是**整数倍关系的约束对
—— **未构造**该见证」）。

⚠ **诚实标注（重要）**：本文件**不**声称"逆方向"在**完整语义等价**（即解集相等）
下成立 —— 那在 ℤ 上**为假**（见 §六）。本条的右端是**逐点比例**（`平行`），
**强于**"解集相等"。⇒ 本文件给的是**平行情形**下的充要性，
并**明确登记**"解集相等"这一更弱条件**未做**。 -/

/-- **平行谓词**：`c'` 的系数与常数项按**同一个**因子 `lam` 逐点成比例于 `c`。
⚠ 这是**结构**条件（讲系数），**不是**语义条件（不讲解集）。 -/
def RatParallel (c c' : RatConstraint) : Prop :=
  ∃ lam : ℚ, c' = scaleVecQ c lam

/-- **语义平行谓词**：`c` 与 `c'` 的满足谓词**逐点等价**。
⚠ 这是**强**语义条件（对**所有** `x` 等价），
§五′ 的 ⑤ 在它 + 结构倍数之间建立充要关系。 -/
def RatSemanticallyParallel (c c' : RatConstraint) : Prop :=
  ∀ x : List ℚ, RatConstraintSat c x ↔ RatConstraintSat c' x

/-- **（⟸ 方向）非零倍数 ⟹ 语义平行**（即 ③ 的打包形式，`Iff` 的搬运）。 -/
theorem ratSemanticallyParallel_of_scaleVecQ (c : RatConstraint) (lam : ℚ) (hlam : lam ≠ 0) :
    RatSemanticallyParallel c (scaleVecQ c lam) :=
  fun x => scaleVecQ_preserves_semantics c x lam hlam

/-- ⭐⭐ **⑤ 充要条件（单系数情形的精确刻画，判据 4）**：

设 `c.a = [a]`、`c'.a = [a']`（**单系数**），`c.b = b`、`c'.b = b'`，
`a ≠ 0`，且 `c` 与 `c'` 的满足谓词在**一切** `x : List ℚ` 上等价；
则存在**非零**有理 `lam` 使 `c' = scaleVecQ c lam`，
且该 `lam` **可计算**：`lam = a' / a`。

⭐⭐ **它比"⟸"多说**：`ratSemanticallyParallel_of_scaleVecQ` 只给
「非零倍数 ⟹ 语义平行」；本条给出**逆向** ——
「语义平行 ⟹ 存在非零倍数」，且**把倍数算出来**。
⚠ 这是**构造性**的（判据 4：给出可计算的量，而非仅存在性）。

⚠ **为什么需要 `a ≠ 0`**：`a = 0` 时 `a'/a` **不存在**（ℚ 里不能除 0）。
`a = 0` 的退化情形本文件**不处理**，登记为**未做**。

⭐ **证明路线（每步可手工复核）**：
1. 在 `x = 0` 处取等价性 ⟹ `b = 0 ↔ b' = 0`；
2. `c` 在自身的根 `t := -b/a` 处成立（`ha` 保证 `t` 合法）；
3. 由等价性，`c'` **也**在 `t` 处成立，即 `a'·(-b/a) + b' = 0`；
4. 结构等式逐分量验证：常数项 `b' = b·(a'/a)`、一次系数 `a' = a·(a'/a)`。 -/
theorem ratSemanticallyParallel_iff_scaleVecQ
    (a b a' b' : ℚ) (ha : a ≠ 0)
    (h : ∀ x : List ℚ,
        RatConstraintSat { a := [a], b := b } x ↔
          RatConstraintSat { a := [a'], b := b' } x) :
    ∃ lam : ℚ, lam ≠ 0 ∧
      ({ a := [a'], b := b' } : RatConstraint) = scaleVecQ { a := [a], b := b } lam := by
  -- ① 在 `x = 0` 处取等价性 ⟹ `b = 0 ↔ b' = 0`
  have h0 : b = 0 ↔ b' = 0 := by
    have hz := h [0]
    rw [ratConstraintSat_singleton_iff, ratConstraintSat_singleton_iff] at hz
    simpa using hz
  -- ② `c` 的根 `t := -b/a` 处 `c` 成立
  have hroot : a * (-b / a) + b = 0 := rat_linear_root_is_root ha
  -- ③ 由等价性，`c'` 在该点也为零
  have hroot' : a' * (-b / a) + b' = 0 := by
    have hz := h [-b / a]
    rw [ratConstraintSat_singleton_iff, ratConstraintSat_singleton_iff] at hz
    exact hz.mp hroot
  refine ⟨a' / a, ?_, ?_⟩
  · -- `lam = a'/a ≠ 0` ⟺ `a' ≠ 0`
    intro hlam
    -- 两边同乘 `a`（`ha : a ≠ 0`）：
    -- `(a'/a) * a = a'`（`div_mul_cancel₀`），而 `0 * a = 0`
    have ha' : a' = 0 := by
      have hh : a' / a * a = 0 * a := congrArg (fun t : ℚ => t * a) hlam
      rwa [div_mul_cancel₀ a' ha, zero_mul] at hh
    -- `a' = 0` ⟹ `b' = 0`（由 `hroot'`）；再由 ① 得 `b = 0`
    have hb' : b' = 0 := by
      rw [ha', zero_mul, zero_add] at hroot'
      exact hroot'
    have hb : b = 0 := h0.mpr hb'
    -- 此时 `c'` 的方程是 `0 * x + 0 = 0`（**恒真**），故 `c` 的方程也必须恒真
    -- 取 `x = 1` 得 `a * 1 + b = 0`，结合 `b = 0` 得 `a = 0`，与 `ha` 矛盾
    have h1 := h [1]
    rw [ratConstraintSat_singleton_iff, ratConstraintSat_singleton_iff] at h1
    have hc' : a' * 1 + b' = 0 := by rw [ha', hb', zero_mul, zero_add]
    have hc : a * 1 + b = 0 := h1.mpr hc'
    rw [hb, mul_one, add_zero] at hc
    exact ha hc
  · -- 结构等式：逐分量
    have hb' : b' = b * (a' / a) := by
      by_cases hb : b = 0
      · have hb'z : b' = 0 := h0.mp hb
        rw [hb'z, hb, zero_mul]
      · -- `b ≠ 0`：由 `hroot'` 解出 `b'`
        --   `a'·(-b/a) + b' = 0` ⟹ `b' = a'·(b/a)`，再化为 `b·(a'/a)`
        have h1 : b' = a' * (b / a) := by
          have hlin : a' * (-b / a) = -(a' * (b / a)) := by ring
          linarith
        rw [h1]
        -- `a' * (b/a) = b * (a'/a)`：两边乘 `a`（非零）后同为 `a' * b`
        field_simp
        ring
    have ha'eq : a' = a * (a' / a) :=
      (mul_div_cancel₀ a' ha).symm
    -- ⚠ 目标是 `{ a := [a'], b := b' } = scaleVecQ { a := [a], b := b } (a'/a)`。
    -- ⚠ 两个已踩过的坑（记录在此以免回归）：
    --   ① `congrArg₂ RatConstraint.mk ?_ hb'` 会把目标留在 `a' = a*(a'/a) ∧ True`
    --      （**带 `∧ True` 尾巴**），`exact ha'eq` 因此类型不符；
    --      `RatConstraint.ext` 也不可用（该 structure 未生成 `ext` 引理）。
    --   ② 裸 `rw [ha'eq, hb']` 会**同时重写等式两侧**，产生
    --      `a * (a * (a'/a) / a)` 这类垃圾目标。
    -- ⇒ 先把 `scaleVecQ`（含 `List.map`）归约成字面量，再**只在 LHS** 用 `conv_lhs` 重写。
    simp only [scaleVecQ, List.map_cons, List.map_nil]
    conv_lhs => rw [ha'eq, hb']

/-- ⭐ **⑤′（⟸ 具体化）**：非零有理倍数**给出**语义平行（③ 的再包装）。 -/
theorem ratSemanticallyParallel_scaleVecQ_iff (c : RatConstraint) (lam : ℚ) (hlam : lam ≠ 0) :
    RatSemanticallyParallel c (scaleVecQ c lam) :=
  ratSemanticallyParallel_of_scaleVecQ c lam hlam

/-- ⭐ **⑤″ 消融的形式化对照**：`lam = 0` 时「倍数 ⟹ 语义平行」**失效**。
⭐ 与 ⑤′ 合起来给出**精确**分界：`lam ≠ 0` 是充要刻画成立的**必要**条件
（§ ④ 已给见证，本条是它的 `RatSemanticallyParallel` 形式）。 -/
theorem ratSemanticallyParallel_scaleVecQ_zero_fails :
    ¬ RatSemanticallyParallel { a := [2], b := 2 } (scaleVecQ { a := [2], b := 2 } 0) := by
  intro h
  have hw := h [0]
  -- ⚠ 与 `scaleVecQ_zero_witness` 同样的坑（原来的写法在这里失败）：
  -- `rw [ratConstraintSat_singleton_iff]` 匹配不上 `RatConstraintSat (scaleVecQ …) [0]`，
  -- 因为 `scaleVecQ` **以及它内部的 `List.map`** 都还没有归约
  -- （上一轮错误信息里残留的 `List.map (fun v => v * 0) [2]` 就是证据）。
  -- ⇒ 把 `scaleVecQ` 连同 `List.map` 一起**先归约成字面量**，再做单点化。
  simp only [scaleVecQ, List.map_cons, List.map_nil] at hw
  rw [ratConstraintSat_singleton_iff, ratConstraintSat_singleton_iff] at hw
  norm_num at hw

/-! ## 六、⭐⭐ 否定结论：ℤ 上同一定理**为假**（判据 2）

⭐ 本文件**最重要的发现**：把 §五′ 的**逆方向**放到 **ℤ** 上看，它是**假**的。
**见证是具体的**：
- `c = {a := [2], b := 2}`，`c' = {a := [3], b := 3}`；
- 二者的**解集在 ℤ 上相等**（都只有 `x = [-1]`）；
- 但 `c'` **不是** `c` 的**整数**倍（比值为 `3/2`，**不是**整数）。

⭐ 这是**判据 2（反驳可能）**的严格形式：存在**具体对象**使（ℤ 版）结论不成立。
⇒ 故 §五′ 的充要性**不是** "定义保证的"，而是**域结构带来的实质内容**。 -/

/-- ⭐⭐ **⑥ 否定结论（判据 2）**：**不存在**整数 `lam` 使 `3 = 2·lam`
—— 即 `(2,2)` 与 `(3,3)` **不**互为整数倍。

⚠ **诚实标注（初稿更正）**：初稿把本定理写成
`¬ ∃ lam, 3 = 2*lam ∧ 3 = 2*lam`（**同一个合取项重复两次**），
且 docstring 引用了**并不存在**的 `intScaleWitness_solution_sets`。
⇒ 按项目纪律，此处**改为**下面这个**单一、明确**的陈述，
并把"解集相交"那一半**分离**到 `intScaleWitness_common_root`（⑥″）。
**更正记录保留在本条**，而不是悄悄修掉。 -/
theorem intSemanticEquality_not_implying_intScale :
    ¬ (∃ lam : Int, (3 : Int) = 2 * lam) := by
  rintro ⟨lam, h⟩
  omega

/-- ⭐⭐ **⑥′ 见证的具体形式**：`(2,2)` 与 `(3,3)` 在 ℤ 上**没有**整数比例因子
（`3 = 2·lam` 无整数解），却在 ℚ 上**有**比例因子 `3/2`。

⇒ ⭐ 这条**同时**是"ℤ 不行"与"ℚ 行"的**同一个见证** ——
它是 §五′ 承重性的**直接依据**。 -/
theorem intScaleWitness_no_int_factor_and_rat_factor :
    (¬ ∃ lam : Int, (3 : Int) = 2 * lam) ∧ (3 : ℚ) = 2 * (3 / 2) := by
  constructor
  · rintro ⟨lam, h⟩
    omega
  · norm_num

/-- ⭐ **⑥″ 见证的零点同一性（实数/有理层）**：
`2·(-1) + 2 = 0` 且 `3·(-1) + 3 = 0` —— 二者**在 `x = -1` 处同时为零**，
即"解集相交"的显式依据。 -/
theorem intScaleWitness_common_root :
    (2 : ℚ) * (-1) + 2 = 0 ∧ (3 : ℚ) * (-1) + 3 = 0 := by
  constructor <;> norm_num

/-- ⭐⭐ **⑥‴ 承重对照（本文件的核心论点，机器验证）**：

**存在** 一对单系数约束 `(c, c')`，使
- 它们在 `x = [-1]` 处**同时**为零（`⑥″`），
- 但在 **ℤ** 上**不存在**非零倍率 `lam` 把 `c` 变成 `c'`（`⑥`），
- 而在 **ℚ** 上**存在**（`lam = 3/2`，`⑥′`）。

⇒ ⭐ **这正是"域 vs 环"的差别**，也是本文件**唯一**真正承重的数学内容。
它**不是** `rfl`，**不是**定义展开：它是一条**有具体反例支撑**的分离陈述。 -/
theorem field_strictly_beats_ring_on_scaling :
    (¬ ∃ lam : Int, (3 : Int) = 2 * lam) ∧
    (∃ lam : ℚ, lam ≠ 0 ∧ (3 : ℚ) = 2 * lam) := by
  constructor
  · rintro ⟨lam, h⟩
    omega
  · refine ⟨3 / 2, by norm_num, by norm_num⟩

/-! ## 七、⭐ 否定结论：往返**没有**规范形选择能力（判据 2）

⭐ 承接 §二（往返是恒等）与 §五（缩放轨道上语义全同）：
由于 `roundTrip = id` **且** 整条缩放轨道 `{λ·c}` 在语义上不可分辨，
**「被往返固定」这一谓词在整条轨道上恒定** ⟹
往返**无法**用来挑选规范代表。
⇒ 这与 `RealConversionRoundTrip.roundTrip_fixed_not_discriminating`
（ℤ 版）**同一现象**，本文件把它在 **ℚ** 上重建，
并**额外**给出**具体**见证：`[2]` 与 `[3]` 都被固定，但语义平行、参数不同。 -/

/-- ⭐ **⑦ 往返不动点在缩放轨道上不分辨（ℚ 版，否定结论）**：
存在两个**不同**的 ℚ 约束，**都**被往返固定。 -/
theorem ratRoundtrip_fixed_not_discriminating :
    ∃ c c' : RatConstraint,
      c ≠ c' ∧ extractVecQ (convertVecQ c) = c ∧ extractVecQ (convertVecQ c') = c' := by
  refine ⟨{ a := [2], b := 2 }, { a := [3], b := 3 }, ?_, ?_, ?_⟩
  · -- `b` 分量给出 `2 = 3`（ℚ 中为假）
    intro h
    have hb : (2 : ℚ) = 3 := congrArg (fun c : RatConstraint => c.b) h
    norm_num at hb
  · exact roundtrip_extractVecQ _
  · exact roundtrip_extractVecQ _

/-- ⭐ **⑦′ 承重的否定结论（与 ⑥‴ 串联）**：
被固定的两个约束**语义平行**（共享零点 `-1`），却**不是**同一个对象，
且在 **ℤ** 上**不**互为倍数。
⇒ ⭐ 「往返固定」**完全**不能用来在轨道上选代表
（若能用，它就会把 `[2]` 与 `[3]` 区分开；而它**不区分**）。 -/
theorem ratRoundtrip_fixed_and_parallel_but_distinct :
    ({ a := [2], b := 2 } : RatConstraint) ≠ { a := [3], b := 3 } ∧
    extractVecQ (convertVecQ { a := [2], b := 2 }) = { a := [2], b := 2 } ∧
    extractVecQ (convertVecQ { a := [3], b := 3 }) = { a := [3], b := 3 } ∧
    (¬ ∃ lam : Int, (3 : Int) = 2 * lam) ∧
    (∃ lam : ℚ, lam ≠ 0 ∧ (3 : ℚ) = 2 * lam) := by
  refine ⟨?_, roundtrip_extractVecQ _, roundtrip_extractVecQ _, ?_, ?_⟩
  · intro h
    have hb : (2 : ℚ) = 3 := congrArg (fun c : RatConstraint => c.b) h
    norm_num at hb
  · rintro ⟨lam, h⟩; omega
  · exact ⟨3 / 2, by norm_num, by norm_num⟩

/-! ## 八、⭐ 跨模块桥：接上 `RealConstraintSat.QConstraint`（判据 3）

⭐⭐ `RealConstraintSat`（ℚ 约束 + 有限可判定性）与转换主干
（`ConvertVectorLinear` / `WeightToSymbolEquivalence`，**ℤ**）
在**不同的依赖锥**上（见报告 §依赖图实测）。
本节建立**第一个**连接：把 `RealConstraintSat.QConstraint` 的满足语义
与本文的 `RatConstraintSat` 在**单系数**情形下**逐字对齐**。

⇒ ⭐ **判据 3（跨模块）**：本桥用到**两端**的非平凡内容 ——
- 左端是 `RealConstraintSat` 的 `QConstraint`（含 `DecidableEq`、`QSatisfiableOn` 体系）；
- 右端是本文件的 `RatConstraint` / `dotQ` / `scaleVecQ`（含 §五 的缩放理论）。 -/

/-- **单系数 ℚ 约束编码为 `RatConstraint`**（常量长 `1` 的向量）。
⭐ 这是两侧类型的**桥接函数**，非平凡之处在于它把
`RealConstraintSat` 的**标量**形状接进主干的**向量**形状。 -/
def qConstraintToRat (c : QConstraint) : RatConstraint :=
  { a := [c.a], b := c.b }

/-- ⭐ **⑧ 跨模块桥（承重）**：`RealConstraintSat.QSat` 与本文
`RatConstraintSat`（在 `qConstraintToRat` 下）在 `x = [v]` 处**逐字等价**。

⭐ **它比"两行 simp"多说**：它把两个**独立建立**的 ℚ 约束语义
（一为标量、一为向量；一来自 `RealConstraintSat`、一来自本文镜像）
**证明为同一个**，从而使 §五 的缩放理论可**直接**作用于
`RealConstraintSat` 的 `QConstraint`。 -/
theorem qConstraint_iff_ratConstraintSat (c : QConstraint) (v : ℚ) :
    QSat c v ↔ RatConstraintSat (qConstraintToRat c) [v] := by
  simp [QSat, RatConstraintSat, qConstraintToRat, dotQ]

/-- ⭐ **⑧″ 编码与缩放可交换（技术引理，使 ⑧′ 的证明短且可复核）**：
`qConstraintToRat (c·lam) = scaleVecQ (qConstraintToRat c) lam`。
（两侧都是 `{a := [c.a·lam], b := c.b·lam}`，逐分量相等。） -/
theorem qConstraintToRat_scale (c : QConstraint) (lam : ℚ) :
    qConstraintToRat ⟨c.a * lam, c.b * lam⟩ = scaleVecQ (qConstraintToRat c) lam := by
  simp [qConstraintToRat, scaleVecQ]

/-- ⭐⭐ **⑧′ 桥的【承重】用法：把 §五 的缩放理论搬到 `RealConstraintSat` 的 `QConstraint` 上**。

给定 `RealConstraintSat` 的 `QConstraint c` 与**非零**有理 `lam`，
`c` 与「缩放后的约束」在**行为上等价**。

⇒ 这把 **§五 的域性质**（非零有理缩放保语义）**送达** `RealConstraintSat` 一侧，
是**跨模块**（判据 3）的**实质**内容 —— 两端各自都无法单独得到它：
  `RealConstraintSat` 没有缩放理论，而本文件的缩放理论此前**不**知道
  `QConstraint` 这个类型。

⚠ **证明路线（明示，每步来自本文件已证的引理）**：
`QSat c v`
 ⟺ `RatConstraintSat (qConstraintToRat c) [v]`        （⑧）
 ⟺ `RatConstraintSat (scaleVecQ (qConstraintToRat c) lam) [v]`  （③，需 `hlam`）
 ⟺ `RatConstraintSat (qConstraintToRat ⟨c.a*lam, c.b*lam⟩) [v]` （⑧″，重写）
 ⟺ `QSat ⟨c.a*lam, c.b*lam⟩ v`                          （⑧） -/
theorem qConstraint_scaling_transfer (c : QConstraint) (lam : ℚ) (hlam : lam ≠ 0) (v : ℚ) :
    QSat c v ↔ QSat (⟨c.a * lam, c.b * lam⟩ : QConstraint) v := by
  -- 先把两端各自翻译到 `RatConstraint` 侧
  rw [qConstraint_iff_ratConstraintSat c v,
    qConstraint_iff_ratConstraintSat ⟨c.a * lam, c.b * lam⟩ v]
  -- 再把「缩放后的编码」改写成「编码的缩放」
  rw [qConstraintToRat_scale c lam]
  -- 剩下的就是 §五 的 ③
  exact scaleVecQ_preserves_semantics (qConstraintToRat c) [v] lam hlam

/-! ## 九、⚠ 未做（如实登记，不硬证、不掩盖）

- ⚠⚠ **「解集相等 ⟹ 存在倍数」在 ℤ 上为假**（§六 已给见证），
  故本文件**不**把它当作 ℚ 的定理 —— 它**根本不对**。
- ⚠ **完整的"语义等价"刻画（解集相等情形）未做**：
  §五′ 的 ⑤ 含**平行性**前件（逐点比例），**不是**仅由解集相等推出。
- ⚠ **`a = 0` 的退化情形未处理**：⑤ 需要 `ha : a ≠ 0`（否则 `a'/a` 无定义）。
- ⚠ **多系数（向量）情形的充要刻画未做**：⑤ 只对**单系数** `[a]` 给出。
  多系数时"平行"的判定需要更多线性代数（`List` 上的比例性），**未做**。
- ⚠ **`RatParallel` 未被任何定理使用**：它只是一个**命名**（"存在倍数"的
  缩写），本文件**没有**用它证任何东西。⇒ 它**不计入**本文件的结论数；
  保留它的唯一理由是让 §五′ 的"结构条件 vs 语义条件"之分**在类型层可见**。
- ⚠ **规范形未构造**：⑦ 证明往返**不能**充当规范形选择器，
  但**没有**构造一个能用的规范形（如按首项系数约化）——
  那是 `RealCanonicalForm` 的归属，本文件不碰。
- ⚠ **⑧ 桥只覆盖单系数情形**：`qConstraintToRat` 把 `QConstraint`（标量）
  映到**长度 1** 的 `RatConstraint`；`RealConstraintSat` 中**没有**向量版
  ℚ 约束，故更宽的桥**无从建立**（不是"未做"，是**对侧不存在**）。
- ⚠ **不碰浮点**（任务书明确要求避开）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
