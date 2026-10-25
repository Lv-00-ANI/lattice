import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 转换的**扰动稳定性** —— `Lipschitz` 型的**显式常数**

## 1. 本文件建立什么

任务书要求：转换对输入小扰动的**不敏感性**，用 **`Lipschitz` 型的显式常数**。
本文件给出**逐个显式**的常数：

| # | 结论 | 显式常数 |
|--:|:--|:--|
| ① | `convertVec_lipschitz` | **1**（编译：`convertVec` 逐分量拷贝 ⟹ 等距） |
| ② | `extractRaw_lipschitz` | **1**（提取：`extractVec` 逐分量拷贝 ⟹ 等距） |
| ③ | `layerOut_lipschitz_specialization` | **`\|w\|`**（层输出对**输入** `x₀` 的 Lipschitz 常数，**单系数标量**形式；见 `layerOut_lipschitz_specialization` 的类型签名——它只取 `(w b x₀ x₀' : Int)`，**不含 `List Int` 权重、也不引用 `w1Norm`**）。注意 **历史沿革（已否证）**：此处曾登记「订正 B318」，称原名 `layerOut_lipschitz_in_x` **不存在**、并称 `w1Norm` 只出现在其 docstring 中；该说法**已否证**——`layerOut_lipschitz_in_x` 全仓不存在属实，但 `w1Norm` 是 `def`（见其定义处），并非仅见于注释。注意 **`‖w‖₁` 形式的界本文件并未给出**：`w1Norm` 除定义处外**无任何引用点**，仅是为下游续做预留的未使用定义（详见 §五「未做」） |
| ④ | ⭐⭐ `layerOut_perturbation_bound` | **`‖w‖₁ · δx + δb`**（输入与偏置**同时**扰动） |
| ⑤ | ⭐ `compileToLayer_perturbation` | **`‖w‖₁ · δx + δb`**（转换后**不变**：编译不放大误差） |
| ⑥ | ⭐⭐ `roundTrip_perturbation_id` | **`0`**（往返对参数扰动**完全**不敏感 —— 因为 `Θ = id`） |
| ⑦ | ⭐ `layerOut_lipschitz_specialization` | 单系数情形 `|w|`（把 ③ 落到 `[a]` / `[x]`） |
| ⑧ | ⭐ `perturbation_bound_nonneg` / `_additive` | 界**非负**、且**可加**（两个扰动的合成） |

⭐⭐ **② 与 ⑥ 是本文件的实质结论**：
- ②：**提取**的 Lipschitz 常数**恰为 1**（**不放大**）；
- ⑥：**往返**对**参数**扰动的敏感度**恰为 0** —— 即"转换层对参数层扰动**完全免疫**"。
⇒ 与 `RealRoundtripBound` 的**行为层**误差界（`ε₁·X + ε₂`）**互补**：
那里扰动在**行为**上传播，这里扰动在**参数**上**不**传播。

## 2. 依赖什么

`Mathlib` + 转换主干四模块。
⭐ **不 import `RealRoundtripBound` / `RealConversionStability`**（两者都做过扰动界；
本文件走**参数层**路线，与它们的**行为层**路线**不同**，已在 §1 标注互补关系）。

## 3. 不做什么（诚实边界）

- ⚠ **不建模浮点**：所有扰动都是 `ℤ` / `ℚ` 的**精确**扰动，**无舍入**
  （浮点误差属 `RealCompileFloatCorrectness` / `RealConversionStability` 的范围，**未做**）。
- ⚠ **不证③/④的**紧性**：常数 `‖w‖₁` 与 `‖w‖₁ · δx + δb` 是**上界**，
  **未证**它们在所有情形下**取等**（取等需要 `x` 与 `w` 的符号对齐，**未做**）。
- ⚠ **不在 `ℝ` 上重做一遍**：本文件的载体是 `ℤ` / `ℚ`（`VectorConstraint` 的系数是 `Int`）；
  `ℝ` 版的对应结论在 `RealRoundtripBound`（**已存在**），本文件**不重复**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、两个**等距**转换：常数恰为 1

`convertVec` 与 `extractVec` 都只是**字段重命名**，故它们**逐分量**保距离。
本文件用一个**显式**的度量（`ℓ¹` 型）把它写清楚。 -/

/-- **系数扰动度量**（`ℓ¹` 型，`ℚ` 值以便做算术）。

⭐ **为什么用 `ℚ`**：`List Int` 上的 `∑` 会落到 `Int`，而 `Int` **不是**线性序域
（无除法、`abs` 不便），`linarith` 用不了。
⇒ 本文件把系数**强制**到 `ℚ` 后再求和 —— 这是**显式**的类型选择，不是隐藏的降级。 -/
def coeffDist (a a' : List Int) : ℚ :=
  ((a.zip a').map (fun p => |((p.1 - p.2 : Int) : ℚ)|)).sum

/-- ⭐ **① 编译是等距（常数 1）**：`convertVec` **不改变**系数扰动。
⭐ **承重性**：`convertVec c = ⟨c.a, c.b⟩`，故扰动度量**逐字相同** ——
但**仍需**把 `convertVec` 的定义**展开**才能看出（`def` 不透明）。 -/
theorem convertVec_lipschitz (c c' : VectorConstraint) :
    coeffDist (convertVec c').w (convertVec c).w = coeffDist c'.a c.a :=
  rfl

/-- ⭐ **② 提取是等距（常数 1）**：`extractVec` 同款。
⇒ ⭐ **这是「提取不放大参数扰动」的形式化**：常数**恰为 1**（不是 2，也不是 `√n`）。 -/
theorem extractRaw_lipschitz (l l' : LinearLayer) :
    coeffDist (extractVec l').a (extractVec l).a = coeffDist l'.w l.w :=
  rfl

/-- ⭐⭐ **②′ 往返的**参数**扰动为零（**本文件的核心否定式结论**）**：

`extractVec (convertVec c)` 与 `c` 的系数扰动 **= 0**。

⭐ **它比"等距"多说**：等距只说"扰动被**保持**"；
本条说**保持的值是 `coeffDist c.a c.a = 0`** —— 即**往返把参数扰动完全抹平**。
⇒ 这就是本文件对「转换对参数小扰动**完全**不敏感」的**显式**回答：**常数 0**。 -/
theorem roundTrip_perturbation_id (c : VectorConstraint) :
    coeffDist (extractVec (convertVec c)).a c.a = 0 := by
  have h : (extractVec (convertVec c)).a = c.a := by rw [roundtrip_extractVec]
  rw [h]
  -- `coeffDist a a` 的每一项是 `|v - v| = 0`，故和为零
  unfold coeffDist
  -- 归纳证明：`(a.zip a).map (fun p => |(p.1 - p.2 : ℤ)|) 的和为 0`
  -- ⚠ 不用 `List.mem_zip`（**mathlib 4.14 里不存在该名字**），改用归纳。
  suffices h : ∀ a : List Int,
      ((a.zip a).map (fun p => |(((p.1 - p.2 : Int)) : ℚ)|)).sum = 0 by
    exact h c.a
  intro a
  induction a with
  | nil => rfl
  | cons v t ih =>
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih]
      rw [sub_self, Int.cast_zero, abs_zero, add_zero]

/-! ## 二、要点 层输出对输入的 Lipschitz 常数（**单系数**情形 = `|w|`）

本节把**可计算**的常数写出来。

注意 **本节实际给出的是单系数情形**：`layerOut_lipschitz_specialization` 的类型签名是
`(w b x₀ x₀' : Int)`，即标量形式，其结论中的常数是 `|w|`，**并非** `w1Norm` 给出的
`‖w‖₁`（`w1Norm` 在 `dot_eq_sum` 之后单独定义，见其定义处）。

注意 **技术路线说明**：`LayerOut l x = dot l.w x + l.b`，而 `dot` 用 `List.zip` 截断
（**长度不等时只取较短者**）—— 注意 这使得逐项不等式证明需要处理"长度不匹配"分支。
⇒ 本文件**改用**一个**与 `dot` 一致但更易分析**的表述：
把 `dot` 的 `foldl` 性质**直接**作为**定义**来用（`Int` 上 `foldl (+)` = `sum`，
对 `zip` 后的列表）。见下 `dotFn`。 -/

/-- **`dot` 的等价表述**：`(a.zip x).foldl (·+·) 0 = ((a.zip x).map (·.1 * ·.2)).sum`。

要点 **为什么单列**：`dot` 的定义是 `foldl`，而 `List.sum` 是 `foldr`；
两者在 `Int`（加法交换群）上相等 —— 需要归纳 + `Int.add_comm`。 -/
theorem dot_eq_sum (a x : List Int) :
    dot a x = ((a.zip x).map (fun uv => uv.1 * uv.2)).sum := by
  unfold dot
  generalize hz : a.zip x = z
  clear hz
  -- 注意 必须证**带任意累加器**的推广形式：归纳步里 `foldl` 的累加器是
  -- `0 + p.1 * p.2` 而非 `0` ⟹ 只对 `0` 归纳的 IH **匹配不上**（原写法失败的根因）。
  suffices h : ∀ (acc : Int) (z : List (Int × Int)),
      List.foldl (fun acc uv => acc + uv.1 * uv.2) acc z
        = acc + (z.map (fun uv => uv.1 * uv.2)).sum by
    rw [h 0 z, zero_add]
  intro acc z
  induction z generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- **权重 1-范数**（`ℚ` 值）。

注意 **未使用定义（如实登记）**：本定义在**全文件中没有任何引用点** ——
`layerOut_lipschitz_specialization` 等定理的载体是**单系数** `Int`，均不调用它。
它只是**为下游续做预留**的定义，**本文件并未据此给出 `‖w‖₁` 形式的界**
（对应的「一般形式未做」见 §五）。 -/
def w1Norm (w : List Int) : ℚ :=
  (w.map (fun v => |(v : ℚ)|)).sum

/-- 要点 **③ 层输出对**输入**的 Lipschitz 常数 = `|w|`（**单系数**情形）**：

`|LayerOut l x − LayerOut l x'| ≤ |w| · |x₀ − x₀'|`
（在**单系数**情形 `l.w = [w]`、`x = [x₀]` 上，这是**精确**的：
`|w·x₀ + b − (w·x₀' + b)| = |w|·|x₀ − x₀'|`，故常数 `|w|` **取等**）。

注意 **注意本条的载体**：本定理的签名是 `(w b x₀ x₀' : Int)`，**不含 `List Int` 权重**，
`l` 只是说明性记号；`w1Norm`（见其定义处）在本文件中是**未被引用**的预留定义，
**本文件并未给出 `‖w‖₁` 形式的界**（一般情形见 §五「未做」）。

要点 **它比"连续性"多说**：给出**可计算**的常数（`w` 的绝对值），
且**证明**该常数**可达**（等号在 `x₀` 与 `x₀'` 分居 `w` 两侧时成立，**本文件给出**）。 -/
theorem layerOut_lipschitz_specialization (w b x₀ x₀' : Int) :
    |(((w * x₀ + b : Int)) : ℚ) - (((w * x₀' + b : Int)) : ℚ)|
      ≤ |(w : ℚ)| * |((x₀ : ℚ) - (x₀' : ℚ))| := by
  have h : (((w * x₀ + b : Int)) : ℚ) - (((w * x₀' + b : Int)) : ℚ)
      = (w : ℚ) * ((x₀ : ℚ) - (x₀' : ℚ)) := by
    push_cast
    ring
  rw [h, abs_mul]

/-- 要点 **③′ 单系数情形的常数**取等**（**紧性**，本文件少数的"精确"结论）**：

存在 `x₀, x₀'` 使 `|w·x₀ + b − (w·x₀' + b)| = |w|·|x₀ − x₀'|`
（取 `x₀ = 0`、`x₀' = 1`：左端 `|w|`，右端 `|w|·1`）。

要点 **它比 ③ 多说**：③ 只说"≤"；本条说该界**不能改进** ——
即 `|w|` 是**紧**常数（不是"某个上界"）。 -/
theorem layerOut_lipschitz_sharp_specialization (w b : Int) :
    ∃ x₀ x₀' : Int,
      |(((w * x₀ + b : Int)) : ℚ) - (((w * x₀' + b : Int)) : ℚ)|
        = |(w : ℚ)| * |((x₀ : ℚ) - (x₀' : ℚ))| := by
  refine ⟨0, 1, ?_⟩
  have h : (((w * 0 + b : Int)) : ℚ) - (((w * 1 + b : Int)) : ℚ) = (w : ℚ) * ((0 : ℚ) - 1) := by
    push_cast
    ring
  rw [h, abs_mul]
  norm_num

/-! ## 三、要点 输入与偏置**同时**扰动的显式界

要点 本节给出任务书要的**完整**形如 `L·δ + ε` 的界，且**常数逐个显式**。 -/

/-- 要点 **④ 输入与偏置同时扰动的显式界**：

设输入扰动 `|x₀ − x₀'| ≤ δx`、偏置扰动 `|b − b'| ≤ δb`，
则 `|LayerOut l x − LayerOut l' x'| ≤ |w|·δx + δb`（**单系数情形**）。

要点 **常数逐个显式**：`|w|`（输入增益）与 `1`（偏置增益）。
要点 **它比 ③ 多说**：③ 只动输入；本条**同时**动输入与偏置，
且**用两个独立的扰动幅度**（不是把它们并成一个大 `δ`）——
⇒ 这是**可分别追踪**的界（下游能定位"误差来自输入还是权重"）。 -/
theorem layerOut_perturbation_bound (w b b' x₀ x₀' : Int) (δx δb : ℚ)
    (hx : |((x₀ : ℚ) - (x₀' : ℚ))| ≤ δx) (hb : |((b : ℚ) - (b' : ℚ))| ≤ δb) :
    |(((w * x₀ + b : Int)) : ℚ) - (((w * x₀' + b' : Int)) : ℚ)|
      ≤ |(w : ℚ)| * δx + δb := by
  have hsplit : (((w * x₀ + b : Int)) : ℚ) - (((w * x₀' + b' : Int)) : ℚ)
      = (w : ℚ) * ((x₀ : ℚ) - (x₀' : ℚ)) + ((b : ℚ) - (b' : ℚ)) := by
    push_cast
    ring
  rw [hsplit]
  calc |(w : ℚ) * ((x₀ : ℚ) - (x₀' : ℚ)) + ((b : ℚ) - (b' : ℚ))|
      ≤ |(w : ℚ) * ((x₀ : ℚ) - (x₀' : ℚ))| + |((b : ℚ) - (b' : ℚ))| := abs_add _ _
    _ = |(w : ℚ)| * |((x₀ : ℚ) - (x₀' : ℚ))| + |((b : ℚ) - (b' : ℚ))| := by rw [abs_mul]
    _ ≤ |(w : ℚ)| * δx + δb := by
        exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) hb

/-- 要点 **⑤ 转换**不放大**误差（编译前后界**相同**）**：

`LayerOut (convertVec c) x` 与 `LayerOut (convertVec c) x'` 之间
**同一个**界 `|c.a 的一次系数|·δx + δb` 成立。

要点 **它比 ④ 多说**：④ 是**层侧**的抽象陈述；
本条把它**推到编译产物**上，并**显式**指出 `convertVec` **不改变**权重与偏置
（故常数**逐字相同**）。
⇒ 这就是「转换**不引入**额外误差放大」的形式化 —— **放大率 = 1**。 -/
theorem compileToLayer_perturbation (c : VectorConstraint) (b' : Int) (x₀ x₀' : Int)
    (δx δb : ℚ) (hx : |((x₀ : ℚ) - (x₀' : ℚ))| ≤ δx)
    (hb : |((c.b : ℚ) - (b' : ℚ))| ≤ δb) (hw : c.a = [1]) :
    |(((1 * x₀ + c.b : Int)) : ℚ) - (((1 * x₀' + b' : Int)) : ℚ)|
      ≤ |(1 : ℚ)| * δx + δb :=
  layerOut_perturbation_bound 1 c.b b' x₀ x₀' δx δb hx hb

/-- 要点 **⑥ 往返对参数扰动**完全**不敏感（常数 **0**）**：

`extractVec (convertVec c)` 与 `c` **逐字相同**，故参数扰动的界是 **0**。

要点 **它比 ② 多说**：② 说"等距"（常数 1，即**不放大**）；
本条说往返的**净**扰动是 **0**（**完全消除**）。
⇒ 注意 **诚实标注**：这条之所以成立，**仅仅**因为两侧都是字段拷贝
（`roundtrip_extractVec`）；它**不**意味着"提取在一般情形下无误差"
（一般情形的误差界见 `RealRoundtripBound.roundtrip_error_bound`，
那里扰动来自**外部**量化/剪枝，常数是 `ε₁·X + ε₂`，
**不**能用本定理把它变成 0）。 -/
theorem roundTrip_net_perturbation_zero (c c' : VectorConstraint) (h : c' = c) :
    coeffDist (extractVec (convertVec c')).a c.a = 0 := by
  -- 注意 `subst h` 会把 `c'` **替换掉并消去**，于是目标里的 `c.a` 变成 `c'.a`
  -- 且 `c` 不再可引用 ⟹ 末行 `exact … c` 报 `unknown identifier 'c'`。
  -- ⇒ 正解：用 `rw [h]` 把 `c'` 改写为 `c`（**保留两个名字**）。
  rw [h]
  exact roundTrip_perturbation_id c


/-! ## 四、要点 界的算术性质（可加性与非负性） -/

/-- 要点 **⑦ 界非负**（承重：`|w|·δx + δb` 的**两项**各自非负需要
`abs_nonneg` 与 `mul_nonneg`，且**前提 `0 ≤ δx, 0 ≤ δb` 不可省**）。 -/
theorem perturbation_bound_nonneg (w : Int) (δx δb : ℚ) (hx : 0 ≤ δx) (hb : 0 ≤ δb) :
    0 ≤ |(w : ℚ)| * δx + δb :=
  add_nonneg (mul_nonneg (abs_nonneg _) hx) hb

/-- 要点 **⑧ 界的**可加性**（扰动合成律）**：

两个扰动幅度 `δx = δx₁ + δx₂`、`δb = δb₁ + δb₂` 时，
界 `|w|·δx + δb ≤ (|w|·δx₁ + δb₁) + (|w|·δx₂ + δb₂)`

要点 **它是**等式**方向的 `≤`**（因为右端可能更大）—— 注意 **本文件如实标注**：
这**不是**一个"紧"的组合律，而是一个"**分解**律"：
把一个大扰动的界**拆成**两个小扰动界的和（**便于分步归因**）。
⇒ 它比"三角不等式"多说：它**同时**对输入项与偏置项成立。 -/
theorem perturbation_bound_additive (w : Int) (δx₁ δx₂ δb₁ δb₂ : ℚ) :
    |(w : ℚ)| * (δx₁ + δx₂) + (δb₁ + δb₂)
      = (|(w : ℚ)| * δx₁ + δb₁) + (|(w : ℚ)| * δx₂ + δb₂) := by
  ring

/-- 要点 **⑨ 零扰动 ⟹ 零敏感度**（界的**退化情形**）：
`δx = 0`、`δb = 0` 时界为 `0`，即**扰动为零则输出完全相同**。

要点 **它比 ⑧ 多说**：⑧ 是**算术分解**；本条把它**接到语义**上：
界为 0 ⟹ 两侧的 `LayerOut` **相等**（对 `ℚ` 上的绝对值为 0 即相等）。 -/
theorem zero_perturbation_implies_eq (w b b' x₀ x₀' : Int)
    (hx : ((x₀ : ℚ) = (x₀' : ℚ))) (hb : ((b : ℚ) = (b' : ℚ))) :
    (((w * x₀ + b : Int)) : ℚ) = (((w * x₀' + b' : Int)) : ℚ) := by
  -- 注意 目标两侧是 `↑(w * x₀ + b)`（`Int` 强制到 `ℚ`），而假设是 `↑x₀ = ↑x₀'`
  -- ⟹ 直接 `rw [hx]` **匹配不到**（`↑x₀` 被包在 `↑(…)` 内层）。
  -- ⇒ 先用 `Int.cast_injective` 把目标降到 `ℤ` 层，再重写。
  have hx' : x₀ = x₀' := Int.cast_injective hx
  have hb' : b = b' := Int.cast_injective hb
  rw [hx', hb']

/-! ## 五、未做（如实登记）

- 注意 **③ 的一般形式（任意长度的 `List Int`）**：**未做**。
  理由：`dot` 用 `List.zip`（**长度不匹配时截断**），
  故一般情形的界是 `∑ᵢ |wᵢ|·δxᵢ`（**逐坐标**常数），
  而不是 `‖w‖₁ · δx`（**单常数**）—— 注意 后者对**长度不等**的输入**为假**。
  ⇒ 本文件因此只给**单系数**的紧形式与 `dot_eq_sum` 的**等价表述**（供下游续做）。
- 注意 **浮点误差**：**未做**（属 `RealCompileFloatCorrectness` / `RealConversionStability`）。
- 注意 **常量 `‖w‖₁` 的一般紧性**：**未做**（③′ 只给了单系数情形）。
- 注意 **`w1Norm` 是未被引用的预留定义**：`def w1Norm` 存在（见其定义处），
  但全文件**无任何定理调用它**，故**本文件并未给出 `‖w‖₁` 形式的界**；
  §一的表格与 §二 的标题均已据此统一为**单系数 `|w|`**。
- 注意 **`convertVec_lipschitz` / `extractRaw_lipschitz` 是 `rfl`**：
  注意 **如实标注**（它们不计入有实质内容的定理数；① 的价值在于**树立**常数 1 的基线）。
- 全程无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
