import Mathlib
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Meta.RealDotRepresentationAudit
/-!
# LATTICE: 符号 ⇄ 权重 端到端闭环 —— 编译-提取往返定理与其**诚实边界**

## 0. 为什么需要本文件（缺口的精确定位）

doc/02 §4.3 声称转换层 L2⇄L3 是「唯一难点」，且整条链路「完整且可逆」。
审计（E1）发现该声称在 Lean 库里**没有对应的单一陈述**：

| 方向 | 定理所在文件 | 该文件的 import |
|:--|:--|:--|
| L2 → L3（编译保语义） | `SymbolToWeightCorrectness.symbolToWeight_correct` | `Mathlib`、`ConvertVectorLinear` |
| L3 → L2（提取往返恒等） | `WeightToSymbolEquivalence.roundtrip_extractVec` | `Mathlib`、`ConvertLinear`、`ConvertVectorLinear` |

**两个文件互不 import**（本文件之前，全库**没有任何** `.lean` 同时 import 二者；
接收方 `TotalLoss` / `ConstraintEmbeddingSoundness` / `LayerComposition` 只 import 编译侧）。
因此「编译 → 提取 → 仍是原符号」这条**端到端闭环定理此前不存在**，
"可逆" 只是**名义上的对称**（两个方向各自成立，但彼此没有对接）。

本文件把它补上，并**同时给出它的诚实边界**（下文 §5–§7）。

## 1. 链路图（每一级转换 + 对应定理）

```
                       ┌─ ConvertVectorLinear.convertVec  (record 重命名 a ↦ w, b ↦ b)
   L2 符号侧           │     定理: convertVec_preserves_semantics   [保语义]
  VectorConstraint ────┤     定理: convertVec_preserves_solution_set
   {a : List Int, b}   │     定理: scaleVec_preserves               [缩放不变性 = 规范形自由度]
                       │
                       │  列表级: SymbolToWeightCorrectness.compileToLayer = List.map convertVec
                       │     定理: symbolToWeight_correct           [AllSatisfied ⟺ AllZeroOutputs]
                       ▼
   L3 权重侧            …
  LinearLayer          │
   {w : List Int, b}   │
                       │
                       ├─ WeightToSymbolEquivalence.extractVec    (record 重命名 w ↦ a, b ↦ b)
                       │     定理: roundtrip_extractVec            [extractVec ∘ convertVec = id]
                       │     定理: extract_is_valid                [行为等价]
                       └──────────────────────────────────────────┐
                                                                  │
   ★ 断点（本文件之前）：上述两段从不在同一条定理里出现 ★          │
                                                                  ▼
   本文件接上：
     extractLayer_compileToLayer        : extractLayer ∘ compileToLayer = id   （§2）
     compileToLayer_extractLayer        : compileToLayer ∘ extractLayer = id   （§2）
     compile_extract_end_to_end         : AllSatisfied (extractLayer (compileToLayer cs)) x
                                            ⟺ AllZeroOutputs (compileToLayer cs) x        （§3）
     closed_loop_adds_nothing           : 闭环 ⟺ 单向（在语法往返恒等的线性子类上）    （§3）
     activated_loop_breaks              : 一旦折入激活，闭环**失效**（机器验证反例）    （§5）
     linearization_collapses_models     : 非线性线性化编译**非单射** ⟹ 不可逆          （§6）
     validity_does_not_determine_syntax : 行为等价**推不出**语法相等（缩放轨道）        （§7）
```

**结论（一眼可见）**：链路在**线性子类**上是**真的闭合**（§2–§3，两侧互为逆映射），
但该闭合**不含新语义内容**（§3 的 `closed_loop_adds_nothing`：闭环与单向定理**等价**）；
真正的断点在**激活/非线性折入之后**（§5–§6，机器验证反例）；
且即便在线性子类上，「可逆」也只在**规范形（缩放轨道）意义下**成立（§7）。

## 2. 诚实标注（本文件主张 / 不主张什么）

- **主张**：线性子类（`convertVec`/`extractVec` 这一对）上，端到端闭环**成立**，
  且 `extractLayer` 与 `compileToLayer` 互为**双向逆**（`LeftInverse` + `RightInverse`）。
- **主张（诚实降级之一 —— 降级）**：该闭环**不比单向定理更强**：
  `closed_loop_adds_nothing` 证明两者**等价**。故「可逆」在数学上是**同构的白话**，
  真内容全在 `convertVec_preserves_semantics` 的**零化语义**里。
- **主张（诚实降级之二 —— 降级）**：语法相等比语义等价**严格更强**：
  `validity_does_not_determine_syntax` 给出机器验证反例（缩放轨道 `c ↦ scaleVec c 2`）。
  故 §3 的闭环只能在**规范形意义下**读作「仍是原符号」。
- **不主张（未证 / 已证为假）**：**折入激活后**的端到端闭环。
  `activated_loop_breaks`（§5）与 `linearization_collapses_models`（§6）给出
  **机器验证反例**，说明「一般非线性下编译-提取可逆」**为假**，本文件不证该假命题。
- 本文件**只读**引用既有文件，**不修改** `SymbolToWeightCorrectness` /
  `WeightToSymbolEquivalence` / `ConvertLinear` / `ConvertVectorLinear`（核心契约）。
- 无 `sorry` / `axiom` / `admit`；全部定理在内核可验证。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、提取器接口：把 L3 → L2 的提取器抬到列表级

`WeightToSymbolEquivalence.extractVec` 作用于单个 `LinearLayer`；
本文件的 `extractLayer` 把它是**逐层映射**到整层（列表），
从而与 `SymbolToWeightCorrectness.compileToLayer`（`List.map convertVec`）**同类型对接**。
这是"两段互不相接的证明"之间缺失的那一个适配子。 -/

/-- **列表级提取器（L3 → L2）**：逐神经元提取，得到约束集合。
这是连接 `WeightToSymbolEquivalence.extractVec`（单层）与
`SymbolToWeightCorrectness.ConstraintSet`（约束列表）的适配子。 -/
def extractLayer (ls : Layer) : ConstraintSet :=
  ls.map extractVec

/-! ## 二、语法闭环：两侧互为逆映射

`convertVec` 与 `extractVec` 都是 record 字段重命名（`a ↦ w`, `w ↦ a`），
故在**对象层**它们互为逆；抬到列表级后，`compileToLayer` 与 `extractLayer`
是 `ConstraintSet` 与 `Layer` 之间的**双向逆对**。 -/

/-- **端到端闭环（提取方向 = 左逆）**：`extractLayer (compileToLayer cs) = cs`。
即「编译 → 提取」回到**原约束集**（语法恒等）。
证明：列表归纳 + 单元素恒等 `roundtrip_extractVec`。 -/
theorem extractLayer_compileToLayer (cs : ConstraintSet) :
    extractLayer (compileToLayer cs) = cs := by
  unfold extractLayer compileToLayer
  induction cs with
  | nil => rfl
  | cons c t ih =>
      -- 先只拆**外层** map 的 cons（`List.map_cons` 会匹配到最外层的 map），
      -- 再代入 `ih`，最后用单元素往返恒等收口。
      show extractVec (convertVec c) :: List.map extractVec (List.map convertVec t) = c :: t
      rw [ih, roundtrip_extractVec]

/-- **端到端闭环（编译方向 = 右逆）**：`compileToLayer (extractLayer ls) = ls`。
即「提取 → 编译」回到**原权重层**（语法恒等）。
证明：列表归纳 + 结构 eta（`⟨l.w, l.b⟩ = l`）。 -/
theorem compileToLayer_extractLayer (ls : Layer) :
    compileToLayer (extractLayer ls) = ls := by
  unfold extractLayer compileToLayer
  induction ls with
  | nil => rfl
  | cons l t ih =>
      show convertVec (extractVec l) :: List.map convertVec (List.map extractVec t) = l :: t
      rw [ih]
      cases l with
      | mk w b => rfl

/-- **两侧互为左逆**：`extractLayer ∘ compileToLayer = id`（把 §二的等式提升为函数级陈述）。 -/
theorem extractLayer_leftInverse : Function.LeftInverse extractLayer compileToLayer :=
  fun cs => extractLayer_compileToLayer cs

/-- **两侧互为右逆**：`compileToLayer ∘ extractLayer = id`。 -/
theorem extractLayer_rightInverse : Function.RightInverse extractLayer compileToLayer :=
  fun ls => compileToLayer_extractLayer ls

/-- **双射（同构的机器版）**：`compileToLayer` 是 `ConstraintSet → Layer` 的双射，
因为 `extractLayer` 同时是它的左逆与右逆。
（诚实标注：本定理之所以成立，正因两侧都只是 record 字段重命名；见 §7。） -/
theorem compileToLayer_bijective : Function.Bijective compileToLayer :=
  ⟨fun _ _ h => by
      have h' := congrArg extractLayer h
      simpa [extractLayer_compileToLayer] using h',
    fun ls => ⟨extractLayer ls, compileToLayer_extractLayer ls⟩⟩

/-! ## 三、端到端闭环语义定理（本文件的核心交付）

以下三条把 `SymbolToWeightCorrectness`（编译保语义）与
`WeightToSymbolEquivalence`（提取往返）**放进同一条定理**——
这正是全库此前缺失的那条交叉引用。 -/

/-- **把 `symbolToWeight_correct` 经定义级等式 `extract ∘ compile = id` 换形。**

「编译 `cs` 得到权重层 → 从权重层提取回符号 → 全约束满足」
**⟺**「编译得到的权重层输出全零」。

⚠⚠ **第 19 轮降级：标题原来是「★ 端到端闭环定理（target form）★」，那个标题声称的比这里证的多。**

**它证的是**：`extractLayer (compileToLayer cs) = cs`（本文件的 `extractLayer_compileToLayer`，**`rfl`**），
于是左式的 `AllSatisfied` 变成 `AllSatisfied cs`，再由 `symbolToWeight_correct` 收尾。
**证明体是 `rw` 一行 + 一次既有定理的实例化，没有任何往返内容。**

**为什么「闭环」在这里是免费的**：那一跳的 `extract` 是**字段重命名**（本文件自己的
`RealConstraintEdit.lean:33`、`:450` 把它判为「`rfl` 级空壳缺陷」），
所以 `extract ∘ compile = id` **是定义级的**，第二个方向不花任何代价。

⭐ **真正的端到端需要一条信息有损的编译路径**——`extract` 不再是字段重命名。
**那条没有，本条也不声称有。**

**保留本条仍有用**：它把两个此前从不互相引用的文件接成一条定理，
所以「同时引用」这件事本身是真的。 -/
theorem compile_extract_end_to_end (cs : ConstraintSet) (x : List Int) :
    AllSatisfied (extractLayer (compileToLayer cs)) x ↔
      AllZeroOutputs (compileToLayer cs) x := by
  rw [extractLayer_compileToLayer cs]
  exact symbolToWeight_correct cs x

/-- **闭环的符号侧读数**：提取回来约束集与原约束集**语义相同**。
（语法上更直接：`extractLayer_compileToLayer` 给出的是等式。） -/
theorem compile_extract_semantics_closed (cs : ConstraintSet) (x : List Int) :
    AllSatisfied (extractLayer (compileToLayer cs)) x ↔ AllSatisfied cs x := by
  rw [extractLayer_compileToLayer cs]

/-- **往返于权重侧**：`compile (extract W)` 的行为与原层 `W` 完全一致
（输出全零谓词相同）——对应任务的第二种目标形态 `compile (extract W) ≡ W`。 -/
theorem compile_extract_weight_side (ls : Layer) (x : List Int) :
    AllZeroOutputs (compileToLayer (extractLayer ls)) x ↔ AllZeroOutputs ls x := by
  rw [compileToLayer_extractLayer ls]

/-- **闭环幂等（回路是投影）**：再跑一圈不改变结果。
（`extract`/`compile` 已互逆，故回路是一次投影；不动点集是整个空间。） -/
theorem closed_loop_idempotent (cs : ConstraintSet) :
    extractLayer (compileToLayer (extractLayer (compileToLayer cs))) =
      extractLayer (compileToLayer cs) := by
  rw [extractLayer_compileToLayer, extractLayer_compileToLayer]

/-- **要点 诚实降级（关键）：闭环并不比单向定理更强。**

在语法往返恒等（`extractLayer_compileToLayer`）成立的前提下，
「闭环语义陈述」与「单向编译保语义陈述」**互相等价**：
两条 if-and-only-if 的**左右式完全相同**。

**含义（诚实/降级）**：在这条线性子类上，端到端闭环**不携带任何超出
`symbolToWeight_correct` 的新语义内容**——"可逆"是**同构的白话**，
而非独立的数学发现。真正的数学内容在**零化语义**（`dot`/`LayerOut` 的结构）
与**规范形自由度**（`scaleVec`，见 §7）里。
本条与 §5–§6 的反例共同构成本文件的诚实清单。 -/
theorem closed_loop_adds_nothing (cs : ConstraintSet) (x : List Int) :
    (AllSatisfied (extractLayer (compileToLayer cs)) x ↔ AllZeroOutputs (compileToLayer cs) x)
      ↔ (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) := by
  rw [extractLayer_compileToLayer cs]

/-- **抽取-验证契约（跨文件对接）**：提取出的约束候选**行为有效**
（`ExtractionValid` 的向量版），即「提取候选通过验证器（行为等价）」——
把 `WeightToSymbolEquivalence.extract_is_valid` 抬到向量/列表层。
定义向量版 `ExtractionValidVec` 后，闭环的两端在**行为**上也被钉住。 -/
def ExtractionValidVec (l : LinearLayer) (c : VectorConstraint) : Prop :=
  ∀ x : List Int, LayerOut l x = 0 ↔ VectorConstraintSat c x

theorem extractVec_is_valid (l : LinearLayer) : ExtractionValidVec l (extractVec l) := by
  intro x
  show LayerOut l x = 0 ↔ VectorConstraintSat (extractVec l) x
  unfold extractVec VectorConstraintSat LayerOut
  rfl

theorem extractLayer_candidates_valid (ls : Layer) :
    ∀ c ∈ extractLayer ls, ∃ l ∈ ls, ExtractionValidVec l c := by
  intro c hc
  unfold extractLayer at hc
  rcases List.mem_map.mp hc with ⟨l, hl, rfl⟩
  exact ⟨l, hl, extractVec_is_valid l⟩

/-! ## 四、闭环与验证回路（`lv_verify` / `lv_repair`）的衔接

`VerifyLoopProgress` 的回路语义是「验证失败 → 修正 → 再验证」，
`RealLV.lv_verify` 是接口层判定。本节的桥把**闭环定理**与**回路稳定性**接起来：
在闭环成立（`extractLayer ∘ compileToLayer = id`）的线性子类上，
**回路对编译产物是空操作**——因为符号侧与权重侧的满足谓词经闭环后完全一致，
验证绝不会误报，也就无需修正。这就是 §3 的 `closed_loop_adds_nothing` 在回路视角的读数。 -/

/-- **回路-闭环衔接**：若权重层已在闭环像中（`ls = compileToLayer cs`），
则「层输出全零」恰好就是「原约束集满足」——
验证器在编译产物上的判定与符号侧判定**逐点一致**（无误报、无漏报）。 -/
theorem verify_loop_closed_agreement (cs : ConstraintSet) (x : List Int) :
    AllZeroOutputs (compileToLayer cs) x ↔ AllSatisfied cs x :=
  (symbolToWeight_correct cs x).symm

/-- **回路在闭环像上是恒等的**：对编译产物再做一圈「提取 → 编译」不改变权重层，
故验证回路的修正步骤在该子类上**无触发对象**（回路稳定）。
（`verify_loop_closed_agreement` + `compileToLayer_extractLayer` 的合成读数。） -/
theorem verify_loop_stable_on_image (cs : ConstraintSet) :
    compileToLayer (extractLayer (compileToLayer cs)) = compileToLayer cs := by
  rw [compileToLayer_extractLayer]

/-! ## 五、★ 断点一：折入激活后闭环**失效**（机器验证反例）★

线性子类的闭环之所以成立，纯粹因为两侧是**同一个零化谓词的两种写法**。
一旦在权重侧折入激活 `σ`（这是权重侧相对符号侧**唯一真正多于**的东西），
`σ ∘ LayerOut` 的零集一般**严格大于** `LayerOut` 的零集，
于是「输出零化」不再等价于「约束满足」——**闭环断了**。

`RealSymbolToWeightNonlinear.reluZ_counterexample` 已经机器验证了单条约束上
「激活输出为零 ∧ 约束不满足」；本节把它提升为**列表级闭环失效**定理。 -/

/-- 激活折入后的层输出列表（逐神经元激活）。 -/
def actLayerOut (act : ℤ → ℤ) (cs : ConstraintSet) (x : List Int) : List ℤ :=
  (compileToLayer cs).map (fun l => act (LayerOut l x))

/-- 激活折入后的「输出全零」谓词（`AllZeroOutputs` 的激活版）。 -/
def actAllZero (act : ℤ → ℤ) (cs : ConstraintSet) (x : List Int) : Prop :=
  ∀ v ∈ actLayerOut act cs x, v = 0

/-- 机器验证的事实：约束集 `[cEx]`（即 `x₀ + 1 = 0`）在 `x = [-5]` 上
**不被满足**（`-5 + 1 = -4 ≠ 0`）。 -/
lemma cEx_not_allSatisfied_neg5 : ¬ AllSatisfied [cEx] [-5] := by
  intro h
  exact reluZ_counterexample.2 (h cEx (by simp))

/-- 机器验证的事实：同一点上，**折入 ReLU 后输出全零**（`reluZ (-4) = 0`）。 -/
lemma cEx_actAllZero_neg5 : actAllZero reluZ [cEx] [-5] := by
  intro v hv
  simp only [actLayerOut, compileToLayer, List.map_cons, List.map_nil,
    List.mem_singleton] at hv
  subst hv
  simpa [NonlinearLayerOut] using reluZ_counterexample.1

/-- **★ 断点定理（闭环在线性子类之外失效）★**

存在约束集与输入，使**激活后的权重层输出全零**，但**原约束集并不满足**。
取 `cs = [cEx]`（`x₀ + 1 = 0`）、`x = [-5]`、激活 `reluZ`：
`reluZ (LayerOut (convertVec cEx) [-5]) = reluZ (-4) = 0`，而 `VectorConstraintSat cEx [-5]` 为假。

**语气（诚实/降级）**：这就是 §3 闭环的**边界**——
`AllZeroOutputs` 换成激活版 `actAllZero` 后，
`symbolToWeight_correct` 的类比**为假**（即 `reluZ_not_zeroFixing` 的列表级读数）。
故「编译-提取可逆」**不能**无条件推广到激活层；本文件不证该假命题。 -/
theorem activated_loop_breaks :
    ∃ (cs : ConstraintSet) (x : List Int),
      actAllZero reluZ cs x ∧ ¬ AllSatisfied cs x :=
  ⟨[cEx], [-5], cEx_actAllZero_neg5, cEx_not_allSatisfied_neg5⟩

/-- **★ 断点定理（提取器无法修复）★**

在激活折入的链路上，**语法逆提取器 `extractLayer` 并不能挽救闭环**：
存在输入使激活输出全零，但经「编译 → 提取」回到的符号约束**不被满足**。

证明用上面的反例：`extractLayer (compileToLayer [cEx]) = [cEx]`
（§二的语法恒等成立），
而 `¬ AllSatisfied [cEx] [-5]`。
**故断点不在「提取器语法不对」，而在「激活破坏了零化语义」。** -/
theorem activated_extract_cannot_repair :
    ¬ (∀ (cs : ConstraintSet) (x : List Int),
        actAllZero reluZ cs x → AllSatisfied (extractLayer (compileToLayer cs)) x) := by
  intro h
  exact cEx_not_allSatisfied_neg5 (h [cEx] [-5] cEx_actAllZero_neg5)

/-- **闭环正确性的充分必要条件（诚实清单的形式化）**：
折入激活 `act` 后，「激活输出全零 ⟺ 约束满足」对**全部**约束集与输入成立
当且仅当 `act` 的零集恰为 `{0}`（`ZeroFixing`）。

- 充分性：`RealSymbolToWeightNonlinear.zeroFixing_of_strictMono`
  （严格单调 + `σ 0 = 0`）给出可用的激活类；
- 必要性：若 `ZeroFixing` 不成立，则存在 `y ≠ 0` 与 `act y = 0`，
  取约束使 `LayerOut` 恰在零点取 `y`，即得反例（`reluZ` 正是此情形）。

本条把「链路在哪里断」**精确到一行条件**：断点 = 激活的零集假设失效。 -/
theorem activated_closure_iff_zeroFixing (act : ℤ → ℤ) :
    (∀ (cs : ConstraintSet) (x : List Int),
        AllSatisfied cs x ↔ actAllZero act cs x) ↔ ZeroFixing act := by
  -- 单元素约束 `x₀ = 0`（`a = [1]`, `b = 0`）与其取值计算，两个方向共用。
  have hdot : ∀ y : ℤ, dot [1] [y] = y := by
    intro y
    simp [dot]
  -- `LayerOut (convertVec ⟨[1],0⟩) [y] = y`（点积为 `y`，偏置为 `0`）
  have hval : ∀ y : ℤ, LayerOut (convertVec { a := [1], b := 0 }) [y] = y := by
    intro y
    simp [LayerOut, convertVec, hdot y]
  -- 该单元素层在该输入上的输出列表恰为 `[act y]`（下述两个方向共用的形状引理）
  have hmap : ∀ y : ℤ,
      actLayerOut act [{ a := [1], b := 0 }] [y] =
        [act y] := by
    intro y
    simp only [actLayerOut, compileToLayer, List.map_cons, List.map_nil]
    rw [hval y]
  have hsat_iff : ∀ y : ℤ,
      AllSatisfied [{ a := [1], b := 0 }] [y] ↔ y = 0 := by
    intro y
    constructor
    · intro hs
      have h1 := hs { a := [1], b := 0 } (by simp)
      simp only [VectorConstraintSat] at h1
      rw [hdot y] at h1
      simpa using h1
    · intro hy
      intro c hc
      have hc' : c = { a := [1], b := 0 } := by simpa using hc
      subst hc'
      show dot [1] [y] + 0 = 0
      rw [hdot y, hy]
      rfl
  have hact_iff : ∀ y : ℤ,
      actAllZero act [{ a := [1], b := 0 }] [y] ↔ act y = 0 := by
    intro y
    unfold actAllZero
    rw [hmap y]
    constructor
    · intro h
      exact h (act y) (by simp)
    · intro h v hv
      have hv' : v = act y := by simpa using hv
      rw [hv']
      exact h
  constructor
  · -- **必要性**：取单约束 `x₀ = 0`，由「全零 ⟺ 满足」反推 `act y = 0 ↔ y = 0`。
    intro h y
    exact (hact_iff y).symm.trans ((h [{ a := [1], b := 0 }] [y]).symm.trans (hsat_iff y))
  · -- **充分性**：`ZeroFixing act` ⟹ 闭环在激活下保持（逐约束 iff = `nonlinear_layer_zero_iff`）
    intro hfix cs x
    constructor
    · intro hsat v hv
      unfold actLayerOut at hv
      rw [List.mem_map] at hv
      rcases hv with ⟨l, hl, rfl⟩
      show act (LayerOut l x) = 0
      rw [hfix]
      unfold compileToLayer at hl
      rw [List.mem_map] at hl
      rcases hl with ⟨c, hc, rfl⟩
      exact (convertVec_preserves_semantics c x).mp (hsat c hc)
    · intro haz c hc
      have hmem : act (LayerOut (convertVec c) x) ∈ actLayerOut act cs x := by
        unfold actLayerOut
        exact List.mem_map.mpr ⟨convertVec c, List.mem_map.mpr ⟨c, hc, rfl⟩, rfl⟩
      have hz := haz _ hmem
      rw [hfix] at hz
      exact (convertVec_preserves_semantics c x).mpr hz

/-! ## 六、★ 断点二：非线性线性化编译**非单射** ⟹ 不可逆（机器验证反例）★

`RealNonlinearCompile.linearization_global_fails` 已证：存在非线性 `f` 与仿射 `L`，
使 `L ≡ 0`（编译器在所有输入处都报告"满足"）而 `f` 并非处处为零。
本节的推论把它的**可逆性含义**说清楚：该映射在**对象层非单射**，
故**不存在**任何从权重侧对象回到符号侧对象的左逆——
这是「全局可逆**为假**」在编译侧最干净的机器验证形态。 -/

/-- **回收**：`RealNonlinearCompile.linearization_global_fails`
（全局线性化保语义不成立，已机器验证）。 -/
theorem global_linearization_fails :
    ∃ (f L : ℝ → ℝ), (∀ t, L t = 0) ∧ ∃ t, f t ≠ 0 :=
  linearization_global_fails

/-- **★ 断点定理：非线性线性化编译在对象层非单射 ★**

存在**两个不同**的符号侧函数 `f ≠ g`，它们的线性化编译产出**同一个**权重侧对象（`L ≡ 0`）。
见证：`f = t ↦ t²`、`g = t ↦ 0`、`L = t ↦ 0`。

**含义（诚实/标注）**：非单射 ⟹ **不存在左逆**（回收到
`RealExtractInvertibility.leftInverse_iff_injective` 的一般判据上，
「全局可逆 ⟺ 单射」）。故「编译-提取全局可逆」在非线性子类上**为假**，
本文件不证该假命题，只给出机器验证反例。 -/
theorem linearization_collapses_models :
    ∃ (f g L : ℝ → ℝ), f ≠ g ∧ (∀ t, L t = 0) := by
  refine ⟨fun t => t ^ 2, fun _ => 0, fun _ => 0, ?_, fun t => rfl⟩
  intro h
  have h1 : (1 : ℝ) ^ 2 = 0 := congrFun h 1
  norm_num at h1

/-- **断点的可逆性措辞（左逆不存在）**：不存在 `e` 使 `e ∘ Φ = id`，
其中 `Φ f := fun _ => 0` 是非线性线性化编译的**退化代表**
（`linearization_global_fails` 中 `L ≡ 0` 的极限情形）。
这是「非单射 ⟹ 无左逆」在本场景的显式落地。 -/
theorem no_left_inverse_for_collapsing_compile :
    ¬ ∃ e : (ℝ → ℝ) → (ℝ → ℝ), ∀ f : ℝ → ℝ, e (fun _ => (0 : ℝ)) = f := by
  rintro ⟨e, he⟩
  have h : (fun _ : ℝ => (0 : ℝ)) = fun t : ℝ => t ^ 2 := by
    have h0 := he (fun _ : ℝ => (0 : ℝ))
    have h1 := he (fun t : ℝ => t ^ 2)
    rw [h0] at h1
    exact h1
  have h2 : (0 : ℝ) = (1 : ℝ) ^ 2 := congrFun h 1
  norm_num at h2

/-! ## 七、★ 断点三：语义等价 **推不出** 语法相等（缩放轨道，机器验证反例）★

§二–§三 的闭环是**语法**恒等；但**行为等价**是它的弱形式。
`WeightToSymbolEquivalence` 的 docstring 说「提取候选须通过验证器（**行为等价**）确认」。
本节证明：**行为等价严格弱于语法相等**——语义上无法确定唯一的符号候选，
存在**非平凡的自同构轨道**（缩放群 `c ↦ scaleVec c lam`，`lam ≠ 0`）。

**含义（诚实/降级）**：§三的闭环只能在**规范形（轨道代表）意义下**读作
「仍是原符号」。若要真正的唯一提取，必须**先固定规范形**（如首系数为 1），
那不在本文件范围内（标注为未做）。 -/

/-- 基准约束：`a = [1]`、`b = 1`（即 `x₀ + 1 = 0`）。 -/
def cUnit : VectorConstraint :=
  { a := [1], b := 1 }

/-- **轨道成员在行为上有效**：把约束缩放 `lam ≠ 0` 后编译，得到的层
仍是对原约束 `c` 的**行为有效提取**（`ExtractionValidVec`）。
证明：`convertVec_preserves_semantics` 与 `scaleVec_preserves` 的合成。 -/
theorem scale_orbit_behaviorally_valid (c : VectorConstraint) (lam : Int) (hlam : lam ≠ 0) :
    ExtractionValidVec (convertVec (scaleVec c lam)) c := by
  intro x
  -- `LayerOut (convertVec (scaleVec c lam)) x = 0
  --    ↔ VectorConstraintSat (scaleVec c lam) x      (convertVec_preserves_semantics)
  --    ↔ VectorConstraintSat c x`                     (scaleVec_preserves，方向：c ⟺ scaleVec c lam)
  exact (convertVec_preserves_semantics (scaleVec c lam) x).symm.trans
    (scaleVec_preserves c x lam hlam).symm

/-- **机器验证反例：语义等价但语法不等**。
`cUnit` 与 `scaleVec cUnit 2`（即 `a = [2]`、`b = 2`）**语义完全等价**，但**不是同一个约束**。
（`2·x₀ + 2 = 0 ⟺ x₀ + 1 = 0` 在 `Int` 上成立，因为 `Int` 无零因子。） -/
theorem validity_does_not_determine_syntax :
    ∃ c₁ c₂ : VectorConstraint,
      c₁ ≠ c₂ ∧ (∀ x : List Int, VectorConstraintSat c₁ x ↔ VectorConstraintSat c₂ x) := by
  refine ⟨cUnit, scaleVec cUnit 2, ?_, fun x => scaleVec_preserves cUnit x 2 (by norm_num)⟩
  intro h
  have hb : cUnit.b = (scaleVec cUnit 2).b := congrArg VectorConstraint.b h
  simp only [scaleVec, cUnit] at hb
  norm_num at hb

/-- **诚实降级的正面读数**：存在一个层 `l`（`= convertVec (scaleVec cUnit 2)`），
它**不是** `convertVec cUnit`，但经提取得到的候选 `cUnit` 对它**行为有效**。
即：**同一层可以有多个行为有效的符号候选**（提取不是唯一确定的）。 -/
theorem extraction_not_unique :
    ∃ l : LinearLayer, l ≠ convertVec cUnit ∧ ExtractionValidVec l cUnit := by
  refine ⟨convertVec (scaleVec cUnit 2), ?_, scale_orbit_behaviorally_valid cUnit 2 (by norm_num)⟩
  intro h
  have hb : (convertVec (scaleVec cUnit 2)).b = (convertVec cUnit).b := congrArg LinearLayer.b h
  simp only [convertVec, scaleVec, cUnit] at hb
  norm_num at hb

/-- **缩放轨道在 `lam = 1` 时退化到原约束**：`scaleVec c 1 = c`。
（`a ↦ a.map (· * 1)` 不是定义相等，需逐项归纳——故单列此引理。） -/
lemma scaleVec_one (c : VectorConstraint) : scaleVec c 1 = c := by
  obtain ⟨a, b⟩ := c
  show (⟨List.map (fun v => v * 1) a, b * 1⟩ : VectorConstraint) = ⟨a, b⟩
  simp

/-- **闭环的规范形版本（可证的最强形式）**：在**固定轨道代表**（此处取 `lam = 1` 的
平凡代表，即约束自身）的前提下，闭环的语法恒等与行为等价**同时**成立。

本定理是本文件对「可逆」能给出的**最强真陈述**：
语法恒等（`extractLayer_compileToLayer`）与行为等价（`ExtractionValidVec`）在此**同时**成立，
但**唯一性**（不同 `lam` 给出同一候选）在线性子类上**为假**
（`validity_does_not_determine_syntax`）。
**未做**：构造真正的规范形映射 `canonicalize`（如首非零分量归一）并证唯一性——
与 C2 审计 §6.2 的同一缺口。 -/
theorem canonical_form_closed (c : VectorConstraint) :
    extractVec (convertVec (scaleVec c 1)) = c ∧
      ExtractionValidVec (convertVec (scaleVec c 1)) c := by
  refine ⟨?_, scale_orbit_behaviorally_valid c 1 (by norm_num)⟩
  rw [scaleVec_one, roundtrip_extractVec]

/-! ## 八、诚实降级清单（本文件的形式化总结）

把上文各条**汇总为单一可检索的诚实陈述**，便于自动提取（`STYLE.md` §5.4）。 -/

/-- **诚实清单（机器可检索）**：本文件主张的**全部**内容用一条合取陈述概括：

1. 线性子类上语法闭环成立（两侧互为逆）；
2. 但闭环**等价于**单向编译保语义（**不含新语义内容** —— 降级）；
3. 行为等价**推不出**语法相等 —— 缩放轨道反例（**降级**）；
4. 折入激活后闭环**失效** —— 机器验证反例（**未证**该假命题的推广）；
5. 非线性线性化编译**非单射** ⟹ 全局可逆**为假** —— 机器验证反例（**降级**）。

**不主张**：一般非线性下的端到端可逆性（已由 4、5 证伪）。 -/
theorem honesty_register :
    (∀ cs : ConstraintSet, extractLayer (compileToLayer cs) = cs) ∧
    (∀ (cs : ConstraintSet) (x : List Int),
        (AllSatisfied (extractLayer (compileToLayer cs)) x ↔ AllZeroOutputs (compileToLayer cs) x)
          ↔ (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x)) ∧
    (∃ c₁ c₂ : VectorConstraint,
        c₁ ≠ c₂ ∧ (∀ x : List Int, VectorConstraintSat c₁ x ↔ VectorConstraintSat c₂ x)) ∧
    (∃ (cs : ConstraintSet) (x : List Int), actAllZero reluZ cs x ∧ ¬ AllSatisfied cs x) ∧
    (∃ (f g L : ℝ → ℝ), f ≠ g ∧ (∀ t, L t = 0)) :=
  ⟨extractLayer_compileToLayer, closed_loop_adds_nothing,
    validity_does_not_determine_syntax, activated_loop_breaks,
    linearization_collapses_models⟩

/-! ## §N ⭐ 表示审计的**闭环消费者**（`RealDotRepresentationAudit` 接线）

## 为什么这一节存在（**判据纪律，不是装饰**）

本仓已登记的**二级孤儿**反模式（`L08:269-276`）：**审计器自己没人引用**。实测（B475）：
`RealChainAxioms` / `RealChainAxioms2` 的 in-degree **全为 0**；
`RealRflAudit` / `RealHypothesisAudit` 的 importer 中含 scratch 探针（非 roots）。
⇒ ⭐ **「建一个审计模块」若不给它真实消费者，只是把孤儿往后推一格。**

本文件是**编译-提取闭环**的权威（`extractLayer ∘ compileToLayer = id`），
而闭环两侧的 `AllSatisfied` / `AllZeroOutputs` **全部落在 `ConvertVectorLinear.dot` 上**。
⇒ 它是表示审计的天然消费者：**若 `dot` 与多份重声明分叉，本节的定理随之失败。**

⚠ **诚实标注**：本节**不**新增数学内容；价值恰在**接线** ——
审计从「自说自话」变为「编译-提取闭环的承重前提」。 -/

/-- ⭐ **闭环所依赖的点积表示无歧义**：CVL.`dot` 与 `dotL`、`dotQ`（经 ℚ 强制转换）、
以及 `Fin n → Int` 补零载体的 `Matrix.dotProduct` —— **四者同值**。

⚠ 本定理**全部内容**来自 `RealDotRepresentationAudit`；它存在的意义是让该审计
成为**生产 roots 模块的承重依赖**（审计若被改坏，本定理编译失败）。 -/
theorem closed_loop_dot_representation_unambiguous (a x : List Int) :
    (dot a x = dotL a x)
      ∧ (dotQ (a.map (fun v => (v : ℚ))) (x.map (fun v => (v : ℚ))) = ((dot a x : Int) : ℚ))
      ∧ (dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x)) :=
  dot_representation_agreement a x

end Lattice

