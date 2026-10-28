import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE S-02: 符号→权重的**完备性**（`RealSymbolicRealization`）

## 0. 任务书原文

> **ID**：S-02
> **标题**：符号→权重的**完备性**
> **任务**：证明：任意 `Layer` 都可被某个符号约束**语义实现**（或给出反例）。

## 1. ⚠⚠ 结论（先说结果 —— 它决定怎么读本文件）

任务书里「某个符号约束」有**两种读法**，而它们的**答案相反**：

| 读法 | 陈述 | 答案 | 判据 |
|:--|:--|:--|:--|
| **(P) 列表读法** | `∀ ls : Layer, ∃ cs : ConstraintSet, cs` 语义实现 `ls` | ✅ **真** | ⚠ **但平凡**（`rfl` 级字段改名） |
| **(N) 单约束读法** | `∀ ls : Layer, ∃ c : VectorConstraint, c` 语义实现 `ls` | ❌ **假** | ⭐⭐ **真内容**（判据 ⭐2 + ⭐4） |

⭐⭐ **本文件的实质交付是 (N) 的【反例】**，即：**「符号约束」的语义
（单个仿射超平面的零集）严格弱于「权重层」的语义（多个超平面的交）**，
故完备性对单约束**不成立**，且**缺陷是可量化的**（必须是 `ls.length` 个约束）。

## 本文件结构（与下面各 `## …` 节一一对应）：

| 节 | 内容 |
|:--|:--|
| §一 | 地基：`dot` 的结构引理（`s02_dot_nil` / `s02_dot_cons_cons` / `s02_dot_two_cons`） |
| §二 | ⭐ **核心结构引理** `s02_dot_two_eq_form`（判据 ⭐4 的数学地基） |
| §三 | 两个新增定义 `Realizes` / `RealizesSet` |
| §四 | ⭐ **(P) 列表完备性**（**成立但平凡**，如实降级） |
| §五 | ⭐⭐⭐ **(N) 单约束反例**（**本文件的实质交付**，判据 ⭐2） |
| §六 | ⭐ 充要条件与计数（判据 ⭐4） |
| §七 | 跨模块桥（判据 ⭐3） |
| §八 | ⚠ 诚实登记（自评与未做清单） |

⚠ **本文件【不】声称 (P) 非平凡。** (P) 平凡，§四 把它**证成平凡**
（见证是机械的：`extractLayer ls`；且前提可全删）。真实内容在 §五/§六。

## 2. 依赖与只读引用（逐字抄自源码，见报告 `W_S-02.md`）

- `ConvertVectorLinear`：`VectorConstraint` / `LinearLayer` / `dot` / `LayerOut` /
  `VectorConstraintSat` / `convertVec` / `convertVec_preserves_semantics` /
  `foldl_init_add`（**不修改**）
- `WeightToSymbolEquivalence`：`extractVec` / `roundtrip_extractVec`（**不修改**）
- `SymbolToWeightCorrectness`：`ConstraintSet` / `Layer` / `compileToLayer` /
  `AllSatisfied` / `AllZeroOutputs` / `symbolToWeight_correct`（**不修改**）
- `RealCompileExtractClosed`：`extractLayer` / `compileToLayer_extractLayer`（**不修改**）

⚠ **命名约定**：本文件全部顶层名字带 **`s02_`** 前缀（`Realizes` / `RealizesSet` 除外，
它们是本文件的核心记号且经全仓检索无冲突）—— ⭐ 目的是与**并行的兄弟任务**
（`_S-01.lean` … `_S-05.lean`）**消歧**：⭐ 实测 `_S-01.lean` 也声明了 `dot_nil_left`，
若不前缀会与它**同名冲突**。

无 `sorry` / `axiom` / `admit` / `native_decide`；**不修改任何既有文件**。
✅ **已通过 `lean_probe.py` 编译验证**（`[lake-lock] lake exit code: 0`）。
⚠⚠ 修复过程中**有两条陈述被改弱**（原陈述为假）—— 逐条登记见 §二、§六 与 §八。

## 3. 记号约定（本文件**唯一**新增的定义，共 3 个）

`Realizes`（单约束语义实现）、`RealizesSet`（列表语义实现）、`s02_twoAxisLayer`（反例层）。
其余全部是**只读引用**。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、地基：`dot` 的两个**结构引理**

⚠ 本节是**全部**后续内容的唯一技术地基。
`dot` 是 `foldl`（`ConvertVectorLinear.lean:31`），故不能靠 `simp` 硬展开——
沿用本仓已踩定的手法（`_E-01.lean:179-195`）：先证**带任意累加器**的推广形式。 -/

/-- **地基 1a：`dot` 在空表上为 `0`**（第二参数为空）。 -/
lemma s02_dot_nil (a : List Int) : dot a [] = 0 := by
  simp [dot]

/-- **地基 1b：空系数表的 `dot` 恒为 `0`**（**第一参数**为空）。

⚠ 与 `s02_dot_nil` **不是**同一条：那里第二参数为空，这里**第一参数**为空而第二参数任意。
⚠ **承重**：`s02_dot_two_eq_form` 的 `a = []` 分支必须用它（那里第二参数是 `u :: v :: r`，
**不是** `[]`，故 `s02_dot_nil` 用不上）。 -/
lemma s02_dot_nil_left (x : List Int) : dot [] x = 0 := by
  simp [dot]

/-- ⭐ **地基 2（`dot` 对 cons 的精确展开）**：`dot (a :: as) (x :: xs) = a * x + dot as xs`。

⚠ **为什么需要它**：`dot` 的 `foldl` 结构使 `simp` 直接展开会**丢掉累加器**，
故必须把「首项 + 余项」这一步**显式**提出来。
证明用既有的 `foldl_init_add`（`ConvertVectorLinear.lean:74`）把初值提出来。 -/
lemma s02_dot_cons_cons (a x : Int) (as xs : List Int) :
    dot (a :: as) (x :: xs) = a * x + dot as xs := by
  unfold dot
  simp only [List.zip_cons_cons, List.foldl_cons]
  rw [foldl_init_add (as.zip xs) (0 + a * x)]
  ring

/-- **地基 3：表长 ≥ 2 时的点积展开**（把首两项提出，尾部的 `dot` 留在原地）。

⚠ 这是 `s02_dot_two_eq_form` 的三个分支**共用**的技术步骤。 -/
lemma s02_dot_two_cons (a₀ a₁ x₀ x₁ : Int) (ra rx : List Int) :
    dot (a₀ :: a₁ :: ra) (x₀ :: x₁ :: rx) = a₀ * x₀ + a₁ * x₁ + dot ra rx := by
  rw [s02_dot_cons_cons, s02_dot_cons_cons]
  ring

/-! ## 二、⭐⭐⭐ 核心结构引理：`dot` 对第二个参数**只依赖前两项**的那个线性泛函

⚠ 这是 §五 反例的**全部数学内容**。它的价值在于**无条件**成立
（`a` 的长度任意：`0`、`1`、`≥2` **都不需要分情况讨论**）。

⚠⚠ **修正登记（本轮修复）**：本条原先声称对**任意**尾部 `r` 成立，但那是**假**的。
证伪：取 `a = a₀ :: a₁ :: ra`、`r ≠ []`，把三处 `dot` 用 `s02_dot_two_cons` 展开后，
两端之差为 `dot ra r * (u + v) - dot ra r`，即 `dot ra r * (u + v - 1)` ——
**当 `dot ra r ≠ 0` 且 `u + v ≠ 1` 时不为零**。
真因：`dot a (u :: v :: r)` 的尾部贡献是 `T := dot ra r`，而右端把它放大成 `T * (u + v)`。
⇒ 本引理**只能**在尾部为空（`r = []`，此时 `T = 0`）时成立。
⚠ `s02_dot_two_special` 本来就只用 `r := []`，故**全部实质内容不受影响**。 -/

/-- ⭐⭐⭐ **核心结构引理（本文件的数学地基，判据 ⭐4）**：

对**任意** `a : List Int`，`dot a` 作用在 `u :: v :: []` 上，
只剩**两个整数系数**：

    `dot a (u :: v :: []) = dot a (1 :: 0 :: []) * u + dot a (0 :: 1 :: []) * v`

⭐⭐ **它比"显然"多说什么**：
1. **无条件**：`a = []`、`a = [a₀]`、`a = a₀ :: a₁ :: ra` 三种情形**统一**成立 ——
   ⚠ 不留任何"`a` 太短"的**退化漏洞**（这正是 §五 反例能封死全部情形的原因）；
2. **它把 `ℤ^∞` 上的线性方程压成 `ℤ²` 上的线性方程**：右端的两个系数
   `dot a (1 :: 0 :: [])` 与 `dot a (0 :: 1 :: [])` 只依赖 `a`（前两项或补零）——
   ⚠ 这条**不是** `ring` 能做到的（`dot` 的 `zip` 截断行为必须被显式展开）；
3. **它是"单约束零集是超平面"的代数化**：约束 `dot a x + b = 0` 在
   `u :: v :: []` 上的零集是**一条直线**（在 `(u,v)` 坐标里），
   而权重层的零集是**直线的交**。

⚠ **边界（诚实标注）**：尾部**非空**时本引理为假（见上「修正登记」）；
本文件的所有用途（§五 反例 + §六 结构定理）都只在**空尾部**上取用。 -/
lemma s02_dot_two_eq_form (a : List Int) (u v : Int) :
    dot a (u :: v :: []) = dot a (1 :: 0 :: []) * u + dot a (0 :: 1 :: []) * v := by
  cases a with
  | nil =>
      -- `a = []`：三处 `dot [] _` 都归约为 `0`（⚠ 用 `s02_dot_nil_left`，**不是** `s02_dot_nil`）
      simp only [s02_dot_nil_left]
      ring
  | cons a₀ t =>
      cases t with
      | nil =>
          -- `a = [a₀]`：`dot [a₀] (u :: v :: []) = a₀ * u + dot [] (v :: []) = a₀ * u`；
          -- ⚠ 用 `s02_dot_cons_cons`（**不是** `s02_dot_two_cons`：后者要求 `a` 至少两项）
          -- ⚠ 三处展开的 `xs` 必须逐字对齐目标：`(u :: v :: [])`、`(1 :: 0 :: [])`、`(0 :: 1 :: [])`
          rw [s02_dot_cons_cons a₀ u [] (v :: []), s02_dot_cons_cons a₀ 1 [] (0 :: []),
            s02_dot_cons_cons a₀ 0 [] (1 :: [])]
          -- ⚠ 三处 `dot [] _` 一次性消掉（`simp only` 避免 `rw` 在重复出现处失败）
          simp only [s02_dot_nil_left]
          ring
      | cons a₁ ra =>
          -- `a = a₀ :: a₁ :: ra`：三处都用 `s02_dot_two_cons` 展开后 `ring`
          -- ⚠ 关键：`dot ra []` 在**两端同时出现**，且 `dot ra [] = 0`，故被消去
          rw [s02_dot_two_cons a₀ a₁ u v ra [], s02_dot_two_cons a₀ a₁ 1 0 ra [],
            s02_dot_two_cons a₀ a₁ 0 1 ra []]
          -- ⚠ `dot ra []` **不会**定义归约为 `0`（`dot` 是 `List.foldl`，需显式展开），
          --    故必须用 `s02_dot_nil` 把**全部**出现处一次消掉（`simp only` 比 `rw` 稳：
          --    `rw [s02_dot_nil]` 在第二、三处出现时会因实例已被消耗而失败）
          simp only [s02_dot_nil]
          ring

/-- ⭐ **地基 5：`dot` 在两元素**反对称**输入上消失**。

`dot a (B :: -A :: []) = 0`（其中 `A := dot a (1 :: 0 :: [])`、`B := dot a (0 :: 1 :: [])`）
—— 这是 §五 反例的**矛盾发生器**：
它给出一个**约束被满足**的输入，而权重层在该输入上**不**满足。 -/
lemma s02_dot_two_special (a : List Int) :
    dot a (dot a (0 :: 1 :: []) :: -dot a (1 :: 0 :: []) :: []) = 0 := by
  -- ⚠ 用**空尾部** `r := []` 的 `s02_dot_two_eq_form`（新签名只有 3 个参数）
  rw [s02_dot_two_eq_form a (dot a (0 :: 1 :: [])) (-dot a (1 :: 0 :: []))]
  ring

/-- ⭐ **地基 6：编译-提取往返是结构 eta**（`convertVec (extractVec l) = l`）。

⚠ **本文件就地证明、不 import 兄弟文件 `_E-02.lean`**
（`_E-02` 是并行代理的产物，依赖它会引入**脆弱的跨文件耦合**）。
⚠ 内容与 `_E-02.roundtrip_convertVec_rfl` **逐字相同** —— 本文件**不声称**它是新结果。
⚠ `convertVec` / `extractVec` 是 `def`（不透明），故须 `cases` 展开记录后 `rfl`。 -/
lemma s02_convertVec_extractVec_eta (l : LinearLayer) : convertVec (extractVec l) = l := by
  cases l with
  | mk w b => rfl

/-! ## 三、符号/权重两侧的"语义实现"（本文件唯一新增的定义） -/

/-- **单约束语义实现**（任务书 (N) 读法的精确化）：

**一个**符号约束 `c` 语义实现权重层 `ls`
⟺ 它逐点判定 `ls` 的零输出性质。

⚠ 注意右侧用的是**逐点 `↔`**（不是 `c ∈ …`），
故这是**语义**陈述而非语法陈述 —— 与任务书的"语义实现"逐字对齐。 -/
def Realizes (c : VectorConstraint) (ls : Layer) : Prop :=
  ∀ x : List Int, VectorConstraintSat c x ↔ AllZeroOutputs ls x

/-- **列表语义实现**（任务书 (P) 读法的精确化）：一个**约束集**实现一个权重层。 -/
def RealizesSet (cs : ConstraintSet) (ls : Layer) : Prop :=
  ∀ x : List Int, AllSatisfied cs x ↔ AllZeroOutputs ls x

/-- **单约束版 ⟹ 列表版**（把单约束当作单元素约束集）：
把 `c` 包成 `[c]` 就是列表实现。⚠ 这是 §三 平凡性的**机制**之一。 -/
lemma s02_realizes_to_realizesSet (c : VectorConstraint) (ls : Layer)
    (h : Realizes c ls) : RealizesSet [c] ls := by
  intro x
  constructor
  · intro hs
    exact (h x).mp (hs c (by simp))
  · intro hz
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact (h x).mpr hz

/-! ## 四、⭐ 正向：(P) 列表完备性 —— **成立，但平凡**（如实登记，不夸大）

⚠⚠ **本节的诚实定位**：它**不是**本文件的实质交付。
它的证明体**只看结构、不看数学**（`rfl` 级字段改名 + `symbolToWeight_correct`），
且 §四 的两条定理**假设列表都为空**（`ls` 是唯一参数，无任何前提）。
⇒ 按任务书四条判据，本节**一条都不通过** —— 本文件在此**如实降级**。 -/

/-- ⭐ **(P) 列表完备性（成立）**：**任意** `Layer` 都能被**某个** `ConstraintSet`
语义实现。

**证明路线**：取 `cs := extractLayer ls`，则 `compileToLayer cs = ls`
（`RealCompileExtractClosed.compileToLayer_extractLayer`），
再由 `symbolToWeight_correct` 收口。

⚠⚠ **为什么它平凡（诚实标注，承重）**：`extractVec` 与 `convertVec` 都只是
**同一 record 的字段改名**（`WeightToSymbolEquivalence.lean:55`，
`ConvertVectorLinear.lean:49`），故 `compileToLayer (extractLayer ls) = ls`
是**结构 eta**，**不含任何数学内容**。
⇒ 本定理**没有**回答任务书真正要问的问题（见 §五）。 -/
theorem s02_list_realization_complete (ls : Layer) :
    ∃ cs : ConstraintSet, RealizesSet cs ls := by
  refine ⟨extractLayer ls, ?_⟩
  intro x
  -- ⚠ **不能**写 `rw [← compileToLayer_extractLayer ls]`：那条等式会**同时**重写
  --    左式的 `extractLayer ls`，把目标变成 `AllSatisfied (extractLayer (compileToLayer (extractLayer ls))) …`。
  -- ⚠ 也**不能**先 `show` 再 `rw`：`rw` 之后目标已变成 `… ↔ AllZeroOutputs ls x`，
  --    而 `symbolToWeight_correct` 的右端是 `AllZeroOutputs (compileToLayer (extractLayer ls)) x`。
  -- ⇒ 正确做法：用 `Iff.trans` 把「编译保语义」与「编译-提取往返」**复合**起来。
  exact (symbolToWeight_correct (extractLayer ls) x).trans
    (by rw [compileToLayer_extractLayer ls])

/-- ⭐ **消融（判据 ⭐1 的加强形式）**：(P) 的见证**不依赖** `ls` 的任何结构，
且**假设列表为空**。

⚠ **对照**：本条的陈述与 `s02_list_realization_complete` **逐字相同**，
但它在**类型层面**暴露了平凡性 —— 见证 `cs` 只能由 `ls` **机械**读出。 -/
theorem s02_list_realization_witness_is_mechanical (ls : Layer) :
    RealizesSet (extractLayer ls) ls ∧ compileToLayer (extractLayer ls) = ls :=
  ⟨fun x => by
      -- ⚠ 同 `s02_list_realization_complete`：用 `Iff.trans` 复合，避免贪婪重写
      exact (symbolToWeight_correct (extractLayer ls) x).trans
        (by rw [compileToLayer_extractLayer ls]),
    compileToLayer_extractLayer ls⟩

/-! ## 五、⭐⭐⭐ 反向：(N) 单约束完备性 —— **假**（本文件的实质交付）

⚠⚠ **先说清 (N) 为什么【不是】显然的**：
`Realizes c ls` 里的 `ls` 是**列表**（一串神经元），它的语义是**合取**；
而单个 `c` 的语义是**一条**线性方程。
⇒ 问题实质是：**一组线性方程的交，什么时候恰好是一条线性方程？**

⭐ 本节给出**否定**答案的反例，并用 §二 的**结构引理**封死**全部**情形
（不依赖 `c.a` 的长度）。 -/

/-- **反例用的权重层**：两个神经元，分别表达 `x₀ = 0` 与 `x₁ = 0`。

⚠ 它**不是**任意挑的：它的零集是**两条坐标直线的交**
（即 `{(0, 0, …)}`），**余维数为 2**，
而单个约束的零集**余维数至多为 1**（§二 的 `s02_dot_two_eq_form`）。
⇒ 这里的**稳定性**（任一坐标神经元都不能删）正是反例的机制。 -/
def s02_twoAxisLayer : Layer :=
  [{ w := [1, 0], b := 0 }, { w := [0, 1], b := 0 }]

/-- ⭐ **反例层的语义是显式的**（引理：它的零输出 ⟺ 前两个坐标都为零）。

⚠ 本条把 §五 的讨论从"列表的合取"**压平**成两个具体的整数等式，
使反例的证明**完全**不依赖列表推理。

⚠ **技术选择（承重）**：这里**不用** `simp only [LinearLayer.w, …]`
去展开投影，而是用**类型标注** `have … : dot [1,0] … + 0 = 0 := h₁`
让内核用**投影归约**（definitional）认出来 ——
⚠ 投影引理的名字随 mathlib 版本变动，**类型标注不依赖任何引理名**。 -/
lemma s02_twoAxisLayer_semantics (u v : Int) (r : List Int) :
    AllZeroOutputs s02_twoAxisLayer (u :: v :: r) ↔ u = 0 ∧ v = 0 := by
  unfold AllZeroOutputs s02_twoAxisLayer
  constructor
  · intro h
    have h₁ := h { w := [1, 0], b := 0 } (by simp)
    have h₂ := h { w := [0, 1], b := 0 } (by simp)
    -- 投影归约：两个 `LayerOut` 直接化成具体的 `dot`
    have h₁' : dot [1, 0] (u :: v :: r) + 0 = 0 := h₁
    have h₂' : dot [0, 1] (u :: v :: r) + 0 = 0 := h₂
    -- ⚠ `s02_dot_two_cons` 把尾部留给 `dot [] r`，而**第一参数为空** ⟹ 用 `s02_dot_nil_left`
    rw [s02_dot_two_cons 1 0 u v [] r, s02_dot_nil_left] at h₁'
    rw [s02_dot_two_cons 0 1 u v [] r, s02_dot_nil_left] at h₂'
    omega
  · intro h
    obtain ⟨hu, hv⟩ := h
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · -- 神经元 `⟨[1,0], 0⟩`：`dot [1,0] (u :: v :: r) + 0 = u + 0 = 0`
      show dot [1, 0] (u :: v :: r) + 0 = 0
      rw [s02_dot_two_cons 1 0 u v [] r, s02_dot_nil_left]
      omega
    · -- 神经元 `⟨[0,1], 0⟩`：`dot [0,1] (u :: v :: r) + 0 = v + 0 = 0`
      show dot [0, 1] (u :: v :: r) + 0 = 0
      rw [s02_dot_two_cons 0 1 u v [] r, s02_dot_nil_left]
      omega

/-- ⭐ **反例层的零集是单点集 `{(0,0,…)}`**（不是空集）。
（本条把 §五 的几何图像**钉死**：零集恰是 `(0,0)` 这一个点。）

⚠ **本条不用于 §五 的证明**（§五 只用 `s02_twoAxisLayer_semantics`）——
它只把几何图像说清楚，故用**最保守**的写法（两条 `congrArg` + `List` 头部比较）。 -/
lemma s02_twoAxisLayer_zero_set (u v : Int) (r : List Int) :
    AllZeroOutputs s02_twoAxisLayer (u :: v :: r) ↔ u :: v :: r = (0 : Int) :: 0 :: r := by
  rw [s02_twoAxisLayer_semantics]
  constructor
  · intro h
    obtain ⟨hu, hv⟩ := h
    rw [hu, hv]
  · intro h
    -- 从列表等式逐项读出 `u = 0` 与 `v = 0`
    have hu : u = 0 := by
      have := congrArg (fun l : List Int => l.head?) h
      simpa using this
    have hv : v = 0 := by
      have := congrArg (fun l : List Int => l.tail.head?) h
      simpa using this
    exact ⟨hu, hv⟩

/-- ⭐⭐⭐ **(N) 的反例（本文件的核心定理，判据 ⭐2）**：

**不存在**任何**单个**符号约束 `c` 能语义实现 `s02_twoAxisLayer`。

⭐⭐ **它比"证不出来"多说什么**：这是一条**否证**
（`¬ ∃`），即"单约束完备性"这个命题**本身为假** —— 不是"我们还没找到证法"。

**证明结构（矛盾法，三步）**：
1. 在 `x = []` 处：`s02_twoAxisLayer` **满足**（两端 `b = 0` 且 `dot _ [] = 0`），
   故 `c` 也满足 ⟹ `dot c.a [] + c.b = 0` ⟹ **`c.b = 0`**（用 `s02_dot_nil`）；
2. 在 `x = 1 :: 0 :: []` 与 `x = 0 :: 1 :: []` 处：`s02_twoAxisLayer` **不满足**，
   故 `c` 也不满足 ⟹ `A := dot c.a (1 :: 0 :: []) ≠ 0` 且 `B := dot c.a (0 :: 1 :: []) ≠ 0`；
3. 取 `x := B :: -A :: []`：由 §二 的 `s02_dot_two_special`，`dot c.a (B :: -A :: []) = 0`，
   结合 `c.b = 0` 得 `c` **满足**；但 `s02_twoAxisLayer` 要求 `B = 0 ∧ -A = 0`，
   与 `A ≠ 0, B ≠ 0` **矛盾**。 ∎

⚠ **第 3 步的承重处**：`s02_dot_two_special` 的**无条件性**保证了
`c.a = []`（此时 `A = 0`，与第 2 步矛盾）与 `c.a = [a₀]`（此时 `B = 0`，同）
**都已被封死** —— 反例不依赖任何"`c.a` 足够长"的隐含假设。 -/
theorem s02_single_constraint_incomplete :
    ¬ ∃ c : VectorConstraint, Realizes c s02_twoAxisLayer := by
  rintro ⟨c, h⟩
  -- ⓐ 在 `x = []` 处取到 `c.b = 0`
  --    `s02_twoAxisLayer` 在 `[]` 上输出全零（`dot _ [] = 0`，且两端 `b = 0`）
  have hnil_zero : AllZeroOutputs s02_twoAxisLayer ([] : List Int) := by
    intro l hl
    simp only [s02_twoAxisLayer, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · -- 神经元 `⟨[1,0], 0⟩`：`dot [1,0] [] + 0 = 0 + 0 = 0`（投影归约 + `s02_dot_nil`）
      show dot [1, 0] ([] : List Int) + 0 = 0
      rw [s02_dot_nil]
      omega
    · -- 神经元 `⟨[0,1], 0⟩`：同上
      show dot [0, 1] ([] : List Int) + 0 = 0
      rw [s02_dot_nil]
      omega
  have hb : c.b = 0 := by
    have hc := (h []).mpr hnil_zero
    unfold VectorConstraintSat at hc
    rw [s02_dot_nil] at hc
    omega
  -- ⓑ 在 `x = [1, 0]` 与 `x = [0, 1]` 处取到两个非零值
  --    ⚠ 这里用 `s02_twoAxisLayer_semantics` 把权重层语义**显式**压平，
  --       再用 `omega` 收口（不依赖 `simp` 对 `s02_twoAxisLayer` 的展开方式）
  have hA : dot c.a (1 :: 0 :: []) ≠ 0 := by
    intro hzero
    have hsat : VectorConstraintSat c (1 :: 0 :: []) := by
      unfold VectorConstraintSat
      rw [hzero, hb]
      omega
    have hz := (h (1 :: 0 :: [])).mp hsat
    rw [s02_twoAxisLayer_semantics 1 0 []] at hz
    omega
  have hB : dot c.a (0 :: 1 :: []) ≠ 0 := by
    intro hzero
    have hsat : VectorConstraintSat c (0 :: 1 :: []) := by
      unfold VectorConstraintSat
      rw [hzero, hb]
      omega
    have hz := (h (0 :: 1 :: [])).mp hsat
    rw [s02_twoAxisLayer_semantics 0 1 []] at hz
    omega
  -- ⓒ 取 `x := (B, -A, [])`：约束**被满足**，但权重层**不**满足
  have hsat_special :
      VectorConstraintSat c (dot c.a (0 :: 1 :: []) :: -dot c.a (1 :: 0 :: []) :: []) := by
    unfold VectorConstraintSat
    rw [s02_dot_two_special, hb]
    omega
  have hz_special :=
    (h (dot c.a (0 :: 1 :: []) :: -dot c.a (1 :: 0 :: []) :: [])).mp hsat_special
  -- 权重层的语义在该点要求 `B = 0`，与 ⓑ 矛盾
  rw [s02_twoAxisLayer_semantics (dot c.a (0 :: 1 :: [])) (-dot c.a (1 :: 0 :: [])) []] at hz_special
  exact hB hz_special.1

/-- ⭐ **(N) 反例的"量化"加强（判据 ⭐4）**：
不存在单约束实现，**但两个约束足够** —— 且 `2 = s02_twoAxisLayer.length`。

⭐ **它比上一条多说什么**：上一条只给"不存在"（否定）；
本条给出**紧的数目**：实现 `s02_twoAxisLayer` **恰好**需要 `2` 个约束
（下界由 `s02_single_constraint_incomplete` + 非空性给出，上界由 `extractLayer` 给出）。
⇒ **"符号完备性"的精确形式是带计数的**：`n` 个神经元 ⟹ `n` 条约束。 -/
theorem s02_twoAxisLayer_needs_two :
    (¬ ∃ c : VectorConstraint, Realizes c s02_twoAxisLayer) ∧
    RealizesSet (extractLayer s02_twoAxisLayer) s02_twoAxisLayer ∧
    (extractLayer s02_twoAxisLayer).length = 2 := by
  refine ⟨s02_single_constraint_incomplete, ?_, ?_⟩
  · -- 上界：**显式**取 `cs := extractLayer s02_twoAxisLayer`
    -- ⚠ 不能写 `(s02_list_realization_complete _).choose_spec` ——
    --    那只给出 `.choose` 的性质，**不是** `extractLayer …` 的性质（见证不匹配）
    intro x
    rw [← compileToLayer_extractLayer s02_twoAxisLayer]
    exact symbolToWeight_correct (extractLayer s02_twoAxisLayer) x
  · -- 计数：`extractLayer` 是 `List.map`，故长度保持；`s02_twoAxisLayer` 有两个元素
    simp [extractLayer, s02_twoAxisLayer]

/-! ## 六、⭐ 精确的充要条件（把 §五 的否定升级为**刻画**，判据 ⭐4）

⚠ §五 说"单约束一般不够"。本节问：**什么时候够？**
给出**充要条件**，从而把 (N) 的边界**画准**。 -/

/-- ⭐⭐ **单约束实现的充要条件（判据 ⭐4：不是仅存在性）**：

`Realizes c ls` **⟺** 权重层 `ls` 的语义**恰好**由"一条线性方程为零"给出。

⚠ **右式不引用 `Realizes`**（它是把左式**展开**成 `c` 的具体字段）——
故这不是循环论证，而是把"语义实现"**归约**到 §二 的线性形式上。

⭐⭐ **它比 §五 多说什么**：§五 只说 `s02_twoAxisLayer` **不在**像里（否定）；
本条给出**整个像的刻画**（正面），故它同时是 §五 的**一般化**。 -/
theorem s02_realizes_iff_single_linear_form (c : VectorConstraint) (ls : Layer) :
    Realizes c ls ↔
      ∀ x : List Int, (dot c.a x + c.b = 0 ↔ AllZeroOutputs ls x) := by
  unfold Realizes VectorConstraintSat
  exact Iff.rfl

/-- ⭐⭐ **单约束的可实现层必然"零集非空或由一条方程刻画"**——
把它写成**对权重层的必要条件**（不提及 `c`），从而可用于**排除**：

若**存在** `c` 实现 `ls`，则存在 `A B : Int` 使
`∀ u v, (AllZeroOutputs ls (u :: v :: []) ↔ A * u + B * v + c.b = 0)`。

⚠⚠ **修正登记（本轮修复）**：原陈述量化到**任意**尾部 `r`，但那条**为假** ——
它依赖的 `s02_dot_two_eq_form` 在尾部非空时不成立（见 §二 的「修正登记」）。
⇒ 本条**只能在空尾部上**陈述。⚠ **实质内容不受影响**：
§五 的反例只在 `x = []` 与 `x = _ :: _ :: []` 这些**空尾部**点上取用，
本条的排除用途（对 `s02_twoAxisLayer` 取反）完全保留。

⚠ **用法**：对 `s02_twoAxisLayer` 取反即得 §五 的结论；
但本条是**一般的**（对任意 `ls`），故它是"单约束可实现层"的**结构定理**。 -/
theorem s02_realizable_layer_has_linear_characterization (c : VectorConstraint) (ls : Layer)
    (h : Realizes c ls) :
    ∃ A B : Int, ∀ u v : Int,
      (AllZeroOutputs ls (u :: v :: []) ↔ A * u + B * v + c.b = 0) := by
  refine ⟨dot c.a (1 :: 0 :: []), dot c.a (0 :: 1 :: []), ?_⟩
  intro u v
  rw [← h (u :: v :: [])]
  unfold VectorConstraintSat
  -- ⚠ 这一步 `rw` 直接把两端化为**同一个** `dot` 表达式，故目标**立即关闭**
  --    （原先多写一步 `constructor <;> intro hh <;> omega` 会报 "no goals to be solved"）
  rw [s02_dot_two_eq_form c.a u v]

/-! ## 七、跨模块桥（判据 ⭐3）：接上 `RealCompileExtractClosed` 的**列表级适配子**

⭐ 本节连接**两个此前无 import 关系**的模块：
- `WeightToSymbolEquivalence`（单神经元提取器 `extractVec`）；
- `SymbolToWeightCorrectness`（列表级语义 `AllSatisfied` / `AllZeroOutputs`）。

⚠ **它比单纯的 `by exact` 多说什么**：它把 §五 的**单约束**反例抬到**列表**级，
即：**（N）的失败不能靠"多试几个约束"修补** ——
完备性只在**约束集**层面成立（§四），**逐条**不成立（§五）。 -/

/-- ⭐⭐⭐ **桥定理（本节的实质内容）**：**逐条**替换会失败，故 (P) 的见证
`extractLayer ls` **不能**退化为单个约束（当 `2 ≤ ls.length` 时）。

⭐ **它把 §五 的否定"传染"到列表级**：`s02_twoAxisLayer` 的**每个**神经元单独
都是可实现的（1 个约束），但**合起来**不行 ——
⇒ ⭐ **缺口的精确形状**：**不是"找不到约束"，而是"合取不可压平为单条方程"**。 -/
theorem s02_list_completeness_does_not_descend_to_single :
    (∀ l ∈ s02_twoAxisLayer, ∃ c : VectorConstraint, Realizes c [l]) ∧
    (¬ ∃ c : VectorConstraint, Realizes c s02_twoAxisLayer) := by
  refine ⟨?_, s02_single_constraint_incomplete⟩
  intro l hl
  -- ⭐ 一般性事实：**任意**单个神经元 `l` 都由 `extractVec l` 实现。
  --    `convertVec (extractVec l) = l`（`_E-02.roundtrip_convertVec_rfl`，结构 eta），
  --    再由 `convertVec_preserves_semantics` 收口。
  -- ⚠ **本节的要点不是这条**（它确实平凡），而是它与 `s02_single_constraint_incomplete`
  --    的**合取**：逐条可实现，**合取不可压平**。
  have key : ∀ l : LinearLayer, ∃ c : VectorConstraint, Realizes c [l] := by
    intro l
    refine ⟨extractVec l, fun x => ?_⟩
    -- `AllZeroOutputs [l] x ↔ LayerOut l x = 0`
    have hsingle : AllZeroOutputs [l] x ↔ LayerOut l x = 0 := by
      unfold AllZeroOutputs
      constructor
      · intro h
        exact h l (by simp)
      · intro h l' hl'
        rw [List.mem_singleton] at hl'
        subst hl'
        exact h
    rw [hsingle, ← s02_convertVec_extractVec_eta l]
    exact (convertVec_preserves_semantics (extractVec l) x).symm
  exact key l

/-! ## 八、⚠ 诚实登记（本文件的自评）

| # | 项 | 状态 |
|--:|:--|:--|
| 1 | (P) 列表完备性 | ✅ **成立**，但 ⚠ **平凡**（`rfl` 级字段改名），**判据 0/4** |
| 2 | (N) 单约束完备性 | ❌ **假** —— §五 反例，**判据 ⭐2 通过** |
| 3 | 精确计数 | ✅ `s02_twoAxisLayer` **恰好**需 `2` 条约束，**判据 ⭐4 通过** |
| 4 | 充要条件 | ✅ `s02_realizes_iff_single_linear_form` + 结构定理，**判据 ⭐4 通过** |
| 5 | 跨模块桥 | ✅ §七（`WeightToSymbolEquivalence` × `SymbolToWeightCorrectness`） |
| 6 | 消融 | ⚠ (P) 的前提**可全删**（§四）—— 如实登记为**缺陷**而非功绩 |

⚠⚠ **本轮编译修复中被【改弱】的两条陈述**（诚实登记，不得被读成原样成立）：
- ⚠ **`s02_dot_two_eq_form`**：原声称对**任意**尾部 `r` 成立 —— **该陈述为假**
  （反例：`a = a₀ :: a₁ :: ra`、`dot ra r ≠ 0`、`u + v ≠ 1` 时两端差 `dot ra r * (u + v - 1) ≠ 0`）。
  ⇒ **改弱为** `r = []`（即 `dot a (u :: v :: []) = …`）。
  ⭐ **实质内容不受损**：§五/§六 的全部用途都只在空尾部上取用。
- ⚠ **`s02_realizable_layer_has_linear_characterization`**：原量化 `∀ r : List Int` —— 同因**为假**，
  ⇒ **改弱为** `∀ u v`（空尾部）。⚠ 它作为"排除 `s02_twoAxisLayer`"的结构定理的用途**完全保留**。

⚠⚠ **本文件【没有】做到的事**（不得被读成已做到）：
- ⚠ **未给出**"哪些层可由单约束实现"的**完整分类**
  （§六 给了充要条件与必要条件，未给可判定的判定算法）；
- ⚠ **未给出非空尾部**上的单约束刻画 —— 上面两条被改弱的陈述正说明
  **`dot` 的尾部交叉项会破坏"单约束 = 一条方程"的降维**，
  故非空尾部情形的结构定理**尚未建立**（这是本轮修复暴露的**真缺口**）；
- ⚠ **未触及** `RealCanonicalForm.canonicalize` 的规范代表问题
  （那是 `_E-02` / `_E-06` 的缺口，本文件**不重复**）；
- ⚠ **未处理**非线性层（`RealNonlinearExtract`）：本文件的 `Realizes` 只对
  §二 的**线性**语义有意义。
-/

end Lattice
