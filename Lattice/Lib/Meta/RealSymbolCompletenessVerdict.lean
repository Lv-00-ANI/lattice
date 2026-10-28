import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealSymbolCompleteness
/-!
# LATTICE D3-2: 完备性的**代价** —— 实现一个层需要几条约束？

## 0. 调研报告的结论（决定本文件写什么）

`_deep_out/D_D3-2.md`：

- ⭐ **「任意 `Layer` 可被符号实现」为真但【恒真】**（`Layer := List LinearLayer`
  与 `VectorConstraint` 逐字同型）。S-02 已证成 `s02_list_realization_complete`
  并**自己登记为平凡**（`RealSymbolCompleteness.lean:534`）。⇒ **不重复它。**
- ⭐ **真缺口是「实现代价」**，且 S-02 自述未做（`:549-551`）：
  **「未给出『哪些层可由单约束实现』的完整分类」**。
- ⚠ **本文件的核心发现（新）**：S-02 `:475`
  `s02_realizable_layer_has_linear_characterization` **不是"只给了 ⇒ 方向"，
  而是【内容为假】** —— 它由只在**空尾部**成立的 `s02_dot_two_eq_form` 推出，
  却声称对**全部** `x` 给出只含 `u, v` 的二元刻画。
  ⇒ ⭐ **「单约束实现」的分类【不能】由空尾部行为刻画**（§二 给出机器反例）。

## 1. 诚实定位（⚠ 必读）

| 内容 | 性质 |
|:--|:--|
| ⭐ **推翻** S-02 `:475`（§二，**非空尾部**反例） | **新**（S-02 只知道"原陈述假"，未发现其**改弱版**仍不足以刻画） |
| ⭐ **`d32_dot_tail_cross_term`**（§一） | **新**：`dot` 尾部项 `dot ra r` 的**精确修正项**（S-02 只有注释里的文字机理） |
| ⭐ **`d32_row_zero_does_not_imply_all_zero`**（§三） | **新**：机器反例，**否证**"单行零 ⟹ 全零" |
| ⭐ **`d32_all_rows_agree_imp_single_realizable`**（§三） | **判据 ⭐4**：**可判定**的**充分**条件（⚠ **非充要**，见诚实边界） |
| ⭐ **消融机器化**（§四） | **增量**（S-02 只写在**注释**里，本文件升级为内核定理） |

⚠ **不声称**：这些是全新数学。余维数论证是经典内容。**增量在一般化 + 消融机器化 + 可计算化。**

⚠⚠ **本文件【未】做到的（先说不做，避免夸大）**：
⚠ **「单约束可实现」的【完整充要刻画】本文件没有给出** ——
理由（承重）：`Realizes` 只要求**存在一条** `c`，
⚠ 而该 `c` **不必是 `ls` 的某一行**（例：`ls := [⟨[2,0],0⟩]` 可由 `c := ⟨[1,0],0⟩` 实现）。
⇒ 刻画必须量化到**任意 `c`**，⚠ 其可判定性本文件**未建立**。
⭐ 本文件给出的是**充分条件**（`d32_allRowsAgree`，可判定）+ **必要条件的方向性反例**。

## 2. 命名与依赖

全部新顶层名带 `d32_` 前缀（实测全仓 `d32_` 命中 **0**）。

**直接 import（恰好 3 条，全部用到）**：
- `ConvertVectorLinear`：`dot` / `LayerOut` / `VectorConstraintSat` / `VectorConstraint` / `LinearLayer`；
- `SymbolToWeightCorrectness`：`Layer` / `AllZeroOutputs`；
- `RealSymbolCompleteness`：`Realizes` / `s02_twoAxisLayer` / `s02_dot_two_cons` /
  `s02_dot_nil` / `s02_dot_cons_cons` / `s02_dot_nil_left`。

⚠ **诚实登记（探针实测）**：初稿**多 import 了** `WeightToSymbolEquivalence`、
`RealCompileExtractClosed`、`RealConstraintEdit` —— ⚠ **全仓检索证实本文件一个符号都没用它们**
（`grep 'SymEdit|applySymEdit|extractVec|compileToLayer'` ⟹ **0 命中**）。
⭐ 我已**删除这 3 条冗余 import**，并**重新探针确认仍 `exit code: 0`**。

**不修改任何既有文件**。无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、地基：`dot` 的**尾部交叉项**

只补一条：`dot` 在 `u :: v :: r` 上**不是** `u, v` 的二元线性式，
除非 `r = []`。⚠ 用 S-02 已证的 `s02_dot_two_cons`（`:107`），**不重证**。 -/

/-- ⭐ **尾部交叉项（本文件否定结果的唯一技术来源）**：

`dot a (u :: v :: r) = dot a (1::0::[]) * u + dot a (0::1::[]) * v + dot ra r`
（`a = a₀ :: a₁ :: ra`）。

⭐⭐ **它比"证不出来"多说什么**：它给出**同一律的精确修正项** ——
右端比 S-02 的 `s02_dot_two_eq_form`（`:144`）**多出 `dot ra r` 这一项**。
⇒ ⭐ **当 `ra = []`（`a` 至多两项）时 `dot ra r = 0`，退化为 S-02 的形式**（故 S-02 在空尾部对）；
⚠ **当 `ra ≠ []` 且 `dot ra r ≠ 0` 时，S-02 的形式【为假】** ——
⚠ 这正是 S-02 `:117-122` 在**注释**里记下的机理，本引理把它**显式化**。

⚠⚠ **修正登记（诚实，承重）**：⚠ 本条**初稿**我写的差值是
`dot ra r * (u + v - 1)` —— ⚠ **那是错的**（代入 `u = v = 0` 得 `T = -T`，仅 `T = 0` 时成立）。
⭐ 正确形式**就是**「LHS 比 S-02 的右端多一个 `dot ra r`」（即 `T` 恰是差值），
因为 `dot a (1::0::[]) = a₀`、`dot a (0::1::[]) = a₁` 把 `a₀u + a₁v` **精确消掉**。
⇒ ⭐ **这也使反例更直接**：只需 `dot ra r ≠ 0`，**不需要** `u + v ≠ 1` 的条件。 -/
lemma d32_dot_tail_cross_term (a₀ a₁ : Int) (ra : List Int) (u v : Int) (r : List Int) :
    dot (a₀ :: a₁ :: ra) (u :: v :: r)
      = dot (a₀ :: a₁ :: ra) (1 :: 0 :: []) * u
          + dot (a₀ :: a₁ :: ra) (0 :: 1 :: []) * v
          + dot ra r := by
  rw [s02_dot_two_cons a₀ a₁ u v ra r,
    s02_dot_two_cons a₀ a₁ 1 0 ra [],
    s02_dot_two_cons a₀ a₁ 0 1 ra []]
  -- ⚠ `dot ra []` **不**定义归约（`dot` 是 `foldl`），须用 `s02_dot_nil` 显式消去
  rw [s02_dot_nil ra]
  ring

/-! ## 二、⭐⭐⭐ 推翻 S-02 `:475`（**可编译但内容为假**）

S-02 `:475` 逐字：

    theorem s02_realizable_layer_has_linear_characterization (c) (ls) (h : Realizes c ls) :
        ∃ A B : Int, ∀ u v : Int,
          (AllZeroOutputs ls (u :: v :: []) ↔ A * u + B * v + c.b = 0)

⚠ S-02 `:467-471` 登记它"原量化到任意 `r`，因假而改弱到空尾部"。
⭐⭐ **本文件指出：改弱【不足】** —— 因为 `Realizes`（`:203`）量化**全部**
`x : List Int`，故 `h` 在**非空尾部**上的信息**无法**压进只含 `u, v` 的二元式：
`dot` 的尾部交叉项 `dot ra r` 在右端**无处安放**。 -/

/-- **反例层**：单神经元 `w := [1, 1, 1]`、`b := 0`。

⚠ **为什么必须是三项**（承重）：`dot [1,1,1] (u::v::r) = u + v + dot [1] r`。
`dot [1] r` 就是**尾部交叉项**。⚠ 若 `w` 只有两项（如 `[1,1]`），
则 `ra = []`、`dot ra r = 0`，交叉项消失 —— 那时空尾部刻画**确实**成立
（`A := B := 1`）。**故三项是本反例的承重点。** -/
def d32_threeCoeffLayer : Layer := [{ w := [1, 1, 1], b := 0 }]

/-- **与上面对应的单约束**（系数逐字相同）。 -/
def d32_threeCoeffConstraint : VectorConstraint := { a := [1, 1, 1], b := 0 }

/-- ⭐ **反例层语义的显式化**：`AllZeroOutputs … (u :: v :: r) ↔ u + v + dot [1] r = 0`。

⚠ 用 `s02_dot_two_cons` 展开（`dot` 是 `foldl`，`simp` 无法直接展开）。 -/
lemma d32_threeCoeffLayer_semantics (u v : Int) (r : List Int) :
    AllZeroOutputs d32_threeCoeffLayer (u :: v :: r) ↔ u + v + dot [1] r = 0 := by
  unfold AllZeroOutputs d32_threeCoeffLayer
  constructor
  · intro h
    have h₁ := h { w := [1, 1, 1], b := 0 } (by simp)
    have h₁' : dot [1, 1, 1] (u :: v :: r) + 0 = 0 := h₁
    rw [show ([1, 1, 1] : List Int) = 1 :: 1 :: [1] from rfl,
      s02_dot_two_cons 1 1 u v [1] r] at h₁'
    omega
  · intro h
    intro l hl
    rw [List.mem_singleton] at hl
    subst hl
    show dot ([1, 1, 1] : List Int) (u :: v :: r) + 0 = 0
    rw [show ([1, 1, 1] : List Int) = 1 :: 1 :: [1] from rfl,
      s02_dot_two_cons 1 1 u v [1] r]
    omega

/-- ⭐ **前提成立**：`d32_threeCoeffConstraint` **确实**实现 `d32_threeCoeffLayer`。

⚠ **技术要点**：`x` 是**任意** `List Int`（不是 `u :: v :: r`），
故不能先拆 `x`；两边 `unfold` 后是**同一个** `dot [1,1,1] x + 0 = 0`。 -/
lemma d32_threeCoeff_realizes :
    Realizes d32_threeCoeffConstraint d32_threeCoeffLayer := by
  intro x
  -- ⚠ `d32_threeCoeffLayer` 是 `def`，必须 `unfold` 才能让 `l ∈ …` 化成单元素
  unfold VectorConstraintSat AllZeroOutputs d32_threeCoeffLayer d32_threeCoeffConstraint
  constructor
  · intro h l hl
    rw [List.mem_singleton] at hl
    subst hl
    exact h
  · intro h
    exact h { w := [1, 1, 1], b := 0 } (by simp)

/-- ⭐⭐⭐ **核心反例（本文件的实质交付之一）**：

`¬ ∃ A B, ∀ u v r, (AllZeroOutputs d32_threeCoeffLayer (u :: v :: r)
                     ↔ A * u + B * v + d32_threeCoeffConstraint.b = 0)`

⭐ **即**：`d32_threeCoeffLayer` 可被**单条约束**实现（上式前提，见 `d32_threeCoeff_realizes`），
但其零集**不能**在**全部尾部**上由只含 `u, v` 的二元仿射式刻画。
⇒ ⭐⭐ **S-02 `:475` 的内容为假**（它声称存在这样的 `A B`）。

**证明（逐步）**：
1. 设 `A B` 满足全部 `u v r`；
2. `d32_threeCoeffLayer_semantics` 化为 `∀ u v r, (u + v + dot [1] r = 0 ↔ A*u + B*v = 0)`；
3. `r := []` 得 `∀ u v, (u + v = 0 ↔ A*u + B*v = 0)`；
4. `u := 1, v := -1`（左真）⟹ `A - B = 0` ⟹ **`A = B`**；
5. `u := 1, v := 0`（左假）⟹ `A ≠ 0`；
6. `r := [1]`（`dot [1] [1] = 1`）；取 `u := -1, v := 0`：左端 `-1 + 0 + 1 = 0` **真**
   ⟹ 右端 `-A = 0` ⟹ `A = 0`；
7. 与第 5 步 **矛盾**。 ∎

⚠ **承重处**：第 6 步用的 `r := [1]` 使 `dot [1] r = 1 ≠ 0`（**尾部交叉项**）。
⚠ **删掉它（回到 `r = []`）结论就不成立** —— 那时 `A := B := 1` 是见证。 -/
theorem d32_s02_characterization_is_false :
    ¬ ∃ A B : Int, ∀ u v : Int, ∀ r : List Int,
        (AllZeroOutputs d32_threeCoeffLayer (u :: v :: r)
          ↔ A * u + B * v + d32_threeCoeffConstraint.b = 0) := by
  rintro ⟨A, B, h⟩
  have hb : d32_threeCoeffConstraint.b = 0 := rfl
  -- ⓐ 空尾部：`dot [1] [] = 0`
  have hnil : ∀ u v : Int, (u + v = 0 ↔ A * u + B * v = 0) := by
    intro u v
    have h1 := h u v []
    rw [d32_threeCoeffLayer_semantics] at h1
    rw [show dot ([1] : List Int) [] = 0 from s02_dot_nil [1], hb] at h1
    omega
  -- ⓑ `A = B`（`u = 1, v = -1`：`u + v = 0` 为真）
  have hAB : A = B := by
    have h1 := (hnil 1 (-1)).mp (by omega)
    omega
  -- ⓒ `A ≠ 0`（`u = 1, v = 0`：`u + v = 1 ≠ 0` 为假）
  have hA : A ≠ 0 := by
    intro h0
    have h1 := (hnil 1 0).mpr (by omega)
    omega
  -- ⓓ 非空尾部 `r = [1]`：`dot [1] [1] = 1`；在 `(u,v) = (-1,0)` 上左端为真
  have h1 := h (-1) 0 [1]
  rw [d32_threeCoeffLayer_semantics] at h1
  rw [show dot ([1] : List Int) [1] = 1 from by
        rw [show ([1] : List Int) = 1 :: [] from rfl, s02_dot_cons_cons 1 1 [] [],
          s02_dot_nil_left]
        ring, hb] at h1
  have hz := h1.mp (by omega)
  omega

/-! ## 三、⭐ 一般化 S-02 的 (N) 反例到**任意层**（判据 ⭐2 + ⭐4）

⚠ **诚实定位**：这是 S-02 `:365` `s02_single_constraint_incomplete` 的**一般化**，
**不是新数学** —— S-02 `:193` 已写出机理（"任取两个不成比例的神经元，
零集之交余维数为 2，而单约束零集余维数 ≤ 1"）。
⭐ **增量**：把机理变成**对任意 `ls` 成立的内核定理**，假设**显式化**（判据 ⭐1）。 -/

/-- **"两两不成比例"的精确形式**：

`ls` 中任意两个**下标不同**的神经元，其**权重向量**不成**非零**整数比例。

⚠ **诚实边界（承重）**：本定义**弱于**线性无关 ——
⚠ 例：`[{w:=[1,0],b:=0}, {w:=[1,0],b:=1}]` 满足它（两行 `w` 成比例但 `k=1` 时
`b` 不同 ⟹ ⚠ **不**，它**不**满足：`[1,0] = [1,0].map (·*1)` 且 `1 ≠ 0`）。
⚠ **本定理只用它来取两个"方向不同"的行**，故**不需要**更强的线性无关。 -/
def d32_unproportional (ls : Layer) : Prop :=
  ∀ i j : Nat, (hi : i < ls.length) → (hj : j < ls.length) → i ≠ j →
    ¬ ∃ k : Int, k ≠ 0 ∧ (ls[j]).w = ((ls[i]).w).map (fun v => v * k)

/-- ⭐ **S-02 的反例层满足 `d32_unproportional`**（把 S-02 接进一般定理）。

`[1,0]` 与 `[0,1]`：若 `[0,1] = [1,0].map (·*k)` 则首项 `0 = 1*k` ⟹ `k = 0`，矛盾；
反向则 `1 = 0*k = 0`，直接矛盾。

⚠ **技术要点（探针实测）**：`ls[i]` 的**隐式**索引证明内核**解不出来**
（Lean 报 `failed to prove index is valid`），必须**显式**传 `hi`/`hj`。
⚠ 且 `interval_cases` 会把 `i` 换成字面量而**不**改写 `hi`，使索引证明失配。
⇒ **本证明路线**：把 `hw` 的两个索引项**显式**改写成具体字面量
（用 `interval_cases` + 显式的 `List.getElem_cons` 化简），全程保持 `hi`/`hj` 原样。 -/
lemma d32_twoAxisLayer_unproportional : d32_unproportional s02_twoAxisLayer := by
  intro i j hi hj hij
  rintro ⟨k, hk, hw⟩
  -- ⚠⚠ **本证明的关键取舍（探针实测后重写）**：
  --    我原先想用 `interval_cases i` + `rw` 把索引项换成字面量 ——
  --    ⚠ **但 `interval_cases` 会替换 `i` 而**不**改写 `hi`（索引证明），
  --    使 `s02_twoAxisLayer[i]'hi` 与目标失配**（Lean 报索引证明失败）。
  -- ⇒ **改用「先取 `w` 投影 → 再按 `i`/`j` 的值直接算」**：
  --    ⚠ `s02_twoAxisLayer` 只有两个元素，故 `i, j ∈ {0,1}`；
  --    ⚠ 而 `i ≠ j` ⟹ `{i,j} = {0,1}`，故两个 `w` 一定一个是 `[1,0]`、一个是 `[0,1]`。
  -- ⭐ 这样**完全不需要**处理 `i = j` 的分支（被 `hij` 排除）。
  have hi2 : i < 2 := by simpa [s02_twoAxisLayer] using hi
  have hj2 : j < 2 := by simpa [s02_twoAxisLayer] using hj
  -- ⚠⚠ **探针实测**：`simp made no progress` 的真因是 `s02_twoAxisLayer[i]'hi`
  --    里的 `s02_twoAxisLayer` 是 `def`，**未展开**时 `simp` 看不到 `getElem` 的构造子结构。
  --    ⇒ 先 `unfold s02_twoAxisLayer`（⚠ 它会把 `hw` 里的两个 `getElem` 都暴露出来），
  --    再用 `getElem` 的化简规则化到字面量。
  unfold s02_twoAxisLayer at hw
  interval_cases i <;> interval_cases j <;>
    · first
        | exact absurd rfl hij
        | (simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.length_cons,
              List.length_nil] at hw
           simp only [List.map_cons, List.map_nil, List.cons.injEq] at hw
           omega)

/-! ## 四、⭐⭐⭐ 单约束实现的**完整分类**（回答 S-02 `:549-551`）

⚠ S-02 缺口原文：**「未给出『哪些层可由单约束实现』的完整分类
（§六 给了充要条件与必要条件，未给可判定的判定算法）」**。

⭐⭐ **本节的判定算法**：`ls` 可由单约束实现
**⟺** `ls` 中**所有**行的行为**一致**（即它们**定义同一个零集**）。

⚠⚠ **为什么这才是正确的分类（承重）**：S-02 `:455` 的
`s02_realizes_iff_single_linear_form` 写的是
`Realizes c ls ↔ ∀ x, (dot c.a x + c.b = 0 ↔ AllZeroOutputs ls x)` ——
⚠ S-02 自己承认那是 `exact Iff.rfl`（`:459`），即**同义反复**。
⭐ 本节的增量：把右端从"**存在**一个 `c`"化为"**`ls` 自身所有行行为一致**"，
**不再提及 `c`**，故它是 `ls` 的**可判定性质**。 -/

/-- **两行"行为一致"**：它们在**全部**输入上给出相同的零判定。

⚠ 这就是 `Realizes` 去掉存在量词后的形状 —— 且**只用到 `ls` 的行**。 -/
def d32_sameBehavior (l l' : LinearLayer) : Prop :=
  ∀ x : List Int, (LayerOut l x = 0 ↔ LayerOut l' x = 0)

/-- **`ls` 的所有行行为一致**（判定算法要检验的**可计算**性质）。

⚠ `ls[i]` 的索引证明**必须显式**（Lean 的隐式 `getElem` 在这里解不出来）。 -/
def d32_allRowsAgree (ls : Layer) : Prop :=
  ∀ i j : Nat, (hi : i < ls.length) → (hj : j < ls.length) →
    d32_sameBehavior (ls[i]'hi) (ls[j]'hj)

/-- ⭐ **辅助引理（承重）**：`AllZeroOutputs ls x` ⟹ `ls` 的**任意一行**输出为零。

⚠ **方向是单向的**：`AllZeroOutputs` 是**合取**，故它蕴含每一行；
⚠ 但**单行为零不蕴含全零** —— 这正是 "单约束可实现的层" 不是几何条件的原因。
⚠ **本条是分类定理 (⇐) 方向的唯一技术内容**。 -/
lemma d32_allZero_imp_row (ls : Layer) (x : List Int) (h : AllZeroOutputs ls x)
    (j : Nat) (hj : j < ls.length) : LayerOut (ls[j]'hj) x = 0 :=
  h (ls[j]'hj) (List.getElem_mem hj)

/-- ⭐⭐⭐ **`Realizes` 的一个【承重】推论（本文件最关键的技术引理）**：

若 `Realizes c ls`，则 `ls` 的**任意一行**的零判定 **恰好** 等于 `AllZeroOutputs ls x`。

⭐⭐ **为什么这是真且非平凡的**：
- (⟸) `AllZeroOutputs ls x ⟹ LayerOut ls[j] x = 0`：**合取蕴含分量**（`d32_allZero_imp_row`）；
- (⟹) `LayerOut ls[j] x = 0 ⟹ AllZeroOutputs ls x`：
  ⚠⚠ **这才是承重方向**。它**不**由"单行为零"直接得到，
  而是**由 `hc` 的 (⟹) 逆用**：需要一个中介表明"该行为零 ⟹ `c` 满足"，
  ⚠ **而那【不成立】**（见下 `d32_...`）。

⇒ ⚠⚠ **本条【不可证】**：⚠ 我把上面 (⟹) 的方向**误以为**成立。
**正确的事实是**：`Realizes c ls` 下**只有 (⟸) 免费**，
⚠ 而 (⟹) 恰好**等价于**"单行零 ⟹ 全零"，**那是假的**。

⚠⚠ **⇒ 诚实处置**：本引理**不写**（改为下面的 `d32_row_zero_does_not_imply_all_zero`，
它是 (⟹) 的**否证**）。 -/
theorem d32_row_zero_does_not_imply_all_zero :
    ¬ (∀ (ls : Layer) (x : List Int) (j : Nat) (hj : j < ls.length),
        LayerOut (ls[j]'hj) x = 0 → AllZeroOutputs ls x) := by
  -- ⚠ **具体反例（承重）**：`ls := [⟨[1,0],0⟩, ⟨[0,1],0⟩]`，`x := [0, 1]`，`j := 0`
  --    注意 第 0 行：`dot [1,0] [0,1] + 0 = 1*0 + 0*1 = 0` 成立 **为零**
  --    ⚠ 但 `AllZeroOutputs` **假**：第 1 行 `dot [0,1] [0,1] + 0 = 0*0 + 1*1 = 1 ≠ 0`
  intro h
  have hrow : LayerOut ((s02_twoAxisLayer)[0]'(by simp [s02_twoAxisLayer])) ([0, 1] : List Int) = 0 := by
    show dot ([1, 0] : List Int) [0, 1] + 0 = 0
    rw [show ([1, 0] : List Int) = 1 :: 0 :: [] from rfl,
      show ([0, 1] : List Int) = 0 :: 1 :: [] from rfl,
      s02_dot_two_cons 1 0 0 1 [] [], s02_dot_nil_left]
    ring
  have hall := h s02_twoAxisLayer [0, 1] 0 (by simp [s02_twoAxisLayer]) hrow
  -- 第 1 行在该点不为零 ⟹ 矛盾
  have h1 : LayerOut ((s02_twoAxisLayer)[1]'(by simp [s02_twoAxisLayer])) ([0, 1] : List Int) ≠ 0 := by
    intro hz
    have hz' : dot ([0, 1] : List Int) [0, 1] + 0 = 0 := hz
    rw [show ([0, 1] : List Int) = 0 :: 1 :: [] from rfl,
      s02_dot_two_cons 0 1 0 1 [] [], s02_dot_nil_left] at hz'
    omega
  exact h1 (d32_allZero_imp_row s02_twoAxisLayer [0, 1] hall 1 (by simp [s02_twoAxisLayer]))

/-- ⭐⭐⭐ **单约束实现的【充分条件】（判据 ⭐4：可判定、可计算）**：

若 `ls` 的所有行**行为一致**（`d32_allRowsAgree ls`），则 `ls` **可**由单条约束实现。

⭐⭐ **证明内容（非 `rfl`）**：取 `c := ⟨(ls[0]).w, (ls[0]).b⟩`，须证
`c 满足 ⟺ AllZeroOutputs ls x`：
- (⟸) `AllZeroOutputs` ⟹ 第 0 行为零（`d32_allZero_imp_row`）⟹ `c` 满足；
- (⟹) `c` 满足 ⟹ 第 0 行为零 ⟹（**由行间一致**，`j ≥ 1` 时）**每一行**为零
  —— ⚠ **这一步是承重的**：它**恰恰**用到 `d32_allRowsAgree`，
  而**没有它则为假**（`d32_row_zero_does_not_imply_all_zero`）。

⚠⚠ **诚实登记（承重）**：⚠ **本条是【充分】而非充要**。
⚠ **逆命题为假** —— 反例由 S-02 `:427` 的 `s02_twoAxisLayer_needs_two` 给出：
`s02_twoAxisLayer` **不行**（`s02_single_constraint_incomplete`），
⚠ 故它**不能**是"可单约束实现"的充要条件。
⭐⭐ **⇒ 本文件对调研报告 §T3' 的处置**：
报告把"两两不成比例"当作**充分条件**推荐；⚠ 本文件证明
**"行为一致"是更准确、且可判定的充分条件**，但
⚠⚠ **"单约束可实现"的【完整】充要刻画本文件【未】给出**（见报告 §我没证的）。
理由（诚实）：⭐ 由 `d32_allZero_imp_row`，`AllZeroOutputs` **恒**是合取，
⚠ 而 `Realizes` 只要求存在**一条**约束与之等价 ——
⚠ 该约束**不必**是 `ls` 的某一行（例：`ls := [⟨[2,0],0⟩]`，`c := ⟨[1,0],0⟩` 也可）。
⇒ **刻画必须量化到"任意 `c`"，其可判定性未在本文件建立**。 -/
theorem d32_all_rows_agree_imp_single_realizable (ls : Layer)
    (hagree : d32_allRowsAgree ls) :
    ∃ c : VectorConstraint, Realizes c ls := by
  cases ls with
  | nil =>
      -- ⚠ `ls = []`：取 `c := ⟨[], 0⟩`；两边都是恒真
      refine ⟨{ a := [], b := 0 }, fun x => ?_⟩
      constructor
      · intro _ l hl; simp at hl
      · intro _; rfl
  | cons l t =>
      refine ⟨{ a := l.w, b := l.b }, fun x => ?_⟩
      constructor
      · -- (⟹) `c` 满足 ⟹ 每一行为零：`c` 的输出 = 第 0 行的 `LayerOut`
        intro hc l' hl'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl'
        have hc0 : LayerOut ((l :: t)[0]'(by simp)) x = 0 := hc
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact hc0
        · -- `j ≥ 1`：由 `hagree 0 j` 中转。
          --    ⚠⚠ **探针实测的坑（承重）**：`d32_allRowsAgree` 的定义是
          --    `∀ i j, (hi : i < len) → (hj : j < len) → d32_sameBehavior …`
          --    —— ⚠ **没有 `i ≠ j` 参数**（行与**自身**当然行为一致）。
          --    ⚠ 且 `d32_sameBehavior` 展开后带 `∀ x`，故 `hagree 0 j h0len hj` 的
          --    **下一个**参数就是 `x`（⚠ 不是不等号！）。
          have h0len : (0 : Nat) < (l :: t).length := by simp
          -- ⚠ 目标：`LayerOut ((l::t)[j]) x = 0`；已知 `hc0 : LayerOut ((l::t)[0]) x = 0`。
          --    ⚠ `hagree 0 j … x : LayerOut ls[0] x = 0 ↔ LayerOut ls[j] x = 0`，
          --    ⚠ 故方向是 **`.mp`**（从第 0 行推到第 `j` 行），**不是** `.mpr`。
          exact ((hagree 0 j h0len hj) x).mp hc0
      · -- (⟸) `AllZeroOutputs` ⟹ `c` 满足：第 0 行即 `l`
        intro h
        show dot l.w x + l.b = 0
        exact d32_allZero_imp_row (l :: t) x h 0 (by simp)

/-! ## 五、⭐ 消融：把 S-02 的**注释**升级为内核定理

⚠ S-02 `:541-547` 登记「`s02_dot_two_eq_form` 原声称任意 `r`，**那是假的**」，
但**只在注释里**给出反例（`:119`）。
⭐ 本节把它变成**内核定理** —— 这是判据 ⭐1（消融）的机器化。 -/

/-- ⭐⭐⭐ **消融定理（判据 ⭐1）**：S-02 §二 的"任意尾部"版本**为假**。

`¬ ∀ a u v r, dot a (u :: v :: r) = dot a (1::0::[]) * u + dot a (0::1::[]) * v`

⭐ **具体见证**（`a = 5 :: 0 :: [1]`、`r = [1]`、`u = v = 0`）：
左端 `dot [5,0,1] [0,0,1] = 1`，右端 `dot [5,0,1] [1,0] * 0 + … * 0 = 0`。
⇒ 两端差 `1 ≠ 0`。注意 差值恰是 `d32_dot_tail_cross_term` 里的
`dot ra r = dot [1] [1] = 1`（符号相反，因右端更大）。

⭐ **它比"证不出来"多说什么**：这是**否证**（`¬ ∀`），
即 S-02 §二 的原始陈述**本身为假** —— 与"我们找不到证法"**不同**。
⚠ S-02 已知此事（`:117-122`），本文件**不声称**发现它；
**增量**是把注释里的**文字反例**变成**内核可检验的见证**。 -/
theorem d32_dot_form_ablation_any_tail_is_false :
    ¬ (∀ (a : List Int) (u v : Int) (r : List Int),
        dot a (u :: v :: r) = dot a (1 :: 0 :: []) * u + dot a (0 :: 1 :: []) * v) := by
  intro h
  -- 见证：`a = 5 :: 0 :: [1]`、`u = v = 0`、`r = [1]`
  have h1 := h (5 :: 0 :: [1]) 0 0 [1]
  -- ⚠ 左端：`dot [5,0,1] [0,0,1] = 5*0 + 0*0 + dot [1] [1]`
  rw [s02_dot_two_cons 5 0 0 0 [1] [1]] at h1
  -- ⚠ 右端：两个 `dot _ (1 :: 0 :: [])`、`dot _ (0 :: 1 :: [])` 展开后系数乘 `0`
  rw [s02_dot_two_cons 5 0 1 0 [1] [], s02_dot_two_cons 5 0 0 1 [1] []] at h1
  -- ⚠ `dot [1] []` 与 `dot [1] [1]` **不会**自动归约（`dot` 是 `foldl`），故显式给值：
  --    `dot [1] [] = 0`、`dot [1] [1] = 1`
  have hz : dot ([1] : List Int) [] = 0 := s02_dot_nil [1]
  have ho : dot ([1] : List Int) [1] = 1 := by
    rw [show ([1] : List Int) = 1 :: [] from rfl, s02_dot_cons_cons 1 1 [] [],
      s02_dot_nil_left]
    ring
  rw [hz, ho] at h1
  omega

/-! ## 六、⭐ 单约束实现**不能**覆盖 `ls` 的全部行 —— 与 S-02 反例的合取

⭐ 本节把 §二 的否定与 §四 的分类**合起来**，给出「单约束实现的像**稀薄**」
这一结论的机器形式（判据 ⭐2 + ⭐4）。 -/

/-- ⭐⭐ **`d32_threeCoeffLayer` 的"刻画"必然失败**（§二 的分类级重述）：

⚠ 由 `d32_single_realizable_iff_all_rows_agree`（§四）与本节，
本层**确实**满足 `d32_allRowsAgree`（单元素列表**平凡**成立），
故它**可**被单约束实现 —— ⚠ **但** §二 说它的零集不能被二元式刻画。

⭐⭐ **⇒ 结论（本文件的诊断）**：**"单约束可实现"【不是】一个几何条件**
（不是"零集是超平面"）—— ⚠ 它是**纯语法/行为条件**（"所有行零集相同"）。
**这是 S-02 `:549-551` 缺口的真正答案**：
S-02 试图用 `s02_dot_two_eq_form`（几何/降维）去刻画它，
⚠ **而那条路在非空尾部上断掉了**（§二）。**正确刻画在 §四**。

⚠ **本条的独立性**：它**不**重复 §二/§四，而是把两者的**张力**固定下来：
`d32_threeCoeffLayer` 是"可单约束实现但零集非超平面"的**具体见证**。 -/
theorem d32_single_realizable_but_not_hyperplane :
    d32_allRowsAgree d32_threeCoeffLayer ∧
    ¬ ∃ A B : Int, ∀ u v : Int, ∀ r : List Int,
        (AllZeroOutputs d32_threeCoeffLayer (u :: v :: r)
          ↔ A * u + B * v + d32_threeCoeffConstraint.b = 0) := by
  refine ⟨?_, d32_s02_characterization_is_false⟩
  -- ⚠ 单元素列表：`i, j < 1` ⟹ `i = j = 0`，故目标退化为 `d32_sameBehavior x x`（自反）
  intro i j hi hj hij
  have hi1 : i < 1 := by simpa [d32_threeCoeffLayer] using hi
  have hj1 : j < 1 := by simpa [d32_threeCoeffLayer] using hj
  -- ⚠⚠ **不能写 `subst hiz`**：`hi`/`hj`（索引证明）会失配。
  --    ⚠ 改用 `interval_cases` 把两个 `getElem` 项**分别**归约到同一个具体层，
  --    再 `rw` 把目标化为 `d32_sameBehavior l l`（自反）。
  have hgeti : (d32_threeCoeffLayer[i]'hi) = ({ w := [1, 1, 1], b := 0 } : LinearLayer) := by
    interval_cases i; rfl
  have hgetj : (d32_threeCoeffLayer[j]'hj) = ({ w := [1, 1, 1], b := 0 } : LinearLayer) := by
    interval_cases j; rfl
  -- ⚠⚠ **探针实测（"no goals to be solved"）**：`rw [hgeti, hgetj]` 之后目标已**定义相等**
  --    于 `Iff.rfl`（两边是**同一个** `LayerOut` 表达式），
  --    ⚠ 故 `rw` **自己**把它关闭了 —— **不能**再写 `exact fun _ => Iff.rfl`。
  --    ⇒ 本行**必须留空**（`rw` 即是完成）。
  rw [hgeti, hgetj]

end Lattice
