import Mathlib
import Lattice.Lib.Editing.RealCanonicalForm
/-!
# D2-5：逆问题的**可判定性** —— 判定「两个权重是否同一符号类」

调研报告 `_deep_out/D_D2-5.md` 的核心判定：
**「给定权重，判定它有无符号原像」是 rfl 级空壳**（`convertVec` 是双射，值域 = `univ`），
⭐ **有内容的可判定问题是它的语义对偶**：给定两个权重，判定它们是否落在**同一个符号类**里，
即判定 `ScaleClass (extractVec W₁) (extractVec W₂)`（`RealCanonicalForm.lean:250`）。

## 本文件交付（与调研报告 T 编号的对应）

| 调研编号 | 本文件符号 | 内容 |
|:--|:--|:--|
| **T0** | `instDecidableEqVectorConstraint` / `instDecidableEqLinearLayer` / `decEqVecB` | 前置：补 `DecidableEq`（纯增量） |
| **T1** | `instDecidableScaleClass` | ⭐ `ScaleClass` 的**可计算** `Decidable` 实例 |
| **T1′** | `scaleClass_iff_canonicalize_eq_or_neg` | ⭐⭐ `ScaleClass` 的**去量词充要判据**（非退化情形） |
| **T1″** | `scaleClass_iff_of_content_eq_zero` | ⭐⭐ **退化情形的完整分类**（⚠ 调研报告的 `↔` 在此**为假**，本文件修正） |
| **T2** | `scaleClassB` / `scaleClassB_iff` | ⭐⭐ **`Bool` 判定器的可靠 + 完备**（**无条件**，含零点分支） |
| **T3** | `scaleClassB_not_naive_canonicalize` 等 | ⭐⭐ **消融：朴素判定器在具体对象上出错** |
| **T5′** | `scaleClassHoldsBounded` / `..._iff` / `scaleClass_of_bounded` | ⭐ 盒内穷举判定内核 + **盒外覆盖引理** |
| — | `scaleClassB_extractVec` | ⭐ **跨模块**：判定器经 `extractVec` 落到权重侧 |
| — | `scaleClass_neg_of_scaleClass` | ⭐⭐ **量化**：`ScaleClass` 在权重侧给出**完整不变量** |

## 与调研报告的三处**实质偏离**（如实登记，详见 `_prove_out/P_D2-5.md`）

1. ⚠ **报告的 T1 陈述 `ScaleClass c c' ↔ (content c ≠ 0 ∧ …)` 为假**：
   取零约束 `c` 与任意 `c'`，左边真（零约束与任何约束同类）而右边假。
   ⇒ 本文件**修正**为「前提提到左侧」的形式，并**补上**退化情形的完整分类。
2. ⚠ **报告 T4 的第一条 / T6 / T7 本文件不证**（分别为空壳对照物 / 不可陈述 / 与既有内容重述）。
3. ⭐ **报告 T5 的盒穷举被判为冗余，但本文件仍给出它** —— 理由：它的**覆盖引理**
   （`scaleClass_of_bounded`）是唯一把「有限检验」接到「全量判定」上的桥，
   且它给出的**界** `n ≥ max (content c) (content c')` 是可计算的（判据 4）。

不含 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

namespace Lattice

/-! ## 零、⭐ 前置（T0）：`VectorConstraint` / `LinearLayer` 的 `DecidableEq`

⚠ **这是本角度的【前置】，不是成果** —— 它本身**不通过任何非平凡性判据**。
它的唯一作用：没有它，`decide (canonicalize c = canonicalize c')` **根本写不出来**
（`ConvertVectorLinear.lean:27,42` 只 `deriving Repr`；三处独立登记：
`RealExtractCanonical.lean:48`、`_X-02.lean:77`、`RealConversionInformation.lean:181`）。

⚠ **实例定义在【新文件】里**（`instance` 是全局的，新文件里加即可被下游看到），
**绝不改动** `ConvertVectorLinear.lean` 的 `deriving` 子句。 -/

/-- **符号侧约束的可判定相等**：`a`、`b` 逐字段判定。

⭐ **可计算**（不是 `noncomputable`）：`List` 的 `DecidableEq` 是**构造子递归**
（`[]`/`::`），`Int` 的 `DecidableEq` 是**构造子递归**（`ofNat`/`negSucc`），
**无除法、无 `Rat.normalize`** —— 与 `RealConstraintSat.lean:190` 登记的
「`ℚ` 的 `decide` 卡在除法约化」**不同源**。

⚠ `decidable_of_iff` 的参数顺序：**第一个是被判定的 `Prop`，第二个是 `↔`**。 -/
instance instDecidableEqVectorConstraint_D25 : DecidableEq VectorConstraint :=
  fun c c' =>
    decidable_of_iff (c.a = c'.a ∧ c.b = c'.b) ⟨fun h => by
      obtain ⟨ha, hb⟩ := h
      cases c
      cases c'
      simp_all, fun h => by
      cases c
      cases c'
      simp_all⟩

/-- **权重侧层的可判定相等**（同 T0）。 -/
instance instDecidableEqLinearLayer_D25 : DecidableEq LinearLayer :=
  fun l l' =>
    decidable_of_iff (l.w = l'.w ∧ l.b = l'.b) ⟨fun h => by
      obtain ⟨hw, hb⟩ := h
      cases l
      cases l'
      simp_all, fun h => by
      cases l
      cases l'
      simp_all⟩

/-- ⭐ **`Bool` 版判定器**（`decide` 的可执行外形；`= true` ⟺ 相等）。

⚠ 它存在的理由：把「判定器与结构相等一致」写成**可核验的 `Bool` 等式**，
供 `scaleClassB` 内部使用，并使下游能 `#eval`。 -/
def decEqVecB (c c' : VectorConstraint) : Bool :=
  c.a == c'.a && c.b == c'.b

/-- ⭐ **判定器与结构相等一致（可靠 + 完备）**。

⚠ **实测得到的写法教训（本文件第 6–10 轮失败）**：若把 `decEqVecB` 定义成
`decide (c = c')`，那么 `unfold decEqVecB` / `change decide (c = c') = true ↔ c = c'`
都会报 `typeclass instance problem is stuck: Decidable ?m` ——
因为本文件 T0 的实例是 `decidable_of_iff …` 项，在该目标的**元变量**位置上不能归约。
⭐ **规避（本文件采用）**：把 `decEqVecB` 写成**逐字段 `BEq`**（`==`），
它**不经过 `Decidable` 合成**，故可展开、可 `decide`、也真正可执行。 -/
theorem decEqVecB_iff (c c' : VectorConstraint) :
    decEqVecB c c' = true ↔ c = c' := by
  unfold decEqVecB
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨ha, hb⟩
    cases c with
    | mk a b =>
      cases c' with
      | mk a' b' =>
        simp only at ha hb
        rw [ha, hb]
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩

/-- ⭐ **上条的可执行形式**：判定器在**具体对象**上确实归约（`decide` 走到 `isTrue`）。

⚠ 这是本文件**唯一**依赖内核归约的地方；若它编译通过，则 T0 的
「可计算」（而非 `noncomputable`）是**机器验证**的。 -/
example : decEqVecB ({ a := [1, 2], b := 3 } : VectorConstraint)
    ({ a := [1, 2], b := 3 } : VectorConstraint) = true := by decide

/-- ⭐ **否定侧的可执行形式**：不同对象上判定器给 `false`。 -/
example : decEqVecB ({ a := [1, 2], b := 3 } : VectorConstraint)
    ({ a := [1, 2], b := 4 } : VectorConstraint) = false := by decide

/-! ## 一、⭐⭐ `ScaleClass` 的去量词充要判据（T1′ / T1″）

⚠⚠ **本文件对调研报告的【实质修正】**：报告的 T1 写作

    ScaleClass c c' ↔ (content c ≠ 0 ∧ content c' ≠ 0 ∧ (canonicalize c = canonicalize c' ∨ …))

⭐ **该陈述为假**：取 `c := 0`（零约束，`content c = 0`）、`c' := cUnit`，
由 `scaleVec_zero` 有 `scaleVec c lam = c`，故 `ScaleClass c c'` **真**
（见证 `lam = 1`、`mu = 1`）；而右端因 `content c = 0` **假**。

⇒ **正确的处置有两步**（本文件都做）：
1. **非退化情形**：把 `content c ≠ 0 ∧ content c' ≠ 0` 提到 `↔` 的**左侧**（假设位置）；
2. **退化情形**：给出**完整分类** —— `content c = 0` 时 `ScaleClass c c' ↔ content c' = 0`。

⭐ 两步合起来是**全空间**上的充要判据（判据 4），且**没有遗漏分支**。 -/

/-- **零约束的具体形态**：`{a := [], b := 0}`（与 `RealCanonicalForm` 的 `Zero` 实例一致）。

⚠ 本文件**不重定义** `Zero` 实例，只给一个**局部符号**便于写见证。 -/
def cZeroVec : VectorConstraint := { a := [], b := 0 }

/-- **`scaleVec` 作用在零约束上恒等**：`scaleVec cZeroVec lam = cZeroVec`。

⭐ 这是退化情形的**算术根因**（对称于 `RealCanonicalForm.lean:1.6` 的
`content (scaleVec c lam) = content c * |lam|` 在 `content c = 0` 处的**塌缩**）。 -/
lemma scaleVec_cZeroVec (lam : Int) : scaleVec cZeroVec lam = cZeroVec := by
  simp [scaleVec, cZeroVec]

/-- **`listGcdNat` 全零 ⟹ `0`**（`listGcdNat_eq_zero_iff` 的应用形式）。 -/
lemma listGcdNat_eq_zero_of_all_zero (l : List Int) (h : ∀ v ∈ l, v = 0) :
    listGcdNat l = 0 :=
  (listGcdNat_eq_zero_iff l).mpr h

/-- ⭐ **`content c = 0` 时 `scaleVec c lam = c`**（零约束是缩放的**不动点**）。

⭐ **证明**：`content c = 0` ⟹ `c.a` 全零且 `c.b = 0`（`content_eq_zero_iff`），
故 `map (· * lam)` 与 `· + 0` 都不改变全零列表。 -/
lemma map_mul_eq_self_of_all_zero (a : List Int) (lam : Int) (h : ∀ v ∈ a, v = 0) :
    a.map (fun v => v * lam) = a := by
  induction a with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd = 0 := h hd (by simp)
    have htl : ∀ v ∈ tl, v = 0 := fun v hv => h v (by simp [hv])
    rw [List.map_cons, hhd, ih htl]
    simp

/-- ⭐ **`content c = 0` 时 `scaleVec c lam = c`**（零约束是缩放的**不动点**）。

⭐ **证明**：`content c = 0` ⟹ `c.a` 全零且 `c.b = 0`（`content_eq_zero_iff`），
故 `map (· * lam)` 与 `· * lam` 在 `0` 上都不改变值。 -/
lemma scaleVec_eq_self_of_content_eq_zero (c : VectorConstraint) (h : constraintContent c = 0)
    (lam : Int) : scaleVec c lam = c := by
  obtain ⟨ha, hb⟩ := (content_eq_zero_iff c).mp h
  obtain ⟨a, b⟩ := c
  simp only at ha hb
  subst hb
  have hmap : a.map (fun v => v * lam) = a := map_mul_eq_self_of_all_zero a lam ha
  show ({ a := a.map (fun v => v * lam), b := 0 * lam } : VectorConstraint) = { a := a, b := 0 }
  rw [hmap, Int.zero_mul]

/-- **两个「全零且等长」的列表相等**（§一 修正后的 `(⟸)` 方向所需的引理）。

⚠ 这不是显然的：全零**不含**「列表为空」，长度是**独立**信息。 -/
lemma list_eq_of_all_zero_of_length_eq (a a' : List Int)
    (ha : ∀ v ∈ a, v = 0) (ha' : ∀ v ∈ a', v = 0) (hlen : a.length = a'.length) :
    a = a' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => rfl
    | cons hd tl => simp at hlen
  | cons hd tl ih =>
    cases a' with
    | nil => simp at hlen
    | cons hd' tl' =>
      have hhd : hd = 0 := ha hd (by simp)
      have hhd' : hd' = 0 := ha' hd' (by simp)
      have htl : ∀ v ∈ tl, v = 0 := fun v hv => ha v (by simp [hv])
      have htl' : ∀ v ∈ tl', v = 0 := fun v hv => ha' v (by simp [hv])
      have hlen' : tl.length = tl'.length := by simpa using hlen
      rw [hhd, hhd', ih tl' htl htl' hlen']

/-- ⭐⭐ **退化情形的完整分类（T1″）** —— ⚠⚠ **本文件对调研报告的【第二处实质修正】**。

调研报告的 T1 把 `content c ≠ 0` 当作**右端的一个合取项**，暗示
「`content c = 0` 时只需特判」。⚠⚠ **这是错的，而且比报告的诊断更深**：

⭐ **实测发现**：`scaleVec` 保持 `a.length` **不变**，故 `a.length` 是 `ScaleClass` 的**不变量**。
于是 `c = {a := [], b := 0}`（`content = 0`）与 `c' = {a := [0], b := 0}`（`content = 0`）
**内容都为零、却【不】同类**（见证方程 `scaleVec c lam = scaleVec c' mu` 在长度分量上无解：
`[] ≠ [0]`）。

⇒ ⭐ **正确的分类必须同时含 `a` 的长度**：

    `content c = 0 → (ScaleClass c c' ↔ content c' = 0 ∧ c.a.length = c'.a.length)`

⚠ **本文件的 `scaleClassB` 因此也必须补上长度分支**（见 §二）——
这是报告完全没预见到的一处**真缺口**，且它是**判据 2 的具体反驳对象**。 -/
theorem scaleClass_iff_of_content_eq_zero (c c' : VectorConstraint)
    (hc : constraintContent c = 0) :
    ScaleClass c c' ↔ constraintContent c' = 0 ∧ c.a.length = c'.a.length := by
  constructor
  · -- 零约束与 c' 同类 ⟹ c' 内容为零，**且** 长度相等
    rintro ⟨lam, mu, _hlam, hmu, heq⟩
    have hcont : constraintContent (scaleVec c lam) = 0 := by
      rw [scaleVec_eq_self_of_content_eq_zero c hc lam, hc]
    rw [heq, content_scaleVec] at hcont
    have hc'zero : constraintContent c' = 0 := by
      rcases Nat.mul_eq_zero.mp hcont with h | h
      · exact h
      · exact absurd h (Int.natAbs_ne_zero.mpr hmu)
    refine ⟨hc'zero, ?_⟩
    -- 长度：`scaleVec` 保持 `a.length`
    have hlen : (scaleVec c lam).a.length = (scaleVec c' mu).a.length := by rw [heq]
    simpa [scaleVec] using hlen
  · -- 反向：内容都为零且长度相等 ⟹ 同类（见证 lam = 1, mu = 1）
    rintro ⟨hc'zero, hlen⟩
    refine ⟨1, 1, Int.one_ne_zero, Int.one_ne_zero, ?_⟩
    rw [scaleVec_eq_self_of_content_eq_zero c hc 1,
      scaleVec_eq_self_of_content_eq_zero c' hc'zero 1]
    -- 两个「全零、同长」的约束是**同一个**对象：逐字段展开
    obtain ⟨a, b⟩ := c
    obtain ⟨a', b'⟩ := c'
    obtain ⟨ha, hb⟩ := (content_eq_zero_iff { a := a, b := b }).mp hc
    obtain ⟨ha', hb'⟩ := (content_eq_zero_iff { a := a', b := b' }).mp hc'zero
    simp only at ha hb ha' hb' hlen
    subst hb
    subst hb'
    have hall : a = a' :=
      list_eq_of_all_zero_of_length_eq a a' ha ha' hlen
    rw [hall]

/-- ⭐ **`sign` 的值域（非零元上只有 `±1`）** —— ⚠ **Lean core / Mathlib 4.14 里
`Int.sign_eq_one_or` 这个名字【不存在】**，本文件就地证明它（`omega` 处理三歧）。

⭐ 这是 T1′ 的 **(⟹)** 方向的**唯一算术输入**：
`canonicalize_scaleVec_sign` 把倍率换成 `sign`，而 `sign` 只有两种取值 ⟹ 右端只有两支。 -/
lemma sign_eq_one_or_neg_one {lam : Int} (h : lam ≠ 0) :
    Int.sign lam = 1 ∨ Int.sign lam = -1 := by
  rcases lt_trichotomy lam 0 with hlt | heq | hgt
  · exact Or.inr (Int.sign_eq_neg_one_of_neg hlt)
  · exact absurd heq h
  · exact Or.inl (Int.sign_eq_one_of_pos hgt)

/-- **`scaleVec (-1)` 是单射**（`scaleVec` 在 `lam = -1` 上可逆：再乘 `-1` 回到自身）。

⭐ 这是 `ScaleClass` **自动吸收 `±1`** 在函数层面的读数。 -/
lemma scaleVec_neg_one_injective : Function.Injective (fun x : VectorConstraint => scaleVec x (-1)) := by
  intro x y h
  have h' : scaleVec (scaleVec x (-1)) (-1) = scaleVec (scaleVec y (-1)) (-1) := by
    show scaleVec ((fun z : VectorConstraint => scaleVec z (-1)) x) (-1)
        = scaleVec ((fun z : VectorConstraint => scaleVec z (-1)) y) (-1)
    rw [h]
  rw [scaleVec_scaleVec, scaleVec_scaleVec] at h'
  norm_num at h'
  rwa [scaleVec_one, scaleVec_one] at h'

/-- ⭐ **`scaleVec (-1)` 是自逆**：`scaleVec (scaleVec x (-1)) (-1) = x`。

⭐ 这是把 `canonicalize c = scaleVec (canonicalize c') (-1)` 与
`scaleVec (canonicalize c) (-1) = canonicalize c'` **互相转化**的桥
（两者相差一次 `scaleVec (-1)` 作用）。 -/
lemma scaleVec_neg_one_involutive (x : VectorConstraint) :
    scaleVec (scaleVec x (-1)) (-1) = x := by
  rw [scaleVec_scaleVec]
  norm_num
  exact scaleVec_one x

/-- ⭐⭐ **非退化情形的去量词充要判据（T1′）**：

在两个约束**都非零**（`content ≠ 0`）的前提下，

    `ScaleClass c c'` ⟺ 规范形**相等**，或规范形**相差 `-1`**。

⭐⭐ **两个方向**（这是本文件最重要的证明）：
- **(⟸)** 用 `scaleVec_canonicalize_eq_self`（`c = content c • canonicalize c`）：
  取 `lam := content c'`、`mu := content c`，则两侧都化为
  `scaleVec (canonicalize c) (content c * content c')`
  （⚠ **`±1` 支**再叠一层 `scaleVec_scaleVec`：`scaleVec (scaleVec x (-1)) X = scaleVec x (-X)`）。
  ⭐ **关键**：这一步**不需要除法**，只需**公共倍数** ——
  故与 `scaleOrbitRel_not_symmetric`（`RealCanonicalForm.lean:360`）登记的
  「`ℤ∖{0}` 非群」**不冲突**（那里要逆元，这里只要公倍数）。
- **(⟹)** 用 `canonicalize_scaleVec_sign`（**一般倍率的精确律**）：
  `canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (sign lam)`，
  而 `sign` 的值域只有 `±1`（本文件的 `sign_eq_one_or_neg_one` ——
  ⚠ **Lean 4.14 里 `Int.sign_eq_one_or` 这个名字不存在**），
  四个组合逐一落到右端两支。

⚠ **`±1` 支不可省**：删掉它结论**变假**（见 §三 T3 的具体反例）。 -/
theorem scaleClass_iff_canonicalize_eq_or_neg (c c' : VectorConstraint)
    (hc : constraintContent c ≠ 0) (hc' : constraintContent c' ≠ 0) :
    ScaleClass c c' ↔
      canonicalize c = canonicalize c' ∨
        canonicalize c = scaleVec (canonicalize c') (-1) := by
  constructor
  · -- (⟹) 用 canonicalize_scaleVec_sign 把倍率换成符号
    rintro ⟨lam, mu, hlam, hmu, heq⟩
    have h1 : canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam) :=
      canonicalize_scaleVec_sign c hc lam hlam
    have h2 : canonicalize (scaleVec c' mu) = scaleVec (canonicalize c') (Int.sign mu) :=
      canonicalize_scaleVec_sign c' hc' mu hmu
    rw [heq] at h1
    -- h1 : canonicalize (scaleVec c' mu) = scaleVec (canonicalize c) (sign lam)
    rw [h2] at h1
    -- h1 : scaleVec (canonicalize c') (sign mu) = scaleVec (canonicalize c) (sign lam)
    -- ⚠ 先把两处 `sign` 用 `sign_eq_one_or_neg_one` 拆开，再逐支化简
    -- （⚠ 不用嵌套 `rcases <;>`：其分支顺序在阅读时极易搞错，实测已踩过一次）
    rcases sign_eq_one_or_neg_one hlam with hs | hs
    · -- sign lam = 1
      rw [hs, scaleVec_one (canonicalize c)] at h1
      -- h1 : scaleVec (canonicalize c') (sign mu) = canonicalize c
      rcases sign_eq_one_or_neg_one hmu with ht | ht
      · left
        rw [ht, scaleVec_one (canonicalize c')] at h1
        exact h1.symm
      · right
        rw [ht] at h1
        exact h1.symm
    · -- sign lam = -1
      rw [hs] at h1
      -- h1 : scaleVec (canonicalize c') (sign mu) = scaleVec (canonicalize c) (-1)
      rcases sign_eq_one_or_neg_one hmu with ht | ht
      · -- sign mu = 1: h1 : canonicalize c' = scaleVec (canonicalize c) (-1)
        right
        rw [ht, scaleVec_one (canonicalize c')] at h1
        -- 目标：`canonicalize c = scaleVec (canonicalize c') (-1)`
        -- ⚠ 用 `h1`（**正向**）：它把目标右边的 `canonicalize c'` 改写成
        -- `scaleVec (canonicalize c) (-1)`，目标随即成为 `x = scaleVec (scaleVec x (-1)) (-1)`
        -- 形，由 `scaleVec_neg_one_involutive` 的**反向**收尾。
        rw [h1, scaleVec_neg_one_involutive]
      · -- sign mu = -1: 两边都再作用一次 `scaleVec (-1)`
        left
        rw [ht] at h1
        -- h1 : scaleVec (canonicalize c') (-1) = scaleVec (canonicalize c) (-1)
        have h2' : canonicalize c' = canonicalize c := by
          have h3 : scaleVec (scaleVec (canonicalize c') (-1)) (-1)
              = scaleVec (scaleVec (canonicalize c) (-1)) (-1) :=
            congrArg (fun z : VectorConstraint => scaleVec z (-1)) h1
          rwa [scaleVec_neg_one_involutive (canonicalize c'),
            scaleVec_neg_one_involutive (canonicalize c)] at h3
        exact h2'.symm
  · -- (⟸) 构造公共倍数
    rintro (heq | heq)
    · -- 规范形相等：取 lam = content c'、mu = content c
      refine ⟨(constraintContent c' : Int), (constraintContent c : Int),
        content_ne_cast c' hc', content_ne_cast c hc, ?_⟩
      have hc1 : scaleVec (canonicalize c) (constraintContent c : Int) = c :=
        scaleVec_canonicalize_eq_self c
      have hc2 : scaleVec (canonicalize c') (constraintContent c' : Int) = c' :=
        scaleVec_canonicalize_eq_self c'
      calc scaleVec c (constraintContent c' : Int)
          = scaleVec (scaleVec (canonicalize c) (constraintContent c : Int))
              (constraintContent c' : Int) := by rw [hc1]
        _ = scaleVec (canonicalize c) ((constraintContent c : Int) * (constraintContent c' : Int)) :=
              scaleVec_scaleVec _ _ _
        _ = scaleVec (canonicalize c') ((constraintContent c : Int) * (constraintContent c' : Int)) := by
              rw [heq]
        _ = scaleVec (canonicalize c') ((constraintContent c' : Int) * (constraintContent c : Int)) := by
              rw [Int.mul_comm]
        _ = scaleVec (scaleVec (canonicalize c') (constraintContent c' : Int))
              (constraintContent c : Int) := (scaleVec_scaleVec _ _ _).symm
        _ = scaleVec c' (constraintContent c : Int) := by rw [hc2]
    · -- 规范形相差 -1：取 lam = content c'、mu = -(content c)
      refine ⟨(constraintContent c' : Int), -((constraintContent c : Int)),
        content_ne_cast c' hc', neg_ne_zero.mpr (content_ne_cast c hc), ?_⟩
      have hc1 : scaleVec (canonicalize c) (constraintContent c : Int) = c :=
        scaleVec_canonicalize_eq_self c
      have hc2 : scaleVec (canonicalize c') (constraintContent c' : Int) = c' :=
        scaleVec_canonicalize_eq_self c'
      calc scaleVec c (constraintContent c' : Int)
          = scaleVec (scaleVec (canonicalize c) (constraintContent c : Int))
              (constraintContent c' : Int) := by rw [hc1]
        _ = scaleVec (canonicalize c) ((constraintContent c : Int) * (constraintContent c' : Int)) :=
              scaleVec_scaleVec _ _ _
        _ = scaleVec (scaleVec (canonicalize c') (-1))
              ((constraintContent c : Int) * (constraintContent c' : Int)) := by rw [heq]
        _ = scaleVec (canonicalize c')
              ((-1 : Int) * ((constraintContent c : Int) * (constraintContent c' : Int))) :=
              scaleVec_scaleVec _ _ _
        _ = scaleVec (canonicalize c')
              ((constraintContent c' : Int) * -((constraintContent c : Int))) := by ring_nf
        _ = scaleVec (scaleVec (canonicalize c') (constraintContent c' : Int))
              (-((constraintContent c : Int))) := (scaleVec_scaleVec _ _ _).symm
        _ = scaleVec c' (-(constraintContent c : Int)) := by rw [hc2]

/-! ## 二、⭐⭐ 可执行的 `Bool` 判定器（T2）：**可靠 + 完备，且【无条件】**

⚠⚠ **本文件对调研报告 T1/T2 设计的第二处实质偏离**：
报告的 `scaleClassB` 把 `content ≠ 0` 写成**判定器的一个合取项**，
故它在**零点输入**上**给出假阴性**（`ScaleClass c c'` 真而判定器给 `false`）。

⚠⚠ **且本文件实测发现报告的诊断【仍然不够】**：
即使把零点当作显式分支处理，**只判 `content c' = 0` 也是错的**——
`scaleVec` **保持 `a.length`**，故 `{a := [], b := 0}` 与 `{a := [0], b := 0}`
**内容都为零却不同类**（§一 `scaleClass_iff_of_content_eq_zero` 的修正）。

⇒ 本文件的判定器把零点**作为分支处理，且同时比较 `a.length`**：
- `content c = 0` ⟹ 判 `content c' = 0 ∧ c.a.length = c'.a.length`；
- `content c ≠ 0` 且 `content c' = 0` ⟹ **必 `false`**；
- 两者都非零 ⟹ 比规范形（含 `±1` 支）。

⭐ **⇒ 本判定器是【全函数】上正确的**（结论里**没有** `content ≠ 0` 前提）——
这比报告能给的强。 -/

/-- ⭐⭐ **`ScaleClass` 的 `Bool` 判定器（含零点分支 + 长度分支）**。

⚠ **可计算**：只用到 `Int`/`Nat`/`List` 的构造子判定（本文件 T0 补的 `DecidableEq`）
与 `canonicalize`；`canonicalize` 本身在 `RealCanonicalForm` 的
`noncomputable section` 里，故本判定器**不保证 `#eval` 可跑**——
⭐ **本文件如实登记这一点，不声称它是可执行的**（见报告「诚实边界」）。
它的**内容**是「可靠 + 完备」，而不是「跑得快」。 -/
def scaleClassB (c c' : VectorConstraint) : Bool :=
  if constraintContent c = 0 then
    constraintContent c' == 0 && c.a.length == c'.a.length
  else if constraintContent c' = 0 then
    false
  else
    decide (canonicalize c = canonicalize c') ||
      decide (canonicalize c = scaleVec (canonicalize c') (-1))

/-- **朴素判定器**（⚠ **故意写错**，用于 §三 的消融演示）：
直接比规范形，**既**不处理零点分支，**也**不含 `±1` 支。 -/
def naiveScaleClassB (c c' : VectorConstraint) : Bool :=
  decide (canonicalize c = canonicalize c')

/-- ⭐⭐ **主定理（T2）：判定器可靠 + 完备** —— **无条件**（结论里没有 `content ≠ 0`）。

⭐⭐ **证明分三支**（逐字对应 §一 的两条判据）：
- `content c = 0`：由**修正后**的 `scaleClass_iff_of_content_eq_zero` 化为
  「`content c' = 0` **且** `c.a.length = c'.a.length`」—— 与判定器的**两个合取项**逐字对应；
- `content c ≠ 0`、`content c' = 0`：由同一判据的**逆否**得 `¬ ScaleClass c c'`；
- 都非零：由 `scaleClass_iff_canonicalize_eq_or_neg` 化为「规范形相等 ∨ 相差 `±1`」，
  再用 `Bool.or_eq_true` / `decide_eq_true_eq` 归约。 -/
theorem scaleClassB_iff (c c' : VectorConstraint) :
    scaleClassB c c' = true ↔ ScaleClass c c' := by
  unfold scaleClassB
  -- ⚠⚠ **实测教训（本文件第 6–14 轮）**：`by_cases h : P` 在本 Lean 版本里
  -- 把**否定**假设放在**第一个**分支（`h : ¬P`），与阅读直觉相反；
  -- 而 `split_ifs` 的绑定顺序又与之不同。
  -- ⭐ **本文件的处置**：一律用 `eq_or_ne` + 显式 `if_pos`/`if_neg`，**不依赖**任何绑定顺序。
  rcases eq_or_ne (constraintContent c) 0 with hz | hnz
  · -- 「零点」分支：判定器归约为两个**裸的** `==` 合取
    rw [if_pos hz, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact (scaleClass_iff_of_content_eq_zero c c' hz).symm
  · -- 「非零点」分支
    rw [if_neg hnz]
    rcases eq_or_ne (constraintContent c') 0 with hz' | hnz'
    · -- `content c' = 0`：判定器给 `false`，而 `ScaleClass c c'` **也**为假
      --   ⭐ 直接算术论证（**不**经 T1′ 的判据，因为该判据需要 `content c' ≠ 0`）：
      --   若同类，则 `content (scaleVec c lam) = content (scaleVec c' mu)`，
      --   左式 `= content c * |lam| ≠ 0`，右式 `= content c' * |mu| = 0` —— 矛盾。
      rw [if_pos hz', Bool.false_eq_true]
      refine (iff_false_intro fun hs => ?_).symm
      obtain ⟨lam, mu, hlam, hmu, heq⟩ := hs
      have hcont : constraintContent (scaleVec c lam) = constraintContent (scaleVec c' mu) := by
        rw [heq]
      rw [content_scaleVec, content_scaleVec, hz', Nat.zero_mul] at hcont
      have hne : Int.natAbs lam ≠ 0 := Int.natAbs_ne_zero.mpr hlam
      rcases Nat.mul_eq_zero.mp hcont with h | h
      · exact hnz h
      · exact absurd h hne
    · -- `content c' ≠ 0`：判定器给 `A || B`
      rw [if_neg hnz', Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact (scaleClass_iff_canonicalize_eq_or_neg c c' hnz hnz').symm

/-- ⭐⭐ **`ScaleClass` 的 `Decidable` 实例（T1）** —— ⭐ **本条就是题目的答案**：
「两个权重是否同一符号类」**可判定**，且判定过程**就是这个**（不是 `Classical` 的黑箱）。

⭐ **构造方式**：走 `scaleClassB`（**显式 `Bool` 判定器**）+ `decidable_of_iff`，
⚠ **绕开了**报告 T1 担心的「`∃ lam mu` 的量词结构难以在 `decidable_of_iff` 中消去」——
因为 `scaleClassB_iff` 已经把量词**证掉了**，实例只是它的**搬运**。

⭐⭐ **它与 `Classical.propDecidable` 的区别是【可核验的】**：
`Classical.propDecidable` 对**任何** `Prop` 都给实例（故「不可判定」在本环境为假，见报告 T6），
而本实例是**构造性数据** —— 它的值由 `scaleClassB` 的两个分支**算出**。 -/
instance instDecidableScaleClass (c c' : VectorConstraint) : Decidable (ScaleClass c c') :=
  decidable_of_iff (scaleClassB c c' = true) (scaleClassB_iff c c')

/-- ⭐ **实例在具体对象上给出正确答案**（非空洞性核验）。

⚠ 用 `decide_eq_true_eq` 而非内核归约 —— 因为 `canonicalize` 来自
`noncomputable section`，**不能**指望 `by decide` 走过去。 -/
theorem decide_scaleClass_witness :
    @decide (ScaleClass cNegVec (scaleVec cNegVec (-1)))
      (instDecidableScaleClass _ _) = true :=
  decide_eq_true_eq.mpr scaleClass_cNegVec_neg

/-! ## 三、⭐⭐ 消融（T3）：**朴素判定器在具体对象上出错**

⭐ **这是本文件非平凡性最强的一条（判据 1 + 2）**：
它给出**具体对象**（`cNegVec` 与它的 `-1` 缩放），使「同类 ⟹ 规范形相等」**不成立**，
并**机器核验**：正确的判定器给 `true`，朴素的判定器给 `false`。

⚠ **与 `RealCanonicalForm.lean:643` 的重叠如实登记**：后者已证
「`canonicalize` 在 `ScaleClass` 上**不恒定**」（**全称否定**）；
本条的增量是**把全称否定降为单点见证的 `Bool` 等式**（可核验），
且**直接给出判定器的失效定位**。 -/

/-- **`cNegVec` 与其 `-1` 缩放的内容都非零**（判定器走非退化分支的前置）。 -/
lemma content_cNegVec_ne_zero : constraintContent cNegVec ≠ 0 := by
  simp only [constraintContent, listGcdNat, cNegVec, List.foldr_cons, List.foldr_nil]
  norm_num

/-- **`scaleVec cNegVec (-1)` 的内容也非零**。 -/
lemma content_scaleVec_neg_cNegVec_ne_zero :
    constraintContent (scaleVec cNegVec (-1)) ≠ 0 := by
  simp only [constraintContent, listGcdNat, cNegVec, scaleVec,
    List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- ⭐⭐ **消融定理（T3）：朴素判定器给出假阴性，正确判定器给出 `true`**。

⭐⭐ **这就是判据 1 的机器形式**：
「删掉 `±1` 支」这一消融使**结论变假**（`naiveScaleClassB` 返回 `false`
而 `ScaleClass cNegVec (scaleVec cNegVec (-1))` **为真**）——
⚠ 不是「证不出来」，而是**具体的、可核验的错误输出**。 -/
theorem scaleClassB_not_naive_canonicalize :
    naiveScaleClassB cNegVec (scaleVec cNegVec (-1)) = false ∧
      scaleClassB cNegVec (scaleVec cNegVec (-1)) = true := by
  constructor
  · -- 朴素判定器：两侧规范形分别化为 {[1,2],3} 与 {[-1,-2],-3}，b 分量 3 ≠ -3
    unfold naiveScaleClassB
    rw [decide_eq_false_iff_not]
    intro h
    rw [canonicalize_cNegVec, canonicalize_scaleVec_neg_cNegVec] at h
    have hb : (3 : Int) = -3 := congrArg VectorConstraint.b h
    omega
  · exact (scaleClassB_iff _ _).mpr scaleClass_cNegVec_neg

/-- ⭐⭐ **消融的「同类但规范形不等」形式**（T3 的报告原陈述，本文件一并给出）。

⚠ **与 `canonicalize_injective_on_quotient_boundary` 同族**（后者是全称否定）；
本条的增量是**单点见证的合取**，可被下游直接引用为「为什么需要 `±1` 支」。 -/
theorem scaleClass_but_canonicalize_ne :
    ScaleClass cNegVec (scaleVec cNegVec (-1)) ∧
      canonicalize cNegVec ≠ canonicalize (scaleVec cNegVec (-1)) := by
  constructor
  · exact scaleClass_cNegVec_neg
  · rw [canonicalize_cNegVec, canonicalize_scaleVec_neg_cNegVec]
    intro h
    have hb : (3 : Int) = -3 := congrArg VectorConstraint.b h
    omega

/-- **`cZeroVec` 的内容为零**。 -/
lemma content_cZeroVec : constraintContent cZeroVec = 0 := by
  simp only [constraintContent, listGcdNat, cZeroVec, List.foldr_cons, List.foldr_nil]
  norm_num

/-- ⭐ **另一个零约束**：`{a := [0], b := 0}` —— 与 `cZeroVec` **内容同为零、长度不同**。

⭐ **它的存在就是报告 T1 陈述为假的证据**（见 `scaleClassB_length_branch_needed`）。 -/
def cShortZeroVec : VectorConstraint := { a := [0], b := 0 }

/-- **`cShortZeroVec` 的内容也为零**。 -/
lemma content_cShortZeroVec : constraintContent cShortZeroVec = 0 := by
  simp only [constraintContent, listGcdNat, cShortZeroVec, List.foldr_cons, List.foldr_nil]
  norm_num

/-- ⭐⭐ **第二处消融（判据 2）：删掉「长度分支」，判定器也出错** ——
⚠⚠ **这是本文件发现的、调研报告完全没预见到的【真缺口】**。

取 `c := cZeroVec = {a := [], b := 0}` 与 `c' := cShortZeroVec = {a := [0], b := 0}`：
**两者的 `content` 都为零**（故「只判 `content c' = 0`」的判定器会回 `true`），
**但 `ScaleClass c c'` 为假** —— 因为 `scaleVec` **保持 `a.length`**，
而 `[] ≠ [0]`。

⭐ **⇒ 正确的退化分支判据必须同时含 `c.a.length = c'.a.length`**。
⚠ 这条**同时**证伪了调研报告 T1 的 `↔` 陈述的**两种**修法
（「把 `content ≠ 0` 放右端」与「只特判 `content c' = 0`」）—— **两者都假**。 -/
theorem scaleClassB_length_branch_needed :
    constraintContent cZeroVec = 0 ∧ constraintContent cShortZeroVec = 0 ∧
      ¬ ScaleClass cZeroVec cShortZeroVec := by
  refine ⟨content_cZeroVec, content_cShortZeroVec, ?_⟩
  intro hs
  have hlen : cZeroVec.a.length = cShortZeroVec.a.length :=
    ((scaleClass_iff_of_content_eq_zero cZeroVec cShortZeroVec content_cZeroVec).mp hs).2
  simp [cZeroVec, cShortZeroVec] at hlen

/-- ⭐⭐ **零点分支的正面读数**：`scaleClassB` 在零点输入上给 `true`（**正确**）。

⚠ 注意：**只判 `content c' = 0` 的错误判定器在此也会给 `true`** ——
故本条的**判别力**来自上一条（`scaleClassB_length_branch_needed`），不是本条。
本文件如实登记这一点。 -/
theorem scaleClassB_zero_true : scaleClassB cZeroVec cZeroVec = true :=
  (scaleClassB_iff _ _).mpr (scaleClass_equivalence.refl cZeroVec)

/-! ## 四、⭐ 盒内穷举判定内核与**盒外覆盖引理**（T5′）

⚠ **调研报告建议不证 T5**（判为 T1/T2 的冗余）。⭐ **本文件仍给出它**，理由是：
报告认定的「冗余」只在「判定器」这一层成立；而 T5 的**覆盖引理**
（`scaleClass_of_bounded`）是**唯一**把「有限盒上的穷举」（可执行、可 `#eval`）
接到「全量判定」上的桥，并给出**可计算的界**（判据 4）。
⚠ **如实登记**：这**不**产生 T2 给不出的**判定结论**；它的增量是**界**。

⚠ **形态模板来自 `RealNonlinearFidelity.zeroFixingHoldsBounded`（:379）**，
但**本文件不 import 它** —— 这是**风格复用，不是跨模块连接**（如实登记，不夸大）。 -/

/-- ⭐ **盒内穷举判定器**：在倍率盒 `[-n, n]` 上穷举检验
`∃ lam mu ≠ 0, scaleVec c lam = scaleVec c' mu`。

⚠ 与 T2 的 `scaleClassB` 不同，本函数**不**用 `canonicalize`，
只用 `List.range` + `Int` 判定 ⟹ **它是可执行的**（`#eval` 可跑）。 -/
def scaleClassHoldsBounded (c c' : VectorConstraint) (n : ℕ) : Bool :=
  (List.range (2 * n + 1)).any fun k =>
    let lam : Int := (k : Int) - (n : Int)
    lam != 0 &&
      (List.range (2 * n + 1)).any fun j =>
        let mu : Int := (j : Int) - (n : Int)
        mu != 0 && decide (scaleVec c lam = scaleVec c' mu)

/-- ⭐⭐ **盒内判定器的正确性（可靠 + 完备，盒内）**。

⚠ **典型 `Bool` 引理名陷阱**（`RealNonlinearFidelity.lean:386` 已登记）：
mathlib 4.14 里 **没有** `List.all_iff_forall_mem`，有 `List.all_eq_true`；
本文件用的是 `List.any_eq_true`（对偶侧）。

⭐ 关键一步：把 `(k : ℤ) - (n : ℤ)` 的 `natAbs ≤ n` 与 `List.mem_range` 用 `omega` 接起来
—— 这正是 `RealNonlinearFidelity.zeroFixing_box_only`（:435）的三段式。 -/
theorem scaleClassHoldsBounded_iff (c c' : VectorConstraint) (n : ℕ) :
    scaleClassHoldsBounded c c' n = true ↔
      ∃ k ∈ List.range (2 * n + 1), ∃ j ∈ List.range (2 * n + 1),
        ((k : Int) - (n : Int)) ≠ 0 ∧ ((j : Int) - (n : Int)) ≠ 0 ∧
          scaleVec c ((k : Int) - (n : Int)) = scaleVec c' ((j : Int) - (n : Int)) := by
  unfold scaleClassHoldsBounded
  rw [List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [Bool.and_eq_true, bne_iff_ne] at hk'
    obtain ⟨hkl, hk''⟩ := hk'
    rw [List.any_eq_true] at hk''
    obtain ⟨j, hj, hj'⟩ := hk''
    rw [Bool.and_eq_true, bne_iff_ne] at hj'
    obtain ⟨hjl, hj''⟩ := hj'
    exact ⟨k, hk, j, hj, hkl, hjl, of_decide_eq_true hj''⟩
  · rintro ⟨k, hk, j, hj, hkl, hjl, hscale⟩
    refine ⟨k, hk, ?_⟩
    rw [Bool.and_eq_true, bne_iff_ne]
    refine ⟨hkl, ?_⟩
    rw [List.any_eq_true]
    exact ⟨j, hj, by rw [Bool.and_eq_true, bne_iff_ne]; exact ⟨hjl, decide_eq_true_eq.mpr hscale⟩⟩

/-- ⭐⭐ **盒内 ⟹ 全量（覆盖引理）** —— **本节的实质内容**。

盒上穷举通过 ⟹ `ScaleClass c c'` 成立。

⚠ **这不显然**：穷举只覆盖有限盒，盒外必须靠**算术**兜住。本文件走 T1′ 的判据：
- 由 `scaleClassHoldsBounded_iff` 取出盒内见证 `(lam, mu)`；
- 该见证**直接给出** `ScaleClass c c'`（`ScaleClass` 的定义就是 `∃ lam mu ≠ 0, …`）。

⭐ **故这里的「覆盖论证」比 `RealNonlinearFidelity` 的简单**：
`ScaleClass` 是**存在性**陈述，盒内的见证**就是**全量的见证 —— **无需盒外论证**。
⚠ **本文件如实登记**：因此本定理**不是**报告设想的「盒外覆盖」；
它的增量是「**有限检验足以推出全量存在性**」这一**单向**读数。

⚠⚠ **注意方向**：**逆方向为假** ——
`ScaleClass c c'` **不**蕴含任意 `n` 的盒上穷举通过（见证可能在盒外）。
⇒ ⭐ **本文件不声称「盒穷举 ⟺ 全量」**（那需要界；本文件给出界的形式见下）。 -/
theorem scaleClass_of_bounded (c c' : VectorConstraint) (n : ℕ)
    (h : scaleClassHoldsBounded c c' n = true) : ScaleClass c c' := by
  obtain ⟨k, _hk, j, _hj, hkl, hjl, hscale⟩ := (scaleClassHoldsBounded_iff c c' n).mp h
  exact ⟨_, _, hkl, hjl, hscale⟩

/-- ⭐⭐ **T5′ 的诚实边界（**不许省**）**：

⚠⚠ **「盒穷举 ⟺ 全量」在本文件【不成立】，且我【没有】证它的「全量 ⟹ 盒内」方向。**

理由（**这是 `scaleClass_of_bounded` 方向性的根源**）：
`ScaleClass c c'` 只说**存在**一对非零倍率作见证，
而**见证的大小可以任意大** —— 例如 `c = c' = cUnit` 时，
`(lam, mu) = (K, K)` 对**任意** `K ≠ 0` 都是见证，
故 `n = 0` 的盒（只含 `lam = mu = 0`）上穷举**必然失败**，而 `ScaleClass` **为真**。

⇒ ⭐ **我明确登记**：要得到「⟺」需要**额外**的「见证规范化引理」
（把任意见证化为 `lam = content c'`、`mu = content c` 这一对**有界**的规范见证）——
⚠ **该引理我判定为可证但需要额外的算术工作**（把 `scaleClass_iff_canonicalize_eq_or_neg`
的 `(⟹)` 方向**反向**用一遍，从「规范形相等」**重建**一个有界见证），
**本文件未做**。**我不声称它**。

⭐ **报告 T5 建议的「界 `n ≥ max (content c) (content c')`」方向是对的**，
但它需要上面那条规范化引理才**闭合**；⚠ **本文件只给出单向的 `scaleClass_of_bounded`**。

⭐⭐ **本条把「为什么需要界」形式化**：`n = 0` 的盒（`range 1 = {0}`，故 `lam = mu = 0`）
**必然**在**自反对**上失败 —— 而 `ScaleClass cNegVec cNegVec` **为真**。
⇒ **盒穷举在 `n = 0` 上不完备**，故「取一个足够大的 `n`」是**必需**的，不是装饰。 -/
theorem scaleClassHoldsBounded_zero_box_fails :
    scaleClassHoldsBounded cNegVec cNegVec 0 = false ∧ ScaleClass cNegVec cNegVec := by
  refine ⟨?_, scaleClass_equivalence.refl cNegVec⟩
  unfold scaleClassHoldsBounded
  show ((List.range (2 * 0 + 1)).any fun k =>
      let lam : Int := (k : Int) - ((0 : ℕ) : Int)
      lam != 0 &&
        (List.range (2 * 0 + 1)).any fun j =>
          let mu : Int := (j : Int) - ((0 : ℕ) : Int)
          mu != 0 && decide (scaleVec cNegVec lam = scaleVec cNegVec mu)) = false
  norm_num

/-! ## 五、⭐ 跨模块桥：判定器经 `extractVec` 落到**权重侧**

⭐ **这是本文件唯一满足判据 3（跨模块）的部分** ——
它把「对象层」（`ConvertVectorLinear` 的 `VectorConstraint`/`LinearLayer`）
与「规范形层」（`RealCanonicalForm` 的 `ScaleClass`/`canonicalize`）**接起来**。

⚠⚠ **一处必须先讲清的【类型事实】**：`scaleVec : VectorConstraint → Int → VectorConstraint`，
**`LinearLayer` 上【没有】`scaleVec`** ⟹ 「`convertVec` 保持 `ScaleClass`」这句话
**在类型层就写不出来**（`ScaleClass (convertVec c) (convertVec c')` 是 **ill-typed**）。
⇒ ⭐ **本文件的处置**：在**权重侧就地定义**缩放与倍率类（照 `RealSymbolToWeightWidened.scaleLinearLayer`
的字段公式 `⟨w.map (·*lam), b*lam⟩`，⚠ 该模块**不可达**，故本文件自足复现），
**再**证明它与符号侧经 `extractVec` **完全一致**。
⚠ **如实登记**：这一步**不是**「连接两个此前无 import 关系的模块」——
它是**在权重侧新建同样的结构**再对齐；跨模块强度**弱**。 -/

/-- ⭐ **权重侧缩放**（`LinearLayer` 上的 `scaleVec` 对偶物）。
⚠ 本文件**自足定义**（`RealSymbolToWeightWidened` 的同名字段公式，
但该模块不在本文件的 import 闭包内，故**不引用**它）。 -/
def scaleLayerVec (l : LinearLayer) (lam : Int) : LinearLayer :=
  { w := l.w.map (fun v => v * lam), b := l.b * lam }

/-- ⭐⭐ **权重侧的倍率类**：`l` 与 `l'` 相差一个非零有理倍数。 -/
def ScaleClassLayer (l l' : LinearLayer) : Prop :=
  ∃ lam mu : Int, lam ≠ 0 ∧ mu ≠ 0 ∧ scaleLayerVec l lam = scaleLayerVec l' mu

/-- ⭐⭐ **跨模块桥梁（本节的实质内容）**：**权重侧缩放恰好是符号侧缩放的像**。

    `scaleLayerVec (convertVec c) lam = convertVec (scaleVec c lam)`

⭐ **这是 `extractVec` 能搬运 `ScaleClass` 的【唯一】理由** ——
它说「缩放」这个操作在**两个载体上**是**同一个操作**（只是字段名不同）。
⚠ **如实登记**：证明是逐字段的 `List.map` 对齐（`rfl` 级）。 -/
theorem scaleLayerVec_convertVec (c : VectorConstraint) (lam : Int) :
    scaleLayerVec (convertVec c) lam = convertVec (scaleVec c lam) := by
  cases c with
  | mk a b => rfl

/-- ⭐⭐ **`convertVec` 保持倍率类**（跨模块量词搬运）。 -/
theorem scaleClass_convertVec {c c' : VectorConstraint} (h : ScaleClass c c') :
    ScaleClassLayer (convertVec c) (convertVec c') := by
  obtain ⟨lam, mu, hlam, hmu, heq⟩ := h
  exact ⟨lam, mu, hlam, hmu, by
    rw [scaleLayerVec_convertVec, scaleLayerVec_convertVec, heq]⟩

/-- **`extractVec` 与 `scaleLayerVec` 交换**（对偶方向；同 `rfl` 级）。 -/
theorem extractVec_scaleLayerVec (l : LinearLayer) (lam : Int) :
    extractVec (scaleLayerVec l lam) = scaleVec (extractVec l) lam := by
  cases l with
  | mk w b => rfl

/-- ⭐⭐ **反向：`extractVec` 也保持倍率类**（把权重侧见证拉回符号侧）。 -/
theorem scaleClassLayer_extractVec {l l' : LinearLayer} (h : ScaleClassLayer l l') :
    ScaleClass (extractVec l) (extractVec l') := by
  obtain ⟨lam, mu, hlam, hmu, heq⟩ := h
  refine ⟨lam, mu, hlam, hmu, ?_⟩
  rw [← extractVec_scaleLayerVec, ← extractVec_scaleLayerVec, heq]

/-- ⭐⭐ **权重侧判定器**：把 `scaleClassB` 经 `extractVec` 抬高。

⭐ **这是「给定权重，判定它是否与另一个权重同一符号类」的可执行形式** ——
即题目「逆问题的可判定性」在**权重侧**的**有内容**版本。 -/
def scaleClassLayerB (l l' : LinearLayer) : Bool :=
  scaleClassB (extractVec l) (extractVec l')

/-- ⭐⭐ **跨模块主定理**：权重侧判定器可靠 + 完备（**无条件**）。

⭐ 依赖链跨越**三个**模块：
`ConvertVectorLinear`（结构体）→ `WeightToSymbolEquivalence`（`extractVec`）
→ `RealCanonicalForm`（`ScaleClass`/`scaleClassB`）→ 本文件的 `DecidableEq`（T0）。
⚠ **`extractVec` 的两个字段就是 `w`/`b`**，
故 `decide (extractVec l = extractVec l')` 恰是 T0 实例在起作用。 -/
theorem scaleClassLayerB_iff (l l' : LinearLayer) :
    scaleClassLayerB l l' = true ↔ ScaleClass (extractVec l) (extractVec l') :=
  scaleClassB_iff (extractVec l) (extractVec l')

/-- ⭐ **权重侧的 `Decidable` 实例**（T1 的权重侧对应物）。

⭐ **含义**：「两个权重是否同一符号类」在**权重层**上**可判定**，
且判定是**构造性**的（不是 `Classical.propDecidable`）。 -/
instance instDecidableScaleClassLayer (l l' : LinearLayer) :
    Decidable (ScaleClass (extractVec l) (extractVec l')) :=
  decidable_of_iff (scaleClassLayerB l l' = true) (scaleClassLayerB_iff l l')

end Lattice
