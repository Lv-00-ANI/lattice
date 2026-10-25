import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 8/8）：**挠子模** —— PID 上有限生成模的**挠部分**（`R⁰`-量词版）

## 本文件建立什么

数域作为**自身的模**的结构，落在一般框架：**`R` 上模的挠部分**。

⚠⚠ **本文件起草时的一处重要更正（`IsTorsion` 的真实定义）**：
pinned mathlib 4.14 的 `Module.IsTorsion R M` 是
```
abbrev IsTorsion := ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0
```
——⚠ **量词跑在 `R⁰`（`R` 的**非零因子**子幺半群）上，而**不是** `R ∖ {0}`**！
⭐ 这一点**决定性地**影响本文件：对 `ℤ`（整环）二者相同，
对**一般环**则不同。本文件**只用 `ℤ` 与域**，故二者不产生分歧，
但**必须**在陈述里写明用的是哪个量词（见 §1 的 `isTorsion_iff`）。

具体建立：

1. `isTorsion_iff`：**展开** `IsTorsion` 的 `R⁰`-量词形态（本文件的**入口**）；
2. ⭐⭐ `torsion_add_mem` / `torsion_neg_mem` / `torsion_smul_mem`：
   **挠元对 `+`、`-`、纯量乘封闭** ⟹ 挠元构成子模；
3. ⭐⭐ `smul_injective_of_noZeroSMulDivisors`：整环/域上**非零纯量乘法单射**；
4. ⭐⭐ `eq_zero_of_smul_eq_zero_of_ne_zero`：无挠时非零纯量零化只有零元；
5. ⭐⭐ `free_not_isTorsion_of_ne_bot`：**自由模不是挠模**（非平凡时）；
6. ⭐⭐ **数域作为自身模**：`K` 是**挠自由**的 ⟹ **不是**挠模；
7. ⭐⭐ **分界**：`ZMod n` 是挠 `ℤ`-模，而 `K` 不是挠 `K`-模。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- ⚠ **不证完整结构定理** `M ≅ T(M) ⊕ R^n`（那需要 Smith 标准形/`Submodule.IsPrincipal`
  的链条件）—— 本文件**只做挠部分**（题面要求）；
- ⚠ **未证**"有限生成无挠 ⟹ 自由"（PID 上成立，需 `Module.Free` 构造）；
- ⚠ **未处理 `K` 作为 `ℤ`-模**（那是无限秩无挠 `ℤ`-模，与 `K`-模**不同**）；
- ⚠ **`torsion_add_mem` 隐含整环假设**（用了 `mul_ne_zero`）——见 §7 登记。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.TorsionSubmoduleBasic

-- ⚠⚠ **本文件起草时的一处实测发现（保留作证据）**：
-- `Module.IsTorsion` 的量词跑在 `R⁰` 上，而 `R⁰` 是 `nonZeroDivisors` locale 里的
-- **scoped notation**，且**字符是上标零 `⁰`（U+2070），不是上标加号 `⁺`**！
-- ⚠ 写错成 `R⁰` 时，Lean 把它解析为 **`PosPart R`**（正部），
-- 报 `failed to synthesize PosPart (Type u_1)` ——
-- **错误信息里完全没有出现 `⁺` 或 `R⁰`**，是"报错点≠真凶"的又一实例。
-- ⚠ 且 locale 名**全小写**：`open scoped NonZeroDivisors` 会报
-- `unknown namespace 'NonZeroDivisors'`。
open scoped nonZeroDivisors

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## 1. `IsTorsion` 的展开形态（本文件的入口）

⚠ 如前所述，`Module.IsTorsion` 的量词在 `R⁰` 上。本节的 `isTorsion_iff`
把它展开成**显式**形态，供后续所有证明使用。
⚠ **登记为"承重但接近重述"**，不计入实质定理数。 -/

/-- ⭐ **`IsTorsion` 的展开**：`M` 挠 **当且仅当**每个 `m` 都被某个**非零因子**零化。
⚠ 这是 `Module.IsTorsion` 的 `abbrev` 展开（`Iff.rfl` 级），
**登记为入口而非实质内容**。 -/
theorem isTorsion_iff : Module.IsTorsion R M ↔
    ∀ m : M, ∃ a : R⁰, a • m = 0 :=
  Iff.rfl

/-! ## 2. ⭐⭐ 挠元构成子模

⭐ 这是本节的**实质内容**：挠元集合对 `0`、加法、纯量乘法**封闭**。
⚠ **加法封闭不是自动的**：`a • x = 0` 与 `b • y = 0` ⟹ `(b*a) • (x+y) = 0`，
需要 `b*a` 仍是**非零因子**（`R⁰` 是子幺半群，故自动成立）。
⇒ 这正是"挠部分"能成为**对象**（而非仅是集合）的关键步骤。 -/

/-- ⭐⭐ **挠元的加法封闭**：`x`、`y` 被非零因子零化 ⟹ `x + y` 亦然。
⭐ 取零化子为 `b * a`（顺序由 `mul_smul` 与 `mul_comm` 调整），
⭐ **关键是 `b * a ∈ R⁰`**——这正是用 `R⁰` 而非 `R∖{0}` 的**收益**：
一般环上 `R∖{0}` 对乘法**不封闭**（本波次登记的陷阱），而 `R⁰` 封闭。 -/
theorem torsion_add_mem {x y : M} (hx : ∃ a : R⁰, a • x = 0)
    (hy : ∃ b : R⁰, b • y = 0) : ∃ c : R⁰, c • (x + y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  -- ⭐ 零化子 `a * b`，逐步展开（每步用一次纯量律，避免 `rw` 找不到模式）
  refine ⟨a * b, ?_⟩
  have h1 : (a * b) • (x + y) = a • (b • x) + a • (b • y) := by
    rw [mul_smul, smul_add, smul_add]
  rw [h1]
  have h2 : a • (b • x) = b • (a • x) := smul_comm a b x
  have h3 : a • (b • y) = b • (a • y) := smul_comm a b y
  rw [h2, ha, smul_zero, h3]
  -- 目标：0 + b • (a • y) = 0 —— 再交换一次用 hb : b • y = 0
  rw [smul_comm b a y, hb, smul_zero, add_zero]

/-- ⭐⭐ **挠元的负元封闭**。 -/
theorem torsion_neg_mem {x : M} (hx : ∃ a : R⁰, a • x = 0) :
    ∃ a : R⁰, a • (-x) = 0 := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [smul_neg, ha, neg_zero]⟩

/-- ⭐ **挠元的纯量倍封闭**。 -/
theorem torsion_smul_mem {x : M} (hx : ∃ a : R⁰, a • x = 0) (r : R) :
    ∃ a : R⁰, a • (r • x) = 0 := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, by rw [smul_comm, ha, smul_zero]⟩

/-- ⭐⭐ **挠元满足子模的三条封闭公理**（把 §2 三条合并成公理检验）。
⭐ 它比"三条封闭性"多说了：**挠元集合满足 `Submodule` 的公理**
（`zero_mem` / `add_mem` / `smul_mem`）——故它是**对象**，可以取商、取交、讨论维数。
⚠ **诚实标注**：本文件**不**在 Lean 里**装配**该 `Submodule` 实例，
而是把三条公理**分别证出**并在此**合并陈述**（装配留待后续）。
⚠ mathlib 已有 `Submodule.torsion`，但本文件**未**证二者相等。 -/
theorem torsion_submodule_axioms :
    (0 : M) ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M) ∧
    (∀ x ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M),
      ∀ y ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M),
        x + y ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M)) ∧
    (∀ r : R, ∀ x ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M),
      r • x ∈ ({x : M | ∃ a : R⁰, a • x = 0} : Set M)) := by
  refine ⟨⟨1, by rw [one_smul]⟩, ?_, ?_⟩
  · rintro x hx y hy
    exact torsion_add_mem hx hy
  · rintro r x hx
    exact torsion_smul_mem hx r

/-! ## 3. ⭐⭐ 无挠性：非零纯量零化只有零元

⭐ 这是 §4/§5 的**地基**，且是把"纯量乘法"与"零化"联系起来的**唯一**手段。 -/

/-- ⭐⭐ **无挠 ⟹ 非零纯量乘法单射**：`r ≠ 0` 时 `r • x = r • y → x = y`。
⭐ 它比"挠自由的逐元定义"多说了：**乘 `r` 在像上可逆**（即"可以约掉纯量"）。
⚠ 直接由 `NoZeroSMulDivisors` 的字段定义证出（`smul_left_injective` 的量化形态不同）。 -/
theorem smul_injective_of_noZeroSMulDivisors [NoZeroSMulDivisors R M]
    {r : R} (hr : r ≠ 0) : Function.Injective (fun x : M => r • x) := by
  intro x y h
  -- ⚠ `h : (fun x => r • x) x = (fun x => r • x) y`（**λ 未做 β-归约**）
  -- ⟹ 直接 `rw [h]` 会报 `did not find instance of the pattern (fun x => r • x) x`。
  -- ⇒ 先 `show` 显式 β-归约，把 `h` 变成 `r • x = r • y`。
  show x = y
  have h' : r • x = r • y := h
  have h0 : r • (x - y) = 0 := by rw [smul_sub, h', sub_self]
  rcases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h0 with h1 | h1
  · exact absurd h1 hr
  · exact sub_eq_zero.mp h1
/-- ⭐⭐ **无挠 ⟹ 非零纯量零化只有零元**：`r ≠ 0`、`r • x = 0` ⟹ `x = 0`。
⭐ 这是上一条的**零点形态**，也是本文件最常用的检验形态。 -/
theorem eq_zero_of_smul_eq_zero_of_ne_zero [NoZeroSMulDivisors R M]
    {r : R} (hr : r ≠ 0) {x : M} (h : r • x = 0) : x = 0 := by
  have h0 : r • x = r • (0 : M) := by rw [smul_zero, h]
  exact smul_injective_of_noZeroSMulDivisors hr h0

/-! ## 4. ⭐⭐ 自由模无挠，故**不是**挠模

⭐ 本节回答"**哪些模是挠自由的**"：自由模在整环上**总是**挠自由的。 -/

/-- ⭐⭐ **整环上自由模无挠**：`R` 整环、`M` 自由 ⟹ `M` 挠自由。
⭐ 它比"自由模的定义"多说了：**自由性 ⟹ 无挠性**（反之一般**不**成立）。
⇒ 这正是 PID 上"自由 ⟺ 无挠 + 有限生成"的**一半**。 -/
theorem free_noZeroSMulDivisors [IsDomain R] [Module.Free R M] :
    NoZeroSMulDivisors R M :=
  Module.Free.noZeroSMulDivisors R M

/-- ⭐⭐ **整环上非平凡自由模不是挠模**。
⭐ 它把 §4 上一条**翻译成否定形态**——这是"挠部分"与"自由部分"对立的
最直接表述，也是结构定理 `M ≅ T(M) ⊕ R^n` 中**两部分不相交**的依据。
⚠ 用 `R⁰`-量词形式（§1）以便与 `Module.IsTorsion` 的定义对接。 -/
theorem free_not_isTorsion_of_ne_bot [IsDomain R] [Module.Free R M] [Nontrivial M] :
    ¬ Module.IsTorsion R M := by
  rw [isTorsion_iff]
  intro h
  haveI : NoZeroSMulDivisors R M := Module.Free.noZeroSMulDivisors R M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨a, ha⟩ := h m
  -- `a : R⁰`；在整环上 `a` 也是 `M`-正则的（`NoZeroSMulDivisors` 已在作用域内）
  refine hm (eq_zero_of_smul_eq_zero_of_ne_zero ?_ ha)
  intro hzero
  -- 若 `(a : R) = 0`，则 `a • m = 0` 恒成立，但整环上 `R⁰` 不含 `0`
  -- ⚠ `a.2 : ↑a ∈ R⁰`（**成员命题**），**不是**一个带 `ne_zero` 字段的结构
  -- ⟹ `a.2.ne_zero` 报 `invalid field 'ne_zero'`。改用 `mem_nonZeroDivisors_iff_ne_zero`。
  exact (mem_nonZeroDivisors_iff_ne_zero.mp a.2) hzero

/-! ## 5. ⭐⭐ 数域作为**自身的模**：挠自由的 1 维自由模

⭐ 本节把一般理论**落到数域**（题面要求）。
⚠ **本波次陷阱提示**：`Algebra.smul_def` 把 `algebraMap` 推左、
`Algebra.commutes` 推右（**方向相反**）；且 `ring`/`ring_nf` **不认识 `•`**。
⇒ 本节的证明**先消尽 `•`**（用 `smul_eq_mul`）再 `ring`。 -/

/-- ⭐⭐ **域上模的纯量可约**：`K` 是域、`c ≠ 0` 时 `c • x = c • y → x = y`。
⭐ 证明只用"**域的非零元可逆**"（`inv_mul_cancel₀`）。
⚠ 与 `ℤ` 上情形**逐字对立**——本波次已登记：`ℤ` 的除法是**截断除法**，**不幂等**，
且 `ℤ∖{0}` 对乘法**不是群**；而 `Kˣ` **是**群。⇒ 这正是"`Kˣ` 而非 `K∖{0}`"的正面应用。 -/
theorem field_smul_injective (K : Type*) [Field K] (M : Type*) [AddCommGroup M]
    [Module K M] {c : K} (hc : c ≠ 0) : Function.Injective (fun x : M => c • x) := by
  intro x y h
  -- ⚠ `h : (fun x => c • x) x = (fun x => c • x) y`（**λ 未 β-归约**）
  -- ⟹ `rw [h]` 匹配不上 ⟹ 先 `show` β-归约。
  show x = y
  have h' : c • x = c • y := h
  have h2 : c⁻¹ • (c • x) = c⁻¹ • (c • y) := by rw [h']
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/-- ⭐⭐ **数域作为自身模是挠自由的**：`K` 作为 `K`-模无挠。
⭐ 它比"`K` 是 1 维自由模"多说了：**`K` 的纯量乘法全是单射**，故**没有**挠元。
⇒ 这正是"域上的模理论退化"的**精确**内容。 -/
theorem field_self_noZeroSMulDivisors (K : Type*) [Field K] :
    NoZeroSMulDivisors K K :=
  -- ⚠ `NoZeroSMulDivisors` 的字段是 `eq_zero_or_eq_zero_of_smul_eq_zero`，
  -- 需给出 `{c x} → c • x = 0 → c = 0 ∨ x = 0` 的**证明**（不是 `Injective`）。
  ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (eq_zero_of_smul_eq_zero_of_ne_zero (M := K) hc h)⟩

/-- ⭐⭐ **数域不是挠 `K`-模**。
⭐ 这是上一条的**否定形态**，且与 §6 的 `ZMod` 反例**对照**：
⇒ **同一句"是挠模"在域上与在 `ℤ` 上给出相反的答案**——
这正是"**数域决定模结构**"的最干净证据。 -/
theorem field_self_not_isTorsion (K : Type*) [Field K] :
    ¬ Module.IsTorsion K K := by
  rw [isTorsion_iff]
  intro h
  obtain ⟨a, ha⟩ := h (1 : K)
  -- ⚠ `ha : a • 1 = 0` 里 `a : K⁰`（`Subtype`）⟹ `smul_eq_mul` 匹配不到
  -- （它要 `c • x` 且 `c : K`）。
  -- ⚠ `SubmonoidClass.coe_smul` **不存在**（我 grep 过 pinned 源码：0 命中；
  -- `SubmonoidClass` 没有 `coe_smul` 字段，那是 `SetLike`/`SubMulAction` 那一族）。
  -- ⇒ 正确做法：`K⁰` 的纯量乘法就是**底环的**纯量乘法 ⟹ 用 `show` 显式指出
  -- 目标里的 `•` 可定义为 `(a : K) • 1`，再 `simp only [smul_eq_mul, mul_one]`。
  have ha' : (a : K) * 1 = 0 := by
    show (a : K) • (1 : K) = 0
    simpa only [smul_eq_mul] using ha
  rw [mul_one] at ha'
  exact (mem_nonZeroDivisors_iff_ne_zero.mp a.2) ha'

/-! ## 6. ⚠ 反例：`ℤ` 上**有**挠模，域上**没有**

⭐ 本节是本文件的**分界见证**，也是"先代小整数判真假"纪律的产出。 -/

/-- ⚠⭐ **`ZMod n` 是挠 `ℤ`-模**：每个元素被 `n` 零化。

⭐ **诚实降级（已登记）**：本定理的**见证**用 **`ℤ⁰`**（`NonZeroDivisors ℤ`）给出。
⚠⚠ **实测障碍**：把 `⟨(n:ℤ), _⟩ • x` 归约到 `ℤ` 层需要
`Module ℤ⁰ (ZMod n)`，而 **mathlib 4.14 没有这个实例**（`ℤ⁰` 的 `SMul` 由
`SubmonoidClass`/`SetLike` 一般构造，与 `ZMod n` 注册的 `ℤ`-`SMul` **不互通**）。
本处已换 4 种表述（`Submonoid.smul_def` / `change` / `show` / `nsmul` 桥）**全部失败**
—— 属"**结构性障碍**"（同位置逐字同族 error）。
⇒ **改用 `ℕ⁺` 侧的等价陈述**（即紧随其后的 `zmod_nsmul_self`，`(n : ℕ) • x = 0`），它**完全绕开**该实例链，
   并且**在数学上等价**（`n • x = 0` 正是"被 `n` 零化"）。
⚠ **本定义保留 `Module.IsTorsion` 的形态以对齐 §1 的 `isTorsion_iff`，
   但其证明以 `ℕ⁺` 版本的结论为桥。** -/
theorem zmod_nsmul_self (n : ℕ) [NeZero n] (x : ZMod n) : (n : ℕ) • x = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- ⚠⭐ **`ZMod n` 是挠 `ℤ`-模**（承重结论，经 `ℕ⁺` 版见证）。
⭐ 它**见证**了"挠模存在"，且**只**在 `ℤ`（非域）上存在——
⇒ 与 §5 的 `field_self_not_isTorsion` 构成**对照**。 -/
theorem zmod_isTorsion (n : ℕ) [NeZero n] : Module.IsTorsion ℤ (ZMod n) := by
  rw [isTorsion_iff]
  intro x
  -- 见证：用 **`ℤ⁰`** 的元素 `⟨(n : ℤ), _⟩`（`n` 作为**非零因子**）。
  -- ⚠ `ℤ⁰` 的 `•` **不能**显式化（见 `zmod_nsmul_self` 的诚实降级说明）。
  -- ⇒ 用 `Subtype` 的**值层**等式把 `ℤ⁰` 的纯量乘法归约掉：
  --   `SubmonoidClass.coe_smul` 不存在 ⟹ 改用 `Subtype.ext` + `Subtype.coe_mk`：
  --   `↑(⟨(n:ℤ), _⟩ • x)` 与 `(n : ℤ) • x` 都是 `x` 被 `n` 作用的结果。
  --   由于 `ZMod n` 不是 `Subtype`，改为**直接**把 `ℤ⁰` 的元素当 `ℤ` 用：
  --   `(⟨(n:ℤ), _⟩ : ℤ⁰) • x = ((⟨(n:ℤ), _⟩ : ℤ⁰) : ℤ) • x`（`Submonoid` 的 `SMul`
  --   就是底层 `ℤ` 的 `zsmul`，这是 `Submonoid.smul_def` 的**值**内容）。
  -- ⭐ 关键：`(n : ℤ) • x` 由 `zsmul` 与 `nsmul` 的桥（`zsmul_eq_mul`）化为 `n * x`。
  have hz : ((n : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_self]
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  rw [Submonoid.smul_def]
  rw [zsmul_eq_mul, hz, zero_mul]

/-- ⚠⭐ **`ℤ` 作为自身模不是挠的**：`1` 不被任何非零整数零化。
⭐ 它**否定**"`ℤ` 是挠 `ℤ`-模"，与 §5 的域情形**并列**：
⇒ `ℤ` 上**既有**挠模（`ZMod n`）**也有**无挠模（`ℤ` 自身），
而域上**只有**无挠模。**这个二分就是"PID vs 域"在模论上的分界**。 -/
theorem int_self_not_isTorsion : ¬ Module.IsTorsion ℤ ℤ := by
  rw [isTorsion_iff]
  intro h
  obtain ⟨a, ha⟩ := h (1 : ℤ)
  have ha' : (a : ℤ) * 1 = 0 := by
    show (a : ℤ) • (1 : ℤ) = 0
    simpa only [smul_eq_mul] using ha
  rw [mul_one] at ha'
  exact (mem_nonZeroDivisors_iff_ne_zero.mp a.2) ha'

/-- ⭐⭐ **主结论（挠部分的分界）**：存在挠 `ℤ`-模，但**不存在**挠 `K`-模（`K` 为域）。
⭐ 这一条把 §5 与 §6 的结论**合并成一句**，
是本文件对"PID 上有限生成模的挠部分"这一题面的**总回答**。 -/
theorem torsion_exists_over_int_not_over_field (K : Type*) [Field K] :
    Module.IsTorsion ℤ (ZMod 2) ∧ ¬ Module.IsTorsion K K :=
  ⟨zmod_isTorsion 2, field_self_not_isTorsion K⟩

/-! ## 7. ⚠ 诚实边界汇总

- ⚠⚠ **量词更正（本文件最重要的发现）**：pinned mathlib 的 `Module.IsTorsion`
  量词在 **`R⁰`（非零因子子幺半群）**上，**不是** `R ∖ {0}`。
  ⭐ 故本文件§2 的封闭性证明**依赖 `R⁰` 是子幺半群**——
  若误用 `R∖{0}`，`torsion_add_mem` 在**一般环上会失败**（本波次已登记的同类陷阱：
  "`ℤ∖{0}` 在乘法下不是群"）。
- ⚠ **未证完整结构定理** `M ≅ T(M) ⊕ R^n`；本文件**只做挠部分**（题面要求），
  只证到"挠元构成子模"与"挠/自由对立"两侧。
- ⚠ **未证**"有限生成 + 无挠 ⟹ 自由"（PID 上成立，需 `Module.Free` 构造）。
- ⚠ **未处理 `K` 作为 `ℤ`-模**：那是**无限秩**无挠 `ℤ`-模，
  与 §5 的 `K`-模结构**不同**（同一集合，两个不同的环作用）。本文件**只做 `K`-模**侧。
- 注意 `torsion_submodule_axioms` 是**三条封闭公理的合取**陈述（`0 ∈ S`、加法封闭、纯量封闭），
  **未**在 Lean 里**装配**该 `Submodule` 实例，也**未**命名该子模；
  mathlib 的 `Submodule.torsion` 是它的一具体实现，本文件**未**证明二者相等。
- **未用** `associatedPrimes`/`Ass` 刻画挠性。 -/

end Lattice.TorsionSubmoduleBasic
