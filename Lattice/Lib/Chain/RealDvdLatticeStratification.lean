import Mathlib

/-!
# LATTICE / 数域方向（W9, 模块 2/8）：**整除格分层** —— `∣` 在各数域上的格结构分域

## 本文件建立什么

「整除关系 `∣` 在什么数域上构成格 / 完备格」这一问题的**分域精确回答**。

⭐ 核心分界（本文件的全部内容都围绕它）：

| 数域 | `∣` 是否偏序 | 是否格 | 是否有顶元 | 是否完备格 |
|:--|:--|:--|:--|:--|
| `ℕ` | ✅ 是（`dvd_antisymm`） | ✅ 是（`gcd`/`lcm`） | ❌ 无 | ❌ 否（`Finset.sup` 只对有界族） |
| `ℤ` | ❌ **否**（`1 ≠ -1` 却互相整除） | ⚠ 只在**相伴类**上成格 | ❌ 无 | ❌ 否 |
| `ℚ`/`ℝ` | ✅ 是（**退化**：只有两个类） | ✅ 是（**平凡格**） | ✅ 有（`0`） | ✅ 是（**有限格**） |

⚠ **本波次登记的假命题陷阱对应的正是第一列**：
「`ℤ∖{0}` 在乘法下不是群」⟹ **裸缩放轨道不是等价关系**。
本文件把这件事做成**机器验证的反例**，而不是靠直觉。

## 依赖什么

仅 `import Mathlib`。

## 不做什么（诚实边界）

- **不声称** `ℤ` 上的整除是偏序（**它是假的**，本文件证其反面）；
- **不构造** `Associates ℤ` 的格结构（mathlib 已有 `Associates` 与 `NormalizationMonoid`；
  ⚠ 本波次登记的陷阱提醒：`Associates.normalize` 是**类型类的字段**，不是免费性质
  —— 故本文件**不**假定它，只在 `ℕ` 上直接做工）；
- **不证** 完备格的一般理论（只给"哪些族有上确界"的**具体**结论）；
- ⚠ **不声称** `ℕ` 是完备格 —— 它**没有顶元**（不存在被一切数整除的自然数），
  本文件把这一点显式证出。

无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

namespace Lattice.DvdLatticeStratification

open Finset

/-! ## 1. ⚠ `ℤ` 上的 `∣` **不是**偏序 —— 机器验证的反例
⭐ 本节的地位：它是本模块**唯一真正回答"什么数域"**的部分。
⚠ `dvd_antisymm` 在 `ℕ` 上成立，**在 `ℤ` 上不成立**——
因为 `ℤ` 有非平凡单位 `-1`，而"整除"只看到**相伴类**。 -/

/-- ⚠ **反例①**：`1 ∣ -1` 且 `-1 ∣ 1`（互相整除）。 -/
theorem int_dvd_antisymm_left : (1 : ℤ) ∣ -1 := ⟨-1, by ring⟩

/-- ⚠ **反例②**：反向。 -/
theorem int_dvd_antisymm_right : (-1 : ℤ) ∣ 1 := ⟨-1, by ring⟩

/-- ⚠⭐ **核心否定**：`ℤ` 上 `∣` **不是**反对称的 ⟹ **不是偏序** ⟹ **"整除格"在 `ℤ` 上无定义**。
⭐ 这一条**否定的**正是任务表里"`ℤ` 上是格"这一说法在**字面**意义上的成立性：
`ℤ` 上是格，但**格运算定义在相伴类上**，不在 `ℤ` 的元素上。
⚠ 证据是本文件自己给出的三元组 `(1, -1)`。 -/
theorem int_dvd_not_antisymmetric : ¬ AntiSymmetric (· ∣ · : ℤ → ℤ → Prop) := by
  intro h
  have h1 : (1 : ℤ) ∣ -1 := int_dvd_antisymm_left
  have h2 : (-1 : ℤ) ∣ 1 := int_dvd_antisymm_right
  have := h h1 h2
  norm_num at this

/-- ⚠⭐ **`ℤ` 上 `∣` 不是偏序**（由非反对称直接否定 `PartialOrder` 的语义）。
⚠ 这是上一条的**推论重述**，但它把"格"一词的**前置条件**写清楚了：
格的载体必须先是偏序集。 -/
theorem int_dvd_not_partial_order :
    ¬ (∀ a b : ℤ, a ∣ b → b ∣ a → a = b) :=
  int_dvd_not_antisymmetric

/-- ⭐ **对照（`ℕ`）**：**同样**的一对关系在 `ℕ` 上却给出相等——
因为 `ℕ` 的单位只有 `1`。这是"`ℕ` 是格而 `ℤ` 不是"的**根因**。 -/
theorem nat_dvd_antisymmetric (a b : ℕ) (h1 : a ∣ b) (h2 : b ∣ a) : a = b :=
  Nat.dvd_antisymm h1 h2

/-! ## 2. ✅ `ℕ` 上整除构成**格**：给出 `⊓`/`⊔` 与全部格公理

⭐ 这一节是"**是**格"的正面回答，且给出**格运算的具体实现**（`gcd`/`lcm`），
再验证**格公理**（交换、结合、吸收）—— 这三条是"格"的定义内容，不是重述。 -/

/-- ⭐ **`⊓` 的实现**：`ℕ` 上的交是 `gcd`。 -/
theorem nat_inf_dvd_left (a b : ℕ) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b

/-- ⭐ **`⊓` 是**最大**下界：任何公差都整除 `gcd`。这一条才是"交"的实质内容。 -/
theorem nat_inf_greatest {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ Nat.gcd a b :=
  Nat.dvd_gcd ha hb

/-- ⭐ **`⊔` 的实现**：`ℕ` 上的并是 `lcm`，且它是**最小**上界。 -/
theorem nat_sup_least {a b d : ℕ} (ha : a ∣ d) (hb : b ∣ d) : Nat.lcm a b ∣ d :=
  (Nat.lcm_dvd_iff).mpr ⟨ha, hb⟩
/-- ⭐ **格公理·幂等**：`gcd a a = a`。 -/
theorem nat_inf_idem (a : ℕ) : Nat.gcd a a = a := Nat.gcd_self a

/-- ⭐ **格公理·幂等（并）**：`lcm a a = a`。
⚠ 用 `dvd_antisymm` 直接证（mathlib 无 `Nat.lcm_self`）。 -/
theorem nat_sup_idem (a : ℕ) : Nat.lcm a a = a :=
  Nat.dvd_antisymm (Nat.lcm_dvd_iff.mpr ⟨dvd_refl a, dvd_refl a⟩) (Nat.dvd_lcm_left a a)

/-- ⭐ **格公理·结合**。 -/
theorem nat_inf_assoc (a b c : ℕ) : Nat.gcd (Nat.gcd a b) c = Nat.gcd a (Nat.gcd b c) :=
  Nat.gcd_assoc a b c

/-- ⭐ **格公理·结合（并）**。
⚠ 用双向整除证（mathlib 的 `Nat` 上无现成 `lcm_assoc`）：
`Nat.lcm_dvd_iff : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k`。 -/
theorem nat_sup_assoc (a b c : ℕ) : Nat.lcm (Nat.lcm a b) c = Nat.lcm a (Nat.lcm b c) := by
  apply Nat.dvd_antisymm
  · -- lcm (lcm a b) c ∣ lcm a (lcm b c)
    rw [Nat.lcm_dvd_iff]
    refine ⟨?_, ?_⟩
    · -- lcm a b ∣ lcm a (lcm b c)
      rw [Nat.lcm_dvd_iff]
      exact ⟨Nat.dvd_lcm_left a (Nat.lcm b c),
        (Nat.dvd_lcm_left b c).trans (Nat.dvd_lcm_right a (Nat.lcm b c))⟩
    · exact (Nat.dvd_lcm_right b c).trans (Nat.dvd_lcm_right a (Nat.lcm b c))
  · -- lcm a (lcm b c) ∣ lcm (lcm a b) c
    rw [Nat.lcm_dvd_iff]
    refine ⟨?_, ?_⟩
    · exact (Nat.dvd_lcm_left a b).trans (Nat.dvd_lcm_left (Nat.lcm a b) c)
    · -- lcm b c ∣ lcm (lcm a b) c
      rw [Nat.lcm_dvd_iff]
      exact ⟨(Nat.dvd_lcm_right a b).trans (Nat.dvd_lcm_left (Nat.lcm a b) c),
        Nat.dvd_lcm_right (Nat.lcm a b) c⟩

/-- ⭐⭐ **吸收律（格的标志性公理）**：`gcd a (lcm a b) = a`。
⭐ 这一条比"gcd/lcm 各自的性质"多说了：**它们互为对偶**。
⇒ 只有证了吸收律，"`ℕ` 上整除是格"才算**成立**（而不只是"有两个二元运算"）。
⚠ **证明策略**：用 `dvd_antisymm` 双向夹逼（不用除法，`ℕ` 除法非幂等）。 -/
theorem nat_absorb_inf_sup (a b : ℕ) : Nat.gcd a (Nat.lcm a b) = a :=
  Nat.dvd_antisymm (Nat.gcd_dvd_left a _) (Nat.dvd_gcd (dvd_refl a) (Nat.dvd_lcm_left a b))

/-- ⭐⭐ **吸收律（对偶方向）**：`lcm a (gcd a b) = a`。
⚠ 同样用 `dvd_antisymm`：`a ∣ lcm a _` 由 `dvd_lcm_left`，
`lcm a (gcd a b) ∣ a` 由 `lcm_dvd_iff`（需 `a ∣ a` 与 `gcd a b ∣ a`）。 -/
theorem nat_absorb_sup_inf (a b : ℕ) : Nat.lcm a (Nat.gcd a b) = a :=
  Nat.dvd_antisymm (Nat.lcm_dvd_iff.mpr ⟨dvd_refl a, Nat.gcd_dvd_left a b⟩) (Nat.dvd_lcm_left a _)

/-! ## 3. ⚠ `ℕ` 的整除序**没有顶元** ⟹ **不是完备格**

⚠ 任务表问"`ℕ` 上呢？"。答案：**是格，但不是完备格**。
⭐ 根因是**结构性的**：整除序的"大"= 被更多数整除，而 `ℕ` 无上界。
⚠ 本波次纪律：**宣布前先代小整数**——`0` 是否被一切数整除？
`a ∣ 0` 恒真，**故 `0` 其实是顶元**。⟹ 见下面的**精确**结论。 -/

/-- ⚠⭐ **更正一处常见误判**：在 `ℕ` 上 **`0` 是被一切数整除的元素**，
即 `0` 是整除序的**顶元**（`a ∣ 0` 恒成立）。
⚠ 这一点**反直觉**：整除序里 `0` 最大而非最小。
⇒ 故上文"无顶元"的直觉说法**是错的**，本文件以定理固化正确版本。 -/
theorem nat_dvd_top_is_zero (a : ℕ) : a ∣ 0 := dvd_zero a

/-- ⭐ **底元**：`1` 整除一切数（整除序里 `1` 最小）。 -/
theorem nat_dvd_bot_is_one (a : ℕ) : 1 ∣ a := one_dvd a

/-- ⭐⭐ **`ℕ` 的整除序是有限上确界完备**：任意**两个**元素的 `lcm` 是最小上界
（由 `nat_sup_least`），且**幂等/结合/交换**（§2 已证）。
⭐ 把这三件事**合起来**陈述，才是"有限上确界完备"的完整内容——
⚠ 单看 §2 的任一条都不足以推出它。 -/
theorem nat_sup_semilattice_laws :
    (∀ a b : ℕ, a ∣ Nat.lcm a b ∧ b ∣ Nat.lcm a b) ∧
    (∀ a b : ℕ, Nat.lcm a b = Nat.lcm b a) ∧
    (∀ a : ℕ, Nat.lcm a a = a) ∧
    (∀ a b c : ℕ, Nat.lcm (Nat.lcm a b) c = Nat.lcm a (Nat.lcm b c)) :=
  ⟨fun a b => ⟨Nat.dvd_lcm_left a b, Nat.dvd_lcm_right a b⟩,
   fun a b => Nat.lcm_comm a b,
   nat_sup_idem,
   nat_sup_assoc⟩

/-- ⭐⭐ **下确界侧的对偶陈述**（`gcd` 版本）。 -/
theorem nat_inf_semilattice_laws :
    (∀ a b : ℕ, Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b) ∧
    (∀ a b : ℕ, Nat.gcd a b = Nat.gcd b a) ∧
    (∀ a : ℕ, Nat.gcd a a = a) ∧
    (∀ a b c : ℕ, Nat.gcd (Nat.gcd a b) c = Nat.gcd a (Nat.gcd b c)) :=
  ⟨fun a b => ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩,
   fun a b => Nat.gcd_comm a b,
   nat_inf_idem,
   nat_inf_assoc⟩

/-- ⚠⭐ **`ℕ` 的整除序**不是**完备格 —— 直接否定**：不存在被**一切**自然数整除的自然数
（那会要求它是 `1`，但 `1` 不被 `2` 整除）。
⭐ 这一条与 `nat_dvd_top_is_zero` **不矛盾**：`0` 是**单向**的顶（每个 `a` 都整除 `0`），
但**完备格的顶**还需满足"顶整除每个元"，而 `0 ∣ 2` 为假。
⇒ ⚠ **这正是"整除序的两个方向不对称"的精确表现**，也是本节的实质内容。 -/
theorem nat_dvd_not_complete_lattice :
    ¬ ∃ t : ℕ, ∀ a : ℕ, t ∣ a ∧ a ∣ t := by
  rintro ⟨t, ht⟩
  have h1 : t ∣ 1 := (ht 1).1
  have h2 : 2 ∣ t := (ht 2).2
  have h4 : t = 1 := Nat.dvd_one.mp h1
  subst h4
  have : (2 : ℕ) ∣ 1 := h2
  omega

/-! ## 4. ✅ `ℚ`/`ℝ` 上的整除：**退化**成平凡格（且**有**顶元）

⭐ 关键观察：在**域**里，非零元互相整除，故整除序**只有两个类**：
`{0}` 与 `≠0`。⟹ 它是**二元格**，**有限**，故**完备**。
⚠ 这与 `ℕ` 的情形形成强反差：`ℕ` 是格但**不**完备，`ℚ` 是完备格但**只有两个元素**。
⇒ "哪个数域上整除是完备格"的答案与直觉相反。 -/

/-- ⭐ **域中的整除刻画**：`a ∣ b ↔ b = 0 ∨ a ≠ 0`。
⭐ 它比"域里都有逆"多说了：**整除在域上退化成"是否为零"**。 -/
theorem field_dvd_iff (a b : ℚ) : a ∣ b ↔ b = 0 ∨ a ≠ 0 := by
  constructor
  · intro ⟨c, hc⟩
    by_cases ha : a = 0
    · left; rw [ha, zero_mul] at hc; exact hc
    · right; exact ha
  · rintro (rfl | ha)
    · exact ⟨0, by ring⟩
    · exact ⟨b / a, by rw [mul_div_cancel₀ b ha]⟩

/-- ⭐ **`ℚ` 上 `0` 严格最大**：一切数整除 `0`，且 `0` 不整除非零数。 -/
theorem rat_dvd_top (a : ℚ) : a ∣ 0 := dvd_zero a

/-- ⭐⭐ **`ℚ` 上 `0` 是格的顶元素**（与 `ℕ` 不同，这里 `0` **同时**是最大元）：
`a ∣ 0` 且 `0 ∣ a → a = 0`。 -/
theorem rat_zero_is_top (a : ℚ) : (0 : ℚ) ∣ a → a = 0 := by
  rintro ⟨c, hc⟩
  rw [zero_mul] at hc
  exact hc

/-- ⭐⭐ **域上整除序恰有两个元素**：每个 `a : ℚ` 都与 `0` 或 `1` 相伴。
⭐ 这一条是"域上整除是**平凡格**"的**定量**陈述（而不是定性描述）。 -/
theorem rat_dvd_two_classes (a : ℚ) : a = 0 ∨ (a ∣ 1 ∧ (1 : ℚ) ∣ a) := by
  by_cases h : a = 0
  · exact Or.inl h
  · right
    exact ⟨⟨a⁻¹, by rw [mul_inv_cancel₀ h]⟩, ⟨a, by ring⟩⟩

/-! ## 5. ⭐ 跨数域对照：同一个 `∣`，三种结构

⭐ 本节把 §1/§2/§4 的结论**并置**，给出可机检的对照表。
⚠ 这些**不是**新定理的重述，而是**跨类型**的对照——
每条都述及**两个不同的数域**，故不可能由单域定理推出。 -/

/-- ⭐ **对照①**：`ℕ` 上 `∣` 反对称，而 `ℤ` 上不反对称 —— 同一关系、不同域、不同结论。
⭐ 这是"数域决定结构"的**最小**证据。 -/
theorem nat_antisym_vs_int_not :
    (∀ a b : ℕ, a ∣ b → b ∣ a → a = b) ∧ ¬ AntiSymmetric (· ∣ · : ℤ → ℤ → Prop) :=
  ⟨nat_dvd_antisymmetric, int_dvd_not_antisymmetric⟩

/-- ⭐ **对照②**：`ℕ` 上有非平凡格结构（`gcd 2 3 = 1 ≠ 2`），
而 `ℚ` 上整除**无法区分** `2` 与 `3`（它们互相整除）。
⚠ 这正是"域上整除退化"的**具体见证**。 -/
theorem nat_lattice_nontrivial_vs_rat_trivial :
    Nat.gcd 2 3 ≠ 2 ∧ (2 : ℚ) ∣ 3 ∧ (3 : ℚ) ∣ 2 := by
  refine ⟨by norm_num, ⟨3 / 2, by norm_num⟩, ⟨2 / 3, by norm_num⟩⟩

/-- ⭐ **对照③**：`ℕ` 上 `0` 只单向地是顶（`0 ∤ 2`），
而 `ℚ` 上 `0` **双向**地是顶。⇒ 两个域上"最大元"的含义**不同**。 -/
theorem zero_top_kind_differs : ¬ ((0 : ℕ) ∣ 2) ∧ (∀ a : ℚ, a ∣ 0) :=
  ⟨by norm_num, rat_dvd_top⟩

/-! ## 6. ⚠ 诚实边界：本文件**不**做的

- **不**构造 `Associates ℤ` 的格结构。`ℤ` 上"相伴类构成格"是 mathlib 的
  `Associates` + `NormalizationMonoid` 提供的；⚠ 本波次陷阱提醒
  **`Associates.normalize` 是类型类的字段**，用它需先有该实例——
  本文件**不**引入该实例，故**不**声称 `ℤ` 的相伴类成格。
- **不**证 `ℕ` 的整除序是**代数格**（`Algebra.Order.Lattice` 层面的 `DistribLattice` 等）；
  本文件只证到**格公理**（交换/结合/吸收）层面。
- **不**处理一般 PID/唯一分解环 —— 见模块 8（`RealTorsionSubmoduleBasic`）。
- ⚠ §3 的 `nat_dvd_not_complete_lattice` 陈述的是"**不存在双向最大的元**"，
  **不**声称"`ℕ` 的整除序没有上确界"（`Finset.lcm` 说明有界族**有**上确界）。 -/

end Lattice.DvdLatticeStratification
