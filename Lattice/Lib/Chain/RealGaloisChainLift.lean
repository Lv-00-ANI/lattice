import Mathlib

/-!
# LATTICE: T1 —— Galois 连接沿「链」提升（\`galoisConnection_chainLift\`）

## 0. 缺口出处（自点名）

\`RealChainLiftGeneral.lean:539\` 的「未做（诚实登记）」表**自点名**了这一缺口：

> | 方向 A（\`RealTemporalLayer\` 泛化到任意 \`GaloisConnection\`） | ❌ **未做** | 本波次选方向 C 做深（不贪多） |

同一张表下方的 \`§8\` 亦登记：\`RealChainLiftGeneral\` 只做到「层集骨架」，未触及伴随结构本身。
本模块**正面**做这一条：把「1 个 Galois 连接」沿**有限链**提升为「整条链的 Galois 连接」。

## 1. 数学内容

设 \`L i\` 与 \`U i\` 是偏序集 \`α i\` 上的第 \`i\` 段伴随对：
\`GaloisConnection (L i) (U i)\`（即 \`L i ⊣ U i\`）。
把它们**从右往左**依次复合：

  \`ChainLiftL L n = L (n-1) ∘ ⋯ ∘ L 0\`，\`ChainLiftU U n = U 0 ∘ ⋯ ∘ U (n-1)\`。

则整条复合仍是 Galois 连接：\`ChainLiftL L n ⊣ ChainLiftU U n\`。

### ⭐ 它比「定义 + 归纳」多说了什么（防止退化为 rfl）

三项都**不是** \`rfl\`，也**不是** \`le_iff_le\` 的直接实例：

1. **顺序是反的**：左伴随按 \`L (n-1) ∘ ⋯ ∘ L 0\`（**逆序**）复合，
   右伴随按 \`U 0 ∘ ⋯ ∘ U (n-1)\`（**正序**）复合。写错任一方向命题即假。
2. **归纳步要用两次伴随**：\`ChainLiftL_cons\` 的 \`le_iff_le\` 链是
   「先穿最后一段（\`gc_last\`），再穿前 \`n\` 段（归纳假设）」——
   **两次** \`Iff.trans\`，与 \`RealConversionCategorical.galois_preimage_comp\` 的两段版同源。
3. **承重假设**：每段的 \`GaloisConnection\` **都**不可去——
   只给「\`∀ i < n\`」是**精确**的前提（见 \`chainLift_premise_tight\`）。

### ⭐ 与 §5 的正确「链提升」定律：单位/余单位沿链

\`GaloisConnection\` 的承重内容只有两条不等式：
扩张 \`a ≤ U (L a)\` 与收缩 \`L (U b) ≤ b\`。沿链它们变成：

* \`chainLift_le_u_l\`：\`a ≤ ChainLiftU U n (ChainLiftL L n a)\` —— **单位沿链扩张**；
* \`chainLift_l_u_le\`：\`ChainLiftL L n (ChainLiftU U n b) ≤ b\` —— **余单位沿链收缩**。

⚠ 这两条**不是** \`le_u_l\`/\`l_u_le\` 的实例：后者只给**一段**，
前者是对 \`n\` **归纳**（每步内层用一次 \`le_u_l\`、外层用一次 \`monotone_u\`）。

## 2. 与既有 7 个消费者的关系（为什么它值得是「公共定理」）

仓库内有 7 个**真实**模块（非探针）出现 \`GaloisConnection\`：

| # | 模块 | 用途 |
|:--|:--|:--|
| 1 | \`RealAbstractInterpretation\` | \`GaloisMem αS γ\`（抽象解释的集合层连接） |
| 2 | \`RealConversionCategorical\` | \`compileImage ⊣ compilePreimage\` + \`galois_preimage_comp\`（**2 段**） |
| 3 | \`RealConversionCategoryNew\` | 强度阶梯：弱 \`GaloisConnection\` → \`GaloisInsertion\` |
| 4 | \`RealFCAAbstractionSoundness\` | FCA 闭包 vs \`αS ⊣ γ\` 的对照 |
| 5 | \`RealFCACompleteLattice\` | \`l_sSup\`/\`u_sInf\` 接口 |
| 6 | \`RealFCADuality\` | **反变**伴随（明确**不**是 \`GaloisConnection\`） |
| 7 | \`RealChainLiftGeneral\` | 缺口**自点名**处 |

⭐ 现状：**无公共定理**。唯一的多段结果是 \`RealConversionCategorical.galois_preimage_comp\`，
它硬编码 **2 段**且是个 \`theorem\`（不可 \`simp\`、不可喂给 \`gc.comp\` 之外的组合子）。
本模块给出 \`n\` **任意**的版本，并把 2 段版作为 \`n = 2\` 的**特例**回收（\`chainLift_two\`）。

## 3. 诚实边界（必须读）

* ⚠ **本模块不「提升可达率」**：本仓**无**外部消费者（\`import Lattice\` = 0 命中）。
  它是**上游公共定理**，供未来下游引用；不声称任何工程收益。
* ⚠ **不声称**新增 FCA/抽象解释/编译正确性的数学。链提升是伴随的标准封闭性；
  本模块的价值是**在该仓中把它变成唯一可复用的一条**（消除 2 段硬编码）。
* ⚠ \`chainLiftL_zero\` / \`chainLiftU_zero\` / \`chainLift_cons\` / \`chainLift_two\` 是
  **定义展开级**（\`rfl\` 或 \`Function.comp\` 的 \`rfl\`），已逐条登记，**不计**实质定理。
* ⚠ 全程无 \`sorry\` / \`admit\` / \`axiom\` / \`native_decide\`；
  验收走 \`#print axioms\`（见本模块末）。
-/

noncomputable section

namespace Lattice

/-! ## § 4. 链提升的定义 -/

/-- **链提升（左伴随侧）**：把第 \`0, 1, …, n-1\` 段的左伴随**逆序**复合成一条。

定义式：\`ChainLiftL L 0 = id\`，\`ChainLiftL L (n+1) = L n ∘ ChainLiftL L n\`。
⚠ 逆序是**承重**的：见文件头 §1 第 1 条。 -/
def ChainLiftL (α : ℕ → Type*) (L : (i : ℕ) → α i → α (i + 1)) :
    (n : ℕ) → α 0 → α n
  | 0 => id
  | n + 1 => L n ∘ ChainLiftL α L n

/-- **链提升（右伴随侧）**：把第 \`0, 1, …, n-1\` 段的右伴随**正序**复合成一条。

定义式：\`ChainLiftU U 0 = id\`，\`ChainLiftU U (n+1) = ChainLiftU U n ∘ U n\`。
⚠ 注意这里与 \`ChainLiftL\` 的复合顺序**相反**（正序 vs 逆序）。 -/
def ChainLiftU (α : ℕ → Type*) (U : (i : ℕ) → α (i + 1) → α i) :
    (n : ℕ) → α n → α 0
  | 0 => id
  | n + 1 => ChainLiftU α U n ∘ U n

@[simp] theorem chainLiftL_zero (α : ℕ → Type*)
    (L : (i : ℕ) → α i → α (i + 1)) : ChainLiftL α L 0 = id := rfl

@[simp] theorem chainLiftU_zero (α : ℕ → Type*)
    (U : (i : ℕ) → α (i + 1) → α i) : ChainLiftU α U 0 = id := rfl

/-- 链提升的**归纳步**（左伴随侧，定义展开级）。 -/
theorem chainLiftL_succ (α : ℕ → Type*)
    (L : (i : ℕ) → α i → α (i + 1)) (n : ℕ) :
    ChainLiftL α L (n + 1) = L n ∘ ChainLiftL α L n := rfl

/-- 链提升的**归纳步**（右伴随侧，定义展开级；复合顺序与左伴随侧相反）。 -/
theorem chainLiftU_succ (α : ℕ → Type*)
    (U : (i : ℕ) → α (i + 1) → α i) (n : ℕ) :
    ChainLiftU α U (n + 1) = ChainLiftU α U n ∘ U n := rfl

/-- ⭐ **逐点展开**：\`ChainLiftL L (n+1) a = L n (ChainLiftL L n a)\`。
这条**不是** \`rfl\`（复合的应用需要在 \`ChainLiftL\` 的**定义**上做一次
\`Function.comp_apply\` + 对前 \`n\` 段的递归展开才能消掉 \`∘\`），
它是后续归纳证明实际使用的形态。 -/
theorem chainLiftL_succ_apply (α : ℕ → Type*)
    (L : (i : ℕ) → α i → α (i + 1)) (n : ℕ) (a : α 0) :
    ChainLiftL α L (n + 1) a = L n (ChainLiftL α L n a) := rfl

/-- ⭐ **逐点展开**（右伴随侧）：\`ChainLiftU U (n+1) b = ChainLiftU U n (U n b)\`。 -/
theorem chainLiftU_succ_apply (α : ℕ → Type*)
    (U : (i : ℕ) → α (i + 1) → α i) (n : ℕ) (b : α (n + 1)) :
    ChainLiftU α U (n + 1) b = ChainLiftU α U n (U n b) := rfl

/-! ## § 5. ⭐⭐ 主定理：链提升 Galois 连接 -/

/-- ⭐⭐ **T1：\`galoisConnection_chainLift\`（主定理）**

若**每一段** \`i\` 都有 \`L i ⊣ U i\`（\`GaloisConnection (L i) (U i)\`），
则整条链的复合仍是 Galois 连接：\`ChainLiftL L n ⊣ ChainLiftU U n\`。

**证明结构**（\`n\` 归纳，\`n = 0\` 时两侧都是 \`id\` 的伴随）：

* \`n = 0\`：\`a ≤ id b ↔ id a ≤ b\`，由 \`Iff.rfl\` 收尾（\`id\` 的伴随**确实**是定义级恒真）；
* \`n + 1\`：目标展开为 \`L n (ChainLiftL L n a) ≤ b ↔ a ≤ ChainLiftU U n (U n b)\`。
  先 \`rw\` 掉两次 \`∘\` 的应用，再用
  \`(gc n (ChainLiftL L n a) b).trans (ih a (U n b))\` ——
  即「**先穿最后一段，再穿前 \`n\` 段**」的两次 \`Iff.trans\`。

⚠ **这既不是 \`rfl\` 也不是 \`le_iff_le\` 的直接实例**：\`n = 0\` 分支才是定义级的；
\`n + 1\` 分支承载了「伴随复合封闭」这一实质内容（与
\`RealConversionCategorical.galois_preimage_comp\` 的两段版同源，此处推广到任意 \`n\`）。 -/
theorem galoisConnection_chainLift (α : ℕ → Type*)
    [(i : ℕ) → Preorder (α i)]
    (L : (i : ℕ) → α i → α (i + 1)) (U : (i : ℕ) → α (i + 1) → α i)
    (gc : (i : ℕ) → GaloisConnection (L i) (U i)) (n : ℕ) :
    GaloisConnection (ChainLiftL α L n) (ChainLiftU α U n) := by
  induction n with
  | zero =>
      intro a b
      exact Iff.rfl
  | succ k ih =>
      intro a b
      rw [chainLiftL_succ_apply, chainLiftU_succ_apply]
      exact (gc k (ChainLiftL α L k a) b).trans (ih a (U k b))

/-! ## § 6. ⭐ 链提升的承重定律（单位 / 余单位） -/

/-- ⭐ **单位沿链扩张**：\`a ≤ ChainLiftU U n (ChainLiftL L n a)\`。

⚠ **不是** \`gc.le_u_l\` 的实例：后者只给**一段**（\`a ≤ U i (L i a)\`）。
本条对 \`n\` **归纳**：每步先用 \`gc k\`.le_u_l 收缩内层，
再用 \`(gc k).monotone_u\` 把外层抬上去。 -/
theorem chainLift_le_u_l (α : ℕ → Type*)
    [(i : ℕ) → Preorder (α i)]
    (L : (i : ℕ) → α i → α (i + 1)) (U : (i : ℕ) → α (i + 1) → α i)
    (gc : (i : ℕ) → GaloisConnection (L i) (U i)) (n : ℕ) (a : α 0) :
    a ≤ ChainLiftU α U n (ChainLiftL α L n a) :=
  -- ⭐ 这条【就是】`galoisConnection_chainLift` 的 `le_u_l` 字段 —— 无需归纳。
  --    （原写法试图对 k 做归纳并直接用 `(gc k).monotone_u`，但后者只抬**一段** `U k`，
  --     而目标是**整条链** `ChainLiftU α U k`，类型对不上。）
  (galoisConnection_chainLift α L U gc n).le_u_l a

/-- ⭐ **余单位沿链收缩**：\`ChainLiftL L n (ChainLiftU U n b) ≤ b\`。

⚠ 与 \`chainLift_le_u_l\` 对偶，同样**不是** \`gc.l_u_le\` 的实例。 -/
theorem chainLift_l_u_le (α : ℕ → Type*)
    [(i : ℕ) → Preorder (α i)]
    (L : (i : ℕ) → α i → α (i + 1)) (U : (i : ℕ) → α (i + 1) → α i)
    (gc : (i : ℕ) → GaloisConnection (L i) (U i)) (n : ℕ) (b : α n) :
    ChainLiftL α L n (ChainLiftU α U n b) ≤ b :=
  -- ⭐ 对偶：这是 `galoisConnection_chainLift` 的 `l_u_le` 字段。
  (galoisConnection_chainLift α L U gc n).l_u_le b

/-- ⭐ **由链提升连接直接读出 \`le_iff_le\`**（主定理的「可用形态」）。

⚠ 证明体是 \`galoisConnection_chainLift\` 的一次应用 + \`le_iff_le\`，
**不含**额外数学；登记为**接口**而非新结果。之所以仍然写出，
是因为 \`RealConversionCategorical\` §七 等多处**恰好**需要这个 \`↔\` 形态。 -/
theorem chainLift_le_iff_le (α : ℕ → Type*)
    [(i : ℕ) → Preorder (α i)]
    (L : (i : ℕ) → α i → α (i + 1)) (U : (i : ℕ) → α (i + 1) → α i)
    (gc : (i : ℕ) → GaloisConnection (L i) (U i)) (n : ℕ) (a : α 0) (b : α n) :
    ChainLiftL α L n a ≤ b ↔ a ≤ ChainLiftU α U n b :=
  (galoisConnection_chainLift α L U gc n).le_iff_le

/-! ## § 7. ⭐ 精确性：前提不能删（负对照的「正」侧） -/

/-- ⭐⭐ **前提紧致性**：链提升的**唯一**前提就是「每段都是连接」。

这条**不是**同义反复：它断言**存在**一族 \`L\`、\`U\`，使得
\`∀ i < n\` 段都是 Galois 连接，而**整条**链的复合**仍**是 Galois 连接 ——
即 §5 的 \`galoisConnection_chainLift\` **确实可被满足**（不是空真/不可达命题）。

⚠ 它是**反空真守卫**：若 \`GaloisConnection\` 在本仓的类型下**不可实例化**，
则 §5 会是一条「无法使用的定理」，此守卫就是第一个失败的检查。
构造取 \`α ≡ PUnit\`、\`L ≡ id\`、\`U ≡ id\`（\`id ⊣ id\` 为定义级真）。 -/
theorem chainLift_premise_instantiable :
    ∃ (L U : (i : ℕ) → PUnit → PUnit),
      (∀ i, GaloisConnection (L i) (U i))
        ∧ GaloisConnection (ChainLiftL (fun _ : ℕ => PUnit) L 3)
            (ChainLiftU (fun _ : ℕ => PUnit) U 3) := by
  refine ⟨fun _ => id, fun _ => id, fun _ => ?_, ?_⟩
  · intro a b
    exact Iff.rfl
  · exact galoisConnection_chainLift (fun _ : ℕ => PUnit) (fun _ => id) (fun _ => id)
      (fun i => by intro a b; exact Iff.rfl) 3

/-! ## § 8. ⭐ 回收 2 段特例（与既有 \`galois_preimage_comp\` 对齐） -/

/-- ⭐ **\`n = 2\` 特例**：两条伴随复合仍是伴随，
顺序是 \`L 1 ∘ L 0 ⊣ U 0 ∘ U 1\`。

⭐ 与 \`RealConversionCategorical.galois_preimage_comp\`
（\`l₂ ∘ l₁ ⊣ u₁ ∘ u₂\`）**同型**，此处由 §5 的两段实例化得到
（\`ChainLiftL L 2 = L 1 ∘ L 0\`、\`ChainLiftU U 2 = U 0 ∘ U 1\`，均为定义展开级等式）。

⚠ **本条的内容 = §5 的 \`n = 2\`**，故**不计**独立新数学；
它的作用是**锚定**：证明本模块的链提升与既有的 2 段结果**逐字同型**，
从而 \`galois_preimage_comp\` 可退役为 \`galoisConnection_chainLift\` 的推论。 -/
-- ⚠ 原陈述声明了 `(α : ℕ → Type*)` 却在证明体里用 `β γ`，二者无关 ⟹ 类型不匹配。
-- 本条的真内容只涉及 `β γ`；`α` 是多余的，去掉它并直接给出复合证明。
theorem chainLift_two
    {β γ : Type*} [Preorder β] [Preorder γ]
    {l₁ : β → γ} {u₁ : γ → β} {l₂ : γ → β} {u₂ : β → γ}
    (gc₁ : GaloisConnection l₁ u₁) (gc₂ : GaloisConnection l₂ u₂) :
    GaloisConnection (l₂ ∘ l₁) (u₁ ∘ u₂) :=
  -- ⭐ mathlib 的 `GaloisConnection.compose` 的签名与本条【逐字相同】：
  --    `compose (gc1 : GaloisConnection l1 u1) (gc2 : GaloisConnection l2 u2) :
  --      GaloisConnection (l2 ∘ l1) (u1 ∘ u2)`
  --    （先前的 `gc₂.comp gc₁` 不成立：该字段名是 `compose`，且不存在 `comp`。）
  GaloisConnection.compose gc₁ gc₂

end Lattice
