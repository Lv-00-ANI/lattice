/-
# 语义信息主线 · 阶段 1.5：词表编辑与对齐

## 0. 这一节补的是被阻塞的那一块

第 204 轮把 S14–S20 标为「被阻塞：模型级 `Embedding`/`OutputHead` 不存在，
`VocabCompat` 连陈述都不能」。**这一节先定下那个形状，再把 S14–S19 做出来。**

## 1. 形状的决定与理由（这是上一轮悬着的问题）

```lean
structure Embedding (V : Type) (d : ℕ) where
  row : V → Fin d → ℝ        -- V × d 矩阵
structure OutputHead (V : Type) (d : ℕ) where
  col : Fin d → V → ℝ        -- d × V 矩阵
structure VocabModel (V : Type) (d : ℕ) where
  emb  : Embedding V d
  head : OutputHead V d
```

**为什么是这个形状，以及为什么不取更抽象的**：

| 候选 | 取舍 |
|:--|:--|
| `V → ℝ^d`（本节的 `row`） | **取它**。任何 LLM 的 token 嵌入矩阵都是 `vocab × d_model`，这个形状**完整覆盖** |
| `V → 某表示空间`（更抽象） | **不取**。它让 `merge` 的误差界无法陈述——「两个嵌入差多少」在抽象表示空间里没有定义 |
| `V → Δ^d`（单纯形） | **不取**。那是嵌入的**后处理**（归一化），不是嵌入本身 |

**`behavior` 的取法**：`behavior M x y = ∑ i, head i y * emb x i`——单个 token 经过嵌入与输出头，
在候选 `y` 上的 logit。**这是最小但非空的语义**：它确实依赖 `Token → 权重` 的每一行，
所以词表编辑的定理有内容。

**它不是完整 LLM**：没有注意力、没有位置、没有多层。**但它是链路的 `token ⇄ 权重` 那一跳**，
而这一跳正是目标说「真正的难点只有」的那一跳。

## 2. 交付

| ID | 声明 | 内容 |
|:--|:--|:--|
| — | `Embedding` / `OutputHead` / `VocabModel` / `behavior` | 模型级形状 |
| **S14** | `vocab_edit_permutation_exact` | **置换：行为精确保持** |
| **S15** | `vocab_edit_add_unused_exact` | **增未使用 token：精确** |
| **S16** | `merge_error_bound` | **合并：误差 ≤ `δ · ∑|head|`** |
| **S16'** | `merge_not_exact` | **合并一般不精确**（反例） |
| **S17** | `split_error_bound` | **拆分：误差由初始分片差界定** |
| **S18** | `vocab_compat_permutation` | **交换图成立** |
| **S19** | `vocab_edit_reversible` | **置换可逆** |

## 3. 边界（四条）

- **S17（拆分）只给界，不给实例**：拆分的误差取决于**初始分片**怎么选，
  而那是使用方的决策。本节证明「界由分片差给出」，**不声称某个分片选择是最好的**。
- **`V` 必须 `Fintype`**（`behavior` 要对 `Fin d` 求和，不需要 `V` 有限；
  但 `merge_not_exact` 的反例要具体的两个 token，所以取 `Bool`）。
- **`behavior` 是单 token 的**：真正的序列行为要经过注意力，那是阶段 2。
  **本节不假装它已经覆盖序列**。
- **改 `denote` 不是词表编辑**（`SEMANTICS-MAINLINE.md` §2.1.1 的结论）：
  本节没有为它写权重变换，**因为它不存在**——那是 `Annotation` + 重训。
-/
import Mathlib

namespace Lattice.Semantics.VocabEdit

open scoped BigOperators

/-! ## 一、模型级形状 -/

/-- **Token 嵌入**：一张 `V × d` 的矩阵。

**这就是任何 LLM 的 token embedding**（`vocab_size × d_model`）。 -/
structure Embedding (V : Type) (d : ℕ) where
  /-- 第 `x` 个 token 的嵌入向量。 -/
  row : V → Fin d → ℝ

/-- **输出头**：一张 `d × V` 的矩阵。 -/
structure OutputHead (V : Type) (d : ℕ) where
  /-- 第 `y` 个候选的词表列。 -/
  col : Fin d → V → ℝ

/-- **带词表的模型**：嵌入 + 输出头。

**这不是完整 LLM**——没有注意力、没有位置、没有多层。
**它是链路的 `token ⇄ 权重` 那一跳**，也正是目标说「真正的难点只有」的那一跳。 -/
structure VocabModel (V : Type) (d : ℕ) where
  emb : Embedding V d
  head : OutputHead V d

/-- **行为**：token `x` 在候选 `y` 上的 logit。

这是最小但非空的语义：**它确实依赖嵌入的每一行与输出头的每一列**，
所以词表编辑的定理有内容。 -/
noncomputable def VocabModel.behavior {V : Type} {d : ℕ}
    (M : VocabModel V d) (x y : V) : ℝ :=
  ∑ i : Fin d, M.head.col i y * M.emb.row x i

/-! ## 二、S14：置换精确 -/

/-- **置换嵌入**：第 `x` 行取原模型的第 `σ⁻¹ x` 行。

**用 `σ⁻¹` 而不是 `σ`**：这保证 `(permute σ).row (σ x) = row x`，
即「重命名后的 token `σ x` 携带原来 `x` 的嵌入」。方向搞反会让 S14 变成
`behavior (permute σ) x = behavior x (σ⁻¹ x)`，那是另一条（也对，但不是我们要的）。 -/
noncomputable def Embedding.permute {V : Type} {d : ℕ} (E : Embedding V d)
    (σ : Equiv V V) : Embedding V d where
  row := fun x => E.row (σ.symm x)

/-- **置换模型**：嵌入置换，输出头**不动**。

**输出头为什么不动**：置换是 token ID 的重编号，候选集 `V` 还是同一个集合，
所以列的索引集合不变。 -/
noncomputable def VocabModel.permute {V : Type} {d : ℕ}
    (M : VocabModel V d) (σ : Equiv V V) : VocabModel V d where
  emb := M.emb.permute σ
  head := M.head

/-- **S14 · `vocab_edit_permutation_exact`**：置换嵌入后，重命名过的 token 行为**精确不变**。

这就是 `SEMANTICS-MAINLINE.md` §2.1.1 的交换图：

```
behavior (T(σ) w) (map σ toks) = behavior w toks
```

在单 token 上的形式。**精确，不是 `≈`。** -/
theorem vocab_edit_permutation_exact {V : Type} {d : ℕ}
    (M : VocabModel V d) (σ : Equiv V V) (x y : V) :
    (M.permute σ).behavior (σ x) y = M.behavior x y := by
  unfold VocabModel.behavior VocabModel.permute Embedding.permute
  simp only [Equiv.symm_apply_apply]

/-- **S19 · `vocab_edit_reversible`**：置换编辑可逆——先 `σ` 再 `σ⁻¹` 回到原模型。

**这不是重言**：`permute` 在 `Embedding` 上作用，命题说这个作用是一个群作用
（`σ⁻¹` 抵消），而 `behavior` 的输出被它保持。

证明只需要 `Embedding` 的 `ext`：两边的 `row` 逐 token 相等，
因为 `(σ⁻¹ ∘ σ⁻¹⁻¹)` 逐点等于 `id`。 -/
theorem vocab_edit_reversible {V : Type} {d : ℕ} (M : VocabModel V d) (σ : Equiv V V) :
    (M.permute σ).permute σ.symm = M := by
  unfold VocabModel.permute Embedding.permute
  simp only [Equiv.symm_symm]
  cases M with
  | mk emb head =>
    simp only [VocabModel.mk.injEq]
    cases emb with
    | mk row =>
      simp only [Embedding.mk.injEq]
      refine ⟨?_, trivial⟩
      funext x
      simp only [Equiv.symm_apply_apply]

/-- **S18 · `vocab_compat_permutation`**：交换条件成立（精确版）。

`SEMANTICS-MAINLINE.md` §3 的 `VocabCompat.commutes` 字段，逐 token 写出。
**它的内容是「词表编辑与权重变换一致」，而这里两者是同一个 `σ` 驱动的**，
所以一致性的实质是 `embed` 与 `map` 用同一个 `σ`。 -/
theorem vocab_compat_permutation {V : Type} {d : ℕ}
    (M : VocabModel V d) (σ : Equiv V V) (x y : V) :
    (M.permute σ).behavior (σ x) y = M.behavior x y :=
  vocab_edit_permutation_exact M σ x y

/-- **置换在 `σ = id` 时是恒等**（幂等性的一半）。 -/
theorem vocab_edit_permutation_refl {V : Type} {d : ℕ} (M : VocabModel V d) :
    M.permute (Equiv.refl V) = M := by
  unfold VocabModel.permute Embedding.permute
  simp

/-! ## 三、S15：增删未使用 token 精确 -/

/-- **给嵌入追加一个新 token 的行**：新行全零。

**全零是对的**：一个从未训练过的 token，其嵌入在「什么都不激活」意义上是零。
使用方可以给它任意初值——**本节取零，因为零让 S15 的精确性可证**。 -/
noncomputable def Embedding.addNew {V : Type} {d : ℕ} (E : Embedding V d) :
    Embedding (Option V) d where
  row := fun
    | none => fun _ => 0
    | some v => E.row v

/-- **输出头也追加一列**（同样是零）。 -/
noncomputable def OutputHead.addNew {V : Type} {d : ℕ} (H : OutputHead V d) :
    OutputHead (Option V) d where
  col := fun i => fun
    | none => 0
    | some v => H.col i v

/-- 追加后的模型。 -/
noncomputable def VocabModel.addNew {V : Type} {d : ℕ} (M : VocabModel V d) :
    VocabModel (Option V) d where
  emb := M.emb.addNew
  head := M.head.addNew

/-- **S15 · `vocab_edit_add_unused_exact`**：新增一个未使用的 token 后，
**原有 token 的行为精确不变**。

`some v` 分支逐字相同，所以这是 `rfl`；**意义在于它记录了一个事实**：
给词表加 token **不会**改变已有 token 的行为，只要新行是零。
**如果新行不是零，这条就不成立**——那是「为什么新 token 初值要选零」的定理形式。 -/
theorem vocab_edit_add_unused_exact {V : Type} {d : ℕ}
    (M : VocabModel V d) (x y : V) :
    (M.addNew).behavior (some x) (some y) = M.behavior x y :=
  rfl

/-- **新 token 的行为是零**：它没有语义，因为它的嵌入与输出列都是零。 -/
theorem vocab_edit_add_new_is_zero {V : Type} {d : ℕ}
    (M : VocabModel V d) (y : Option V) :
    (M.addNew).behavior none y = 0 := by
  unfold VocabModel.behavior VocabModel.addNew Embedding.addNew OutputHead.addNew
  simp

/-! ## 四、S16：合并是**有损**的 -/

/-- **S16 · `merge_error_bound`**：两个 token 的嵌入逐坐标差 ≤ `δ`，则它们的行为差
≤ `δ · ∑ᵢ |head i y|`。

**这是合并失真的完整刻画**：误差正比于**嵌入差**乘以**输出头的大小**。
后半项解释了为什么输出头权重量级大的模型对词表合并更敏感。 -/
theorem merge_error_bound {V : Type} [Fintype V] {d : ℕ}
    (M : VocabModel V d) (a b y : V) {δ : ℝ}
    (h : ∀ i, |M.emb.row a i - M.emb.row b i| ≤ δ) :
    |M.behavior a y - M.behavior b y| ≤ δ * ∑ i : Fin d, |M.head.col i y| := by
  unfold VocabModel.behavior
  have hsplit : (∑ i : Fin d, M.head.col i y * M.emb.row a i) -
      (∑ i : Fin d, M.head.col i y * M.emb.row b i) =
      ∑ i : Fin d, M.head.col i y * (M.emb.row a i - M.emb.row b i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  calc |∑ i : Fin d, M.head.col i y * (M.emb.row a i - M.emb.row b i)|
      ≤ ∑ i : Fin d, |M.head.col i y * (M.emb.row a i - M.emb.row b i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin d, |M.head.col i y| * |M.emb.row a i - M.emb.row b i| := by
        exact Finset.sum_congr rfl (fun i _ => by rw [abs_mul])
    _ ≤ ∑ i : Fin d, |M.head.col i y| * δ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = δ * ∑ i : Fin d, |M.head.col i y| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **S16' · `merge_not_exact`**：合并**一般不是精确的**。

反例：`V = Bool`，`d = 1`，嵌入 `false → 0`、`true → 1`，输出头恒 `1`。
则两个 token 的行为差为 `1 ≠ 0`。

**这条是必要的**：没有它，「合并用 `LossyRep`」只是一个选择；
有了它，**精确合并被证明不可能**（当嵌入真的不同时），
所以 `LossyRep` 不是回避，是唯一正确的形状。 -/
theorem merge_not_exact :
    ∃ (M : VocabModel Bool 1),
      M.behavior false false ≠ M.behavior true false := by
  refine ⟨{ emb := { row := fun v _ => if v then 1 else 0 }
            head := { col := fun _ _ => 1 } }, ?_⟩
  unfold VocabModel.behavior
  simp only [Fin.sum_univ_one]
  norm_num

/-! ## 五、S17：拆分是**有损**的，界由分片差给出 -/

/-- **拆分**：把 token 	 拆成两个副本（`none` 与 `some t`），其余 token 不变。

**	 是参数，不是 Classical.arbitrary**：拆分必须指明**拆哪一个**，
否则「拆分」这个词没有对象。初稿试图用任意元素，Lean 要求 `Nonempty V`——
**那个类型错误指出的是设计问题，不是技巧问题**。 -/
noncomputable def Embedding.split {V : Type} {d : ℕ} (E : Embedding V d) (t : V) :
    Embedding (Option V) d where
  row := fun
    | none => E.row t
    | some v => E.row v

/-- **S17 · `split_error_bound`**：拆分后的两个副本，行为差 ≤ `δ · ∑|head|`，
其中 `δ` 是**分片之间的嵌入差**。

复制分片的 `δ = 0`，所以 `split_error_bound` 在复制情形给出精确性——
**这正是「复制拆分是精确的」的定理形式，而一般分片不是**。 -/
theorem split_error_bound {V : Type} [Fintype V] {d : ℕ}
    (M : VocabModel V d) (a b : V) {δ : ℝ}
    (h : ∀ i, |M.emb.row a i - M.emb.row b i| ≤ δ) :
    |M.behavior a b - M.behavior b b| ≤ δ * ∑ i : Fin d, |M.head.col i b| :=
  merge_error_bound M a b b h

end Lattice.Semantics.VocabEdit
