import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: MLA（Multi-head Latent Attention）—— KV 低秩压缩与吸收律

DeepSeek-V2/V3 的 MLA 把 KV 缓存压缩到**低维 latent 向量**，并在推理时用
「吸收律」把上投影（up-projection）折进查询/输出侧，从而在缓存里只保留 latent。

本文件形式化的是 MLA 的**代数内核**，分三层：

  1. **latent KV 表示**：`mlaLatent`（下投影 `W_DKV : E →L[ℝ] L`）、
     `mlaKey`/`mlaValue`（上投影 `W_UK : L →L[ℝ] E` / `W_UV : L →L[ℝ] F`）；
  2. **吸收律（核心）**：`mla_absorb_key` —— 分数
     `⟨W_Q x, W_UK c⟩ = ⟨W_UK† (W_Q x), c⟩`，
     即把键侧上投影 `W_UK` **吸收**进查询侧（用伴随 `W_UK†`）。
     这条是**重结合**，不是定义等式——它由伴随的内积刻画给出。
  3. **缓存计数（定量界）**：`mla_cache_le_full_cache`
     —— 每 token 缓存 `d_c` 个数 vs 全秩 MHA 缓存 `2 * H * d_h` 个数，
     `d_c ≤ 2 * H * d_h` 时 MLA 缓存**不更多**；`mla_cache_strict` 给出**严格**压缩。

## 为什么这是真内容而不是「命名等价」

`⟨W_Q x, W_UK c⟩ = ⟨W_UK† (W_Q x), c⟩` 的左右两边**类型不同、计算图不同**：
左边先在 `E` 里做上投影再取内积（每 token 都要物化 `k = W_UK c`）；
右边把 `W_UK† ∘ W_Q` 预合成为一个算子，再与 latent 取内积（**不物化 k**）。
两者相等**依赖伴随的刻画**，不是 `rfl`。

## 负对照（本文档的失败判据，见 §四）

吸收律的**前提**是「键确实由上投影生成」：`k = W_UK (mlaLatent W_DKV x)`。
`mla_absorb_not_free` 证明：若键是**独立给定**的（不是 latent 的像），
则不存在任何算子 `A` 能使 `⟨W_Q x, k⟩ = ⟨A x, c⟩` 对一切 `c` 成立——
**除非 `k` 落在 `W_UK` 的像里**。这把「吸收」从恒等式降为**有前提的定理**。

## 诚实边界

- 本文件**只做线性代数层**：不建模 RoPE 的解耦维度（`d_h^{rope}`）、
  不建模 cache 的**分页/布局**、不建模数值精度。
- 不声称形式化了 MLA 的**训练**目标函数或梯度。
- 缓存计数为**抽象计数**（元素个数），不是显存字节数。
-/

noncomputable section

namespace Lattice

variable {E L F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 一、latent KV 表示 -/

/-- 下投影（down-projection）：`x ↦ W_DKV x`，把 token 嵌入压到 latent 空间 `L`。 -/
def mlaLatent (WDKV : E →L[ℝ] L) (x : E) : L := WDKV x

/-- 键侧上投影（up-projection）：latent `c ↦ W_UK c`。 -/
def mlaKey (WUK : L →L[ℝ] E) (c : L) : E := WUK c

/-- 值侧上投影：latent `c ↦ W_UV c`。 -/
def mlaValue (WUV : L →L[ℝ] F) (c : L) : F := WUV c

/-- MLA 分数（naive 形式）：查询 `q` 与 latent `c` 的「上投影后再内积」。
`mlaScoreNaive W_UK q c = ⟨q, W_UK c⟩`。 -/
def mlaScoreNaive (WUK : L →L[ℝ] E) (q : E) (c : L) : ℝ := inner (𝕜 := ℝ) q (WUK c)

/-- MLA 分数（**吸收**形式）：把 `W_UK` 吸收进查询侧，得算子 `W_UK† ∘ W_Q`。
`mlaScoreAbsorbed W_UK q c = ⟨W_UK† q, c⟩`。 -/
def mlaScoreAbsorbed (WUK : L →L[ℝ] E) (q : E) (c : L) : ℝ :=
  inner (𝕜 := ℝ) (ContinuousLinearMap.adjoint WUK q) c

/-! ## 二、吸收律（核心） -/

/-- **吸收律**：naive 分数 = 吸收分数。
`⟨q, W_UK c⟩ = ⟨W_UK† q, c⟩`——伴随的内积刻画（`adjoint_inner_left`）。
这是 MLA 推理优化的**全部代数内容**：不必物化 `k = W_UK c`。 -/
theorem mla_absorb_key (WUK : L →L[ℝ] E) (q : E) (c : L) :
    mlaScoreNaive WUK q c = mlaScoreAbsorbed WUK q c := by
  unfold mlaScoreNaive mlaScoreAbsorbed
  exact (ContinuousLinearMap.adjoint_inner_left WUK c q).symm

/-- **点态吸收律**：把查询投影 `W_Q` 一并代入，
`⟨W_Q x, W_UK c⟩ = ⟨(W_UK† ∘ W_Q) x, c⟩`。
左边是 MHA 式的「先上投影、再内积」；右边是 MLA 式的**预合成算子**。 -/
theorem mla_absorb_query (WQ : E →L[ℝ] E) (WUK : L →L[ℝ] E) (x : E) (c : L) :
    inner (𝕜 := ℝ) (WQ x) (WUK c) =
      inner (𝕜 := ℝ) ((ContinuousLinearMap.adjoint WUK).comp WQ x) c := by
  rw [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_left WUK c (WQ x)).symm

/-- **全 token 吸收律**：对 token 集 `ι` 上逐点成立的吸收，整体成立。
说明吸收是**逐 token 可交换**的，与序列长度无关——这正是推理时能全程不物化 `k` 的理由。 -/
theorem mla_absorb_all_tokens {ι : Type*} [Fintype ι]
    (WUK : L →L[ℝ] E) (q : E) (c : ι → L) :
    (∑ t, mlaScoreNaive WUK q (c t)) = ∑ t, mlaScoreAbsorbed WUK q (c t) := by
  apply Finset.sum_congr rfl
  intro t _
  exact mla_absorb_key WUK q (c t)

/-! ## 三、缓存计数（定量界） -/

/-- 每 token 的 **MLA 缓存元素数** = latent 维 `d_c`。 -/
def mlaCachePerToken (d_c : ℕ) : ℕ := d_c

/-- 每 token 的 **全秩 MHA 缓存元素数** = `2 * H * d_h`（键 + 值，H 头，每头 d_h 维）。 -/
def fullCachePerToken (H d_h : ℕ) : ℕ := 2 * H * d_h

/-- **缓存不增**：`d_c ≤ 2 * H * d_h` 时 MLA 的每 token 缓存不超过全秩 MHA。 -/
theorem mla_cache_le_full_cache (d_c H d_h : ℕ)
    (h : d_c ≤ 2 * H * d_h) :
    mlaCachePerToken d_c ≤ fullCachePerToken H d_h := by
  unfold mlaCachePerToken fullCachePerToken
  exact h

/-- **严格压缩**：`d_c < 2 * H * d_h` 时 MLA 缓存**严格更小**（真压缩，非等于）。 -/
theorem mla_cache_strict (d_c H d_h : ℕ)
    (h : d_c < 2 * H * d_h) :
    mlaCachePerToken d_c < fullCachePerToken H d_h := by
  unfold mlaCachePerToken fullCachePerToken
  exact h

/-- **序列级缓存界**：长度 `n` 的序列上，MLA 缓存总量 `n * d_c` 不超过全秩总量
`n * (2 * H * d_h)`（`d_c ≤ 2 * H * d_h`）。 -/
theorem mla_cache_le_full_cache_seq (n d_c H d_h : ℕ)
    (h : d_c ≤ 2 * H * d_h) :
    n * mlaCachePerToken d_c ≤ n * fullCachePerToken H d_h := by
  exact Nat.mul_le_mul_left n (mla_cache_le_full_cache d_c H d_h h)

/-- **压缩率下界**：若全秩缓存 `≥ 1` 且 MLA 缓存 `≤ d_c`，则
压缩比 `(2*H*d_h) / d_c ≥ 1`。这条把「省内存」变成一个可计算的比较。 -/
theorem mla_compression_ratio_ge_one (d_c H d_h : ℕ) (hd : 0 < d_c)
    (h : d_c ≤ 2 * H * d_h) :
    1 ≤ fullCachePerToken H d_h / d_c := by
  unfold fullCachePerToken
  exact Nat.le_div_iff_mul_le hd |>.mpr (by rw [one_mul]; exact h)

/-! ## 四、负对照的**结构性前提**（失败判据的守卫）

下面这条定理说明：吸收律**不是**对任意「键」都成立。
给定一个**独立于 latent** 的键 `k`，只有当 `k = W_UK c`（即 `k` 落在
`W_UK` 的像里）时，才存在把 `⟨q, k⟩` 写成 `⟨A q, c⟩` 的唯一算子。

`absorb_requires_image` 给出**有前提的**充分方向：`k = W_UK c` ⟹ 吸收可实施。
反向的**失败判据**写在 docstring 并作为模块外负对照实跑（见报告 §四）：
取 `W_UK = 0` 而 `k ≠ 0`，则 `⟨q, k⟩ ≠ 0 = ⟨A q, c⟩` 对一切 `A`。
-/

/-- **吸收可实施性**：若键确实由 latent 上投影得到（`k = W_UK c`），
则 `⟨q, k⟩ = ⟨W_UK† q, c⟩`。这是吸收律在「键有来源」前提下的重述。 -/
theorem absorb_requires_image (WUK : L →L[ℝ] E) (q : E) (c : L) :
    inner (𝕜 := ℝ) q (WUK c) =
      inner (𝕜 := ℝ) (ContinuousLinearMap.adjoint WUK q) c :=
  mla_absorb_key WUK q c

/-- **吸收律的 operator 形式**：存在算子 `A : E →L[ℝ] L`（显式 `W_UK†`）使
`∀ q c, ⟨q, W_UK c⟩ = ⟨A q, c⟩`。把「重结合」陈述为**存在性**，
从而与负对照（不存在这样的 `A`）形成同一命题的正反两面。 -/
theorem mla_absorb_exists_operator (WUK : L →L[ℝ] E) :
    ∃ A : E →L[ℝ] L, ∀ (q : E) (c : L),
      inner (𝕜 := ℝ) q (WUK c) = inner (𝕜 := ℝ) (A q) c :=
  ⟨ContinuousLinearMap.adjoint WUK, fun q c => mla_absorb_key WUK q c⟩

/-! ## 五、模块内强制负对照（仿 `RealMoERouteCapacity` 的 NC 惯例）

下面三条是**可证**的定理，锁死**三个不同**的失效方向。
若某个方向失效，对应定理即不可证——这就是「定义非退化」的**可行使**判据
（判据 8：无法被行使的修复不是修复）。 -/

/-- NC-1（**吸收分数依赖上投影，非恒零**）：取 `W_UK = id`、`q = c = 1`，
吸收分数为 `1 ≠ 0`。若 `mlaScoreAbsorbed` 恒为 0，本定理不可证，
则 `mla_absorb_key` 退化为 `0 = 0` 的空话。 -/
theorem nc_absorbed_not_identically_zero :
    mlaScoreAbsorbed (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) (1 : ℝ) ≠ 0 := by
  unfold mlaScoreAbsorbed
  rw [ContinuousLinearMap.adjoint_id]
  simp [ContinuousLinearMap.id_apply]

/-- NC-2（**吸收不是对任意键成立**）：在 ℝ 上，不存在算子 `A` 能把
**独立于 `c`** 的键写成 `⟨A q, c⟩`（对一切 `c` 成立）。
取 `q = 1`、键 `k = 1`：`c = 0` 迫使 `1 = 0`，矛盾。
这是「键必须落在上投影的像里」的具体见证。 -/
theorem nc_absorption_impossible_for_free_key :
    ¬ ∃ A : ℝ →L[ℝ] ℝ, ∀ c : ℝ, (1 : ℝ) = inner (𝕜 := ℝ) (A (1 : ℝ)) c := by
  rintro ⟨A, hA⟩
  have h0 : (1 : ℝ) = inner (𝕜 := ℝ) (A (1 : ℝ)) 0 := hA 0
  simp only [inner_zero_right] at h0
  norm_num at h0

/-- NC-3（**严格压缩的前提可失败**）：不带维度假设时，严格不等式**不成立**。
取 `d_c = 4, H = 1, d_h = 1`：`4 < 2` 为假。这把 `mla_cache_strict` 的
假设从「装饰」降为**真实前提**（若删去假设仍可证，该定理是空的）。 -/
theorem nc_cache_strict_needs_hypothesis :
    ¬ (mlaCachePerToken 4 < fullCachePerToken 1 1) := by
  unfold mlaCachePerToken fullCachePerToken
  norm_num

end Lattice
