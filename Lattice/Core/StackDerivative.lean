import Mathlib
import Lattice.Core.Net

/-!
# `Lattice.Core.StackDerivative` — **`affineAct` 对输入的导数（`P2-02` 的第一级）**

## 为什么从这里开始

`P2-02` 要的是 `netLoss` 对**参数**的梯度。**而参数只通过 `netAct` 进入损失**，所以第一级是
**「单层的 `affineAct` 对输入可微」**——**而它的导数是 `W` 本身（作为连续线性映射）。**

## 形状

`affineAct L x = fun j => (∑ i, L.W i j * x i) + L.b j`。
**它是「线性部分 + 常数」**：

```lean
affineCLM L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)   -- 线性部分
affineAct L x = affineCLM L x + L.b            -- 等式
HasFDerivAt (affineAct L) (affineCLM L) x      -- 导数
```

⚠ **`x` 是【输入】，不是参数。** **本文件证的是「对输入」，而 `P2-02` 真正要的是「对 `(W, b)`」**——
**两者的线性映射不同（对输入是 `W` 作用，对 `(W,b)` 是 `x` 作用），所以这是第一级而不是全部。**

⚠ **`relu` 的折点**：本文件**只处理仿射层**，所以不受 `relu` 在 `0` 处不可导的影响。
**但任何把 `netAct` 当成「处处可微」的陈述都必须在 `relu` 的折点外成立**——**那条前提还没有写。**
-/

namespace Lattice.Core

/-- **单层的线性部分**：`x ↦ fun j => ∑ i, W i j * x i`。

**作为连续线性映射**——连续性来自「有限个「常数乘坐标投影」之和」。 -/
noncomputable def affineCLM {n : ℕ} (L : AffineLayer (Fin n)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) where
  toFun := fun x j => ∑ i, L.W i j * x i
  map_add' := by
    intro x y
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  cont := by
    fun_prop

/-- **`affineAct` 是「线性部分 + 偏置」**——`affineCLM` 之所以有用，全靠这条等式。 -/
theorem affineAct_eq_affineCLM_add {n : ℕ} (L : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    affineAct L x = affineCLM L x + L.b :=
  rfl

/-- ⭐ **`affineAct L` 对输入可微**，导数是 `affineCLM L`。

**由「线性映射的导数 + 加常数」得到**，而 `affineAct` 按定义就是那两个的复合。 -/
theorem hasFDerivAt_affineAct {n : ℕ} (L : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    HasFDerivAt (affineAct L) (affineCLM L) x := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => affineCLM L y + L.b) (affineCLM L) x :=
    (affineCLM L).hasFDerivAt.add_const (L.b)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => (affineAct_eq_affineCLM_add L y).symm))

/-! ## ⭐⭐ 对**参数** `(W, b)` 的可微性——`P2-02` 真正需要的那一级

上一节给的是对**输入** `x` 的导数（导数是 `W` 作用）。**本节给对参数 `(W, b)` 的**，那时 `x` 是常数。

## 为什么不手工构造那条连续线性映射

**我试过。** `paramsCLM x : ((Fin n → Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ)` 的
`map_add'`／`map_smul'` 是「有限和的分配律」，而 `Finset.sum_add_distrib` 在这个形状下不出手，
`ring`／`ring_nf` 也无法在 `∑` 内部按索引对齐——**三次尝试都失败在同一处。**

**⇒ 所以本文件不手工构造 CLM，而是证【可微性】。** `fderiv ℝ f p` 就是那条线性映射，
**而 mathlib 的 `fderiv` 会自动归一化它**——**消费者拿到的东西完全一样，而证明只需一行 `fun_prop`。**

⚠ **这不是让步**：`DifferentiableAt` + `fderiv` 是 mathlib 里**标准**的用法，
**而手工构造 CLM 只在需要【显式】线性映射的形状时才必要**（例如要拿它的算子范数）。
**若将来需要算子范数，那时再构造，并且应当先把 `map_add'` 抽成一条独立的引理。**

## 定义域为什么是 `(Fin n → Fin n → ℝ) × (Fin n → ℝ)` 而不是 `stackParams 1 n`

`stackParams 1 n = Fin 1 → (Fin n → Fin n → ℝ) × (Fin n → ℝ)`。**`Fin 1` 只有一个元素，所以两者等价**，
**但直接写 `Prod` 少一层 `Fin 1` 的搬运**，而 `Prod` 的实例都是现成的。**`stackParams k n` 在 `k ≥ 2` 时才真正必要。** -/

/-- **参数空间**：`W : Fin n → Fin n → ℝ` 与 `b : Fin n → ℝ` 的积。

**这是「单层参数」的赋范向量空间**——`Prod` 与 `Pi` 的实例自动给出，不需要手写代数。 -/
abbrev singleParams (n : ℕ) : Type := (Fin n → Fin n → ℝ) × (Fin n → ℝ)

/-- ⭐⭐ **`affineAct` 对参数可微**：`x` 固定时，`(W, b) ↦ affineAct ⟨W, b⟩ x` 在任意点可微。

**证明是 `simp only [affineAct]` 加 `fun_prop`**——**后者处理「有限和 + 常数乘 + 加常数」这个形状**，
**而上一节已经证明它能处理同一类目标（那里的 `cont` 也是它关掉的）。**

**导数就是 `fderiv ℝ (fun p => affineAct ⟨p.1, p.2⟩ x) (W, b)`**，**不需要显式写出它。** -/
theorem differentiableAt_affineAct_params {n : ℕ} (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ
      (fun p : singleParams n => affineAct ⟨p.1, p.2⟩ x) (W, b) := by
  change DifferentiableAt ℝ
    (fun p : singleParams n => fun j => (∑ i, p.1 i j * x i) + p.2 j) (W, b)
  fun_prop

/-- **`affineAct` 对参数的导数存在**，且它就是 `fderiv`。

**这一条是给消费者的句柄**：它把 `DifferentiableAt` 变成 `HasFDerivAt`，
**而 `fderiv` 就是那个线性映射。** -/
theorem hasFDerivAt_affineAct_params {n : ℕ} (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun p : singleParams n => affineAct ⟨p.1, p.2⟩ x)
      (fderiv ℝ (fun p : singleParams n => affineAct ⟨p.1, p.2⟩ x) (W, b)) (W, b) :=
  (differentiableAt_affineAct_params W b x).hasFDerivAt

/-! ## ⭐⭐ `netActN`：`Fin k` 上的递归栈求值——`foldl` 的可微替代

## 为什么需要它

`netAct ls x = ls.foldl (fun acc L => affineAct L acc) x`。**`List.foldl` 在 mathlib 里没有可微性引理**，
**所以「`k` 层栈对参数可微」不能靠一条 `foldl` 的定理，必须对 `k` 归纳。**

**而对 `k` 归纳需要一条【在 `ℕ` 上递归】的求值函数**——**那就是 `netActN`。**

## ⚠ 递归方向必须与 `List.ofFn_succ` 一致

**第一次我写的是「末层作用于前 `k` 层的结果」**（从**尾**剥离），
**而 `List.ofFn_succ` 拆的是【首元素】**（`List.ofFn f = f 0 :: List.ofFn (fun i => f i.succ)`）。
**两者方向相反，所以那条等式证不出来。**

**⇒ `netActN` 从【头】剥离**：先作用 `p 0`，再递归到 `p ∘ succ`。
**那也正是 `foldl` 的自然顺序**，所以等式与 `List.foldl_cons` 直接对齐。 -/

/-- **`k` 层仿射栈的递归求值（从头剥离）**：`k = 0` 是恒等；
`k + 1` 是先作用首层，再递归到其余。 -/
noncomputable def netActN (n : ℕ) : (k : ℕ) → (Fin k → AffineLayer (Fin n)) → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, x => x
  | k + 1, p, x => netActN n k (fun i => p i.succ) (affineAct (p 0) x)

/-- **`netActN` 在 `k = 0` 处是恒等。** -/
theorem netActN_zero {n : ℕ} (p : Fin 0 → AffineLayer (Fin n)) (x : Fin n → ℝ) :
    netActN n 0 p x = x :=
  rfl

/-- **`netActN` 的递归步**：先作用首层。 -/
theorem netActN_succ {k n : ℕ} (p : Fin (k + 1) → AffineLayer (Fin n)) (x : Fin n → ℝ) :
    netActN n (k + 1) p x
      = netActN n k (fun i => p i.succ) (affineAct (p 0) x) :=
  rfl

/-- ⭐ **`netActN` 就是 `netAct`（经 `List.ofFn`）**——**这条等式让 `netActN` 上的结论能搬到 `netAct` 上。**

**证明对 `k` 归纳**：`k = 0` 时 `netAct [] x = x`；`k + 1` 时用 `List.ofFn_succ` 拆出首元素，
再用 `List.foldl_cons`（`foldl` 的首步）。

⚠ **归纳假设 `ih` 的第一个参数是 `p`**（因为 `p` 是定理的显式参数），所以 `rw` 要写成 `ih (fun i => p i.succ)`。 -/
theorem netActN_eq_netAct {k n : ℕ} (p : Fin k → AffineLayer (Fin n)) (x : Fin n → ℝ) :
    netActN n k p x = netAct (List.ofFn p) x := by
  induction k generalizing x with
  | zero =>
      simp only [netActN_zero, netAct, List.ofFn_zero, List.foldl_nil]
  | succ k ih =>
      rw [netActN_succ, ih (fun i : Fin k => p i.succ)]
      simp only [netAct, List.ofFn_succ, List.foldl_cons]

/-! ## ⭐⭐ `netActN` 对输入可微——**按 `k` 归纳**

## 为什么这里是 `x` 而不是参数

**参数侧（`singleParams k n = Fin k → (W, b)`）的可微性要更复杂的形状**：需要 `Fin k →` 上的 `fderiv`
与逐层的 `HasFDerivAt.comp`，**而那要先把「第 `i` 层只依赖 `q i`」这件事显式化**——**那是下一轮。**

**本节做的是【输入侧】，而它的归纳结构干净得多**：

```
netActN n (k+1) p y = netActN n k (p ∘ succ) (affineAct (p 0) y)
```

⇒ **它是「单层 `affineAct (p 0)`」与「前 `k` 层」的复合**，所以归纳步就是 `DifferentiableAt.comp`。

## 为什么必须 `∀` 在陈述里

**归纳时 `p` 会变成 `p ∘ succ`**，所以 `p` 不能固定在定理的 binder 上——
**陈述写成 `∀ k p x, ...`，归纳对 `k` 做，`p`/`x` 在每一步重新引入。** -/

/-- ⭐⭐ **`k` 层栈对输入可微**：对任意层表 `p` 与任意输入 `x`。

**证明对 `k` 归纳**：`k = 0` 是恒等（`differentiableAt_id`）；
`k + 1` 用 `netActN_succ` 把函数改写成复合，再用 `DifferentiableAt.comp` 拼「首层」与「其余」。 -/
theorem differentiableAt_netActN {n : ℕ} :
    ∀ (k : ℕ) (p : Fin k → AffineLayer (Fin n)) (x : Fin n → ℝ),
      DifferentiableAt ℝ (netActN n k p) x
  | 0, p, x => by
      have hfun : netActN n 0 p = id := by
        funext y
        exact netActN_zero p y
      rw [hfun]
      exact differentiableAt_id
  | k + 1, p, x => by
      have hfun : netActN n (k + 1) p
          = fun y => netActN n k (fun i => p i.succ) (affineAct (p 0) y) := by
        funext y
        exact netActN_succ p y
      rw [hfun]
      exact (differentiableAt_netActN k (fun i => p i.succ) (affineAct (p 0) x)).comp x
        (hasFDerivAt_affineAct (p 0) x).differentiableAt

/-- ⭐⭐ **`netAct` 对输入可微**——**把上一节的结论搬到 `netAct` 上**。

**桥就是 `netActN_eq_netAct`（第 108 轮）**：`netAct (List.ofFn p) x = netActN n k p x`，
所以 `netAct` 在层表 `List.ofFn p` 处的可微性就是 `netActN` 的可微性。 -/
theorem differentiableAt_netAct_ofFn {k n : ℕ} (p : Fin k → AffineLayer (Fin n))
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ (fun y => netAct (List.ofFn p) y) x := by
  have hfun : (fun y => netAct (List.ofFn p) y) = netActN n k p := by
    funext y
    exact (netActN_eq_netAct p y).symm
  rw [hfun]
  exact differentiableAt_netActN k p x

/-- **`netAct` 在 `Fin k` 层表上的导数存在**——`HasFDerivAt` 的句柄，由 `fderiv` 给出。 -/
theorem hasFDerivAt_netAct_ofFn {k n : ℕ} (p : Fin k → AffineLayer (Fin n))
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y => netAct (List.ofFn p) y)
      (fderiv ℝ (fun y => netAct (List.ofFn p) y) x) x :=
  (differentiableAt_netAct_ofFn p x).hasFDerivAt

/-! ## ⭐⭐⭐ 联合可微性：`(参数, 输入) ↦ netActN`

## 为什么必须是联合的

第 110 轮我试图由「对参数可微」（固定 `x`）与「对输入可微」（固定层表）复合成
`q' ↦ netActN n k (pack q') x`，**失败了**：归纳步里 `netActN` 的第二个参数是
`affineAct (q' 0) x`，**它随 `q'` 变**，而「固定 `x` 的可微性」在 `x` 变了之后不能直接用。

**⇒ 需要的是一条【两个分量都动】的可微性**：

```lean
fun r : (Fin k → singleParams n) × (Fin n → ℝ) => netActN n k (packLayers r.1) r.2
```

**在 `(q, x)` 处可微**。**有了它，参数侧（固定 `x`）与输入侧（固定层表）都只是复合特例。**

## 分层

1. **`packLayers`**：把 `Fin k → singleParams n` 装成 `Fin k → AffineLayer (Fin n)`——**一处定义，处处引用**；
2. **`differentiableAt_affineAct_joint`**：单层对 `(W, b, x)` 三者联合可微（`change` 展开 + `fun_prop`）；
3. **`differentiableAt_netActN_joint`**：全栈的联合可微性（对 `k` 归纳）；
4. **两条推论**：参数侧与输入侧的分别可微性。 -/

/-- **把逐层参数 `(W, b)` 装成 `AffineLayer`**——`singleParams n` 的两个分量恰好就是 `AffineLayer` 的两个字段。 -/
noncomputable def packLayers {k n : ℕ} (q : Fin k → singleParams n) :
    Fin k → AffineLayer (Fin n) :=
  fun i => ⟨(q i).1, (q i).2⟩

/-- **`packLayers` 的逐点等式**——避免每次都要展开那个 `fun`。 -/
theorem packLayers_apply {k n : ℕ} (q : Fin k → singleParams n) (i : Fin k) :
    packLayers q i = ⟨(q i).1, (q i).2⟩ :=
  rfl

/-- ⭐⭐ **单层对 `(W, b, x)` 联合可微**。

**`change` 把 `affineAct` 展开成「有限和 + 常数」之后，`fun_prop` 一步收掉**——
**与第 105／107 轮同一形状，只是这次 `W`、`b`、`x` 三者同时是变量。** -/
theorem differentiableAt_affineAct_joint {n : ℕ} (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ
      (fun r : singleParams n × (Fin n → ℝ) =>
        affineAct (⟨r.1.1, r.1.2⟩ : AffineLayer (Fin n)) r.2)
      ((W, b), x) := by
  change DifferentiableAt ℝ
    (fun r : singleParams n × (Fin n → ℝ) =>
      fun j => (∑ i, r.1.1 i j * r.2 i) + r.1.2 j) ((W, b), x)
  fun_prop

/-- ⭐⭐⭐ **全栈对 `(参数, 输入)` 联合可微**——`P2-02` 的主引理。

**证明对 `k` 归纳**（`q` 与 `x` 在陈述里量化，所以每一步都能重新引入）：

- `k = 0`：`(q, x) ↦ x`，即第二投影，`fun_prop` 直接给；
- `k + 1`：用 `netActN_succ` 把函数改写成
  `r ↦ netActN n k (pack (r.1 ∘ succ)) (affineAct (⟨r.1 0⟩) r.2)`，
  **即「`r ↦ (r.1 ∘ succ, affineAct (⟨r.1 0⟩) r.2)`」与「归纳假设」的复合。**
  前者由 `DifferentiableAt.prod` 给出：第一分量 `fun_prop`，第二分量是
  `differentiableAt_affineAct_joint` 复合 `r ↦ (r.1 0, r.2)`。 -/
theorem differentiableAt_netActN_joint {n : ℕ} :
    ∀ (k : ℕ) (q : Fin k → singleParams n) (x : Fin n → ℝ),
      DifferentiableAt ℝ
        (fun r : (Fin k → singleParams n) × (Fin n → ℝ) => netActN n k (packLayers r.1) r.2)
        (q, x)
  | 0, q, x => by
      have hfun : (fun r : (Fin 0 → singleParams n) × (Fin n → ℝ) =>
          netActN n 0 (packLayers r.1) r.2) = fun r => r.2 := by
        funext r
        exact netActN_zero _ r.2
      rw [hfun]
      fun_prop
  | k + 1, q, x => by
      have hfun : (fun r : (Fin (k + 1) → singleParams n) × (Fin n → ℝ) =>
          netActN n (k + 1) (packLayers r.1) r.2)
          = fun r => netActN n k (packLayers (r.1 ∘ Fin.succ))
              (affineAct (⟨(r.1 0).1, (r.1 0).2⟩ : AffineLayer (Fin n)) r.2) := by
        funext r
        exact netActN_succ (packLayers r.1) r.2
      rw [hfun]
      -- the induction hypothesis, at the point the inner map sends `(q, x)` to
      have hIH := differentiableAt_netActN_joint k (q ∘ Fin.succ)
        (affineAct (⟨(q 0).1, (q 0).2⟩ : AffineLayer (Fin n)) x)
      -- the inner map `r ↦ (r.1 ∘ succ, affineAct (⟨r.1 0⟩) r.2)` is differentiable
      have hinner : DifferentiableAt ℝ
          (fun r : (Fin (k + 1) → singleParams n) × (Fin n → ℝ) =>
            (r.1 ∘ Fin.succ, affineAct (⟨(r.1 0).1, (r.1 0).2⟩ : AffineLayer (Fin n)) r.2))
          (q, x) := by
        refine DifferentiableAt.prod ?_ ?_
        · fun_prop
        · change DifferentiableAt ℝ
            (fun r : (Fin (k + 1) → singleParams n) × (Fin n → ℝ) =>
              fun j => (∑ i, (r.1 0).1 i j * r.2 i) + (r.1 0).2 j) (q, x)
          fun_prop
      exact hIH.comp (q, x) hinner

/-- **参数侧的 `HasFDerivAt` 句柄**——下游要用导数时从这里取。 -/
theorem hasFDerivAt_netActN_params {n : ℕ} (k : ℕ) (q : Fin k → singleParams n)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun q' : Fin k → singleParams n => netActN n k (packLayers q') x)
      (fderiv ℝ (fun q' : Fin k → singleParams n => netActN n k (packLayers q') x) q) q :=
  (DifferentiableAt.comp q (differentiableAt_netActN_joint k q x)
    ((differentiableAt_id : DifferentiableAt ℝ (fun q' : Fin k → singleParams n => q') q).prod
      (differentiableAt_const x))).hasFDerivAt

end Lattice.Core
