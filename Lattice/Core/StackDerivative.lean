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

end Lattice.Core
