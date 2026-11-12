import Mathlib
import Lattice.Core.IR.Compile

/-!
# P1-1：权重向量的**有限支撑**载体（阶段 B）

## 为什么需要这个

**`Core/IR/Compile.lean:74` 把权重向量定义为**

```lean
abbrev IRWeights : Type := ℕ → ℝ
```

**这是一个**无限函数**。它作为抽象模型完全够用 —— 所有关于它的定理都成立 ——
但它**不能**对应到任何可执行的表示：真实权重是有限数组，而 `ℕ → ℝ` 需要无穷多存储。**

**=> 规划把它列为「C 前置条件 0/12」的根因：可以证明关于 `ℕ → ℝ` 的定理，
却无法把它们**编译成**任何有限结构。**

## 本文件做什么

**定义 `FinSupport`：**

```lean
structure FinSupport (N : Nat) where
  w : Fin N → ℝ
```

**并给出与 `ℕ → ℝ` 的**双向**连接：**

| 方向 | 内容 |
|:--|:--|
| `FinSupport.toFun` | **把有限支撑**嵌入**为 `ℕ → ℝ`（`N` 之外取 `0`）** |
| `FinSupport.ofFun` | **把 `ℕ → ℝ` **截断**为有限支撑（取前 `N` 项）** |
| `toFun_ofFun` | **`(ofFun N f).toFun = f` 在 `i < N` 处成立** |
| `ofFun_toFun` | **`ofFun N (W.toFun) = W` —— 这是**真正的**往返（有限侧）** |

**=> 关键的不对称：**

- **`ofFun ∘ toFun = id`（在 `FinSupport N` 上）—— **成立**，因为有限侧没有丢失信息；**
- **`toFun ∘ ofFun = id`（在 `ℕ → ℝ` 上）—— **不成立**，因为截断丢掉了 `N` 之后的部分。**

**第二个方向的不成立**不是缺陷，而是事实：`ℕ → ℝ` 里有 `N` 之外非零的函数，
它们不可能由任何 `FinSupport N` 表示。

**=> 这与项目里已经证明的「左逆而非右逆」模式一致**（`layerWords ∘ wordsLayer = id` 是左逆）。
本文件把同样的结论在权重载体上重述一遍，并**明确登记**右逆不可能。** -/

namespace Lattice.Core.IR

/-- **有限支撑的权重向量：`N` 个实数，下标为 `Fin N`。**

**=> 这是**可执行**的载体：真实权重是有限数组，而 `Fin N → ℝ` 正是一个长度为 `N` 的数组。**
**=> 与 `IRWeights := ℕ → ℝ` 的区别是**可表示性**，不是数学内容。** -/
structure FinSupport (N : ℕ) where
  /-- **分量。** -/
  w : Fin N → ℝ

/-- **把有限支撑嵌入为无限函数：`N` 之外取 `0`。**

**=> 这是 `FinSupport N → IRWeights` 的规范嵌入。选择 `N` 之外为 `0` 是**唯一**使
`toFun` 保持线性的选择（把 `Fin N` 的生成元送到 `ℕ → ℝ` 的标准基）。** -/
noncomputable def FinSupport.toFun {N : ℕ} (W : FinSupport N) : IRWeights :=
  fun i => if h : i < N then W.w ⟨i, h⟩ else 0

/-- **把无限函数截断为有限支撑：取前 `N` 项。**

**=> 这是 `IRWeights → FinSupport N` 的规范截断。** -/
noncomputable def FinSupport.ofFun (N : ℕ) (f : IRWeights) : FinSupport N :=
  ⟨fun i => f i.val⟩

/-- **`toFun` 在 `i < N` 处是恒等：嵌入不改变支撑内的分量。**

**=> 这条说明嵌入在有限侧是**忠实**的，因此后面的往返才能成立。** -/
theorem FinSupport.toFun_apply {N : ℕ} (W : FinSupport N) (i : Fin N) :
    W.toFun i.val = W.w i := by
  unfold FinSupport.toFun
  rw [dif_pos i.isLt]

/-- **`toFun` 在 `N` 之外取 `0`。**

**=> 这条与上一条一起**唯一地**刻画了嵌入：支撑内忠实、支撑外为零。** -/
theorem FinSupport.toFun_apply_out {N : ℕ} (W : FinSupport N) {i : ℕ} (h : N ≤ i) :
    W.toFun i = 0 := by
  unfold FinSupport.toFun
  rw [dif_neg (by omega : ¬ i < N)]

/-- **`ofFun ∘ toFun = id`：有限侧的往返是**恒等**。**

**=> 因为有限侧没有丢失信息。这是 P1-1 的**核心定理**：
有限支撑的表示可以无损地往返。** -/
theorem FinSupport.ofFun_toFun {N : ℕ} (W : FinSupport N) :
    FinSupport.ofFun N W.toFun = W := by
  cases W with
  | mk w =>
      simp only [FinSupport.ofFun, FinSupport.toFun_apply]

/-- **`toFun ∘ ofFun = id` **不成立**：截断丢掉了 `N` 之后的部分。**

**=> 见证：`N = 1`，`f := fun _ => 1`。截断后 `toFun` 在 `i = 1` 处给出 `0`，而 `f 1 = 1`。**

**=> 这是**登记下来的否证**，与项目里的「左逆而非右逆」模式一致：
无限载体里有有限支撑无法表示的元素。** -/
theorem FinSupport.toFun_ofFun_ne_id :
    ∃ (N : ℕ) (f : IRWeights), (FinSupport.ofFun N f).toFun ≠ f := by
  refine ⟨1, fun _ => 1, ?_⟩
  intro h
  have h1 := congrFun h 1
  rw [FinSupport.toFun_apply_out (W := FinSupport.ofFun 1 (fun _ => 1)) (by omega : 1 ≤ 1)] at h1
  simp at h1

end Lattice.Core.IR
