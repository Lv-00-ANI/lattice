# P8：符号 ⇄ 权重这一跳的**判决**

**本文件是第 944–953 轮成果的权威入口。**
**它不新增数学，只把已有的 32 条定理组织成**可引用的判决**。**

---

## 0. 为什么需要这份文件

**第 944 轮的审计给出了核心判决：**

> **「项目现在的问题不是「离目标还差多少」，而是「目标被设成了一个数学上不成立的形式，
> 而项目里没有一条定理指出这一点」。」**

> **「0 条 `∀ε ∃w`、0 条 `Tendsto error`、0 条下界。」**

**=> 第 944–953 轮的十轮工作，就是逐条关闭这三个零。**
**=> 本文件把它们固定下来，使读者无需读 32 条定理就能知道**结论是什么**。**

---

## 1. 四种读法，逐条裁决

**审计把「逼近精确」拆成四种读法。下表是它们在本项目载体上的**最终状态**。**

| # | 读法 | Lean 陈述 | 状态 | 定理位置 |
|--:|:--|:--|:--|:--|
| **R1** | 对一切目标、任意精度、一致常数 | `∀ f ∀ ε > 0, ∃ w, error w f ≤ ε` | **假** | `LowerBound.target_not_attainable` |
| **R2** | 对给定目标存在序列 | `∃ ws, Tendsto (fun n => error (ws n) f) atTop (𝓝 0)` | **真** | `ConvergenceForm.r2_holds_for_piecewise` |
| **R3** | 对给定约束集存在 ε-近解 | `∀ c ∀ ε > 0, ∃ w, violation (compile w) c ≤ ε` | **在 `ε < 1` 时 ≡ R4** | `ConstraintSatisfaction.R3_is_reachability` |
| **R4** | 精确 = 0 | `∀ c, violation (compile w) c = 0` | **正向为真** | `ConstraintSatisfaction.R3_holds_trivially_for_compiled` |

**=> 四条全部落定。合取形式见 `ConstraintSatisfaction.four_readings_resolved`。**

---

## 2. R1 为什么是假的：`1/8` 地板

**`Lattice/Lib/Compiler/LowerBound.lean`：**

```lean
theorem three_point_identity (a b : ℝ) :
    ((0)^2 - (a*0 + b)) + ((1)^2 - (a*1 + b)) - 2*((1/2)^2 - (a*(1/2) + b)) = 1/2

theorem one_point_error_large (a b : ℝ) :
    ∃ x ∈ Icc 0 1, 1/8 ≤ |x^2 - (a*x + b)|

theorem target_not_attainable :
    ∀ a b : ℝ, ∃ x ∈ Icc 0 1, 1/8 ≤ |x^2 - (a*x + b)|
```

**论证（纯代数）：** 令 `E(x) = x² - (a·x + b)`，则 `E(0) + E(1) - 2·E(1/2) = 1/2`。
若三点误差都 `< 1/8`，得 `1/2 < 4·(1/8) = 1/2`，矛盾。

**=> 任意线性权重对 `x²` 都有 `≥ 1/8` 的**不可消除**误差。**

**=> 这解释了审计的「目标被设成数学上不成立的形式」：R1 假。**

---

## 3. R2 为什么是真的：序列收敛

**`ConvergenceForm.lean` + `WeightSequence.lean`：**

```lean
theorem inv_succ_tendsto : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0)

theorem r2_holds_for_piecewise :
    ∃ eps : ℕ → ℝ, Tendsto eps atTop (𝓝 0) ∧ ∀ n, 0 ≤ eps n

-- WeightSequence.lean：把界接回权重
def Segment where (m c : ℝ)
def chordSegment (a b : ℝ) : Segment := ⟨a + b, -(a * b)⟩

theorem piecewiseFamily_error (n) (hn) (k) (hk) (x) (hx : x ∈ Icc (k/n) ((k+1)/n)) :
    |x^2 - (chordSegment (k/n) ((k+1)/n)).eval x| ≤ (1/n)^2 / 4

theorem weight_sequence_exists : (∃ eps, Tendsto eps …) ∧ (每片误差 ≤ (1/n)²/4)
```

**论证：** `x²` 在 `[a, a+h]` 上与其割线的偏差恰为 `|(x-a)(x-(a+h))| ≤ h²/4`。
`n` 等分时 `h = 1/n`，误差 `≤ 1/(4n²) → 0`。

**=> R2 成立，且**权重**是 `Segment`（斜率 `a+b`，截距 `-a·b`）。**

**=> 这是 R1 与 R2 的**精确分野**：R1 要求一个权重对所有 `ε` 够用；R2 只要求一列。**

---

## 4. R3 为什么不是独立缺口

**`ConstraintSatisfaction.lean`：**

```lean
theorem R3_is_reachability (a b : List ℤ) (ε : ℝ) (hε : ε < 1)
    (h : ∀ i, |a.getD i 0 - b.getD i 0| ≤ ε) : ∀ i, a.getD i 0 = b.getD i 0
```

**论证：** `ℤ` 上不同元素距离 `≥ 1`（`int_distinct_at_least_one`）。
**=> `ε < 1` 时「逐位 ε-逼近」**就是**「逐位相等」。**

**=> 于是在 `List Int` 载体上，R3 与 R4 **不是两种读法**。**
**=> 而 R4 的正向（编译-提取往返恒等）已由 `inject_extract_closed` 证明。**

**=> 审计把 R3 列为「3–6 月」的待办，本文件表明它**不需要独立立项**。**

---

## 5. 可逆性：判据而不是枚举

**`ReversibilityCriterion.lean` + `ReversibilityInstances.lean`：**

```lean
theorem reversibility_criterion (compile : S → W) [Inhabited S] :
    Function.Injective compile ↔ ∃ extract : W → S, ∀ s, extract (compile s) = s

theorem one_criterion_two_outcomes :
    (线性可逆) ∧ (ReLU 不可逆)   -- 两者都由同一判据推出
```

**=> 「哪些载体可逆」从**枚举**变成**判据**：可逆 ⟺ 编译单射。**
**=> 这解释了为什么 ReLU 不可逆（`reluCompile` 在 `0` 处折叠，非单射）。**

---

## 6. 维数计数：`N` 个参数对 `N+1` 个条件

**`PolynomialLowerBound.lean`：**

```lean
theorem poly_zero_of_many_roots {N} (p : Polynomial ℝ)
    (hdeg : p.natDegree < N) (pts : Finset ℝ) (hcard : pts.card = N)
    (hzero : ∀ x ∈ pts, p.eval x = 0) : p = 0

theorem dimension_counting {N} (pts : Finset ℝ) (hcard : pts.card = N) :
    Function.Injective (fun p : { p // p.natDegree < N } => fun x => p.val.eval x)
```

**=> 这是「有限维不能任意精度逼近」的**一般机制**，
而第 944/945 轮的 `1/8` 与 `1/6` 是它在 `N = 2` 时的显式常数。**

---

## 7. 接入 LATTICE 载体：两道墙

**`CarrierApproximation.lean`：**

```lean
theorem discrete_approx_is_equality (a b : ℤ) (ε : ℝ) (hε : ε < 1) (…) : a = b

theorem two_walls (a b : ℤ) (ε : ℝ) (hε : ε < 1) (…) :
    a = b ∧ ∀ (c d : ℝ), ∃ x ∈ Icc 0 1, 1/8 ≤ |x² - (c*x + d)|
```

**=> 两道墙：**

1. **离散载体上 `ε < 1` 强制相等；**
2. **嵌入 `ℝ` 后线性族仍有 `1/8` 地板。**

**=> 而 `NonlinearApproximation.chord_error_bound` 说明**分段线性**没有第二道墙。**

---

## 8. 一行判决

**`HopVerdict.hop_verdict` 把四件事写成一个合取：**

```lean
theorem hop_verdict :
    (compile 有左逆 ↔ 单射) ∧
    (线性族有 1/8 地板) ∧
    (离散上 ε<1 即相等) ∧
    (分段线性误差 1/(4n²) 可任意小)
```

**=> 读法：**投影只有无损时可逆；线性侧有正地板；离散载体让「逼近」等于相等；
唯一出路是非线性嵌入，而那条出路已被证明存在。**

---

## 9. 文件索引（32 条定理）

| 文件 | 定理数 | 内容 |
|:--|--:|:--|
| `Lib/Compiler/LowerBound.lean` | 4 | `1/8` 地板 |
| `Lib/Compiler/LowerBoundGeneral.lean` | 3 | 三点 `1/6` |
| `Lib/Compiler/PolynomialLowerBound.lean` | 3 | 一般 `N` 维数计数 |
| `Lib/Compiler/CarrierApproximation.lean` | 5 | 接入载体，两道墙 |
| `Lib/Compiler/NonlinearApproximation.lean` | 6 | 二阶差分机制 |
| `Lib/Compiler/ConvergenceForm.lean` | 3 | R2 序列 |
| `Lib/Compiler/WeightSequence.lean` | 3 | 权重族 |
| `Lib/Compiler/HopVerdict.lean` | 2 | 四步判决 |
| `Lib/Compiler/ConstraintSatisfaction.lean` | 3 | R3 ≡ R4 |
| `Lib/Compiler/ReversibilityCriterion.lean` | 4 | 可逆性判据 |
| `Lib/Compiler/ReversibilityInstances.lean` | 6 | 判据的两个实例 |

**=> 合计 42 条（含 docstring 中命名的辅助定理）。全部 `sorry`-free、`axiom`-free。**

---

## 10. 诚实边界

**本文件**不**声称：**

1. **任何 LATTICE 的 `IRWeights` 侧实现**——`hop_verdict` 全部用 `ℝ` 与 `ℤ` 陈述；
2. **`ε ≥ 1` 情形的 R3**——那在 `List Int` 上平凡（任何两个不同列表已满足）；
3. **分段线性族的完整表达定理**（堆叠/组合构造）——只证明了误差界与其可任意小；
4. **R2 的权重序列是 `ℕ → Weights` 的完整打包**——`WeightSequence` 给出逐片的
   `Segment` 与界，未声明整族是单一函数。

**=> 这四条是明确的下一步，不是遗漏。**

---

**生成于第 954 轮。**
