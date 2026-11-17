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

## 3b. R2 可以加强成 **R1**，只要族是非线性的（第 959 轮）

**R2 是**逐点/序列**形式的：存在一列界趋于零。**
**=> 第 959 轮把它加强成**一致**形式，即 R1 的形状。**

**`Lib/Compiler/PiecewiseUniform.lean`：**

```lean
theorem piecewiseWeights_at_one (n) (hn) : piecewiseWeights n 1 = 1

theorem piecewiseWeights_error_closed (n) (hn) (x) (hx : x ∈ Icc 0 1) :
    |x ^ 2 - piecewiseWeights n x| ≤ (1 / n) ^ 2 / 4

theorem piecewiseWeights_uniform_tendsto :
    ∀ ε > 0, ∃ n : ℕ, 1 ≤ n ∧ ∀ x ∈ Icc (0:ℝ) 1, |x ^ 2 - piecewiseWeights n x| ≤ ε

theorem r1_false_linear_true_piecewise :
    (∀ a b : ℝ, ∃ x ∈ Icc 0 1, 1/8 ≤ |x^2 - (a*x + b)|) ∧   -- 线性：假
    (∀ ε > 0, ∃ n ≥ 1, ∀ x ∈ Icc 0 1, |x^2 - ws n x| ≤ ε)      -- 分段线性：真
```

**修掉的具体缺陷：** 第 955 轮的界只对 `x < 1` 成立，
因为 `segmentIndex n 1 = n` 越界而 `piecewiseFamily_error` 要求 `k < n`。
**=> 但端点上函数值**恰好精确**（`piecewiseWeights n 1 = 1 = 1²`），只是那条路径覆盖不到。**
**=> 本文件补上端点，界遂在**闭区间**上成立。**

**=> 结论：`∀ f ∀ ε > 0 ∃ w` 这个**形状**本身并没有错——**
**它只是对**线性族**为假，对**分段线性族**为真，而且在后者上是**一致**为真。**

**=> 审计所说「目标被设成了数学上不成立的形式」，精确的说法应当是：
「目标的作用域被设得太宽（含线性族）」，而不是「形式本身不可满足」。**

---

## 3c. 一般弦：把 `chordSegment` 从 `x²` 泛化（第 960 轮）

**`WeightSequence.chordSegment a b = ⟨a+b, -(a·b)⟩` 是**过 `(a,a²)` 与 `(b,b²)` 的割线**——
**它把 `f = ·²` 写死进了定义。**

**`Lib/Compiler/ChordGeneral.lean` 把割线定义为**从函数值出发**的一般构造：**

```lean
def chordSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)
def chordOf (f : ℝ → ℝ) (a b : ℝ) : Segment :=
  ⟨chordSlope f a b, f a - chordSlope f a b * a⟩

theorem chordOf_sq (a b) (h : a ≠ b) :
    chordOf (fun x => x^2) a b = chordSegment a b          -- 旧定义是特例
theorem chordOf_affine (c d a b) (h : a ≠ b) :
    chordOf (fun x => c*x + d) a b = ⟨c, d⟩              -- 仿射的弦就是它自己
theorem piecewiseInterp_affine_exact (c d n) (hn) (x) :
    piecewiseInterp (fun t => c*t + d) n x = c*x + d      -- 误差为 0
```

**两个关键点：**

1. **`chordOf_sq`**证明旧定义被**包含**，故第 948–959 轮的全部结果**不作废**；
2. **`piecewiseInterp_affine_exact`**给出表达力：**分段线性族**包含**仿射族**，且误差恰为 `0`。**

**=> 这就是「线性族为什么有 `1/8` 地板」的**结构性解释**：**
**分段线性族能精确表示仿射族能表示的一切，而 `x²` 不在仿射族内，
所以仿射族对 `x²` 的失败是**必然**的，不是一个偶然的常数。**

**⚠ 本节**不**声称完整表达定理（堆叠/组合构造仍开放）；
它只闭合了**包含关系 + 精确表示**这一层。**

---

## 3d. 一般误差界：把 `h²/4` 从 `x²` 泛化到满足帐篷界的一切函数（第 961 轮）

**第 948 轮的 `chord_error_bound` 依赖一个**仅对二次函数成立**的因式分解：
`x² - 割线 = (x-a)(x-b)`。=> 对一般 `f` 没有对应物。**

**`Lib/Compiler/ChordErrorGeneral.lean` 把那个因式分解**当成假设**：**

```lean
theorem tent_le_quarter (a b x M) (hab : a <= b) (hx) (hM : 0 <= M) :
    M * ((x - a) * (b - x)) <= M * ((b - a) ^ 2 / 4)          -- AM-GM, no calculus

theorem chord_error_of_tent_bound (f : R -> R) (a b M) (hab : a < b) (hM : 0 <= M)
    (htent : forall x in Icc a b, |f x - chord.eval x| <= M * ((x - a) * (b - x))) :
    forall x in Icc a b, |f x - chord.eval x| <= M * ((b - a) ^ 2 / 4)

theorem sq_chord_error_eq_tent (a b x) (hab) (hx) :
    |x^2 - chord.eval x| = (x - a) * (b - x)                   -- the tent bound HOLDS with M = 1

theorem chord_error_sq_rederived (a b x) (hab) (hx) :
    |x^2 - chord.eval x| <= (b - a) ^ 2 / 4                    -- old bound, RE-DERIVED
```

**两个要点：**

1. **`chord_error_of_tent_bound` 对**任意 `f`**成立，不需可微性、不需中值定理；
   它把「二阶曲率」的作用**完全封装**进帐篷假设。**
2. **`chord_error_sq_rederived` 证明旧界是新定理的**实例**——
   若没有这一条，所谓泛化就只是另起一套。**

**=> 于是第 948–959 轮的 `1/(4n²)`、`quarter_inv_sq_tends_to_zero`、
一致逼近，全部**原样成立**，且现在对**一般 `f`** 有了推广。**

**⚠ 本节不声称**从 `|f''| <= M` 推出帐篷界**：那需要 Taylor/MVT，仍开放。
本节只把帐篷假设**当作输入**，并证明它足以推出误差界。**

---

## 3e. 从**凸性**推出帐篷界，从而得到经典界 `M(b-a)²/8`（第 962 轮）

**第 961 轮记下：帐篷假设从何而来？本节给出答案的**第一层**。**

**教科书路线是 Rolle 连用两次（`φ(t) = f t - p t - K(t-a)(t-b)` 三个零点）。
本项目用**等价的半凸性**路线，只需 Mathlib 已有的一个引理。**

**`Lib/Compiler/ConvexityChord.lean`：**

```lean
theorem chord_eval_eq_div (g) (a b x) (hab : a < b) :
    (chordOf g a b).eval x = (g b * (x - a) + g a * (b - x)) / (b - a)

theorem convex_le_chord (f) (a b x) (hab : a < b)
    (hconv : ConvexOn R (Icc a b) f) (hx : x in Icc a b) :
    f x <= (chordOf f a b).eval x                       -- 凸 => 图像在弦下

theorem tent_of_semiconvex (f) (a b M x) (hab) (hM)
    (h1 : ConvexOn R (Icc a b) (fun t => f t + (M/2) * t^2))
    (h2 : ConvexOn R (Icc a b) (fun t => -(f t) + (M/2) * t^2))
    (hx : x in Icc a b) :
    |f x - chord.eval x| <= (M/2) * ((x - a) * (b - x))  -- 双侧帐篷界

theorem chord_error_of_semiconvex (f) (a b M x) (hab) (hM) (h1) (h2) (hx) :
    |f x - chord.eval x| <= M * (b - a)^2 / 8            -- 经典界
```

**关键点：**

1. **`convex_le_chord` 由 `ConvexOn.slope_mono_adjacent` 交叉相乘得到——
   **不经过任何 Lagrange 余项构造**；
2. **对 `F t = f t + (M/2)t²` 与 `G t = -f t + (M/2)t²` 各用一次就得**双侧**帐篷界；
3. **接上 §3d 的 `chord_error_of_tent_bound`，帐篷常数 `M/2` 给出 `M(b-a)²/8`。**

**=> 这正是文献中的线性插值误差界 `(x₁-x₀)²/8 · max|f''|`。**

**⚠ 剩下**一层**：从 `|f''| ≤ M` 到 `h1`/`h2`。**
**配方已写在文件 §5：用 `convexOn_of_deriv2_nonneg`
（`Analysis/Convex/Deriv.lean:212`），只需迭代导数恒等式
`deriv^[2] (fun t => f t + c·t²) = deriv^[2] f + 2c`。**

**=> 于是「`|f''| ≤ M` ⇒ 弦误差 `≤ M(b-a)²/8`」只差一条**机械导数恒等式**。**

---

## 3f. 链条闭合：`|f''| <= M` 推出 `M(b-a)^2/8`（第 963 轮）

**§3e 记下「剩下一层：从 `|f''| <= M` 到 `h1`/`h2`」。**本节把它闭合。

**`Lib/Compiler/SecondDerivBound.lean`（6 项声明）：**

```lean
theorem deriv_shift_eq (f) (c) (hf : Differentiable R f) :
    deriv (fun t => f t + c * t^2) = fun y => deriv f y + 2 * c * y

theorem iter_deriv_shift_eq (f) (c) (x) (hf) (hf') :
    deriv^[2] (fun t => f t + c * t^2) x = deriv^[2] f x + 2 * c

theorem deriv_neg_eq      (f) (hf)       : deriv (fun t => -(f t)) = fun y => -(deriv f y)
theorem iter_deriv_neg_eq (f) (x) (hf) (hf') : deriv^[2] (fun t => -(f t)) x = -(deriv^[2] f x)

theorem convex_shift_of_lower (a b M) (hab) (hM) (g) (hg) (hg')
    (hge : forall x in interior (Icc a b), -M <= deriv^[2] g x) :
    ConvexOn R (Icc a b) (fun t => g t + (M/2) * t^2)

theorem chord_error_of_second_deriv_bound (f) (a b M) (hab) (hM)
    (hf : Differentiable R f)
    (hf' : DifferentiableOn R (deriv f) (interior (Icc a b)))
    (hM2 : forall x in interior (Icc a b), |deriv^[2] f x| <= M) :
    forall x in Icc a b, |f x - chord.eval x| <= M * (b - a)^2 / 8
```

**于是整条链闭合：**

```
|f''| <= M  --(convex_shift_of_lower 用两次: g = f, 再 g = -f)-->  半凸对 h1, h2
           --(tent_of_semiconvex)-->  帐篷界 (M/2)(x-a)(b-x)
           --(chord_error_of_tent_bound)-->  M(b-a)^2 / 8
```

**三个技术障碍（已写入文件文档，供后续复用）：**

1. **`rw` 无法穿透 `deriv^[2]` 展开后的 lambda => 先用 `funext` 写成**函数等式**；**
2. **`deriv^[2]` 是 `iteratedDeriv` 记号，`simp` 展不开 => 用 `show` 强制写成 `deriv (deriv _) _`；**
3. **`deriv_neg` 是「取负**函数自身**」的导数（`deriv Neg.neg x = -1`），不是所要的
   => 用 `HasDerivAt.neg`。**

**另记签名陷阱：`deriv_const_mul` 的第一个参数是常数 `c`，证明在其后**（不是证明在前的常见形状）。

**=> P8 的「一般误差界」链条至此**不再有未证的一层**。**

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

## 9. 文件索引（19 个文件，98 项声明）

| 文件 | 定理数 | 内容 |
|:--|--:|:--|
| `Lib/Compiler/LowerBound.lean` | 4 | `1/8` floor |
| `Lib/Compiler/LowerBoundGeneral.lean` | 3 | three points, `1/6` |
| `Lib/Compiler/PolynomialLowerBound.lean` | 3 | general-`N` dimension counting |
| `Lib/Compiler/CarrierApproximation.lean` | 5 | wired to the carrier, two walls |
| `Lib/Compiler/NonlinearApproximation.lean` | 6 | second-difference mechanism |
| `Lib/Compiler/ConvergenceForm.lean` | 3 | R2 sequence |
| `Lib/Compiler/WeightSequence.lean` | 6 | per-piece weight family |
| `Lib/Compiler/HopVerdict.lean` | 3 | the four-step verdict |
| `Lib/Compiler/ConstraintSatisfaction.lean` | 3 | R3 = R4 for `ε < 1` |
| `Lib/Compiler/R3Triviality.lean` | 3 | **`ε ≥ 1` is NOT trivial** (disproof) |
| `Lib/Compiler/PiecewiseWeights.lean` | 4 | **the family as ONE function** |
| `Lib/Compiler/PiecewiseUniform.lean` | 5 | **UNIFORM on the closed interval: R1 true for piecewise** |
| `Lib/Compiler/ChordGeneral.lean` | 14 | **the GENERAL chord: `chordOf f a b`, and affine is exact (stage F)** |
| `Lib/Compiler/SecondDerivBound.lean` | 6 | **`\|f''\| <= M` => `M(b-a)^2/8` (stage H, chain CLOSED)** |
| `Lib/Compiler/ConvexityChord.lean` | 5 | **convexity => tent => `M(b-a)²/8` (stage G)** |
| `Lib/Compiler/ChordErrorGeneral.lean` | 5 | **the GENERAL error bound: tent hypothesis => `M(b-a)²/4`** |
| `Lib/Compiler/ModulusAbstract.lean` | 10 | **the generic modulus `√δ` (stage D)** |
| `Lib/Compiler/ReversibilityCriterion.lean` | 4 | reversibility criterion |
| `Lib/Compiler/ReversibilityInstances.lean` | 6 | the criterion's two instances |

**=> **19 files, 98 declarations**. All `sorry`-free, `axiom`-free.**

---

## 10. 诚实边界

**本文件**不**声称：**

1. **任何 LATTICE 的 `IRWeights` 侧实现**——`hop_verdict` 全部用 `ℝ` 与 `ℤ` 陈述；
2. ~~**`ε ≥ 1` 情形的 R3**——那在 `List Int` 上平凡~~**
   **⚠ **第 955 轮已推翻此说**：反例 `a = 0`、`b = 5`、`ε = 1`
   给出 `|0 - 5| = 5 > 1`。**正确宣言**是：
   **R3 在 `ε ≥ 1` 时**仍是实质命题**，随 `ε` 变化。**
   **参见 `Lib/Compiler/R3Triviality.lean` 的 `R3_boundary_corrected`。**
3. **分段线性族的完整表达定理**（堆叠/组合构造）——只证明了误差界与其可任意小；
4. ~~**R2 的权重序列是 `ℕ → Weights` 的完整打包**——未声明整族是单一函数。~~**
   **✅ **第 955 轮已闭合**：`PiecewiseWeights.piecewiseWeights : ℕ → ℝ → ℝ`
   就是那个单一函数，且 `piecewiseWeights_error` 直接关于它陈述尹差界。**

### 四条边界的**实测状态**（第 957 轮核实）

| # | 原表述 | 状态 | 依据 |
|--:|:--|:--|:--|
| 1 | `IRWeights` 侧无实现 | **仍开放** | `git grep IRWeights Lattice/Lib/Compiler/*` 为空 |
| 2 | `ε ≥ 1` 平凡 | **已推翻** | `R3Triviality.R3_boundary_corrected`（反例 `0,5,1`） |
| 3 | 缺完整表达定理 | **近乎闭合** | `ChordGeneral` + `ChordErrorGeneral` + `ConvexityChord` + `SecondDerivBound`：包含关系、精确表示、一般误差界、`\|f''\| <= M => M(b-a)^2/8` 均已证；**仅堆叠构造开放** |
| 4 | R2 未包成单一函数 | **已闭合** | `PiecewiseWeights.piecewiseWeights`（`fe54eb8d`） |

**=> 四条中**两条已处理、两条开放**。**

---

## 10b. 模数：把 `T2Modulus` 的 `√δ` 抽象到 `Lib` 层（第 957 轮）

**审计的另一条判决：**

> **`T2Modulus` 的 `g = √δ` 是**全库唯一真逼近内容**，但它活在 `GeoExpr` 上。**

**=> 若它随几何层归档而消失，全库就没有逼近模数了。**

**`Lib/Compiler/ModulusAbstract.lean` 把它抽象成与载体无关的结构：**

```lean
structure Modulus where
  toFun   : ℝ → ℝ
  eq_sqrt : ∀ δ, 0 ≤ δ → toFun δ = Real.sqrt δ
```

**为什么必须带 `eq_sqrt`（而不是只带 `nonneg`/`at_zero`/`mono`）：**
**`Lattice/Probe/ModulusShape` 证明了只凭那三条**推不出** `bound`（反例 `toFun ≡ 0`）。**

| 定理 | 内容 |
|:--|:--|
| `Modulus.bound` | **`0 ≤ δ → 0 ≤ e → e² ≤ δ → e ≤ toFun δ`（载体无关）** |
| `Modulus.bound_tight` | **`(toFun δ)² = δ`（界被达到，不可改进）** |
| `modulus_verdict` | **上两者的合取** |
| `T2Modulus.g_eq_sqrtModulus_toFun` | **几何层的 `g` 逐字等于抽象的 `toFun`** |
| `T2Modulus.approx_min_violation_bound_via_abstract` | **用抽象**重推**既有的 `approx_min_violation_bound`** |

**=> 方向合法：`Plugins`（rank 3）→ `Lib`（rank 3）同层横向，I4 通过。**

**另：`hop_verdict_with_modulus` 把模数作为第五合取项接入 `hop_verdict`，
使审计所言「P8 与 T2 互不相连」成为定理级连接。**

**=> 这四条是明确的下一步，不是遗漏。**

---

**生成于第 954 轮；第 956 轮更新至精确状态；第 957 轮新增 §10b（模数）；第 959 轮新增 §3b（一致逼近）；第 960–963 轮新增 §3c–§3f（一般弦、一般误差界、凸性路线、二阶导数界）。**
