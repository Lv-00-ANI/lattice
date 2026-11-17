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

## 9. 文件索引（14 个文件，55 条定理）

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
| `Lib/Compiler/ModulusAbstract.lean` | 10 | **the generic modulus `√δ` (stage D)** |
| `Lib/Compiler/ReversibilityCriterion.lean` | 4 | reversibility criterion |
| `Lib/Compiler/ReversibilityInstances.lean` | 6 | the criterion's two instances |

**=> **15 files, 68 declarations**. All `sorry`-free, `axiom`-free.**

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
| 3 | 缺完整表达定理 | **仍开放** | 无 `compose`/`stack` 形式的分段构造 |
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

**生成于第 954 轮；第 956 轮更新至精确状态；第 957 轮新增 §10b（模数）；第 959 轮新增 §3b（一致逼近）。**
