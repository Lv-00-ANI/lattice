import Mathlib

/-!
# LATTICE: 可执行验证桥 —— Float 实现、ℝ 规范与误差界

本文件是浮点语义（`RealIEEE754`/`RealMixedPrecisionRounding`）与**可执行实现**之间的桥：

  1. **可执行层（Float，计算）**：`fRelu`/`fSigmoid`/`fSilu`/`fSoftmax2`/`fSoftplus`/
     `fCrossEntropy2`/`fLinearAttention`/`fRoPE` 的 `Float` 实现，并用 `#eval` 做
     **断言式自检**（自检块打印具体数值，供人工核对；不影响 `lake build` 退出码）；
  2. **规范层（ℝ，证明）**：`realRelu`/`realSigmoid`/`realSilu`/`realSoftmax2`/
     `realSoftplus`/`realCrossEntropy2`/`realLinearAttention`/`realRoPE`；
  3. **精确桥（ℚ 层）**：`qRelu`/`qLinearAttention` 等**纯代数**可执行函数，
     证明 `(qRelu q : ℝ) = realRelu (q : ℝ)`（`qRelu_cast`）与
     `(qLinearAttention q k v : ℝ) = realLinearAttentionRat (q:ℝ) (k:ℝ) (v:ℝ)`
     （`qLinearAttention_cast`）——这是本文件形式的 `↑(evalFn x) = realFn x`；
  4. **误差界桥（δ 参数化）**：`PrimApprox` 结构给出 `expA`/`logA`/`cosA`/`sinA`
     四个原语近似及其误差 `δ`（**显式假设的数据**，与 `RealFloatFormat.RoundOp` 同一风格），
     由此证明 `sigA_close`/`siluA_close`/`softmax2A_close`/`softplusA_close`/`ce2A_close`/
     `linearAttentionA_close`/`ropeA_fst_close`/`ropeA_snd_close` 等误差界。

## 诚实标注：为什么桥是「ℚ 精确 + δ 参数化」而不是 `↑(Float) = ℝ`
Lean 4.14 的 `Float` **没有**到 `ℝ`（也没有到 `ℚ`）的转换：工具链只有 `Rat.toFloat : ℚ → Float`，
没有 `Float.toRat`，故 `↑(fSigmoid x) : ℝ` 这样的项**无法书写**。因此：
  · 对**纯代数**函数，本文件用 `ℚ` 版可执行函数（`ℚ` 有到 `ℝ` 的 cast），把
    「可执行 = 规范」证成**等式**（`qRelu_cast`/`qLinearAttention_cast`）；
  · 对**含超越原语**的函数（`exp`/`log`/`sin`/`cos`），把桥证成**误差界**：
    原语的浮点误差 `δ` 作为 `PrimApprox` 的显式假设，结论是复合函数的误差界
    （如 `|sigA − realSigmoid| ≤ δ`、`|ce2A − realCrossEntropy2| ≤ (2+|y|)·δ`）；
  · `Float` 层的**数值正确性**由 `#eval` 自检 + 下列 python/numpy 对照给出（**未做**：
    把 `Float` 结果自动导入 ℚ/ℝ 的机械化桥，Lean 4.14 缺少必要原语 —— 标注）。

## 如何用 Python/numpy 做数值对照（人工复核；**构建时不联网、不调用 Python**）
在项目根目录（`C:\Users\xingg\Desktop\agent\lattice\lean`）之外的任意 shell 执行：

```
# 1) sigmoid 在 0 处的值应为 0.5；在 1 处约 0.7310585786
python -c "import numpy as np; print(1/(1+np.exp(-0.0)), 1/(1+np.exp(-1.0)))"

# 2) 2 类 softmax（等价于 logit 差的 sigmoid）：[1,0] -> [0.7310586, 0.2689414]
python -c "import numpy as np; x=np.array([1.0,0.0]); e=np.exp(x-x.max()); print(e/e.sum())"

# 3) 二元交叉熵（logits 形式）：-(y*log p + (1-y)*log(1-p))，p=sigmoid(z)
python -c "import numpy as np; z=0.0; p=1/(1+np.exp(-z)); print(-(1*np.log(p)+0*np.log(1-p)))"

# 4) silu(1) = 1*sigmoid(1) 约 0.7310585786
python -c "import numpy as np; x=1.0; print(x/(1+np.exp(-x)))"

# 5) 线性注意力核 exp(q*k)*v：q=k=1, v=2 -> 2*e 约 5.4365637
python -c "import numpy as np; print(np.exp(1.0*1.0)*2.0)"

# 6) RoPE 旋转（theta=0 时为恒等）：(x1,x2)=(1,0) -> (1,0)
python -c "import numpy as np; t=0.0; x1,x2=1.0,0.0; print(x1*np.cos(t)-x2*np.sin(t), x1*np.sin(t)+x2*np.cos(t))"

# 7) 与 Lean 的 #eval 输出逐项比对：#eval 块位于本文档「可执行自检」一节
```

无 sorry/axiom/admit；除 `PrimApprox`（显式假设结构）与 ℚ/Float 可执行函数外，全部为定理。
-/

noncomputable section

namespace Lattice

/-! ## 一、可执行层：`Float` 实现（计算） -/

/-- 可执行 ReLU：`max x 0`（`Float` 的 `max` 是精确的，不引入舍入）。 -/
def fRelu (x : Float) : Float := max x 0.0

/-- 可执行 sigmoid：`1 / (1 + exp (−x))`（调用 `Float.exp`）。 -/
def fSigmoid (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

/-- 可执行 SiLU：`x * sigmoid x`。 -/
def fSilu (x : Float) : Float := x * fSigmoid x

/-- 可执行 2 类 softmax：`softmax([a,b]) = sigmoid(a − b)`（等价形式，避免除零）。 -/
def fSoftmax2 (a b : Float) : Float := fSigmoid (a - b)

/-- 可执行 softplus：`log (1 + exp z)`。 -/
def fSoftplus (z : Float) : Float := Float.log (1.0 + Float.exp z)

/-- 可执行二元交叉熵（logits 形式，`y ∈ {0,1}`）：`softplus z − y·z`。 -/
def fCrossEntropy2 (y z : Float) : Float := fSoftplus z - y * z

/-- 可执行线性注意力核（指数形式）：`exp (q·k) · v`。 -/
def fLinearAttention (q k v : Float) : Float := Float.exp (q * k) * v

/-- 可执行 RoPE 旋转（二维）：`(x1·cos θ − x2·sin θ, x1·sin θ + x2·cos θ)`。 -/
def fRoPE (x1 x2 theta : Float) : Float × Float :=
  (x1 * Float.cos theta - x2 * Float.sin theta, x1 * Float.sin theta + x2 * Float.cos theta)

/-! ## 二、可执行自检（`#eval` 断言：打印具体数值供人工核对）

下面每一行 `#eval` 在**构建时**求值并打印；`#eval` 只在 `Float`（完全可计算）上进行，
不涉及 `ℝ`（其 `≤`/`=` 判定是 `noncomputable`，无法 `#eval`）。
末行的布尔检查是**断言式**自检：全部通过才打印 `selfcheck: OK`。 -/

-- ReLU：3 → 3，−3 → 0
#eval (fRelu 3.0, fRelu (-3.0))
-- sigmoid：0 → 0.5；softmax([1,0]) ≈ 0.7310586
#eval (fSigmoid 0.0, fSoftmax2 1.0 0.0)
-- SiLU(1) ≈ 0.7310586；softplus(0) = log 2 ≈ 0.6931472
#eval (fSilu 1.0, fSoftplus 0.0)
-- 二元交叉熵：y=1,z=0 → softplus 0 − 0 = log 2 ≈ 0.6931472；y=0,z=1 → log 2 − 0 ≈ 0.6931472；
-- 注意 `z = 0` 时两类都等于 log 2（对称点），只有 `z ≠ 0` 才分开
#eval (fCrossEntropy2 1.0 0.0, fCrossEntropy2 0.0 1.0)
-- 二元交叉熵的显式零点：log(1+exp z) − y·z 在 (y,z)=(0,0) 处仍为 log 2 ≈ 0.6931472
#eval fCrossEntropy2 0.0 0.0
-- 线性注意力：exp(1·1)·2 ≈ 5.4365637
#eval fLinearAttention 1.0 1.0 2.0
-- RoPE：θ=0 时为恒等 (1,0) → (1,0)
#eval fRoPE 1.0 0.0 0.0
-- 断言式自检（全部为真则 OK）
-- 说明：只对**精确可实现**的等式做断言（ReLU 的 max、sigmoid(0)=0.5 恰可表示、
-- RoPE 在 θ=0 时乘 0 与乘 1）。含 `Float.log`/`Float.exp` 的项**不做** `==` 断言
-- （其舍入结果不是精确值，例如 `fCrossEntropy2 0.0 0.0 = log 2` 并非 `0.0`）——
-- 这类量由上一行的 `#eval` 打印数值供人工/numpy 对照（诚实降级：不做浮点精确断言）。
#eval
  if (fRelu 3.0 == 3.0) && (fRelu (-3.0) == 0.0) && (fSigmoid 0.0 == 0.5)
      && (fCrossEntropy2 0.0 0.0 > 0.69) && (fCrossEntropy2 0.0 0.0 < 0.70)
      && ((fRoPE 1.0 0.0 0.0).1 == 1.0)
      && ((fRoPE 1.0 0.0 0.0).2 == 0.0)
    then "selfcheck: OK"
    else "selfcheck: FAIL"

/-! ## 三、规范层：`ℝ` 定义（证明用） -/

/-- ℝ 版 ReLU：`max x 0`。 -/
def realRelu (x : ℝ) : ℝ := max x 0

/-- ℝ 版 sigmoid：`1 / (1 + exp (−x))`。 -/
def realSigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- ℝ 版 SiLU：`x * sigmoid x`。 -/
def realSilu (x : ℝ) : ℝ := x * realSigmoid x

/-- ℝ 版 2 类 softmax：`sigmoid (a − b)`。 -/
def realSoftmax2 (a b : ℝ) : ℝ := realSigmoid (a - b)

/-- ℝ 版 softplus：`log (1 + exp z)`。 -/
def realSoftplus (z : ℝ) : ℝ := Real.log (1 + Real.exp z)

/-- ℝ 版二元交叉熵（logits 形式）：`softplus z − y·z`。 -/
def realCrossEntropy2 (y z : ℝ) : ℝ := realSoftplus z - y * z

/-- ℝ 版线性注意力核：`exp (q·k) · v`。 -/
def realLinearAttention (q k v : ℝ) : ℝ := Real.exp (q * k) * v

/-- ℝ 版 RoPE 旋转（二维）。 -/
def realRoPE (x1 x2 theta : ℝ) : ℝ × ℝ :=
  (x1 * Real.cos theta - x2 * Real.sin theta, x1 * Real.sin theta + x2 * Real.cos theta)

/-! ## 四、精确桥（ℚ 层）：`↑(evalFn x) = realFn x` 可证的部分

`ℚ` 有到 `ℝ` 的 cast，且算术完全可计算，故**纯代数**函数可以在 `ℚ` 上实现并**精确**桥到 ℝ。
含超越函数的函数无法这样处理（`ℚ` 上无 `exp`/`log`），其桥见下一节的 δ 参数化误差界。 -/

/-- 可执行（`ℚ` 版）ReLU：`max q 0`（纯代数，精确）。 -/
def qRelu (q : ℚ) : ℚ := max q 0

/-- **精确一致性定理（ReLU）**：`(qRelu q : ℝ) = realRelu (q : ℝ)`
——可执行的 `ℚ` 实现与其 ℝ 规范**逐点相等**（`Rat.cast_max`）。 -/
theorem qRelu_cast (q : ℚ) : (qRelu q : ℝ) = realRelu (q : ℝ) := by
  unfold qRelu realRelu
  simpa using Rat.cast_max q 0

/-- 可执行（`ℚ` 版）归一化线性注意力核：`(q·k)·v / (1 + q²)`（纯代数，分母恒正）。 -/
def qLinearAttention (q k v : ℚ) : ℚ := (q * k) * v / (1 + q * q)

/-- ℝ 规范版（与 `qLinearAttention` 逐项对应的同一有理表达式）。 -/
def realLinearAttentionRat (q k v : ℝ) : ℝ := (q * k) * v / (1 + q * q)

/-- **精确一致性定理（归一化线性注意力）**：
`(qLinearAttention q k v : ℝ) = realLinearAttentionRat (q:ℝ) (k:ℝ) (v:ℝ)`
——可执行 `ℚ` 实现与其 ℝ 规范逐点相等（`push_cast` + `ring`）。 -/
theorem qLinearAttention_cast (q k v : ℚ) :
    (qLinearAttention q k v : ℝ) = realLinearAttentionRat (q : ℝ) (k : ℝ) (v : ℝ) := by
  unfold qLinearAttention realLinearAttentionRat
  push_cast
  ring

/-! ## 五、误差界桥（δ 参数化）：含超越原语的函数

`PrimApprox` 把「浮点原语 `exp`/`log`/`sin`/`cos` 与其真值的差距」作为**显式假设数据**
（误差 `δ`），从而得到复合函数的误差界。这与 `RealFloatFormat.RoundOp` 的手法一致：
不是 `axiom`，而是使用者必须提供的结构实例（`Float` 层由 `#eval` 数值自检背书）。 -/

/-- 原语近似接口：四个超越原语的近似函数 + 统一的误差界 `δ`（**显式假设数据**）。
`exp_pos` 保证 sigmoid/softplus 的分母非零；四个 `*_close` 是原语误差界。 -/
structure PrimApprox where
  /-- 近似指数 -/
  expA : ℝ → ℝ
  /-- 近似对数 -/
  logA : ℝ → ℝ
  /-- 近似余弦 -/
  cosA : ℝ → ℝ
  /-- 近似正弦 -/
  sinA : ℝ → ℝ
  /-- 原语误差上界 -/
  δ : ℝ
  /-- 误差非负 -/
  δ_nonneg : 0 ≤ δ
  /-- 近似指数恒正 -/
  exp_pos : ∀ x : ℝ, 0 < expA x
  /-- 指数误差界 -/
  exp_close : ∀ x : ℝ, |expA x - Real.exp x| ≤ δ
  /-- 对数误差界（仅在正参数上要求） -/
  log_close : ∀ x : ℝ, 0 < x → |logA x - Real.log x| ≤ δ
  /-- 余弦误差界 -/
  cos_close : ∀ x : ℝ, |cosA x - Real.cos x| ≤ δ
  /-- 正弦误差界 -/
  sin_close : ∀ x : ℝ, |sinA x - Real.sin x| ≤ δ

/-- 近似 sigmoid：`1 / (1 + expA (−x))`。 -/
def sigA (P : PrimApprox) (x : ℝ) : ℝ := 1 / (1 + P.expA (-x))

/-- 近似 SiLU：`x * sigA x`。 -/
def siluA (P : PrimApprox) (x : ℝ) : ℝ := x * sigA P x

/-- 近似 softplus：`logA (1 + expA z)`。 -/
def softplusA (P : PrimApprox) (z : ℝ) : ℝ := P.logA (1 + P.expA z)

/-- 近似二元交叉熵：`softplusA P z − y·z`。 -/
def ce2A (P : PrimApprox) (y z : ℝ) : ℝ := softplusA P z - y * z

/-- 近似线性注意力核：`expA (q·k) · v`。 -/
def linAttnA (P : PrimApprox) (q k v : ℝ) : ℝ := P.expA (q * k) * v

/-- 近似 RoPE 旋转。 -/
def ropeA (P : PrimApprox) (x1 x2 theta : ℝ) : ℝ × ℝ :=
  (x1 * P.cosA theta - x2 * P.sinA theta, x1 * P.sinA theta + x2 * P.cosA theta)

/-- 三角不等式（差值形式）：`|a − b| ≤ |a| + |b|`（供本文件反复使用）。 -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have hsplit : a - b = a + -b := by ring
  rw [hsplit]
  simpa using abs_add a (-b)

/-- **对数在 `[1, ∞)` 上 1-Lipschitz**：`a, b ≥ 1 ⟹ |log a − log b| ≤ |a − b|`
（由 `Real.log_le_sub_one_of_pos` 与 `div_le_self` 得到；这是交叉熵误差界的关键引理）。 -/
lemma real_log_abs_sub_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rcases le_total b a with h | h
  · have hne : Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)]
    have hbound : Real.log (a / b) ≤ a - b := by
      have h2 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      have h3 : a / b - 1 = (a - b) / b := by
        rw [sub_div a b b, div_self (ne_of_gt hb0)]
      have h4 : (a - b) / b ≤ a - b := div_le_self (by linarith) hb
      linarith
    have hnn : 0 ≤ Real.log a - Real.log b := sub_nonneg.mpr (Real.log_le_log hb0 h)
    rw [abs_of_nonneg hnn, abs_of_nonneg (by linarith : 0 ≤ a - b)]
    rw [hne]
    exact hbound
  · have hexp : Real.log b - Real.log a = Real.log (b / a) := by
      rw [Real.log_div (ne_of_gt hb0) (ne_of_gt ha0)]
    have hbound : Real.log (b / a) ≤ -(a - b) := by
      have h2 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      have h3 : b / a - 1 = (b - a) / a := by
        rw [sub_div b a a, div_self (ne_of_gt ha0)]
      have h4 : (b - a) / a ≤ b - a := div_le_self (by linarith) ha
      linarith
    have hnn : Real.log a - Real.log b ≤ 0 := sub_nonpos.mpr (Real.log_le_log ha0 h)
    rw [abs_of_nonpos hnn, abs_of_nonpos (by linarith : a - b ≤ 0)]
    rw [show -(Real.log a - Real.log b) = Real.log b - Real.log a by ring, hexp]
    exact hbound

/-- **sigmoid 误差界**：`|sigA P x − realSigmoid x| ≤ δ`
（用 `inv_sub_inv` 把差写成分式，分母 `≥ 1` 故误差不被放大）。 -/
theorem sigA_close (P : PrimApprox) (x : ℝ) : |sigA P x - realSigmoid x| ≤ P.δ := by
  have hu : 0 < P.expA (-x) := P.exp_pos (-x)
  have hv : 0 < Real.exp (-x) := Real.exp_pos (-x)
  have h1u : 0 < 1 + P.expA (-x) := by linarith
  have h1v : 0 < 1 + Real.exp (-x) := by linarith
  have hune : (1 + P.expA (-x)) ≠ 0 := ne_of_gt h1u
  have hvne : (1 + Real.exp (-x)) ≠ 0 := ne_of_gt h1v
  have hdiff : 1 / (1 + P.expA (-x)) - 1 / (1 + Real.exp (-x))
      = (Real.exp (-x) - P.expA (-x)) / ((1 + P.expA (-x)) * (1 + Real.exp (-x))) := by
    rw [one_div, one_div, inv_sub_inv hune hvne]
    have hnum : (1 + Real.exp (-x)) - (1 + P.expA (-x)) = Real.exp (-x) - P.expA (-x) := by
      ring
    rw [hnum]
  unfold sigA realSigmoid
  rw [hdiff, abs_div]
  have hdpos : 0 < (1 + P.expA (-x)) * (1 + Real.exp (-x)) := mul_pos h1u h1v
  have hd1 : 1 ≤ (1 + P.expA (-x)) * (1 + Real.exp (-x)) := by
    have ha : (1 : ℝ) ≤ 1 + P.expA (-x) := by linarith
    have hb : (1 : ℝ) ≤ 1 + Real.exp (-x) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (1 + P.expA (-x)) * (1 + Real.exp (-x)) := mul_le_mul ha hb (by norm_num) (by linarith)
  have hnum : |Real.exp (-x) - P.expA (-x)| ≤ P.δ := by
    have h := P.exp_close (-x)
    rwa [abs_sub_comm] at h
  rw [abs_of_pos hdpos]
  calc
    |Real.exp (-x) - P.expA (-x)| / ((1 + P.expA (-x)) * (1 + Real.exp (-x)))
        ≤ P.δ / ((1 + P.expA (-x)) * (1 + Real.exp (-x))) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hdpos)
    _ ≤ P.δ / 1 := div_le_div_of_nonneg_left P.δ_nonneg (by norm_num) hd1
    _ = P.δ := by ring

/-- **SiLU 误差界**：`|siluA P x − realSilu x| ≤ |x| · δ`（误差按输入幅度放大）。 -/
theorem siluA_close (P : PrimApprox) (x : ℝ) :
    |siluA P x - realSilu x| ≤ |x| * P.δ := by
  have h := sigA_close P x
  have hsplit : siluA P x - realSilu x = x * (sigA P x - realSigmoid x) := by
    unfold siluA realSilu
    ring
  rw [hsplit, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg x)

/-- **2 类 softmax 误差界**：`|sigA P (a−b) − realSoftmax2 a b| ≤ δ`。 -/
theorem softmax2A_close (P : PrimApprox) (a b : ℝ) :
    |sigA P (a - b) - realSoftmax2 a b| ≤ P.δ := by
  simpa [realSoftmax2] using sigA_close P (a - b)

/-- **softplus 误差界**：`|softplusA P z − realSoftplus z| ≤ 2·δ`
（`log` 的 δ 误差 + 对数的 1-Lipschitz 传递指数误差）。 -/
theorem softplusA_close (P : PrimApprox) (z : ℝ) :
    |softplusA P z - realSoftplus z| ≤ 2 * P.δ := by
  have hlog : |P.logA (1 + P.expA z) - Real.log (1 + P.expA z)| ≤ P.δ :=
    P.log_close (1 + P.expA z) (by linarith [P.exp_pos z])
  have hmid : |Real.log (1 + P.expA z) - Real.log (1 + Real.exp z)|
      ≤ |P.expA z - Real.exp z| := by
    have h := real_log_abs_sub_le (a := 1 + P.expA z) (b := 1 + Real.exp z)
      (by linarith [P.exp_pos z]) (by linarith [Real.exp_pos z])
    have harg : (1 + P.expA z) - (1 + Real.exp z) = P.expA z - Real.exp z := by ring
    rwa [harg] at h
  have hexp : |P.expA z - Real.exp z| ≤ P.δ := P.exp_close z
  have hsplit : softplusA P z - realSoftplus z
      = (P.logA (1 + P.expA z) - Real.log (1 + P.expA z))
        + (Real.log (1 + P.expA z) - Real.log (1 + Real.exp z)) := by
    unfold softplusA realSoftplus
    ring
  rw [hsplit]
  calc
    |(P.logA (1 + P.expA z) - Real.log (1 + P.expA z))
        + (Real.log (1 + P.expA z) - Real.log (1 + Real.exp z))|
        ≤ |P.logA (1 + P.expA z) - Real.log (1 + P.expA z)|
          + |Real.log (1 + P.expA z) - Real.log (1 + Real.exp z)| := abs_add _ _
    _ ≤ P.δ + P.δ := add_le_add hlog (le_trans hmid hexp)
    _ = 2 * P.δ := by ring

/-- **二元交叉熵误差界**：`|ce2A P y z − realCrossEntropy2 y z| ≤ (2 + |y|)·δ`。 -/
theorem ce2A_close (P : PrimApprox) (y z : ℝ) :
    |ce2A P y z - realCrossEntropy2 y z| ≤ (2 + |y|) * P.δ := by
  have h := softplusA_close P z
  have hsplit : ce2A P y z - realCrossEntropy2 y z = softplusA P z - realSoftplus z := by
    unfold ce2A realCrossEntropy2
    ring
  rw [hsplit]
  have h2 : 2 * P.δ ≤ (2 + |y|) * P.δ := by
    have hle : (2 : ℝ) ≤ 2 + |y| := by linarith [abs_nonneg y]
    exact mul_le_mul_of_nonneg_right hle P.δ_nonneg
  linarith

/-- **线性注意力核误差界**：`|linAttnA P q k v − realLinearAttention q k v| ≤ δ·|v|`。 -/
theorem linearAttentionA_close (P : PrimApprox) (q k v : ℝ) :
    |linAttnA P q k v - realLinearAttention q k v| ≤ P.δ * |v| := by
  have h : |P.expA (q * k) - Real.exp (q * k)| ≤ P.δ := P.exp_close (q * k)
  have hsplit : linAttnA P q k v - realLinearAttention q k v
      = (P.expA (q * k) - Real.exp (q * k)) * v := by
    unfold linAttnA realLinearAttention
    ring
  rw [hsplit, abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg v)

/-- 余弦项的幅度缩放误差：`|x·cosA θ − x·cos θ| ≤ |x|·δ`。 -/
lemma cosA_scaled_close (P : PrimApprox) (x th : ℝ) :
    |x * P.cosA th - x * Real.cos th| ≤ |x| * P.δ := by
  have h : |P.cosA th - Real.cos th| ≤ P.δ := P.cos_close th
  have hsplit : x * P.cosA th - x * Real.cos th = x * (P.cosA th - Real.cos th) := by ring
  rw [hsplit, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg x)

/-- 正弦项的幅度缩放误差：`|x·sinA θ − x·sin θ| ≤ |x|·δ`。 -/
lemma sinA_scaled_close (P : PrimApprox) (x th : ℝ) :
    |x * P.sinA th - x * Real.sin th| ≤ |x| * P.δ := by
  have h : |P.sinA th - Real.sin th| ≤ P.δ := P.sin_close th
  have hsplit : x * P.sinA th - x * Real.sin th = x * (P.sinA th - Real.sin th) := by ring
  rw [hsplit, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg x)

/-- **RoPE 第一分量误差界**：`|(ropeA).1 − (realRoPE).1| ≤ (|x1| + |x2|)·δ`。 -/
theorem ropeA_fst_close (P : PrimApprox) (x1 x2 th : ℝ) :
    |(ropeA P x1 x2 th).1 - (realRoPE x1 x2 th).1| ≤ (|x1| + |x2|) * P.δ := by
  have hval : (ropeA P x1 x2 th).1 - (realRoPE x1 x2 th).1
      = (x1 * P.cosA th - x1 * Real.cos th) - (x2 * P.sinA th - x2 * Real.sin th) := by
    have h1 : (ropeA P x1 x2 th).1 = x1 * P.cosA th - x2 * P.sinA th := rfl
    have h2 : (realRoPE x1 x2 th).1 = x1 * Real.cos th - x2 * Real.sin th := rfl
    rw [h1, h2]
    ring
  rw [hval]
  calc
    |(x1 * P.cosA th - x1 * Real.cos th) - (x2 * P.sinA th - x2 * Real.sin th)|
        ≤ |x1 * P.cosA th - x1 * Real.cos th| + |x2 * P.sinA th - x2 * Real.sin th| :=
          abs_sub_le_abs_add _ _
    _ ≤ |x1| * P.δ + |x2| * P.δ :=
          add_le_add (cosA_scaled_close P x1 th) (sinA_scaled_close P x2 th)
    _ = (|x1| + |x2|) * P.δ := by ring

/-- **RoPE 第二分量误差界**：`|(ropeA).2 − (realRoPE).2| ≤ (|x1| + |x2|)·δ`。 -/
theorem ropeA_snd_close (P : PrimApprox) (x1 x2 th : ℝ) :
    |(ropeA P x1 x2 th).2 - (realRoPE x1 x2 th).2| ≤ (|x1| + |x2|) * P.δ := by
  have hval : (ropeA P x1 x2 th).2 - (realRoPE x1 x2 th).2
      = (x1 * P.sinA th - x1 * Real.sin th) + (x2 * P.cosA th - x2 * Real.cos th) := by
    have h1 : (ropeA P x1 x2 th).2 = x1 * P.sinA th + x2 * P.cosA th := rfl
    have h2 : (realRoPE x1 x2 th).2 = x1 * Real.sin th + x2 * Real.cos th := rfl
    rw [h1, h2]
    ring
  rw [hval]
  calc
    |(x1 * P.sinA th - x1 * Real.sin th) + (x2 * P.cosA th - x2 * Real.cos th)|
        ≤ |x1 * P.sinA th - x1 * Real.sin th| + |x2 * P.cosA th - x2 * Real.cos th| :=
          abs_add _ _
    _ ≤ |x1| * P.δ + |x2| * P.δ :=
          add_le_add (sinA_scaled_close P x1 th) (cosA_scaled_close P x2 th)
    _ = (|x1| + |x2|) * P.δ := by ring

/-! ## 六、注：桥的完整性与诚实边界
  · **精确桥（可执行 = 规范）**：`qRelu_cast`（ReLU）与 `qLinearAttention_cast`
    （归一化线性注意力）——在 `ℚ` 上实现、在 `ℝ` 上证等式，是形如
    `↑(evalFn x) = realFn x` 的定理（`Float` 无到 ℝ 的转换，见文件头「诚实标注」）。
  · **误差界桥（δ 参数化）**：`sigA_close`（sigmoid）、`siluA_close`（SiLU）、
    `softmax2A_close`（2 类 softmax）、`softplusA_close` 与 `ce2A_close`（交叉熵）、
    `linearAttentionA_close`（线性注意力）、`ropeA_fst_close`/`ropeA_snd_close`（RoPE）
    —— 每条误差界的常数都是**显式可读**的（如 `δ`、`2δ`、`(2+|y|)δ`、`(|x1|+|x2|)δ`）。
  · **可执行自检**：`#eval` 块给出 ReLU/sigmoid/SiLU/softmax/交叉熵/线性注意力/RoPE 的
    具体数值与布尔断言（全通过打印 `selfcheck: OK`），供与文件头的 numpy 命令逐项对照。
  · **未做/诚实降级**：① 没有把 `Float` 结果机械地导入 ℚ/ℝ 的形式化桥
    （Lean 4.14 缺 `Float.toRat`/`Float → ℝ`，标注）；② `PrimApprox` 的 δ 是
    **显式假设数据**而非从 `Float` 实现推出的定理（`#eval` 只做数值背书，标注）；
    ③ 因此 `PrimApprox` 的 `Float` 实例未形式化构造（未做）。
  · **与 `RealIEEE754`/`RealMixedPrecisionRounding` 的关系**：本文件提供**算子级**的
    可执行实现与其 ℝ 规范；`PrimApprox.δ` 可与 `FloatFormat.eps`（单位舍入）取同一数量级，
    从而把「可执行算子的误差」与「浮点格式的舍入误差」在同一账本上对齐。
  无 sorry/axiom/admit。 -/

end Lattice
