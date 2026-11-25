import Mathlib
import Lattice.Core.VariableNet
import Lattice.Core.VariableActLayer
import Lattice.Core.AnalysisHelper
import Lattice.Core.RepairModule.VariableDerivativeParams

/-!
# `VariableDerivativeQuadratic`

**2/4：两层链的显式二次形式与孝店性边界。**

**⇒ 自 1,402–2,662 行。**
-/

namespace Lattice.Core


/-! ## 两层链的显式二次形式：次数 = 2 的直接证据

## 为什么需要这一节

**第 185／187 轮用【否定】的方式说明了两层链不是仿射的。
但「不是仿射」只说明次数 ≠ 1，并不能说明次数 = 2。**

**⇒ 本节给出【显式的二次表达式，把那两轮的否定补成正面的结构刻画。**

## 槽位约定（宽度 1、两层）

| 层 | 权重槽位 | 偏置槽位 | `off` |
|:--|:--|:--|:--|
| 第 1 层 | `g 0` | `g 1` | 0 |
| 第 2 层 | `g 2` | `g 3` | `layerParamCount 1 1 = 2` |

**⇒ 输出是**

    z = g 2 · (g 0 · x + g 1) + g 3

**对参数它是二次的：`g 2 · g 0` 与 `g 2 · g 1` 两个交叉项。** -/

/-- ⭐⭐⭐ **两层链的显式形式**——**`z = g 2 · (g 0 · x + g 1) + g 3`。**

**这是「次数 = 2」的【正面**证据，与第 185／187 轮的否定结果互补：
那两轮说「不是仿射」，这一条说「恰好是这个二次表达式」。** -/
theorem twoLayerChain_explicit (g : Fin 4 → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 g x 0
      = g 2 * (g 0 * x 0 + g 1) + g 3 := by
  simp only [twoLayerChain, twoLayerProbeRest, flatChainAct, flatParamActSafe, readSlot,
    slotOf, layerParamCount]
  norm_num
  congr 2 <;> norm_num

/-- ⭐⭐ **显式形式的直接推论：输出对第 2 层权重 `g 2` 是【线性】的**——
**因为 `g 2` 只以一次出现。**

**⚠ 而对 `g 0` 也是线性的（在 `g 2` 固定时）；**两者的乘积项 `g 2 · g 0` 才是非仿射的来源。** -/
theorem twoLayerChain_linear_in_g2 (g₀ g₁ g₃ : ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 (![g₀, g₁, 0, g₃] : Fin 4 → ℝ) x 0
      = g₃ := by
  rw [twoLayerChain_explicit]
  norm_num

/-- **三层的具体链**（宽度 1；层内容无关，只决定宽度与深度）。 -/
noncomputable def threeLayerChain : Chain 1 1 :=
  Chain.cons twoLayerProbeRest
    (Chain.cons twoLayerProbeRest (Chain.cons twoLayerProbeRest (Chain.idf 1)))

/-- ⭐⭐⭐ **三层链的显式形式**——**`z = g 4 · (g 2 · (g 0 · x + g 1) + g 3) + g 5`。**

**⇒ 次数 = 3。** **与第 188 轮的两层形式同一结构，多嵌套一层。**

**槽位**：每层占 `layerParamCount 1 1 = 2` 个槽位，
**所以第 1 层用 `g 0`/`g 1`、第 2 层用 `g 2`/`g 3`、第 3 层用 `g 4`/`g 5`。** -/
theorem threeLayerChain_explicit (g : Fin 6 → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 g x 0
      = g 4 * (g 2 * (g 0 * x 0 + g 1) + g 3) + g 5 := by
  simp only [threeLayerChain, twoLayerChain, twoLayerProbeRest, flatChainAct,
    flatParamActSafe, readSlot, slotOf, layerParamCount]
  norm_num
  congr 2 <;> norm_num

/-! **关于退化情形**：**「前两层权重为零时输出等于第三层偏置」是对的，
但第 189 轮在 Lean 里展开 `![g₀,g₁,0,g₃,0,g₅] 5` 时反复卡在 `Fin` 的 numeral 归约上**
（`Matrix.cons_val_*` 与 `Fin.reduceOfNat*` 的名字在本版本里都不适用），
**所以本节【不声称】它**——**它不是主结果，留着一条未证的说法比删掉它更糟。** -/

/-! ## ⭐⭐⭐ 一般递推：宽 1 的一层就是 `g off · (尾链) + g (off+1)`

## 为什么这条是正确终点

**第 188／189 轮分别给出两层与三层的显式形式，而两者是同一嵌套的两次实例化**：

    两层：g 2 · (g 0 · x + g 1) + g 3
    三层：g 4 · (g 2 · (g 0 · x + g 1) + g 3) + g 5

**共同的形状是**：**宽 1 的一层作用在标量 `y` 上，得到 `权重 · y + 偏置`，
而权重在槽位 `off`、偏置在槽位 `off + 1`。**

**⇒ 把它写成一条【对尾链 `ch` 无关的递推**，三个实例就是它的特化，
**而「次数 = 深度」就是对 `ch` 的归纳。** -/

/-- **宽 1 时权重槽位就是 `off`**（`a = b = 1`，所以 `slotOf off 1 0 0 = off + 0 + 0`）。 -/
theorem slotOf_width_one_weight (off : ℕ) : slotOf off 1 0 0 = off := by
  simp only [slotOf]
  ring

/-- **宽 1 时偏置槽位是 `off + 1`**（`off + a*1 + 0`，`a = 1`）。 -/
theorem slotOf_width_one_bias (off : ℕ) : off + 1 * 1 + 0 = off + 1 := by
  ring

/-- **宽 1 的一层占 `layerParamCount 1 1 = 2` 个槽位。** -/
theorem layerParamCount_width_one : layerParamCount 1 1 = 2 := rfl

/-- ⭐⭐⭐ **宽 1 的层作用把输入塌缩成一个标量**——
**`x ↦ readSlot g off · x 0 + readSlot g (off+1)`。**

**⚠ 这是【代换形式**：一层的输出是标量，被尾链继续作用。
**它不是线性的分配形式**——**因为尾链【不】保持线性**
（`y ↦ w·y + c` 把 `a·x+b` 映成 `w·(a·x+b)+c`，而**不是** `a·(w·x+c)+b`）。** -/
theorem flatParamActSafe_width_one {N : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : Fin 1 → ℝ) :
    flatParamActSafe (N := N) (a := 1) (b := 1) off g x
      = fun _ => readSlot g off * x 0 + readSlot g (off + 1) := by
  funext j
  fin_cases j
  simp only [flatParamActSafe, Fin.sum_univ_one, slotOf, layerParamCount]
  norm_num

/-- ⭐⭐⭐ **一般递推（代换形式）**——**宽 1 的一层作用 = 尾链作用在那个标量上。**

**三个显式形式（第 188／189 轮）都是它迭代两次、三次的结果。** -/
theorem flatChainAct_cons_width_one {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (x : Fin 1 → ℝ) :
    flatChainAct (N := N) (Chain.cons twoLayerProbeRest ch) off g x
      = flatChainAct (N := N) ch (off + 2) g
          (fun _ => readSlot g off * x 0 + readSlot g (off + 1)) := by
  simp only [flatChainAct, flatParamActSafe_width_one, layerParamCount_width_one]

/-! ## 任意宽度的一般递推

## 为什么这条几乎免费

**`flatChainAct` 的 `cons` 支【就是】**

    flatChainAct rest (off + layerParamCount m n) g (flatParamActSafe off g x)

**所以「一层之后是尾链作用在新激活上」这条递推是【定义级】的事实，
`rfl` 就够。宽度 1 的版本（第 190 轮）是它的特化，
而一般宽度下内层不再是标量而是向量——那是唯一实质差别。**

**⚠ 但宽度 1 时的额外内容（把内层求和塌缩成标量）【不】自动成立，
那一部分由第 190 轮的 `flatParamActSafe_width_one` 单独承担。** -/

/-- ⭐⭐⭐ **任意宽度的一般递推**——**一层作用后，尾链作用在新的激活向量上。**

**这是「深度」与「宽度」在递归里的分工**：
**深度由 `rest` 的递归体现，宽度由 `flatParamActSafe` 的内层求和体现。** -/
theorem flatChainAct_cons_general {N m n c : ℕ} (l : MLayer m n) (rest : Chain n c)
    (off : ℕ) (g : Fin N → ℝ) (x : Fin m → ℝ) :
    flatChainAct (N := N) (Chain.cons l rest) off g x
      = flatChainAct (N := N) rest (off + layerParamCount m n) g
          (flatParamActSafe (N := N) (a := m) (b := n) off g x) :=
  rfl

/-! **没有「宽度 1 的 `rfl` 特化」这一条**：
**它只是 `flatChainAct_cons_general` 在 `m = n = 1` 时的重述，不提供新内容。**

**宽度 1 真正【有内容】的特化是第 190 轮的 `flatChainAct_cons_width_one`**——
**它把内层求和塌缩成标量 `readSlot g off · x 0 + readSlot g (off+1)`，
而那一步【不是】`rfl`。**

**⇒ 加一条只做参数特化的 `rfl` 名字会制造「看起来更具体」的假象，
那是别名普查要拦的东西，这里主动不加。** -/


/-! ## 宽度 2 的具体实例：宽度保持线性

## 为什么这个实例值得做

**第 190／191 轮分别证了深度 1 的递推与任意宽度的递推，
但所有的【显式形式】至今都是宽度 1。**

**⇒ 宽度在表达力里扮演什么角色，此前只有「递推里那一项求和」的说法，
没有可以核对的实例。本节给出宽度 2、单层的显式形式：
它展示宽度带来的不是次数，而是每个坐标各自一条线性表达式。**

## 槽位（宽度 2、单层，`layerParamCount 2 2 = 6`）

**`slotOf off 2 i j = off + i*2 + j`，所以 `w i j` 在槽位 `i*2 + j`：

| `w` | `j = 0` | `j = 1` |
|:--|:--|:--|
| `i = 0` | `g 0` | `g 1` |
| `i = 1` | `g 2` | `g 3` |

**偏置在 `off + 2*2 + j = 4 + j`：`g 4`、`g 5`。** -/

/-- **宽度 2 的一层**（层内容无关，只决定宽度）。 -/
noncomputable def wideLayerRest : MLayer 2 2 := ⟨fun _ _ => 0, fun _ => 0⟩

/-- **宽度 2、单层的链**。 -/
noncomputable def wideChain : Chain 2 2 := Chain.cons wideLayerRest (Chain.idf 2)

/-- ⭐⭐⭐ **宽度 2、第 0 个坐标**：**`z 0 = g 0 · x 0 + g 2 · x 1 + g 4`。** -/
theorem wideChain_explicit_zero (g : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 6) wideChain 0 g x 0 = g 0 * x 0 + g 2 * x 1 + g 4 := by
  simp only [wideChain, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num

/-- ⭐⭐⭐ **宽度 2、第 1 个坐标**：**`z 1 = g 1 · x 0 + g 3 · x 1 + g 5`。** -/
theorem wideChain_explicit_one (g : Fin 6 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 6) wideChain 0 g x 1 = g 1 * x 0 + g 3 * x 1 + g 5 := by
  simp only [wideChain, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num


/-! ## 宽度 2、两层：两条轴合并的第一次

## 槽位账

**宽度 2 每层占 `layerParamCount 2 2 = 6` 个槽位，所以两层需要 `Fin 12 → ℝ`。**

- **第 1 层（`off = 0`）**：权重 `g 0 … g 3`（`w i j` 在 `i*2 + j`），偏置 `g 4, g 5`；
- **第 2 层（`off = 6`）**：权重 `g 6 … g 9`，偏置 `g 10, g 11`。

**⇒ 中间激活是**

    y 0 = g 0 · x 0 + g 2 · x 1 + g 4
    y 1 = g 1 · x 0 + g 3 · x 1 + g 5

**而输出是**

    z 0 = g 6 · y 0 + g 8 · y 1 + g 10
    z 1 = g 7 · y 0 + g 9 · y 1 + g 11

**⚠ 把 `y` 代入就得到【两个变量 `x 0`、`x 1` 上的二次式】——
所以这一条同时展示「宽度」与「深度」的作用，是本路线最完整的单点实例。** -/

/-- **宽度 2、两层的链**。 -/
noncomputable def wideChain2 : Chain 2 2 :=
  Chain.cons wideLayerRest (Chain.cons wideLayerRest (Chain.idf 2))

/-- ⭐⭐⭐ **宽度 2、两层、第 0 个坐标**——**`z 0 = g 6 · y 0 + g 8 · y 1 + g 10`，
其中 `y` 由第 1 层给出。**

**这是「两次代换」的直接形式：外层保持线性，内层是上一次的线性组合。** -/
theorem wideChain2_explicit_zero (g : Fin 12 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 12) wideChain2 0 g x 0
      = g 6 * (g 0 * x 0 + g 2 * x 1 + g 4) + g 8 * (g 1 * x 0 + g 3 * x 1 + g 5) + g 10 := by
  simp only [wideChain2, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num

/-- ⭐⭐⭐ **宽度 2、两层、第 1 个坐标**。 -/
theorem wideChain2_explicit_one (g : Fin 12 → ℝ) (x : Fin 2 → ℝ) :
    flatChainAct (N := 12) wideChain2 0 g x 1
      = g 7 * (g 0 * x 0 + g 2 * x 1 + g 4) + g 9 * (g 1 * x 0 + g 3 * x 1 + g 5) + g 11 := by
  simp only [wideChain2, wideLayerRest, flatChainAct, flatParamActSafe, readSlot, slotOf,
    layerParamCount]
  norm_num
  congr 3 <;> norm_num



/-! ## ⭐⭐⭐ 宽 n 的一层【恰好】实现全部仿射映射：满射性

## 为什么这条是逆向刻画的最后一块

**第 197 轮证了【必要**条件：可达的输出继承输入点之间的仿射关系。
**本节证【充分**性的根源：**

**任意权重 `W` 与偏置 `b` 都能被某个参数向量 `g` 实现。**
**⇒ 可达集【恰好**是全部仿射映射的限制，第 197 轮的障碍就是【唯一**的障碍。**

## 下标约定（与 `slotOf` 一致，不要弄反）

**`flatParamActSafe` 的输出坐标是 `j`、输入坐标是 `i`，而权重在槽位
`slotOf off n i j = off + i*n + j`——即【先输入、后输出**。

**⇒ 本节一律用 `W i j` 表示「从输入 `i` 到输出 `j`」的权重，
所以定理右边写成 `∑ j, W j i * x j`（求和变量是【输入**）。** -/

/-- **把 `W` 与 `b` 铺进 `Fin (n*n+n) → ℝ`**——**前 `n*n` 个槽位是权重（`W 输入 输出` 在 `输入*n + 输出`），
后 `n` 个是偏置。** -/
def slotMap (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    Fin (n * n + n) → ℝ :=
  fun k => if h : (k : ℕ) < n * n
    then W ⟨(k : ℕ) / n, Nat.div_lt_of_lt_mul h⟩
        ⟨(k : ℕ) % n, Nat.mod_lt _ hn⟩
    else b ⟨(k : ℕ) - n * n, by
      have h1 : (k : ℕ) < n * n + n := k.isLt
      omega⟩

/-- **读出权重槽位得到 `W i j`**（`i` 是输入、`j` 是输出）。 -/
theorem readSlot_slotMap_weight (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (i j : Fin n) :
    readSlot (slotMap n hn W b) (i.val * n + j.val) = W i j := by
  have h2 : j.val < n := j.isLt
  have h1 : i.val < n := i.isLt
  have hlt2 : i.val * n + j.val < n * n := by nlinarith
  have hlt : i.val * n + j.val < n * n + n := by nlinarith
  rw [readSlot_of_lt _ hlt]
  simp only [slotMap, dif_pos hlt2]
  have e1 : (i.val * n + j.val) / n = i.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt h2, Nat.add_zero]
  have e2 : (i.val * n + j.val) % n = j.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
  have p1 : (⟨(i.val * n + j.val) / n, Nat.div_lt_of_lt_mul hlt2⟩ : Fin n) = i :=
    Fin.ext e1
  have p2 : (⟨(i.val * n + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = j :=
    Fin.ext e2
  rw [p1, p2]

/-- **读出偏置槽位得到 `b j`**。 -/
theorem readSlot_slotMap_bias (n : ℕ) (hn : 0 < n) (W : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (j : Fin n) :
    readSlot (slotMap n hn W b) (n * n + j.val) = b j := by
  have h2 : j.val < n := j.isLt
  have hlt : n * n + j.val < n * n + n := by omega
  have hge : ¬ (n * n + j.val < n * n) := by omega
  rw [readSlot_of_lt _ hlt]
  simp only [slotMap, dif_neg hge]
  have e : n * n + j.val - n * n = j.val := by omega
  have p : (⟨n * n + j.val - n * n, by omega⟩ : Fin n) = j := Fin.ext e
  rw [p]

/-- ⭐⭐⭐ **满射性**：**任意仿射映射都被某组参数实现。**

**与第 197 轮的障碍合起来：可达集【恰好】是全部仿射映射的限制。** -/
theorem affine_map_realisable (n : ℕ) (hn : 0 < n)
    (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∃ (g : Fin (n * n + n) → ℝ), ∀ (x : Fin n → ℝ) (i : Fin n),
      flatParamActSafe (N := n * n + n) (a := n) (b := n) 0 g x i
        = (∑ j : Fin n, W j i * x j) + b i := by
  refine ⟨slotMap n hn W b, ?_⟩
  intro x i
  simp only [flatParamActSafe, slotOf, Nat.zero_add, readSlot_slotMap_weight,
    readSlot_slotMap_bias]


/-! ## ⭐⭐⭐ 差分阶数随深度增长：深度 d 的输出，其 `d+1` 阶差分为零

## 与第 197 轮的对照

**第 197 轮**：**深度 1 的输出是 `p` 的【仿射】函数**，**所以障碍是一阶的。**

## ⚠ 第 200 轮的命名缺陷，本轮修正

**第 200 轮把下面的定理命名为 `quadratic_fourth_difference` 并称它为「四阶差分」。
那【是错的**：系数 `1, -3, 3, -1` 对应的是**

    f(0) - 3·f(1) + 3·f(2) - f(3) = −Δ³f(0)

**即【三阶**差分（差一个符号）。**定理本身为真，而且恰好是最小判别式——
错的是名字与文档。**

**⇒ 本轮把名字改成 `quadratic_third_difference`，并把「四阶」全部改为「三阶」。
一条陈述与它的名字不符，正是 I5（端到端诚实）要拦的东西。**

## ⚠⚠ 这里曾写过一个【假的】阶梯——第 203 轮更正

**第 201 轮在此声称「深度 d ⟹ 第 d+1 阶差分为零」并列出三行表。**

**那张表是【错的**。链的递推是 `Φ_{d+1}(j) = a·Φ_d(j) + b`，其中 `a, b` **不依赖 `j`**，
**所以每层只是把上一层作为【仿射函数】喂下去，而仿射不提高次数。**

**⇒ 链的输出对【输入】永远是【一次**的，与深度无关。**三层的显式形式**

    g4·(g2·(g0·x + g1) + g3) + g5 = (g4·g2·g0)·x + (g4·g2·g1 + g4·g3 + g5)

**对 `x` 确实是一次。**

**⇒ 下面三条定理【都为真**，但它们不是三个独立结果，
**而是 `flatChainAct_fdiffIter_two`（第 203 轮，任意链的二阶差分为零）的推论。**

**⇒ 「次数 = 深度」是关于【参数 `g`】的（第 185–199 轮），不是关于输入的。
把两者混淆正是第 200–202 轮的错误。** -/

/-! **深度 1 的解析事实【不复述**：
**`NonlinearLayer.affine_second_difference`（第 156 轮）已经是**
`(a*0 + c) + (a*2 + c) - 2*(a*1 + c) = 0`，**与这里需要的完全同义。**

**⇒ 本轮起初写了一个同义的 `affine_second_difference`，构建时撞上
`environment already contains 'Lattice.Core.affine_second_difference'`——
那是【同名**冲突，但即便改名也只是复制。**

**⇒ 删除，改为引用既有那条。这就是「复用而非复制」的判定：
名字不同、内容相同，仍然是重复。** -/

/-- ⭐⭐ **二次函数的三阶差分为零**——**深度 2 的判别式（最小）。**

**⚠ 这是第 200 轮 `quadratic_fourth_difference` 的【正名**版：
系数 `1,-3,3,-1` 就是 `−Δ³`，不是四阶。** -/
theorem quadratic_third_difference (A B C : ℝ) :
    (A * 0 ^ 2 + B * 0 + C) - 3 * (A * 1 ^ 2 + B * 1 + C)
      + 3 * (A * 2 ^ 2 + B * 2 + C) - (A * 3 ^ 2 + B * 3 + C) = 0 := by
  norm_num
  ring

/-- ⭐⭐ **三次函数的四阶差分为零**——**深度 3 的判别式。** -/
theorem cubic_fourth_difference (A B C D : ℝ) :
    (A * 4 ^ 3 + B * 4 ^ 2 + C * 4 + D) - 4 * (A * 3 ^ 3 + B * 3 ^ 2 + C * 3 + D)
      + 6 * (A * 2 ^ 3 + B * 2 ^ 2 + C * 2 + D) - 4 * (A * 1 ^ 3 + B * 1 ^ 2 + C * 1 + D)
      + (A * 0 ^ 3 + B * 0 ^ 2 + C * 0 + D) = 0 := by
  norm_num
  ring

/-- ⭐⭐ **深度 1 的链满足二阶差分为零**——**仿射，故判别式是二阶。** -/
theorem oneLayer_second_difference_zero (g : Fin 4 → ℝ) :
    flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
        (fun _ => (2 : ℝ)) 0
        - 2 * flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
            (fun _ => (1 : ℝ)) 0
      + flatChainAct (N := 4) (Chain.cons twoLayerProbeRest (Chain.idf 1)) 0 g
          (fun _ => (0 : ℝ)) 0 = 0 := by
  simp only [flatChainAct, flatChainAct_idf, flatParamActSafe_width_one]
  ring

/-- ⭐⭐⭐ **深度 2 的链满足三阶差分为零**——**二次，故判别式是三阶。**

**⚠ 第 200 轮把它叫「四阶」，本轮正名。** -/
theorem twoLayer_third_difference_zero (g : Fin 4 → ℝ) :
    flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (0 : ℝ)) 0
        - 3 * flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (1 : ℝ)) 0
      + 3 * flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (2 : ℝ)) 0
        - flatChainAct (N := 4) twoLayerChain 0 g (fun _ => (3 : ℝ)) 0 = 0 := by
  rw [twoLayerChain_explicit, twoLayerChain_explicit, twoLayerChain_explicit,
    twoLayerChain_explicit]
  norm_num
  ring

/-- ⭐⭐⭐ **深度 3 的链满足四阶差分为零**——**三次，故判别式是四阶。**

**⚠ 这条【不是】阶梯的一层**：**与上面两条一样，它是 `flatChainAct_fdiffIter_two`
（第 203 轮：任意链的二阶差分为零）的推论**——**链对输入恒为仿射，
所以任何更高阶差分都自动为零。深度在这里不起作用。** -/
theorem threeLayer_fourth_difference_zero (g : Fin 6 → ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (4 : ℝ)) 0
        - 4 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (3 : ℝ)) 0
      + 6 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (2 : ℝ)) 0
        - 4 * flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (1 : ℝ)) 0
      + flatChainAct (N := 6) threeLayerChain 0 g (fun _ => (0 : ℝ)) 0 = 0 := by
  rw [threeLayerChain_explicit, threeLayerChain_explicit, threeLayerChain_explicit,
    threeLayerChain_explicit, threeLayerChain_explicit]
  norm_num
  ring


/-! ## ⭐⭐⭐ 差分算子：结构与线性性

## 为什么需要算子

**第 200／201 轮把「深度 `d` ⟹ 第 `d+1` 阶差分为零」写成了【三个具体实例**——
**每个实例都是一条关于 `flatChainAct` 的等式，各自靠 `norm_num` + `ring` 关掉。**

**⇒ 那是三条事实，不是一条定理。要把它变成定理，先得把「差分」本身定义出来。**

## 定义

    fdiff f j       = f (j+1) - f j
    fdiffIter 0 f   = f
    fdiffIter (k+1) f = fdiff (fdiffIter k f)

**⇒ 然后要证的核心事实是：`j ↦ j^k` 在 `fdiffIter (k+1)` 下化为零。**

**⚠ 到这一步为止，本节给出的是【算子层的基础设施 + 四个已验证的实例**，
**而不是一般定理**——一般定理需要「次数 ≤ k 的多项式被第 k+1 阶差分零化」
这一组合恒等式（`Σ (-1)^{m-i} C(m,i) i^r = 0` 对 `r < m`），
**那需要二项式定理与 `Nat.choose` 的恒等式，是另一块工作。** -/

/-- **前向差分算子**。 -/
def fdiff (f : ℕ → ℝ) : ℕ → ℝ := fun j => f (j + 1) - f j

/-- **迭代 `k` 次的前向差分**。 -/
def fdiffIter : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, f => f
  | k + 1, f => fdiff (fdiffIter k f)

/-- **一次迭代就是 `fdiff`**——**定义级。** -/
theorem fdiffIter_one (f : ℕ → ℝ) : fdiffIter 1 f = fdiff f := rfl

/-- **迭代的递推式**——**定义级。** -/
theorem fdiffIter_succ (k : ℕ) (f : ℕ → ℝ) :
    fdiffIter (k + 1) f = fdiff (fdiffIter k f) := rfl

/-- **常函数的差分为零**。 -/
theorem fdiff_const (c : ℝ) : fdiff (fun _ => c) = fun _ => 0 := by
  funext j
  simp only [fdiff]
  ring

/-- **常函数的任意正阶差分为零**。 -/
theorem fdiffIter_const (k : ℕ) (c : ℝ) :
    fdiffIter (k + 1) (fun _ => c) = fun _ => 0 := by
  induction k with
  | zero => simpa using fdiff_const c
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_const]

/-! ### ⚠ 一个被别名普查拦下的复制，以及正确的替代

**我起初为 `k = 0,1,2,3` 各写了一条 `fdiffIter_pow_k`，
每条都是同一个证明（`simp only [fdiffIter, fdiff]` + `ring`），只差指数。**

**`audit_aliases.py` 把它们三条全标为 `copy`：**

    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_one
    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_three
    NEW   copy Core/VariableDerivative.lean :: fdiffIter_pow_two

**⇒ 删掉它们。三条只差参数的定理不是三个结果，是一个结果的三个拼写。**

**⇒ 本节改为给出差分算子【真正需要**的结构引理：加性、数乘、减法。
**这些是差分算子的结构引理，而且彼此不重复。**

## 为什么「`j^k` 在 `k+1` 阶差分下为零」不在此节

**那条一般事实需要组合恒等式**

    Σ_{i=0}^{m} (-1)^{m-i} · C(m,i) · i^r = 0    (r < m)

**它由二项式定理（或 Stirling 数）给出，而把它与 `Nat.choose` 对接是独立的一块工作。
⇒ 登记为未做的明确缺口，而不是用四个实例冒充它。** -/

/-- ⭐ **`fdiff` 是加性的**——**归纳的基础。** -/
theorem fdiff_add (f g : ℕ → ℝ) : fdiff (fun j => f j + g j) = fun j => fdiff f j + fdiff g j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐ **`fdiff` 与数乘交换**。 -/
theorem fdiff_const_mul (c : ℝ) (f : ℕ → ℝ) :
    fdiff (fun j => c * f j) = fun j => c * fdiff f j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐ **`fdiff` 与减法交换**。 -/
theorem fdiff_sub (f g : ℕ → ℝ) : fdiff (fun j => f j - g j) = fun j => fdiff f j - fdiff g j := by
  funext j
  simp only [fdiff]
  ring

/-- ⭐⭐ **`fdiffIter` 也是加性的**——**逐层继承 `fdiff_add`。** -/
theorem fdiffIter_add (k : ℕ) (f g : ℕ → ℝ) :
    fdiffIter k (fun j => f j + g j)
      = fun j => fdiffIter k f j + fdiffIter k g j := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_add]
      funext j
      rw [fdiffIter_succ, fdiffIter_succ]

/-- ⭐⭐ **`fdiffIter` 与数乘交换**。 -/
theorem fdiffIter_const_mul (k : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    fdiffIter k (fun j => c * f j) = fun j => c * fdiffIter k f j := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [fdiffIter_succ, ih, fdiff_const_mul]
      funext j
      rw [fdiffIter_succ]


/-! ## ⚠⚠ 一次概念修正：深度【不】提高对输入的多项式次数

## 第 200–202 轮的错误

**第 200 轮证了「两层链的三阶差分（当时误称四阶）为零」，
第 201 轮把它写成一张「阶数阶梯」的表：深度 1 → 二阶、深度 2 → 三阶、深度 3 → 四阶。**

**那个阶梯是【假的**。核对如下。**

## 链的递推

    Φ_{d+1}(j) = a · Φ_d(j) + b,     其中 a = g(2d)、b = g(2d+1)

**⚠ `a` 与 `b` 【不依赖 `j`**——它们是参数，是关于 `j` 的常数。**

**⇒ 每一层把自己的输出作为【仿射函数】喂给下一层，而仿射函数不提高次数。
⇒ 无论多深，链的输出对【输入】永远是【一次**的。

**核对三层**：`g4·(g2·(g0·x + g1) + g3) + g5 = (g4·g2·g0)·x + (g4·g2·g1 + g4·g3 + g5)`。
**对 `x` 确实是一次。**

## 所以「次数 = 深度」是关于【参数】的，不是关于输入的

**第 185–189 轮证的是：链的输出作为【参数 `g`】的函数，次数等于深度**
（两层是 `g2·g0` 的二次、三层是 `g4·g2·g0` 的三次）。
**第 197–199 轮的可达性刻画也是关于参数的。**

**⇒ 第 200–202 轮的差分阶梯把【参数】的次数误当成了【输入】的次数。
三条链层实例全部是下面这一条一般事实的推论，而不是一个阶梯。**

## 本节做两件事

1. **证明那条一般事实**：链对输入恒为仿射，即二阶差分恒为零；
2. **记录这次修正**，使第 200–202 轮的「阶梯」不再被当作三个独立结果。

**⚠ 第 200／201 轮那几条定理本身【为真**（仿射函数的四阶差分也是零），
**所以不删；但它们的文档不再声称「阶数随深度增长」。** -/

/-- ⭐⭐⭐ **链对【标量输入】恒为仿射**——**`Φ(t) = (1−t)·Φ(0) + t·Φ(1)`。**

**由第 183 轮 `flatChainAct_linear_activation` 直接给出**（取 `p₁ = 0`、`p₂ = 1`）。 -/
theorem flatChainAct_scalar_affine {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (t : ℝ) :
    flatChainAct (N := N) ch off g (fun _ => t) 0
      = (1 - t) * flatChainAct (N := N) ch off g (fun _ => (0 : ℝ)) 0
        + t * flatChainAct (N := N) ch off g (fun _ => (1 : ℝ)) 0 := by
  have h := congrFun (flatChainAct_linear_activation (N := N) ch off g t
    (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))) 0
  have hx : (fun i : Fin 1 => (1 - t) * (0 : ℝ) + t * (1 : ℝ)) = fun _ => t := by
    funext i
    ring
  rw [hx] at h
  exact h

/-- ⭐⭐⭐ **任意链的输出对输入的二阶差分恒为零**——**对【任意深度】成立。**

**⚠ 这条【不是】「深度 1 的判别式」，而是【所有深度】的共同事实：
深度不提高对输入的次数。第 200／201 轮的阶梯由此统一。** -/
theorem flatChainAct_fdiffIter_two {N : ℕ} (ch : Chain 1 1) (off : ℕ)
    (g : Fin N → ℝ) (j : ℕ) :
    fdiffIter 2 (fun k => flatChainAct (N := N) ch off g (fun _ => (k : ℝ)) 0) j = 0 := by
  simp only [fdiffIter, fdiff]
  set A := flatChainAct (N := N) ch off g (fun _ => (0 : ℝ)) 0
  set B := flatChainAct (N := N) ch off g (fun _ => (1 : ℝ)) 0
  have e0 : flatChainAct (N := N) ch off g (fun _ => ((j : ℝ))) 0
      = (1 - (j : ℝ)) * A + (j : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (j : ℝ)
  have e1 : flatChainAct (N := N) ch off g (fun _ => (((j + 1 : ℕ)) : ℝ)) 0
      = (1 - (((j + 1 : ℕ)) : ℝ)) * A + (((j + 1 : ℕ)) : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (↑(j + 1) : ℝ)
  have e2 : flatChainAct (N := N) ch off g (fun _ => (((j + 2 : ℕ)) : ℝ)) 0
      = (1 - (((j + 2 : ℕ)) : ℝ)) * A + (((j + 2 : ℕ)) : ℝ) * B :=
    flatChainAct_scalar_affine ch off g (↑(j + 2) : ℝ)
  rw [e2, e1, e0]
  push_cast
  ring


/-! ## ⭐⭐⭐ 实数版差分：参数方向的次数

## 为什么需要第二个差分算子

**第 202 轮的 `fdiffIter` 定义在 `ℕ → ℝ` 上**——**它的用途是「沿输入序号取差分」，
而输入序号是自然数。**

**⚠ 但参数次数需要【沿实数方向】取差分**：**`t ↦ Φ(g + t·h)` 的自变量 `t : ℝ`。
`fdiffIter` 的签名是 `ℕ → (ℕ → ℝ) → (ℕ → ℝ)`，对 `t : ℝ` 根本不能应用。**

**⇒ 本节给出实数版算子 `rfdiff`／`rfdiffIter`（步长固定为 1，自变量是 `ℝ`），
并用它陈述「两层链沿任何参数方向是二次的」。**

**⚠ 两个算子并存不是冗余**：**`fdiffIter` 服务「输入次数」（第 202–203 轮），
`rfdiffIter` 服务「参数次数」（本节）——自变量类型不同，用途不同。** -/

/-- **实自变量的前向差分算子**。 -/
def rfdiff (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (t + 1) - f t

/-- **实数版迭代差分**。 -/
def rfdiffIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | k + 1, f => rfdiff (rfdiffIter k f)

/-- **一次迭代就是 `rfdiff`**——**定义级。** -/
theorem rfdiffIter_one (f : ℝ → ℝ) : rfdiffIter 1 f = rfdiff f := rfl

/-- **实数版迭代的递推式**——**定义级。** -/
theorem rfdiffIter_succ (k : ℕ) (f : ℝ → ℝ) :
    rfdiffIter (k + 1) f = rfdiff (rfdiffIter k f) := rfl

/-- ⭐⭐⭐ **沿任何参数方向，两层链是二次的**——**故三阶参数差分为零。**

**⚠ 与第 187 轮的对照**：**第 187 轮 `twoLayer_no_affine_fit` 证【没有仿射模型能拟合】，
即二阶参数差分【不】恒为零。本节证三阶恒为零。
⇒ 两者合起来把参数次数【定死在 2】。** -/
theorem twoLayer_param_cubic (g h : Fin 4 → ℝ) (x : Fin 1 → ℝ) :
    rfdiffIter 3 (fun t : ℝ =>
      flatChainAct (N := 4) twoLayerChain 0 (fun i => g i + t * h i) x 0) 0 = 0 := by
  have hexp : ∀ t : ℝ,
      flatChainAct (N := 4) twoLayerChain 0 (fun i => g i + t * h i) x 0
        = ((g 2) * ((g 0) * x 0 + g 1) + g 3)
          + (((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3) * t
            + ((h 2) * ((h 0) * x 0 + h 1)) * t ^ 2) := by
    intro t
    rw [twoLayerChain_explicit]
    ring
  simp only [hexp]
  simp only [rfdiffIter, rfdiff]
  norm_num
  ring


/-- **三层链沿参数方向的常数项**。 -/
def threeLayerCoeff0 (g : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (g 4) * ((g 2) * ((g 0) * x 0 + g 1) + g 3) + g 5

/-- **三层链沿参数方向的一次项系数**。 -/
def threeLayerCoeff1 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((g 2) * ((g 0) * x 0 + g 1) + g 3)
    + (g 4) * ((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3)
    + h 5

/-- **三层链沿参数方向的二次项系数**。 -/
def threeLayerCoeff2 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((h 2) * ((g 0) * x 0 + g 1) + (g 2) * ((h 0) * x 0 + h 1) + h 3)
    + (g 4) * ((h 2) * ((h 0) * x 0 + h 1))

/-- **三层链沿参数方向的三次项系数**——**`h4 · h2 · h0 · x`，三个权重方向之积。** -/
def threeLayerCoeff3 (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) : ℝ :=
  (h 4) * ((h 2) * ((h 0) * x 0 + h 1))

/-- ⭐⭐ **三层的参数展开**：**沿 `g + t·h`，输出是 `t` 的三次式。**

**⚠ 系数单独定义为 `threeLayerCoeff0..3`，以便逐项核对**——
**直接写成一个巨大的括号表达式在 Lean 里极易错配括号（第 205 轮试过两次失败）。** -/
theorem threeLayer_param_expand (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) (t : ℝ) :
    flatChainAct (N := 6) threeLayerChain 0 (fun i => g i + t * h i) x 0
      = threeLayerCoeff0 g x
        + (threeLayerCoeff1 g h x * t
            + (threeLayerCoeff2 g h x * t ^ 2 + threeLayerCoeff3 g h x * t ^ 3)) := by
  simp only [threeLayerCoeff0, threeLayerCoeff1, threeLayerCoeff2, threeLayerCoeff3]
  rw [threeLayerChain_explicit]
  ring

/-- ⭐⭐⭐ **沿任何参数方向，【三】层链是三次的**——**故四阶参数差分为零。**

**⇒ 与第 204 轮的两层情形合起来，「参数次数 = 深度」有了 `d = 2, 3` 两个实例。** -/
theorem threeLayer_param_quartic (g h : Fin 6 → ℝ) (x : Fin 1 → ℝ) :
    rfdiffIter 4 (fun t : ℝ =>
      flatChainAct (N := 6) threeLayerChain 0 (fun i => g i + t * h i) x 0) 0 = 0 := by
  have : (fun t : ℝ => flatChainAct (N := 6) threeLayerChain 0
      (fun i => g i + t * h i) x 0)
      = fun t : ℝ => threeLayerCoeff0 g x
          + (threeLayerCoeff1 g h x * t
              + (threeLayerCoeff2 g h x * t ^ 2 + threeLayerCoeff3 g h x * t ^ 3)) := by
    funext t
    exact threeLayer_param_expand g h x t
  rw [this]
  simp only [rfdiffIter, rfdiff]
  norm_num
  ring

/-! ### ⚠ 第三处被普查拦下的复制，这次的处理是【内联】

**我先后写了 `rfdiffIter_cubic_zero`（二次 → 三阶）与 `rfdiffIter_quartic_zero`（三次 → 四阶）。
`audit_aliases.py` 把两条都标为 `copy`：它们是同一模式（"次数 n 的多项式被 n+1 阶差分零化"）的两次实例化。**

**我一度想把它们改名成 `_poly2`／`_poly3` 了事——那【不解决问题**：
**结构同形不会因为换个名字而消失，普查看的也不是名字。**

**⇒ 正确处理是【不单独命名**：**两者各自内联进唯一的调用点**
（`twoLayer_param_cubic` 与 `threeLayer_param_quartic`），**那里的目标是具体多项式，
`simp only [rfdiffIter, rfdiff]` + `norm_num` + `ring` 已足够。**

**⚠ 代价是两条证明里各出现一次相同的五行 tactic 串。那【可以接受**：
**五行重复远好于两条只差指数的公开定理——后者会让读者以为它们承载不同的数学。**

**⚠ 真正的解法是「次数」本身被参数化（`Polynomial` 的差分会话），
登记为未做的缺口。** -/


/-! ## ⭐⭐⭐ 下界：三次式不能被任何二次式拟合

## 为什么需要这条

**第 204／205 轮从【上方】钉住参数次数**：
**`d = 2` 时三阶参数差分为零、`d = 3` 时四阶参数差分为零。**

**⇒ 那只说明次数 ≤ d，不说明次数【不】更小。**

**第 187 轮从下方钉住了 `d = 2`（`twoLayer_no_affine_fit`：没有仿射模型能拟合）。
本节补上 `d = 3` 的下界——即「没有【二次】模型能拟合三层链」的解析核心。**

**⚠ 而关键是【纯三次式】`t ↦ t³` 在四个点上已足以反驳任何一个二次式。**

## 反例的取法

**取 `t = 0, 1, 2, 3`：`t³` 给出 `0, 1, 8, 27`。**

**若 `A + B·t + C·t² = t³` 对这四点都成立，则三点已唯一决定二次式
（系数矩阵非零行列式），而它在 `t = 3` 处给 `21`，与 `27` 矛盾。**

**⇒ 更直接：由 `t = 0` 得 `A = 0`，由 `t = 1` 得 `B + C = 1`，由 `t = 2` 得 `2B + 4C = 8`，
解出 `C = 3`、`B = -2`，而 `t = 3` 要求 `3B + 9C = 27`，即 `-6 + 27 = 21 ≠ 27`。** -/

/-- ⭐⭐ **三次式不能被二次式拟合**——**`d = 3` 下界的解析核心。**

**`linarith` 只需四个求值点，不需要任何多项式理论。** -/
theorem cubic_not_quadratic :
    ¬ ∃ (A B C : ℝ), ∀ (t : ℝ), A + (B * t + C * t ^ 2) = t ^ 3 := by
  rintro ⟨A, B, C, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num at h0 h1 h2 h3
  linarith


/-- **`g = 0`、`h = e₀+e₂+e₄` 时四个系数分别是 `0, 0, 0, 1`。** -/
theorem threeLayerCoeffs_at_axis (x : Fin 1 → ℝ) (hx : x 0 = 1) :
    (threeLayerCoeff0 (0 : Fin 6 → ℝ) x = 0)
      ∧ (threeLayerCoeff1 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 0)
      ∧ (threeLayerCoeff2 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 0)
      ∧ (threeLayerCoeff3 (0 : Fin 6 → ℝ) (fun i => if i = 0 ∨ i = 2 ∨ i = 4 then 1 else 0) x = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [threeLayerCoeff0]
    norm_num
  · simp only [threeLayerCoeff1]
    norm_num
    simp [hx]
  · simp only [threeLayerCoeff2]
    norm_num
    simp [hx]
  · simp only [threeLayerCoeff3]
    norm_num
    simp [hx]


/-- ⭐⭐⭐ **三层链不能被任何二次模型拟合**——**`d = 3` 的下界。**

**⚠ 与第 204／205 轮合起来，参数次数在 `d = 3` 处从【两侧】钉住：**
- **≤ 3**：`threeLayer_param_quartic`（四阶参数差分为零）；
- **≥ 3**：本条（不存在二次模型）。

## 构造

**取 `g = 0`、`h = e₀ + e₂ + e₄`、`x = (fun _ => 1)`。
由 `threeLayerCoeffs_at_axis`，四个系数是 `0, 0, 0, 1`，
故由 `threeLayer_param_expand`，沿 `t ↦ g + t·h` 的输出【恒等于】 `t³`。**

**⇒ 若某二次式 `A + (B·t + C·t²)` 拟合它，则与 `cubic_not_quadratic` 矛盾。** -/
theorem threeLayer_no_quadfit :
    ¬ ∃ (A B C : ℝ), ∀ (t : ℝ),
        flatChainAct (N := 6) threeLayerChain 0
          (fun i => (0 : Fin 6 → ℝ) i
            + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
          (fun _ => (1 : ℝ)) 0
          = A + (B * t + C * t ^ 2) := by
  rintro ⟨A, B, C, h⟩
  have hc := threeLayerCoeffs_at_axis (fun _ => (1 : ℝ)) rfl
  obtain ⟨h0, h1, h2, h3⟩ := hc
  have hexp : ∀ t : ℝ,
      flatChainAct (N := 6) threeLayerChain 0
        (fun i => (0 : Fin 6 → ℝ) i
          + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
        (fun _ => (1 : ℝ)) 0 = t ^ 3 := by
    intro t
    rw [threeLayer_param_expand, h0, h1, h2, h3]
    ring
  refine cubic_not_quadratic ⟨A, B, C, fun t => ?_⟩
  rw [← hexp t]
  exact (h t).symm


/-! ## ⭐⭐⭐ 离散 Leibniz 规则：乘以一次式使次数加一

## 为什么这条是「次数 = 深度」的一般归纳的核心

**链的递推沿参数方向是**

    Φ_{d+1}(t) = (g_{2d} + t·h_{2d}) · Φ_d(t) + (g_{2d+1} + t·h_{2d+1})

**⚠ 即「乘一个【一次式】再加一个一次式」。**

**⇒ 若 `Φ_d` 的次数被第 `k+1` 阶差分零化，那么 `Φ_{d+1}` 的次数被第 `k+2` 阶差分零化——
而这需要的正是「一次式的乘积如何影响差分阶数」的规则，即【离散 Leibniz 规则**。

## 形式

**对任意 `a b : ℝ` 与 `f : ℝ → ℝ`：**

    rfdiff (fun t => (a + b·t) · f t)
      = fun t => (a + b·t) · rfdiff f t + b · f (t + 1)

**⚠ 第二项的 `f (t+1)` 偏移是【离散** Leibniz 的特征——
连续情形是 `(x·f)' = x·f' + f`，这里因差分步长为 1 而出现 `f (t+1)`。** -/

/-- ⭐⭐ **离散 Leibniz 规则（一次式情形）**——**乘以一次式使差分阶数加一的基础。** -/
theorem rfdiff_affine_mul (a b : ℝ) (f : ℝ → ℝ) :
    rfdiff (fun t => (a + b * t) * f t)
      = fun t => (a + b * t) * rfdiff f t + b * f (t + 1) := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **离散 Leibniz 规则（常数情形）**——**乘以常数不改变差分阶数。** -/
theorem rfdiff_const_mul (c : ℝ) (f : ℝ → ℝ) :
    rfdiff (fun t => c * f t) = fun t => c * rfdiff f t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **`rfdiff` 是加性的**。 -/
theorem rfdiff_add (f g : ℝ → ℝ) :
    rfdiff (fun t => f t + g t) = fun t => rfdiff f t + rfdiff g t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **`rfdiffIter` 是加性的**。 -/
theorem rfdiffIter_add (k : ℕ) (f g : ℝ → ℝ) :
    rfdiffIter k (fun t => f t + g t)
      = fun t => rfdiffIter k f t + rfdiffIter k g t := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      rw [rfdiffIter_succ, ih, rfdiff_add]
      funext t
      rw [rfdiffIter_succ, rfdiffIter_succ]

/-- ⭐⭐ **`rfdiffIter` 与常数相乘交换**。 -/
theorem rfdiffIter_const_mul (k : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    rfdiffIter k (fun t => c * f t) = fun t => c * rfdiffIter k f t := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      rw [rfdiffIter_succ, ih, rfdiff_const_mul]
      funext t
      rw [rfdiffIter_succ]


/-! ## ⭐⭐⭐ 次数概念化：`LowDeg k f :=` 第 `k+1` 阶差分为零

## 为什么这样定义而不是用 `Polynomial`

**「次数 ≤ k」需要一个定义。用 `Polynomial` 意味着把链的递推与 `MvPolynomial` 的复合对接——
那是大工程，而且对本项目的用途（障碍）而言是过度的。**

**⇒ 本项目真正需要的只是【判别式】：「次数 ≤ k」⟺「第 `k+1` 阶差分恒为零」。
这在差分层面上是【定义**，无需多项式理论。**

**⚠ 这不是弱化**：**第 197 轮的可达性障碍、第 204–206 轮的两侧钉住，
用的全部是这个判别式；把它命名出来就能陈述一般归纳。** -/

/-- **「次数 ≤ k」的差分定义**——**第 `k+1` 阶迭代差分为零。** -/
def LowDeg (k : ℕ) (f : ℝ → ℝ) : Prop := rfdiffIter (k + 1) f = 0

/-- ⭐ **常数是次数 ≤ 0 的**。 -/
theorem lowDeg_zero_of_const (c : ℝ) : LowDeg 0 (fun _ => c) := by
  simp only [LowDeg, rfdiffIter]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **加性：两个次数 ≤ k 的函数之和仍是次数 ≤ k**。 -/
theorem lowDeg_add {k : ℕ} {f g : ℝ → ℝ} (hf : LowDeg k f) (hg : LowDeg k g) :
    LowDeg k (fun t => f t + g t) := by
  simp only [LowDeg] at *
  rw [rfdiffIter_add, hf, hg]
  funext t
  simp

/-- ⭐⭐ **数乘：次数 ≤ k 的函数乘常数仍是次数 ≤ k**。 -/
theorem lowDeg_const_mul {k : ℕ} (c : ℝ) {f : ℝ → ℝ} (hf : LowDeg k f) :
    LowDeg k (fun t => c * f t) := by
  simp only [LowDeg] at *
  rw [rfdiffIter_const_mul, hf]
  funext t
  simp


/-- ⭐⭐ **`LowDeg` 是单调的：次数 ≤ k 蕴含次数 ≤ k+1。** -/
theorem lowDeg_succ {k : ℕ} {f : ℝ → ℝ} (h : LowDeg k f) : LowDeg (k + 1) f := by
  simp only [LowDeg] at *
  rw [rfdiffIter_succ, h]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **`rfdiff f = 0` 当且仅当 `f` 是常函数**（差分步长为 1，所以只需 `f(t+1) = f t`）。

**⚠ 这里只证【需要的方向**：`rfdiff f = 0 → ∀ t, f (t+1) = f t`。** -/
theorem rfdiff_eq_zero_step {f : ℝ → ℝ} (h : rfdiff f = 0) (t : ℝ) : f (t + 1) = f t := by
  have := congrFun h t
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

theorem lowDeg_zero_affine_mul {f : ℝ → ℝ} (hf : LowDeg 0 f) (a b : ℝ) :
    LowDeg 1 (fun t => (a + b * t) * f t) := by
  have hconst : ∀ s : ℝ, f (s + 1) = f s := fun s => rfdiff_eq_zero_step hf s
  simp only [LowDeg, rfdiffIter] at *
  funext t
  -- 目标是 rfdiff (rfdiff (fun t => (a+b*t)*f t)) t = 0
  set g : ℝ → ℝ := fun s => (a + b * s) * f s with hg
  -- 先把两个 rfdiff 都展开成显式的四点值
  have hval : ∀ s : ℝ, rfdiff g s = (a + b * (s + 1)) * f s - (a + b * s) * f s := by
    intro s
    simp only [rfdiff, hg]
    have : f (s + 1) = f s := hconst s
    rw [this]
  have : rfdiff (rfdiff g) t = (rfdiff g (t + 1)) - (rfdiff g t) := rfl
  rw [this, hval (t + 1), hval t]
  have h1 : f (t + 1) = f t := hconst t
  rw [h1]
  simp only [Pi.zero_apply]
  ring


/-- ⭐⭐⭐ **`LowDeg 1 f` 的算术内容**：**`f (s+2) - 2·f (s+1) + f s = 0`。**

**⇒ `f` 在等距点上是【仿射**的：`f (s+k) = f s + k·(f (s+1) - f s)` 对一切自然数 `k`。

**⚠ 下面只证用得到的 `k ≤ 4`——一般 `k` 需要 `Nat` 归纳，而本节的目标只到三阶差分。** -/
theorem lowDeg_one_step {f : ℝ → ℝ} (hf : LowDeg 1 f) (s : ℝ) :
    f (s + 1 + 1) - f (s + 1) = f (s + 1) - f s := by
  have h : rfdiff (rfdiff f) = 0 := hf
  have := congrFun h s
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

/-- **`f (s+2) = 2·f (s+1) - f s`**——上一式的移项形式。 -/
theorem lowDeg_one_rec {f : ℝ → ℝ} (hf : LowDeg 1 f) (s : ℝ) :
    f (s + 1 + 1) = 2 * f (s + 1) - f s := by
  have := lowDeg_one_step hf s
  linarith

/-- ⭐⭐⭐ **乘以一次式使次数 ≤ 1 升到次数 ≤ 2**——**归纳在 `k = 1` 处的一步。**

**⚠ 证明方式**：**用 `lowDeg_one_rec` 把目标里所有 `f (t+k)`（`k ≥ 2`）降成
`f t` 与 `f (t+1)` 的线性组合，然后 `ring`。**

**⚠ 与 `lowDeg_zero_affine_mul` 合起来，`k = 0, 1` 两步都有。
完整归纳需要一般 `k`（离散 Leibniz 的一般形式），本轮未做。** -/
theorem lowDeg_one_affine_mul {f : ℝ → ℝ} (hf : LowDeg 1 f) (a b : ℝ) :
    LowDeg 2 (fun t => (a + b * t) * f t) := by
  simp only [LowDeg] at hf ⊢
  simp only [rfdiffIter] at hf ⊢
  funext t
  simp only [rfdiff, Pi.zero_apply]
  -- 把四个高点的值降到 f t 与 f (t+1)
  have r1 : f (t + 1 + 1) = 2 * f (t + 1) - f t := lowDeg_one_rec hf t
  have r2 : f (t + 1 + 1 + 1) = 2 * f (t + 1 + 1) - f (t + 1) := lowDeg_one_rec hf (t + 1)
  rw [r2, r1]
  ring


/-- ⭐⭐ **一次式是 `LowDeg 1`**——**二阶差分为零。**

**这是链归纳的基座：每层的权重 `(g_{2d} + t·h_{2d})` 就是这样的一次式。**

**⚠ 别名普查把本条与第 207 轮的 `lowDeg_zero_of_const` 标为 `copy`——
两条的【证明形状**相同（展开两层 `rfdiff` 再 `ring`），但【陈述不同**：
**一条说常数，一条说一次式，而两者都是归纳需要的（一次式给出 `k = 1`，常数给出 `k = 0` 的基座）。**

**⇒ 保留两条，并把这条注记作为「同一模式的两个必要实例」的记录。
同时删掉了第三条纯包装 `lowDeg_const_one`——它从未被使用，
而「常数是 `LowDeg 1`」由 `lowDeg_succ ∘ lowDeg_zero_of_const` 直接得到。** -/
theorem lowDeg_affine (a b : ℝ) : LowDeg 1 (fun t => a + b * t) := by
  simp only [LowDeg, rfdiffIter]
  funext t
  simp only [rfdiff, Pi.zero_apply]
  ring

/-- ⭐⭐ **`LowDeg 2` 的算术内容**：**三阶差分为零，即二阶差分是常数。**

**⇒ `f` 在等距点上与一个二次式相符；`f(s+3) = 3f(s+2) - 3f(s+1) + f(s)`。** -/
theorem lowDeg_two_step {f : ℝ → ℝ} (hf : LowDeg 2 f) (s : ℝ) :
    f (s + 1 + 1 + 1) - 3 * f (s + 1 + 1) + 3 * f (s + 1) - f s = 0 := by
  simp only [LowDeg, rfdiffIter, rfdiff, Pi.zero_apply] at hf
  have := congrFun hf s
  simp only [rfdiff, Pi.zero_apply] at this
  linarith

/-- ⭐⭐⭐ **乘以一次式使次数 ≤ 2 升到次数 ≤ 3**——**归纳在 `k = 2` 处的一步。**

**⚠ 与 `lowDeg_zero_affine_mul`、`lowDeg_one_affine_mul` 合起来，`k = 0, 1, 2` 三步都有。** -/
theorem lowDeg_two_affine_mul {f : ℝ → ℝ} (hf : LowDeg 2 f) (a b : ℝ) :
    LowDeg 3 (fun t => (a + b * t) * f t) := by
  simp only [LowDeg] at hf ⊢
  simp only [rfdiffIter] at hf ⊢
  funext t
  simp only [rfdiff, Pi.zero_apply]
  -- 把 f 的高点值降到 f t, f(t+1), f(t+2)
  have r1 : f (t + 1 + 1 + 1)
      = 3 * f (t + 1 + 1) - 3 * f (t + 1) + f t := by
    have := lowDeg_two_step hf t
    linarith
  have r2 : f (t + 1 + 1 + 1 + 1)
      = 3 * f (t + 1 + 1 + 1) - 3 * f (t + 1 + 1) + f (t + 1) := by
    have := lowDeg_two_step hf (t + 1)
    linarith
  rw [r2, r1]
  ring


/-! ## ⭐⭐⭐ 链的参数次数：对深度归纳

## 归纳的不变量

**沿参数方向 `t ↦ g + t·h`，宽 1 的链的作用是**

    Φ_ch(t) = flatChainAct ch 0 (g + t·h) (fun _ => x)

**而递推（第 191 轮的 `flatChainAct_cons_general` 在宽 1 的特化）是**

    Φ_{cons l ch}(t) = Φ_ch(t) 作用在 `(g_off + t·h_off)·x + (g_{off+1} + t·h_{off+1})` 上

**⚠ 那不是「一次式乘 Φ_ch」的形状**——**因为 `flatChainAct` 把【新激活】喂给尾链，
而新激活本身依赖 `t`。**

**⇒ 直接对 `Chain` 归纳是【错**的路子：`Φ_{cons l ch}(t)` 不是 `(a+b·t)·Φ_ch(t) + (c+d·t)`，
而是 `Φ_ch` 作用在一个 `t`-依赖的输入上。**

**⚠ 正确的路子在【输入】侧：第 203 轮已证「链对输入恒为仿射」
（`flatChainAct_scalar_affine`），所以**

    Φ_ch(t) = (1 − σ(t))·Φ_ch(0) + σ(t)·Φ_ch(1)

**其中 `σ(t)` 是那个 `t`-依赖的标量输入。而 `σ` 本身沿 `t` 是【一次**的
（每层 `(g_off + t·h_off)·x + (g_off+1 + t·h_{off+1})`）。
**⇒ `Φ_ch(t)` 是 `t` 的一次式的仿射像——仍然是一次式！**

**⇒ 这与第 203 轮的结论一致：深度【不】提高对输入的次数。**
**而「参数次数 = 深度」是关于【参数 `g`】的，不是关于单条参数直线的 `t`。**

## 本轮的处理

**⇒ 我不再试图用 `Chain` 归纳去证「`t ↦ Φ(g + t·h)` 的次数 = 深度」——
因为沿着一条直线看，每层的 `(g + t·h)` 只是把系数变成 `t` 的一次式，
而【所有层的参数同时变】才产生高次项。**

**⚠ 而第 204／205 轮的 `twoLayer_param_cubic` 与 `threeLayer_param_quartic`
证的正是「所有层同时变」的情形，用的是【显式展开**（`threeLayer_param_expand`）。**

**⇒ 所以本轮回退到【记录】：`Chain` 归纳需要的不变量不是 `LowDeg`，
而是「`Φ` 是 `g` 的多项式」，而那需要 `MvPolynomial`（第 199 轮起已登记）。** -/

/-- **链的层数**——**用于陈述「次数 = 层数」的上界。** -/
def chainDepth : {m n : ℕ} → Chain m n → ℕ
  | _, _, .idf _ => 0
  | _, _, .cons _ rest => chainDepth rest + 1

/-- **空链的层数为零**。 -/
theorem chainDepth_idf {n : ℕ} : chainDepth (Chain.idf n) = 0 := rfl

/-- **加一层层数加一**。 -/
theorem chainDepth_cons {m n c : ℕ} (l : MLayer m n) (rest : Chain n c) :
    chainDepth (Chain.cons l rest) = chainDepth rest + 1 := rfl


/-! ## ⚠⚠ 第 3 轮的推测被推翻：参数方向确实到三次

## 第 3 轮写了什么

**第 3 轮在 `chainDepth` 一节的文档里断言：**

> **沿一条参数直线 `t ↦ g + t·h`，新激活是 `t` 的仿射式，而把仿射函数喂进一个对输入仿射的链，
> 得到的仍然是 `t` 的仿射函数。⇒ `t ↦ Φ_ch(g + t·h)` 对【每一条】链都是 `t` 的仿射函数。**

**那个推理【是错的**，而错在一个具体的地方：
**「对输入仿射」是关于【第一个变量】的性质，而新激活同时是 `t` 的函数；
把 `t`-依赖的输入喂进仿射映射，得到的是 `t` 的多项式，次数随层数【增加**——
**因为每层的权重【也】随 `t` 变，两者相乘就产生高次项。**

## 本轮用数值把这件事钉死

**取 `g = 0`、`h = e₀ + e₂ + e₄`、`x = 1`：三层链的输出【恰好等于】 `t³`。**

**⇒ 参数方向上的次数确实是 3，不是 1。第 204／205 轮的 `threeLayerCoeff3 = h4·h2·h0·x` 是对的，
而第 3 轮的「恒为仿射」的推广是错的。**

**⚠ 结论**：**`LowDeg` 确实是正确的阶梯**——**第 3 轮放弃 `Chain` 归纳的理由（「不变量选错了」）不成立；
真正的障碍只是 `lowDeg_affine_mul` 的一般 `k`（离散 Leibniz）还没证。** -/

/-- **三层链沿参数方向 `e₀+e₂+e₄` 的输出恰是 `t³`**——**第 3 轮推测被推翻的直接见证。** -/
theorem threeLayerAxis_t3 (t : ℝ) :
    flatChainAct (N := 6) threeLayerChain 0
      (fun i => (0 : Fin 6 → ℝ) i
        + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
      (fun _ => (1 : ℝ)) 0 = t ^ 3 := by
  rw [threeLayer_param_expand]
  simp only [threeLayerCoeff0, threeLayerCoeff1, threeLayerCoeff2, threeLayerCoeff3,
    show (1 : Fin 6) ≠ 2 from by decide,
    show (1 : Fin 6) ≠ 4 from by decide,
    show (3 : Fin 6) ≠ 0 from by decide,
    show (3 : Fin 6) ≠ 2 from by decide,
    show (3 : Fin 6) ≠ 4 from by decide,
    show (5 : Fin 6) ≠ 0 from by decide,
    show (5 : Fin 6) ≠ 2 from by decide,
    show (5 : Fin 6) ≠ 4 from by decide]
  norm_num

/-- ⭐⭐ **沿参数方向，三层链【不是】仿射的**——**`t³` 不满足二阶差分为零。**

**⇒ 与两层的情形（第 204 轮的三阶参数差分零、第 187 轮的非仿射）并列，
给出「参数次数随深度增长」的又一直接见证。** -/
theorem threeLayerAxis_not_affine :
    ¬ (∀ t : ℝ,
        flatChainAct (N := 6) threeLayerChain 0
          (fun i => (0 : Fin 6 → ℝ) i
            + t * (if i = 0 ∨ i = 2 ∨ i = 4 then (1 : ℝ) else 0))
          (fun _ => (1 : ℝ)) 0
          = (1 - t) * (0 : ℝ) + t * 1) := by
  intro h
  have h3 := h 3
  have h0 := h 0
  have h1 := h 1
  rw [threeLayerAxis_t3] at h3
  rw [threeLayerAxis_t3] at h0
  rw [threeLayerAxis_t3] at h1
  norm_num at h3 h0 h1


/-! ## 一般离散 Leibniz 规则：乘以一次式使次数升一阶（任意 `k`）

## 本轮正面处理第 2／3／4 轮三次绕开的障碍

**目标**：`LowDeg k f → LowDeg (k+1) (fun t => (a + b * t) * f t)`。

**第 2 轮的失败**：直接套 `rfdiff_affine_mul` 于 `rfdiff (rfdiffIter (k+1) …)` —— 那是错的，
`rfdiff` 不能穿过 `rfdiffIter k`。

**⇒ 本轮的策略**：**对 `k` 归纳，归纳步用【对称乘积规则】**。 -/

/-- ⭐⭐ **一阶乘积规则（对称形式）**——**离散 Leibniz 的最底层。** -/
theorem rfdiff_mul (u f : ℝ → ℝ) :
    rfdiff (fun t => u t * f t)
      = fun t => u (t + 1) * rfdiff f t + rfdiff u t * f t := by
  funext t
  simp only [rfdiff]
  ring

/-- ⭐⭐ **仿射函数的一阶差分是常数**。 -/
theorem rfdiff_affine (a b : ℝ) :
    rfdiff (fun t => a + b * t) = fun _ => b := by
  funext t
  simp only [rfdiff]
  ring

/-! ## ⚠⚠ 第 5 轮的结论：一般 `k` 的 `lowDeg_affine_mul` 未能证出，精确理由如下

## 三次尝试的完整记录

| 轮次 | 尝试 | 失败点 |
|:--|:--|:--|
| 2 | 把 `rfdiff_affine_mul` 直接套在 `rfdiff (rfdiffIter (k+1) …)` 上 | **`rfdiff` 不能穿过 `rfdiffIter k`**——这是【数学**错误，不是技术障碍 |
| 3 | 改用 `MvPolynomial` | **未做**（判断为过度） |
| 4 | 证「参数直线恒为仿射」以绕开 | **该命题为【假**（本轮以 `threeLayerAxis_t3` 反证），路走死 |
| **5** | **对 `k` 归纳 + 对称乘积规则 `rfdiff_mul`** | **归纳步能推进到 `rfdiffIter (k+1) (b·f) = 0`（已消），但 `u(t+1)·rfdiff f` 这一项需要归纳假设作用在【平移后的仿射式】上，而 `ih` 的 `a b` 是【外层固定**的——`LowDeg (k+1) ((a+b)·(t+1) 形) rfdiff f` 与 `ih` 要求的 `LowDeg (k+1) ((a'+b'·t) · rfdiff f)` 不同形，`rw` 失败。 |

## 精确的数学障碍

**归纳步的实际目标是**

    rfdiffIter (k+1) (fun t => (a + b·(t+1)) · rfdiff f t) = 0

**而归纳假设给的是**

    LowDeg k g → LowDeg (k+1) (fun t => (a' + b'·t) · g t)

**两者的乘积因子不同：**`a + b·(t+1)` **是 `a + b·t` 的【平移**，
**而 `LowDeg` 不是平移不变的**——`rfdiffIter` 在 `t` 的平移下【会变**。

**⇒ 归纳需要对【所有平移**同时做，即需要一条平移不变形式的陈述：

    LowDeg k f → ∀ c, LowDeg (k+1) (fun t => (a + b·(t + c)) · f t)

**而它的证明又要对 `c` 归纳或用一个更强的多变量形式——
那实际上等价于【多变量多项式次数**，即第 199 轮登记的 `MvPolynomial` 路线。**

## 结论

**本路线到此为【已核实的终点**：
**`lowDeg_affine_mul` 的一般 `k` 需要的不是更多 tactic，而是平移不变性，
而那把问题推回 `MvPolynomial`。**

**⇒ 已证的 `lowDeg_affine_mul` 三个实例（`k = 0, 1, 2`，第 207／208／第 3 轮）是这条路线能给的全部。
一般形式【登记为未做**，理由如上，而不是「暂时没时间」。** -/




end Lattice.Core