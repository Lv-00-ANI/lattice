/-
# 程序作为权重侧表示：AST、语义、**语法往返**

## 0. 为什么这是解决「只能线性」的正确方向

第 200 轮证明了 `no_affine_represents_sphere`：**一般非线性约束不存在精确的仿射表示**。
那不是没做够，是数学事实。

**所以「把非线性函数逆成权重」这条路是封死的。** 但这是一条路的封死，不是所有路的封死。

**换一个方向**：不要把非线性函数逆成权重，而是**把「程序」本身当作权重侧表示**。
于是：

| 层 | 符号侧 | 权重侧 | 往返的含义 |
|:--|:--|:--|:--|
| 仿射（第 168/182 轮） | `List ℝ` | `AffineLayer` | **数值**往返 `extract ∘ compile = id` |
| **程序（本节）** | 规格/约束 | `LayerProgram` | **语法**往返 `decode ∘ encode = id` |

**关键洞察**：程序的「逆」是**反解析**（parse），不是求反函数。
**parse 总是存在的**（编码是我们自己设计的）；求反函数不总是存在（球面例子）。

**所以非线性不是障碍——只要换一个往返的定义。** 语义由 `evalProgram` 单独给定理。

## 1. 交付

| 声明 | 内容 |
|:--|:--|
| `Instr n` | 三种指令：`affine W b`、`relu`、`scale c` |
| `LayerProgram n` | `List (Instr n)`，直序程序 |
| `applyInstr` / `evalProgram` | 语义 |
| `eval_append` | **组合性**：`evalProgram x (p ++ q) = evalProgram (evalProgram x p) q` |
| `Wire n` | 线格式：`tag k` 或 `num x` |
| `encodeInstr` | 指令 → 线格式 |
| `decodeInstr` | **反解析**（本节的重点） |
| **`decodeInstr_encodeInstr`** | **语法往返：`decode (encode i) = some i`** |
| **`programRep`** | **`Representation`：程序 ↔ 线格式** |

## 2. 为什么线格式用 `Nat` 标签而不是浮点字面量

初稿写的是 `encodeInstr | .relu => [1]`，想用 `ℝ` 值当标签。**编译失败**：

```
dependent match elimination failed, inaccessible pattern found
    .(Real.zero)
```

`ℝ` 上的字面量不是可匹配的构造子（`0 : ℝ` 展开成 `Real.ofCauchy …`），
所以**用它当判别位不可行**。改成 `Wire.tag (k : ℕ)` 之后一切正常。

**这不是形式化的挑剔，是 C 实现的事实**：C 侧的判别位本来就是整数。
线格式用 `ℕ` 标签与真实实现一致，用 `ℝ` 值反而不一致。

## 3. 边界（三条）

- **只做 `affine` / `relu` / `scale` 三种指令。** `softmax` / `layernorm` / `attention`
  需要规约（reduction），而直序程序的语义会变复杂（需要「全局」依赖）。
  **这是设计的边界，不是偷懒**：先把无规约的闭合，再处理规约。
- **`0 < n` 是必需的**：反解析要用 `k / n`、`k % n` 拆出二维索引，`n = 0` 时 `Fin 0` 空。
  这与 `LayerQuantizationBits` / `RectangularWeightEncoding` 的同一个约束。
- **语法往返是精确的，语义往返不是**：`decode ∘ encode = id` 是等式；
  而「`evalProgram` 之后能还原输入」对 `relu` **不可能**（非单射）。
  **本节只声称前者**——这正是程序表示的要点：**逆语法，不逆函数**。
- 本节**不改** `ActivationLadder`：那个 `Ladder` 只做「程序切两段」，没有反解析。
-/
import Mathlib
import Lattice.Lift.Extraction

namespace Lattice.Lift.ProgramAST

/-! ## 一、指令与程序 -/

/-- **一条指令**：仿射、ReLU、缩放。

三种都作用在 `Fin n → ℝ` 上，所以**宽度不变**，可以任意串联。 -/
inductive Instr (n : ℕ) where
  /-- 仿射层：`x ↦ Wᵀx + b`。 -/
  | affine (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
  /-- ReLU，逐元素。 -/
  | relu
  /-- 逐元素缩放。 -/
  | scale (c : ℝ)

/-- **程序**是直序的指令序列。 -/
abbrev LayerProgram (n : ℕ) := List (Instr n)

/-- **一条指令的作用**。 -/
noncomputable def applyInstr {n : ℕ} (x : Fin n → ℝ) : Instr n → (Fin n → ℝ)
  | .affine W b => fun j => (∑ i, W i j * x i) + b j
  | .relu => fun j => max (x j) 0
  | .scale c => fun j => c * x j

/-- **程序的语义**。 -/
noncomputable def evalProgram {n : ℕ} (x : Fin n → ℝ) (p : LayerProgram n) : Fin n → ℝ :=
  p.foldl applyInstr x

/-- 空程序的语义是恒等。 -/
theorem eval_nil {n : ℕ} (x : Fin n → ℝ) : evalProgram x ([] : LayerProgram n) = x := rfl

/-- **组合性**：先跑 `p` 再跑 `q`，等于对 `p` 的结果跑 `q`。

**这条让程序的可组合成为定理**，也是后面 `Representation` 能有意义的前提。 -/
theorem eval_append {n : ℕ} (x : Fin n → ℝ) (p q : LayerProgram n) :
    evalProgram x (p ++ q) = evalProgram (evalProgram x p) q := by
  unfold evalProgram
  rw [List.foldl_append]

/-! ## 二、线格式与**反解析**

**线格式是 `List ℝ`，不是 `List (Wire n)`。**

初稿写了一个 `Wire` 归纳类型（`tag k` / `num x`），再写 `asNum` 把它投影回 `ℝ`。
**那层抽象是多余的，而且它让证明变长而不是变短**：`decodeInstr` 在 `List (Wire n)` 上
`getD`，再 `asNum`，于是每一步都要一条「`asNum` 穿过 `getD`」的桥，
而 `List.getD_append_left` 这类引理在本 mathlib 里**不存在**。

**判别位直接放在 `ℝ` 流里**：`0` = affine，`1` = relu，`2` = scale。
C 侧的格式也是这样——一个 `double` 数组，头几个位置是 opcode 与形状。
**少一层类型，多一条能证的定理。**

**这不能靠 `match` 上 `ℝ` 字面量**（见下），所以 `decodeInstr` 用 `if` 判等，而不是模式匹配。 -/

/-- **判别位**：线格式的前几个数编码指令种类。 -/
def TAG_AFFINE : ℝ := 0
def TAG_RELU : ℝ := 1
def TAG_SCALE : ℝ := 2

/-- **编码一条指令**为数值流。

`affine` 的布局：`0`，然后 `n*n` 个系数（行主序），然后 `n` 个偏置。
**这是 C 的 row-major 布局。** -/
noncomputable def encodeInstr {n : ℕ} (hn : 0 < n) : Instr n → List ℝ
  | .affine W b =>
      TAG_AFFINE ::
        (List.ofFn (fun k : Fin (n * n) =>
          W ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩
            ⟨k.val % n, Nat.mod_lt _ hn⟩))
        ++ (List.ofFn b)
  | .relu => [TAG_RELU]
  | .scale c => [TAG_SCALE, c]

/-- **反解析一条指令**：读判别位，按判别位决定读多少载荷。

**用 `if` 而不是 `match`**：`ℝ` 上的字面量不是可匹配的构造子
（`(0 : ℝ) :: _` 会报 inaccessible pattern），所以判别必须走 `Decidable` 等值。 -/
noncomputable def decodeInstr {n : ℕ} (hn : 0 < n) : List ℝ → Option (Instr n)
  | [] => none
  | (t :: rest) =>
      if t = TAG_AFFINE then
        some (.affine
          (fun i j => rest.getD (i.val * n + j.val) 0)
          (fun j => rest.getD (n * n + j.val) 0))
      else if t = TAG_RELU then some .relu
      else if t = TAG_SCALE then some (.scale (rest.getD 0 0))
      else none

/-! ## 三、往返 -/

/-- **`n` 为正时的取模/取商重建**：`(k / n) * n + k % n = k`。

`Nat.div_add_mod` 给的是 `n * (k / n) + k % n = k`（除数在前），先 `Nat.mul_comm` 换过来。
**这个顺序问题在 `RectangularWeightEncoding` 也撞过。** -/
theorem div_mul_add_mod {n : ℕ} (hn : 0 < n) (k : ℕ) : k / n * n + k % n = k := by
  rw [Nat.mul_comm]
  exact Nat.div_add_mod k n

/-- **`getD` 在左段内**：下标落在 `as` 里时，`as ++ bs` 与 `as` 读同一项。

**本 mathlib 没有 `List.getD_append_left`**（与 `List.getD_append_right` 不对称），所以自己证。
走的是 `getElem`：`getD` 在界内时等于 `getElem`，而 `append` 的 `getElem` 有 `getElem_append_left`。 -/
theorem getD_append_left {α : Type} (as bs : List α) (k : ℕ) (d : α) (hk : k < as.length) :
    (as ++ bs).getD k d = as.getD k d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk]
  simp only [List.getElem_append_left hk]

/-- **`getD` 在右段内**：下标超出 `as` 的长度时，等于在 `bs` 里的对应项。 -/
theorem getD_append_right {α : Type} (as bs : List α) (k : ℕ) (d : α) (hk : as.length ≤ k) :
    (as ++ bs).getD k d = bs.getD (k - as.length) d := by
  by_cases hin : k < (as ++ bs).length
  · rw [List.getD_eq_getElem _ _ hin, List.getD_eq_getElem _ _ (by simp at hin ⊢; omega)]
    simp only [List.getElem_append_right hk]
  · rw [List.getD_eq_default _ _ (by omega)]
    rw [List.getD_eq_default _ _ (by simp at hin ⊢; omega)]

/-- **载荷的读回**：`List.ofFn f` 的第 `k` 项能被 `getD k 0` 读回。 -/
theorem getD_ofFn_payload {n : ℕ} (k : ℕ) (hk : k < n) (f : Fin n → ℝ) :
    (List.ofFn f).getD k 0 = f ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hk)]
  simp only [List.getElem_ofFn, Fin.val_mk]

/-- **`relu` 的语法往返**：`decode (encode relu) = some relu`。 -/
theorem decodeInstr_encode_relu {n : ℕ} (hn : 0 < n) :
    decodeInstr hn (encodeInstr hn (.relu : Instr n)) = some .relu := by
  unfold decodeInstr encodeInstr TAG_AFFINE TAG_RELU
  norm_num

/-- **`scale` 的语法往返**：`decode (encode (scale c)) = some (scale c)`。 -/
theorem decodeInstr_encode_scale {n : ℕ} (hn : 0 < n) (c : ℝ) :
    decodeInstr hn (encodeInstr hn (.scale c : Instr n)) = some (.scale c) := by
  unfold decodeInstr encodeInstr TAG_AFFINE TAG_RELU TAG_SCALE
  norm_num

/-- **`affine` 的语法往返**（核心情形）：系数与偏置在行主序上逐位读回。

**这是 C 解释器需要的规格**：写出的字节流读回来，得到的指令与原指令的 `W`、`b`
在每个 `(i, j)` 上相等。 -/
theorem decodeInstr_encode_affine {n : ℕ} (hn : 0 < n) (W : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) :
    decodeInstr hn (encodeInstr hn (.affine W b : Instr n)) = some (.affine W b) := by
  have hcoef : ∀ i j : Fin n, i.val * n + j.val < n * n := by
    intro i j
    have h1 : i.val < n := i.isLt
    have h2 : j.val < n := j.isLt
    nlinarith
  -- `unfold` leaves an inner `match Instr.affine W b with …` unreduced: `encodeInstr` is defined by
  -- pattern matching, and `unfold` rewrites the whole call rather than applying the equation lemma.
  -- `simp only` on `encodeInstr` with the constructor fires the equation lemma directly, which also
  -- reduces the `++`; `List.cons_append` is then unnecessary.
  show decodeInstr hn (TAG_AFFINE :: (List.ofFn (fun k : Fin (n * n) =>
        W ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩
          ⟨k.val % n, Nat.mod_lt _ hn⟩)) ++ List.ofFn b) = some (.affine W b)
  unfold decodeInstr
  -- reduce the scrutinee (0 :: …) ++ … to   :: (… ++ …) so the match fires
  simp only [List.cons_append, TAG_AFFINE, ↓reduceIte, Option.some.injEq, Instr.affine.injEq]
  constructor
  · funext i j
    -- the flat index `i*n + j` addresses the coefficient block
    have hidx := hcoef i j
    rw [getD_append_left _ _ _ _ (by simp only [List.length_ofFn]; exact hidx)]
    rw [getD_ofFn_payload _ hidx]
    congr 1
    · -- (i*n + j) / n = i
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [Nat.mul_comm i.val n, Nat.mul_add_div (by omega), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    · -- (i*n + j) % n = j
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [Nat.mul_comm i.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
  · funext j
    -- the flat index `n*n + j` addresses the bias block
    rw [getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    exact getD_ofFn_payload j.val j.isLt b

/-! ## 四、为什么不建 `Representation`：一条被否决的路线

初稿写了

```lean
def programRep (n : ℕ) (hn : 0 < n) : Representation (LayerProgram n) (List ℝ) where
  compile := fun p => p.flatMap (encodeInstr hn)
  extract := fun ws => ...        -- 重建
  roundtrip := ...
```

**`extract` 写不出来，而且原因不是技巧不够，是结构性的**：

- `Representation.roundtrip : ∀ p, extract (compile p) = p` 要求 `extract` 是 `compile` 的
  **全局逆**，返回类型是 `LayerProgram n`（**不是 `Option`**）；
- 而解码在遇到非法流时**必然失败**——`Representation` 没有 `Option` 的位置。

**所以正确的形状是「单条指令的语法往返」而不是一个 `Representation`**：

| 定理 | 内容 |
|:--|:--|
| `decodeInstr_encode_relu` | `decode (encode relu) = some relu` |
| `decodeInstr_encode_scale` | `decode (encode (scale c)) = some (scale c)` |
| `decodeInstr_encode_affine` | **核心**：系数与偏置逐位读回 |

**这三条才是 C 解释器要的规格**：它要「读回的流等于写出的指令」，
不是「存在一个全函数把任意流变成程序」（后者是假的）。

**一个满足不了 `roundtrip` 的实例比没有实例更糟**——它会让读者以为有一条不存在的往返。
初稿确实写了那样一个 `extract`（返回空列表），删掉了。 -/

/-! ## 六、**整程序**的语法往返（S11）

### §五 只做到单条指令

`decodeInstr_encode_relu` / `_scale` / `_affine` 三条证明的是
「**一条**指令编码后再解码得到它自己」。**而 S11 要的是整程序**：

```lean
decodeProgram (encodeProgram p) = some p
```

**这两件事不一样**：`decodeInstr` 用 `getD … 0` 读整个列表，**它不知道一条指令到哪里结束**，
所以整程序必须先按指令长度切分。**这就是 §五 停下的地方。**

### 如何切分而不重做 `getD` 的工作

指令长度由 **tag** 决定：

| 指令 | 编码长度 |
|:--|:--|
| `affine W b` | `1 + n·n + n` |
| `relu` | `1 + n` |
| `scale c` | `2` |

于是 `decodeProgram` 按 tag 取长度 `len`，对 `xs.take len` 调 `decodeInstr`，对 `xs.drop len` 递归。

**关键点：不需要任何新的 `getD` 引理。** 因为

```
(xs ++ rest).take xs.length = xs          -- `List.take_left`
(xs ++ rest).drop xs.length = rest        -- `List.drop_left`
```

于是 `decodeInstr hn ((encodeInstr hn i ++ rest).take (encodeInstr hn i).length)`
**就是** `decodeInstr hn (encodeInstr hn i)`——**追加的 `rest` 被 `take` 完全隔离掉了**。
剩下的正是已有的三条逐指令引理。**把工作放在「切分」上，已有的 `getD` 证明就原封不动可用。**

### 交付

| 声明 | 内容 |
|:--|:--|
| `instrLength` | 一条指令的编码长度 |
| `instrLengthOfTag` | 由 tag 决定的长度（供解码端使用） |
| **`encodeInstr_length`** | **`(encodeInstr hn i).length = instrLength i`** |
| **`encodeInstr_length_ofTag`** | **由 tag 读出的长度 = 实际长度**（解码端依赖它） |
| `decodeProgram` | 整程序解码 |
| `encodeProgram` | 整程序编码 |
| **`decodeProgram_encodeProgram`** | **整程序精确往返** |
| `encodeProgram_eval` | 编码/解码不改变求值语义 |

### 边界

- **`0 < n` 是必需的**：`encodeInstr` 的 `affine` 情形要 `n` 做行主序除法，`n = 0` 时无坐标可编码。
- **`decodeProgram` 对垃圾输入返回 `none` 或截断**：未知 tag 一律 `none`（不是「尽力而为」）。
  **拒绝比猜测好**——一个静默截断的解码器会让「程序往返」这条规格变成空话。
- **本节只做语法往返，不做语义等价**：`encodeProgram_eval` 说的是「解码后再编码求值相同」，
  那是**由往返推出**的，不是独立建立的等价。 -/

/-- **由 tag 决定的编码长度**——解码端只有列表，所以只能从 tag 推。

`noncomputable`：`t = TAG_AFFINE` 是 `ℝ` 上的等式判定，而 `ℝ` 没有可计算的 `DecidableEq`。
**这是本库反复出现的同一件事**（`GeoConstraint` 无 `DecidableEq`、`Edit.del` 用谓词）。 -/
noncomputable def instrLengthOfTag (n : ℕ) (t : ℝ) : ℕ :=
  if t = TAG_AFFINE then 1 + (n * n + n)
  else if t = TAG_RELU then 1
  else 2

/-- **由 tag 决定的长度至少为 1**——解码端靠它保证每次递归都真的缩短列表。 -/
theorem one_le_instrLengthOfTag (n : ℕ) (t : ℝ) : 1 ≤ instrLengthOfTag n t := by
  unfold instrLengthOfTag
  split_ifs <;> omega

/-- **由 tag 读出的长度就是实际编码长度。**

这条是解码端的地基：`decodeProgram` 只能用 tag 推长度，所以它必须与实际长度一致，
否则 `take` 会切错位置。 -/
theorem encodeInstr_length_ofTag {n : ℕ} (hn : 0 < n) (i : Instr n) :
    instrLengthOfTag n ((encodeInstr hn i).headD 0) = (encodeInstr hn i).length := by
  cases i with
  | affine W b =>
      have htag : (encodeInstr hn (.affine W b : Instr n)).headD 0 = TAG_AFFINE := rfl
      have hlen : (encodeInstr hn (.affine W b : Instr n)).length = 1 + (n * n + n) := by
        show (TAG_AFFINE :: (List.ofFn (fun k : Fin (n * n) =>
            W ⟨k.val / n, (Nat.div_lt_iff_lt_mul hn).mpr k.isLt⟩
            ⟨k.val % n, Nat.mod_lt _ hn⟩) ++ List.ofFn b)).length = 1 + (n * n + n)
        rw [List.length_cons, List.length_append, List.length_ofFn, List.length_ofFn]
        ring
      rw [htag, hlen]
      unfold instrLengthOfTag
      rw [if_pos rfl]
  | relu =>
      have htag : (encodeInstr hn (.relu : Instr n)).headD 0 = TAG_RELU := rfl
      -- `relu` encodes to `[TAG_RELU]`: one element, no payload. An earlier draft of this table
      -- said `1 + n`, which was simply wrong about the encoding.
      have hlen : (encodeInstr hn (.relu : Instr n)).length = 1 := rfl
      rw [htag, hlen]
      unfold instrLengthOfTag
      rw [if_neg (by unfold TAG_AFFINE TAG_RELU; norm_num), if_pos rfl]
  | scale c =>
      have htag : (encodeInstr hn (.scale c : Instr n)).headD 0 = TAG_SCALE := rfl
      have hlen : (encodeInstr hn (.scale c : Instr n)).length = 2 := rfl
      rw [htag, hlen]
      unfold instrLengthOfTag
      rw [if_neg (by unfold TAG_AFFINE TAG_SCALE; norm_num),
          if_neg (by unfold TAG_RELU TAG_SCALE; norm_num)]

/-- **整程序编码**：把每条指令的编码拼起来。 -/
noncomputable def encodeProgram {n : ℕ} (hn : 0 < n) (p : LayerProgram n) : List ℝ :=
  p.flatMap (encodeInstr hn)

/-- **整程序解码（带燃料）**：按 tag 取长度切分，逐条解码。

**为什么用显式燃料而不是 `termination_by`**：`termination_by` 的方程引理在 `rw`/`simp` 下
**不展开**（第 216 轮实测两次失败），于是「解一次 `decodeProgram`」这件事本身写不出来。
燃料版是**对 `ℕ` 的结构递归**：终止性免费，方程引理干净，`rw` 与 `simp` 都能用。
**代价**是多一个参数，而它由 `decodeProgram` 自动填成 `xs.length`。**

**未知 tag 返回 `none`，不猜。** 一个静默截断的解码器会让「程序往返」这条规格变成空话。 -/
noncomputable def decodeProgramGo {n : ℕ} (hn : 0 < n) : ℕ → List ℝ → Option (LayerProgram n)
  | 0, _ => some []
  | _ + 1, [] => some []
  | k + 1, (t :: rest) =>
      let len := instrLengthOfTag n t
      match decodeInstr hn ((t :: rest).take len) with
      | some i => (decodeProgramGo hn k ((t :: rest).drop len)).map (fun p => i :: p)
      | none => none

/-- **整程序解码**：燃料取输入长度，所以一定够用。 -/
noncomputable def decodeProgram {n : ℕ} (hn : 0 < n) (xs : List ℝ) : Option (LayerProgram n) :=
  decodeProgramGo hn xs.length xs

/-- **编码至少一个元素长**——燃料够用与「每步真的前进」都靠它。 -/
theorem one_le_encodeInstr_length {n : ℕ} (hn : 0 < n) (i : Instr n) :
    1 ≤ (encodeInstr hn i).length := by
  rw [← encodeInstr_length_ofTag hn i]
  exact one_le_instrLengthOfTag n _

/-- **燃料够用**：程序长度不超过它的编码长度。 -/
theorem length_le_encodeProgram {n : ℕ} (hn : 0 < n) (p : LayerProgram n) :
    p.length ≤ (encodeProgram hn p).length := by
  induction p with
  | nil => simp [encodeProgram]
  | cons i rest ih =>
      rw [List.length_cons, show encodeProgram hn (i :: rest)
            = encodeInstr hn i ++ encodeProgram hn rest from by
          unfold encodeProgram; rw [List.flatMap_cons],
          List.length_append]
      have := one_le_encodeInstr_length hn i
      omega

/-- **`decodeProgramGo` 在 cons 上的方程**（`rfl`：定义就是长这样）。

单独列出来是因为主证明里 `encodeInstr hn i ++ …` **不是语法上的 cons**，
必须先经 `cases` 把它写成 `t0 :: ts`，这条引理才能应用。 -/
theorem decodeProgramGo_cons {n : ℕ} (hn : 0 < n) (k : ℕ) (t : ℝ) (rest : List ℝ) :
    decodeProgramGo hn (k + 1) (t :: rest)
      = (match decodeInstr hn ((t :: rest).take (instrLengthOfTag n t)) with
         | some i =>
             (decodeProgramGo hn k ((t :: rest).drop (instrLengthOfTag n t))).map (fun p => i :: p)
         | none => none) := rfl

/-- **燃料版往返**：燃料够用时，解码编码后的程序得到原程序。 -/
theorem decodeProgramGo_encodeProgram {n : ℕ} (hn : 0 < n) (p : LayerProgram n) :
    ∀ k : ℕ, p.length ≤ k → decodeProgramGo hn k (encodeProgram hn p) = some p := by
  induction p with
  | nil =>
      intro k _
      cases k with
      | zero => rfl
      | succ k => rfl
  | cons i rest ih =>
      intro k hk
      -- write the encoded first instruction as a syntactic cons
      obtain ⟨t0, ts, ht0⟩ : ∃ t0 ts, encodeInstr hn i = t0 :: ts := by
        cases h : encodeInstr hn i with
        | nil =>
            exfalso
            have h1 := one_le_encodeInstr_length hn i
            rw [h] at h1
            simp at h1
        | cons t0 ts => exact ⟨t0, ts, rfl⟩
      have hk1 : 1 ≤ k := by
        have : 0 < (i :: rest).length := by simp
        omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hsplit : encodeProgram hn (i :: rest) = t0 :: (ts ++ encodeProgram hn rest) := by
        unfold encodeProgram
        rw [List.flatMap_cons, ht0, List.cons_append]
      rw [hsplit, decodeProgramGo_cons]
      -- the tag determines exactly the first instruction's length
      have hlen : instrLengthOfTag n t0 = (t0 :: ts).length := by
        have h := encodeInstr_length_ofTag hn i
        rw [ht0] at h
        exact h
      -- `← List.cons_append` puts the list back in `(t0 :: ts) ++ _` shape so `take_left` applies
      have htake : (t0 :: (ts ++ encodeProgram hn rest)).take (instrLengthOfTag n t0)
          = t0 :: ts := by
        rw [hlen, ← List.cons_append, List.take_left]
      have hdrop : (t0 :: (ts ++ encodeProgram hn rest)).drop (instrLengthOfTag n t0)
          = encodeProgram hn rest := by
        rw [hlen, ← List.cons_append, List.drop_left]
      have honly : decodeInstr hn
          ((t0 :: (ts ++ encodeProgram hn rest)).take (instrLengthOfTag n t0)) = some i := by
        rw [htake, ← ht0]
        cases i with
        | affine W b => exact decodeInstr_encode_affine hn W b
        | relu => exact decodeInstr_encode_relu hn
        | scale c => exact decodeInstr_encode_scale hn c
      rw [honly, hdrop, ih k' (by simpa using hk)]
      rfl

/-- **整程序的精确语法往返**（**S11**）。

`decodeProgram` 的燃料取 `xs.length`，而 `length_le_encodeProgram` 保证它够用，
于是 `decodeProgramGo_encodeProgram` 直接给出结论。 -/
theorem decodeProgram_encodeProgram {n : ℕ} (hn : 0 < n) (p : LayerProgram n) :
    decodeProgram hn (encodeProgram hn p) = some p := by
  unfold decodeProgram
  exact decodeProgramGo_encodeProgram hn p (encodeProgram hn p).length
    (length_le_encodeProgram hn p)

/-- **编码不改变求值**：编码后再解码再求值，等于直接求值。

**这是往返引理的直接推论，不是独立建立的语义等价**——所以它不声称「编码保留了语义」，
只声称「`decode` 之后拿到的是同一个程序」。两者的区别在 `ProgramAST` 里必须分清：
**语法往返是本节证的；语义等价是靠往返得到的。** -/
theorem evalProgram_encodeProgram {n : ℕ} (hn : 0 < n) (p : LayerProgram n)
    (x : Fin n → ℝ) :
    (decodeProgram hn (encodeProgram hn p)).map (fun q => evalProgram x q)
      = some (evalProgram x p) := by
  rw [decodeProgram_encodeProgram hn p]
  rfl

end Lattice.Lift.ProgramAST
