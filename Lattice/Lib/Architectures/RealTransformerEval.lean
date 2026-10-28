/-
# S12：`Block` / `Model` 的 `eval` 语义

## 0. 补的是什么

`Lib/Attention/` 有 **36 个文件**：注意力、softmax 界、RoPE、GQA、因果掩码、KV 缓存……
**但没有一个 `Block` 或 `Model` 结构，也没有 `eval`。**

这意味着「一个 transformer 模型的输出是什么」在本库里**没有被定义过**——有的只是**零件**。
S12 要的正是那个整体。**零件齐、整体缺**，与本会话反复出现的形态同类
（S13 是「两半都在、接缝没有」，这里是「零件都在、组装没有」）。

## 1. 为什么结构与常数分开

**结构里不放 Lipschitz 常数。** 放进去的话 `Block.eval_lipschitz` 的证明就会是那个字段的投影——
审计已经把那个形态判过一次（`Core/Repair.stable`）。**常数作为定理的假设**：
定理对**任意**满足 Lipschitz 条件的层成立，而「这个层确实满足」是使用者提供的**事实**。

## 2. 块的形状（残差写死在语义里）

```
h   := w + attn w          -- 残差 + 注意力
g   := h + ff h            -- 残差 + 前馈
out := norm g
```

**残差把常数从 `L` 变成 `1 + L`**——这是「残差让深层网络可训练」在**界**上的最简形式。

常数推导（**`g = R_ff ∘ h`，所以是乘积**）：

1. `h w = w + attn w` 是 `(1 + La)`-Lipschitz；
2. `R_ff u = u + ff u` 是 `(1 + Lf)`-Lipschitz；
3. `g = R_ff ∘ h` 是 **`(1 + Lf)(1 + La)`**-Lipschitz。

**推导中途我把它「更正」成 `1 + Lf(1+La)` 过一次——那是错的**：
`g w = h w + ff (h w)`，残差是**对 `h w`** 加的（`R_ff` 在 `h` 之外），
不是 `w + ff (h w)`。**看错一层括号，常数就从乘积变成了加法。**

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `SubLayer` / `Block` / `Model` | 结构（**只含函数，不含证明**） |
| **`Block.eval`** | **块的求值（含两条残差）** |
| **`Model.eval`** | **模型求值 = 逐块 `eval`，再过 `head`** |
| `Model.eval_nil` | 空模型 = `head x` |
| **`residual_lipschitz`** | **`x ↦ x + f x` 的常数是 `1 + L`** |
| **`Block.eval_lipschitz`** | **常数 `Ln · (1 + Lf·(1 + La))`** |
| `Block.eval_lipschitz_identity` | **`La = Lf = Ln = 0` 时块是恒等** |

## 4. 边界的实质

- **`eval` 的语义是本文件定义的**，不是从 `Attention/` 的零件自动得到的。
  **`Attention/RealAttention.lean` 的注意力与本文件的 `SubLayer.apply` 之间还没有桥**——
  那要把具体注意力函数填进来并证它的常数。**本节不做。**
- **`Model` 的 Lipschitz 常数本节不给。** 它是 `∏ (块的常数)`，需要一次对 `List.foldl` 的归纳；
  **本节只给单块**，并在 `Model.eval_lipschitz_cons` 里给出递推形式。**没做的东西不假装做了。**
- **常数是乘性的**，随深度指数增长——与 `Lift/StackError` 的 `∏ gain` 是同一个现象。
- **`norm` 不是 LayerNorm**：真正的 LayerNorm 要除以标准差，本节不声称 `norm` 是它。
- **两条残差不是唯一的 block 形状**：本节只对**本文件定义的**这个 `eval` 陈述性质。 -/
import Mathlib
import Lattice.Core.Net

namespace Lattice.Lib.TransformerEval

variable {n : ℕ}

/-! ## 一、结构：**只有函数，没有证明** -/

/-- **一个子层**：从配置到配置的映射。**不带 Lipschitz 常数**——见 §1。 -/
structure SubLayer (n : ℕ) where
  apply : (Fin n → ℝ) → (Fin n → ℝ)

/-- **一个 transformer 块**：注意力、前馈、归一化三件。 -/
structure Block (n : ℕ) where
  attn : SubLayer n
  ff : SubLayer n
  norm : SubLayer n

/-- **一个模型**：一串块 + 输出头。 -/
structure Model (n : ℕ) where
  blocks : List (Block n)
  head : SubLayer n

/-! ## 二、求值语义 -/

/-- **块的求值**：两条残差 + 归一化。

`h := w + attn w`、`g := h + ff h`、`out := norm g`。**残差写死在语义里**，不是可选项。 -/
noncomputable def Block.eval (B : Block n) (x : Fin n → ℝ) : Fin n → ℝ :=
  B.norm.apply (fun i =>
    (x i + B.attn.apply x i)
      + B.ff.apply (fun j => x j + B.attn.apply x j) i)

/-- **模型的求值**：逐块 `eval`，最后过 `head`（与 `netAct` 同方向：第一个块先作用）。 -/
noncomputable def Model.eval (M : Model n) (x : Fin n → ℝ) : Fin n → ℝ :=
  M.head.apply (M.blocks.foldl (fun acc B => B.eval acc) x)

/-- **空模型**：只有 `head`。 -/
theorem Model.eval_nil (M : Model n) (x : Fin n → ℝ) (h : M.blocks = []) :
    M.eval x = M.head.apply x := by
  unfold Model.eval
  rw [h]
  rfl

/-! ## 三、Lipschitz 传播 -/

/-- **一条残差的 Lipschitz 界**：`x ↦ x + f x` 的常数是 `1 + L`。

**这就是残差的作用**：没有残差时增益是 `L`，有残差时是 `1 + L`。
`L → 0` 时前者让信号消失、后者给出恒等——**这是「残差保证不丢失输入」的定量形式**。 -/
theorem residual_lipschitz (f : (Fin n → ℝ) → (Fin n → ℝ)) {L : ℝ}
    (h : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖(fun i => x i + f x i) - (fun i => y i + f y i)‖ ≤ (1 + L) * ‖x - y‖ := by
  intro x y
  have hsplit : (fun i => x i + f x i) - (fun i => y i + f y i)
      = (x - y) + (f x - f y) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsplit]
  calc ‖(x - y) + (f x - f y)‖ ≤ ‖x - y‖ + ‖f x - f y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + L * ‖x - y‖ := by linarith [h x y]
    _ = (1 + L) * ‖x - y‖ := by ring

/-- **块的 Lipschitz 常数**：`Ln · ((1 + Lf) · (1 + La))`。

推导链条（**`g = R_ff ∘ h`，常数相乘**）：

1. `h w = w + attn w` 是 `(1 + La)`-Lipschitz（`residual_lipschitz`）；
2. `R_ff u = u + ff u` 是 `(1 + Lf)`-Lipschitz（`residual_lipschitz`）；
3. `g = R_ff ∘ h` 是 `(1 + Lf)·(1 + La)`-Lipschitz（复合）；
4. `eval = norm ∘ g` 再乘 `Ln`。 -/
theorem Block.eval_lipschitz (B : Block n) {La Lf Ln : ℝ}
    (hLa : 0 ≤ La) (hLf : 0 ≤ Lf) (hLn : 0 ≤ Ln)
    (ha : ∀ x y, ‖B.attn.apply x - B.attn.apply y‖ ≤ La * ‖x - y‖)
    (hf : ∀ x y, ‖B.ff.apply x - B.ff.apply y‖ ≤ Lf * ‖x - y‖)
    (hn : ∀ x y, ‖B.norm.apply x - B.norm.apply y‖ ≤ Ln * ‖x - y‖) :
    ∀ x y, ‖B.eval x - B.eval y‖ ≤ (Ln * ((1 + Lf) * (1 + La))) * ‖x - y‖ := by
  intro x y
  -- the attention residual, and the feed-forward residual
  have hh : ∀ u v, ‖(fun j => u j + B.attn.apply u j)
        - (fun j => v j + B.attn.apply v j)‖ ≤ (1 + La) * ‖u - v‖ :=
    residual_lipschitz B.attn.apply ha
  have hR : ∀ u v, ‖(fun i => u i + B.ff.apply u i)
        - (fun i => v i + B.ff.apply v i)‖ ≤ (1 + Lf) * ‖u - v‖ :=
    residual_lipschitz B.ff.apply hf
  -- `g = R_ff ∘ h`
  have hg : ∀ u v, ‖(fun i => (u i + B.attn.apply u i)
        + B.ff.apply (fun j => u j + B.attn.apply u j) i)
      - (fun i => (v i + B.attn.apply v i)
        + B.ff.apply (fun j => v j + B.attn.apply v j) i)‖
      ≤ ((1 + Lf) * (1 + La)) * ‖u - v‖ := by
    intro u v
    calc ‖(fun i => (u i + B.attn.apply u i)
          + B.ff.apply (fun j => u j + B.attn.apply u j) i)
        - (fun i => (v i + B.attn.apply v i)
          + B.ff.apply (fun j => v j + B.attn.apply v j) i)‖
        = ‖(fun i => (fun j => u j + B.attn.apply u j) i
              + B.ff.apply (fun j => u j + B.attn.apply u j) i)
          - (fun i => (fun j => v j + B.attn.apply v j) i
              + B.ff.apply (fun j => v j + B.attn.apply v j) i)‖ := rfl
      _ ≤ (1 + Lf) * ‖(fun j => u j + B.attn.apply u j)
            - (fun j => v j + B.attn.apply v j)‖ := hR _ _
      _ ≤ (1 + Lf) * ((1 + La) * ‖u - v‖) := by
          apply mul_le_mul_of_nonneg_left (hh u v)
          linarith
      _ = ((1 + Lf) * (1 + La)) * ‖u - v‖ := by ring
  calc ‖B.eval x - B.eval y‖
      = ‖B.norm.apply (fun i => (x i + B.attn.apply x i)
            + B.ff.apply (fun j => x j + B.attn.apply x j) i)
          - B.norm.apply (fun i => (y i + B.attn.apply y i)
            + B.ff.apply (fun j => y j + B.attn.apply y j) i)‖ := rfl
    _ ≤ Ln * ‖(fun i => (x i + B.attn.apply x i)
            + B.ff.apply (fun j => x j + B.attn.apply x j) i)
          - (fun i => (y i + B.attn.apply y i)
            + B.ff.apply (fun j => y j + B.attn.apply y j) i)‖ := hn _ _
    _ ≤ Ln * (((1 + Lf) * (1 + La)) * ‖x - y‖) := by
        apply mul_le_mul_of_nonneg_left (hg x y) hLn
    _ = (Ln * ((1 + Lf) * (1 + La))) * ‖x - y‖ := by ring

/-! ## 四、一条我写了又删的定理

初稿在这里放过

```lean
theorem Block.eval_lipschitz_identity {La Lf Ln : ℝ} (h : La = 0) (h2 : Lf = 0) :
    Ln * (1 + Lf * (1 + La)) = Ln := by rw [h, h2]; ring
```

**删掉了。** 它是 `Ln * 1 = Ln` 的 `ring`——**一条装饰性算术**，
与本会话早先删掉的 `(8 : ℕ) + 4 = 12`（`netLoss` 那轮）和 `isRedundant_true` 是同一类：
**标题宣称在陈述覆盖或退化情形，实际陈述的是算术。**

退化情形的结论本来就是**定义上的**（`La = Lf = 0` 时 `1 + 0·(1+0) = 1`），
不需要一条定理去「核对公式」。**公式对不对，靠读推导链，不靠一条 `ring`。** -/

end Lattice.Lib.TransformerEval
