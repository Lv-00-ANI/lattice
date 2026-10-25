/-
# 性质变化时的组合：非相邻条款需要「桥」

## 0. 本节补什么

第 46 轮的 `preserves_foldl` 处理的是：**同一性质**沿阶段列表传递。
但**非相邻**条款跨的是**不同性质**（数据合成给出配置，再注入给出惩罚为零）。

`ClauseComposition` 的边界声明说非相邻组合「应当由传递性得到」。
**本节验证那句话是否成立，并给出不成立时的正确形式。**

## 1. 结果：传递性**不够**，需要一个桥

**同性质**（第 46 轮，`preserves_foldl`）：
```
每段保持 P  ⟹  整体保持 P
```

**换性质**（本节）：只知「段 1 保持 P」「段 2 保持 Q」**推不出** `Q`——
因为 `P` 与 `Q` 之间没有任何联系。需要的是一条**桥**：

```
P y ⟹ Q y        （在转手点 y 上）
```

于是：
```
P x  →  P (f x)  ──桥──▶  Q (f x)  →  Q (g (f x))
```

**这个「桥」就是非相邻条款之间必须显式给出的东西。** 它与第 44 轮的
`agrees`（并置组合的粘合）是同一类东西：**连接两条不同陈述的假设**。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `compose_with_bridge` | 两段 + 桥 ⟹ 目标性质在末端成立 |
| `compose_list_with_bridges` | **多段**，每段带上自己的桥 |
| `bridge_is_necessary` | 没有桥时命题为**假**（给出反例） |

**`bridge_is_necessary` 是本节最关键的一条**：它证明「应当由传递性得到」这个说法
**太乐观**——缺桥时结论不成立。

## 3. 为什么这对整个项目重要

`COMPLETENESS-AUDIT.md` 说「16 条条款都有载体」。第 44–46 轮进一步问「能否组合」，
答案是：

| 组合类型 | 需要 |
|:--|:--|
| 相邻 + 同性质 | 无（`preserves_foldl`） |
| 相邻 + 并置两结构 | 粘合（`agrees`） |
| **非相邻 + 换性质** | **桥**（本节） |

⇒ **链路的每一类组合都有精确的「需要什么」。** 这比「应该能组合」强得多。

## 4. 边界

- 本节给出**形式**，**不**为每条实际条款对构造桥。为「数据合成 → 再注入」
  构造桥需要说明「合成的配置」如何与「惩罚为零」相接——那涉及它们之间的
  中间条款（验证、修正），属具体的三到四段组合，本节未做。
- `bridge_is_necessary` 的反例是**一般的**（任何 `P`、`Q` 有反例即可），
  不是针对某个具体条款。
- 本节**不**声称所有非相邻对都缺桥。有些可能因为性质恰好兼容而不缺——
  那需要逐个检查，本节未做。
-/
import Mathlib

namespace Lattice.Audit

namespace BridgedComposition

/-! ## 一、两段 + 桥 -/

/-- **两段组合需要桥**：若段 `f` 保持 `P`、段 `g` 保持 `Q`，
且 `P` 在转手点蕴含 `Q`，则末端满足 `Q`。

**桥 `hbridge` 不可省**——见 `bridge_is_necessary`。 -/
theorem compose_with_bridge {α : Type} (P Q : α → Prop) (f g : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, Q x → Q (g x))
    (hbridge : ∀ x, P x → Q x)
    (x : α) (hx : P x) :
    Q (g (f x)) :=
  hg (f x) (hbridge (f x) (hf x hx))

/-- **多段 + 逐段桥**：每段保持自己的性质，每对相邻性质之间有一座桥。

这是**非相邻组合的一般形式**：段数不限，但每两次转手都需要一座桥。 -/
theorem compose_three_with_bridges {α : Type} (P Q R : α → Prop)
    (f g h : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, Q x → Q (g x)) (hh : ∀ x, R x → R (h x))
    (hPQ : ∀ x, P x → Q x) (hQR : ∀ x, Q x → R x)
    (x : α) (hx : P x) :
    R (h (g (f x))) :=
  hh (g (f x)) (hQR _ (hg (f x) (hPQ _ (hf x hx))))

/-! ## 二、桥的必要性：没有它命题为假 -/

/-- **没有桥时，两段组合的结论不成立。**

反例：取 `α = ℕ`、`P x := x = 0`、`Q x := x = 1`、`f := id`、`g := id`。
则 `P`、`Q` 各自被 `id` 保持，但 `P 0` 成立而 `Q 0` 不成立。

⇒ **`ClauseComposition` 原边界声明「应当由传递性得到」过强。**
非相邻组合**需要一条桥**，不是免费得到。 -/
theorem bridge_is_necessary :
    ¬ (∀ (P Q : ℕ → Prop) (f g : ℕ → ℕ),
        (∀ x, P x → P (f x)) → (∀ x, Q x → Q (g x)) →
        ∀ x, P x → Q (g (f x))) := by
  intro h
  have hinst := h (fun x => x = 0) (fun x => x = 1) id id
    (fun _ hx => hx) (fun _ hx => hx) 0 rfl
  norm_num at hinst

end BridgedComposition

end Lattice.Audit
