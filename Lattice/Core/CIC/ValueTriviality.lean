import Mathlib
import Lattice.Core.CIC.Value
import Lattice.Core.CIC.Typing

/-!
# `typable_has_value` 是**空前提定理**：它不需要 `Typable`（阶段 5，宏观盘点）

## 怎么发现的

**第 794 轮的流程教训（手推已存在的引理）促使本轮做一次 CIC 层的完整盘点。
`Value.lean` 的名字看起来像「进展定理」，于是去读它的定义 —— 结果如下。**

## 事实

**`Value.lean` 的定义是：**

| 名称 | 内容 |
|:--|:--|
| `Value` | **`Term` 的结构镜像**：同样七个构造子 |
| `valueOf` | **`Term → Value`，全函数，对 `Term` 做普通递归** |
| `IsValueOf` | **`valueOf t = v`** |

**于是 `IsValueOf v t` 就是 `valueOf t = v`。而 `valueOf` 是全函数，所以**

```
∃ v, IsValueOf v t
```

**对**任意 `t : Term`**成立 —— 取 `v := valueOf t` 即可。这与 `Typable K Γ t` **毫无关系**。**

**=> `typable_has_value : Typable K Γ t → ∃ v, IsValueOf v t` 因此是**空前提**：
它的结论在没有前提时也成立。`Typable` 那一项对证明没有贡献。**

## 这意味着什么

**这不是错误 —— `Value.lean` 自己在文档里写明了「`Value` 是 `Term` 的结构镜像」，
所以这个结果是**自洽**的。但它**不是**进展定理（progress）：

- **进展定理**说的是「**良类型的封闭项**要么是值、要么能再走一步」；
- **本定理**说的是「每个项都有它的结构镜像」。**后者对 `app (lam A b) a`（一个 redex）
  同样成立，而进展定理**恰恰**要排除它。**

**=> 一个名字像进展、形式像进展、而在定义上对所有项成立的定理，是**判据的漏洞**：
它让「我们有进展定理」这句话看起来被证明了，而实际被证明的是别的东西。**

## 本文件做什么

**把「结论不需要前提」写成一条定理（`value_exists_unconditionally`），
从而把上面那段话从散文变成可检查的事实。** **不修改 `Value.lean`、不删除任何定理 ——
`typable_has_value` 依然为真，只是它的前提是多余的。** -/

namespace Lattice.Core.CIC

/-- **每个项都有结构镜像，**不需要任何前提**。**

**`∃ v : Value, IsValueOf v t`。**

**=> 与 `typable_has_value` 的结论相同，但这里没有 `Typable` 前提。
这证明后者是空前提定理。** -/
theorem value_exists_unconditionally (t : Term) : ∃ v : Value, IsValueOf v t :=
  ⟨valueOf t, rfl⟩

/-- **`typable_has_value` 的结论不依赖 `Typable`。**

**=> 写成显式形式：给定任意 `t`，都得到那个 `∃ v, IsValueOf v t`，
而**不需要**构造 `K`、`Γ` 或任何 `Typable K Γ t` 的证据。** -/
theorem typable_has_value_premise_redundant (t : Term) :
    (∃ v : Value, IsValueOf v t) := value_exists_unconditionally t

end Lattice.Core.CIC
