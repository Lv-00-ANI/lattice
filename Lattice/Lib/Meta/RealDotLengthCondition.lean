import Mathlib

/-!
# `dot` 的长度条件：截断缺陷的机器可检见证与长度假设的**必要性**

## 事实（WP-17 实测，`ConvertVectorLinear.lean:35-36` 逐字）

> 注意：**本文件全部跨文件行号锚点（含本节）系 B475 实测，会随对应文件改动而漂移，引用前须复核。**

```lean
def dot (a x : List Int) : Int :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0
```

`List.zip` **静默截断到较短表**。⇒ `dot` 是**最长公共前缀**点积，**不是**数学上的内积。

实测（`decide`，见 §2）：
* `dot [1,2,3] [5] = 5`
* `dot [] [7] = 0`
* `dot [1,2] [3,4] = dot [1,2] [3,4,99] = dot [1,2] [3,4,1000] = 11`

## 注意：一处**先前的表述需要精确化**（WP-17 的净增量）

`chain-v2/L21` 主张：桥 `dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x)`
**必须**携带 `h : x.length = a.length`，否则「把截断缺陷焊进泛化层」。

> 注意：**该「必须」已被机器否证（后续批次）**：`RealListFinBridge.lean` 中
> `dot_eq_dotProduct (a x : List Int) : dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x)`
> **无需任何长度条件**即成立（`lake build RealListFinBridge` `exit 0`，公理 ⊆ 三件套，无 `sorryAx`）。
> 且 `x = []`、`a = [3,5]` 的所谓反例【不存在】——**两侧都 = 0**（`rfl` 可证）。
> 更一般地，桥对**模数不敏感**（`max a.length x.length` 同样成立）。

注意：**但本轮小整数穷举显示：朴素 Σ 表述【并不】被截断否证。**
对 `dot a x = Σ_{i<a.length} aᵢxᵢ` 与 `dot a x = Σ_{i<x.length} aᵢxᵢ` 两种读法，
在 `|a|,|x| ≤ 3`、系数 `∈ [-2,2]` 的全枚举下，**反例数 = 0** ——
原因是**补零与截断在此处恰好同效**（被丢弃的因子若视为 0，两项相等）。

⇒ ⭐ **长度假设的必要性【不体现在 Σ 等式上】，而体现在【点分离性】上**：
`dot a ·` 在固定 `a` 下**不是单射** —— `dot a (x ++ t) = dot a x` 对**一切** `t` 成立。
**这才是必须携带长度条件的机器可检理由。**

## 判据（`chain-v2/L21:196` 要求的反向门禁）

> 去掉 `h : x.length = a.length` 后，该陈述**必须是假命题** —— 用具体值给出机器验证反例。

本文件按 `PROCESS.md §3.3` 五步处置落实该门禁：
① 构造反例并核对它满足原命题全部假设；② 三分类；③ 改陈述为真但更弱；
④ 逐字登记原陈述为假 + 反例 + 为何弱化；⑤ ⭐ **把反例固化为定理**（防复活）。

## 诚实边界

* 注意：本文件**未**修改 `ConvertVectorLinear.lean`（链关键文件）。修正方案见
  `_recon2/patches/WP-17-dot-length.md`。
* 注意：~~本文件是**新增文件**，**未注册 roots**（roots 由 coordinator 独占）；
  故它**不参与全量构建**，其编译证据来自一次性探针。~~
  **【已订正】本文件现已在 `lakefile.toml:9` 的 `roots` 中**（实测），参与全量构建。
  注意：但其**生产消费者仍为 0**（`grep '^import RealDotLengthCondition'` 全仓 0 命中）——
  「转正 ≠ 接线」的第 4 个实例，且主体恰是**为修正该缺陷而写的文件本身**。
* 注意：本文件的 `dot` 是**本地重声明**（与 `ConvertVectorLinear.dot` 定义逐字相同），
  以便**自包含、可独立编译**；这本身即 §5 登记的「`dot` 被 5 处重复声明」的实例。
-/

namespace Lattice

/-! ## §1 本地点积：与 `ConvertVectorLinear.lean:35-36` **逐字相同** -/

/-- 点积（List 版）：`Σ a[i]*x[i]` —— **截断到较短表**。

注意：本定义与 `ConvertVectorLinear.lean:35-36` 逐字相同，此处本地重声明
以保持本文件自包含（该重复本身是登记项）。 -/
def dotL (a x : List Int) : Int :=
  (a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0

/-! ## §2 截断的直接见证（`decide`，机器可检） -/

/-- ⭐ **截断见证 1**：`a` 比 `x` 长时，`a` 的尾部被静默丢弃。 -/
theorem dot_truncates_a : dotL [1, 2, 3] [5] = 5 := by decide

/-- ⭐ **截断见证 2**：`a` 为空 ⟹ 结果恒 0，`x` 完全被忽略。 -/
theorem dot_empty_left_ignores_x : dotL ([] : List Int) [7] = 0 := by decide

/-- ⭐ **截断见证 3**：`x` 的尾部被静默丢弃（三个不同的 `x` 给出同一个值）。 -/
theorem dot_truncates_x :
    dotL [1, 2] [3, 4] = 11 ∧ dotL [1, 2] [3, 4, 99] = 11
      ∧ dotL [1, 2] [3, 4, 1000] = 11 := by decide

/-- 对照：等长时行为正常。 -/
theorem dot_same_length_ok : dotL [1, 2] [3, 4] = 11 := by decide

/-! ## §3 ⭐⭐ 核心：`dot` 在固定 `a` 下**不是单射**（长度假设的真正必要性）

`a.zip (x ++ t) = (a.zip x)` **恒成立**（当 `a` 不长于 `x` 时），
故把任意尾巴续在 `x` 后面**不改变** `dot` 的值。

这是「点分离」类陈述**必须**携带长度条件的机器可检理由：
没有长度条件时，`dot a x = dot a x'` **不能**推出 `x = x'`。 -/

/-- ⭐ **定向辅助引理**（`PROCESS.md §8` 判据 7：`rw` 是**句法**匹配、不归一化到 `defeq`，
故把需要的形状**陈述成一条定向定理**，比在原地 `rw` 更稳）。

`List.zip_append` 的形状是 `zip (l₁ ++ r₁) (l₂ ++ r₂) = zip l₁ l₂ ++ zip r₁ r₂`
—— 注意：**两侧都必须是 `++`**。而主证明中的目标形如 `a.zip (…)`，
其**左操作数是 `a`（不是 `++`）**，故 `rw [List.zip_append …]` 匹配不上。
本引理先把 `a` 写成 `a ++ []`，再套用。 -/
theorem zip_append_right (a p q : List Int) (h : a.length = p.length) :
    a.zip (p ++ q) = a.zip p ++ ([] : List Int).zip q := by
  -- `zip_append` 需要**两侧都是 `++`**；把 `a` 与 `p` 各补一个 `[]` 以凑形。
  have key := List.zip_append (l₁ := a ++ []) (r₁ := ([] : List Int))
                (l₂ := p ++ []) (r₂ := q) (by simpa using h)
  simpa using key

/-- ⭐ **尾部无关性的核心引理**：当 `a.length ≤ x.length` 时，`a.zip` 对 `x` 的**任意**尾部无感。

注意：证明**不**走「`x = take ++ drop` 后重写」那条路 —— 那条路会同时改写
**RHS 里的 `x`**，使目标退化成含 `take a.length (take a.length x ++ drop a.length x)`
的自指形状（这正是原稿 `:107` 的 unsolved goals）。
改为**直接对 `x` 作结构归纳**，前提 `h` 随之变弱/变强，`zip_append_right` 仅在
「`a` 非空而 `x` 非空」的可控场合使用。 -/
theorem zip_append_tail_eq (a x t : List Int) (h : a.length ≤ x.length) :
    a.zip (x ++ t) = a.zip x := by
  induction a generalizing x with
  | nil => simp
  | cons y a' ih =>
    cases x with
    | nil => simp at h
    | cons z x' =>
      -- a = y :: a', x = z :: x'  ⟹ 逐点剥离，化为对 (a', x') 的同一命题
      simp only [List.length_cons, Nat.succ_le_succ_iff] at h
      simp only [List.cons_append, List.zip_cons_cons]
      rw [ih x' h]

/-- ⭐⭐ **主定理（反例固化为定理，防复活）**：
`dot` 对 `x` 的**任意尾部**无感 —— 只要 `a.length ≤ x.length`。 -/
theorem dot_append_tail_eq (a x t : List Int) (h : a.length ≤ x.length) :
    dotL a (x ++ t) = dotL a x := by
  simp only [dotL, zip_append_tail_eq a x t h]

/-- ⭐⭐ **点分离性为假**（把「必要性」做成定理）：
存在 `x ≠ x'` 使 `dot a x = dot a x'` —— 故任何形如
`dot a x = dot a x' → x = x'` 的陈述**在没有长度条件时是假的**。 -/
theorem dot_not_injective_witness :
    ∃ x x' : List Int, x ≠ x' ∧ dotL [1] x = dotL [1] x' :=
  ⟨[1], [1, 0], by decide, by decide⟩

/-- 同一见证的具体值（便于人工核对）。 -/
theorem dot_not_injective_concrete :
    dotL [1] [1] = dotL [1] [1, 0] ∧ ([1] : List Int) ≠ [1, 0] := by decide

/-! ## §4 与链语义的连接：满足集对尾部不敏感

`VectorConstraintSat c x := dot c.a x + c.b = 0`。
因 `dot c.a (x ++ t) = dot c.a x`（`c.a.length ≤ x.length`），
**约束的满足性对 `x` 的尾部完全无感**。 -/
/-- 链级语义的局部重声明（与 `ConvertVectorLinear.lean:38-39` 同形）。

注意：**订正（本文件首版缺陷）**：首版写作 `def satL (a b : List Int) (c : Int) (x) := dotL a x + c = 0`
—— 把原型的 `c : VectorConstraint`（字段 `a : List Int`、`b : Int`）**拆成松参数时，
误把「权重向量 `b`」当成了「常数项」**，导致 `b` 在定义体中**从未出现**
（编译器报 `unused variable b`，依 `PROCESS.md §4.6` 那是「假设写松」的机械信号）。

原型的两个字段语义是：`c.a : List Int`（权重）与 `c.b : Int`（常数项）。
故本处的参数应取 `(a : List Int) (b : Int)` —— **`b` 必须是 `Int` 且进入定义体**。

⇒ 这**不是**在消除警告，而是**改正一个语义转写错误**：
`b` 由「未使用的死变量」变为**承重的常数项**。 -/
def satL (a : List Int) (b : Int) (x : List Int) : Prop :=
  dotL a x + b = 0

/-- ⭐ **满足性对尾部不敏感**：若 `x` 满足，则 `x ++ t` 也满足。

注意：条件仍须 `a.length ≤ x.length`（不是 `≤ (x++t).length`）：
`zip_append_tail_eq` 的假设是「`a` 不长于**原** `x`」，这是最弱的前提。 -/
theorem sat_append_tail (a : List Int) (b : Int) (x t : List Int)
    (h : a.length ≤ x.length) :
    satL a b x → satL a b (x ++ t) := by
  intro hx
  simpa [satL, dot_append_tail_eq a x t h] using hx

/-- ⭐ **具体见证**：约束 `a=[1,1], b=-3`（即 `x₀+x₁-3=0`）。

* `[3]` 满足（`dot [1,1] [3] = 3`，`3 + (-3) = 0`）
* `[3, 0]` 满足（尾部 `0` 无感）
* `[3, 100, 100]` **不**满足（第 2 个分量被计入 ⟹ `103 - 3 = 100 ≠ 0`）

注意：注意 `[3]` 与 `[3,0]` 的区别：`x` 比 `a` **短**时，缺的分量**视为不存在**（不进求和），
故 `[3]` 满足而数学上 `x₀+x₁-3 = 0` 需要 `x₁ = 0`。
**这正是「截断」在链语义上的可观测效果。**

注意：`satL` 是按 `def` 定义的 `Prop`，`decide` 不会自动展开它
（`Decidable (satL …)` 无法合成）⟹ 必须显式 `unfold satL` 后再 `decide`。
这本身是判读点：**「定义性包裹」会挡住 `decide`**。 -/
theorem sat_tail_insensitive_concrete :
    satL [1, 1] (-3) [3] ∧ satL [1, 1] (-3) [3, 0]
      ∧ ¬ satL [1, 1] (-3) [3, 100, 100] := by
  unfold satL dotL
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⭐ **短 `x` 被接受**：`x = [3]` 满足「`x₀+x₁-3=0`」，而 `x` 只有 1 个分量。

即：**维数不匹配不被拒绝，缺失分量被静默当作「不存在」而非「0」**。 -/
theorem sat_accepts_short_x : satL [1, 1] (-3) [3] := by
  unfold satL dotL; decide

/-! ## §5 登记：`dot` 的重复声明（本文件即第 6 处）

`dot`（`List Int` 版）在以下模块**各自独立声明**（定义逐字相同）：

| 模块 | 行 | 在 roots |
|:--|--:|:--:|
| `ConvertVectorLinear` | 35 | 成立 |
| `RealRoundtripNondegenerate` | 52 | 成立 |
| `_D2-1` | 52 | 不成立 scratch |
| `_D2-3` | 76 | 不成立 scratch |
| `_S-04` | 112 | 不成立 scratch |
| **本文件 `dotL`** | — | 成立 **已注册**（订正；原写「未注册」已过期） |

注意：**行号锚点的时效性**：上表各行号系**实测取值**（观测时点：B475 批次），
均为**跨文件**引用，会随对应文件改动而漂移 —— 引用前须复核。
可复跑核验（在仓库根 `lattice/` 下执行）：

```powershell
Select-String -Path lean/ConvertVectorLinear.lean,lean/RealRoundtripNondegenerate.lean,
    lean/_probes_archived/_D2-1.lean,lean/_probes_archived/_D2-3.lean,
    lean/_probes_archived/_S-04.lean -Pattern 'def dot'
```

（注：`_D2-1`/`_D2-3`/`_S-04` 三个 scratch 探针现位于 `_probes_archived/` 子目录下。）

注意：另有 `RealLv00Compiler.lean:199` 的 `dot (p q : ℝ × ℝ) : ℝ` —— **同名不同型**，
按 `chain-v2` 四分判据属 **(ii) 命名冲突，不可合并**。
（同一跨文件锚点时效性告警适用；`Select-String -Path lean/RealLv00Compiler.lean -Pattern 'def dot'` 可复核。）

⇒ **本节的认定是「只登记不合并」**：3 个 roots 模块的同名同型同义 `dot`
是**真重复**（判据 (i)），但**合并会改动链关键文件**，超出本 WP 范围。 -/

end Lattice
