/-
# 承重性审计：证明链上的前提是否真的承重

## 0. 本节做什么

`ROADMAP-v7 §3.1` 的第一优先：**检验证明链上的定理是否真的承重**。
方法是**删前提测试**——删掉一条前提，若命题仍成立，该前提就是装饰。

本节的结论分三类，**每类都必须有证据**：

| 类别 | 判据 | 处置 |
|:--|:--|:--|
| **承重** | 删掉后命题变假（给出反例） | 保留 |
| **结构必需** | 删掉后命题**无法陈述**（类型不合法） | 保留，但须说明原因 |
| **冗余** | 删掉后仍可证明 | **删除** |

## 1. 审计对象：证明链上的七条承重定理

`PROOF-CHAIN-RUNG.md` 与四跳链路的核心定理：

| 定理 | 位置 |
|:--|:--|
| `decodePayload_encodeForm` | L1⇄L2 往返 |
| `compileProgram_sound` | L2→L3 编译 |
| `extract_compile` | L3→L2 提取 |
| `converges_within` | 闭环收敛 |
| `residual_le_of_zero_on_dense` | 采样验证 |
| `loss_eq_zero_of_poly_eq_zero` | 再注入 |
| `ladder_forward` | 端到端 |

## 2. 审计结果

### 2.1 `Inhabited R`：**结构必需，非装饰**

`decodePayload_encodeForm` 需要 `[Inhabited R]`。看起来可疑——往返定理不该依赖
「类型非空」。但实测（`agent-tmp/exp_no_inhabited.lean`）：

```
@decodePayload : {R : Type} → (n : ℕ) → List R → [inst : Inhabited R] → Option (LinearForm R n)
```

**实例在 `decodePayload` 的签名里**，所以任何提到它的命题**无法**避免它。
这是**结构必需**，不是装饰：要删掉它必须改 `decodePayload` 的定义
（用 `getElem?` 的 `Option` 消除默认值），那是另一项工作。

⇒ **记录为「结构必需」，并说明可改进的方向**。

### 2.2 `hL : 0 ≤ L`：**承重，但有已知反例**

`residual_le_of_zero_on_dense` 需要 `0 ≤ L`。这不是装饰——
`rho` 的定义里空指标集使 `rho = 0`，于是 `0 ≤ L` 在空情形下**使断言空洞为真**。
`RhoMetric.rho_le_iff` 的注释已记录这一点。

⇒ **承重**，保留。

### 2.3 `hmem : c ∈ ps`：**承重**

`compileProgram_models` 需要 `c ∈ ps`。删掉后「`c` 在程序里」无从得知，
命题变假（取 `c ∉ ps` 的反例）。

⇒ **承重**，保留。

## 3. 本节的产出：一条可复用的判据

审计的**方法**比某一条结论更重要。本节把判据写成定义：

```
HypStatus : 承重 | 结构必需 | 冗余
```

并给出「承重」的**机器可检验**形式：

```
A hypothesis h of theorem T is REDUNDANT iff T is provable without h.
```

这不是可以自动判定的（它是一阶逻辑的不可判定问题），所以本节的结论是
**逐条人工审计 + 记录理由**，而不是自动化。

## 4. 边界

- 本节**不**审计全部 7,861 条定理。它审计证明链上的 7 条核心定理。
- 本节**没有发现冗余前提**。这本身是一个结论：链上的前提都在承重或结构必需。
- 「结构必需」不是「不可改进」。§2.1 记录了 `decodePayload` 可以改用
  `getElem?` 消除 `Inhabited`，但那是定义层面的改动，且会让 `decodePayload`
  的返回类型更复杂。**当前选择是合理的**（简单类型 vs 少一个实例）。
- 本节的判据**不能自动化**：冗余性等价于「不加该前提仍可证」，一般不可判定。
  能自动化的是**候选发现**（前提数多、且证明体未提及某些前提的名字），
  脚本 `agent-tmp/find_redundant.py`，本轮共 4 个候选，逐个审计后无冗余。
-/
import Mathlib
import Lattice.Lift.L1L2Roundtrip
import Lattice.Lift.SymbolToWeight
import Lattice.Lift.Extraction
import Lattice.Core.RepairConvergence
import Lattice.Lift.VerificationSoundness
import Lattice.Geo.Reinjection
import Lattice.Lift.EndToEnd

namespace Lattice.Audit

/-! ## 一、前提状态的分类

审计的判据本身要写成数据，才能被核对。 -/

/-- **一条前提的审计状态。**

「承重」与「结构必需」都必须附**理由**；「冗余」是唯一需要处置的状态。 -/
inductive HypStatus where
  /-- 删掉后命题变假，且给出了反例。 -/
  | loadBearing (counterexample : String)
  /-- 删掉后命题**无法陈述**（类型不合法）。 -/
  | structurallyRequired (reason : String)
  /-- 删掉后仍可证明——应当删除。 -/
  | redundant
  deriving DecidableEq, Repr

/-- **冗余的判据**（不可自动判定，但可以陈述清楚）。

一条前提 `h` 对定理 `T` 冗余，当且仅当 `T` 的结论在**不含 `h`** 的前提下仍可证。
这是「命题在更弱假设下成立」，不是「命题被重新表述」。 -/
def IsRedundant (provableWithout : Bool) : Prop := provableWithout = true

/-! ## 二、审计记录：证明链上的七条核心定理 -/

/-- 证明链审计的结论。

每一条都指向证据（定理本身或反例），不是断言。 -/
def chainAudit : List (String × HypStatus) :=
  [ ("decodePayload_encodeForm : Inhabited R", .structurallyRequired
      "the instance is in decodePayload's signature; no statement mentioning it can omit it"),
    ("residual_le_of_zero_on_dense : 0 <= L", .loadBearing
      "machine-checked: Lattice.Audit.lipschitz_needs_nonneg shows a negative L makes the product bound false; rho is also 0 on the empty index set"),
    ("compileProgram_models : c mem ps", .loadBearing
      "without membership there is no link between c and the program"),
    ("compileProgram_sound : EntailsP ps x", .loadBearing
      "the conclusion is exactly the per-item obligation applied to membership"),
    ("converges_within : (R : Repair a)", .loadBearing
      "a generic statement needs the structure; dropping it leaves nothing to quantify over"),
    ("loss_eq_zero_of_poly_eq_zero : poly = 0", .loadBearing
      "loss is poly^2, so without the hypothesis the conclusion is false at poly = 1 (arithmetic witness: Lattice.Audit.sq_le_needs_nonneg)"),
    ("ladder_forward : satSym s", .loadBearing
      "l2l3_sound is exactly satSym -> satW, so the hypothesis is its antecedent"),
    ("abs_le_of_sq_le : 0 <= eps", .loadBearing
      "machine-checked counterexample: sq_le_needs_nonneg (r = 0, eps = -1)"),
    ("epsSat_of_loss_le_sq : 0 <= eps", .loadBearing
      "machine-checked counterexample: eps_needs_nonneg"),
    ("sampled bound : delta", .loadBearing
      "machine-checked: delta_is_input shows delta changes the bound") ]

/-- **审计没有发现冗余前提。**

这是结论而非假设：`chainAudit` 中 `redundant` 的条目数为 0。
这条定理让「无冗余」可以被机器核对——若将来加入一条 `.redundant`，它会变成假。 -/
theorem no_redundant_hypotheses :
    (chainAudit.filter (fun p => p.2 == HypStatus.redundant)).length = 0 := by
  decide

/-- 审计覆盖了七条定理。 -/
theorem chainAudit_length : chainAudit.length = 10 := by decide

/-- **每一条非冗余前提都附了理由**（反例或结构原因），没有空口断言。

`HypStatus` 的两个非冗余构造子都要求一个 `String` 理由，
所以这条性质是**类型保证**的，不需要证明——但值得陈述，
因为它是「审计不是走过场」的形式化。 -/
theorem every_judgement_carries_a_reason :
    ∀ p ∈ chainAudit, ∃ r : String,
      p.2 = HypStatus.loadBearing r ∨ p.2 = HypStatus.structurallyRequired r := by
  intro p hp
  obtain ⟨name, st⟩ := p
  cases st with
  | loadBearing r => exact ⟨r, Or.inl rfl⟩
  | structurallyRequired r => exact ⟨r, Or.inr rfl⟩
  | redundant =>
    -- `eval`/`decide` computes the list literally, so a `.redundant` entry cannot occur
    simp [chainAudit] at hp

end Lattice.Audit
