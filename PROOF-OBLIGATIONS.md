# PROOF OBLIGATIONS

本文件把“证明部分完成”拆成可验收的 Lean 定理。
**每条义务在 CIC 载体上陈述**；几何版本作为 Domain 实例保留（见 `CARRIER-CIC.md`）。

不使用 2/12、解处、SafeBranch、register 作为完成。
不使用 `String` 伪证明、`→ True`、自数 `rfl`、别名 def 作为完成。

---

## 载体约定

| 符号 | 含义 |
| `Term` / `IR` | CIC 语法 `Term`；IR 是 `Term` 的结构层（`parse : Term → Option IR`） |
| `Typable Γ t A` | 在 context `Γ` 下 `t : A` 可类型化（CIC 层） |
| `WellFormed S` | IR `S` 的关系集自洽（IR 层） |
| `compile : IR → Weights` | IR 编码到抽象权重 |
| `parse : Term → Option IR` | CIC 语法解析成结构 |
| `steps t` | `t` 的归约步数上界 |
| `ε` | 单步误差界 |

几何对应物（`Holds`、`Pt n`、`ExpressibleSpec`）只出现在 `Domains/Geometry` 的实例陈述里。

---

## T0 Construct

```lean
construct_sound     : WellFormed S ∧ parse t = some S → Models (compile S) (semantics S)
construct_complete  : WellFormed S → ∃ W, compile S = W
construct_canonical : compile S = W → ∀ W', Models W' (semantics S) → canonical W ≤ canonical W'
construct_approx    : compile S = W → ∀ x, |denote W x - denote S x| ≤ size S * ε
```

- 构造的对象是 **term**，不是点配置；
- “可构造”= 可类型性 + `compile` 有定义，**可判定**；
- 权重字面量不算 construct。

**几何 Domain 实例：** `no_specSolver` 已证任意 spec 的构造器不存在，
因此几何版只在 family 上陈述，且必须显式标注 family 名称。

---

## T1 Compile

```lean
compile_sound : WellFormed S → Models (compile S) (semantics S)
```

- 编译后的对象保语义；
- **结论必须出现 `t`**：不允许出现“结论与输入无关”的形状；
- 前提不空转（不得用 `hR : R.merged = [c]` 之类把输入钉死后丢弃）。

---

## T2 Penalty / Modulus

精确载体：

```lean
penalty_exact :
  ∀ c ∈ exactConstructors, penaltyLoss c Φ = 0 ↔ Holds c Φ
```

一般情形：

```lean
penalty_min_to_violation :
  IsLocalMin (fun y => loss (compile y)) x → violation (compile S) x ≤ size S * ε
```

要求：

- 精确只在具体载体声明，且构造子集合**显式列出**；
- 一般情形必须有 `g(ε)` 或 `steps t * ε` 形式的显式界；
- `ε → 0` 有定理（或 `steps t = 0` 退化为 exact）；
- 不接受 2/12、解处、SafeBranch、`g ≡ 0`。

---

## T3 Extract

```lean
extract_compile      : extract (compile S) = S            -- compile 单射，extract 是其逆
flatten_injective    : Function.Injective flatten
semantic_not_injective : ¬ Function.Injective (fun c => denote c)
no_extractor_preserves_both :
  ¬ ∃ E, (∀ S, E (compile S) = S) ∧ (∀ c c', denote c = denote c' → E c = E c')
```

- 对象层双射；
- 参数层单射非同构；
- 语义层不可逆；
- 两层同时不可能。

**纪律：** `extract_compile` 必须是**定理**，不能是 `Representation.roundtrip` 这样的结构字段投影。

---

## T4 Repair

```lean
repair_progress        : ¬ Sat t → μ (repair t) < μ t ∨ Sat (repair t)
loop_converges         : ∃ n, Sat (iterate n t)
-- **Round 776: 本行的名字在主树里不存在。** 实际承载者是
-- `Repair.progress : ∀ (R : Repair α) (x : α), ∃ n, R.Sat (R.iterate n x)`
-- 与 `RepairConvergence.converges_within : R.Sat (R.iterate (R.μ x) x)`。
-- **→ 规范保留原命题，但把名字标为「待对齐」**，而不是把它伪造成存在。
conj_loop_fixed_point  : ∃ r, Sat r ∧ fix r = r ∧ extract (compile r) = r
```

- 收敛；
- 修复不破坏语义；
- 不动点存在；
- 反例可复现。

**纪律：** `Repair.atomic` 与 `decreases` 的关系必须写明；
`conj_loop_fixed_point` 不得映射到 `atomic_of_zero_iff` 之类的别名。

---

## T5 Recovery

```lean
lattice_recovery_exact :
  unload P s = s' → effectOf P s = e → undo e s' = s
```

- 卸载插件只撤销自己的影响；
- 其他插件效果保留；
- 无 inverse 时用 snapshot；
- 必须有 `unload_removes_only_own` 形式，而不只是“整序列 undo”。

---

## T6 Spatial

```lean
lattice_ordering :
  requires P Q → ¬ active Q s → ¬ active P s
lattice_resolution_coherent :
  provider P s → provider P s' → cert P s = cert P s' ∨ invalidated (cert P s)
```

- 依赖满足才启动（`canActivate`）；
- provider 替换时先 deactivate 依赖者；
- 证书在 provider 变化时失效。

**纪律：** 不得只有“停用门”而没有“激活门”。

---

## T7 Confluence

```lean
lattice_confluence :
  ∀ trace, quiescent (run trace s) → run trace s ≃ construct (finalSpec trace)
```

条件见 `CONFLUENCE.md`。

**纪律：** `≃` 是 `ResultEquiv` 的 `behavior` 或 `approx` 口径；
不得用 `Option.bind_assoc` 之类的结合律冒充汇合。

---

## T8 Failure

```lean
lattice_failure_isolated :
  failed P s → (∀ Q ≠ P, behavior Q s = behavior Q s') ∧ ¬ cert P s'
```

- 失败插件不影响其他 fiber；
- 回滚；
- 不产生证书；
- confluence 排除失败分支。

**纪律：** 不得用 `if failing then none` 的定义展开冒充隔离。

---

## Plugin

```lean
plugin_registry_complete : PluginRegistryComplete
```

- 每个定理归属一个插件；
- 每个插件有 `PluginProof`；
- claim 与 proof **按 `Obligation.theoremName` 逐条对应**，
  不是“非空 ⇒ 12 字段全真”；
- registry 中所有插件通过；
- 插件的 `Obligation.theoremName` 必须在树中真实存在
  （由 `gov/check_obligation_proofs.py` 检查 —— 它扫描 74 条义务，报告 `no ghost names, no missing files`；第 195 轮核对时发现原文引用的 `check_obligation_names.py` 并不存在，而实际承担该职责的是 `check_obligation_proofs.py`）。

**纪律：** `pluginCensusSize` 等计数不得手写字面量；
`migratedPluginCount` 必须由 `proofRegistry.length` 推导。

---

## 不包含

- format parsing；
- weight I/O；
- C；
- conformance；
- external trainer；
- SFT/DPO/RLHF；
- optimizer。
