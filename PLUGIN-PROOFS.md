# PLUGIN PROOFS

## 1. 原则

- 插件 = 能力契约 + `Semantics` + 语义化证明 + `Manifest`；
- 不是“一个文件一个插件”；
- 每个定理必须归属一个插件；
- Lean 证明是静态包，运行时插件实例是动态的；
- 每个插件在其层级目录下有语义命名的证明子文件夹。

## 2. 目录

```text
Lattice/Plugins/
  Core/
    Constraint/
      Manifest.lean
      Semantics.lean
      Soundness/
      Completeness/
      Laws/
      Plugin.lean
    Repair/
  Runtime/
    Tokenization/
    ProgramSemantics/
  Domains/
    Constraints/
      Penalty/
        Manifest.lean
        Semantics.lean
        Soundness/
        Exactness/
        Approximation/
        Plugin.lean
      NetLoss/
    Geometry/
  Compose/
  Semantics/
  Architectures/
    Conv/
      Manifest.lean
      Semantics.lean
      Soundness/
      Equivariance/
      Laws/
      Plugin.lean
    Attention/
    Norm/
    DAG/
  Backends/
    C/                -- systemRegistry，不进 ProofComplete
  Registry.lean
  SystemRegistry.lean
```

## 3. 语义命名

| 目录 | 内容 |
|:--|:--|
| `Soundness/` | 语义保持 |
| `Completeness/` | 覆盖/完备 |
| `Laws/` | 代数律 |
| `Exactness/` | 精确 iff |
| `Approximation/` | ε/误差 |
| `Recovery/` | 时间可组合 |
| `Spatial/` | 空间可组合 |
| `Confluence/` | 汇合 |
| `Equivariance/` | 群作用 |
| `Idempotence/` | 幂等 |
| `Invariants/` | 状态不变量 |
| `Refinement/` | C 形式语义（将来） |

## 4. Manifest

```lean
inductive ObligationKind
| soundness
| completeness
| laws
| exactness
| approximation
| recovery
| spatial
| confluence
| equivariance
| idempotence
| invariants
| refinement

structure Obligation where
  name        : Name
  kind        : ObligationKind
  theoremName : Name
  file        : Path

structure PluginManifest where
  name        : Name
  layer       : Layer
  requires    : Finset ServiceKey
  provides    : Finset ServiceKey
  obligations : List Obligation
  version     : Version
```

## 5. VerifiedPlugin

```lean
structure PluginProof where
  soundness     : ...
  completeness  : ...
  laws          : ...
  exactness     : ...
  approximation : ...
  recovery      : ...
  spatial       : ...
  confluence    : ...
  equivariance  : ...
  idempotence   : ...
  invariants    : ...

structure VerifiedPlugin where
  manifest : PluginManifest
  install  : LatticeContext → Fiber
  proof    : PluginProof
```

## 6. Registry

```lean
def proofRegistry  : List VerifiedPlugin := [...]
def systemRegistry : List SystemPlugin   := [...]
```

## 7. ProofComplete

```lean
def PluginRegistryComplete : Prop :=
  ∀ p ∈ proofRegistry,
    p.proof.soundness ∧ p.proof.laws ∧ ...

def ProofComplete : Prop :=
  T0 ∧ T1 ∧ T2 ∧ T3 ∧ T4 ∧ T5 ∧ T6 ∧ T7 ∧ T8 ∧
  PluginRegistryComplete
```

## 8. 依赖规则

- 证明文件夹只 import 本插件 `Semantics` 与更低层；
- `Plugin.lean` import 证明文件夹；
- `Registry.lean` import 所有 `Plugin.lean`；
- 禁止证明文件夹 import `Plugin.lean`；
- 禁止反向依赖上层。

## 9. 证明升级

```lean
structure ProofUpgrade where
  from                : Version
  to                  : Version
  strengthen          : ...
  backward_compatible : ...
```

- 不删除旧定理；
- registry 只启用最新版；
- `PROOF-DEBT` 按插件生成。

## 10. C

`Backends/C` 在 `systemRegistry`，不进入 `ProofComplete`。
只有将来补 C 形式语义时，才新增 `Refinement/` 并另立 ADR。
