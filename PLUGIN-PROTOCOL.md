# PLUGIN PROTOCOL

## 1. 服务键

```lean
structure ServiceKey where
  name    : Name
  version : Version
```

服务类别：

- `SymbolDomain`；
- `Carrier`；
- `Compiler`；
- `Extractor`；
- `Verifier`；
- `Repairer`；
- `ArtifactStore`；
- `CertStore`。

## 2. 插件

```lean
structure LatticePlugin where
  name     : Name
  requires : Finset ServiceKey
  provides : Finset ServiceKey
  install  : LatticeContext → Fiber
  dispose  : Fiber → LatticeEffect
```

插件是**能力契约**，不是“一个文件”。

## 3. 效应

```lean
structure LatticeEffect where
  run  : State → State × (State → State)
  mode : EffectMode
  cert : Option Cert
```

```lean
inductive EffectMode
| reversible
| snapshot
| approximate
| irreversible
```

- `reversible`：`undo ∘ run = id`；
- `snapshot`：保存旧 artifact，恢复；
- `approximate`：显式 ε，undo 用 snapshot；
- `irreversible`：必须显式 commit，不能假装可逆。

## 4. Fiber

```lean
inductive FiberState
| inactive
| active
| unloading
| failed
```

规则：

1. 依赖满足才进入 `active`；
2. provider 卸载前，依赖者先 `deactivate`；
3. `failed` 不参与 confluence；
4. 证书在 provider/artifact 变化时失效。

## 5. 依赖顺序

```text
Carrier < Compiler < Extractor < Verifier < Repairer < Orchestrator
```

禁止反向依赖。

## 6. 证书

```lean
structure Cert where
  specHash     : Hash
  providerIds  : Finset ProviderId
  artifactHash : Hash
```

- provider 变 → `providerIds` 不匹配 → stale；
- artifact 变 → `artifactHash` 不匹配 → stale；
- 旧证书不能证明新模型。

## 7. Registry

```lean
def proofRegistry  : List VerifiedPlugin := [...]
def systemRegistry : List SystemPlugin   := [...]
```

- `proofRegistry` 进入 `ProofComplete`；
- `systemRegistry` 包括 C backend、loader、conformance，不进入 `ProofComplete`。
