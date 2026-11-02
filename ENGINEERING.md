# ENGINEERING

## 1. 范围

工程部分，不是证明部分。

包含：

- 格式解析；
- 权重文件 I/O；
- 导出；
- C ABI；
- conformance；
- runtime loader；
- 插件目录加载。

## 2. 格式适配器

```lean
structure RawModel where
  bytes  : ByteArray
  format : Format

structure FormatAdapter where
  parse  : RawModel → Option ModelArtifact
  export : ModelArtifact → Option RawModel
```

- `parse` 失败返回 `none`；
- `export` 可能丢精度；
- 不支持格式显式拒绝；
- 不把 `Opaque` 当 `Structured`。

## 3. 权重文件

只处理模型/权重文件：

- 不含 optimizer state；
- 不含训练日志；
- 不含数据集；
- 不含配置文件。

## 4. C 后端

```text
Lattice/Plugins/Backends/C/
  Manifest.lean
  AST.lean
  Refinement/
  Conformance/
```

- 在 `systemRegistry`；
- 不进入 `ProofComplete`；
- 将来若要进入：补 C 形式语义，新增 `CRefinement` 义务，另立 ADR。

## 5. conformance

- 测试证据，不是定理；
- 不冒充 `Proof`；
- 误差比较必须声明绝对/相对/ULP。

## 6. 信任边界

- 外部训练器；
- PyTorch/JAX；
- C 实现；
- 私有格式；
- 浮点误差。

工程失败不影响数学定理，但影响系统正确性；必须在文档中显式声明。
