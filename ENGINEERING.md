# ENGINEERING

## 0. 定位

工程部分，**不是**证明部分。

**新增（2026-11-05）：CIC 的「实现」也属于工程侧。**

| 对象 | 归属 |
|:--|:--|
| CIC 的**语法**（`Term` / `Level`） | 证明侧（`Lattice/Core/CIC/Syntax.lean`） |
| CIC 的**类型规则**（`Typable`） | 证明侧（`Lattice/Core/CIC/Typing.lean`） |
| CIC 的**归约**（β/δ/ι/ζ） | 证明侧（`Lattice/Core/CIC/Reduction.lean`） |
| CIC 的**实现**（parser / elaborator / evaluator） | **工程侧，已单独立项** |
| 几何 → CIC 的 `encode` | 证明侧（`Lattice/Core/CIC/Encode/Geometry.lean`） |
| 五载体的 `encode` / `decode` | 证明侧（待建） |

因此：语言实现换了，Lean 证明不失效——证明只依赖语法与规则。

## 1. 范围

包含：

- 格式解析；
- 权重文件 I/O；
- 导出；
- C ABI；
- conformance；
- runtime loader；
- 插件目录加载；
- **CIC 实现（parser / elaborator / evaluator）**。

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

**当前状态（2026-11-05）：** `RawModel` 与 `FormatAdapter` **全库 0 处**；
本节是规格，不是实现陈述。

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

**当前状态：** `Lattice/Plugins/Backends/C/` **不存在**；`systemRegistry` **全库 0 处**。
C 代码不写，但 ABI / 布局 / 序列化 / conformance / refinement 的 **Lean 侧规格**要写。

## 5. conformance

- 测试证据，不是定理；
- 不冒充 `Proof`；
- 误差比较必须声明绝对/相对/ULP。

**当前状态：** `CInterface/{ABI,LayoutBytes,Serialization,Conformance}.lean` 存在，
但是 **Lean 规格**，与 `SEMANTICS-MAINLINE.md` 的 12 个 `lattice_*` 不同名不同量
（`ABI.lean:126` 的 `abiTable_length = 11`）。

## 6. 信任边界

- 外部训练器；
- PyTorch/JAX；
- C 实现；
- 私有格式；
- 浮点误差；
- **CIC 实现（parser / elaborator / evaluator）**。

工程失败不影响数学定理，但影响系统正确性；必须在文档中显式声明。

## 7. 干净构建

`lakefile.toml:27` 的 `packagesDir = "../lattice/lean/.lake/packages"` 指向仓库外。
干净 checkout 需要：

1. 删除 `packagesDir` 行；或
2. 让 `.github/workflows/lattice.yml` 的 materialise 步骤执行该删除。

当前 workflow **没有**执行这一步；这是干净 checkout 不可构建的**唯一阻塞**。
