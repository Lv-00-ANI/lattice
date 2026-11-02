# ARCHITECTURE CARRIERS

## 1. 定位

Conv / Attention / Norm / DAG 是 **L3 载体插件**，不是 LATTICE 主线。

LATTICE 主线是符号⇄权重转换；架构是转换的目标载体。

## 2. 目录

```text
Lattice/Plugins/Architectures/Conv/
Lattice/Plugins/Architectures/Attention/
Lattice/Plugins/Architectures/Norm/
Lattice/Plugins/Architectures/DAG/
```

每个插件包含：

```text
Manifest.lean
Semantics.lean
Soundness/
Equivariance/
Laws/
Idempotence/     -- Norm
Confluence/      -- DAG
Plugin.lean
```

## 3. 接口

```lean
structure CarrierPlugin where
  key     : ServiceKey
  Arch    : Type
  compile : Symbol → Arch
  extract : Arch → Symbol
  sound   : ...
```

## 4. 四个载体

### Conv

- 符号：卷积/权重共享约束；
- L3：Toeplitz/循环结构；
- 证明：`compile_conv_sound`、`extract_conv_sound`、`conv_equivariant`。

### Attention

- 符号：路由/选择约束；
- L3：softmax 核；
- 证明：行随机、mask 语义、`attn_equivariant`。

### Norm

- 符号：尺度/平移约束；
- L3：幂等归一化；
- 证明：`norm_idem`、`norm_equivariant`。

### DAG

- 符号：程序/约束图；
- L3：顺序/并行/残差；
- 证明：`denote_seq`、`denote_par`、`denote_resid`、`dag_confluence`。

## 5. 依赖

```text
Carrier < Compiler < Extractor < Verifier < Repairer
```

不得反向依赖。

## 6. 非目标

- 不用架构空间取代 L0–L3；
- 不要求所有架构先统一；
- 不把 Conv/Attention/Norm/DAG 当证明主线。
