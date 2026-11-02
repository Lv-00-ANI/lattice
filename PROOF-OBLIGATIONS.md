# PROOF OBLIGATIONS

本文件把“证明部分完成”拆成可验收的 Lean 定理。
不使用 2/12、解处、SafeBranch、register 作为完成。

## T0 Construct

```lean
construct_sound
construct_complete
construct_canonical
construct_approx
construct_from_scratch
```

- 只对 `ExpressibleSpec`；
- 权重字面量不算 construct。

## T1 Compile

```lean
compile_sound
```

- 编译后的对象保语义；
- 前提不空转。

## T2 Penalty

精确载体：

```lean
penalty_exact
```

一般情形：

```lean
penalty_min_to_violation :
  IsLocalMin (loss p) x → violation p x ≤ g ε
```

要求：

- 精确只在具体载体声明；
- 一般情形显式 `g ε`；
- `ε→0` 有定理；
- 不接受 2/12、解处、SafeBranch。

## T3 Extract

```lean
flatten_injective
semantic_not_injective
no_extractor_preserves_both
```

- 对象层双射；
- 参数层单射非同构；
- 语义层不可逆；
- 两层同时不可能。

## T4 Repair

```lean
repair_progress
loop_converges
conj_loop_fixed_point
```

- 收敛；
- 修复不破坏语义；
- 反例可复现。

## T5 Recovery

```lean
lattice_recovery_exact
```

- 卸载插件只撤销自己的影响；
- 其他插件效果保留；
- 无 inverse 时用 snapshot。

## T6 Spatial

```lean
lattice_ordering
lattice_resolution_coherent
```

- 依赖满足才启动；
- provider 替换时先 deactivate 依赖者；
- 证书在 provider 变化时失效。

## T7 Confluence

```lean
lattice_confluence
```

条件见 `CONFLUENCE.md`。

## T8 Failure

```lean
lattice_failure_isolated
```

- 失败插件不影响其他 fiber；
- 回滚；
- 不产生证书；
- confluence 排除失败分支。

## Plugin

```lean
plugin_registry_complete
```

- 每个定理归属一个插件；
- 每个插件有 `PluginProof`；
- registry 中所有插件通过。

## 不包含

- format parsing；
- weight I/O；
- C；
- conformance；
- external trainer；
- SFT/DPO/RLHF；
- optimizer。
