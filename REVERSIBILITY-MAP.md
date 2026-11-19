# `REVERSIBILITY-MAP.md` —— 每一跳的「可逆性 + 信息丢失」证据地图

> **状态：** 第 977 轮建立。由 `gov/audit_reversibility_coverage.py` 测量，`--check` 守护本文件的每个定理名。
> **定位：** 回答「哪一跳还缺证据」。**不要靠台账猜**——第 972 轮我猜错了 O-2，第 977 轮我猜错了「数据跳缺丢失定理」。

---

## 1. 为什么需要这张图

**目标要的是一条闭环：数据 ⇄ token ⇄ 符号模型 ⇄ 权重。**
**=> 每一跳都需要**两类**证据，缺一不可：**

| 类别 | 内容 | 缺了会怎样 |
|:--|:--|:--|
| **可逆性** | 解码 ∘ 编码 = id（或其单射形式） | 不知道该跳是否无损 |
| **信息丢失** | 精确陈述**丢了什么**（`∃ d', … ∧ … = …` 或 `¬ Injective`） | 会误以为它无损 |

**=> 只有往返、没有丢失陈述，等于宣称「无损」而没验证过。**

## 2. 测量到的四跳（全部有证据）

| 编码器 | 可逆性 | 忠实性 | 信息丢失 |
|:--|:--|:--|:--|
| `skeletonCode` | `decodeSkeleton_code`, `decodeSkeletonStrict_code` | `decodeSkeletonStrict_faithful`, `decodeSkeletonStrict_none_of_not_code` | - |
| `tensorShapeCode` | `decodeTensorShape_code` | `decodeTensorShapeStrict_faithful` | `decodeTensorShape_not_faithful` |
| `encode` | `decode_encode` | - | `encode_drop_b_roundtrip_fails` |
| `Encode` | - | - | `decode_encode_shape` |
| `listCode` | `decodeList_code` | - | - |

**读法：**

- **`skeletonCode`（符号 ⇄ 权重）**：两个方向都有，且**无信息丢失**——这是 P1-8 闭合的地方（第 976 轮）。
- **`tensorShapeCode`**：三列齐。**这正是第 973–975 轮补出来的那一格**：丢失陈述（`decodeTensorShape_not_faithful`）先证明「宽松」，严格化再给出忠实。
- **`encode`（token ⇄ 符号）**：可逆 + 丢失（`encode_drop_b_roundtrip_fails` 等三条）。
- **`Encode`（数据 ⇄ token）**：`decode_encode_shape` **本身就是**丢失陈述——它的结论是
  `∃ d', decode (Encode.encode d) = some d' ∧ d'.corpus.length = d.corpus.length ∧ d'.indices = []`，
  **即只恢复个数与顺序，不恢复数值、且索引被清空**。**形状可逆 ≠ 数据可逆。**
- **`listCode`**：只有可逆。**忠实性在此不需要**：`decodeList` 的值域就是列表，不存在「接受非码」的问题；而单射性由左逆直接得到。

## 3. 关于「候选缺口」的裁定

**`audit_reversibility_coverage.py --report` 列出若干「有往返、无忠实、无丢失」的编码器。**
**=> 逐条裁定（第 977 轮）：**

| 候选 | 裁定 |
|:--|:--|
| `listCode` | **不是缺口**：左逆已蕴含单射，且 `decodeList` 是总函数，没有「非码」可言 |
| `pairCompile`, `seqEncode`, `seqDecode` | **同上**：`*_roundtrip` 已给出左逆，忠实性多余 |
| `extractCode`, `strictly_code`, `roundTrip_compatible_with_compile` | **工具的归组假象**：这些是**定理名**被当作编码器名，不是真的编码器 |

**=> 结论：四跳的证据是**齐全的**。工具的价值在于**排除了**我原本以为存在的缺口。**

## 4. 诚实边界

**本文件的分类与工具的 `kind()` 都是**启发式**的：按名字与陈述形状判断。**
**=> 它不能判定语义等价，也不声称能。它是**地图**，不是证明。**
**=> 定理名由 `--check` 守护，故本文件不会因为重命名而悄悄失效。**
