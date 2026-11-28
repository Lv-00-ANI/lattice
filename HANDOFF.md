# HANDOFF —— 接手这一层时你需要知道的四件事

**本文写于第 1217 轮（会话末）。⇒ 它只讲**当前的事实**，不讲打算；每条数字都有**可重跑的命令**（见 §5）。**
**⇒ 权威顺序：**工具输出 > 本文件 > 其他文档**。若本文件与工具不符，**以工具为准**并修正本文件。**

---

## 1. 现在是什么状态（八个数，全部实测）

```bash
cd gov && python measure_eight.py
```

| 量 | 值 |
|:--|--:|
| 模块（内核） | **1,126** |
| 定理 / 声明 | **10,321 / 13,921** |
| `.lean` 文件 / 行 | **1,226 / 281,665** |
| 检查 | **131 = 109 门禁 + 22 报告器** |
| 反应性探针 | **11**（全绿） |
| 接缝 / 连接器 / 未登记预算 | **9 / 60 / 0** |
| 条款 / 载体 | **14 / 44** |
| `ProofComplete` 项数 | **30** |

**⇒ 而「恒绿门禁」（结构性不可能失败的那些）从**8 降到 0**——这是本会话最该被继承的一件事：**
**⇒ **一个不会失败的门禁，和没有门禁是一样的。** ⇒ 现在每道门禁都有一个**不是字面 0 的退出**（`GATE-1` 看守这条）。**

---

## 2. 做了什么（按规划编号）

| 阶段 | 交付 |
|:--|:--|
| **Phase 0** | 五 `--strict` 注册 · 三态裁决（SKIP 不算通过）· 两腐化基线重建 · 六处默认写改比较 · **GATE-1/2/3** · 七组同 FQN 合并 · 三秩表合一 |
| **Phase 1** | 整数嵌入**单射** · **预像 + 左逆** · **精确边界**（两系数皆整 ⟺ 有层）· 两条编码**逐段 + 全域**一致 · 第三入口**以定理判定不等价** · 产物契约 W1-2 **以测量否定** |
| **Phase 2** | T7 / T6 换载体（**追加**）· T0 **裁决为进判据** · T8 **裁决为不进**（证据：插件级 vs 步骤级）· 判据 **24 → 30**，由 `check_criterion_size.py` 看守 |
| **Phase 3（部分）** | `PluginState` 状态机 + 3 定理 · `DeployScope`/`RankKey`/`Wins` + 6 定理（含**严格全序**）· `DepGraph`/`Ranked` + 3 定理（含**子图单调**）· 规范里那句假定理已换成两条真定理 |

---

## 3. 缺什么，以及为什么（**这不是待办清单，是实测理由**）

| 未做 | 实测到的阻断 |
|:--|:--|
| **`Ranked ⟺ 无回路`** | 需拓扑排序论证（在可达节点的有限子图上造测度）。**真活，未开写**，且**不写半截** |
| ~~`plugin.yml` 能力索引~~ | **已存在**（第 1223 轮实测）：`Plugins/Manifest.lean` 有 `ObligationKind`(12)、`PluginLayer`(8)、`Obligation`、**`PluginManifest`**；它出现在 **15 个文件**，**每个插件的 `Manifest.lean` 都在用**；`check_plugin_yml.py` **逐字段**对比 11 份 YAML 与 Lean 声明。⇒ 写 Lean 侧 YAML 解析器只会**重复**那道门禁 |
| **Phase 4**（组合层接真实管线） | **不被阻断**（第 1226 轮实测）：`pipeline` 的末环是 **`compileToLayer`**（函数形入口，已逐段+全域接通），**从不**调用 `compileSkel`。⇒ 待做的是把三个普通函数包成 `Primitive` 并组装 `defaultPipeline` |
| **Phase 5**（IR 契约 / 编辑统一模型） | `EditTarget` / `Change` / `EditMode` **全部不存在**（0 处） |
| **Phase 6**（执行边界 / 自举） | `.c` / `.h` / `@[extern]` **0 个** |
| **Phase 7 / 8** | 前置于 Phase 6 / 持续项 |

**⇒ 故「lattice 项目彻底做完」**没有达到**。⇒ 接手时不要把它当作已完成。**

---

## 4. 这一层最容易被**误判**的三处（都实际发生过）

1. **几何层「归档」不等于「出了构建」**。`archive/LvFormal` 出了构建（103 文件）；而
   `Lattice/Reference/Geometry` **仍在**构建里（**323** 条 import 边）。⇒ 说「不参与主构建」是**错的**。
2. **`t6_spatial` / `t7_confluence` 不是规范要的那两条**。`CARRIER-CIC.md:187` 与 `CONFLUENCE.md:12-13`
   各自明文说了这一点；判据现在**两条都合**，而不是替换。
3. **`--fast` 跳过 11 个探针**，而那 11 个是**唯一测试「检查本身」**的。⇒ 完整验证必须**两半相加**（见 §5）。

---

## 5. 怎么重新测量本文的每一句

```bash
cd gov
python measure_eight.py             # §1 的八个数
python verify_all.py --fast         # 第一半：约 460 秒，98 通过
# 第二半：11 个探针逐个跑（约 17 分钟；整条 `verify_all` 完整需 1484 秒，超出本环境窗口）
for f in gate_reactivity layer_reactivity check_slots_reactivity check_comments_reactivity \
         check_i8_reactivity check_registry_reactivity check_registry_gate_reactivity \
         verify_g4 audit_tables_reactivity audit_counts_reactivity check_ci_workflow_reactivity; do
  python "$f.py" || echo "PROBE FAILED: $f"
done
python check_criterion_size.py      # §1 的判据项数，并核对文档里的声称
python chain_connectors.py --check  # §1 的接缝
python check_theorem_liveness.py --check
```

**⇒ 若某条与本文件不符，**以工具为准**。⇒ 本文没有「作者权威」。**

---

## 6. 下一步从哪起（一句话）

**⇒ 从 `Ranked ⟺ 无回路` 起**：它是 W3-3 唯一剩下的**纯数学**义务，且**不需要新语义**——
**⇒ 只需在 `Finset` 上做拓扑排序；做完，编排内核的三个组件就都是**双向**刻画的，而不是单向的。**
