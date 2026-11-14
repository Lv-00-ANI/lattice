# LATTICE 插件系统设计

> **文档性质**：设计文档（design document）
> **本文主题**：LATTICE 的插件系统本身——它是什么、由什么构成、Lean 侧证明什么、C 侧实现什么
> **本文定位**：插件系统**是证明的一部分**，不是证明之外的框架。它同时被 Lean 证明与 C 实现，两侧共用同一份声明
> **本文不回答**：现状实测数据（见 SURVEY）、迁移执行进度（见 PLAN）、被否决候选的理由（见 DECISIONS）
> **读者**：实现者、评审者、接手维护者
> **修订说明**：本轮补充三处——① 能力暴露分层（第 3.5 节）；② C 侧运行时校验范围（第 10.8 节）；③ 归档层切断顺序（附录 G.7）。并新增附录 I（自举）与附录 J（整理路线图）
> **整理阶段定位**：本文描述的是**目标形态**。当前仓库处于**粗整理**状态；当 LATTICE 证明层正式初步完成、进入 C 实现前，须按本文第 5 章（下层/上层插件划分）与第 3.5 节（暴露最大化 + 语义化）**做一次全量重构**。路线见附录 J

---

## 目录

```
正文
  1  插件系统在证明中的位置
  2  插件系统的定义与两侧分工
  3  术语、判据与暴露模型
  4  三层构件
  5  两层结构
  6  目录与命名
  7  清单规格
  8  声明的一致性：Lean 侧证明什么
  9  编排层要证明的性质
  10 插件系统的实现：C 侧做什么
  11 不变量、禁则与门禁

附录
  A  编排对象一：证明链路 L0–L7
  B  编排对象二：载体系统
  C  编排对象三：层架构
  D  编排载体：组合子层
  E  检索面：RAG
  F  否定结果在插件系统中的地位
  G  与既有设计的投影（含归档层切断顺序）
  H  未决项
  I  自举：装载器自身的证明与实现
  J  整理路线图：从粗整理到语义化重构
```

---

# 正文

## 1 插件系统在证明中的位置

### 1.1 一句话

**插件系统是证明的一部分。**

它不是在证明之外用来“组织证明”的框架；插件之间的归属、依赖、承诺、冲突、版本、参数、检索、编排，每一条本身就是可被机器检查的命题。

### 1.2 证明的两个构成

```
证明
 ├── 数学内容
 │     ├── 证明链路 L0–L7 的定理
 │     ├── 载体系统的定理
 │     └── 否定结果
 │
 └── 插件系统   ← 也是证明
       ├── 归属：某文件实现某协议
       ├── 依赖：某插件依赖某协议
       ├── 承诺：某槽有某定理
       ├── 冲突：某插件与他者互斥
       ├── 版本：某协议与其他版本兼容
       ├── 参数：某插件有哪些可调项
       ├── 检索：某能力有哪些实现者
       └── 编排：排序、登记、激活、状态迁移
```

**这两部分之间是“两类证明对象”的关系，并非“内容 + 容器”的关系。**

### 1.3 为什么必须是证明

| 若插件系统不是证明 | 若插件系统是证明 |
|:--|:--|
| 「某文件实现某协议」只能靠文档声明 | 它是可被检查的定理（`implements_eq_offered`） |
| 依赖无环只能靠人工检查 | 它是可被证明的命题（`requires_acyclic`） |
| 排序结果依赖遍历顺序 | 它是全序，可复算（`traversal_independent`） |
| 一个实现者卸载后孤立依赖不知情 | 它是可被证明的迁移性质（`orphan_fails_satisfies`） |
| 「为什么这个实现生效」不可回答 | 「因为它在第 2 分量胜出」可回答（`decided_at_dim_consistent`） |
| 「这个插件承诺了什么」不可回答 | 「它的 soundness 槽有三条定理」可回答（`obligations_resolve`） |

### 1.4 证明之外仍然存在的部分

**有一类对象不被证明，但被实现：真实运行时上下文。**

| 对象 | 为何不被证明 |
|:--|:--|
| 内存状态的实际读写 | 它是运行时行为，不是静态命题 |
| 进程的启动与停止 | 同上 |
| 调用栈的实际维护 | 同上 |
| 内存分配的副作用序列 | 同上（详见第 3.6 节与附录 I.6） |

**这就是本文第 10 节的内容：C 侧实现。**

### 1.5 本文的四个边界

| 属于本文 | 不属于本文 |
|:--|:--|
| 插件系统的形态与规则 | 现状的实测数据 |
| Lean 侧证明什么 | 迁移的执行进度 |
| C 侧实现什么 | 被否决候选的理由 |
| 插件系统所编排的对象（附录） | 归档层的逐个文件处置 |

### 1.6 本文所处的阶段

**本文是目标形态，不是现状描述。**

| 项 | 现状 | 目标 |
|:--|:--|:--|
| 归属 | `implements` 是字符串 | 解析到协议 |
| 承诺 | 部分已用 `verifiedObligation` | 十二槽全部三态 |
| 编排 | 无 | Q1–Q18 |
| 暴露 | 全部平铺 | 三层暴露（第 3.5 节） |
| 命名 | `Real*` 前缀为主 | 语义前缀-标识后缀 |

**⟹ 从现状到目标的路径见附录 J。**

---

## 2 插件系统的定义与两侧分工

### 2.1 一句话

**插件系统是 LATTICE 中「可复用证明单元」的声明与验证机制，由 Lean 侧证明其一致性、由 C 侧实现其运行时。**

### 2.2 两侧分工

| 侧 | 做什么 | 产物 |
|:--|:--|:--|
| **Lean 侧** | 证明声明之间的一致性 | 定理 |
| **C 侧** | 按声明实际装载、登记、激活插件 | 运行行为 |

**两侧共用同一份清单。** 清单是唯一的声明源，不是两侧各有一份。

### 2.3 分工表

| 对象 | Lean 侧 | C 侧 |
|:--|:--|:--|
| 清单的语法 | 类型化表示 | 解析器 |
| 归属一致性 | **证明** | — |
| 依赖无环 | **证明** | — |
| 承诺可解析 | **证明** | — |
| 排序键全序 | **证明** | — |
| 冲突判定次序 | **证明** | — |
| 状态机闭集 | **证明** | — |
| 版本兼容全序 | **证明** | — |
| 响应式激活 | **证明** | — |
| 三态出口聚合 | **证明** | — |
| 自举序列收敛 | **证明**（见附录 I） | 实现 |
| 装载器执行 | — | **实现** |
| 注册表存储 | — | **实现** |
| 内存状态读写 | — | **实现** |
| 进程与调用栈 | — | **实现** |
| 冲突轨迹记录 | — | **实现** |
| 文件存在性检查 | — | **实现**（运行时） |
| 动态链接 | — | **实现**（运行时） |
| 内存分配成功性 | — | **实现**（运行时） |

### 2.4 由三部分组成

| 部分 | 回答的问题 | 本文位置 |
|:--|:--|:--|
| **声明** | 单元是什么、实现什么、依赖什么、承诺什么 | 第 4–7 节 |
| **验证** | 这些声明之间是否一致 | 第 8–9 节 |
| **实现** | 如何按声明实际运行 | 第 10 节 + 附录 I |

### 2.5 插件系统有哪些作用

**编排只是其中一种。完整的作用清单如下：**

| # | 作用 | 被证明的内容 | 定理 |
|--:|:--|:--|:--|
| 1 | **归属** | 一个文件属于哪个插件 | `implements_eq_offered` |
| 2 | **依赖** | 一个插件需要哪些能力 | `requires_acyclic` |
| 3 | **承诺** | 一个插件保证什么 | `obligations_resolve` |
| 4 | **冲突** | 哪些实现互斥 | `decl_before_key` |
| 5 | **版本** | 哪些版本兼容 | `compat_trans` |
| 6 | **参数** | 一个插件有哪些可调项 | `merge_last_wins` |
| 7 | **检索** | 一个能力有哪些实现者 | `traversal_independent` |
| 8 | **编排** | 声明如何被排序、登记、激活 | Q1–Q18 |

**前七项是声明，第八项是声明之间的拼接。八项都是证明对象。**

### 2.6 为什么不能用目录替代

目录只能表达「文件放在哪」，不能表达：

| 目录不能表达 | 后果 |
|:--|:--|
| 这个单元**实现什么** | 无法检查「声明了但未实现」 |
| 这个单元**依赖什么** | 无法在声明阶段发现「依赖不存在」 |
| 这个单元**与什么互斥** | 无法在声明阶段发现「两个实现互斥」 |
| 这个单元的**版本** | 无法表达兼容性 |
| 这个单元的**承诺** | 无法区分「不适用」与「未实现」 |
| 这个单元**有哪些实现者** | 无法按能力检索 |

**因此需要一层声明，而目录只是这层声明的物理载体。**

### 2.7 为什么编排需要被证明

把证明切成插件后，立刻出现新问题：**这些插件如何被拼起来？**

| 问题 | 若不回答 |
|:--|:--|
| 两个插件声明同一个协议，谁生效？ | 结果依赖遍历顺序，不可复算 |
| 一个插件的依赖被卸载了，它还算可运行吗？ | 孤儿被误判为可运行 |
| 两个插件互相冲突，谁先被拒绝？ | 拒绝理由是任意的 |
| 插件升级了，旧版本怎么办？ | 无法回退 |

**这些回答的集合就是「编排」。** 而它们每一条都是纯函数或纯判定，因此都可被证明。

---

## 3 术语、判据与暴露模型

### 3.1 三十四条术语

| 编号 | 权威名 | 英文 | 定义 | 禁忌 |
|:--|:--|:--|:--|:--|
| T01 | 插件系统 | plugin system | 可复用证明单元的声明与验证机制；Lean 侧证明、C 侧实现 | 禁忌「组件体系」 |
| T02 | 装载器 | loader | 读取清单、校验、登记、激活的唯一入口；C 侧实现 | 不是「插件管理器」 |
| T03 | 模块组 | module group | 一套完整的插件标准协议；**分类**插件，不**包含**插件 | 禁忌「插件目录」 |
| T04 | 插件 | plugin | 协议的实现者；通过 `implements` 声明归属 | 禁忌「子模块」 |
| T05 | 协议 | protocol | 形如 `<namespace>.<member>@<major>.<minor>` 的命名契约 | 不是工具，不是能力集 |
| T06 | 实现声明 | `implements` | 插件声明它实现哪些协议；**归属的唯一判据** | 不是「继承」 |
| T07 | 依赖声明 | `requires` | 插件声明它需要哪些协议；**底层与上层的判据** | 不是 `import` |
| T08 | 冲突声明 | `conflicts` | 插件声明它与其他协议互斥 | — |
| T09 | 底层插件 | primitive | `requires = []` 且只依赖 Mathlib 的插件 | 禁忌「原子插件」 |
| T10 | 上层插件 | composition | `requires ≠ []` 的插件 | 禁忌「组合插件」 |
| T11 | 场景 | realm | 键空间的分区；键解析为二元组，默认落在对角线 | 不是目录，不是进程 |
| T12 | 排序键 | rank key | 六分量全序，用于同一槽内的实现者排序 | 不是「优先级」 |
| T13 | 槽 | slot | 一个协议标识与场景对上的全部候选实现者 | 不是「列表」 |
| T14 | 胜者 | winner | 槽内按排序键排第一的实现者 | — |
| T15 | 被遮蔽 | shadowed | 已登记但未激活的实现者；**保留登记** | 不是「被删除」 |
| T16 | 孤儿槽 | orphan slot | 零实现者的槽；**是合法状态** | 不是「错误」 |
| T17 | 三态出口 | three-state exit | 通过、有问题、无法判定三种出口 | 不是「错误码」 |
| T18 | 失败报告 | failure report | 结构化失败条目；含具名原因 | 取代「错误码前缀」 |
| T19 | 编排 | orchestration | 协议的声明、登记、排序、激活与依赖判定的统称 | 不是「调度」 |
| T20 | 编排性质 | orchestration property | 编排层需要证明的命题 | — |
| T21 | 组合比 | composition ratio | 引用定理数除以手写步数 | 不是「复杂度」 |
| T22 | in-degree | in-degree | 一个插件被多少其他插件 `requires` | **不是层级** |
| T23 | 事项 | obligation | 一个槽上承诺的 Lean 定理名列表 | 不是「测试」 |
| T24 | 不适用 | `na` | 槽的三态之一；须给理由 | 不是「跳过」 |
| T25 | 待实现 | `todo` | 槽的三态之一；阻止通过 | 不是「以后再说」 |
| T26 | 部署层级 | scope | 决定排序键第一分量；`mainline` > `library` > `user` | 与场景有别 |
| T27 | 语义前缀 | semantic prefix | 文件夹名的第一段；承担子类目分组 | 不是「命名空间」 |
| T28 | 标识后缀 | identifier suffix | 文件夹名的第二段及以后；同类内区分 | — |
| T29 | 纯函数 | pure function | 无副作用、无随机、无可变状态 | 不是「确定性函数」 |
| T30 | 投影 | projection | 既有术语映射到插件系统的对应关系 | 不是「别名」 |
| T31 | 暴露层级 | exposure tier | 能力对使用者的可见层次：协议层、实现层、否定层 | 不是「可见性修饰符」 |
| T32 | 接入声明 | `integration` | 插件声明自己已被上层 `requires`，或声明自己是独立能力 | 不是「使用计数」 |
| T33 | 自举 | bootstrap | 装载器自身作为插件被装载；其行为由 Lean 侧证明 | 不是「二次开发」 |
| T34 | 观测等价 | observable equivalence | 两个实现的**可观测终态**相同，但副作用序列不被证明 | 不是「完全等价」 |

### 3.2 八对易混概念

| 编号 | 易混对 | 正确区分 |
|:--|:--|:--|
| P1 | 模块组与插件 | 模块组是协议集（分类器）；插件是协议的实现者 |
| P2 | 场景与部署层级 | 场景是键空间分区；部署层级是排序键第一分量 |
| P3 | 依赖声明与 `import` | 前者是协议级、可检查；后者是文件级、编译期固定 |
| P4 | 归属与目录 | 归属由 `implements` 决定；目录是物理组织 |
| P5 | in-degree 与层级 | in-degree 是度量；层级由 `requires` 是否为空决定 |
| P6 | Lean 侧与 C 侧 | 前者证明一致性，后者实现运行时；**两侧共用同一份清单** |
| P7 | 暴露层级与实现顺序 | 暴露层级决定**谁可见**；实现顺序决定**谁被调用** |
| P8 | 观测等价与完全等价 | 前者只保终态；后者保逐步执行。C 侧只能给前者 |

### 3.3 四条引用纪律

| 编号 | 纪律 | 理由 |
|:--|:--|:--|
| R1 | 引用 Lean 定理须给「模块路径 + 定理名」 | 行号会漂移，名字不会 |
| R2 | 同一结论存在两处以上权威且互相矛盾时，并列陈述，不选边 | 选边须由裁定给出 |
| R3 | 判据必须能指出**谁在执行它**；指不出则标为待实现 | 没有执行者的判据不是判据 |
| R4 | 术语唯一：权威名与允许别称合计无重复 | 一个名字一件事 |

### 3.4 纯函数约束

**插件系统的全部变更函数强制为纯函数。系统不含任何随机部分。**

| 推论 | 内容 |
|:--|:--|
| 1 | 施加函数被调用两次等价于一次，不产生两条副作用 |
| 2 | 函数相等可证，逆的相等性可机械检验 |
| 3 | `axiom`、`sorry`、`native_decide` 不得出现在证明链上 |
| 4 | `IO`、`Time`、`Random` 不得出现在证明链上 |

**两条由此消失的后果**：

| 原后果 | 在本系统下 |
|:--|:--|
| 施加函数被调用两次会留下两条副作用 | 不成立：纯函数调用两次等价于一次 |
| 逆的相等性不可机械检验 | 不成立：纯函数相等可证 |

**一条由此不消失的性质**：点态可逆不蕴含整串原子。这是传递性问题，与纯度无关。

**纯函数约束的边界**：它只约束 **Lean 侧**。C 侧的实现有内存分配，不是纯函数——这一层的处置见第 3.6 节。

### 3.5 能力暴露模型

#### 3.5.1 三个冲突的意图

本系统同时要满足三个意图：

| # | 意图 | 来源 |
|--:|:--|:--|
| 1 | **能力最大化暴露**：所有已证的能力都应可直接使用 | 设计目标 |
| 2 | **语义化检索**：按协议检索应返回唯一答案 | 第 2.5 节第 7 项 |
| 3 | **否定结果可见**：被证否的命题应始终可见 | 附录 F |

**这三个意图直接平铺时是冲突的**：同一能力存在多份实现（如向量编码有 6 份、softmax 有 3 份），直接暴露会让检索返回互相矛盾的答案。

#### 3.5.2 三层暴露

**解法：不是“全部暴露”，也不是“只暴露胜者”，而是按层次暴露。**

| 层 | 可见性 | 包含什么 | 检索行为 |
|:--|:--|:--|:--|
| **协议层**（默认） | 默认可见 | 每个协议的**胜者** | 返回唯一答案 |
| **实现层**（显式） | 需显式 `open` 才可见 | 同一协议的**落选实现者** | 显式命名空间下才返回 |
| **否定层**（始终） | 始终可见 | 全部**否定定理** | 始终返回 |

#### 3.5.3 三层的判据

| 层 | 判定规则 |
|:--|:--|
| 协议层 | 该实现者是某协议的**胜者**（排序键第一） |
| 实现层 | 该实现者是某协议的**候选中非胜者**，或被 `shadowed` |
| 否定层 | 该定理的陈述是 `¬ P` 形态 |

**一条推论**：任何已证的命题**在某一层上始终可见**——只是默认层不同。这满足了“能力最大化暴露”，同时保证了“检索唯一”。

#### 3.5.4 一个实例

```lean
-- 协议层（默认可见）
namespace Lattice.Protocol.VectorEncode
  def convertVec : VectorConstraint → LinearLayer := ...   -- 胜者

-- 实现层（需显式 open）
namespace Lattice.Protocol.VectorEncode.Alt
  def convertVec_set : ... := ...                          -- 落选
  def convertVec_finset : ... := ...                       -- 落选

-- 否定层（始终可见）
theorem convertVec_not_injective : ¬ Injective convertVec := ...
```

**使用者写 `open Lattice.Protocol.VectorEncode.Alt` 时，才看到三个落选实现；不写则只看到胜者。**

#### 3.5.5 暴露层级与排序键的关系

| 项 | 关系 |
|:--|:--|
| 排序键决定**谁是胜者** | 六分量全序 |
| 暴露层级决定**胜者之外的可见性** | 落选者在实现层 |
| 两者不互相决定 | 改变排序键可能改变胜者，但落选者仍在实现层 |

**⟹ 暴露层级不依赖排序结果，只依赖“是否胜者”这一事实。**

#### 3.5.6 暴露模型与 RAG 的接口

附录 E 的 RAG 索引须区分三层：

| 层的索引行为 |
|:--|
| 协议层：每条协议返回一个胜者条目 |
| 实现层：可选返回全部候选，附“谁是胜者”标注 |
| 否定层：独立索引，按被否证的对象分组 |

**⟹ RAG 默认查协议层；需要“看所有实现”时查实现层；需要“这条路走不通吗”时查否定层。**

### 3.6 纯函数约束的边界

#### 3.6.1 两侧的纯度差异

| 侧 | 纯度 | 理由 |
|:--|:--|:--|
| **Lean 侧** | ✅ 纯函数 | `Primitive.run : I → Option O` 无副作用 |
| **C 侧** | ❌ 有副作用 | `malloc`/`free`/文件读写 |

#### 3.6.2 由此产生的信任边界

| 编号 | 边界 | 内容 |
|:--|:--|:--|
| **B-C1** | C 侧**可观测终态**等于 Lean 侧结果 | 可证（通过抽象函数） |
| **B-C2** | C 侧**中间副作用序列**不被证明 | 不可证 |
| **B-C3** | C 侧**内存分配失败**是 Lean 侧无对应的新增出口 | 须在 C 侧独立处理 |

#### 3.6.3 影响

**第 9.20 节的自举收敛定理只在 Lean 侧成立。** C 侧只能证明第 B-C1 条（观测等价），不能证明副作用序列等价。

**⟹ 这是一个必须显式登记的信任边界，不是可以通过论证消除的问题。**

---

## 4 三层构件

### 4.1 三层与两侧

| 层 | 是什么 | Lean 侧 | C 侧 |
|:--|:--|:--|:--|
| L1 装载器 | 读取清单、校验、登记、激活 | 声明与性质（可证） | **实现** |
| L2 模块组 | 一套完整的插件标准协议；**分类器** | 协议声明的类型 | 分类的实现 |
| L3 插件 | 协议的具体实现者 | 实现声明的类型与证明 | 装载与激活的实现 |

**单根**：装载器加载模块组，模块组分类并激活插件。
**插件不持有装载器，加载动作只能由装载器发起。**

### 4.2 模块组是分类器，不是容器

| 性质 | 含义 | 机械后果 |
|:--|:--|:--|
| `protocols` 是判定集 | 列出可被实现的协议，不列出成员插件 | 一个插件可实现多个模块组的协议 |
| 归属由声明决定 | `implements` 决定归属，目录不决定 | 目录与归属可不重合 |
| 模块组不持有插件引用 | 模块组清单中无插件名列表 | 增删插件不改模块组清单 |

**「分类器」的含义**：插件对照模块组协议被分类，从而决定激活与停用。模块组不「包含」插件。

### 4.3 插件的定义

**一个插件 = 可撤销的变更 + 可响应的依赖 + 经统一中介读写。**

| 要件 | 载体 | 缺失的后果 |
|:--|:--|:--|
| 可撤销的变更 | 一切变更经唯一的上下文变更原语，且该原语是纯函数 | 撤销不可证 |
| 可响应的依赖 | `implements` 与 `requires` | 依赖消失后仍被判为可满足 |
| 经统一中介 | 一切读写只经参数树 | 出现第二上下文载体 |

### 4.4 证明层与实现层的分工

| 层 | 内容 | 承担者 |
|:--|:--|:--|
| **证明层** | 定理、依赖、组合、编排性质 | Lean |
| **实现层** | 真实运行时上下文 | C |

| 对象 | 归属 |
|:--|:--|
| 逆存在、逆真的撤销、次序正确、依赖可满足 | **Lean 证明** |
| 排序全序、依赖无环、冲突判定次序、状态机闭集 | **Lean 证明** |
| 三态出口聚合、满足判定的两个假源 | **Lean 证明** |
| 组合律、格律、组合比、in-degree 度量 | **Lean 证明** |
| 自举序列收敛（观测层） | **Lean 证明** |
| 装载器执行、注册表存储 | **C 实现** |
| 内存状态的实际读写 | C 实现 |
| 进程的启动与停止 | C 实现 |
| 调用栈的实际维护 | C 实现 |
| 副作用序列 | **C 实现（不被证明，见 B-C2）** |

**除真实运行时上下文外，其余全部由 Lean 证明。**

---

## 5 两层结构

### 5.1 判定

| 层 | 判据 | 组合比要求 |
|:--|:--|:--|
| **底层** | `requires = []` 且只依赖 Mathlib | 无要求 |
| **上层** | `requires ≠ []` | 引用定理数 ÷ 手写步数 ≥ 1 |

**没有第三层。**

### 5.2 为何没有第三层

一个既组合他人又被他人复用的插件属于上层。
用一个「中层」标签不构成任何结构性区分——它和上层插件的行为完全相同。

**被复用次数（in-degree）是度量，不是层级。**

| in-degree | 含义 |
|--:|:--|
| 高 | 它是核心组合器 |
| = 0 | 未被复用（合法状态） |
| = 1 | 只被一个上层使用 |

**编排层不会因为 in-degree 高而提升层级，也不会因为 in-degree 为零而降低。**

这正好对应一条已有的结论：**孤儿不是缺陷**。

### 5.3 拆分的三条原则

| 编号 | 原则 | 判据 |
|:--|:--|:--|
| P1 | 底层只依赖 Mathlib | `import Mathlib` 之外无 `import Lattice.*` |
| P2 | 上层以组合为主 | 组合比 ≥ 1 |
| P3 | 一条定理若含可独立复用的引理，必须拆出成插件 | 引理出现在两个以上插件的 `requires` 中 |

### 5.4 拆分的效果示例

```
attention/
  exp-lipschitz/             底层（requires = []）
  softmax-normalize/         底层（requires = []）
  causal-mask/               底层（requires = []）
  softmax-lipschitz/         上层（requires exp-lipschitz + softmax-normalize）
                             但被 causal-softmax-lipschitz 复用
  causal-softmax-lipschitz/  上层（requires softmax-lipschitz + causal-mask）
  attention-core/            上层（requires 上面全部）
```

**`softmax-lipschitz` 与 `causal-softmax-lipschitz` 都是上层。**
前者被后者复用，但复用次数不改变其层。

### 5.5 组合比的可检验形式

```lean
def compositionRatio (p : Plugin) : ℝ :=
  (referencedTheorems p.entry).length / (handWrittenSteps p.entry).length

theorem upper_layer_is_compositional :
  p.requires ≠ [] → compositionRatio p ≥ 1
```

**取该插件 `entry` 定理的证明体，数引用其他定理的次数与手写推理步数。**

| 插件类型 | 组合比要求 |
|:--|:--|
| 底层（`requires = []`） | 无要求 |
| 上层（`requires ≠ []`） | **≥ 1** |

### 5.6 接入状态的独立维度

#### 5.6.1 一个被遗漏的区分

“底层/上层”由 `requires` 判定。但还有一种状态无法被这个判据区分：

| 状态 | `requires` | 被上层 `requires` | 两层判据 |
|:--|:--|:--|:--|
| 底层且被使用 | `[]` | 是 | 底层 |
| 底层且**未被使用** | `[]` | 否 | 底层 |
| **上层且未被使用** | `≠ []` | 否 | 上层 |
| 只在聚合器里 | 任意 | 否 | 无法判定 |

**⟹ “孤立”与“层级”是两个独立维度。**

#### 5.6.2 第十三维度：`integration`

**槽外增加一个维度（不属于十二槽，因为它不是“承诺”，而是“状态”）：**

| 值 | 含义 | 是否阻止通过 |
|:--|:--|:--:|
| `linked` | 已被某上层 `requires` | 否 |
| `standalone` | 独立能力，暂不接主链（须给理由） | 否 |
| `unlinked` | 既未被 `requires`，也未声明 `standalone` | **否，但输出报告** |

#### 5.6.3 为何不阻止通过

**“孤立”不是错误。** 一个已证但暂无上层的插件是合法的——否定定理、独立小理论、待接入的能力都属于此类。

**但它必须可见。** `unlinked` 的全部插件在每次构建时被列出（只报告，不阻断）。

#### 5.6.4 与 in-degree 的区别

| 概念 | 判据 | 用途 |
|:--|:--|:--|
| in-degree | 被多少插件 `requires` | 度量核心程度 |
| `integration` | 是否**至少被一个**插件 `requires` | 区分“孤立”与“接入” |

**⟹ in-degree = 0 与 `integration = unlinked` 等价，但 `linked` 允许 in-degree 在 1 与高值之间。**

#### 5.6.5 一个硬判据

**组合子层（附录 D）必须至少有一个插件的 `integration = linked`。**

理由：若组合子层产出的是“编排性质”，那么它必须被某个上层插件 `requires`；否则它就不是“编排载体”，而是“未接入的独立模块”。

---

## 6 目录与命名

### 6.1 目录的两种作用

| 作用 | 判定力 |
|:--|:--|
| **物理组织**：便于查找、便于门禁扫描 | 无判定力 |
| **语义归属**：决定一个文件属于哪个插件 | **无**——归属由 `implements` 决定 |

**目录与归属可以不重合。此时归属优先。**

### 6.2 命名的形态

**文件夹名形如 `<语义前缀>-<标识后缀>`，至少两段。**

| 部分 | 作用 | 例 |
|:--|:--|:--|
| 语义前缀 | 说明这一类是什么；承担子类目分组 | `softmax`、`causal`、`rope`、`edit` |
| 标识后缀 | 在同类内区分 | `lipschitz`、`mask`、`temp`、`rollback` |

#### 6.2.1 六条判据

| 编号 | 判据 |
|:--|:--|
| N1 | 字符集为 `[a-z0-9-]` |
| N2 | 至少两段 |
| N3 | 第一段是语义类目，不是编号、缩写或无义词 |
| N4 | 禁止 `Real`、`Lt`、`Gt` 这类无语义前缀 |
| N5 | 禁止纯单字母前缀 |
| N6 | 数字可作为标识的一部分（如 `fp32-round`、`layer-norm-2d`） |

#### 6.2.2 语义前缀承担分组

同一前缀的插件在字典序上相邻，因此一个模块组内的插件可按前缀成组阅读。

```
attention/
  softmax-lipschitz/
  softmax-mask/
  softmax-temp/
  causal-mask/
  causal-lipschitz/
  rope-extrapolate/
  rope-positional/
  gqa-weights/
  mla-absorb/
  kv-budget/
  kv-cache/
  head-merge/
  head-pruning/
  cross-attention/
```

**读法**：`softmax-*` 三件、`causal-*` 两件、`rope-*` 两件、`gqa-*`/`mla-*` 各一件、
`kv-*` 两件、`head-*` 两件、`cross-*` 一件。

**若只按「两段 kebab」而禁止前缀，这一层会变成 `lipschitz`、`mask`、`temp`、`extrapolate` 等一堆无类目可归的单字名词，无法按主题阅读。**

### 6.3 嵌套形态

```
<domain>/                         模块组
  module.yml
  <semantic-prefix>-<suffix>/     插件
    plugin.yml
    Proofs.lean
    <semantic-prefix>-<suffix>/   子插件
      plugin.yml
      Proofs.lean
```

#### 6.3.1 子插件的语义

| 项 | 值 |
|:--|:--|
| 是独立插件 | 是；有自己的标识、版本、实现声明 |
| 与父插件的关系 | 依赖关系；子插件可 `requires` 父插件提供的协议 |
| 物理嵌套的作用 | 便于查找；不是归属判据 |

#### 6.3.2 何时用子插件而非同级

| 情形 | 用 |
|:--|:--|
| 两个插件共享一个父能力，且都只在父的语境下有意义 | 子插件 |
| 两个插件彼此独立 | 同级 |

### 6.4 五条组织规则

| 编号 | 规则 | 强制性 |
|:--|:--|:--:|
| O1 | 一个插件一个文件夹 | 约定 |
| O2 | 子插件是父插件文件夹内的子文件夹 | 约定 |
| O3 | 依赖跨文件夹表达 | 允许 |
| O4 | **归属只由 `implements` 决定，与路径无关** | **强制** |
| O5 | **文件夹名符合 6.2** | **强制** |

**O1 与 O4 的关系**：O1 是物理约定，O4 是语义判据。两者在最坏情况下可不重合，此时 O4 优先。

### 6.5 目录重命名的边界

| 情形 | 处置 |
|:--|:--|
| 模块组名与目录名不一致 | 以 `module.yml` 的 `module` 为准 |
| 插件名与目录名不一致 | 以 `plugin.yml` 的 `id` 为准 |
| 目录名不符合 6.2 | 必须改名；改名不改归属 |
| 归属与目录不重合 | 允许；以 `implements` 为准 |

---

## 7 清单规格

### 7.1 协议标识的形态

```
<namespace>.<member>@<major>.<minor>
```

| 部分 | 取值域 |
|:--|:--|
| namespace | 小写，与模块组名一致 |
| member | 小写 kebab，如 `lipschitz`、`lipschitz-coord` |
| 版本 | 三段以内纯数字点分 |

**常数表**：

| 常数 | 值 | 说明 |
|:--|:--|:--|
| `VERSION_RE` | 三段以内纯数字点分 | 收紧后的形态 |
| `DEFAULT_REQ_VER` | `1.0` | 省版本的默认值 |
| `WILDCARD` | `*` | 唯一显式通配 |
| `MAX_VER_SEGMENTS` | 3 | 超过即判有问题 |
| `SEGMENT_MAX` | 1000000 | 单段上限 |

### 7.2 模块组清单 `module.yml`

#### 7.2.1 七键字段表

| # | 键 | 类型 | 必填 | 默认 | 取值域 | 违反码 |
|--:|:--|:--|:--|:--|:--|:--|
| 1 | `module` | 字符串 | 是 | 无 | `[a-z][a-z0-9-]*`，全局唯一 | `mod_name` |
| 2 | `namespace` | 字符串 | 否 | 等于 `module` | 小写 | `ns_form` |
| 3 | `title` | 字符串 | 否 | 等于 `module` | — | 无 |
| 4 | `description` | 字符串 | 否 | 空串 | — | 无 |
| 5 | `protocols` | 协议声明列表 | 否 | 空 | 基数 0 至 64 | `proto_id`、`proto_dup` |
| 6 | `upgrade` | 映射 | 否 | 策略为语义化版本 | `semver` 或 `locked` | `upgrade_policy` |
| 7 | `requires_modules` | 字符串列表 | 否 | 空 | 已定义的模块组名 | `dep_cycle`、`dep_unknown` |

#### 7.2.2 `protocols` 的元素

| 键 | 类型 | 必填 | 说明 |
|:--|:--|:--|:--|
| `id` | 字符串 | 是 | 形如 `<namespace>.<member>` |
| `version` | 字符串 | 是 | 三段以内纯数字点分 |
| `deterministic` | 布尔 | 否 | 是否要求确定性；默认真 |
| `budget` | 整数 | 否 | 资源预算 |

#### 7.2.3 `requires_modules` 的约束

| 情形 | 违反码 | 出口 |
|:--|:--|:--|
| 引用的模块组名不存在 | `dep_unknown` | 无法判定 |
| 模块组之间成环 | `dep_cycle` | 有问题 |

### 7.3 插件清单 `plugin.yml`

#### 7.3.1 十七键字段表

| # | 键 | 类型 | 必填 | 默认 | 取值域 | 违反码 |
|--:|:--|:--|:--|:--|:--|:--|
| 1 | `id` | 字符串 | 是 | 无 | 小写 kebab，至多 64 字符 | `req_id` |
| 2 | `version` | 字符串 | 是 | 无 | 三段以内纯数字点分 | `req_version` |
| 3 | `implements` | 引用列表 | 否 | 空 | 见 7.3.2 | `bad_ref`、`dup_impl` |
| 4 | `requires` | 引用列表 | 否 | 空 | 见 7.3.2 | `bad_ref`、`dup_impl`、`self_req` |
| 5 | `conflicts` | 冲突列表 | 否 | 空 | 见 7.3.3 | `bad_ref` |
| 6 | `params` | 映射 | 否 | 空 | 见 7.4 | `param_spec`、`param_choice` |
| 7 | `files` | 字符串列表 | 否 | 空 | 相对路径；不得含上级目录 | `files_path` |
| 8 | `entry` | 字符串 | 条件必填 | 无 | Lean 定理名 | `entry_missing`、`entry_form` |
| 9 | `realm` | 字符串 | 否 | `mainline` | 小写，至多 32 字符 | `realm_form` |
| 10 | `priority` | 整数 | 否 | 0 | −1000 至 1000 | `priority_range` |
| 11 | `scope` | 枚举 | 否 | `project` | `mainline`、`library`、`user` | `scope_enum` |
| 12 | `provides` | 引用列表 | 否 | 空 | 与 `implements` 同域 | `dup_provides` |
| 13 | `description` | 字符串 | 否 | 空串 | — | 无 |
| 14 | `depends_on` | 字符串列表 | 否 | 空 | 插件标识 | 无 |
| 15 | `slots` | 映射 | 否 | 空 | 见 7.3.4 | 见 7.3.4 |
| 16 | `integration` | 枚举 | 否 | `unlinked` | `linked`、`standalone`、`unlinked` | `integration_enum` |
| 17 | `integration_note` | 字符串 | 条件必填 | 空 | `standalone` 时必填理由 | `integration_note_missing` |

**`entry` 的条件**：`files` 非空时必填。`entry` 是 Lean 定理名，不是函数名。

**`integration` 的条件**：`standalone` 时 `integration_note` 必填且非空。

#### 7.3.2 协议引用

| 写法 | 形态 | 归一化结果 |
|:--|:--|:--|
| 短式 | `namespace.member@1.0` | 原样 |
| 长式 | `protocol` 与 `version` 两键 | 折回短式 |

**省版本时的默认值是 `1.0`，不是通配。**

| 候选 | 后果 | 取舍 |
|:--|:--|:--|
| 省略即 `1.0` | 只有 `2.0` 的实现者时不匹配 | 采用 |
| 省略即通配 | 「版本兼容」这一判据在最常见写法下恒真，因而不成为判据 | 不采用 |
| 省略即 `0.0` | 语义近似「要求 0.x」，与意图无关 | 不采用 |

**四条归属规则**：

| 编号 | 规则 |
|:--|:--|
| 1 | `implements` 是归属声明 |
| 2 | 一个插件可实现多个模块组的协议 |
| 3 | 未出现在 `implements` 中的协议，该插件不提供 |
| 4 | `implements` 与 `provides` 并存时，集合须相等；不等报 `dup_provides` |

**`provides` 是 `implements` 的旧名，处置为**：

| 步 | 动作 | 失败分支 |
|--:|:--|:--|
| 1 | 二者并存 | 集合相等则合为一名；不等报 `dup_provides`，出口有问题 |
| 2 | 只有旧名 | 归一为新名，出一条具名 INFO，不改出口 |
| 3 | 二者皆无 | 合法，视为不实现任何协议 |

#### 7.3.3 冲突引用

| 形态 | 字段 | 默认 |
|:--|:--|:--|
| 短式 | 只有协议名 | 场景取本插件所在场景 |
| 长式 | 协议名与场景两键 | 同上 |

**短式只检查本插件所在场景。**
理由：若按「任意场景有实现者即冲突」，则两个自举场景各有一个合法实现者时会被误拒。

**冲突策略闭集恰两值**：

| 值 | 语义 | 谁 active | 谁 shadowed |
|:--|:--|:--|:--|
| `single_source`（默认） | 一个键只许一个实现者 | 排名最高者 | 其余全部 |
| `ranked` | 允许多个，按排名取最高 | 排名最高者 | 其余全部（保留登记） |

**第三个值已被移除。** 移除的理由不是裁定了它应如何工作，而是收窄了可选面：
一旦被选用，它的登记语义存在而调用语义不存在，它是一个可被触发的未定义状态。
**一个可选而语义未定的值，比没有这个值更危险。**

#### 7.3.4 槽的三态

| 状态 | 写法 | 是否通过 | 说明 |
|:--|:--|:--:|:--|
| 有事项 | `obligations: [定理名, …]` | 是 | 须逐个解析到真实声明 |
| 不适用 | `na: <理由>` | 是 | **理由非空**；计入统计 |
| 待实现 | `todo: <说明>` | 否 | 阻止通过 |

**十二个槽名固定**：

`soundness`、`laws`、`exactness`、`approximation`、`recovery`、`spatial`、
`confluence`、`equivariance`、`idempotence`、`invariants`、`completeness`、`refinement`

**槽不得取字面真值。** 一个槽若无可承诺的事项，须写 `na` 并给理由；
写 `na` 时需要说明为什么该维度对本插件不适用。

### 7.4 参数规格

#### 7.4.1 参数叶

| 字段 | 类型 | 必填 | 取值域 |
|:--|:--|:--|:--|
| `type` | 枚举 | 是 | `int`、`str`、`bool`、`float`、`enum`、`list of str` |
| `default` | 同 `type` | 否 | — |
| `range` | 两个数 | 否 | 仅数值类型；下界不大于上界 |
| `choices` | 值表 | 否 | 仅枚举类型；非空 |
| `desc` | 字符串 | 否 | 至多 256 字符 |

#### 7.4.2 三段合并

| 段 | 载体 | 隐含部署层级 |
|:--|:--|:--|
| 1 | 装配根的 `params` | `mainline` |
| 2 | 模块组目录下的 `params.yml` | `library` |
| 3 | 插件清单的 `params` | `plugin` |

**合并规则**：逐键覆盖（非深合并），后者胜；每键带溯源标记。

**三条不变式**：

| 编号 | 陈述 |
|:--|:--|
| M1 | 后者赢：一个键在多段声明时，结果等于靠后那段的值 |
| M2 | 序无关：固定合并序下互换各段内容来源，规范化结果不变 |
| M3 | 幂等：把合并结果当作三段再合并一次，结果不变 |

**为何逐键覆盖而非深合并**：

| 理由 | 说明 |
|:--|:--|
| 1 | 参数树的叶是参数规格对象，半个规格对象没有意义 |
| 2 | 深合并会使「键在哪些段被声明」不可枚举，与「未声明即报错」冲突 |
| 3 | 深合并下覆盖须逐叶定义，使合并序依赖树形状，而依赖树形状的序不可静态检验 |

### 7.5 未列键的处置

本字段表未列出的键报 `unknown_key`，出口为**无法判定**。
理由：未列键可能是新版本引入的合法字段，本版本无从判定。

### 7.6 违反码总表

| 码名 | 触发条件 | 出口 |
|:--|:--|:--|
| `req_id` | `id` 不匹配正则 | 有问题 |
| `req_version` | `version` 不匹配三段 | 有问题 |
| `bad_ref` | 协议引用不匹配正则 | 有问题 |
| `dup_impl` | 同一列表内重复 | 有问题 |
| `self_req` | 依赖项同时出现在归属声明中 | 有问题 |
| `dup_provides` | `implements` 与 `provides` 集合不等 | 有问题 |
| `files_path` | `files` 含上级目录或绝对路径 | 有问题 |
| `entry_missing` | `files` 非空而 `entry` 缺失 | 有问题 |
| `entry_form` | `entry` 不是 Lean 定理名形态 | 有问题 |
| `realm_form` | 场景名不匹配正则 | 有问题 |
| `priority_range` | 优先级越界 | 有问题 |
| `scope_enum` | 部署层级不在闭集 | 有问题 |
| `param_spec` | 参数类型不在闭集，或 `range` 配了非数值类型 | 有问题 |
| `param_choice` | 枚举类型无 `choices` | 有问题 |
| `proto_id` | 协议标识不匹配正则 | 有问题 |
| `proto_dup` | 同一模块组内协议重复 | 有问题 |
| `upgrade_policy` | 升级策略不在闭集 | 有问题 |
| `dep_cycle` | 模块组依赖成环 | 有问题 |
| `integration_enum` | `integration` 不在闭集 | 有问题 |
| `integration_note_missing` | `integration = standalone` 而无理由 | 有问题 |
| `dep_unknown` | 引用的模块组不存在 | **无法判定** |
| `unknown_key` | 出现未列的键 | **无法判定** |
| `undeclared_ref` | 引用的协议未被任何模块组声明 | **无法判定** |

---

## 8 声明的一致性：Lean 侧证明什么

### 8.1 八类作用对应的八类定理

| # | 作用 | 定理 |
|--:|:--|:--|
| 1 | **归属** | 提供的协议集合等于归属声明 |
| 2 | **依赖** | 依赖图无环 |
| 3 | **承诺** | 槽内每个定理解析到真实声明 |
| 4 | **冲突** | 判定次序正确（见 Q6） |
| 5 | **版本** | 兼容关系是全序（见 Q8） |
| 6 | **参数** | 三段合并不变（M1–M3） |
| 7 | **检索** | 多实现者的排序可复算（见 Q4） |
| 8 | **编排** | 第 9 节的十八条 |

### 8.2 归属一致性

```lean
theorem implements_eq_offered :
  ∀ p : Plugin, offered p = p.implements
```

**含义**：一个插件提供的协议集合，恰好等于它声明实现的协议集合。
不存在「实现了但没声明」，也不存在「声明了但没实现」。

### 8.3 依赖无环

```lean
theorem requires_acyclic : ¬ ∃ cycle, cycle ∈ dependencyGraph
theorem self_req_rejected : p.requires ∩ p.implements ≠ ∅ → error "self_req"
theorem undeclared_ref_undecidable : undeclared_ref → exit = undecidable
```

### 8.4 承诺可解析

```lean
theorem obligations_resolve :
  ∀ p, ∀ t ∈ obligations p, ∃ decl, decl.name = t
```

**含义**：槽里写的每个定理名，都能解析到一个真实的 Lean 声明。
不存在「承诺了一个不存在的定理」。

### 8.5 参数合并不变

```lean
theorem merge_last_wins   : merge h m p k = p k                 -- M1
theorem merge_order_free  : canon (merge σ) = canon (merge σ')  -- M2
theorem merge_idempotent  : merge (merge x) = merge x           -- M3
```

### 8.6 检索与排序

```lean
theorem rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey
theorem traversal_independent : max over permutation = same
```

**含义**：同一协议下的多个实现者，其胜者是唯一确定的，与遍历顺序无关。

### 8.7 三条声明纪律

| 编号 | 纪律 | 理由 |
|:--|:--|:--|
| S1 | 声明是唯一的源 | C 侧与 Lean 侧读同一份清单，不各写一遍 |
| S2 | 声明不得由代码结构推断 | 归属不由目录推断，依赖不由 `import` 推断 |
| S3 | 声明的每一部分都可解析 | 槽内的定理名、协议名、模块组名，均须解析到真实对象 |

### 8.8 接入状态的可解析

```lean
theorem integration_resolves :
  ∀ p, p.integration = linked → ∃ q, p.id ∈ q.requires
theorem standalone_has_note :
  ∀ p, p.integration = standalone → p.integration_note ≠ ""
theorem integration_not_tier :
  ∀ p, p.integration = unlinked → (tier p = primitive ∨ tier p = composition)
```

**含义**：`linked` 必须真的被某个上层 `requires`；`standalone` 必须给理由；`integration` 不影响层级。

---

## 9 编排层要证明的性质

### 9.1 编排的定义

**编排**指协议声明之间的拼接：排序、登记、激活、依赖判定。

编排是八类作用中的第八类，不是全部。

### 9.2 十八条性质总表

| 项 | 内容 | 前置 |
|:--|:--|:--|
| Q1 | 组合律 | 无 |
| Q2 | 强度格 | 无 |
| Q3 | 覆盖半格 | 无 |
| Q4 | 排序键全序 | 无 |
| Q5 | 依赖无环 | Q4 |
| Q6 | 冲突判定次序 | Q4、Q5 |
| Q7 | 插件状态机 | Q4、Q6 |
| Q8 | 版本兼容全序 | 无 |
| Q9 | 响应式激活 | Q4、Q6、Q7 |
| Q10 | 内核四校验性质 | Q9 |
| Q11 | 三态出口聚合 | 无 |
| Q12 | 满足判定的两个假源 | Q4、Q8 |
| Q13 | 孤儿槽的清空 | Q4、Q12 |
| Q14 | 热替换的四门禁 | Q4、Q7、Q8 |
| Q15 | 冲突轨迹的形态 | Q4、Q6 |
| Q16 | 上层的组合比 | Q1 |
| Q17 | in-degree 是度量 | 无 |
| Q18 | 自举序列收敛（观测层） | Q4、Q7、Q10 |

### 9.3 Q1 组合律

| 编号 | 定理 | 内容 |
|:--|:--|:--|
| Q1.1 | 结合的运行律 | `compose (compose f g) k` 与 `compose f (compose g k)` 的运行等价 |
| Q1.2 | 结合的前后置律 | 前后置条件的结合等价 |
| Q1.3 | 左单位律 | 恒等作为左单位 |
| Q1.4 | 平行交换律 | 平行组合的运行可交换 |
| Q1.5 | 迭代单调律 | 迭代在更强前提下的单调性 |
| Q1.6 | 帧条件的结合律 | 见未决项 U1；若裁定帧属于编排则须补 |

```lean
theorem compose_run_assoc    : (compose (compose f g) k).run = (compose f (compose g k)).run
theorem compose_post_assoc   : (compose (compose f g) k).post ↔ (compose f (compose g k)).post
theorem identity_compose_run : (compose (identity I) f).run = f.run
theorem parallel_comm_run    : (parallel f g).run = (parallel g f).run ∘ swap
theorem loop_mono            : n ≤ m → (loop p dec n x).isSome → (loop p dec m x).isSome
```

### 9.4 Q2 强度格

强度是五元全序：`negative < existence < conditional < approx < exact`。组合时取最小。

```lean
theorem min_rank_le_left  : (a.min b).rank ≤ a.rank
theorem min_rank_le_right : (a.min b).rank ≤ b.rank
theorem min_comm          : a.min b = b.min a
theorem min_assoc         : (a.min b).min c = a.min (b.min c)
theorem min_idem          : a.min a = a

-- 实例层的差异：五个构造子中至少三个被真实实例使用
theorem strength_uses_at_least_three : ({p.strength | p ∈ allPlugins}).length ≥ 3
```

**实例层的现状与目标**：现状所有实例都是 `.exact`，使格结构在实例层退化为常值。目标至少三个构造子被使用——这要求真正的近似插件存在。

### 9.5 Q3 覆盖半格

覆盖是半格：`none` 是不限制，`some s` 是恰好处理 `s` 中的情形。交取交集，并取并集。

```lean
theorem inter_none_left  : Coverage.inter none b = b
theorem inter_none_right : Coverage.inter a none = a
theorem union_none_left  : Coverage.union none b = none
theorem inter_comm       : Coverage.inter a b = Coverage.inter b a
theorem inter_assoc      : Coverage.inter (Coverage.inter a b) c = Coverage.inter a (Coverage.inter b c)
theorem inter_idem       : Coverage.inter a a = a

-- 并的具体用例：至少两处
theorem union_has_two_uses : (usesOf Coverage.union).length ≥ 2
```

### 9.6 Q4 排序键全序

排序键有六个分量，按字典序比较，大者胜。

| 序 | 分量 | 方向 | 性质 |
|--:|:--|:--|:--|
| 1 | 部署层级 | `mainline` 高于 `library` 高于 `user` | 部署事实 |
| 2 | 作者优先级 | 大者胜 | 作者偏好 |
| 3 | 协议版本 | 数值大者胜 | 声明 |
| 4 | 装载序号 | 小者胜 | 装载先后 |
| 5 | 登记序号 | 小者胜 | 登记先后 |
| 6 | 插件标识 | 字典序小者胜 | 打破完全并列 |

**为何是六而不是七**：原设计有七分量，第一分量为「非对角场景优先」。
该分量在同一槽内恒为常数（同一槽的场景必等于键的第二分量），对排序零贡献。
它被删除的理由不是「它错」，而是「它恒不触发」。

```lean
theorem rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey
theorem scope_dominates_priority : scope a > scope b → a.rankKey > b.rankKey
theorem plugin_id_breaks_tie : a.rankKey.take 5 = b.rankKey.take 5 → a.id ≠ b.id
theorem traversal_independent : max over permutation = same
```

**两条实现守则**：

| 守则 | 违反后果 |
|:--|:--|
| 部署层级必须排在作者优先级之前 | 低层插件填满优先级即可盖掉高层，层次失效 |
| 插件标识必须收尾 | 前五分量可全并列时结果取决于遍历序，不可复算 |

**第 6 分量取「小者胜」而非「大者胜」**：两者都使结果唯一。取小者胜是任意选择，此处显式记录其任意性。

### 9.7 Q5 依赖无环

```lean
theorem requires_acyclic : ¬ ∃ cycle, cycle ∈ dependencyGraph
theorem self_req_rejected : p.requires ∩ p.implements ≠ ∅ → error "self_req"
theorem undeclared_ref_undecidable : undeclared_ref → exit = undecidable
```

### 9.8 Q6 冲突判定的次序

三类冲突，判定次序固定。

| 类 | 定义 | 判定时机 | 成本 |
|:--|:--|:--|:--|
| 声明冲突 | 插件声明互斥的协议已在同一场景内有实现者 | **最先** | 零成本、无副作用 |
| 键冲突 | 同一键出现两个及以上实现者 | 注册时 | — |
| 依赖冲突 | 某依赖项没有任何满足它的实现者 | **最后** | 依赖满足随注册而变 |

**声明冲突必须最先**：它是插件的自述。
若能被键冲突的排名规则绕过，则作者的意思被系统覆盖 —— 那不是排名，而是无视声明。

```lean
theorem decl_before_key : c_decl_hits p → admit p = error
theorem decl_is_realm_scoped : conflicts_short p r ↔ conflicted_in_realm p r p.realm
theorem three_classes_ordered : C-decl → C-key → C-req
```

### 9.9 Q7 插件状态机

| 态 | 含义 | 提供的槽能否被满足 | 可迁出到 |
|:--|:--|:--|:--|
| `declared` | 已解析清单，未登记 | 否 | `loaded`、`error` |
| `loaded` | 已登记，未激活 | 否 | `active`、`shadowed`、`error` |
| `active` | 是自有槽的胜者 | **是** | `shadowed`、`error` |
| `shadowed` | 已登记而未被激活；保留登记 | 否 | `active`、`error` |
| `error` | 被拒 | 否 | **终态** |

```lean
inductive PluginState | declared | loaded | active | shadowed | error

theorem error_is_terminal         : ¬ ∃ s, transitions error s
theorem no_skip_loaded            : ¬ transitions declared active
theorem shadowed_retains_dispose  : state = shadowed → dispose ≠ none
theorem active_requires_satisfied : state = active → all satisfies implements
theorem implements_eq_offered     : implements = offered
```

**被遮蔽不等于被丢弃**：被遮蔽者仍持有登记与逆。

### 9.10 Q8 版本兼容全序

| 序 | 判据 | 结果 |
|--:|:--|:--|
| 0 | 需求版本是显式通配 | 兼容（唯一逃逸口） |
| 1 | 任一侧不匹配三段以内纯数字点分 | 不兼容 |
| 2 | 缺失段记零 | 不适用 |
| 3 | 有者主版本不等于需求主版本 | 不兼容 |
| 4 | 有者次版本小于需求次版本 | 不兼容 |
| 5 | 次版本相等且有者补丁小于需求补丁 | 不兼容 |
| 6 | 其余 | 兼容 |

```lean
theorem compat_refl : compat v v
theorem compat_trans : compat a b → compat b c → compat a c
theorem wildcard_is_only_escape : req = "*" → compat anything
theorem missing_segment_is_zero : versionCompat "1.0" = versionCompat "1.0.0"
theorem prerelease_rejected : req = "1.0.0-rc" → ¬ compat anything
theorem default_is_not_wildcard : normRef "p" = ("p", "1.0") ∧ ("p","1.0") ≠ ("p","*")
```

### 9.11 Q9 响应式激活

| 态 | 定义 | 可迁出到 |
|:--|:--|:--|
| `sat` | 全部依赖项判真 | `unsat` |
| `unsat` | 至少一项判假 | `sat` |
| `blocked` | 曾判真、随后因依赖变化被停用 | `sat`、`unsat` |

| 事件 | 产生 | 可能翻转的键 |
|:--|:--|:--|
| E1 注册 | 新实现者登记 | 该实现者的键 |
| E2 注销 | 某键的胜者被卸载 | 该键 |
| E3 重设场景表 | 映射被修改 | 该场景内引用该协议的一切组件 |
| E4 热替换 | 同标识换版本 | 该插件提供的键 |

```lean
inductive SatState | sat | unsat | blocked
inductive Event | E1_register | E2_unregister | E3_reset_rho | E4_hot_swap

theorem event_has_exactly_four       : Event 恰 4 个构造子
theorem touched_keys_complete        : keys_touched e = 受影响 key 全集
theorem reclass_sound                : on_event reg ev → 每个受影响组件的新状态 = 重新计算的结果
theorem blocked_retains_registration : state = blocked → 登记仍在
```

### 9.12 Q10 内核四校验的性质

| 编号 | 校验 | 命题 |
|--:|:--|:--|
| 一 | 逆存在 | 若施加函数是合法的变更，则存在其逆 |
| 二 | 逆真的撤销 | 施加后撤销，冻结域逐格回到施加前 |
| 三 | 次序正确 | 按逆序撤销，每一步回到该步施加前 |
| 四 | 依赖可满足 | 施加前依赖成立，施加后仍成立或明确报告不满 |

```lean
theorem inverse_exists     : IsEffect fn → ∃ dispose, dispose ∘ fn = id
theorem inverse_restores   : snapshot (dispose (fn ctx)) = snapshot ctx
theorem lifo_order         : 按逆序撤销 ⟹ 每步回到该步施加前
theorem coeffect_satisfied : coeffect ctx → coeffect (fn ctx) ∨ 明确报告不满
```

**纯函数使两条后果消失**：

| 原后果 | 在本系统下 |
|:--|:--|
| 施加函数被调用两次会留下两条副作用 | 不成立：纯函数调用两次等价于一次 |
| 逆的相等性不可机械检验 | 不成立：纯函数相等可证 |

**仍成立的一条**：点态可逆不蕴含整串原子。

### 9.13 Q11 三态出口的聚合

| 出口 | 含义 |
|:--|:--|
| 通过 | 全部判据成立 |
| 有问题 | 至少一条判据明确失败 |
| 无法判定 | 解释集无法收敛到单元素 |

**无法判定不得压成有问题，且无法判定的优先级低于有问题。**

```lean
inductive Exit | ok | failed | undecidable

theorem failed_dominates : aggregate [undecidable, failed] = failed
theorem undecidable_not_compressed : aggregate [undecidable] = undecidable
```

**聚合规则**：任一失败则「有问题」，否则任一无法判定则「无法判定」，否则「通过」。

**这条纪律的理由**：若把无法判定与有问题合并，则「尚未实现」与「实现错误」不可区分。

### 9.14 Q12 满足判定的两个假源

| 因 | 含义 | 性质 |
|:--|:--|:--|
| 无实现者 | 槽为空或胜者为空 | 合法状态 |
| 版本不兼容 | 有实现者但版本不满足 | 退化为依赖未满足 |

**为何版本不兼容不新增码**：若给它独立的错误码，则「暂无实现者」与「版本不兼容」
在出口上不可区分，而三态纪律要求二者可区分。
故它退化为依赖未满足，并在失败报告中分别记两个因。

```lean
inductive UnsatReason | no_provider | version_incompatible

theorem two_reasons_distinguishable : reason = no_provider ∨ reason = version_incompatible
theorem no_provider_is_legal        : slot = ∅ → reason = no_provider
theorem version_incompat_folds      : reason = version_incompatible → requires 未满足
```

### 9.15 Q13 孤儿槽的清空

零实现者是合法状态，但满足判定须失败。故清空时须把胜者置空。

**这条的必要性**：若不清空胜者，则满足判定会把「零实现者」误判为「已满足」——
一个唯一的实现者卸载后，依赖它的组件仍被判为可运行。

```lean
theorem orphan_clears_winner   : providers = [] → recompute slot → winner = none
theorem orphan_fails_satisfies : providers = [] → satisfies = false
```

### 9.16 Q14 热替换的四门禁

热替换指同一标识用新版本替换自己。它不是普通注册，故须独立门禁。

| 判据 | 内容 | 违反即 |
|:--|:--|:--|
| 版本不得倒退 | 新版本不小于旧版本 | `version_regression` |
| 逆须先成立 | 旧实现者的撤销须先成立 | 见 Q10 |
| 须留痕 | 写一条含标识与新旧版本的轨迹 | 不适用 |
| 须重算胜者 | 换后调用重算 | 不适用 |

```lean
theorem version_regression_rejected : newVer < oldVer → hotSwap = error
theorem hot_swap_leaves_trace       : hotSwap 成功 → ∃ trace entry
theorem hot_swap_recomputes         : hotSwap 成功 → winner 已重算
```

### 9.17 Q15 冲突轨迹的形态

| 键 | 内容 |
|:--|:--|
| `event` | 事件名 |
| `key` | 协议标识与场景 |
| `policy` | 冲突策略 |
| `winner` | 胜者标识与版本 |
| `loser` | 败者标识与版本 |
| `decided_at_dim` | 决胜维名 |
| `rank_compare` | 逐维比较结果 |
| `why` | 原因 |

**必须记录决胜维名**：「输了」与「因为哪一条输的」是两件事；
只记败者名字无法判断该规则是否合理。

```lean
structure ConflictTrace where
  event : String; key : Key; policy : Policy
  winner : ProviderId; loser : ProviderId
  decidedAtDim : RankDim; rankCompare : List DimCompare; why : Why

theorem decided_at_dim_consistent :
  (rankCompare.filter (·.decided)).map (·.dim) = [decidedAtDim]
```

### 9.18 Q16 上层的组合比

```lean
def compositionRatio (p : Plugin) : ℝ :=
  (referencedTheorems p.entry).length / (handWrittenSteps p.entry).length

theorem upper_layer_is_compositional :
  p.requires ≠ [] → compositionRatio p ≥ 1
```

### 9.19 Q17 in-degree 是度量

```lean
def inDegree (p : Plugin) : ℕ :=
  (allPlugins.filter (·.requires.contains p.id)).length

theorem indegree_is_not_tier : inDegree p = n → (tier p = primitive ∨ tier p = composition)
```

**这一条的意义**：in-degree 高不改变层，in-degree 为零也不改变层。
孤儿是合法状态，不是缺陷。

### 9.20 Q18 自举序列收敛

**见附录 I 的完整表述。** 此处只给主定理：

```lean
theorem bootstrap_converges (ms : List Manifest) :
  loadAll (loadAll ms) = loadAll ms          -- Lean 侧
theorem bootstrap_observable_eq (c : RuntimeCtx) :
  observe (c_loadAll (c_loadAll c)) = observe (c_loadAll c)   -- C 侧（观测等价）
```

**第 1 条可证（纯函数幂等）。第 2 条只能证观测等价（见 B-C2）。**

---

## 10 插件系统的实现：C 侧做什么

### 10.1 C 侧的五项职责

| # | 职责 | 对应 Lean 侧的哪条定理 |
|--:|:--|:--|
| 1 | 装载器执行 | 声明可解析（8.2–8.4） |
| 2 | 注册表存储 | 排序键全序（Q4） |
| 3 | 内存状态读写 | 内核四校验（Q10） |
| 4 | 进程与调用栈 | 无（不被证明） |
| 5 | 冲突轨迹记录 | 冲突轨迹八键（Q15） |

### 10.2 装载器的执行序

```
1  读入装配根
2  建立场景表
3  载入模块组清单
4  登记协议
5  载入插件清单
6  注册实现者
7  检查冲突
8  检查依赖
9  标记激活
```

**第 2 步不可后移**：场景表决定后续每一步的作用域；先加载模块组则其场景归属无从判定。

**任一步失败时终止，已完成步骤按逆序回退。**
回退不等于撤销：已发生的界外操作只能补偿。

### 10.3 注册表的存储形态

```c
typedef struct {
    char *proto_id;
    char *realm;
} lattice_key_t;

typedef struct {
    lattice_key_t key;
    provider_t *providers;   /* 候选实现者 */
    size_t n_providers;
    provider_t *winner;      /* 胜者 */
    provider_t *shadowed;    /* 被遮蔽者，保留登记 */
    size_t n_shadowed;
    state_t state;           /* pending / active / shadowed / orphan */
    policy_t policy;         /* single_source / ranked */
} lattice_slot_t;
```

**关键约束**：`shadowed` 的实现者必须保留其登记与逆。
这不是可选的——它是 Q7 的 `shadowed_retains_dispose` 在 C 侧的体现。

**若在孤儿槽上不清空 `winner`，则满足判定会把「零实现者」误判为「已满足」。**
这是 Q13 在 C 侧的体现。

### 10.4 内存状态的读写

**这是唯一不被 Lean 证明的部分。**

| 对象 | C 侧实现 | Lean 侧证什么 |
|:--|:--|:--|
| 内存状态的实际读写 | 实现 | 逆存在、撤销正确、次序正确 |
| 进程的启动与停止 | 实现 | — |
| 调用栈的实际维护 | 实现 | 次序正确 |
| 副作用序列 | 实现 | **不证**（见 B-C2） |

**C 侧实现是否遵守契约，由 Lean 侧的契约定理约束；但实现本身不被证明。**

### 10.5 冲突轨迹的记录

每次冲突产出一条轨迹，含八个键。**必须记录决胜维名。**

「输了」与「因为哪一条输的」是两件事；只记败者名字无法判断该规则是否合理。

### 10.6 C 侧与 Lean 侧的一致性如何保证

| 机制 | 内容 |
|:--|:--|
| 共用清单 | 两侧读同一份 `plugin.yml` / `module.yml` |
| 契约定理 | Lean 侧证明清单之间的一致性 |
| 契约检查 | C 侧在装载时检查同一批条件 |
| 门禁 | 每轮构建都跑门禁，门禁读的是同一份清单 |

**⟹ 两侧不是「各写一遍」，而是「同一份声明，两种消费者」。**

### 10.7 C 侧不做的三件事

| 不做 | 理由 |
|:--|:--|
| 不重新计算胜者（除非触发重算） | 胜者由 Lean 侧的排序键确定 |
| 不推断归属 | 归属只由 `implements` 决定 |
| 不推断依赖 | 依赖只由 `requires` 决定 |

### 10.8 C 侧的运行时校验范围

#### 10.8.1 判据：静态可判定的不做运行时校验

C 侧**只**校验那些**无法在构建期判定**的条件。

| 条件 | 可静态判定 | 谁校验 |
|:--|:--:|:--|
| 清单语法合法 | ✅ | 门禁（构建期） |
| 协议引用格式 | ✅ | 门禁 |
| 归属一致性 | ✅ | 门禁 |
| 依赖无环 | ✅ | 门禁 |
| 排序键全序 | ✅ | 门禁（定理） |
| 版本兼容 | ✅ | 门禁 |
| 槽可解析 | ✅ | 门禁 |
| **文件存在性** | ❌ | **C 侧（运行时）** |
| **动态链接成功** | ❌ | **C 侧（运行时）** |
| **内存分配成功** | ❌ | **C 侧（运行时）** |
| **符号可解析** | ❌ | **C 侧（运行时）** |

#### 10.8.2 三条理由

| # | 理由 |
|--:|:--|
| 1 | **避免重复逻辑**：若 C 侧也校验静态可判定条件，则同一规则有两份实现，必有一份会漂移 |
| 2 | **运行时有额外出口**：内存分配失败在 Lean 侧无对应物（B-C3），须在 C 侧独立处理 |
| 3 | **三态纪律的延伸**：C 侧的运行时失败应报告为「有问题」；而 Lean 侧静态判定的「无法判定」不得被 C 侧压成「有问题」 |

#### 10.8.3 C 侧运行时失败的处置

| 失败类型 | 出口 | 说明 |
|:--|:--|:--|
| 文件不存在 | 有问题 | 清单声明了但文件缺失 |
| 动态链接失败 | 有问题 | 平台/依赖问题 |
| 内存分配失败 | 有问题（可重试） | 资源问题，非逻辑问题 |
| 符号无法解析 | 有问题 | `entry` 声明的定理不可链接 |

**⟹ 这四类都是「有问题」，不是「无法判定」**——因为它们都是**确定的失败**，不是解释集不收敛。

---

## 11 不变量、禁则与门禁

### 11.1 三态出口

**聚合规则**：任一失败则「有问题」，否则任一无法判定则「无法判定」，否则「通过」。

**一条纪律**：无法判定不得压成有问题。

### 11.2 十二条不变量

| 编号 | 内容 | 载体 | 判据 | 执行者 |
|:--|:--|:--|:--|:--|
| I1 | 归属由声明决定 | `plugin.yml` 的 `implements` | 提供的协议集合等于归属声明 | 门禁 |
| I2 | 单根 | 插件清单 | 插件不持有装载器 | 门禁 |
| I3 | 层序不可颠倒 | 清单的关系 | 协议定义先于实现 | 门禁 |
| I4 | 标识唯一 | 模块组名、插件标识 | 各自全局唯一 | 门禁 |
| I5 | `error` 是终态 | 状态机 | 无自 `error` 的迁移 | 定理 Q7 |
| I6 | 被遮蔽保留登记 | 状态机 | `shadowed` 仍有登记 | 定理 Q7 |
| I7 | 孤儿槽清空胜者 | 注册表 | 零实现者判失败 | 定理 Q13 |
| I8 | 三态聚合 | 出口 | 有问题优先于无法判定 | 定理 Q11 |
| I9 | 文件夹命名 | 目录 | 见第 6 节 | 门禁 |
| I10 | 底层纯度高 | `plugin.yml` 的 `requires` | `requires = []` 且只依赖 Mathlib | 门禁 |
| I11 | in-degree 只作度量 | 全部清单 | 不参与层级判定 | 门禁（只报告） |
| I12 | 接入状态可解析 | `integration` | `linked` 须真的被 `requires` | 门禁 + 定理 8.8 |

**每条不变量的最小实例**：

| 编号 | 只改这一处 | 期望 |
|:--|:--|:--|
| I1 | 从 `implements` 删一条协议但保留对应 `Proofs.lean` | 有问题 |
| I2 | 在插件清单里加装载器引用 | 有问题 |
| I4 | 两个插件用同一 `id` | 有问题 |
| I9 | 一个文件夹名不含标识后缀 | 有问题 |
| I10 | 给底层插件加一条 `requires` | 有问题 |
| I12 | 把 `integration` 改成 `linked` 但无上层 `requires` | 有问题 |

### 11.3 九条禁则

| 编号 | 禁则 | 判据 | 执行者 |
|:--|:--|:--|:--|
| N1 | 禁用 `Real`、`Lt`、`Gt` 等无语义前缀 | 目录扫描 | 门禁 |
| N2 | 禁用 `axiom` | 源码扫描 | 门禁 |
| N3 | 禁用 `sorry` | 源码扫描 | 门禁 |
| N4 | 禁用 `native_decide` | 源码扫描 | 门禁 |
| N5 | 禁用 `opaque` 在证明链上 | 源码扫描 | 门禁 |
| N6 | 禁用 `IO`、`Time`、`Random` 在证明链上 | 源码扫描 | 门禁 |
| N7 | 槽不得取字面真值 | 清单扫描 | 门禁 |
| N8 | 归属不得由目录推断 | 门禁实现 | 门禁自检 |
| N9 | 依赖不得由 `import` 推断 | 门禁实现 | 门禁自检 |

### 11.4 十类门禁

| 门禁 | 判据 | 违反出口 |
|:--|:--|:--|
| 归属一致性 | 提供的协议集合等于归属声明 | 有问题 |
| 依赖无环 | 依赖图无环 | 有问题 |
| 槽无字面真值 | 十二槽均为三态之一 | 有问题 |
| 文件夹命名 | 见第 6 节的六条判据 | 有问题 |
| 底层纯度 | `requires = []` 且只依赖 Mathlib | 有问题 |
| 上层组合比 | `requires ≠ []` 时组合比不小于一 | 有问题 |
| in-degree 报告 | 输出各插件 in-degree | **只报告，不阻断** |
| 事项可解析 | 槽内每个定理名解析到真实声明 | 有问题 |
| 接入状态 | `integration` 与 `requires` 一致 | 有问题 |
| 未声明引用 | 引用的协议被某模块组声明 | **无法判定** |

### 11.5 门禁的三条纪律

#### 11.5.1 每条门禁必须能红

**要求**：每条门禁须提供一个变异体，该变异体在最小实例上必须失败。

| 门禁 | 变异体 |
|:--|:--|
| 归属一致性 | 从 `implements` 删一条 |
| 依赖无环 | 构造一个两节点环 |
| 槽无字面真值 | 把一个槽写成 `true` |
| 文件夹命名 | 把一个文件夹改成单段 |
| 底层纯度 | 给底层插件加一条 `requires` |
| 上层组合比 | 构造一个手写为主的上层插件 |
| 接入状态 | 把 `integration` 改成 `linked` 但不加 `requires` |

**若变异体不红，则该门禁不是门禁，是注释。**

#### 11.5.2 门禁不得写盘

**要求**：门禁只读。任何门禁不得在被检查的树上写入。

**理由**：若门禁写盘，则「这个数字对不对」在同一进程里先被重写、再被提问。

**自检**：连续运行两次门禁，工作树差异须为空。

#### 11.5.3 门禁的三态不得压成两态

**要求**：报告「无法判定」的门禁，不得把该情形记为「有问题」。

### 11.6 不变量与既有门禁的关系

| 既有门禁 | 变更 |
|:--|:--|
| 分层规则 | 三份定义收敛为一处；组合子层定为基础层而非顶层 |
| 义务登记 | 改读插件清单的槽 |
| 构建产物 | 修正路径拼接 |
| C 接口一致性 | 从字符串比对改为协议引用 |
| 未证构造扫描 | 保留 |
| 注释完整性 | 保留 |
| 自检空壳 | 重写（两个 `--self-test` 目前不做任何检测） |
| 写盘门禁 | 改为只读（当前 8 个门禁在重写自己的输入） |

---

# 附录

## 附录 A · 编排对象一：证明链路 L0–L7

### A.1 八层

| 层 | 名称 | 编排中的角色 |
|:--|:--|:--|
| L0 | 数据层 | 最低层；只依赖 Mathlib 的数据结构 |
| L1 | 词元层 | 依赖 L0 |
| L2 | 语法与中间表示层 | 依赖 L0、L1 |
| L3 | 权重层 | 依赖 L2 |
| L4 | 语义层 | 依赖 L2、L3 |
| L5 | 物理层 | 依赖 L3、L4 |
| L6 | 时空层 | 依赖 L2、L4 |
| L7 | 端到端层 | 依赖以上全部 |

### A.2 编排中的处理

| 层 | 底层还是上层 | 理由 |
|:--|:--|:--|
| L0 | 底层（若只依赖 Mathlib） | `requires = []` |
| L1–L7 | 上层 | 依赖前层 |

**⟹ 靠 `requires` 表达层间依赖，不靠数值 rank。**

### A.3 L7 的特殊性

L7（端到端层）的插件组合比要求最严：它的证明体应当几乎全是组合。
若 L7 的某个插件出现大量手写推理，说明它在重复底层已证的东西。

### A.4 各层的真实强度

| 层 | 判定 |
|:--|:--|
| L0 | 半玩具：桥接器忽略样本宽度 |
| L1 | 玩具，但用反例钉住了边界 |
| L2 类型系统 | 真，但下游零引用 |
| L2 中间表示 | 部分真（22% 实质） |
| L3 | 玩具：编译产物是结构编码，不是权重 |
| L4 | 名义：20 条规定中仅 2 条真 |
| L5 | 玩具：接口与目标函数无交集 |
| L6 | 名义：对象不存在 |
| L7 | 骨架：单条端到端定理为零 |

**⟹ 这些强度判定不影响插件系统本身的设计，但影响哪些插件可以被声明为 `obligations`、哪些只能写 `todo`。**

---

## 附录 B · 编排对象二：载体系统

### B.1 五个载体

| 载体 | 在编排中的位置 |
|:--|:--|
| 卷积 | 上层（依赖 L1、L2） |
| 注意力 | 上层（依赖 L1、L2、L3） |
| 有向无环图 | 上层（依赖 L2） |
| 归一化 | 上层（依赖 L3） |
| 图神经网络 | 上层（依赖 L2、有向无环图） |

### B.2 载体必须被切成插件

**每个载体当前是一个大文件，应被切成多个插件。**

切法：按 `语义前缀-标识后缀` 的命名，同一前缀的插件成组。

| 载体 | 可能的插件数 |
|:--|--:|
| 卷积 | 3–5 |
| 注意力 | 12–15 |
| 有向无环图 | 3–5 |
| 归一化 | 4–6 |
| 图神经网络 | 4–6 |

### B.3 载体的依赖声明

每个载体的插件，其 `requires` 须声明：

| 依赖 | 例子 |
|:--|:--|
| 上层的数学 | `real.exp.lipschitz@1.0` |
| 同层的其他载体 | `arch.dag.core@1.0` |
| 链路层的语义 | `ir.skeleton@1.0` |

### B.4 五个载体的实测状态

| 载体 | 实测 | 对插件系统的影响 |
|:--|:--|:--|
| **卷积** | 一维单通道；等价定理是定义展开 | 缺通道、步长、填充的插件必须新建 |
| **注意力** | 无查询与键的投影 | 缺多头、缺投影的插件必须新建 |
| **有向无环图** | 三个组合子定义体逐字相同 | 三构造子退化，须拆成统一的组合子 |
| **归一化** | 幂等槽实为方差上界；训练等推断假设当结论 | 槽的声明与实际不符，须修正 |
| **图神经网络** | 任意置换都等变 | **比 `Aut(G)` 更强**；真正缺的是 `Aut(G)` 这个概念本身 |

---

## 附录 C · 编排对象三：层架构

### C.1 层架构的作用

层架构是插件系统的**粗粒度视图**：它把数千个插件按依赖距离分成若干层。

### C.2 层架构不能替代编排

| 层架构能表达 | 层架构不能表达 |
|:--|:--|
| 层与层之间的粗粒度顺序 | 层内两个插件的先后 |
| 层的名称 | 一个插件是否真的依赖另一个 |
| 层的数量 | 依赖的方向是否合法 |

**⟹ 层架构是编排的视图，不是编排的判据。**

### C.3 三处互不相同的 rank 定义

| 来源 | 组合子层 | 插件层 | 归档层 | 内核层 |
|:--|--:|--:|--:|--:|
| 第一处 | **6** | **3** | **4** | **0** |
| 第二处 | **4** | **5** | **7** | **1** |
| 第三处 | 6 | — | — | 0 |

**⟹ 三处定义必须收敛为一处，且有数值一致性断言。**

### C.4 组合子层的实测位置

**组合子层实测是整棵树最底层的模块之一（零向下依赖），与数值 rank 6 相反。**

编排层不以数值 rank 为判据，而以下面的形式判定：

| 判据 | 内容 |
|:--|:--|
| 依赖方向合法 | 依赖图无环 |
| 层是视图 | 层由依赖距离推出，不由数值指定 |

### C.5 十六层清单

```
层名          角色
core         内核：中间表示、类型系统、生命周期、修复
slots        槽位登记
lift         提升
runtime      运行时语义（fan-in 最高）
primitives   最小原语
lib          主题索引（18 个子领域）
domains      领域
plugins      插件
geo          几何
reference    归档
audit        审计
evidence     证据
cinterface   C 接口
compose      组合子
usage        使用示例
top          顶层聚合
```

**⟹ 这份清单在插件系统里退化为一个视图：层的判定由 `requires` 的依赖距离推出，不再由数值 rank 指定。**

---

## 附录 D · 编排载体：组合子层

### D.1 定位

**组合子层是编排性质的载体，不是被调用的对象。**

| 它是 | 它不是 |
|:--|:--|
| 编排性质的证明处 | 运行时引擎 |
| 上层插件可 `requires` 的协议来源 | 被端到端流程调用的工具 |
| 底层与上层之间的契约定义 | 独立的应用层 |

**组合子层的「零外部使用」不是缺陷。**
它的产物是**已经证明的编排性质**，供上层插件在 `requires` 中声明。

### D.2 六个组合子

| 组合子 | 载体类型 |
|:--|:--|
| `compose` | `Primitive I M → Primitive M O → Primitive I O` |
| `composeWith` | 带适配器的异型复合 |
| `identity` | `Primitive α α` |
| `parallel` | `Primitive (I₁ × I₂) (O₁ × O₂)` |
| `choice` | 两个 `Primitive I O` 加选择函数 |
| `optional` | `Primitive I I` 加判定函数 |
| `iterate` | `Primitive I I` 加判定与测度 |

### D.3 组合子内部的层次

| 组合子层的产物 | 属于哪一层 |
|:--|:--|
| 组合律的证明 | **底层**——它只依赖这层自己的定义 |
| 格律的证明 | **底层** |
| 具体的组合子实例 | **上层**——它们 `requires` 组合律与格律 |

**⟹ 组合子层内部也分两层：法则的证明是底层，实例是上层。**

### D.4 组合子与两层的对应

| 项 | 状态 |
|:--|:--|
| 组合律 | 大部分已有；缺帧条件的结合律（见 U1） |
| 强度格 | 部分已有；实例层退化为常值 |
| 覆盖半格 | 部分已有；并只有一个用例 |
| 登记表 | 有实例，零行登记 |
| 帧条件 | 全部为字面真值 |
| 端到端流程 | 不使用组合子 |
| 接入状态 | `unlinked`——须至少一个上层 `requires`（见 5.6.5） |

### D.5 组合子在 C 侧的语义

**组合子层的 Lean 侧证明了组合律，C 侧据此实现组合执行。**

| 组合子 | C 侧实现 |
|:--|:--|
| `compose` | 顺序执行两个原语 |
| `parallel` | 执行两个原语并按交换性组合结果 |
| `choice` | 按选择函数分派 |
| `optional` | 按判定函数决定是否执行 |
| `iterate` | 按判定与测度循环 |

**⟹ 组合子的合法性由 Lean 侧定理保证，执行由 C 侧实现。**

### D.6 组合子的协议形态

一个组合子层插件，其 `plugin.yml` 形如：

```yaml
plugin:
  id: compose-sequence
  version: "1.0"
  implements: ["orchestration.compose@1.0"]
  requires: []                      # 底层：只依赖自身定义
  realm: mainline
  scope: library
  files: ["Combinators.lean"]
  entry: "compose_run_assoc"
  integration: linked               # 必须被至少一个上层 requires
  slots:
    soundness:     obligations: [compose_run_assoc, identity_compose_run]
    laws:          obligations: [compose_post_assoc]
    exactness:     na: "不适用"
    approximation: na: "不适用"
    recovery:      na: "不适用"
    spatial:       na: "不适用"
    confluence:    obligations: [compose_run_assoc]
    equivariance:  na: "不适用"
    idempotence:   obligations: [identity_compose_run]
    invariants:    na: "不适用"
    completeness:  na: "不适用"
    refinement:    na: "由 implements 替代"
```

---

## 附录 E · 检索面：RAG

### E.1 RAG 与插件系统的关系

**RAG 不是插件系统的附加功能，而是它的检索面。**

一个插件由三部分组成，RAG 索引的对象正是这三部分：

| 插件的部分 | RAG 索引的维度 |
|:--|:--|
| 归属声明 | 它实现什么协议 |
| 依赖声明 | 它依赖什么协议 |
| 十二槽 | 它承诺什么、什么不适用、什么待实现 |

### E.2 RAG 需要的五个维度

| 维度 | 来源 | 缺它会怎样 |
|:--|:--|:--|
| **协议** | `implements` | 无法按能力检索 |
| **依赖** | `requires` | 无法沿依赖链检索 |
| **承诺** | 十二槽 | 无法按「已证什么」检索 |
| **摘要** | `description` + docstring | 无法按自然语言检索 |
| **暴露层级** | 协议层/实现层/否定层 | 无法区分「唯一答案」与「全部实现」 |

### E.3 RAG 把去重从整洁问题变成正确性问题

**若同一协议有多个实现者而未声明，RAG 会返回互不相同的答案。**

| 现状 | RAG 的后果 |
|:--|:--|
| 同一能力有六份实现，互不引用 | 检索返回六条不同结论 |
| 同一名字有十个不同定义 | 检索返回十条矛盾条目 |

**⟹ 去重不是代码整洁问题，是检索正确性的必要条件。**

### E.4 RAG 索引的形态

| 方案 | 内容 | 取舍 |
|:--|:--|:--|
| 声明文件索引 | 直接读全部清单 | **采用**——与插件系统同源 |
| Lean 声明索引 | 从编译产物提取 | 需要额外工具 |
| 向量索引 | 需要外部模型 | 需要外部服务 |

**采用第一种**：清单是索引的源，因为它是声明式的、可版本化的、可 diff 的。

### E.5 RAG 的四条纪律

| 编号 | 纪律 | 理由 |
|:--|:--|:--|
| E1 | 索引只能读清单，不能读 docstring 作为唯一来源 | docstring 可能失真 |
| E2 | 同一协议的多实现者必须都索引，并标注谁是胜者 | 否则检索不可解释 |
| E3 | 「不适用」与「待实现」必须区分索引 | 否则检索无法判断成熟度 |
| E4 | 三条暴露层必须分别索引 | 否则「唯一答案」与「全部实现」不可区分 |

### E.6 RAG 索引的条目形态

```json
{
  "plugin_id": "causal-softmax-lipschitz",
  "version": "1.0",
  "implements": ["attention.causal-lipschitz@1.0"],
  "requires": ["softmax.lipschitz@1.0", "attention.mask@1.0"],
  "realm": "mainline",
  "scope": "project",
  "tier": "composition",
  "in_degree": 1,
  "integration": "linked",
  "exposure": {
    "protocol_level": true,
    "implementation_level": false,
    "negation_level": false
  },
  "slots": {
    "soundness": {"kind": "obligations", "theorems": ["causal_softmax_lipschitz_coord"]},
    "laws": {"kind": "obligations", "theorems": ["causal_mask_sum_one"]},
    "approximation": {"kind": "obligations", "theorems": ["causal_lipschitz_bound"]},
    "exactness": {"kind": "na", "reason": "不做精确重构"},
    "recovery": {"kind": "na", "reason": "不适用"}
  },
  "description": "因果 softmax 的 Lipschitz 界",
  "summary": "在 causal mask 下，softmax 的 Lipschitz 常数由底层 softmax-lipschitz 与 mask 的单调性组合得到"
}
```

**`tier`、`in_degree`、`integration`、`exposure`、`slots.kind` 都是索引维度，都可以被检索。**

---

## 附录 F · 否定结果在插件系统中的地位

### F.1 否定结果是什么

**「某命题为假」与「某命题未证」是两类不同的结论。**

| 结论 | 可被引用 | 可被依赖 | 暴露层 |
|:--|:--:|:--:|:--|
| 命题为真（定理） | 是 | 是 | 协议层或实现层 |
| **命题为假（否定定理）** | **是** | **是** | **否定层（始终可见）** |
| 命题未证（`todo` 槽） | 否 | 否 | — |

### F.2 否定结果如何进入插件系统

| 项 | 处置 |
|:--|:--|
| `implements` | 否定定理可以 `implements` 一个「不可行性」协议 |
| `requires` | 可以依赖其他否定结果（构造更复杂的反例） |
| 槽 | 归入 `soundness`，因为它是真的陈述 |
| 层 | **上层**——它依赖被否证的那个形式化 |
| 暴露 | **否定层，始终可见** |

### F.3 否定结果的价值

| 价值 | 说明 |
|:--|:--|
| 钉住边界 | 「这条路走不通」是可被引用的结论 |
| 防止重复尝试 | 后来的插件若依赖被否证的前提，会立刻失败 |
| 提升检索质量 | 检索「某能力能否实现」时，否定结果给出确定答案 |

### F.4 十二条已知的否定结果

| # | 命题 |
|--:|:--|
| 1 | 绑定器交换律（即使带条件） |
| 2 | 任意定义环境下存在正规形 |
| 3 | 进展性（现行可类型化下） |
| 4 | 类型唯一性（一般常量集） |
| 5 | 任意两截断点的移位交换 |
| 6 | 路线 C 的终止性装配 |
| 7 | 提升的变量情形 |
| 8 | 位移量为一时替换律在抽象处成立 |
| 9 | 联合律在截断点为零时成立 |
| 10 | 偏移律在变量处成立 |
| 11 | 两套编辑载体可统一 |
| 12 | 三个随机分析文件「名不副实」——**不成立，是诚实降级** |

### F.5 诚实降级的三类

| 类型 | 处置 |
|:--|:--|
| 有先例的自认（如直通估计的恒等代理） | **不是缺陷**；槽写 `obligations` |
| 有边界节的降级（有声明边界的） | **不是缺陷**；槽写 `obligations` 并注明边界 |
| 明确的错位自述（实测与自述不符） | 需修正自述；槽写 `na` 并注明 |

### F.6 一条反转

**部分语义规定是「文档说未形式化，实际有定理」**——方向与通常的「文档吹牛」相反。

**⟹ 这类不是「文档幻觉」，而是「文档过时」。处置是修正文档，不是修正代码。**

---

## 附录 G · 与既有设计的投影

### G.1 概念投影

| 既有概念 | 插件系统中的对应 | 关系 |
|:--|:--|:--|
| 组合子 | 编排性质的载体 | 是底层插件（法则）与上层插件（实例） |
| 本原契约 | 插件的实现声明 | 契约的字段成为协议的能力描述 |
| 强度 | 插件的性质声明 | 保留 |
| 覆盖 | 插件的性质声明 | 保留 |
| 帧条件 | 未定（见 U1） | 待裁定 |
| 义务登记 | 插件的十二槽 | 被替代 |
| 分层规则 | 依赖图的约束 | 被 `requires` 的无环性替代 |
| 靶定理判据 | 各靶项 | 改为协议引用 |
| 端到端流程 | 手写函数组合 | 改为组合子表达 |

### G.2 既成约定的变更

| 既有约定 | 变更 | 理由 |
|:--|:--|:--|
| 归属由目录决定 | 改为由 `implements` 决定 | 目录是组织方式，不是判据 |
| 依赖由 `import` 表达 | 改为由 `requires` 表达 | `import` 是文件级、编译期固定 |
| 分层用数值 rank | 改为依赖无环 | 数值 rank 有三处互不相同的定义 |
| 义务以字符串登记 | 改为定理名列表 | 字符串无法被解析到真实声明 |
| 十二槽可为字面真值 | 改为三态 | 字面真值使槽永远无法被证伪 |
| 槽中有细化槽 | 删除 | 其语义被 `implements` 覆盖 |
| 文件名带无意义前缀 | 改为语义前缀加标识后缀 | 无意义前缀不携带信息 |
| 能力全部平铺 | 改为三层暴露 | 平铺使检索返回矛盾答案 |

### G.3 需要收敛的重复

| 重复 | 份数 | 目标 |
|:--|--:|:--|
| 向量编码 | 6 | 同协议多实现者，由排序键裁决 |
| softmax | 3 | 同上 |
| softmax 的 Lipschitz 界 | 3 | 同上；抽出共享的底层能力 |
| 纤维 | 3 | 同上；已有桥接定理 |
| 往返 | 4 | 同上 |
| 层次参数计数 | 2 | 同上 |
| 唯一性定理 | 2 | 同上 |
| 残差 | 10 | **不是同一协议——拆成 10 个协议** |
| 权重编码器 | 4 | 同协议多实现者；其中一套已被证否 |
| 批方差 | 3 | 同协议多实现者 |

**收敛的依据**：同一协议下的多个实现者由排序键裁决，不删除任何一个。
「残差」例外——它的十个定义语义不同，不是同一协议的多个实现。

### G.4 不能投影的部分

| 既有对象 | 为何不能投影 |
|:--|:--|
| 真实运行时上下文 | 它是 C 的实现，不是 Lean 的证明对象 |
| 内存状态的可逆性 | 属运行时；Lean 只证其性质 |
| 进程的生命周期 | 属运行时 |
| 副作用序列 | 属运行时；只能证观测等价（B-C2） |
| 归档层 | **不是投影对象，是移除对象** |

### G.5 归档层的地位

**归档层要逐步去除，不是被纳入。**

| 项 | 内容 |
|:--|:--|
| 现状 | 主线仍有文件 import 归档层 |
| 目标 | **零** |
| 归属 | **不属于插件系统** |
| 方式 | 逐个切断引用，每切断一处就删除对应的归档文件 |
| 最终状态 | **归档层被移除** |

### G.6 归档层去除的判据

| 判据 | 内容 |
|:--|:--|
| 引用为零 | 主线中不存在对归档层的 import |
| 命名已正 | 无文件仍以归档层的术语命名 |
| 注释已修 | 无注释引用归档层的路径 |
| 目录可删 | 删除归档目录后构建仍然通过 |

### G.7 归档层切断的三阶段顺序

#### G.7.1 三阶段的实测依据

| 阶段 | 对象 | 实测数量 | 风险 |
|:--|:--|--:|:--|
| **阶段一** | 失效的注释路径 | **22 处** | **零**（注释不影响构建） |
| **阶段二** | mainline 对 `Reference` 的 import | **29 个文件 / 52 处** | 中（每处须验证替换） |
| **阶段三** | 仍以几何术语命名的主线文件 | **42 个** | 高（须重命名 + 可能重证） |

#### G.7.2 阶段一：22 处失效注释

**特征**：注释引用的路径在归档时已被移到 `Reference/Geometry/Geometry/README.md`，但引用处未更新。

**处置**：**批量重指向**。零风险，因为注释不参与构建。

**判据**：`grep -r "Lattice/Domains/Geometry" Lattice/` 返回 0。

#### G.7.3 阶段二：29 个 import

**特征**：`Semantics/*`（8 文件）、`Plugins/Targets/*`（9）、`Plugins/Domains/Constraints/*`（7）、`Usage/Examples.lean`（6 处）、`Domains.lean`（4）。

**处置顺序**：

| 子批 | 内容 | 判据 |
|:--|:--|:--|
| 2a | `Domains.lean`（整个文件 4 条 import 中 3 条指向 `Reference`） | 该文件实质已失效，直接删除 |
| 2b | `Usage/Examples.lean` 的 6 处 | 例子可改为不依赖归档层 |
| 2c | `Plugins/Domains/Constraints/*` 7 个 | 需确认这些文件本身是否也该归档 |
| 2d | `Plugins/Targets/*` 9 个 | **须先解决判据依赖问题**（见第 1.6 节与 11.6 节） |
| 2e | `Semantics/*` 8 个 | 最后一批：`Semantics` 的几何词汇最多 |

**判据**：`grep -r "import Lattice.Reference" Lattice/` 返回 0。

#### G.7.4 阶段三：42 个命名文件

**特征**：`Lib/Chain/RealLv00Geometry*`（6 个）、`RealGeometry.lean`、`Lib/Compiler/RealLv00Compiler*`（10 个）、`Runtime/GeoSampledBound.lean`、`Semantics/ConstraintCore.lean` 等。

**处置**：**改名 + 可能重证**。

| 类别 | 数量 | 处置 |
|:--|--:|:--|
| 纯改名（内容不依赖几何） | 待测 | 只改文件名与 namespace |
| 需重证（内容引用几何概念） | 待测 | 改名 + 重建对应定理 |

**判据**：`grep -r "Geometry\|Geo\b" Lattice/ --include=*.lean` 在 mainline 的命中数为 0。

#### G.7.5 为何是这个顺序

| 理由 |
|:--|
| 阶段一零风险，先做可立即减少噪音 |
| 阶段二每切断一处就少一份依赖，为阶段三减少要考虑的对象 |
| 阶段三最贵，放最后，且此时可依赖图已清晰 |

**⟹ 三阶段不可颠倒：先改注释会暴露更多 import 问题；先改命名会让 import 路径全部失效。**

---

## 附录 H · 未决项

| 编号 | 事项 | 形态 | 须由谁给出 |
|:--|:--|:--|:--|
| U1 | 帧条件属于编排还是运行时 | 两种读法都成立 | 裁定 |
| U2 | 细化槽删除后，其语义是否完全由归属声明承担 | 需对照现有全部实例 | 设计者 |
| U3 | 装载器的清单是否为生成物 | 清单为源、Lean 为生成物，或反之 | 设计者 |
| U4 | 场景的完整取值 | 现有三值是否足够 | 裁定 |
| ~~U5~~ | ~~是否引入自举~~ | **已裁定：需要（见附录 I）** | ~~裁定~~ |
| U6 | 底层插件能否被多个模块组共享 | 影响需声明模块组的形态 | 设计者 |
| U7 | `requires = []` 但依赖非 Mathlib 的模块如何归类 | 判据是否只取 `requires` | 裁定 |
| U8 | 归档层移除时，几何语言是否需要在主线重建 | 影响移除的边界 | 裁定 |
| ~~U9~~ | ~~C 侧实现在哪些项上与 Lean 侧契约做运行时校验~~ | **已裁定：只做静态不可判定项（见第 10.8 节）** | ~~设计者~~ |

### H.1 U1 的两种读法

| 读法 | 后果 |
|:--|:--|
| 帧条件属于编排 | 须补 Q1.6 的帧条件结合律 |
| 帧条件属于运行时 | 不补；帧条件字段在清单中标注为运行时字段 |

### H.2 U7 的两种读法

| 读法 | 后果 |
|:--|:--|
| 判据只取 `requires` | 一个 `requires = []` 但依赖非 Mathlib 的模块被归为底层，与「底层只依赖 Mathlib」冲突 |
| 判据取 `requires` 与依赖两者的合取 | 需定义「依赖非 Mathlib」的可检形式 |

### H.3 U8 的两种读法

| 读法 | 后果 |
|:--|:--|
| 几何语言无需在主线重建 | 直接切断全部归档引用 |
| 部分几何语言需在主线保留 | 须先识别哪些是主线必需的，再切断其余 |

### H.4 U5 的裁定（已定）

**引入自举。** 理由是 C 侧装载器本身需要被证明符合契约——见附录 I。

---

## 附录 I · 自举：装载器自身的证明与实现

### I.1 为什么需要自举

**如果没有自举，装载器就是证明之外的信任基点。**

```
非自举：
  C 装载器（信任基点，不被证明）
    ├─ 装载插件 A
    └─ 装载插件 B

自举：
  C 装载器（其行为被 Lean 侧契约约束）
    ├─ 装载插件 A
    ├─ 装载插件 B
    └─ 装载“装载器插件”  ← 自举点
```

**⟹ 要消除信任基点，装载器必须自身也是一个 `Primitive`。**

### I.2 装载器作为 `Primitive`

```lean
def loaderPrim : Primitive (List Manifest) LoaderState where
  pre := fun ms => manifestsWellFormed ms
  post := fun ms st =>
            st.loaded = ms.map (·.id) ∧
            st.winners ⊆ ms ∧
            (∀ k, st.slot k = [] → st.winner k = none)
  run := fun ms => some (loadAll ms)      -- C 侧实现
  sound := by ...                          -- Lean 侧证明
  strength := .exact
  coverage := none
  frame := fun _ _ => True
```

**`run` 是 C 侧实现，`sound` 是 Lean 侧证明。这正是第 2.2 节「两侧共用同一份清单」的落点。**

### I.3 自举链的三步

| 步 | Lean 侧 | C 侧 |
|--:|:--|:--|
| **1 静态装载器** | `loaderPrim.sound` 是定理 | `loadAll` 实现 |
| **2 自举装载器** | `loaderPrim` 能装载自身（类型上必须成立） | `loadAll` 能装载 `loadAll` 本身 |
| **3 自举序列收敛** | `loadAll` 幂等 | `loadAll` 实现幂等 |

### I.4 三步各自的定理

#### I.4.1 第 1 步：静态装载器的正确性

```lean
theorem loader_sound :
  ∀ ms, manifestsWellFormed ms → ∃ st, loadAll ms = some st ∧
    st.loaded = ms.map (·.id) ∧
    st.winners ⊆ ms ∧
    (∀ k, st.slot k = [] → st.winner k = none)
```

**这条定理证明装载器满足它自己的 `post`。它包含 Q13（孤儿清空）作为合取项。**

#### I.4.2 第 2 步：自举装载器

```lean
theorem loader_can_load_self : manifestsWellFormed (manifestOf loaderPrim)
```

**这条定理是类型上的必要条件，不是内容性结果。** 它的价值在于：**证明装载器的清单本身是合法的**——即装载器可以用同一套机制描述。

#### I.4.3 第 3 步：自举序列收敛

```lean
-- Lean 侧（纯函数，幂等）
theorem bootstrap_converges (ms : List Manifest) :
  loadAll (loadAll ms) = loadAll ms

-- C 侧（只能证观测等价）
theorem bootstrap_observable_eq (c : RuntimeCtx) :
  observe (c_loadAll (c_loadAll c)) = observe (c_loadAll c)
```

### I.5 第 3 步的证明思路

```lean
theorem bootstrap_converges (ms : List Manifest) :
  loadAll (loadAll ms) = loadAll ms := by
  -- 装载器的 post 说：st.loaded = ms.map (·.id)
  -- 因此第二次装载的输入恰好是第一次的输出
  -- 而 loadAll 是纯函数，故 f (f x) = f x 当 f 幂等
  -- 幂等性来自 post 的第二个合取：winning set 是 ms 的子集
  ...
```

**关键依赖**：`loadAll` 是**纯函数**（Lean 侧定义），因此幂等性可证。

### I.6 必须显式登记的信任边界

**C 侧的 `loadAll` 不是纯函数。**

| 项 | Lean 侧 | C 侧 |
|:--|:--|:--|
| `loadAll` 有内存分配 | ❌ | ✅ |
| `loadAll` 可失败（`malloc` 返回 NULL） | ❌ | ✅ |
| `loadAll` 两次调用产生**相同的副作用序列** | ✅（纯函数无副作用） | **❌ 不可证** |
| `loadAll` 两次调用产生**相同的可观测终态** | ✅ | ✅（须证明） |

**⟹ 三条信任边界（第 3.6.2 节已列）：**

| 编号 | 内容 |
|:--|:--|
| **B-C1** | C 侧可观测终态等于 Lean 侧结果——**可证** |
| **B-C2** | C 侧中间副作用序列不被证明——**不可证** |
| **B-C3** | C 侧内存分配失败是 Lean 侧无对应的新增出口——**须独立处理** |

### I.7 自举在编排中的位置

**自举是 Q18。它的前置是 Q4（排序键）、Q7（状态机）、Q10（内核四校验）。**

| 理由 |
|:--|
| 自举需要排序键（决定 `loadAll` 内部的登记顺序） |
| 自举需要状态机（`loadAll` 须把每个插件推进到正确状态） |
| 自举需要内核四校验（装载本身是可撤销的变更） |

### I.8 自举的 C 侧实现骨架

```c
lattice_state_t *lattice_load_all(lattice_state_t *s, const manifest_t **ms, size_t n) {
    /* 1 建立场景表 */
    lattice_state_t *s1 = build_realm_table(s);
    if (!s1) return NULL;                     /* B-C3：分配失败 */

    /* 2 载入模块组 */
    lattice_state_t *s2 = load_modules(s1, ms, n);
    if (!s2) { lattice_dispose(s1); return NULL; }

    /* 3 登记协议 */
    lattice_state_t *s3 = register_protocols(s2);
    if (!s3) { lattice_dispose(s2); return NULL; }

    /* 4 载入插件清单 */
    lattice_state_t *s4 = load_plugins(s3, ms, n);
    if (!s4) { lattice_dispose(s3); return NULL; }

    /* 5 注册实现者 */
    lattice_state_t *s5 = register_implementations(s4);
    if (!s5) { lattice_dispose(s4); return NULL; }

    /* 6 检查冲突 */
    lattice_state_t *s6 = check_conflicts(s5);
    if (!s6) { lattice_dispose(s5); return NULL; }

    /* 7 检查依赖 */
    lattice_state_t *s7 = check_requires(s6);
    if (!s7) { lattice_dispose(s6); return NULL; }

    /* 8 标记激活 */
    lattice_state_t *s8 = mark_active(s7);
    if (!s8) { lattice_dispose(s7); return NULL; }

    lattice_dispose(s);                        /* 提交：释放旧状态 */
    return s8;
}
```

**注意 `s8` 的 `dispose` 是观测终点——Lean 侧的 `loadAll` 一次返回结果，C 侧分 8 步。** 这是 B-C2 的具体形态。

### I.9 自举的验收

| # | 验收项 | 判据 |
|--:|:--|:--|
| 1 | `loaderPrim.sound` 被打包进判据 | 主判据的一个合取项 |
| 2 | `loader_can_load_self` 为定理 | 编译通过 |
| 3 | `bootstrap_converges` 为定理 | 编译通过 |
| 4 | `bootstrap_observable_eq` 为定理 | 编译通过（C 侧抽象模型） |
| 5 | C 侧的 8 步各有失败处置 | `lattice_load_all` 的每个 `if (!sN)` 分支 |
| 6 | 自举序列的第三轮与第二轮观测等价 | 运行时测试 |

---

## 附录 J · 整理路线图：从粗整理到语义化重构

### J.1 三个整理层次

**整个证明的整理分三层推进：**

| 层次 | 名称 | 判据 | 何时做 |
|:--|:--|:--|:--|
| **第一层** | 粗整理 | 定理能编译、能通过门禁 | **现在** |
| **第二层** | 结构整理 | 按本文第 5 章的下层/上层划分 | LATTICE 证明层初步完成后 |
| **第三层** | 语义重构 | 按本文第 3.5 节的暴露最大化 + 语义化 | **C 实现启动前** |

### J.2 第一层：粗整理（当前）

**特征**：

| 项 | 现状 |
|:--|:--|
| 命名 | `Real*` 前缀为主 |
| 归属 | 目录决定 |
| 依赖 | `import` 决定 |
| 义务 | 部分为字符串 |
| 暴露 | 全部平铺 |

**这个状态是有价值的**：定理被证明了，检索可以靠 grep。但它不可编排。

### J.3 第二层：结构整理

**触发条件**：LATTICE 证明层正式初步完成（即 L0–L7 每层都有非玩具内容）。

**这一步做什么**：

| # | 动作 | 依据 |
|--:|:--|:--|
| 1 | 把每个定理归入一个插件 | 第 6 章命名规则 |
| 2 | 给每个插件写 `plugin.yml` | 第 7 章清单规格 |
| 3 | 按 `requires` 判定每个插件的层 | 第 5.1 节 |
| 4 | 检查组合比 | 第 5.5 节 |
| 5 | 输出 `integration` 报告 | 第 5.6 节 |

**不做什么**：

| 不做 | 理由 |
|:--|:--|
| 不改定理内容 | 这一步只改变组织方式 |
| 不改证明 | 同上 |
| 不改命名（除文件夹名） | 命名留到第三层 |

**判据**：每个插件都有合法的 `plugin.yml`；`integration` 报告被输出。

### J.4 第三层：语义重构（C 实现前）

**触发条件**：C 实现即将启动。

**这一步做什么**：

| # | 动作 | 依据 |
|--:|:--|:--|
| 1 | 把 `Real*` 前缀改为语义前缀 | 第 6.2 节 |
| 2 | 把同一能力的多份实现收敛为协议 | 附录 G.3 |
| 3 | 建立三层暴露 | 第 3.5 节 |
| 4 | 把"残差"10 个定义拆为 10 个协议 | 附录 G.3 |
| 5 | 把否定定理移入否定层 | 附录 F.2 |
| 6 | 删除归档层 | 附录 G.7 |
| 7 | 重跑全部门禁 | 第 11 章 |

**判据**：

| 判据 | 内容 |
|:--|:--|
| 无 `Real*` 前缀 | `grep -r "Real" Lattice/ --include=*.lean -l` 返回 0 |
| 无归档层引用 | `grep -r "Lattice.Reference" Lattice/` 返回 0 |
| 三层暴露完整 | 每个协议有胜者、落选者、否定者分别可见 |
| 十二槽无字面真值 | `grep -r "= True" --include=plugin.yml` 返回 0 |

### J.5 三层的顺序为何不可颠倒

| 若颠倒 | 后果 |
|:--|:--|
| 先语义重构，后结构整理 | 语义重构要在没有 `plugin.yml` 的情况下判断"哪些是同一协议"，无法判定 |
| 先暴露分层，后义务填全 | 暴露分层要依赖"谁是胜者"，而胜者由排序键决定，排序键需要槽的完整声明 |
| 先删归档层，后切 import | 会导致构建中断 |

**⟹ 顺序是：粗整理 → 结构整理（得到 `plugin.yml`）→ 语义重构（改名 + 分层 + 删归档）。**

### J.6 第二层与第三层的具体分工

| 事项 | 第二层 | 第三层 |
|:--|:--|:--|
| 给每个定理写 `plugin.yml` | ✅ | — |
| 判定层 | ✅ | 重判（可能因改名而变） |
| 组合比检查 | ✅ | 重查 |
| 文件夹改名 | ❌ | ✅ |
| 同名收敛 | ❌ | ✅ |
| 三层暴露 | ❌ | ✅ |
| 删归档层 | ❌ | ✅ |
| 十二槽填全 | ✅ | 重填 |

**⟹ 第二层是"加声明"，第三层是"改代码 + 改声明"。**

### J.7 从当前状态开始的第一个动作

**当前状态**：粗整理，约 850 文件 / 8,300 定理。

**第一个动作不是结构整理，而是**修复 12 条 S 级缺陷**——因为它们会让结构整理的门禁不可信：

| # | 缺陷 | 为何必须先修 |
|--:|:--|:--|
| 1 | `verify_all` 漏传 `--check` | 门禁在重写自己的输入，任何"数字对不对"的检查都无效 |
| 2 | 三份 rank 定义 | 层判据有矛盾，结构整理无法确定按哪份 |
| 3 | 两个 `--self-test` 空壳 | 门禁不能红，等于没有门禁 |
| 4 | `Registry` 空表 | 编排层无示例，结构整理无参照 |
| 5 | `refinement` 槽 11/11 为 `True` | 十二槽有永远无法证伪的槽，结构整理会继承这个缺陷 |

**⟹ 结构整理的第一步是让门禁可信，不是开始写 `plugin.yml`。**

### J.8 三个层次的里程碑

| 层次 | 里程碑 | 可验收的产物 |
|:--|:--|:--|
| 粗整理 | 12 条 S 级缺陷修复 | 门禁能红、能只读、rank 唯一 |
| 结构整理 | 全部插件有 `plugin.yml` | `integration` 报告 + `plugin.yml` 全量 |
| 语义重构 | 三层暴露 + 无 `Real*` + 无归档层 | 检索返回唯一答案 |

---

# 一句话

> **本文完整写出：正文 11 章 + 附录 10 节。**
>
> **核心定位在第 1 章：插件系统是证明的一部分，不是证明之外的框架。它由 Lean 侧（证明八类声明的一致性）与 C 侧（按同一份清单实际装载、登记、激活）共同组成，两侧共用同一份清单。**
>
> **八类作用是完整的：① 归属、② 依赖、③ 承诺、④ 冲突、⑤ 版本、⑥ 参数、⑦ 检索、⑧ 编排。编排只是第八类。**
>
> **本轮新增三处：**
> **• 第 3.5 节 能力暴露模型**——解决“全部暴露”与“检索唯一”的冲突：三层暴露（协议层默认只看胜者、实现层需显式 `open`、否定层始终可见）。这保证任何已证命题在某一层始终可见，同时检索返回唯一答案。**
> **• 第 10.8 节 C 侧运行时校验范围**——C 侧只校验静态不可判定的四类（文件存在性、动态链接、内存分配、符号可解析），其余全部由门禁在构建期完成。避免同一规则两份实现。**
> **• 附录 G.7 归档层切断的三阶段顺序**——22 处失效注释（零风险）→ 29 个 import（中风险）→ 42 个命名文件（高风险）。三阶段不可颠倒。**
>
> **第 5.6 节新增第十三维度 `integration`**——区分“孤立”与“层级”这两个独立维度。`linked` 须真的被某上层 `requires`，`standalone` 须给理由，`unlinked` 只报告不阻断。并给出一条硬判据：**组合子层必须至少有一个插件 `integration = linked`**。
>
> **附录 I 是自举的完整设计**（原为未决项 U5，现裁定为“需要”）：`loaderPrim : Primitive (List Manifest) LoaderState`，`run` 是 C 侧实现、`sound` 是 Lean 侧证明。三步：静态装载器正确性 → 自举装载器 → 自举序列收敛（Q18）。**
>
> **但有一处必须显式登记：C 侧 `loadAll` 不是纯函数（有 `malloc`/`free`），所以自举收敛只在 Lean 侧成立；C 侧只能证**观测等价**（B-C1），不能证**副作用序列等价**（B-C2）。这是三条信任边界之一，不是可以论证消除的问题。**
>
> **附录 J 是整理路线图：**
> **• 第一层 粗整理**（当前）：`Real*` 前缀、目录决定归属、`import` 决定依赖、全部平铺暴露。**
> **• 第二层 结构整理**（LATTICE 证明层初步完成后）：给每个定理写 `plugin.yml`、按 `requires` 判层、检查组合比、输出 `integration` 报告。**只加声明，不改代码**。**
> **• 第三层 语义重构**（C 实现前）：`Real*` 改为语义前缀、同一能力多份实现收敛为协议、“残差”10 个定义拆为 10 个协议、建立三层暴露、删除归档层。**改名 + 分层 + 删归档**。**
>
> **三层顺序不可颠倒：先结构整理得到 `plugin.yml`，才能判定“哪些是同一协议”；先填全义务，才能判定“谁是胜者”。**
>
> **而第一层的第一步不是写 `plugin.yml`，而是修复 12 条 S 级缺陷——因为 `verify_all` 在重写自己的输入、两个 `--self-test` 是空壳、三份 rank 互相矛盾。**门禁不可信时，任何结构整理都无法验收**。**
