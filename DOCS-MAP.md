# DOCS MAP

## 1. 权威顺序

1. 源码定理/定义；
2. `audit_counts.py` / `gate.py` / `verify_all.py` 实测；
3. `PROOF-DEBT.md` / `MACRO-STATUS.md`（生成物）；
4. `DESIGN.md` / `PROOF-OBLIGATIONS.md` / `SPATIOTEMPORAL.md`；
5. `README.md` / `PARADIGM.md` / `USAGE.md`。

## 2. 载体文档（2026-11-05 新增）

- `CARRIER-REPLACEMENT.md` — 决定：主载体从几何改为 CIC；备选、影响、回滚。
- `CARRIER-CIC.md` — 设计：几何如何编码进 CIC；T0–T8 的 CIC 版；新目录。

**阅读顺序：** `CARRIER-REPLACEMENT.md` → `CARRIER-CIC.md` → `PROOF-OBLIGATIONS.md`。

## 3. 证明文档

- `README.md`
- `DESIGN.md`
- `MODEL-WEIGHT.md`
- `CONSTRUCTIVE-TRAINING.md`
- `SPATIOTEMPORAL.md`
- `PLUGIN-PROTOCOL.md`
- `PLUGIN-PROOFS.md`
- `MIGRATION-PLUGINS.md`
- `CONFLUENCE.md`
- `PROOF-OBLIGATIONS.md`
- `ARCHITECTURE-CARRIERS.md`
- `GLOSSARY.md`
- `ROADMAP.md`
- `CARRIER-REPLACEMENT.md`
- `CARRIER-CIC.md`

## 4. 工程文档

- `ENGINEERING.md`
- `USAGE.md`

## 5. 生成物，勿手改

- `PROOF-DEBT.md`
- `MACRO-STATUS.md`
- `gov/ENDTOEND-CENSUS.md`
- `gov/ALIAS-CENSUS.md`
- `REFUTATION-CENSUS.md`
- `REPAIR-CENSUS.md`

## 6. 规则

- 证明文档不写 `Format` / `Bytes` / `C`；
- 工程文档不写“已证明”；
- README 不硬编码易漂数字；
- 文档写“已闭合”必须给定理名；
- 生成物只通过生成器更新；
- **判据（`ProofComplete`）的实际形状以 `Lattice/Plugins.lean` 为准**，文档只做同步；
- 文档中的定理名必须能在树中检索到（`gov/check_obligation_names.py`）；
- 载体相关陈述必须标注 CIC 版还是 Domain 版。
## archive/ —— 历史快照（第 148 轮建立）

**根目录曾同时存在 9 份 ROADMAP-v3.md … ROADMAP-v11.md。**
**它们是**已废止的路线快照**：既不参与当前判据，也不被任何门禁检查，但会与当前的 ROADMAP.md 争夺读者的注意力。**

**⇒ 已移入 rchive/，当前 ROADMAP.md 是唯一权威。**

| 归档文件 | 内容 |
|:--|:--|
| rchive/ROADMAP-v3.md … rchive/ROADMAP-v11.md | **历代路线快照，只读，不参与判据** |

**纪律：** **任何被 ROADMAP.md 取代的版本移入 rchive/，而不是删除；文件名保持原样，以便追溯。**