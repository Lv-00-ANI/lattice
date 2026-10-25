# `gov/repro/` -- 文档结论的可复现证据

> 本目录存放**被文档引用**的脚本。它们的存在意义只有一个：
> 让文档里的每个数字、每个判断**可以被重跑验证**，而不只是被相信。

## 0. 为什么这些脚本在仓库里

此前它们散落在仓库外的 `agent-tmp/`，且**硬编码了某一台机器的绝对路径**。
文档引用一个仓库外、不可运行的脚本，等于**引用了一半的证据**。

本目录把被引用的脚本收进来，并把路径改为**相对本文件推导**：

```python
_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.abspath(os.path.join(_HERE, "..", ".."))      # 仓库根
_WORK = os.path.join(_HERE, "_work")                          # 中间产物
```

⇒ 换一台机器、换一个目录，脚本仍然能跑。

## 1. 收录标准

**只收录被文档按名字引用的脚本。** 判据是 `grep 'agent-tmp/<name>.py' *.md` 命中。

未收录的约 960 个一次性探针不进仓库：它们的价值是**当时的答案**，不是文件本身。
把一次性脚本塞进交付物只会让「仓库里有什么」这个问题失去清晰答案。

## 2. 脚本与它们的文档

| 脚本 | 支撑的文档结论 |
|:--|:--|
| `measure_conventions.py` | `CONVENTIONS §7` 的 N3/N4/F1 违规数 |
| `completeness_audit.py` | `COMPLETENESS-AUDIT` 的 16 条条款 |
| `survey_negatives.py` → `build_census2.py` → `fix_families.py` → `write_census2.py` | `REFUTATION-CENSUS` 的 389 条与分类 |
| `classify_repair.py`、`find_new_repairs.py` | `REPAIR-CENSUS` 的 A/B/C 三类 |
| `measure_chain_deps3.py` | `ROADMAP-v9 §1` 的引用计数（也是 `check_chain_deps.py` 的来源） |
| `measure_geo_by_file.py`、`round24_survey.py` | 按文件语义的覆盖度测量 |
| `arch_interface_audit.py`、`verify_vendor_claim.py` | 定位边界（不绑定厂商）的实测 |
| `derive_number_sources.py` | `CONVENTIONS §6` 的数字来源表 |
| `verify_conv_claims.py`、`check_readme_claims.py` | 文档断言的核对 |
| 其余 | 见各自文件头 |

## 3. 有依赖链的脚本

**必须按顺序运行**，中间产物写入 `_work/`：

```bash
cd gov/repro
python build_census2.py      # 产出 _work/neg_full.txt
python fix_families.py       # 产出 _work/neg_families.txt
python write_census2.py      # 重写 REFUTATION-CENSUS.md
```

`_work/` 是临时目录，不入版本控制。**重跑会覆盖 `REFUTATION-CENSUS.md`**——
这是设计意图：那个文件是**生成的**，不是手写的。

## 4. 门禁与复现脚本的分工

| 类型 | 位置 | 作用 |
|:--|:--|:--|
| **门禁** | `gov/*.py` | **能失败**，由 `verify_all` 运行 |
| **复现证据** | `gov/repro/*.py` | **产出文档数字**，人工按需运行 |

门禁回答「现在是否一致」；复现脚本回答「这个数字是怎么算出来的」。
两者不能互相替代。

## 5. 已知限制

- 部分脚本需要**较长时间**（`p13_loadbearing.py` 约 2 分钟，因为它反复调用 Lean）。
  它们不在门禁里，正是因为这个。
- 脚本假设 `lattice-new/` 与 `agent-tmp/` 是**兄弟目录**（`_AGENT_TMP` 的推导依赖这一点）。
  若目录结构不同，需调整那一行。
- 27 个脚本中 25 个可直接运行；依赖链的那 3 个需要按 §3 的顺序。
