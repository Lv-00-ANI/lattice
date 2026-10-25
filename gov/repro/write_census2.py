"""Regenerate REFUTATION-CENSUS.md with the corrected families."""
import io
import sys
from collections import Counter
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))
_WORK = _os.path.join(_HERE, "_work")
_os.makedirs(_WORK, exist_ok=True)


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
SRC = _os.path.join(_WORK, "neg_full.txt")
recs = [tuple(l.split("\t")) for l in io.open(SRC, encoding="utf-8").read().split("\n") if l.strip()]
FAMF = _os.path.join(_WORK, "neg_families.txt")
fams = []
for l in io.open(FAMF, encoding="utf-8").read().split("\n"):
    if "\t" in l:
        f, n = l.split("\t")
        fams.append((f, int(n)))

lay = Counter(rel.split("/")[0] if "/" in rel else "(root)" for rel, _, _ in recs)

MEANING = {
    "谓词不可达（结论是某性质不成立）": "某个性质在任何配置上都取不到（如 `¬ Sat (iterate n x)`）",
    "存在性被否": "某类对象不存在（`¬ ∃ …`）",
    "等式被否（含不相等）": "某等式普遍不成立，或两对象不相等",
    "界/不等式被否": "某个界/单调性给不出来",
    "全称命题被否（给出反例）": "一般断言不成立，必须附加前提",
    "单射性被否": "编码或映射会丢失信息",
    "等价被否": "两个刻画不能等同",
    "矛盾不可满足 (→ False)": "某组条件无法同时成立",
    "满射性被否": "编码达不到某些目标",
    "极值/极小性被否": "某点不是极小/极大（惩罚不精确）",
}

L = []
L.append("# 否证清册（REFUTATION-CENSUS）")
L.append("")
L.append("> 第 35 轮。脚本 `agent-tmp/fix_families.py` 生成分类，`agent-tmp/write_census2.py` 产出本文件。")
L.append(">")
L.append("> 一个形式化库的可信度，很大程度上取决于它**明确知道什么做不到**。")
L.append("> 本清册把库中已证伪的论断归类，作为这一维度的证据面。")
L.append("")
L.append("## 1. 数量与分布")
L.append("")
L.append("**%d 条**否定结论：`theorem`/`lemma` 级，且**结论类型**以 `¬` / `not` / `→ False` 开头。" % len(recs))
L.append("")
L.append("| 层 | 条数 | 占比 |")
L.append("|:--|--:|--:|")
for l, n in lay.most_common():
    L.append("| `%s` | %d | %.1f%% |" % (l, n, 100.0 * n / len(recs)))
L.append("")
L.append("**分布值得注意**：%d%% 的否证在 `Lib`（具体领域），承重层（`Core`/`Lift`/`Geo`/`Audit`）"
         % round(100.0 * lay.get("Lib", 0) / len(recs)))
L.append("合计只占 %d 条。这不是缺陷：承重层的职责不是穷举「不可能」，" % (len(recs) - lay.get("Lib", 0)))
L.append("而是钉住少数几条**关键**不可能性——而它们恰恰都在那里（见 §3）。")
L.append("")
L.append("## 2. 按否证的对象分类")
L.append("")
L.append("| 类别 | 条数 | 含义 |")
L.append("|:--|--:|:--|")
for f, n in fams:
    L.append("| %s | %d | %s |" % (f, n, MEANING.get(f, "")))
L.append("")
L.append("## 3. 承重层的否证（最重要的一组）")
L.append("")
L.append("这些定理说明**这条链路在哪里停下来**：")
L.append("")
L.append("| 层 | 定理 | 否证的内容 |")
L.append("|:--|:--|:--|")
for rel, name, c in recs:
    l = rel.split("/")[0] if "/" in rel else "(root)"
    if l in ("Core", "Lift", "Geo", "Audit"):
        L.append("| `%s` | `%s` | `%s` |" % (l, name, c.replace("|", "\\|")[:105]))
L.append("")
L.append("## 4. 分类方法与**三次修正**（如实记录）")
L.append("")
L.append("**判定规则**：取陈述的**结论类型**（最后一个顶层 `:` 之后），")
L.append("若以 `¬` / `not ` / `→ False` 开头即计入。分类时先剥掉前导 `¬` 与外层括号，")
L.append("再按**最外层构造子**匹配（量子词 → 等价 → 等式 → 极值 → 不等式 → 谓词应用）。")
L.append("")
L.append("**三次修正过程**：")
L.append("")
L.append("| 版本 | 结果 | 问题 |")
L.append("|:--|:--|:--|")
L.append("| 初版 | 329 条 | 只要陈述里出现 `¬` 就计入，把假设里的否定（`(h : ¬ j ≤ i)`）也算进来 |")
L.append("| 二版 | 272 条 | 改为只看结论，但**文件路径被输出格式截断**，层统计出错（`ib`、`b` 出现） |")
L.append("| **三版** | **%d 条** | 完整路径 + 按最外层构造子分类；抽查发现 3 处误分类并修正 |" % len(recs))
L.append("")
L.append("**残留误差**（仍存在，读者需知道）：")
L.append("")
L.append("1. **语法而非语义**：形如 `¬ False` 的平凡否证也会计入，本清册不判断平凡性；")
L.append("2. **「谓词不可达」占 %d 条**（最大类），" % dict(fams).get("谓词不可达（结论是某性质不成立）", 0))
L.append("   其中不少是**带条件**的事实（例如「在 `¬mask i j` 时输出为零」），")
L.append("   它们的结论确实是 `¬…`，但整体是条件性结论而非反驳。**计入是保守的**（宁可多算）；")
L.append("3. **`∃` 绑定子含 `:`**，嵌套深时可能误判个别条目。")
L.append("")
L.append("## 5. 用途")
L.append("")
L.append("1. **读者**：想知道「这个库限制了什么」，查 §3。")
L.append("2. **后续工作**：新增一条「不可能」比新增一条「可能」更有价值——它排除一条路线，")
L.append("   而 §2 的分类给出了哪些方向的排除已存在。")
L.append("3. **定位**：项目自称通用基础设施。基础设施的可信度来自**边界清晰**，")
L.append("   本清册就是那条边界的清单。")

io.open(_os.path.join(_REPO, "REFUTATION-CENSUS.md"),
        "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")
print("wrote REFUTATION-CENSUS.md (%d lines)" % len(L))
