"""gov/gen_proof_debt.py -- turn review verdicts into a registry.

Severity order is not "how easy to fix" but "how badly it misleads": a theorem that states nothing
(`delete`) is worse than one that states too little (`strengthen`), which is worse than one whose
claim overshoots its content (`downgrade`), which is worse than a recorded debt (`register`).
Within a severity, in-degree breaks ties: a weak theorem twenty files lean on is the one that
propagates.
"""
import io
import json
import os
import sys
from collections import Counter, defaultdict

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
REV = os.path.join(ZERO, "agent-tmp", "review")
OUT = os.path.join(ZERO, "PROOF-DEBT.md")

# in-degree is taken from the inventory, not from the verdict (the reviewer did not compute it)
inv = {}
for line in io.open(os.path.join(REV, "inv.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    inv[(r["file"], r["line"], r["name"])] = r

verdicts = []
for f in sorted(os.listdir(REV)):
    if not (f.startswith("verdicts_") and f.endswith(".jsonl")):
        continue
    for line in io.open(os.path.join(REV, f), encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        try:
            v = json.loads(line)
        except json.JSONDecodeError:
            continue
        key = (v.get("file"), v.get("line"), v.get("name"))
        rec = inv.get(key, {})
        v["in_degree"] = rec.get("in_degree", 0)
        v["users"] = rec.get("users", [])
        verdicts.append(v)

ORDER = ["delete", "strengthen", "downgrade", "register"]
counts = Counter(v.get("verdict", "?") for v in verdicts)
flagged = [v for v in verdicts if v.get("verdict") in ORDER]
flagged.sort(key=lambda v: (ORDER.index(v["verdict"]), -v["in_degree"], v["file"] or "", v["line"] or 0))

lines = []
A = lines.append
A("# PROOF-DEBT：证明强度的诚实登记")
A("")
A("> **本文件由 `gov/gen_proof_debt.py` 生成，勿手改。**")
A("")
A("## 为什么有这个文件")
A("")
A("项目此前的完成标准是「有名字、是定理、0 `sorry`」。**Lean 只检查定理是真的，从不检查它有多强**，")
A("于是一条 `:= h` 的复述、一条 `a = a` 的重言、一条只覆盖 4/12 的定理，")
A("可以和真正完整的定理一样被 `import`、被引用、被写进「已闭合」。")
A("")
A("**这不是猜测，是审阅出来的。** 第一层（被下游引用的 1,360 条定理）由子代理逐条按六个维度判定，")
A("结论在下面。六维度是：")
A("")
A("| 维度 | 问题 |")
A("|:--|:--|")
A("| A 强度 | 陈述是否需要更强才能支撑它的**用途**？ |")
A("| B 配套 | 按用途看还缺哪些定理？ |")
A("| C 前件 | 哪些假设本身可证、从而能删掉？ |")
A("| D 降级 | 精确做不到时，能否把声称降级成误差界（精确 → ε）？ |")
A("| E 覆盖 | doc 声称的范围是否真的覆盖？ |")
A("| F 信息量 | 是否重言 / 只复述假设 / 纯占位？ |")
A("")
A("## 严重度：不是「好不好修」，是「误导得多厉害」")
A("")
A("| 判定 | 含义 | 为什么这个顺序 |")
A("|:--|:--|:--|")
A("| **delete** | 陈述无信息量（`a = a`、`:= h`、`True`） | **什么都没说**，却占着一个名字，最坏 |")
A("| **strengthen** | 说的比该说的弱 | 说了真话但不够，下游按名字以为够 |")
A("| **downgrade** | 声称过强，实际只到子类/误差界 | 说了过头的话 |")
A("| **register** | 有债但当前不值得修 | 已知、已记录 |")
A("")
A("同一严重度内按**入度**（多少别处文件引用）降序：**被二十个文件依赖的弱定理才是会传染的那个。**")
A("")
A("## 统计（本层）")
A("")
A("| 判定 | 条数 |")
A("|:--|--:|")
for k in ["delete", "strengthen", "downgrade", "register", "keep"]:
    A("| `%s` | %d |" % (k, counts.get(k, 0)))
A("| **合计审阅** | **%d** |" % len(verdicts))
A("")
A("> **范围（一条必须说清的更正）**：本文件覆盖 **1,360 条**已审定理。")
A("> 它们最初是按**旧的、有缺陷的** `in_degree` 选出来的「第一层」。")
A("> 审阅人指出该指标把 docstring 提及与不同命名空间的同名声明算成引用，")
A("> 修正后（只计代码、且要求引用方真的 `import` 该模块）入度 ≥ 1 的定理只剩 **839** 条，")
A("> 最高入度从 183 降到 18。")
A(">")
A("> 所以：**这 1,360 条是「高价值样本」，不是精确的「承重集合」**——其中约 521 条实际入度为 0，")
A("> 而真正的承重集合里可能有尚未审阅的条目。")
A("> **六维度的判定本身不受影响**（它们不依赖入度），受影响的只有排序与层边界。")
A("> 下一轮按修正后的入度重跑第一层，并补齐剩余 7,587 条。")
A("")

TITLES = {
    "delete": "一、`delete`：陈述无信息量",
    "strengthen": "二、`strengthen`：说的比该说的弱",
    "downgrade": "三、`downgrade`：声称过强",
    "register": "四、`register`：已登记的债",
}
FIELD = {"delete": "F_content", "strengthen": "A_strength",
         "downgrade": "D_downgrade", "register": "note"}

for sev in ORDER:
    rows = [v for v in flagged if v["verdict"] == sev]
    A("## " + TITLES[sev])
    A("")
    if not rows:
        A("（无）")
        A("")
        continue
    A("| 位置 | 定理 | 入度 | 判定依据 |")
    A("|:--|:--|--:|:--|")
    for v in rows:
        why = (v.get(FIELD[sev]) or v.get("note") or "").replace("|", "\\|").replace("\n", " ")
        if len(why) > 240:
            why = why[:237] + "…"
        A("| `%s:%d` | `%s` | %d | %s |" % (v["file"], v["line"], v["name"], v["in_degree"], why))
    A("")

A("## 后续")
A("")
A("1. **按修正后的入度重跑第一层**（839 条），再补齐其余 7,587 条。")
A("   批次已按修正后的入度重新生成（`agent-tmp/review/batch_000..105.jsonl`）。")
A("2. **工具修正（已修，第 208 轮）**：审阅人报告的两处**本仓库工具自身**的缺陷已修复——")
A("   - 提取器现在只在**剥除全部注释**的文本里找声明，并从保留 docstring 的文本按偏移取回作者自述；")
A("     幻影声明消失（`theorem` 7,576→7,575，`structure` 158→157）；")
A("   - `in_degree` 只统计**代码**中的出现，且要求引用方真的 `import` 定义所在模块；")
A("     `induction` 183→1、`le_trans` 136→0。")
A("   **这是本轮最重要的收获之一：审阅人发现的不是库里的问题，而是丈量库的尺子的问题。**")
A("3. **`delete` 类是唯一可以立刻处理的**：它们没有信息量，删掉不损失任何东西，")
A("   而保留会让 8,000+ 的定理数虚高。")
A("")

io.open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(lines))
print("wrote %s" % OUT)
print("verdicts: %d  flagged: %d" % (len(verdicts), len(flagged)))
for k in ORDER:
    print("  %-10s %d" % (k, counts.get(k, 0)))
