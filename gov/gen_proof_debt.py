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
# Keyed by (file, name), NOT line: deleting a theorem shifts every line below it, and a line-keyed
# join would silently attach the wrong in-degree afterwards.
# ---------------------------------------------------------------- PATH_MAP
# DIRECTORY-DESIGN §2.8 says "PROOF-DEBT is regenerated with a `PATH_MAP`". **That mechanism did not
# exist** -- round 234 found it missing while piloting the P2 move. The 1369 verdicts are keyed on
# `(file, name)` where `file` is relative to `Lattice/`, so ANY `git mv` silently orphans every verdict
# for the moved file: the join misses, `in_degree` falls back to 0, and the ledger quietly loses the
# review. That is the "silent empty" failure mode again, in the ledger.
#
# The guard is `check_proof_debt_orphans.py`: a verdict whose file is gone AND is not listed here fails
# the build. So a future move that forgets this map is caught instead of absorbed.
from _debt_path_map import PATH_MAP

inv = {}
for line in io.open(os.path.join(REV, "inv.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    inv[(r["file"], r["name"])] = r

_reviewed_keys = set()
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
        # a moved file keeps its verdicts only because of PATH_MAP; see the comment above
        v["file"] = PATH_MAP.get(v.get("file"), v.get("file"))
        key = (v.get("file"), v.get("name"))
        rec = inv.get(key, {})
        v["in_degree"] = rec.get("in_degree", 0)
        v["users"] = rec.get("users", [])
        _reviewed_keys.add(key)
        verdicts.append(v)

ORDER = ["delete", "strengthen", "downgrade", "register"]
# Round 5. **The counts never went down.** `proof_debt_resolved.txt` was only *rendered* as a table
# ("已处理"), never subtracted from the flagged totals -- so after four rounds of real work the headline
# still read "34 strengthen / 3 downgrade / 107 register". A metric that cannot fall is not a metric:
# it tells a reader the work is at its starting point no matter what has been done.
#
# Fixed by matching `(path, name)` against the resolved entries and marking each verdict `resolved`.
RESOLVED_KEYS = set()
_RES = os.path.join(HERE, "proof_debt_resolved.txt")
if os.path.exists(_RES):
    for _ln in io.open(_RES, encoding="utf-8"):
        _ln = _ln.rstrip("\n")
        if not _ln or _ln.startswith("#"):
            continue
        _p = _ln.split("\t")
        if len(_p) >= 2:
            RESOLVED_KEYS.add((_p[0].strip(), _p[1].strip()))

for _v in verdicts:
    _f = (_v.get("file") or "").replace("\\", "/")
    _n = _v.get("name") or ""
    if (_f, _n) in RESOLVED_KEYS:
        _v["verdict"] = "resolved"

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
A("**这张表是「第一审判了多少条」，不是「还剩多少条没做」。**")
A("")
A("第 208 轮试过加一列「已处理 / 剩余」，**又删掉了**：账本里的一行可以覆盖 8 条判定"
  "（`delete × 8` 就是一行），也可能一条判定被推翻成另一类——")
A("**于是「剩余」会用行数算出假数字**（它会显示 `delete` 还剩 44，而那 44 条早已判完：")
A("8 条删除、34 条被对抗性复核推翻、3 条改写）。**错的统计比没有统计更糟。**")
A("")
A("真正做了什么，看下面的「已处理」一节与「对抗性复核」一节——**那两节逐条列出，不做汇总。**")

import _debt_coverage
# Round 27. The coverage table used to be computed from inv's STORED in_degree, which came from the
# review inventory and was itself computed by a defective metric -- so the page carried three numbers for
# one quantity (78.2% in the table, 100% in the prose, 839 in the caveat) and no instrument that could
# recompute any of them.  check_coverage_claim.measure() IS that instrument, and the gate compares the
# document against it; passing its result here means generator and gate share one measurement and cannot
# drift.  It is a full-tree scan, so the generator is a few tens of seconds slower -- that is the price of
# a number that can be checked.
import check_coverage_claim
_COV = check_coverage_claim.measure()
_debt_coverage.emit(A, _COV)
A("")
A("")
# **Round 777 (STAGE 4, gate defect G-3): every number below was HARDCODED.**
# The block said "1,360 reviewed", "839 load-bearing", "521 with in-degree 0", "7,587 remaining" --
# four literals in one paragraph, each of which had drifted from the tree by the time anyone read it.
# **=> the paragraph is now an INTERPOLATION over the live measurement.** A number that a generator
# can compute must never be typed into the generator.
_n_reviewed = len(flagged_all) if "flagged_all" in dir() else len(flagged)
_n_load = _COV.get("load", 0)
_n_zero = _COV.get("zero", 0)
_n_zero_reviewed = _COV.get("zero_audited", 0)
A("> **\u8303\u56f4\uff08\u5b9e\u6d4b\uff0c\u6bcf\u6b21\u91cd\u7b97\uff09**\uff1a\u672c\u6587\u4ef6\u8986\u76d6 **%d \u6761**\u5df2\u5ba1\u5b9a\u7406\u3002"
  % _n_reviewed)
A("> **\u672c\u6bb5\u6b64\u524d\u5199\u6b7b\u4e86\u56db\u4e2a\u6570\u5b57\uff081,360 / 839 / 521 / 7,587\uff09\uff0c\u800c\u5b83\u4eec\u65e9\u5df2\u4e0e\u6811\u8131\u8282\u3002**")
A("> **\u2192 \u7b2c 777 \u8f6e\u6539\u4e3a\u63d2\u503c\uff1a\u53ef\u7b97\u7684\u6570\u5b57\u4e0d\u5f97\u88ab\u6253\u5b57\u8fdb\u751f\u6210\u5668\u3002**")
A(">")
A("> **\u627f\u91cd\u96c6\uff08\u4fee\u6b63\u5165\u5ea6 \u2265 1\uff09\uff1a%d \u6761\uff0c\u5176\u4e2d\u5df2\u5ba1 %d \u6761\u3002**"
  % (_n_load, _COV.get("load_audited", 0)))
A("> **\u96f6\u5165\u5ea6\uff1a%d \u6761\uff0c\u5df2\u62bd\u5ba1 %d \u6761\u3002**"
  % (_n_zero, _n_zero_reviewed))
A("> **\u516d\u7ef4\u5ea6\u7684\u5224\u5b9a\u672c\u8eab\u4e0d\u4f9d\u8d56\u5165\u5ea6**\uff0c\u56e0\u6b64\u4e0d\u53d7\u4fee\u6b63\u5f71\u54cd\u3002")
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

RESOLVED = os.path.join(HERE, "proof_debt_resolved.txt")
if os.path.exists(RESOLVED):
    A("## 已处理（修好的条目**保留**在这里，不删）")
    A("")
    A("**为什么保留**：一个只会增长的债单没人信；而修好的条目悄悄消失更糟——")
    A("读者分不清「修好了」与「把发现删掉了」。")
    A("")
    A("| 位置 | 定理 | 做了什么 |")
    A("|:--|:--|:--|")
    for ln in io.open(RESOLVED, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        parts = ln.split("\t")
        if len(parts) >= 3:
            what = parts[2].replace("|", "\\|")
            A("| `%s` | `%s` | %s |" % (parts[0], parts[1], what))
    A("")

A("## 对抗性复核：第一审判错的 **34 / 45**")
A("")
A("把 45 条 `delete` 判定交给第二批子代理，任务设定为**论证第一审判错了**。结果：")
A("")
A("| 结论 | 条数 |")
A("|:--|--:|")
A("| **推翻**（keep） | **34** |")
A("| 确认可删（delete-safe） | 8 |")
A("| 应改写而非删除（rewrite） | 3 |")
A("")
A("**76% 的误判率**，原因高度集中：")
A("")
A("1. **删除会让构建断裂。** 多条「空定理」被同文件后面的定理当作 `atomic` 义务的实参")
A("   （`ObligationIndependence:95`/`:144` 就是 `absorbs_not_derivable`/`decreases_not_derivable` 的实参），")
A("   还有的被 `#print axioms` 审计行点名——而 `#print axioms` 对不存在的名字是**硬错误**。")
A("   第一审只看了 `proof` 与同名重复，没看后文调用点。")
A("2. **「重复」常常是删错了对象。** `softThresh_le_of_is_min` 是已授权改名后的成果，")
A("   真正重复的是同文件 `:428`，且 `:598` 用的是后者。")
A("3. **「证明便宜」被误当成「陈述为空」。** `add_norm_bound` 是三角不等式，便宜但不是重言。")
A("4. **4 条根本不是声明**，是 docstring 散文被旧提取器误抽（`stated`、`rather`、`applies`、")
A("   `eq_softThresh_of_is_min`）。提取器已修，**这些是陈旧数据而非新 bug**。")
A("")
A("**所以本文件把「一次判定」当线索，不当结论。** 任何 `delete` 必须经过")
A("（a）对抗性复核 与（b）全库构建通过，两步都过才落地。")
A("")
A("## 第二把尺子也是错的：点号记法")
A("")
A("对抗性复核发现 `in_degree` 漏掉**点号记法**：token 正则把 `.` 算进标识符，")
A("于是 `L.ladder_forward` 扫成单个 token，`ladder_forward` 永远匹配不到。")
A("实测 `ladder_forward` 有 **15 处调用、13 个文件**，`in_degree` 报 **1**。")
A("")
A("修正后（标识符按 `.` 切开）入度 ≥ 1 的定理从 839 升到 **872**，排名重排：")
A("`roundtrip_extractVec` 升到首位（18）。")
A("")
A("**这是本轮第二次「尺子错了，不是库错了」**——第一次是 docstring 被当成声明。")
A("两次都由审阅人发现，两次都无法由守卫自身发现。")
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
print("verdicts: %d  flagged: %d  resolved: %d"
      % (len(verdicts), len(flagged), counts.get("resolved", 0)))
for k in ORDER:
    print("  %-10s %d" % (k, counts.get(k, 0)))
