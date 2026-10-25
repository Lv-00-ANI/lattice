# -*- coding: utf-8 -*-
"""只读分析 2 + 3：空壳清单（含三分类）+ IRExpr.var bug 影响面。

## 空壳三分类（主线程定义）

  静默丢弃  —— 通配分支返回 no-op 值（`.normal m env`、`pure ()`、`0`、`[]`）
  显式失败  —— 通配分支返回失败标记（`none`、`.aborted`）
  合法兜底  —— 穷尽 match 后的默认分支，或 `match h : x with` 形式

## IRExpr.var bug 影响面

`eval_expr` 的 `.var n => ptX (env n)` 只取 x 坐标。
统计 IRConstraint 15 个构造子里，语义中真正出现 `eval_expr env ...` 的有几个。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
ROOT = os.path.join(ZERO, "Lattice", "LvFormal")
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


# ---------- 分析 2：空壳清单 ----------
WILDCARD = re.compile(r"^(\s*)\|\s*_\s*=>\s*(.*)$")
FUNCDEF = re.compile(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']+)")

SILENT = [r"\.normal\s+\w+\s+\w+\s*$", r"pure\s*\(\s*\)", r"^0\s*$", r"^\[\s*\]\s*$",
          r"^True\s*$", r"rfl\s*$", r"trivial\s*$", r"\.ok\s+\w+\s*$", r"^\(\)\s*$"]
EXPLICIT = [r"^none\s*$", r"\.aborted", r"^\.error", r"^false\s*$", r"^\.fail"]


def classify(val):
    for p in EXPLICIT:
        if re.search(p, val):
            return "显式失败"
    for p in SILENT:
        if re.search(p, val):
            return "静默丢弃"
    return "其他"


def analyze_hollow():
    rows = []
    for base, dirs, fs in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ROOT).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            lines = strip_comments(raw).splitlines()
            cur = None
            # 判断是否是 `match h : x with` 形式（合法兜底）
            for i, l in enumerate(lines):
                fm = FUNCDEF.match(l)
                if fm:
                    cur = fm.group(1)
                m = WILDCARD.match(l)
                if not m:
                    continue
                val = m.group(2).strip()
                kind = classify(val)
                if kind == "其他":
                    continue
                # 上文是否有 `match h :`
                prev = "\n".join(lines[max(0, i - 6):i])
                named = bool(re.search(r"match\s+h\s*:", prev))
                if named:
                    kind = "合法兜底"
                rows.append((rel, cur or "?", val, kind, i + 1))
    return rows


# ---------- 分析 3：IRExpr.var 影响面 ----------
def analyze_ir():
    p = os.path.join(ROOT, "Theory", "IR.lean")
    s = io.open(p, encoding="utf-8", errors="replace").read()
    lines = s.splitlines()

    # eval_expr 定义
    print("--- eval_expr 定义 ---")
    for i, l in enumerate(lines):
        if re.match(r"\s*def\s+eval_expr\b", l):
            for j in range(i, min(i + 14, len(lines))):
                print("  %4d %s" % (j + 1, asc(lines[j])[:100]))
                if j > i and lines[j].strip() == "":
                    break
            break

    # ir_sem 中每个构造子是否用 eval_expr
    print()
    print("--- IRConstraint 15 个构造子：语义是否用到 eval_expr ---")
    start = None
    for i, l in enumerate(lines):
        if re.match(r"\s*def\s+ir_sem\b", l):
            start = i
            break
    body_end = start
    for j in range(start + 1, min(start + 80, len(lines))):
        if re.match(r"^(def|theorem|abbrev|/-!)", lines[j]):
            body_end = j
            break
    else:
        body_end = min(start + 80, len(lines))
    body = lines[start:body_end]

    cur_ctor = None
    stats = {}
    for l in body:
        m = re.match(r"\s*\|\s*\.?([a-zA-Z][A-Za-z0-9_']*)\s*", l)
        if m:
            cur_ctor = m.group(1)
            stats.setdefault(cur_ctor, False)
        if cur_ctor and "eval_expr" in l:
            stats[cur_ctor] = True
    for c, uses in stats.items():
        print("   %-16s %s" % (asc(c), "使用 eval_expr  <-- 受 var bug 影响" if uses else "不直接使用"))
    hit = [c for c, u in stats.items() if u]
    print()
    print("   受影响的构造子: %d / %d" % (len(hit), len(stats)))
    print("   ", ", ".join(asc(c) for c in hit))


def main():
    print("=" * 78)
    print("分析 2：空壳通配分支清单（三分类）")
    print("=" * 78)
    rows = analyze_hollow()
    # 按文件聚合
    agg = {}
    for rel, fn, val, kind, ln in rows:
        agg.setdefault((rel, fn, kind), []).append(val)
    print("%-40s %-22s %4s %s" % ("文件", "函数", "数量", "性质"))
    print("-" * 78)
    for (rel, fn, kind), vals in sorted(agg.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        sample = sorted(set(vals))[:2]
        print("%-40s %-22s %4d %s  返回: %s"
              % (asc(rel), asc(fn)[:22], len(vals), kind,
                 asc(" / ".join(sample))[:28]))
    print()
    print("总计:", len(rows))
    from collections import Counter
    c = Counter(r[3] for r in rows)
    for k, v in c.most_common():
        print("   %-10s %d" % (k, v))

    print()
    print("=" * 78)
    print("分析 3：IRExpr.var (只取 x) 的影响面")
    print("=" * 78)
    analyze_ir()
    return 0


if __name__ == "__main__":
    sys.exit(main())
