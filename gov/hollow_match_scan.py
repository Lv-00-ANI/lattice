# -*- coding: utf-8 -*-
"""扫描「空壳 match」：通配分支返回「什么都不做」的值。

## 为什么

`Cv00Memory.exec_stmt` 的 `| _ => .normal m env` 让 7 个语句构造子被定义成 no-op，
而文件里 0 sorry / 0 admit / 0 axiom —— 形式上的零逃逸掩盖了语义空壳。

这类模式若普遍存在，「已验证」这个说法就需要重新限定。

## 判据

一个 match 分支被判为「空壳」需同时满足：
1. 模式是通配 `_`（或 `| _ =>` 形式）
2. 返回值是「无操作」语义之一：`.normal m env`、`pure ()`、`none`、`[]`、`0`、`rfl`、`trivial`

通配分支本身不是问题（很多 match 是穷尽的、`_` 只为闭合）。所以本脚本**报告**而不判定，
由人来看上下文。

## 输出

文件、行号、返回值、所在函数名（尽力推断）。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
# Round 178, P2-16. This used to point at `Lattice/LvFormal`, which DOES NOT EXIST -- the Lv-00
# sources live under `Lattice/Reference/LvFormal`. So the scan walked nothing, printed
# "0 files, 0 findings", and exited 0: a checker reporting "all clear" about a directory it never
# opened. That is round 57's defect class again, and it is why this file now refuses to report a clean
# result over zero inputs.
ROOT = os.path.join(ZERO, "Lattice", "Reference", "LvFormal")
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

# 通配分支
WILDCARD = re.compile(r"^\s*\|\s*_\s*=>\s*(.+)$")

# 「无操作」返回值
NOOP_VALUES = [
    r"\.normal\s+\w+\s+\w+\s*$",       # .normal m env
    r"pure\s*\(\s*\)",                  # pure ()
    r"return\s*\(\s*\)",
    r"none\s*$",
    r"\[\s*\]\s*$",
    r"0\s*$",
    r"rfl\s*$",
    r"trivial\s*$",
    r"True\s*$",
    r"\.ok\s+\w+\s*$",
]

FUNCDEF = re.compile(r"^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']+)")
INDUCTIVE = re.compile(r"^\s*inductive\s+([A-Za-z0-9_']+)")
CTOR = re.compile(r"^\s*\|\s*([a-z][A-Za-z0-9_']*)\s*\(")


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def count_ctors(lines, name):
    """数某个 inductive 的构造子个数。"""
    for i, l in enumerate(lines):
        if re.match(r"\s*inductive\s+" + re.escape(name) + r"\b", l):
            n = 0
            for j in range(i + 1, min(i + 80, len(lines))):
                if CTOR.match(lines[j]):
                    n += 1
                elif lines[j].strip() and not lines[j].strip().startswith("|") \
                        and not lines[j].strip().startswith("deriving") \
                        and "where" not in lines[j]:
                    if n:
                        break
            return n
    return None


def main():
    findings = []
    all_inductives = {}

    files = []
    for base, dirs, fs in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if f.endswith(".lean"):
                files.append(os.path.join(base, f))

    # 先收集所有 inductive 名与构造子数
    for p in files:
        raw = io.open(p, "rb").read().decode("utf-8", "replace")
        lines = strip_comments(raw).splitlines()
        for i, l in enumerate(lines):
            m = INDUCTIVE.match(l)
            if m:
                all_inductives[m.group(1)] = count_ctors(lines, m.group(1))

    # 再找空壳 match
    for p in files:
        rel = os.path.relpath(p, ROOT).replace("\\", "/")
        raw = io.open(p, "rb").read().decode("utf-8", "replace")
        lines = strip_comments(raw).splitlines()
        cur_fn = None
        for i, l in enumerate(lines):
            fm = FUNCDEF.match(l)
            if fm:
                cur_fn = fm.group(1)
            wm = WILDCARD.match(l)
            if not wm:
                continue
            val = wm.group(1).strip()
            if not any(re.search(pat, val) for pat in NOOP_VALUES):
                continue
            # 往上找最近的 `match ... with`，推断被匹配的类型
            matched_type = None
            for k in range(i - 1, max(-1, i - 40), -1):
                mm = re.search(r"match\s+\(?\s*\w+\s*:\s*([A-Za-z0-9_.']+)", lines[k])
                if mm:
                    matched_type = mm.group(1).split(".")[-1]
                    break
                if re.search(r"\bmatch\b", lines[k]):
                    mm2 = re.search(r"match\s+([A-Za-z0-9_.']+)\s+", lines[k])
                    if mm2:
                        matched_type = mm2.group(1).split(".")[-1]
                        break
            findings.append({
                "file": rel, "line": i + 1, "fn": cur_fn, "value": val,
                "type": matched_type,
                "n_ctors": all_inductives.get(matched_type) if matched_type else None,
            })

    print("=" * 78)
    print("空壳 match 扫描  目标:", asc(ROOT))
    print("=" * 78)
    print("文件数:", len(files), "  发现:", len(findings))
    if not files:
        print()
        print("SCAN FOUND NO FILES under %s -- the scanner is misconfigured, not the tree clean." % ROOT)
        return 1
    print()
    for f in findings:
        ctors = (" [%d 个构造子]" % f["n_ctors"]) if f["n_ctors"] else ""
        print("%s:%d" % (asc(f["file"]), f["line"]))
        print("   函数: %s   匹配类型: %s%s"
              % (asc(str(f["fn"])), asc(str(f["type"])), ctors))
        print("   返回: %s" % asc(f["value"])[:100])
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
