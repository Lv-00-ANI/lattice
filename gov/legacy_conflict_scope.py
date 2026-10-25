# -*- coding: utf-8 -*-
"""冲突影响范围分析：36 组冲突会牵连多少个文件？

## 为什么算这个

36 个重名声明本身不多，但如果每个被**几十个文件引用**，那么改名就会牵连上千处。
反过来若引用很少，改名是局部的。

本脚本对每个冲突名，统计：
- 声明它的文件数
- **在其他文件里被引用**的次数（按裸名出现次数估计）

只读源码。

## 重要限制

裸名出现次数是**上界**：注释已剥离，但字符串和局部变量名仍可能计入。
所以结论应读作「至少 / 至多」的粗估，用于判断规模量级，不做精确断言。
"""
import io
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)
NS = re.compile(r"^namespace\s+(\S+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def scan(path):
    raw = io.open(path, "rb").read().decode("utf-8", "replace")
    src = strip_comments(raw)
    stack, out = [], []
    for line in src.splitlines():
        m = NS.match(line)
        if m:
            stack.append(m.group(1))
            continue
        e = re.match(r"^end\s+(\S+)\s*$", line)
        if e and stack:
            stack.pop()
            continue
        d = DECL.match(line)
        if d:
            out.append((".".join(stack + [d.group(1)]), d.group(1)))
    return out, src


def main():
    legacy_dir = os.path.join(ZERO, "Lattice", "Legacy")
    if not os.path.isdir(legacy_dir):
        print("Legacy 目录不存在")
        return 1

    files = {}
    for f in sorted(os.listdir(legacy_dir)):
        if f.endswith(".lean"):
            p = os.path.join(legacy_dir, f)
            files[f[:-5]] = scan(p)

    # 全名 -> 声明它的文件
    owners = collections.defaultdict(set)
    for mod, (decls, _src) in files.items():
        for name, _short in decls:
            owners[name].add(mod)

    dups = {n: ms for n, ms in owners.items() if len(ms) > 1}
    if not dups:
        print("无冲突")
        return 0

    print("=" * 74)
    print("冲突影响范围（%d 组）" % len(dups))
    print("=" * 74)
    print("%-40s %5s %6s %6s" % ("conflicting name", "files", "uses", "users"))
    print("-" * 74)

    total_users = set()
    rows = []
    for name in sorted(dups):
        short = name.split(".")[-1]
        pat = re.compile(r"\b" + re.escape(short) + r"\b")
        users = set()
        uses = 0
        for mod, (_decls, src) in files.items():
            if mod in dups[name]:
                continue
            hits = len(pat.findall(src))
            if hits:
                users.add(mod)
                uses += hits
        rows.append((uses, len(dups[name]), name, len(users)))
        total_users |= users

    rows.sort(reverse=True)
    for uses, nfiles, name, nusers in rows:
        print("%-40s %5d %6d %6d" % (asc(name), nfiles, uses, nusers))

    print("-" * 74)
    print("涉及文件总数（声明方 + 使用方）:", len(total_users | set().union(*dups.values())))
    print("总引用次数:", sum(r[0] for r in rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())
