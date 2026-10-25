# -*- coding: utf-8 -*-
"""迁移前的侦察：lvFormal 迁入 zero 后会不会与现有命名空间冲突？

## 为什么要先查

lattice/lean 那 606 个文件迁入后爆出 34 组全限定名冲突，代价是隔离 145 个文件。
同一类问题必须在 lvFormal 上先测，否则会重蹈覆辙。

## 查什么

1. lvFormal 声明的命名空间有哪些（是否都用 `namespace lvFormal`，还是散在顶层）
2. 顶层命名空间声明（无 namespace 包裹的）有多少 —— 这些会与 Zero.* 直接撞
3. 与 zero 现有 28 个模块的声明名交集

只读，不改任何文件。
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

SRC = os.path.join(ZERO, "..", "_harvest", "lv00", "formal", "lvFormal")

DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)
NS = re.compile(r"^namespace\s+(\S+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def scan(path):
    """返回 (qualified_names, [namespaces])。用缩进无关的 namespace 栈还原全名。"""
    src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
    stack, out, nss = [], [], []
    for line in src.splitlines():
        m = NS.match(line)
        if m:
            stack.append(m.group(1))
            nss.append(m.group(1))
            continue
        e = re.match(r"^end\s+(\S+)\s*$", line)
        if e and stack:
            stack.pop()
            continue
        d = DECL.match(line)
        if d:
            out.append(".".join(stack + [d.group(1)]))
    return out, nss


def main():
    if not os.path.isdir(SRC):
        print("源目录不存在:", SRC)
        return 1

    files = []
    for base, _d, fs in os.walk(SRC):
        for f in sorted(fs):
            if f.endswith(".lean"):
                files.append(os.path.join(base, f))

    ns_count = collections.Counter()
    toplevel = []          # 没有 namespace 包裹就声明的东西
    allnames = set()
    per_file = {}

    for p in files:
        rel = os.path.relpath(p, SRC).replace("\\", "/")
        names, nss = scan(p)
        for n in nss:
            ns_count[n] += 1
        for n in names:
            allnames.add(n)
            if "." not in n:
                toplevel.append((rel, n))
        per_file[rel] = len(names)

    print("=" * 70)
    print("lvFormal 迁移侦察  源:", asc(SRC))
    print("=" * 70)
    print("文件数:", len(files))
    print()
    print("--- namespace 使用频次 ---")
    for n, c in ns_count.most_common(20):
        print("   %-40s %d" % (asc(n), c))
    print()
    print("--- 顶层（无 namespace）声明数 ---", len(toplevel))
    for rel, n in toplevel[:25]:
        print("   %-46s %s" % (asc(rel), asc(n)))
    print()
    print("声明全名总数:", len(allnames))

    # 与 zero 现有模块求交
    zero_dir = os.path.join(ZERO, "Lattice")
    zero_names = set()
    for base, dirs, fs in os.walk(zero_dir):
        dirs[:] = [d for d in dirs if d not in ("Legacy", "LegacyConflicted", "LvFormal")]
        for f in fs:
            if f.endswith(".lean"):
                names, _ = scan(os.path.join(base, f))
                zero_names.update(names)
    inter = allnames & zero_names
    print()
    print("--- 与 zero 内核的声明全名交集 ---", len(inter))
    for n in sorted(inter)[:20]:
        print("   ", asc(n))
    return 0


if __name__ == "__main__":
    sys.exit(main())
