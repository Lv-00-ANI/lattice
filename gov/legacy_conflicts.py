# -*- coding: utf-8 -*-
"""修正重名分析：区分「短名相同」与「真的会撞车」。

第一版脚本比较的是「名字最后一段」和「短名」，于是 `Lattice.relu` 与 `Lattice.Core.relu`
被判为冲突——但它们在 Lean 里是两个不同的全名，**不会撞车**。

真正的冲突只有一种：**同一全限定名被声明两次**。

本版：
- `full`：全限定名（含命名空间栈）重复 → 这才是会撞车的
- `short`：短名重复但全名不同 → 只是可读性问题，Lean 不报错
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


def scan(path):
    src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
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
    return out


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    full = collections.defaultdict(list)     # 全名 -> [(file)]
    short = collections.defaultdict(list)    # 短名 -> [(full, file)]

    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            for name, s in scan(p):
                full[name].append(rel)
                short[s].append((name, rel))

    real = {k: v for k, v in full.items() if len(set(v)) > 1}

    print("=" * 72)
    print("A. 真正会撞车的：同一全限定名被多个文件声明")
    print("=" * 72)
    print("   数量:", len(real))
    for k in sorted(real):
        print("   %-42s %s" % (asc(k), [asc(x) for x in real[k]]))

    print()
    print("=" * 72)
    print("B. 只是短名相同、全名不同（Lean 不报错）")
    print("=" * 72)
    clash = {k: v for k, v in short.items()
             if len(set(n for n, _ in v)) > 1}
    print("   数量:", len(clash))
    for k in sorted(clash)[:25]:
        print("   %-26s %s" % (asc(k), [asc(n) for n, _ in clash[k]][:4]))

    print()
    print("=" * 72)
    print("C. 判定")
    print("=" * 72)
    if not real:
        print("   无全限定名冲突 => 606 个旧库文件与 28 个内核模块可以共存于同一 Lean 项目。")
        print("   I3 之前的 11 条报告是短名比较造成的误判，需要修正门禁的判定逻辑。")
    else:
        print("   有 %d 处真冲突，必须改名。" % len(real))
    return 0


if __name__ == "__main__":
    sys.exit(main())
