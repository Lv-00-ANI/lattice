# -*- coding: utf-8 -*-
"""修 `audit_abstraction.py` 的三处误报 + 递归统计。

## 误报源与修法

1. **英文单词误报**（`zero` / `seg` / `loss`）：
   几何层的声明名与英文常用词撞车。修法：只把**多字符驼峰**或**长度 >= 4 的自定义名**
   当作几何声明，且该名必须在 Geo 层以 `def`/`structure`/`inductive` 定义过。

2. **命名空间不同不算重复**：
   `Repair.iterate_succ` 与 `RepairWF.iterate_succ` 是不同声明。
   修法：提取声明所在的 `namespace`，以 `namespace.decl` 为键。

3. **递归目录**：
   `Lib` 与 `Slots` 有子目录，`os.listdir` 只取顶层。
   修法：`os.walk`。
"""
import io
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

LAYERS = {
    "Core": "Lattice/Core",
    "Lift": "Lattice/Lift",
    "Lib": "Lattice/Lib",
    "Geo": "Lattice/Geo",
    "Slots": "Lattice/Slots",
}

DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+)", re.M)
NS = re.compile(r"^namespace\s+(\S+)", re.M)
TOKEN = re.compile(r"[A-Za-z0-9_']+")

# 英文常用词，即使与几何声明同名也不当作「泄露」
COMMON = {"Lattice", "seg", "loss", "dot", "dist", "step", "act", "Point", "point",
          "sat", "fix", "run", "map", "comp", "id"}


def files():
    for layer, rel in LAYERS.items():
        base = os.path.join(ZERO, *rel.split("/"))
        # a layer is normally a directory, but `Zero/Slots` is a single file
        if not os.path.isdir(base):
            if os.path.isfile(base + ".lean"):
                yield layer, base + ".lean", rel.split("/")[-1] + ".lean"
            continue
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for f in sorted(fs):
                if f.endswith(".lean"):
                    p = os.path.join(root, f)
                    yield layer, p, os.path.relpath(p, base).replace("\\", "/")


def namespaces_of(src):
    """Every namespace prefix a declaration in this file lives under."""
    out = []
    for m in NS.finditer(src):
        out.append(m.group(1))
    return out


def main():
    texts = {}
    decls = defaultdict(list)
    for layer, path, name in files():
        src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
        texts[(layer, name)] = src
        nss = namespaces_of(src)
        top = nss[0] if nss else ""
        for kind, d in DECL.findall(src):
            # 声明所在的最近 namespace（粗略：文件内第一个）
            decls[d].append((layer, name, kind, top))

    # 几何专属声明：在 Geo 层以 def/structure/inductive 定义、且不是英文常用词
    geo_defs = {d for d, v in decls.items()
                if any(x[0] == "Geo" and x[2] in ("def", "structure", "inductive") for x in v)
                and d not in COMMON and (len(d) >= 4 or any(c.isupper() for c in d))}

    print("=" * 74)
    print("1. Core / Lift 是否引用了 Geo 层的**定义**")
    print("=" * 74)
    leaks = []
    for (layer, name), src in sorted(texts.items()):
        if layer not in ("Core", "Lift"):
            continue
        toks = set(TOKEN.findall(src))
        own = {d for d, v in decls.items()
               if any(x[0] == layer and x[1] == name for x in v)}
        hit = sorted((toks & geo_defs) - own)
        if hit:
            leaks.append((layer, name, hit))
    if leaks:
        for layer, name, hit in leaks:
            print("  %-6s %-30s %s" % (layer, name, ", ".join(hit)))
    else:
        print("  无泄露：Core/Lift 不引用任何 Geo 定义")

    print()
    print("=" * 74)
    print("2. 同名且同命名空间的声明（真重复）")
    print("=" * 74)
    found = False
    for d, v in sorted(decls.items()):
        if len(v) < 2:
            continue
        keyed = {(x[3], x[1]) for x in v}
        if len(keyed) == len(v):
            continue          # 全部不同（namespace 或文件不同）
        found = True
        print("  %-28s %s" % (d, [(x[0], x[1], x[3]) for x in v]))
    if not found:
        print("  无真重复（同名声明都在不同 namespace 或不同文件）")

    print()
    print("=" * 74)
    print("3. 各层规模")
    print("=" * 74)
    total = 0
    for layer in LAYERS:
        fs = [k for k in texts if k[0] == layer]
        n_decl = sum(len(DECL.findall(texts[k])) for k in fs)
        lines = sum(texts[k].count("\n") + 1 for k in fs)
        total += lines
        print("  %-6s %2d 文件  %5d 行  %3d 声明" % (layer, len(fs), lines, n_decl))
    print("  %-6s      %5d 行" % ("合计", total))
    return 0


if __name__ == "__main__":
    sys.exit(main())
