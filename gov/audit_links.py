#!/usr/bin/env python3
"""核实「四条平行链路」：谁 import 谁？

## 背景

子代理复核指出 `Lift` / `Geo` / `LvFormal` / `Legacy` 四组之间无 import 边。
这是「不是一条端到端链路」的直接证据，必须自己核实。

只读。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
IMPORT = re.compile(r"^import\s+(\S+)", re.M)

GROUPS = {
    "Core": "Lattice.Core",
    "Lift": "Lattice.Lift",
    "Lib": "Lattice.Lib",
    "Geo": "Lattice.Geo",
    "Slots": "Lattice.Slots",
    "LvFormal": "Zero.LvFormal",
    "Legacy": "Zero.Legacy",
}


def group_of(mod):
    for g, pre in GROUPS.items():
        if mod == pre or mod.startswith(pre + "."):
            return g
    return "other"


def main():
    edges = {}
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            mod = "Lattice." + rel[len("Lattice/"):-len(".lean")].replace("/", ".")
            g = group_of(mod)
            src = io.open(p, encoding="utf-8").read()
            for imp in IMPORT.findall(src):
                tg = group_of(imp)
                if tg != "other" and tg != g:
                    edges.setdefault((g, tg), 0)
                    edges[(g, tg)] += 1

    print("=" * 66)
    print("组间 import 边（仅非零）")
    print("=" * 66)
    names = list(GROUPS)
    print("%-10s %s" % ("", " ".join("%-9s" % n for n in names)))
    for a in names:
        row = []
        for b in names:
            if a == b:
                row.append("     -   ")
            else:
                row.append("%9d" % edges.get((a, b), 0))
        print("%-10s %s" % (a, " ".join(row)))

    print()
    print("=" * 66)
    print("与内核（Core/Lift/Lib/Geo/Slots）的连接情况")
    print("=" * 66)
    for g in ("LvFormal", "Legacy"):
        into = sum(edges.get((g, k), 0) for k in ("Core", "Lift", "Lib", "Geo", "Slots"))
        outof = sum(edges.get((k, g), 0) for k in ("Core", "Lift", "Lib", "Geo", "Slots"))
        print("  %-10s 指向内核: %d 条   内核指向它: %d 条" % (g, into, outof))
    return 0


if __name__ == "__main__":
    sys.exit(main())
