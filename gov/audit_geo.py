#!/usr/bin/env python3
"""审计 `Zero/Geo/` 的模块依赖与命名规范。

## 为什么需要

目标要求「证明链彻底梳理干净，即使证明出来了文件也不能乱，
语言学术化专业化，该分文件的分文件，命名都要标注」。

`Zero/Geo/` 现在有 12 个文件，是本轮快速建成的。需要核对：
1. 依赖方向是否严格向下（无环）
2. 每个文件的导出是否超出其职责
3. 命名是否符合项目约定

只读。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
GEO = os.path.join(ZERO, "Lattice", "Geo")

IMPORT = re.compile(r"^import\s+(Zero\.Geo\.\S+)", re.M)
DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)


def mod_of(f):
    return "Lattice.Geo." + f[:-5]


def main():
    files = sorted(f for f in os.listdir(GEO) if f.endswith(".lean"))
    deps = {}
    decls = {}
    for f in files:
        src = io.open(os.path.join(GEO, f), encoding="utf-8").read()
        deps[mod_of(f)] = [d for d in IMPORT.findall(src) if d != mod_of(f)]
        decls[mod_of(f)] = DECL.findall(src)

    # 1. 依赖方向
    print("=" * 72)
    print("1. 依赖图")
    print("=" * 72)
    for m in sorted(deps):
        print("  %-26s -> %s" % (m.replace("Lattice.Geo.", ""), 
                                 [d.replace("Lattice.Geo.", "") for d in deps[m]] or "-"))

    # 2. 环检测
    print()
    print("=" * 72)
    print("2. 环检测")
    print("=" * 72)
    WHITE, GREY, BLACK = 0, 1, 2
    color = {m: WHITE for m in deps}
    cycles = []

    def dfs(u, stack):
        color[u] = GREY
        for v in deps.get(u, []):
            if v not in color:
                continue
            if color[v] == GREY:
                cycles.append(stack + [u, v])
            elif color[v] == WHITE:
                dfs(v, stack + [u])
        color[u] = BLACK

    sys.setrecursionlimit(10000)
    for m in deps:
        if color[m] == WHITE:
            dfs(m, [])
    if cycles:
        for c in cycles:
            print("  环:", " -> ".join(x.replace("Lattice.Geo.", "") for x in c))
    else:
        print("  无环，依赖严格向下")

    # 3. 拓扑层
    print()
    print("=" * 72)
    print("3. 拓扑层（自底向上）")
    print("=" * 72)
    rank = {}

    def depth(m, seen=None):
        if m in rank:
            return rank[m]
        if seen is None:
            seen = set()
        if m in seen:
            return 0
        seen.add(m)
        d = [x for x in deps.get(m, []) if x in deps]
        r = 0 if not d else 1 + max(depth(x, seen) for x in d)
        rank[m] = r
        return r

    for m in deps:
        depth(m)
    byrank = {}
    for m, r in rank.items():
        byrank.setdefault(r, []).append(m.replace("Lattice.Geo.", ""))
    for r in sorted(byrank):
        print("  L%d: %s" % (r, sorted(byrank[r])))

    # 4. 命名规范
    print()
    print("=" * 72)
    print("4. 声明统计与命名检查")
    print("=" * 72)
    bad = []
    for m in sorted(decls):
        kinds = [k for k, _ in decls[m]]
        names = [n for _, n in decls[m]]
        print("  %-26s %2d 声明 (%s)" % (m.replace("Lattice.Geo.", ""), len(names),
                                        ", ".join(sorted(set(kinds)))))
        for n in names:
            # 约定：小写开头，但两种情形例外——
            #   * structure/inductive/class（类型本身）
            #   * 返回 Prop 的 def（Lean 惯例：谓词用大驼峰）
            if n[0].isupper():
                if any(k in ("structure", "inductive", "class") for k in kinds):
                    continue
                # 找该声明行，看是否是 Prop 值
                text = io.open(os.path.join(GEO, m.replace("Lattice.Geo.", "") + ".lean"),
                               encoding="utf-8").read()
                mm = re.search(r"^[^\n]*\b" + re.escape(n) + r"\b(?:(?!\n\n)[^\n]*\n)*?[^\n]*:\s*[^\n]*Prop",
                               text, re.M)
                if mm:
                    continue
                bad.append((m, n, "大写开头但既非类型也非 Prop"))
    print()
    if bad:
        print("  命名疑点:")
        for m, n, why in bad:
            print("    %-24s %-30s %s" % (m.replace("Lattice.Geo.", ""), n, why))
    else:
        print("  命名检查通过")

    # 5. 文件行数
    print()
    print("=" * 72)
    print("5. 文件规模（预算 500 行）")
    print("=" * 72)
    total = 0
    for f in files:
        n = io.open(os.path.join(GEO, f), encoding="utf-8").read().count("\n") + 1
        total += n
        flag = "  ** 超预算 **" if n > 500 else ""
        print("  %-26s %4d 行%s" % (f, n, flag))
    print("  %-26s %4d 行" % ("合计", total))
    return 0


if __name__ == "__main__":
    sys.exit(main())
