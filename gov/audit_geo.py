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
# Round 245. The whole of `Geo/` moved to `Domains/` (99 modules), so this audit was pointing at an
# empty directory and reported "合计 0 行" -- **an audit of zero files must not be a pass.** That is
# precisely the failure mode its old self-test exemption rationalised ("the geometry walk is a pure
# enumeration whose failure mode is an empty result"): the enumeration went empty and nothing said so.
#
# It now audits both directories (either may be populated during a migration) and **fails when the
# total module count is zero**. The name is kept because renaming a gate is a separate change; the
# docstring says what it actually covers.
GEO = os.path.join(ZERO, "Lattice", "Domains")
GEO_LEGACY = os.path.join(ZERO, "Lattice", "Geo")

# Round 242. This matched `Zero.Geo.`, the OLD library's module prefix. Measured on the current tree:
# **183** `import Lattice.Geo.*` and **0** `import Zero.Geo.*` -- so the regex matched nothing, the
# graph was empty, every downstream finding (cycles, topological layers, upward edges) was vacuous,
# and because it is registered as a GATING check (it is not in REPORT_ONLY) it was a gate that could
# never fail. The project's own rule, from `check_selftest_coverage.py`: "a check which cannot
# demonstrate its own failure is indistinguishable from a check that passes."
#
# It now matches the prefix the tree actually uses. Both are still accepted, so the file keeps
# working if the old prefix ever reappears in a vendored fragment.
# Round 245. Same defect, third variant. The regex matched `Lattice.Geo.` -- then the whole layer moved
# to `Domains/`, so every internal edge became invisible and "无环" was vacuous AGAIN. A regex that
# silently matches nothing is the failure mode this file has now hit three times.
#
# It now matches the layer it actually scans, and `main` asserts NON-VACUITY below: a scan with zero
# internal edges on a multi-module layer is a defect, not a pass.
IMPORT = re.compile(r"^import\s+(?:Lattice|Zero)\.(?:Geo|Domains)(?:\.[A-Za-z]+)?\.(\S+)", re.M)
DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)


def mod_of(f):
    """Module name from a FILE PATH.

    Round 245: files may live under `Domains/` (post-migration) or `Geo/` (legacy), and the module
    prefix follows the directory so that graph keys match the `import` lines.

    Round 246: it must take the FULL path (the subdirectory decides nothing here, but the prefix does) and
    use only the basename for the module itself -- an earlier version did `f[:-5]` on whatever it was
    given, which silently produced keys like `Lattice.Domains.C:/.../ConstraintSet`.
    """
    name = os.path.basename(f)[:-5]
    hit = "Lattice.Domains." if (os.sep + "Domains" + os.sep) in f else "Lattice.Geo."
    return hit + name


WHITE, GREY, BLACK = 0, 1, 2


def find_cycles(deps):
    """Every cycle in `deps`, as a node list. Empty means the graph is acyclic.

    Round 242. This was inline in `main`, which **always returned 0** and had no `--self-test`, so the
    gate could not fail -- and for its entire life it was fed an EMPTY graph (the import regex matched
    `Zero.Geo.`, the old library's prefix). Extracted so a self-test can exercise it on synthetic data
    without touching the tree.
    """
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
    for m in sorted(deps):
        if color[m] == WHITE:
            dfs(m, [])
    return cycles


def self_test():
    """The detector must find a planted cycle and must not invent one in an acyclic graph."""
    cyc = find_cycles({"A": ["B"], "B": ["A"]})
    if not cyc:
        print("SELF-TEST FAIL: a 2-cycle was NOT detected")
        return 1
    self_loop = find_cycles({"A": ["A"]})
    if not self_loop:
        print("SELF-TEST FAIL: a self-loop was NOT detected")
        return 1
    if find_cycles({"A": ["B"], "B": [], "C": ["A"]}):
        print("SELF-TEST FAIL: an acyclic graph was reported as cyclic")
        return 1
    print("SELF-TEST PASS: detects 2-cycles and self-loops, and leaves a DAG alone")
    return 0


def main():
    problems = 0
    # Round 246. The listing was NON-RECURSIVE, so after `Domains/` gained the `Constraints/` and
    # `Geometry/` subdirectories this audit saw only the two aggregators (123 lines instead of 16,407)
    # and passed. That is the FOURTH vacuity variant in this one file -- so the walk is recursive now,
    # and the zero-modules assertion below still guards the total.
    files = []
    for d in (GEO, GEO_LEGACY):
        if not os.path.isdir(d):
            continue
        for root, _dirs, fs in os.walk(d):
            files.extend(os.path.join(root, f) for f in sorted(fs) if f.endswith(".lean"))
    files.sort()
    # module -> file, so NO code path has to reconstruct a path from a module name again.
    # Round 246: a second `os.path.join(GEO, name)` survived here and crashed once the modules
    # moved into `Domains/Constraints/` and `Domains/Geometry/`.
    file_of = {}
    for _f in files:
        _hit = "Lattice.Domains." if (os.sep + "Domains" + os.sep) in _f else "Lattice.Geo."
        file_of[_hit + os.path.basename(_f)[:-5]] = _f
    if not files:
        print("GEO AUDIT: no modules found -- refusing to pass on an empty scan")
        return 1
    deps = {}
    decls = {}
    for f in files:
        src = io.open(f, encoding="utf-8").read()
        # the FULL path is required: mod_of decides the module prefix from the directory
        deps[mod_of(f)] = [d for d in IMPORT.findall(src) if d != mod_of(f)]
        decls[mod_of(f)] = DECL.findall(src)

    edges = sum(len(v) for v in deps.values())
    if len(deps) > 1 and edges == 0:
        print("GEO AUDIT: %d modules but ZERO internal edges -- the import scan is vacuous" % len(deps))
        return 1

    # 1. 依赖方向
    print("=" * 72)
    print("1. 依赖图")
    print("=" * 72)
    for m in sorted(deps):
        print("  %-26s -> %s" % (m.replace("Lattice.Geo.", "").replace("Lattice.Domains.", ""), 
                                 [d.replace("Lattice.Geo.", "") for d in deps[m]] or "-"))

    # 2. 环检测
    print()
    print("=" * 72)
    print("2. 环检测")
    print("=" * 72)
    cycles = find_cycles(deps)
    if cycles:
        for c in cycles:
            print("  环:", " -> ".join(x.replace("Lattice.Geo.", "") for x in c))
        problems += len(cycles)
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
                text = io.open(file_of[m], encoding="utf-8").read()
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
        n = io.open(f, encoding="utf-8").read().count("\n") + 1
        total += n
        flag = "  ** 超预算 **" if n > 500 else ""
        print("  %-26s %4d 行%s" % (os.path.basename(f), n, flag))
    print("  %-26s %4d 行" % ("合计", total))
    if problems:
        print("\nGEO AUDIT: %d problem(s)" % problems)
        return 1
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main())
