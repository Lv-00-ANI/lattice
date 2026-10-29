"""gov/check_layer_reachability.py -- every module in a layer must be reachable from that layer's aggregator.

## Why this exists, and the round it was written

Round 43 found the same defect one level **up**: `Lattice/Compose.lean` was on disk but not imported by
`Lattice.lean`, so five rounds of Compose work were only ever built by name -- and a **syntax error sat in that
file for five rounds** because the file was unreachable. `gate.py`'s I7 checks that `.olean` files exist, and
they did; **existence is not reachability.**

This asks the same question one level **down**: for every `Lattice/<Layer>/X.lean`, is `X` reachable from
`Lattice.<Layer>` through the import graph (transitively, so a module imported by another module counts)?

## The second thing it reports, which round 44 found the hard way

While measuring this, a **whole layer was silently skipped**: `Lattice/Slots/` was an **empty, untracked
directory**, so a scan that enumerates *files* never saw `Slots` at all, and reported "0 unreachable" for a
tree it had not fully examined. **An empty layer directory makes a measurement lie by omission.** So a layer
directory with no `.lean` files is now reported explicitly (it is a *single-file layer* with a vestigial
directory), and `Lattice/Slots/` was removed.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ROOT, "Lattice")

IMPORT = re.compile(r"(?m)^import\s+(Lattice\.[A-Za-z0-9_.]+)\s*$")


def graph_and_members():
    """`(graph, members)` where `graph: module -> imports` and `members: layer -> [module]`."""
    graph, members = {}, {}
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            mod = "Lattice." + rel[:-5].replace("/", ".")
            graph[mod] = set(IMPORT.findall(io.open(p, encoding="utf-8").read()))
            parts = rel.split("/")
            if len(parts) > 1:
                members.setdefault(parts[0], []).append(mod)
    return graph, members


def layer_names():
    """Top-level `Lattice/<Name>.lean` files that are layer aggregators or single-file layers."""
    out = []
    for f in sorted(os.listdir(LAT)):
        if f.endswith(".lean"):
            out.append(f[:-5])
    return out


def reach(graph, start):
    seen, stack = set(), [start]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for n in graph.get(m, ()):
            if n in graph and n not in seen:
                stack.append(n)
    return seen


def analyse():
    """`(rows, empty_dirs)`; `rows` is `(layer, total, reachable, [unreachable])`."""
    graph, members = graph_and_members()
    rows, empty_dirs = [], []
    for layer in layer_names():
        agg = "Lattice." + layer
        mem = sorted(members.get(layer, []))
        d = os.path.join(LAT, layer)
        if os.path.isdir(d) and not mem:
            empty_dirs.append(layer)
        if agg not in graph:
            rows.append((layer, len(mem), 0, mem))     # aggregator missing: everything is unreachable
            continue
        seen = reach(graph, agg)
        un = [m for m in mem if m not in seen]
        rows.append((layer, len(mem), len(mem) - len(un), un))
    return rows, empty_dirs


def self_test():
    ok = True
    # a module not reachable from the aggregator must be reported
    fake_graph = {"Lattice.A": {"Lattice.A.x"}, "Lattice.A.x": set(), "Lattice.A.y": set()}
    seen = reach(fake_graph, "Lattice.A")
    if "Lattice.A.y" in seen or "Lattice.A.y" not in {"Lattice.A.y"}:
        print("  reachability direction FAILED")
        ok = False
    if "Lattice.A.x" not in seen:
        print("  transitive reachability FAILED (a directly imported module must be reachable)")
        ok = False
    # transitivity: A -> x -> z means z is reachable
    fake_graph2 = {"Lattice.B": {"Lattice.B.x"}, "Lattice.B.x": {"Lattice.B.z"}, "Lattice.B.z": set()}
    if "Lattice.B.z" not in reach(fake_graph2, "Lattice.B"):
        print("  TWO-STEP reachability FAILED")
        ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    rows, empty_dirs = analyse()
    print("LAYER REACHABILITY (every module reachable from `Lattice.<Layer>`)")
    bad = 0
    for layer, total, ok_n, un in rows:
        flag = "" if not un else "  <-- %d UNREACHABLE" % len(un)
        print("  %-14s %4d module(s), %4d reachable%s" % (layer, total, ok_n, flag))
        for m in un[:5]:
            print("       %s" % m)
        if len(un) > 5:
            print("       ... and %d more" % (len(un) - 5))
        bad += len(un)

    if empty_dirs:
        print()
        print("  ⚠ EMPTY LAYER DIRECTORIES: %s" % ", ".join(empty_dirs))
        print("    A directory with no `.lean` file makes any file-enumerating scan SILENTLY SKIP that layer.")
        print("    Round 44 hit exactly this: `Lattice/Slots/` was empty, `Slots` was never examined, and the")
        print("    measurement reported '0 unreachable' for a tree it had not fully looked at.")

    if bad or empty_dirs:
        print()
        print("LAYER REACHABILITY: %d unreachable module(s), %d empty layer dir(s)" % (bad, len(empty_dirs)))
        return 1
    print()
    print("LAYER REACHABILITY: all %d layer(s) fully reachable" % len(rows))
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
