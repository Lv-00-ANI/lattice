"""gen_lib_structure.py -- the shape of the Lib layer: which modules are leaves?

Lib is 605 of the tree's 784 modules. OBJECTIVE-MAP lists only a handful of Lib carriers, so a fair
question is whether the bulk of the library is doing anything -- and "doing anything" for a Lean module
means somebody imports it, or somebody uses its theorems.

`Lattice.lean` imports everything, so "imported at least once" is trivially true and tells you
nothing. The informative question is: which modules are imported ONLY by an aggregator?

A leaf module is not automatically wrong. A terminal application (a real architecture, a quantisation
scheme) is legitimately a leaf: it exists to be instantiated, not to be imported. What a leaf CANNOT
be is something the objective depends on, because nothing can reach it.

So this reports, per leaf:
  - its theorem count
  - whether any of its declarations is named in OBJECTIVE-MAP's carriers

That separates "terminal application, fine" from "objective carrier that nothing imports, broken".
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))
ROOT = os.path.abspath(os.path.join(HERE, ".."))

#: aggregator modules: importing everything is their job
AGGREGATORS = {"Lattice.lean", "Lib.lean", "Geo.lean", "Core.lean", "Lift.lean", "Slots.lean"}

IMPORT = re.compile(r"(?m)^import\s+(\S+)")
THEOREM = re.compile(r"(?m)^(?:theorem|lemma)\s+(\w+)")


def modules():
    """module name -> (path, source)."""
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            mod = "Lattice." + rel[:-5].replace("/", ".") if rel != "Lattice.lean" else "Lattice"
            out[mod] = (rel, io.open(p, "rb").read().decode("utf-8", errors="replace"))
    return out


def carriers():
    """names listed in OBJECTIVE-MAP's carrier column."""
    p = os.path.join(ROOT, "OBJECTIVE-MAP.md")
    if not os.path.exists(p):
        print("OBJECTIVE-MAP.md missing -- run gov/gen_objective_map.py first")
        raise SystemExit(2)
    src = io.open(p, encoding="utf-8").read()
    return set(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", src))


def main(argv):
    M = modules()
    imported_by = {m: set() for m in M}
    for mod, (_rel, src) in M.items():
        for target in IMPORT.findall(src):
            if target in imported_by and target != mod:
                imported_by[target].add(mod)

    from check_objective_coverage import CLAUSES
    CAR = carriers()

    # module of each declaration, to answer "is this carrier's module reachable?"
    decl_mod = {}
    for mod, (_rel, src) in M.items():
        for name in re.findall(r"(?m)^(?:noncomputable\s+)?(?:def|theorem|abbrev|structure|inductive)\s+(\w+)", src):
            decl_mod.setdefault(name, mod)

    leaves = []
    for mod, (rel, src) in sorted(M.items()):
        users = imported_by[mod]
        non_agg = {u for u in users if u.split(".")[-1] + ".lean" not in AGGREGATORS}
        if non_agg:
            continue
        thms = THEOREM.findall(src)
        hot = sorted(set(thms) & CAR)
        leaves.append((rel, len(thms), sorted(users), hot))

    print("=" * 88)
    print("leaf modules: imported by aggregators only (%d of %d)" % (len(leaves), len(M)))
    print("=" * 88)
    needs_attention = [l for l in leaves if l[3]]
    for rel, n, users, hot in leaves:
        mark = " *** OBJECTIVE CARRIER, unreachable ***" if hot else ""
        print("  %-56s theorems %-4d%s" % (rel, n, mark))
        if hot:
            print("      carriers: %s" % ", ".join(hot))

    print()
    print("leaves               : %d" % len(leaves))

    # a clause fails only when NONE of its carriers sits in a reachable module
    leaf_mods = {"Lattice." + rel[:-5].replace("/", ".") for rel, _n, _u, _h in leaves}
    broken = []
    for clause, names in CLAUSES.items():
        mods = {decl_mod.get(n) for n in names}
        if mods and mods <= leaf_mods:
            broken.append((clause, names))
    print("clauses with no reachable carrier : %d" % len(broken))
    for clause, names in broken:
        print("  %-40s %s" % (clause, ", ".join(names)))

    if broken:
        print()
        print("A clause whose every carrier is a leaf is broken: nothing can reach it.")
        return 1
    print()
    print("Every leaf is a terminal application, not an objective carrier -- nothing the objective")
    print("depends on is unreachable.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
