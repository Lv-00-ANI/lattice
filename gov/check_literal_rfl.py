"""P0-4: the literal-`rfl` policy check, classified by CITATION rather than by statement shape.

## Why the shape-based classifier was abandoned

My first attempt classified each `:= rfl` theorem by REGEX over its statement (projection / derivation /
literal). Measuring it against three known cases showed it was wrong:

    graphTheory_templateNames_length          -> "projection"   (it is a bare numeral equality)
    artifact_layer_count                      -> "definitional" (it is a derived-count check)
    computabilityTheory_validB_eq_false       -> "definitional" (it is a boolean literal)

Statement shape cannot separate "a constant nothing cares about" from "a derivation being checked",
because the two look IDENTICAL as text. The distinguishing fact is not in the statement -- it is in
whether anything DEPENDS on it.

## The classification this check actually uses

For each theorem closing by `rfl`, count how many other Lean files mention its name:

  `load-bearing` -- cited from at least one other file. Whatever its statement looks like, something
                    uses it, so it is API and `rfl` is a legitimate proof.

  `leaf`         -- cited from no other file. This is where the plan's "free-floating literal" lives.

The check GATES only on `leaf`-and-numeral/bool theorems: those record a constant and carry no weight.
`leaf`-and-other ones are left alone (constructor unfoldings are legitimately uncited), and anything
load-bearing is never questioned.

Baseline: `gov/literal-rfl-baseline.txt`, one `<file>\t<name>` per line, holding the accepted leaves.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LATTICE = os.path.join(ROOT, "Lattice")
BASELINE = os.path.join(HERE, "literal-rfl-baseline.txt")

THEOREM = re.compile(r"^\s*(?:theorem|lemma)\s+(\w+)\s*:")
RFL = re.compile(r":=\s*rfl\s*$")
NUMERAL = re.compile(r"=\s*\d+\s*$|=\s*(?:true|false)\s*$")


def lean_files():
    for base, dirs, names in os.walk(LATTICE):
        dirs[:] = [d for d in dirs if d not in (".lake", "_archive")]
        for n in names:
            if n.endswith(".lean"):
                yield os.path.join(base, n)


def scan():
    out = []
    for path in lean_files():
        rel = os.path.relpath(path, ROOT).replace("\\", "/")
        lines = open(path, encoding="utf-8").read().split("\n")
        for i, line in enumerate(lines):
            if not RFL.search(line):
                continue
            j = i
            while j >= 0 and "theorem" not in lines[j] and "lemma" not in lines[j]:
                j -= 1
            if j < 0:
                continue
            m = THEOREM.match(lines[j])
            if not m:
                continue
            stmt = " ".join(lines[k].strip() for k in range(j, i + 1))
            stmt = re.sub(r"^.*?(?:theorem|lemma)\s+\w+\s*:", "", stmt)
            stmt = re.sub(r":=\s*rfl\s*$", "", stmt).strip()
            out.append({"file": rel, "name": m.group(1), "line": j + 1,
                        "stmt": stmt, "numeral": bool(NUMERAL.search(stmt))})
    return out


def citations(names):
    got = {n: set() for n in names}
    for path in lean_files():
        rel = os.path.relpath(path, ROOT).replace("\\", "/")
        text = open(path, encoding="utf-8").read()
        for n in names:
            if n in text:
                got[n].add(rel)
    return got


def load_baseline():
    if not os.path.exists(BASELINE):
        return set()
    return {l.rstrip("\n") for l in open(BASELINE, encoding="utf-8") if l.strip()}


def main(argv):
    rows = scan()
    cites = citations({r["name"] for r in rows})
    for r in rows:
        others = cites[r["name"]] - {r["file"]}
        r["cited"] = len(others)
        r["load_bearing"] = bool(others)

    lb = [r for r in rows if r["load_bearing"]]
    leaf_num = [r for r in rows if not r["load_bearing"] and r["numeral"]]
    leaf_other = [r for r in rows if not r["load_bearing"] and not r["numeral"]]

    print("LITERAL-RFL POLICY: %d theorem(s) close by `rfl`" % len(rows))
    print("  load-bearing (cited elsewhere)  %4d  -- API, never questioned" % len(lb))
    print("  leaf, numeral/bool equality     %4d  -- GATED by this check" % len(leaf_num))
    print("  leaf, other (constructor unfold)%4d  -- legitimate, not gated" % len(leaf_other))

    keys = {"%s\t%s" % (r["file"], r["name"]) for r in leaf_num}
    baseline = load_baseline()
    new = sorted(keys - baseline)
    stale = sorted(baseline - keys)

    for k in new:
        print("  NEW    %s" % k.replace("\t", " :: "))
    for k in stale:
        print("  STALE  %s" % k.replace("\t", " :: "))

    if "--write" in argv:
        with open(BASELINE, "w", encoding="utf-8", newline="\n") as f:
            for k in sorted(keys):
                f.write(k + "\n")
        print("  wrote %s (%d accepted leaves)" % (os.path.basename(BASELINE), len(keys)))
        return 0

    if new:
        print("LITERAL-RFL: %d NEW free-floating literal(s)" % len(new))
        return 1
    if stale:
        print("LITERAL-RFL: %d stale baseline entry(ies)" % len(stale))
        return 1
    print("LITERAL-RFL: ok (%d accepted leaves; %d load-bearing)" % (len(baseline), len(lb)))
    return 0


def self_test():
    """Prove this gate can FAIL, on an in-memory fixture, without touching the tree.

    The property under test is the decisive one: a free-floating numeral literal that is NOT in the
    baseline must be classified `NEW` and make the gate fail. A gate that can only ever return ok is
    exactly what round 30's audit found in `plugin_inventory.py --check` (a hard-coded empty dict), so
    every gate here is required to demonstrate its own failure.

    Implemented by overriding the two module-level scanners rather than writing a fake tree: the sandbox
    refuses writes outside the workspace, and the classification logic does not need a real file to be
    exercised.
    """
    global scan, citations, load_baseline
    saved = (scan, citations, load_baseline)
    scan = lambda: [{"file": "Lattice/Fake/Fixture.lean", "name": "fixture_length",
                     "line": 1, "stmt": "someNames.length = 7", "numeral": True}]
    citations = lambda names: {n: set() for n in names}      # cited nowhere -> a leaf
    load_baseline = lambda: set()                            # unregistered -> must be NEW
    try:
        rc = main([])
    finally:
        scan, citations, load_baseline = saved
    if rc == 0:
        print("SELFTEST: FAIL -- an unregistered free-floating literal did not make the gate fail")
        return 1
    print("SELFTEST: ok -- an unregistered free-floating literal makes the gate fail (exit %d)" % rc)
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
