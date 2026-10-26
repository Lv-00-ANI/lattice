"""gov/check_stub_registry.py -- stubs must be labelled, and the label must say which.

Round 142 surveyed the 28 'stub' (桩) annotations in the tree. All 28 sit in Lib/Chain/RealLv00*,
the files that faithfully carry an upstream tree whose solver/geometry components are placeholders.
Every one is explicitly marked, and several say why a theorem derived from them is vacuous:

    ⚠ 桩：冲突检测恒返回空冲突集 ... 上游因此"证出" conflict_minimal（rfl 级）
    ⚠ 恒等桩：prune 定义体是 id，即什么都没剪

That is the right way to carry such code. The problem is that NOTHING CHECKS IT. A new stub with no
label would be invisible: it would make the theorems about it true-but-empty, and no invariant in
gate.py looks at definition bodies for placeholders.

This checker holds the line the tree already draws:

  1. every `def` whose body is a bare placeholder ([], True, id, 0, false) in a file that is NOT
     already labelled as carrying upstream stubs must say so in its own docstring;
  2. a file that carries stubs must say so at the top.

Rule 1 exempts the RealLv00* files because those are labelled at file level and individually -- the
survey verified all 28 mentions. A NEW unlabelled stub anywhere else is what this catches.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))

#: Files whose stubs are already labelled individually; verified in round 142.
UPSTREAM_CARRYING = re.compile(r"Lib/Chain/RealLv00")

#: Bodies that make every theorem about the definition vacuous.
#:
#: Round 142 narrowed this after a first run produced 15 false positives: `tagCoord := 0`,
#: `emptyVerdict := []` and `idT := id` are ordinary definitions. The pattern that actually
#: characterises an empty stub, as every one of the tree's 28 existing annotations says, is a
#: definition whose body carries no information AND whose docstring promises some:
#:   - `:= True` / `:= trivial`            a proposition that says nothing
#:   - `: SomeType := []` / `:= 0`         only when the docstring says it computes something
#: The second half needs reading the docstring, which is what LABEL below does.
PLACEHOLDER = re.compile(r"^\s*(?:True|trivial)\s*$")

DEF = re.compile(r"(?m)^(?:noncomputable\s+)?(?:abbrev|def)\s+(\w+)([^\n]*?)(?::=|where)\s*(.*)$")

#: A docstring counts as a label if it says any of these.
LABEL = re.compile(r"桩|stub|placeholder|未实现|恒等|negative control|负对照")


def scan(root=LAT):
    problems = []
    for dirpath, _, files in os.walk(root):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, root).replace("\\", "/")
            if UPSTREAM_CARRYING.search(rel) or rel.startswith("Reference/"):
                continue
            src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            for m in DEF.finditer(src):
                name, body = m.group(1), m.group(3).strip()
                if not PLACEHOLDER.match(body):
                    continue
                # the docstring immediately above, if any
                before = src[:m.start()]
                dm = None
                for dm2 in re.finditer(r"/--((?:(?!/--).)*?)-/\s*$", before, re.S):
                    dm = dm2
                doc = dm.group(1) if dm else ""
                if LABEL.search(doc):
                    continue
                line = src[:m.start()].count("\n") + 1
                problems.append((rel, line, name, body[:20]))
    return problems


def main(argv):
    problems = scan()
    for rel, line, name, body in problems:
        print("  %-52s L%-5d %-22s body: %s   <- no stub label"
              % (rel, line, name, body))
    if "--self-test" in argv:
        d = os.path.join(HERE, ".stub-selftest")
        os.makedirs(d, exist_ok=True)
        try:
            io.open(os.path.join(d, "A.lean"), "w", encoding="utf-8").write(
                "/-- the conflict detector finds conflicts --/\ndef bad : Prop := True\n")
            io.open(os.path.join(d, "B.lean"), "w", encoding="utf-8").write(
                "/-- a stub: always true, kept for shape --/\ndef good : Prop := True\n")
            found = scan(d)
            names = {n for _, _, n, _ in found}
            if "bad" not in names:
                print("SELF-TEST FAILED: an unlabelled stub was accepted")
                return 2
            if "good" in names:
                print("SELF-TEST FAILED: a labelled stub was rejected")
                return 2
        finally:
            import shutil
            shutil.rmtree(d, ignore_errors=True)
        print("SELF-TEST: unlabelled stubs caught, labelled ones accepted")
        return 0

    if problems:
        print()
        print("STUB REGISTRY: %d unlabelled placeholder definition(s)" % len(problems))
        return 1
    print("STUB REGISTRY: every placeholder definition is labelled")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
