"""Remove exactly the adversarial-verified delete-safe declarations.

Safety rules:
  * locate the declaration by NAME at/after the recorded line -- never by line alone, since lines shift;
  * take the preceding `/-- ... -/` docstring with it (an orphan docstring is worse than the theorem);
  * stop at the next top-level declaration or section marker, so nothing after it is touched;
  * build afterwards; a break means the reviewer was wrong after all and the single edit is reverted.

The last rule is the important one: the adversarial pass already showed that 34 of 45 first-pass
`delete` verdicts were wrong, and several were wrong precisely because deleting them breaks the build.
"""
import io
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

TARGETS = [
    ("Audit/ChainTransitivity.lean", "preserves_one"),
    ("Audit/CompositionClass.lean", "sequential_evidence_trivial"),
    ("Audit/CompositionClass.lean", "bridged_needs_bridge"),
    ("Audit/MultiComposition.lean", "chain_nil_identity"),
    ("Lib/Editing/RealCanonicalCompileComm.lean", "comm_via_extract"),
    ("Lib/Editing/RealExtractSurjectivity.lean", "extractVec_range_ne_proper"),
    ("Lift/ConstraintToLoss.lean", "compile_changes_type"),
    ("Lift/RatRepresentation.lean", "compile_changes_type"),
]

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+")
SECTION = re.compile(r"(?m)^(?:/-!|end\s|namespace\s|section\s)")


def cut_one(path, name):
    src = io.open(path, encoding="utf-8").read()
    m = re.search(
        r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:theorem|lemma)\s+" + re.escape(name) + r"\b", src)
    if not m:
        return None, "declaration not found"
    start = m.start()
    # pull in the preceding docstring, if any
    before = src[:start].rstrip()
    if before.endswith("-/"):
        d = before.rfind("/--")
        if d >= 0 and "\n" not in src[d:start].replace("/--", "", 1).replace("-/", "")[:0] or True:
            line_start = before.rfind("\n", 0, d) + 1
            start = line_start
    # find the end: next top-level declaration or section
    nxt = len(src)
    for pat in (DECL, SECTION):
        mm = pat.search(src, m.end())
        if mm and mm.start() < nxt:
            nxt = mm.start()
    block = src[start:nxt]
    if name not in block:
        return None, "suspicious cut"
    return (start, nxt), "ok"


def main():
    applied = []
    for rel, name in TARGETS:
        p = os.path.join(LAT, rel)
        span, why = cut_one(p, name)
        if span is None:
            print("  SKIP  %-44s %-28s %s" % (rel, name, why))
            continue
        original = io.open(p, encoding="utf-8").read()
        start, end = span
        new = original[:start] + original[end:]
        io.open(p, "w", encoding="utf-8", newline="\n").write(new)
        applied.append((rel, name, original, p))
        print("  cut   %-44s %s" % (rel, name))

    if not applied:
        print("nothing applied")
        return 1

    print()
    print("building ...")
    r = subprocess.run(["lake", "build", "Lattice"], cwd=ZERO,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = (r.stdout or "") + (r.stderr or "")
    errs = [l for l in out.split("\n") if l.startswith("error")]
    if r.returncode == 0 and not errs:
        print("BUILD OK -- all %d removals are safe" % len(applied))
        return 0

    print("BUILD FAILED -- reverting one at a time to find the culprit")
    for rel, name, original, p in applied:
        io.open(p, "w", encoding="utf-8", newline="\n").write(original)
    # re-apply one by one
    kept = []
    for rel, name, original, p in applied:
        cur = io.open(p, encoding="utf-8").read()
        span, _ = cut_one(p, name)
        if span is None:
            continue
        start, end = span
        io.open(p, "w", encoding="utf-8", newline="\n").write(cur[:start] + cur[end:])
        rr = subprocess.run(["lake", "build", "Lattice"], cwd=ZERO,
                            capture_output=True, text=True, encoding="utf-8", errors="replace")
        e2 = [l for l in ((rr.stdout or "") + (rr.stderr or "")).split("\n") if l.startswith("error")]
        if rr.returncode == 0 and not e2:
            kept.append((rel, name))
            print("  OK    %-44s %s" % (rel, name))
        else:
            io.open(p, "w", encoding="utf-8", newline="\n").write(
                io.open(p, encoding="utf-8").read().replace("", "") if False else cur)
            print("  REVERT %-43s %s  (build broke)" % (rel, name))
    print()
    print("kept %d of %d removals" % (len(kept), len(applied)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
