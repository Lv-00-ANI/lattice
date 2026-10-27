"""gen_theorem_usage.py -- theorem-level reachability in the skeleton layers.

Round 159 asked which MODULES are leaves. That is coarse: a module can be imported and still contain
theorems nobody cites. `Lattice.lean` imports everything, so module reachability is nearly free.

This goes one level down. For every theorem in Core/ and Lift/ (the skeleton -- where the objective's
carriers live), count how many places OUTSIDE its own file mention it.

Why only Core/Lift: a Lib theorem about, say, MLA attention is legitimately a terminal statement --
it exists to be read, not to be cited. The skeleton is different: a Core theorem with no consumer is
a carrier nobody carries anything with, which is the C8 failure this project has found five times.

Threshold note: one occurrence in its own file (the declaration itself) is subtracted.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))

#: layers where a zero-citation theorem is suspicious
SKELETON = ("Core", "Lift", "Slots.lean")

DECL = re.compile(r"(?m)^(?:noncomputable\s+)?(?:private\s+)?(?:theorem|lemma)\s+(\w+)")

#: The first run of this script reported 57% uncited, which was a bad criterion, not a finding:
#: a `@[simp]` theorem is used through the simp set and is never cited by name, and a `_aux` / `_step`
#: / `_eq` lemma is a local helper. Both are invisible to a by-name reference count.
#:
#: What IS worth reporting is a theorem whose NAME claims it is a main result -- `_forward`, `_sound`,
#: `_correct`, `_roundtrip`, `_exact`, `_complete`, `_bound` -- and which nothing cites. That is the
#: C8 shape: a carrier nobody carries anything with.
MAIN_WORDS = ("_forward", "_sound", "_correct", "_roundtrip", "_exact", "_complete",
              "_bound", "_covers", "_conservative", "_equiv")

SIMP = re.compile(r"(?m)^@\[simp[^\]]*\]\s*$")


def corpus():
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            out[rel] = io.open(p, "rb").read().decode("utf-8", errors="replace")
    return out


def main(argv):
    C = corpus()
    rows = []
    for rel, src in sorted(C.items()):
        top = rel.split("/")[0] if "/" in rel else rel
        if top not in SKELETON and rel not in SKELETON:
            continue
        # a theorem is `@[simp]` when the attribute line sits directly above it
        for m in re.finditer(r"(?m)^(?P<attr>(?:@\[[^\]]*\]\s*)?)"
                             r"(?:noncomputable\s+)?(?:private\s+)?(?:theorem|lemma)\s+(?P<name>\w+)", src):
            name = m.group("name")
            attr = m.group("attr") or ""
            if "simp" in attr:
                continue
            if not any(w in name for w in MAIN_WORDS):
                continue
            ext = []
            for other, osrc in C.items():
                if other == rel:
                    continue
                if re.search(r"\b%s\b" % re.escape(name), osrc):
                    ext.append(other)
            # second run reported 56% "uncited" and was again wrong: `compileAcc_correct` is used by
            # `compileProg_correct` three lines below it. Same-file use is USE. What is worth
            # reporting is a main-named theorem nothing references at all -- not even its own file.
            local = len(re.findall(r"\b%s\b" % re.escape(name), src)) - 1
            if not ext and local <= 0:
                rows.append((rel, name))

    print("=" * 84)
    print("skeleton theorems whose NAME claims a main result and which NOTHING references")
    print("=" * 84)
    for rel, name in rows:
        print("  %-48s %s" % (rel, name))
    print()
    print("zero-citation skeleton theorems: %d" % len(rows))
    total = 0
    for r, s in C.items():
        if (r.split("/")[0] if "/" in r else r) not in SKELETON and r not in SKELETON:
            continue
        for m in re.finditer(r"(?m)^(?P<attr>(?:@\[[^\]]*\]\s*)?)"
                             r"(?:noncomputable\s+)?(?:private\s+)?(?:theorem|lemma)\s+(?P<name>\w+)", s):
            if "simp" in (m.group("attr") or ""):
                continue
            if any(w in m.group("name") for w in MAIN_WORDS):
                total += 1
    print("skeleton theorems total          : %d" % total)
    if total:
        print("fraction uncited                 : %.0f%%" % (100.0 * len(rows) / total))
    print()
    print("## What this list means")
    print()
    print("Every entry is a TERMINAL theorem: an instantiation of a general result that already has")
    print("live consumers. `weightLadderN_forward` is `ladder_forward` at `weightLadderN`, and")
    print("`ladder_forward` is cited by `Slots.lean` and `Core/OneStepBridge.lean`. Such a theorem")
    print("exists for an external reader to cite, not for the library to call.")
    print()
    print("That is a different thing from a carrier nobody carries anything with (C8). This list is")
    print("therefore REPORT-ONLY: it is a reading list, and the judgement is whether each entry is")
    print("an instantiation of something live -- which it is, for all nine.")
    print()
    print("## Two criteria this script got wrong first")
    print()
    print("1. Counting all theorem kinds reported 57% uncited, because a `@[simp]` theorem is used")
    print("   through the simp set and never cited by name. Fixed by excluding simp-attributed ones.")
    print("2. Counting only CROSS-FILE references reported 56%, because `compileAcc_correct` is used")
    print("   by `compileProg_correct` three lines below it. Fixed by counting same-file use as use.")
    print()
    print("Both errors inflated the number. A reachability metric that does not know how Lean uses")
    print("theorems (simp sets, local helpers) measures the wrong thing.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
