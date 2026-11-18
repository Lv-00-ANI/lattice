# -*- coding: utf-8 -*-
"""Measure DUPLICATE DEFINITION NAMES across the tree.

## Why this checker exists

**Round 921 burned an entire round trying to reduce `reluCompile 1 0 (-1) = 0`.** The mathematics was one
line; the problem was that `relu` is defined TWICE:

| file | line | definition |
|---|---|---|
| `Lattice/Core/Net.lean` | 73 | `def relu (x : ℝ) : ℝ := max x 0` |
| `Lattice/Runtime/RealNonlinear.lean` | 35 | `def relu (x : ℝ) : ℝ := max x 0` |

Both have the SAME body, in DIFFERENT namespaces. `unfold relu` inside `reluCompile`'s context expanded
the wrong one and the goal never closed.

**=> the tree had no way to notice this.** `gate.py`'s I3 checks that a FULL NAMESPACE NAME is unique -- which
it is, `Lattice.relu` and `Lattice.relu` in two files are still two different declarations once the namespace
is resolved. The problem is at the level of the SHORT name that a reader (and `unfold`) sees.

## What it reports

**Every `def` / `theorem` / `structure` / `inductive` / `abbrev` whose SHORT name appears in more than one file,
with those files listed.** It does not fail by itself; it produces a number and a list, so the drift is visible.

**A name that appears in N files is a `collision` of width N. The checker reports the count and the worst cases.**

## Usage

    python audit_duplicate_names.py               # report
    python audit_duplicate_names.py --check       # fail if the total grew above the recorded baseline
    python audit_duplicate_names.py --self-test   # demonstrate both directions
"""

import io
import os
import re
import sys
import collections

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")

DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
                  r"(def|theorem|lemma|structure|inductive|abbrev|instance)\s+([A-Za-z_\u00c0-\uffff][\w\u00c0-\uffff']*)")

# Names that are EXPECTED to recur: they are generic vocabulary, not accidental duplicates.
ALLOWED = {
    "refl", "symm", "trans", "congr", "map", "map_id", "map_comp",
    "width", "length", "size", "empty", "append", "compile", "extract",
    "Sat", "out", "sound", "complete", "criterion", "roundtrip",
}


def strip_comments(src):
    """Remove `--` line comments and nested `/- ... -/` blocks. Docstrings are block comments.

    **Round 967: this was MISSING, and it produced a false positive that was believed for three rounds.**

    `FinSupport.lean` quotes the weight type's signature inside its module docstring:

        abbrev IRWeights : Type := ℕ → ℝ

    The line starts with `abbrev`, so the line-based DECL regex counted it as a DEFINITION in that file.
    => the audit then reported the type as "defined in two files", which is false: it is declared exactly
    once, in `Compile.lean:74`.

    The same false positive also fired on a file this session wrote (`IRWeightsBridge.lean`) when its
    docstring quoted `abbrev <short name>` -- which is what exposed the defect.

    The fix is the one every other measuring script in `gov/` already uses: strip comments and docstrings
    BEFORE matching, so a quoted signature is prose rather than a declaration.
    """
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if two == "/-":
            depth = 1
            i += 2
            continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def scan():
    """short name -> sorted list of (relative file) that define it."""
    where = collections.defaultdict(set)
    for dirpath, _dirs, files in os.walk(LATTICE):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ZERO).replace(os.sep, "/")
            try:
                text = io.open(path, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            for line in strip_comments(text).split("\n"):
                m = DECL.match(line)
                if not m:
                    continue
                kind, name = m.group(1), m.group(2)
                if name in ALLOWED:
                    continue
                where[name].add(rel)
    return {k: sorted(v) for k, v in where.items() if len(v) > 1}


def report(dups):
    total = sum(len(v) - 1 for v in dups.values())
    print("DUPLICATE NAMES: %d shared name(s), %d extra site(s)" % (len(dups), total))
    worst = sorted(dups.items(), key=lambda kv: -len(kv[1]))[:12]
    for name, files in worst:
        print("  %-34s in %d files" % (name, len(files)))
        for f in files[:4]:
            print("      %s" % f)
        if len(files) > 4:
            print("      ... and %d more" % (len(files) - 4))
    return total


BASELINE = 367   # round 967: measured AFTER stripping comments/docstrings (was 541 with them counted)


def main(argv):
    dups = scan()
    total = report(dups)
    if "--check" in argv:
        if total > BASELINE:
            print("\nDUPLICATE NAMES: %d > baseline %d -- a new short-name collision appeared"
                  % (total, BASELINE))
            return 1
        print("\nDUPLICATE NAMES: %d <= baseline %d" % (total, BASELINE))
    return 0


def self_test():
    """Both directions: the regex must fire on a real decl and not on a comment."""
    ok = True
    if not DECL.match("def relu (x : ℝ) : ℝ := max x 0"):
        print("  self-test FAILED: a real def was not matched")
        ok = False
    if DECL.match("-- def relu (x : ℝ) : ℝ := max x 0"):
        print("  self-test FAILED: a comment was matched as a decl")
        ok = False
    if not DECL.match("noncomputable def signCarrier : Carrier where"):
        print("  self-test FAILED: a modifier-prefixed def was not matched")
        ok = False
    dups = scan()
    if "relu" not in dups:
        print("  self-test FAILED: the known `relu` collision was not detected")
        ok = False
    print("  self-test: %s" % ("regex fires correctly and `relu` is detected"
                               if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
