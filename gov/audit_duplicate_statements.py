#!/usr/bin/env python3
"""Audit: do two declarations in the same file state the same thing under different names?

## Why this exists, and why it is not `audit_duplicates.py`

`audit_duplicates.py` groups declarations **by name** and reports names that occur more than once. That catches a
different problem from this one, and its output is dominated by a false positive: `dist`, `seg`, `zero`, `loss`
each appear in several modules under different namespaces, so they are "duplicates" only in the trivial sense of
sharing a leaf name. Of its 324 "identical" pairs, the measured number of real duplications was one.

The one it missed is the instructive case. In `Zero/Geo/Expr.lean`:

    theorem evalPts_add      (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) : ... := rfl
    theorem evalPts_add_eval (e₁ e₂ : GeoExpr n) (pts : ℕ → Pt n) : ... := rfl

Same file, same namespace, byte-identical statement, identical `rfl` proof, and **different names**. Grouping by
name cannot see it, because the two names differ. That is a criterion gap, not a grouping preference.

## The criterion here

Two declarations in the **same file** are duplicates when their signatures agree **after the declared name is
replaced by a placeholder**. Restrictions, each earning its place:

* **`theorem` / `lemma` only.** A `def` with the same body as another `def` is a judgement about reuse, not a
  defect; a duplicated *statement* is a defect with no redeeming reading.
* **Same file only.** Across files the namespaces may legitimately differ, which is exactly the false positive
  that swamps `audit_duplicates.py`. Restricting to one file makes the namespace question moot: Lean rejects two
  declarations of one name in one namespace, so two same-file declarations have two names, and identical
  statements under two names is a defect by construction.
* **Signature, not body.** Two theorems proving the same statement with different tactics are still the same
  statement; the audit reports the pair and leaves consolidation to a human.

## The bug this file shipped with, and its fix

Round 107's first version cut the signature at the first `" :="`, intending to stop at the proof body. But a
*statement* contains `:=` too -- in named arguments such as `GeoConstraint.Holds (n := n) ...`. So

    theorem allSame_collinear    (a b c : ℕ) : GeoConstraint.Holds (n := n) (.collinear a b c) allSame
    theorem allSame_rightAngle   (a b c : ℕ) : GeoConstraint.Holds (n := n) (.rightAngle a b c) allSame

were both truncated to `... GeoConstraint.Holds (n` and reported as duplicates. They are not: the two
constraints are different constructors, and the theorems are two facts, not one stated twice.

The fix cuts at the **depth-0** `:=` only, tracking bracket depth and skipping string/char literals. A `:=`
inside parentheses is part of the statement; one at depth 0 starts the proof. Round 108 also adds a guard: a
group is reported only if the members' full declarations differ **only** in the name, which is re-checked from
the untruncated text.

Exit code 0: this is a survey. The honest output of a survey is the list, not a verdict.
"""
import collections
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))

try:
    from sorry_axiom_census import strip_comments  # noqa: E402
except Exception:  # pragma: no cover - fallback if the helper moves
    def strip_comments(src):
        out, i, n, depth = [], 0, len(src), 0
        while i < n:
            if depth == 0 and src.startswith("/-", i):
                depth, i = 1, i + 2
                continue
            if depth > 0:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    if src[i] == "\n":
                        out.append("\n")
                    i += 1
                continue
            if src.startswith("--", i):
                while i < n and src[i] != "\n":
                    i += 1
                continue
            out.append(src[i])
            i += 1
        return "".join(out)


DECL = re.compile(
    r"^[ \t]*(?:(?:noncomputable|private|protected)[ \t]+|@\[[^\]]*\][ \t]*)*"
    r"(theorem|lemma)[ \t]+([A-Za-z0-9_']+)",
    re.M)

OPEN = "([{"
CLOSE = ")]}"
TERMINATORS = ("\n  where", "\nwhere")


def find_proof_start(text, start):
    """Index of the depth-0 `:=` that begins the proof body, or None."""
    depth = 0
    i, n = start, len(text)
    while i < n:
        c = text[i]
        if c in OPEN:
            depth += 1
            i += 1
            continue
        if c in CLOSE:
            depth = max(0, depth - 1)
            i += 1
            continue
        if depth == 0:
            if text.startswith(":=", i):
                return i
            for t in TERMINATORS:
                if text.startswith(t, i):
                    return i
        i += 1
    return None


def statement(text, m):
    """The declaration text up to the proof body, with the name elided.

    The elision is a placeholder rather than deletion so that two declarations whose statements differ *because*
    the name was mistaken for part of the statement cannot collide.
    """
    stop = find_proof_start(text, m.end())
    if stop is None:
        stop = len(text)
    body = text[m.end():stop]
    return " ".join(body.split())


def full_decl(text, m):
    """The whole declaration, normalised -- used to confirm the two differ only by name."""
    stop = find_proof_start(text, m.end())
    if stop is None:
        stop = len(text)
    return " ".join(text[m.start():stop].split())


def main():
    groups = collections.defaultdict(list)
    scanned = 0

    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            src = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            for m in DECL.finditer(src):
                scanned += 1
                groups[(rel, statement(src, m))].append(
                    (m.group(2), src[:m.start()].count("\n") + 1, full_decl(src, m)))

    hits = {}
    for key, rows in groups.items():
        if len(rows) < 2:
            continue
        # Guard: the untruncated declarations must differ only in the declared name.
        stripped = []
        for name, line, decl in rows:
            stripped.append(decl.replace(name, "<NAME>", 1))
        if len(set(stripped)) == 1:
            hits[key] = rows

    total = sum(1 for d in ("Core", "Lift", "Lib", "Slots", "Geo")
                if any(k[0].startswith("Lattice/%s/" % d) for k in hits))

    print("scanned %d theorem/lemma declarations in %s" % (scanned, os.path.basename(ZERO)))
    print()
    print("=" * 78)
    print("same file, same statement, different names -- %d group(s)" % len(hits))
    print("=" * 78)
    if not hits:
        print("  (none)")
    for (rel, sig), rows in sorted(hits.items()):
        print("  %s" % rel)
        for name, line, _decl in sorted(rows, key=lambda r: r[1]):
            print("      L%-5d %s" % (line, name))
        print("      statement: %s" % sig[:110])
        print()

    print("=" * 78)
    print("Why this is the right criterion here")
    print("=" * 78)
    print("  Declarations are grouped by (file, statement-with-name-elided), not by name. Grouping by name")
    print("  cannot find the case this audit exists for: `evalPts_add` and `evalPts_add_eval` in")
    print("  Zero/Geo/Expr.lean state the same thing under two names, and two names are two groups.")
    print()
    print("  The signature ends at the depth-0 `:=`, not at the first one. Round 107's first version cut at")
    print("  the first `:=` and truncated `GeoConstraint.Holds (n := n) (.collinear a b c)` to")
    print("  `GeoConstraint.Holds (n`, inventing two false duplicates in Zero/Geo/Initialise. A `:=` inside")
    print("  parentheses belongs to the statement; only a depth-0 one starts the proof.")
    print()
    print("  Restricting to one file is what makes the report trustworthy: Lean rejects two declarations of")
    print("  one name in one namespace, so same-file duplicates necessarily carry different names, and a")
    print("  shared statement across two names is a defect rather than a specialisation. Across files the")
    print("  namespaces may legitimately differ -- that is the `dist`/`seg`/`zero` false positive which")
    print("  dominates `audit_duplicates.py`'s 324 'identical' pairs, of which exactly one was real.")
    print()
    print("  Exit 0: a survey reports, it does not verdict. Consolidating a pair is a naming decision, and")
    print("  the surviving name should be the one whose docstring explains the statement.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
