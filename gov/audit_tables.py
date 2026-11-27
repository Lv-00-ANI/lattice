#!/usr/bin/env python3
"""Report on documentation tables: what a row claims, and whether its names exist.

This is a **reporter**, not a gate: it always exits 0. The reason is in the history below.

## The bug this file was written for

`README.md` listed `leZero` `ltZero` `gtZero` in the `poly` row of the penalty table, marked exact. The kernel
has no exactness theorem for any of the three: `Lattice.Geo.Loss`'s `EqConstraint` does not even contain them, and
its module docstring says why. That row was wrong for as long as it stood, and every other audit passed on it.

## Seven drafts, and why the last one is a reporter

| draft | condition for "this row is backed" | outcome |
|:--|:--|:--|
| 1 | the name appears in some declaration or constructor | bad row passes: `leZero` *is* a constructor |
| 2 | only column 1 is examined | bad row passes: constructors sit in column 2 |
| 3 | the name occurs in the text of some theorem | bad row passes: `leZero` occurs in a `match` arm |
| 4 | as 3, with comments stripped first | same: the occurrence is real code, not a docstring |
| 5 | the name is shaped like a theorem (underscore, lowercase) | 15 false hits on module names (`Geo.Loss`) |
| 6 | as 5, allowing qualified names | still false hits on carriers (`Square.midpointPenalty`) |
| 7 | — | stopped; see below |

Drafts 5 and 6 fail for a reason no regex can fix. A table column mixes three kinds of name -- module, constraint
constructor, penalty carrier -- and which of them *ought* to have a theorem depends on the meaning of the column,
which lives in the author's head, not in the text. Draft 3 is the interesting one: "some theorem mentions this
constructor" is not "some theorem states this constructor's exactness", and deciding that needs a Lean parser.

A checker that cannot decide should not vote. So this script reports what it can verify -- whether the names a
row cites exist at all -- and says plainly that existence is not backing.

## What the real fix was

Not a better checker: a better table. `README.md` now writes the theorem names where it can, so a reader can see
the backing directly instead of trusting a check mark.

## Output contract

Exit 1 when a check-marked row cites a name that no kernel declaration, module,
namespace or constructor matches; else 0. Prints, for each such row: the row's first
cells, the backticked names it cites, and any of those names that do not resolve.

The unresolved-name test is decidable, so it gates. Whether a check mark is BACKED by a
theorem is not decidable here (see above), so that part is printed and never gated.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
from layers import CANONICAL as LAYERS  # W0-2: one list, derived from the tree
# Round 245. `Runtime` (66 modules), `Domains` (99) and `Compose` (8) were created by the P2/P3
# migration, and this list was never extended -- so this audit silently IGNORED 173 modules, more
# than a fifth of the tree. The census that I5 rests on (`check_endtoend_content.py`) was among the
# blind ones, which is the worst place for a blind spot: it measures coverage.


IDENT = re.compile(r"`([^`\n]+)`")
DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z0-9_']+)", re.M)
CHECK = "\u2705"


def kernel_identifiers():
    """Declaration names, module names, namespace roots, and constructor names."""
    names = set()
    for layer in LAYERS:
        base = os.path.join(ZERO, "Lattice", layer)
        names.add(layer)
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for d in dirs:
                names.add(d)
            for f in fs:
                if not f.endswith(".lean"):
                    continue
                names.add(f[: -len(".lean")])
                src = io.open(os.path.join(root, f), "rb").read().decode("utf-8", "replace")
                src = src.replace("\r\n", "\n")
                for m in DECL.finditer(src):
                    names.add(m.group(1))
                for m in re.finditer(r"^\s*\|\s*([A-Za-z0-9_']+)", src, re.M):
                    names.add(m.group(1))
                for m in re.finditer(r"^(?:namespace|end)\s+(\S+)", src, re.M):
                    names.add(m.group(1).split(".")[-1])
    names.update(["Geo", "Core", "Lift", "Lib", "Slots"])
    return names


def split_row(line):
    body = line.strip()
    if not body.startswith("|"):
        return None
    return [p.strip() for p in body.strip("|").split("|")]


def main():
    names = kernel_identifiers()
    readme = os.path.join(ZERO, "README.md")
    if not os.path.exists(readme):
        print("README.md not found -- nothing to report")
        return 0
    lines = io.open(readme, encoding="utf-8", errors="replace").read().replace("\r\n", "\n").split("\n")

    rows = 0
    findings = []
    for i, line in enumerate(lines, 1):
        cells = split_row(line)
        if cells is None or CHECK not in line:
            continue
        rows += 1
        cited = [m for c in cells for m in IDENT.findall(c)]
        cited = [m for m in cited if re.fullmatch(r"[A-Za-z][A-Za-z0-9_.']*", m)]
        if not cited:
            continue
        unknown = []
        for m in cited:
            last = m.split(".")[-1]
            if last in names or m in names:
                continue
            unknown.append(m)
        if unknown:
            findings.append((i, cells[0], cells[1] if len(cells) > 1 else "", unknown))

    print("README table rows containing a check mark: %d" % rows)
    print("=" * 78)
    if not findings:
        print("  every name cited by such a row exists in the kernel")
    for ln, c0, c1, unknown in findings:
        print("  README.md:%d  %r | %r" % (ln, c0, c1))
        print("      names that no declaration, module, namespace or constructor matches:")
        print("        %s" % ", ".join(unknown))
    print("=" * 78)
    print("  What this does NOT check: whether a check mark is *backed* by a theorem.")
    print("  Existence is not backing -- `leZero` exists as a constructor while no theorem")
    print("  states its exactness, which is exactly the error this file was written after.")
    print()
    print("  Seven conditions were tried for 'is this check mark backed' and the module")
    print("  docstring records why each failed; the last three would have to parse Lean")
    print("  statements rather than count names. The fix taken instead was to make the")
    print("  README tables name their theorems directly, so the backing is visible on the")
    print("  page rather than inferred by a script.")
    print()
    print("  What it DOES gate on: whether the names a row cites exist at all. That is")
    print("  decidable, so it is a real verdict -- a row citing a non-existent theorem is a")
    print("  broken citation and fails this check.")
    return 0 if not findings else 1


if __name__ == "__main__":
    sys.exit(main())
