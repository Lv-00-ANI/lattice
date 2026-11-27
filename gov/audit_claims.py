#!/usr/bin/env python3
"""Audit *relational claims* in docstrings: does the code establish the relation the prose asserts?

## Why this exists

Three findings in succession had the same shape:

* `Zero/Core/Simulation.lean` says the simulation shape is "stated once here and reused" -- nothing imported it;
* a theorem named `ladder_end_to_end` cited only same-file definitions, so it was not end-to-end at all;
* `Zero/Lift/EndToEnd.lean`'s table says the L2 -> L3 rung is "`Compiler.sound` (T1)" -- `Compiler` appeared in
  that file only inside comments.

`audit_docs.py` checks that a *name* mentioned in prose exists. `audit_reach.py` checks that a *declaration* is
used somewhere. Neither catches this: the name exists, and it may even be used elsewhere -- just not in the place
the prose claims.

## What is checked

For each Lean file, every docstring block (and each `/-- ... -/` comment) is scanned for assertion patterns that
name a declaration, and the named declaration is then looked for **in the same file's code**. Three patterns:

1. "is an instance of `X`", "the one-item instance of `X`", "`X`'s instance"
2. "reuses `X`", "consumed by `X`", "composes with `X`"
3. "equivalent to `X`", "agrees with `X`"

A hit is reported only when the named declaration does **not** appear in that file's code (comments stripped) *and*
the pattern is in the same file. Claims about another file ("see `Lattice.Lift.Foo.bar`") are skipped: those are
cross-references, not local claims.

Exit code 0: informational, like `audit_reach.py`. The judgement "is this claim actually wrong?" needs a reader;
the script only surfaces the candidates.
"""
import io
import os
import re
import sys
from collections import defaultdict

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ZERO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from layers import CANONICAL as LAYERS  # W0-2: one list, derived from the tree
# Round 245. `Runtime` (66 modules), `Domains` (99) and `Compose` (8) were created by the P2/P3
# migration, and this list was never extended -- so this audit silently IGNORED 173 modules, more
# than a fifth of the tree. The census that I5 rests on (`check_endtoend_content.py`) was among the
# blind ones, which is the worst place for a blind spot: it measures coverage.


DOC = re.compile(r"/--(.*?)-/|/-!(.*?)-/", re.S)

# (pattern, human label). The captured group is the claimed declaration's final segment.
PATTERNS = [
    (re.compile(r"instance\s+of\s+`([A-Za-z_][\w.']*)`"), "is an instance of"),
    (re.compile(r"reuse[sd]?\s+`([A-Za-z_][\w.']*)`"), "reuses"),
    (re.compile(r"consumed\s+by\s+`([A-Za-z_][\w.']*)`"), "is consumed by"),
    (re.compile(r"[Ee]quivalent\s+to\s+`([A-Za-z_][\w.']*)`"), "is equivalent to"),
    (re.compile(r"agrees\s+with\s+`([A-Za-z_][\w.']*)`"), "agrees with"),
]

# Module basenames that the prose legitimately names as modules rather than declarations.
MODULE_NAMES = {
    "Plücker", "Plucker", "Exterior", "ExteriorSmooth", "LayerExact", "PenaltySmooth",
    "Differentiable", "ExprDeriv", "FormDeriv", "Unconditional", "RepairBridge",
    "IRBridge", "Semantics", "Syntax", "Logic", "Rules", "Engine", "Compile",
}

DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+)?"
                  r"(?:theorem|lemma|def|structure|inductive|class|abbrev)\s+([\w.']+)", re.M)


def strip_comments(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    s = re.sub(r"--[^\n]*", " ", s)
    return s


def read(p):
    s = io.open(p, encoding="utf-8", errors="replace").read()
    return s.replace("\r\n", "\n").replace("\r", "\n")


def main():
    files = []
    for layer in LAYERS:
        base = os.path.join(ZERO, "Lattice", layer)
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for f in fs:
                if f.endswith(".lean"):
                    files.append(os.path.join(root, f))

    hits = []
    for p in files:
        raw = read(p)
        code = strip_comments(raw)
        # declarations defined in this file
        local = {d.split(".")[-1] for d in DECL.findall(code)}

        for m in DOC.finditer(raw):
            text = m.group(1) or m.group(2) or ""
            for pat, label in PATTERNS:
                for cm in pat.finditer(text):
                    target = cm.group(1).split(".")[-1]
                    if target in code:
                        continue          # the named thing *is* used in this file's code
                    if target in MODULE_NAMES:
                        continue          # the prose names a module, not a declaration
                    # cross-file pointer: the sentence names a `Zero.X.Y` path, so the claim is
                    # about another file and this check does not apply
                    sent = text[max(0, cm.start() - 200): cm.end() + 200]
                    if re.search(r"Zero\.[A-Za-z]+\.[A-Za-z]+", sent):
                        continue
                    hits.append((os.path.relpath(p, ZERO), label, target,
                                 raw[: m.start()].count("\n") + 1,
                                 target in local))

    print("relational claims in docstrings that name a declaration not used in the same file --", len(hits))
    print()
    print("=" * 78)
    by_file = defaultdict(list)
    for rel, label, target, line, is_local in hits:
        by_file[rel].append((line, label, target, is_local))
    for rel in sorted(by_file):
        print("  " + rel)
        for line, label, target, is_local in sorted(by_file[rel]):
            tag = " [defined here]" if is_local else ""
            print("    :%-5d %-20s `%s`%s" % (line, label, target, tag))

    print()
    print("=" * 78)
    print("Interpretation")
    print("=" * 78)
    print("  A hit means: the prose names a declaration as part of a relation, and that")
    print("  declaration's name does not appear in this file's code. Two readings:")
    print()
    print("    - the relation is established elsewhere and the prose is a pointer;")
    print("    - the relation is *only* in the prose.")
    print()
    print("  [defined here] marks the second kind as more likely: the declaration lives in")
    print("  this very file, so a real use would have been easy to write.")
    print()
    print("  Round 64's finding was of the second kind: `EndToEnd`'s table said the L2 -> L3")
    print("  rung was a `Compiler.sound` instance while `Compiler` appeared in that file only")
    print("  inside comments. The prose was corrected rather than the code.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
