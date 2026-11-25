#!/usr/bin/env python
"""check_delivery_claims.py -- every backticked identifier in an entry document must be a declaration.

**Why this exists.** `DELIVERY-COMPILER-LAYER.md` was written to give the compiler layer an ENTRY, and round 1119
found that it cited `evaluate` -- an identifier that is declared NOWHERE in the tree. That is precisely the defect
`check_doc_names.py` catches inside Lean docstrings, reproduced in prose that no gate was watching. The fix was a
one-line edit; the lesson is that a document making checkable claims needs the same instrument as a docstring.

**What it checks.** For each markdown file given on the command line (default: the entry page), every backticked
token that LOOKS like an identifier is resolved against the tree's declarations, covering every declaration form
(`def`, `theorem`, `lemma`, `abbrev`, `structure`, `inductive`, `class`). Directory names and file stems are allowed
through a whitelist, because a document names paths as well as symbols.

**What it does NOT check**, stated so the tool is not read as stronger than it is: whether the CLAIM about the
declaration is true. Existence and content are different questions, and round 1120 measured content separately
(18 statements, 0 disagreements) with a one-off script whose expected tokens are listed there, not here.

Usage:
    python check_delivery_claims.py                     # the default entry document
    python check_delivery_claims.py --file X.md         # any document
    python check_delivery_claims.py --check             # exit 1 on any unresolved identifier
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAT = os.path.join(ROOT, "Lattice")

DEFAULT = os.path.join(ROOT, "DELIVERY-COMPILER-LAYER.md")

#: Path components and section names a document may cite without them being declarations.
ALLOW = {
    "Runtime", "Lib", "Core", "Compose", "Usage", "gov", "Lattice",
    "Lib/Compiler", "Runtime/LayerRepair", "Lib/Compiler/RealLayer",
}

IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")

DECL = (
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|inductive|class)\s+%s\b"
)


def corpus():
    """Comment-stripped sources, so a name mentioned only inside a comment does not count."""
    from tools.sorry_axiom_census import strip_comments

    out = {}
    for root, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            out[rel] = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
    return out


REGISTRY = os.path.join(HERE, "other-owned-stale.txt")


def report_foreign():
    """Report claims known stale in OTHER-owned files. Always exits 0.

    **Round 1123.** Round 1121 measured that MACRO-COGNITION.md says '99 gating + 21 reporters' while
    `verify_all.py` prints 105 gating. That file belongs to another writer, so the correct action is to record the
    fact where a machine can re-check it -- not to edit their prose and not to leave the knowledge in one round's
    notes. A stale claim in someone else's file must never block this writer, hence the constant exit code.
    """
    if not os.path.exists(REGISTRY):
        print("  registry absent: %s" % REGISTRY)
        return 0
    print("  foreign stale claims (measured, NOT edited -- other-owned):")
    n_still = n_done = 0
    for line in io.open(REGISTRY, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = [x.strip() for x in line.split("|")]
        if len(parts) < 3:
            continue
        fname, stale, measured = parts[0], parts[1], parts[2]
        fp = os.path.join(ROOT, fname)
        if not os.path.exists(fp):
            print("    MISSING FILE  %-28s %s" % (fname, stale)); continue
        body = io.open(fp, encoding="utf-8").read()
        if stale in body:
            n_still += 1
            print("    STILL STALE   %-28s '%s'  -> measured: %s" % (fname, stale, measured))
        else:
            n_done += 1
            print("    RESOLVED      %-28s '%s'" % (fname, stale))
    print("  still stale: %d ; resolved by their owner: %d" % (n_still, n_done))
    return 0


def main(argv):
    if "--foreign" in argv:
        return report_foreign()
    path = DEFAULT
    if "--file" in argv:
        path = argv[argv.index("--file") + 1]
    if not os.path.exists(path):
        print("check_delivery_claims: %s does not exist" % path)
        return 1

    doc = io.open(path, encoding="utf-8").read()
    C = corpus()
    checked, bad = 0, []
    for m in IDENT.finditer(doc):
        name = m.group(1)
        if name in ALLOW:
            continue
        checked += 1
        rx = re.compile(DECL % re.escape(name))
        if not any(rx.search(src) for src in C.values()):
            bad.append(name)

    print("  document      : %s" % os.path.basename(path))
    print("  identifiers   : %d checked (%d whitelisted)" % (checked, len(ALLOW)))
    print("  not a decl    : %d" % len(set(bad)))
    for n in sorted(set(bad)):
        print("      %s" % n)
    if bad and "--check" in argv:
        print("DELIVERY CLAIMS: %d identifier(s) do not resolve to a declaration" % len(set(bad)))
        return 1
    if not bad:
        print("DELIVERY CLAIMS: every cited identifier resolves to a declaration")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))