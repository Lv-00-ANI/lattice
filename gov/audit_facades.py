# -*- coding: utf-8 -*-
"""Classify every module that declares NOTHING, and say which class it is in (stage C, P3-2).

## Why a classifier rather than a delete list

**The plan's P3-2 said "delete 19 facades". Measuring found 99 modules with no declarations, and they fall
into THREE classes that must not be treated alike:**

1. **LAYER AGGREGATOR** -- `Core.lean`, `Lib.lean`, `Runtime.lean`, ... **`check_layer_reachability.py`
   REQUIRES these; deleting one breaks the layering gate. They are not facades, they are the layer's index.**
2. **HONEST FACADE** -- declares nothing, imports a module the content MOVED to, and says so in a docstring.
   **These exist so that importers keep working across a move. Deleting them breaks the importers; deleting
   them safely requires rewriting every importer's path first.**
3. **EMPTY SHELL** -- `import Mathlib` and a `namespace`/`end` pair, nothing else. **No content, no record of
   where content went, no plan. These are the only ones that are pure noise.**

**=> "19 facades" is not a well-defined set. This script makes the set well-defined by measuring, and prints
the three classes separately.**

## What the numbers say about the tree

**The EMPTY SHELL class is concentrated in `Reference/Geometry/LvFormal/`:** the Hilbert axiom files,
`Interop/`, `Theory/Axioms/`. **They exist as path placeholders for a formalisation that was never written
into them.**

## Discipline

**This is a REPORTER, not a gate.** Deleting a module changes the module count and every aggregator, so the
decision belongs to a round that can also re-measure. What this script guarantees is that the decision is made
from a measured classification instead of from a number in a plan.

Usage:
    python audit_facades.py              # classify and report
    python audit_facades.py --json       # machine-readable
"""

import io
import json
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")

# Names that are layer aggregators by construction: `<Layer>.lean` at the top of `Lattice/`.
AGGREGATOR_DIRS = {
    "Core", "Lib", "Runtime", "CInterface", "Compose", "Domains",
    "Evidence", "Primitives", "Semantics", "Usage", "Plugins", "Reference",
}

DECL_RE = re.compile(
    r"^\s*(theorem|lemma|def|structure|inductive|instance|abbrev|class|example|noncomputable def)\b"
)


def strip_comments(text):
    """Remove Lean block comments `/- ... -/` and line comments, keeping code lines."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def classify(path, rel):
    text = io.open(path, encoding="utf-8", errors="replace").read()
    code = strip_comments(text)
    lines = [l.strip() for l in code.split("\n") if l.strip()]

    decls = [l for l in lines if DECL_RE.match(l)]
    if decls:
        return None  # has content; not a facade at all

    imports = [l.replace("import ", "", 1) for l in lines if l.startswith("import ")]
    rest = [
        l for l in lines
        if not l.startswith("import ")
        and not l.startswith("namespace ")
        and not l.startswith("end ")
        and not l.startswith("open ")
    ]

    top = rel.replace("\\", "/").split("/")[0]
    is_top = "/" not in rel.replace("\\", "/")
    if is_top and top.endswith(".lean") and top[:-5] in AGGREGATOR_DIRS:
        kind = "AGGREGATOR"
    elif rest:
        kind = "OTHER"        # e.g. attributes, options, or a `set_option`
    elif any(imp == "Mathlib" for imp in imports) and len(imports) == 1:
        kind = "EMPTY_SHELL"  # imports Mathlib and nothing else
    elif imports:
        kind = "FACADE"       # re-exports a real module
    else:
        kind = "EMPTY_FILE"

    return {"module": rel.replace("\\", "/"), "kind": kind, "imports": imports}


def collect():
    rows = []
    for dirpath, _dirnames, filenames in os.walk(LATTICE):
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, LATTICE)
            row = classify(path, rel)
            if row is not None:
                rows.append(row)
    return rows


def main(argv):
    rows = collect()
    by_kind = {}
    for row in rows:
        by_kind.setdefault(row["kind"], []).append(row)

    if "--json" in argv:
        print(json.dumps({"total": len(rows), "by_kind": by_kind}, indent=2, ensure_ascii=False))
        return 0

    print("FACADE AUDIT (modules that declare nothing)")
    print("  total declaration-free modules: %d" % len(rows))
    for kind in sorted(by_kind):
        print("  %-12s %d" % (kind, len(by_kind[kind])))

    shells = by_kind.get("EMPTY_SHELL", [])
    print("\n  EMPTY SHELL -- pure noise, safe to delete once importers are checked (%d):" % len(shells))
    for row in sorted(shells, key=lambda r: r["module"]):
        print("    %s" % row["module"])

    facades = by_kind.get("FACADE", [])
    print("\n  FACADE -- re-exports moved content, keeps importers working (%d):" % len(facades))
    for row in sorted(facades, key=lambda r: r["module"]):
        print("    %s -> %s" % (row["module"], ", ".join(row["imports"])))

    aggs = by_kind.get("AGGREGATOR", [])
    print("\n  AGGREGATOR -- required by check_layer_reachability, MUST NOT be deleted (%d):" % len(aggs))
    for row in sorted(aggs, key=lambda r: r["module"]):
        print("    %s" % row["module"])

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
