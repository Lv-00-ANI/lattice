# -*- coding: utf-8 -*-
"""Is the uncited surface a defect, or is it what a *framework* looks like?

Round 30's re-verification measured 73 theorems with no in-repository citation. The reflex is to call
that dead code. This file records why that reflex is wrong here, and what the right measurement is.

## The distinction

A library has two kinds of consumer:

* **internal** -- another module in this repository;
* **external** -- a backend, a paper, a downstream project that imports `Zero` and proves its own
  obligations (`lift.compile.single_item_sound`, `lift.extract.roundtrip`, `core.repair.atomic`).

`Zero` is explicitly the second kind: its slots are *designed* to be discharged by someone outside. So
"cited nowhere in this tree" cannot be the health metric. What can be measured is narrower and honest:

  1. does every module that *states* a target theorem have its dependencies imported? (else it would not
     compile -- but check anyway, because a stale olean could hide it)
  2. is each `lift/` module reachable from a consumer, or is it an island?
  3. is the uncited set *mostly* endpoint statements, or mostly mid-chain lemmas?

A mid-chain lemma that nothing cites is a real problem: it means the chain is not connected. An endpoint
statement that nothing cites is the deliverable.

## The split that matters

`compileProgram_sound` is the end of a chain of eight lemmas; if the *intermediate* ones were uncited,
the chain would be broken. The measurement below prints, for each target theorem, its dependency
direction -- so "uncited endpoint" and "uncited middle" are separated.

Reads source; modifies nothing.
"""
import io
import os
import re
from collections import Counter
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)



# ---------------------------------------------------------------- scope
# `DSH_GATE_SCOPE=kernel` restricts the walk to the code this project wrote, which is what makes the
# fast verification path affordable. Unset means "everything".
KERNEL_PREFIXES = ("Lattice/Core/", "Lattice/Lift/", "Lattice/Lib/", "Lattice/Slots", "Lattice/Geo/")


def _in_scope(relpath):
    scope = os.environ.get("DSH_GATE_SCOPE")
    if not scope or scope == "all":
        return True
    r = relpath.replace("\\", "/")
    if r.startswith("Lattice/"):
        r = r[len("Lattice/"):]
        r = "Lattice/" + r
    return any(p in r for p in KERNEL_PREFIXES)

def modules():
    out = []
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                relp = os.path.relpath(p, ZERO).replace('\\', '/')
            if _in_scope(relp):
                out.append((p, relp[:-5].replace('/', '.')))
    return out


def main():
    mods = modules()
    text = {m: strip_comments(io.open(p, "rb").read().decode("utf-8", "replace")) for p, m in mods}
    allext = "".join(text.values())
    # One word-frequency pass instead of one regex scan per declaration.
    # The old form cost O(declarations x |allext|); at 632 files that is tens of
    # seconds to minutes, and it is why the full `verify_all.py` run never finished.
    # Word characters are `[A-Za-z0-9_]` -- the same set `\b` uses, so a name like
    # `progress` is counted the same way it was under the old `\bname\b` scan
    # (the `'` in `progress'` is a boundary, not part of the token).
    words = Counter(re.findall(r"[A-Za-z0-9_]+", allext))

    print("=" * 74)
    print("Island check: which modules does nothing import?")
    print("=" * 74)
    imported = set()
    for m in text:
        for i in re.findall(r"^import\s+(\S+)", text[m], re.M):
            imported.add(i)
    roots = {m for m in text if m in ("Lattice", "Lattice.Core", "Lattice.Lift", "Lattice.Lib", "Lattice.Slots")}
    islands = sorted(m for m in text if m not in imported and m not in roots)
    for i in islands:
        print("  island:", i)
    print("  total islands:", len(islands))

    print()
    print("=" * 74)
    print("Per-module: stated theorems, and how many of them are uncited")
    print("=" * 74)
    for m in sorted(text):
        names = [dm.group(2) for dm in DECL.finditer(text[m])]
        if not names:
            continue
        unc = [n for n in names if words.get(n, 0) <= 1]
        print("  %-42s %2d theorems, %2d uncited" % (m, len(names), len(unc)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
