#!/usr/bin/env python3
"""Registry consistency: every registered name has a definition, and every definition is registered.

## Why this exists

Round 27 a text splice deleted an entire `def` from `Lattice/Slots.lean` -- `variableWidthStack`. The
comment-integrity check passed, because the *comments* were intact; what was lost was a definition.
The symptom surfaced only as `unknown identifier` at the next build, and by then the spliced file was
already written.

So the registry gets its own check, and it is a **bidirectional name match** rather than a count:

    every name listed in `fullRegistry`  ->  a `def <name> : Slot :=` exists
    every `def <name> : Slot :=`         ->  the name appears in `fullRegistry`

A count comparison would catch a deletion but not a rename; the name match catches both, and it needs no
history baseline (the working tree may be uncommitted, so comparing against VCS is not available).

## Generalised

`check_registry(path, registry_name, def_signature)` is parameterised, because the same pattern -- a
hand-maintained list plus the declarations it refers to -- is what any future register in this project
would use. Only `Lattice/Slots.lean` uses it today.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402


def registry_entries(src, registry_name):
    """The bare names listed in `def <registry_name> : List ... := [ ... ]`."""
    m = re.search(r"^def\s+" + re.escape(registry_name) + r"\s*:[^\n]*:=\s*\[(.*?)\]",
                  src, re.M | re.S)
    if not m:
        return None
    body = m.group(1)
    return [b.strip() for b in re.findall(r"[A-Za-z0-9_']+", body)]


def slot_definitions(src, type_name):
    """The names of `def <name> : <type_name> :=` declarations."""
    return re.findall(r"^def\s+([A-Za-z0-9_']+)\s*:\s*" + re.escape(type_name) + r"\b",
                      src, re.M)


def check_registry(rep, path, registry_name="fullRegistry", type_name="Slot"):
    src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
    rel = os.path.relpath(path, ZERO).replace("\\", "/")

    entries = registry_entries(src, registry_name)
    defs = slot_definitions(src, type_name)

    if entries is None:
        rep.add("I6", "registry `%s` not found" % registry_name, rel)
        return
    if not defs:
        rep.add("I6", "no `%s` definitions found" % type_name, rel)
        return

    entry_set = set(entries)
    def_set = set(defs)

    for name in sorted(entry_set - def_set):
        rep.add("I6", "registry lists `%s` but no such definition exists" % name, rel)
    for name in sorted(def_set - entry_set):
        rep.add("I6", "definition `%s` is not listed in `%s`" % (name, registry_name), rel)
    # duplicates in the registry would silently inflate the owed count
    for name in sorted(entries):
        if entries.count(name) > 1:
            rep.add("I6", "`%s` listed %d times in `%s`" % (name, entries.count(name), registry_name),
                    rel)


def main():
    class R:
        def __init__(self):
            self.items = []

        def add(self, a, b="", c="", d=0):
            self.items.append((a, b, c, d))

    r = R()
    check_registry(r, os.path.join(ZERO, "Lattice", "Slots.lean"))
    if r.items:
        for it in r.items:
            print(it)
    else:
        print("registry consistent: every registered slot has a definition and vice versa")
    return 0 if not r.items else 1


if __name__ == "__main__":
    sys.exit(main())
