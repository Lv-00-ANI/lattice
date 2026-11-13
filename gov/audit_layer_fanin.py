# -*- coding: utf-8 -*-
"""Report the layer dependency STRUCTURE: who depends on whom, and how much (stage C, P3-4).

## The question

**A layer stack is not just an ordering constraint ("Core must not import Lib"). It is a claim that each
layer DOES SOMETHING for the layers above it.** **A layer whose modules are never imported by another layer
is either a leaf that matters (like `Usage`, which is an entry point) or dead weight.**

**=> the measurable form of "does this layer earn its place" is: how many DISTINCT modules outside the layer
import something inside it.**

## What this reports

For every layer:

- **`modules`** -- `.lean` files under it;
- **`fan_in`** -- distinct modules OUTSIDE the layer that import any module inside it;
- **`fan_in_layers`** -- which layers those importers come from;
- **`internal_only`** -- modules imported by NOTHING outside the layer (used only within, or not at all);
- **`orphans`** -- modules imported by NOTHING at all, inside or outside.

**`internal_only == modules` means the layer has no consumer anywhere: it is either an entry point or dead.**
**The report names which, by also checking whether the layer is imported by `Lattice.lean`.**

## Why a reporter, not a gate

**The right number of fan-in is not a constant.** **`Usage` has fan-in 0 by design (it is the demo entry
point); `Core` has a huge fan-in by design (everything rests on it).** **A gate would need a table of expected
values per layer, and inventing that table before the measurement exists is how a check becomes decorative.**

**So this measures first. When the numbers are in, the gate can encode the ones that are structurally
required.**

Usage:
    python audit_layer_fanin.py
    python audit_layer_fanin.py --json
"""

import io
import json
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")

IMPORT_RE = re.compile(r"(?m)^import\s+(Lattice\.[A-Za-z0-9_.]+)\s*$")


def modules_and_imports():
    """`(layer -> set(module), module -> set(imports))` for everything under `Lattice/`."""
    layer_of = {}
    imports = {}
    for dirpath, dirnames, filenames in os.walk(LATTICE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, LATTICE).replace("\\", "/")
            mod = "Lattice." + rel[:-5].replace("/", ".")
            parts = rel.split("/")
            layer = parts[0] if len(parts) > 1 else "(root)"
            layer_of[mod] = layer
            text = io.open(path, encoding="utf-8", errors="replace").read()
            imports[mod] = set(IMPORT_RE.findall(text))
    return layer_of, imports


def main(argv):
    layer_of, imports = modules_and_imports()

    by_layer = {}
    for mod, layer in layer_of.items():
        by_layer.setdefault(layer, set()).add(mod)

    # reverse index: module -> set of modules importing it
    importers = {mod: set() for mod in layer_of}
    for mod, deps in imports.items():
        for d in deps:
            if d in importers:
                importers[d].add(mod)

    # who does `Lattice.lean` import (the pipeline entry)?
    top = os.path.join(os.path.dirname(LATTICE), "Lattice.lean")
    top_imports = set()
    if os.path.exists(top):
        text = io.open(top, encoding="utf-8", errors="replace").read()
        top_imports = set(IMPORT_RE.findall(text))

    rows = {}
    for layer in sorted(by_layer):
        mods = by_layer[layer]
        outside_importers = set()
        inside_count = 0
        orphan_count = 0
        for m in mods:
            imps = importers[m]
            ext = {i for i in imps if layer_of.get(i) != layer}
            if ext:
                outside_importers |= ext
            else:
                inside_count += 1
                if not imps:
                    orphan_count += 1
        fan_in_layers = sorted({layer_of[i] for i in outside_importers})
        rows[layer] = {
            "modules": len(mods),
            "fan_in": len(outside_importers),
            "fan_in_layers": fan_in_layers,
            "internal_only": inside_count,
            "orphans": orphan_count,
            "in_pipeline": any(m in top_imports or (m.rsplit(".", 1)[0] in top_imports) for m in mods),
        }

    if "--json" in argv:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
        return 0

    print("LAYER FAN-IN (who depends on whom)")
    print("  %-14s %6s %7s %9s %8s  %s" % ("layer", "mods", "fan_in", "internal", "orphans", "consumed by"))
    print("  " + "-" * 92)
    for layer in sorted(rows, key=lambda l: -rows[l]["fan_in"]):
        r = rows[layer]
        consumers = ", ".join(r["fan_in_layers"][:4]) or "--"
        if len(r["fan_in_layers"]) > 4:
            consumers += " (+%d)" % (len(r["fan_in_layers"]) - 4)
        print("  %-14s %6d %7d %9d %8d  %s"
              % (layer, r["modules"], r["fan_in"], r["internal_only"], r["orphans"], consumers))

    print()
    entry_only = [l for l, r in rows.items() if r["fan_in"] == 0 and r["in_pipeline"]]
    no_consumer = [l for l, r in rows.items() if r["fan_in"] == 0 and not r["in_pipeline"]]
    print("  entry points (fan_in 0 but in the pipeline): %s" % (", ".join(sorted(entry_only)) or "none"))
    print("  NO CONSUMER ANYWHERE (fan_in 0, not in pipeline): %s"
          % (", ".join(sorted(no_consumer)) or "none"))

    total_orphans = sum(r["orphans"] for r in rows.values())
    print("\n  total orphan modules (imported by nothing at all): %d" % total_orphans)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
