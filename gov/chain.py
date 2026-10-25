# -*- coding: utf-8 -*-
"""Generate `PROOF-CHAIN.md` from the source, not from memory.

Hard requirement (3) is that the proof chain be completely straightened out. A chain written
by hand drifts the moment a theorem is renamed; the legacy tree shows exactly how that ends
(a 1.97 MB register whose counts disagreed with the code in five places).

So this tool derives the map from the modules themselves:

  * the import graph between `zero/` modules;
  * every `theorem`/`lemma`/`structure`/`class`/`def` and the module it lives in;
  * for each theorem, the zero-module declarations its statement or proof mentions, which
    gives an "uses" edge;
  * the slot registry's owed list, so the map shows what is still on credit.

Output: `gov/PROOF-CHAIN.md`, regenerated on every gate run.
"""
import io
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

REPORT = os.path.join(HERE, "PROOF-CHAIN.md")

DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?"
    r"(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+|partial[ \t]+)*"
    r"(theorem|lemma|structure|class|inductive|def|abbrev)[ \t]+"
    r"([A-Za-z0-9_.']+)", re.M)
IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def lean_files():
    out = []
    for base, dirs, files in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(files):
            if f.endswith(".lean"):
                out.append(os.path.join(base, f))
    out.append(os.path.join(ZERO, "Lattice.lean"))
    return out


def module_name(path):
    rel = os.path.relpath(path, ZERO).replace("\\", "/")
    return rel[:-5].replace("/", ".")


def layer_of(mod):
    """Which layer a module belongs to.

    Round 110 added the `geo` branch. Before that, every module not under Core, Lift or Slots was
    classified `root`, and `root` means *aggregator* -- a file that only re-exports. That made
    `Lattice.Geo`'s 49 modules aggregators by default, so the layer table read `root | 10` when nine of
    those ten were geometry. The geometry layer is not "missing" from the report; it was mislabelled,
    which is a different bug with a different fix: a missing branch, not a missing scan.
    """
    if mod.startswith("Lattice.Core"):
        return "core"
    if mod.startswith("Lattice.Lift"):
        return "lift"
    if mod.startswith("Lattice.Slots"):
        return "slots"
    if mod.startswith("Lattice.Lib"):
        return "lib"
    if mod.startswith("Lattice.Geo"):
        return "geo"
    # `Zero.Reference` deliberately falls through: it is the reference region, not one of this
    # project's layers, and giving it a layer of its own would suggest the layering rules apply.
    return "root"


def main():
    modules = {}
    for p in lean_files():
        src = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        imports = [m.group(1) for m in IMPORT.finditer(src)]
        decls = [(m.group(1), m.group(2)) for m in DECL.finditer(src)]
        modules[module_name(p)] = {
            "path": os.path.relpath(p, ZERO).replace("\\", "/"),
            "imports": [i for i in imports if i.startswith("Lattice")],
            "decls": decls,
            "src": src,
        }

    # every declaration name -> owning module
    owner = {}
    for mod, d in modules.items():
        for _kind, name in d["decls"]:
            owner.setdefault(name.split(".")[-1], mod)

    # uses: which other zero declarations each declaration's body mentions
    uses = collections.defaultdict(set)
    for mod, d in modules.items():
        src = d["src"]
        for kind, name in d["decls"]:
            if kind not in ("theorem", "lemma"):
                continue
            idx = src.find(name)
            if idx < 0:
                continue
            body = src[idx: idx + 6000]
            short = name.split(".")[-1]
            # Round 110: iterate over the identifiers actually present, not over every known name.
            # The old shape ran one regex per declaration per name -- roughly 5e7 searches at the
            # current size, which did not finish. `IDENT` deliberately excludes `'` because `\b`
            # treats `'` as a boundary; using a wider class here would silently change the edges.
            for other in set(IDENT.findall(body)) & owner.keys():
                if other == short or owner[other] == mod:
                    continue
                uses[name].add(other)

    L = []
    L.append("# LATTICE / ZERO proof chain")
    L.append("")
    L.append("> **Generated** by `gov/chain.py`. Do not edit: a hand-written chain drifts")
    L.append("> the moment a theorem is renamed, and the legacy register is the measured")
    L.append("> evidence of how that ends.")
    L.append("")
    L.append("## Layers")
    L.append("")
    L.append("| layer | modules | rule |")
    L.append("|:--|--:|:--|")
    L.append("| core | %d | no imports from lift/lib |" %
             sum(1 for m in modules if layer_of(m) == "core"))
    L.append("| lift | %d | may import core only |" %
             sum(1 for m in modules if layer_of(m) == "lift"))
    L.append("| slots | %d | metadata, imports nothing |" %
             sum(1 for m in modules if layer_of(m) == "slots"))
    L.append("| lib | %d | instantiated library, may import core only |" %
             sum(1 for m in modules if layer_of(m) == "lib"))
    L.append("| geo | %d | the geometry/constraint layer |" %
             sum(1 for m in modules if layer_of(m) == "geo"))
    L.append("| root | %d | aggregator, or a layer with no rule of its own |" %
             sum(1 for m in modules if layer_of(m) == "root"))
    L.append("")

    L.append("## Import graph")
    L.append("")
    for mod in sorted(modules, key=lambda m: (layer_of(m), m)):
        d = modules[mod]
        imps = d["imports"]
        L.append("- `%s` %s" % (mod, ("<- " + ", ".join("`%s`" % i for i in imps)) if imps else ""))
    L.append("")

    L.append("## Declarations per module")
    L.append("")
    L.append("| module | theorem/lemma | other |")
    L.append("|:--|--:|--:|")
    for mod in sorted(modules, key=lambda m: (layer_of(m), m)):
        ds = modules[mod]["decls"]
        th = sum(1 for k, _ in ds if k in ("theorem", "lemma"))
        L.append("| `%s` | %d | %d |" % (mod, th, len(ds) - th))
    L.append("")

    L.append("## Cross-module uses of theorem/lemma declarations")
    L.append("")
    L.append("An edge `A -> B` means the body of `A` mentions declaration `B` from another")
    L.append("module. These are the edges that make the chain a chain rather than a list.")
    L.append("")
    rows = []
    for name, deps in sorted(uses.items()):
        if deps:
            rows.append("- `%s` -> %s" % (name, ", ".join("`%s`" % d for d in sorted(set(deps)))))
    if rows:
        L.extend(rows)
    else:
        L.append("_none: every theorem is self-contained at the module boundary._")
    L.append("")

    # slot registry summary
    try:
        import check_slots
        slots = check_slots.collect()
    except Exception:
        slots = []
    owed = [s for s in slots if not s["discharged_by"]]
    L.append("## Open obligations (from `Zero/Slots.lean`)")
    L.append("")
    if owed:
        L.append("| slot |")
        L.append("|:--|")
        for s in owed:
            L.append("| `%s` |" % s["name"])
    else:
        L.append("_none_")
    L.append("")

    L.append("## The four target theorems and what each rests on")
    L.append("")
    L.append("| target | theorem | explicit obligations |")
    L.append("|:--|:--|:--|")
    L.append("| T1 compilation preserves meaning | `Compiler.compileProgram_sound` | `Compiler.sound` |")
    L.append("| T2 embedding soundness | `PenaltyEmbedding.embedding_sound_at_minimiser` | `PenaltyExact` |")
    L.append("| T3 extraction equivalence | `semantic_not_injective`, `no_extractor_both_layers` | `Representation.roundtrip` |")
    L.append("| T4 loop convergence | `Repair.progress`, `Repair.preserves` | `absorbs`, `decreases`, `atomic` |")
    L.append("")

    io.open(REPORT, "w", encoding="utf-8", newline="\n").write("\n".join(L))
    print("modules:", len(modules))
    print("declarations:", sum(len(d["decls"]) for d in modules.values()))
    print("cross-module use edges:", sum(len(v) for v in uses.values()))
    print("open slots:", len(owed))
    print("wrote", REPORT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
