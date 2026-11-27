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
import artifact_guard
SYNCED = []
sync = artifact_guard.sync
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
    """Every built module. `Reference/` is excluded: it is archived evidence, not part of the build.

    Round 177: this walked `Reference/` too, so the layer table in the generated document counted 910
    modules where the tree that actually builds has 788. A chain document that includes unbuilt modules
    reports edges that no build ever checks.
    """
    out = []
    for base, dirs, files in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if f.endswith(".lean"):
                full = os.path.join(base, f)
                # a generated probe is not part of the deliverable; see audit_counts.is_generated_probe
                if not f.endswith("Probe.lean"):
                    out.append(full)
    # NOT `Lattice.lean` from the repo root: `audit_counts` -- the authority the README quotes -- walks
    # `Lattice/` only, so counting the root aggregator here made this document's module total 789 where
    # the official count is 788. One document, one total.
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

    Round 177: the prefixes needed a TRAILING DOT. `Lattice.Core` is both the prefix of the layer and
    the name of the root-level aggregator `Lattice/Core.lean`, so `startswith("Lattice.Core")` claimed
    the aggregator for the layer and every row of the table read one too high (core 19 instead of 18,
    lift 56 instead of 55, lib 606, geo 93). `audit_counts` -- the authority the README quotes -- counts
    a root-level aggregator as `root`, so the two documents published two different layer splits for the
    same tree. Both now use the same rule.
    """
    if mod.startswith("Lattice.Core."):
        return "core"
    if mod.startswith("Lattice.Lift."):
        return "lift"
    if mod.startswith("Lattice.Slots."):
        return "slots"
    if mod.startswith("Lattice.Lib."):
        return "lib"
    if mod.startswith("Lattice.Geo."):
        return "geo"
    if mod.startswith("Lattice.Audit."):
        return "audit"
    if mod.startswith("Lattice.Usage."):
        return "usage"
    # `Lattice.Reference` deliberately falls through: it is the reference region, not one of this
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
    for key, rule in (("core", "no imports from lift/lib"),
                      ("lift", "may import core only"),
                      ("slots", "metadata, imports nothing"),
                      ("lib", "instantiated library, may import core only"),
                      ("geo", "the geometry/constraint layer, may import lift"),
                      ("audit", "re-states results; may import anything below"),
                      ("usage", "worked examples; top of the graph"),
                      ("root", "aggregator at `Lattice/`, re-exports only")):
        L.append("| %s | %d | %s |"
                 % (key, sum(1 for m in modules if layer_of(m) == key), rule))
    L.append("")
    # These eight numbers are the same split the README quotes (see `gov/audit_counts.py`), which is
    # the point: before round 177 this table counted the root-level aggregators into their own layers
    # and included `Reference/`, so it published a different split for the same tree.
    L.append("> The split above is the same one `README` quotes: root-level aggregators "
             "(`Lattice/Core.lean` etc.) count as `root`, and `Reference/` is excluded because it "
             "is not built.")
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
    # `owed` means DEBT. A `permanent` slot is a recorded boundary, not debt, and counting it as owed
    # would make the report claim three unfinished obligations that can never be finished. This used to
    # be its own copy of `not discharged_by` while `check_slots.py` had another copy -- and they would
    # have drifted the moment either changed. Both now use the `kind` field.
    owed = [s for s in slots if s["kind"] in ("open_", "weakened")]
    bounds = [s for s in slots if s["kind"] == "permanent"]
    L.append("## Open obligations (from `Lattice/Slots.lean`)")
    L.append("")
    if owed:
        L.append("| slot | state |")
        L.append("|:--|:--|")
        for s in owed:
            L.append("| `%s` | `%s` |" % (s["name"], s["kind"]))
    else:
        L.append("_none_")
    L.append("")
    if bounds:
        L.append("### Permanent boundaries (recorded, not debt)")
        L.append("")
        L.append("| slot | why it cannot close |")
        L.append("|:--|:--|")
        for s in bounds:
            L.append("| `%s` | %s |" % (s["name"], s["reason"]))
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

    # **W0-3c: compare, do not overwrite.** The default path must not rewrite a tracked artifact.
    SYNCED.append(("gov/PROOF-CHAIN.md", sync(REPORT, "\n".join(L), allow_write="--write" in sys.argv)))
    print("modules:", len(modules))
    print("declarations:", sum(len(d["decls"]) for d in modules.values()))
    print("cross-module use edges:", sum(len(v) for v in uses.values()))
    print("open slots:", len(owed))
    rc = artifact_guard.require_synced(SYNCED, "PROOF-CHAIN")
    if rc:
        return rc
    print("wrote", REPORT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
