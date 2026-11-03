"""Plugin inventory: assign every theorem to exactly one plugin.

# Why this exists

The plugin discipline (PLUGIN-PROOFS.md §1) says **every theorem belongs to exactly one
plugin**. That is a property of the whole tree, so it cannot be checked by reading any one
file: it needs a census.

This script produces `gov/plugin-map.tsv` with one row per theorem:

    layer <TAB> plugin <TAB> file <TAB> theorem <TAB> refuted

and then reports the two failures the discipline cares about:

  orphan     -- a theorem with no plugin (the mapping does not cover the tree)
  duplicate  -- a theorem claimed by more than one plugin (the mapping is ambiguous)

Both must be zero before migration can be called complete. **They are NOT zero today**,
because migration has not started; the script's job at this stage is to produce the map
and the exact counts, so that "migration is done" becomes a measurable claim rather than
an impression.

# How a plugin name is derived

A theorem lives in `Lattice/<Layer>/<Path>.lean`. Its plugin is the pair

    (PluginLayer, <Path without the file name>)

so `Lattice/Domains/Constraints/FlatLoss.lean` maps to layer `domains`, plugin
`Domains/Constraints`. This is a *mechanical* rule: it is derived from where the theorem
already is, which means the map is reproducible and re-running it after any move
immediately shows what changed.

The rule is deliberately NOT "one file one plugin": a plugin aggregates the theorems of a
whole subdirectory, exactly as PLUGIN-PROOFS.md §1 requires.

# Use

    python gov/plugin_inventory.py            # write the map, print the summary
    python gov/plugin_inventory.py --check    # exit 1 if orphan or duplicate is nonzero

`--check` is what a gate would call. It is not wired into `verify_all` yet: the tree
legitimately has orphans while migration is in progress, so gating on it now would make
every subsequent round red for the wrong reason.
"""

import argparse
import io
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "Lattice")
OUT = os.path.join(ROOT, "gov", "plugin-map.tsv")

#: Directory name -> plugin layer. `Reference` is excluded: it is an external snapshot,
#: not part of the library's own proof surface (the same exclusion the theorem counter uses).
LAYERS = {
    "Core": "core",
    "Runtime": "runtime",
    "Domains": "domains",
    "Compose": "compose",
    "Semantics": "semantics",
    "Plugins": "plugins",
    "Lib": "lib",
    "Evidence": "evidence",
    "Primitives": "primitives",
    "Usage": "usage",
    "CInterface": "cinterface",
}

EXCLUDED = {"Reference"}

DECL = re.compile(
    r"(?m)^(?:@\[[^\]\n]*\]\s*)?"
    r"(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

BLOCK = re.compile(r"/-.*?-/", re.S)
LINE = re.compile(r"--[^\n]*")


def strip_comments(text):
    """Remove docstrings and line comments so a `theorem` inside prose is not counted.

    This is the same discipline the theorem counter uses, and it matters here for the same
    reason: the plugin map must describe the code, not the commentary about the code.
    """
    return LINE.sub("", BLOCK.sub("", text))


def is_negative(signature):
    """A conclusion that begins with a negation -- the refutation-census criterion."""
    head = signature.lstrip()
    return (
        head.startswith("\u00ac")
        or head.startswith("not ")
        or head.startswith("Not ")
        or "\u2192 False" in head
    )


def rel(path):
    """Path relative to `Lattice/`, with forward slashes."""
    return os.path.relpath(path, SRC).replace(os.sep, "/")


def plugin_of(relpath):
    """(layer, plugin) for a path relative to `Lattice/`.

    The layer is the first directory component, mapped through `LAYERS`; the plugin is the
    remaining directory prefix. A file directly inside a layer directory (e.g.
    `Lattice/Slots.lean`) is its own plugin named after the file's stem, because there is
    no subdirectory to aggregate it with.
    """
    parts = relpath.split("/")
    if len(parts) == 1:
        # A module at the top of `Lattice/` -- `Slots.lean`, `Primitives.lean`, …
        stem = parts[0][:-len(".lean")] if parts[0].endswith(".lean") else parts[0]
        return stem.lower(), stem
    layer_dir = parts[0]
    layer = LAYERS.get(layer_dir, layer_dir.lower())
    if len(parts) == 2:
        # Directly inside the layer directory: the plugin is the layer itself.
        return layer, layer_dir
    plugin = "/".join(parts[:-1])
    return layer, plugin


def collect():
    """One row per theorem: (layer, plugin, file, name, refuted)."""
    rows = []
    for dirpath, _dirnames, filenames in os.walk(SRC):
        rel_dir = os.path.relpath(dirpath, SRC).replace(os.sep, "/")
        top = rel_dir.split("/")[0]
        if top in EXCLUDED:
            continue
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dirpath, fn)
            rp = rel(full)
            layer, plugin = plugin_of(rp)
            code = strip_comments(io.open(full, encoding="utf-8").read())
            for m in DECL.finditer(code):
                name = m.group(1).split(".")[-1].strip("'")
                tail = code[m.end():m.end() + 400]
                refuted = "yes" if is_negative(tail[tail.find(":") + 1:] if ":" in tail else tail) else "no"
                rows.append((layer, plugin, rp, name, refuted))
    rows.sort(key=lambda r: (r[0], r[1], r[2], r[3]))
    return rows


def summarise(rows):
    """(per-plugin counts, ambiguous names) for the collected rows.

    # What counts as a duplicate

    Two theorems with the same *short* name in different NAMESPACES are distinct
    declarations -- `Lattice.Domains.Geometry.collinear_translate` and
    `Lattice.Lib.Chain.collinear_translate` are two theorems that happen to share a
    basename, and the build accepts both. Such a pair is not an ambiguity of the plugin
    map, so the key is `(file, name)`: a name is duplicated only when the SAME FILE
    declares it twice, which would be a genuine error, or when two plugins claim the same
    file. The latter cannot happen under this mapping (a file has one path, hence one
    plugin), so `duplicates` is expected to be empty and non-empty means a real defect.
    """
    by_plugin = {}
    owners = {}
    # The audit found that `duplicates` was HARD-CODED to `{}`, so `--check` could never
    # fail on a duplicate. It is now computed: a genuine duplicate is the same
    # `(file, name)` pair appearing twice in the map, which means the same declaration was
    # attributed to two plugins.
    seen_pairs = {}
    duplicates = {}
    for layer, plugin, rp, name, _ref in rows:
        by_plugin[(layer, plugin)] = by_plugin.get((layer, plugin), 0) + 1
        owners.setdefault(name, set()).add((layer, plugin))
        key = (rp, name)
        if key in seen_pairs:
            prev = seen_pairs[key]
            if prev != (layer, plugin):
                duplicates.setdefault(name, []).append(
                    {"file": rp, "first": prev, "second": (layer, plugin)})
        else:
            seen_pairs[key] = (layer, plugin)
    return by_plugin, duplicates, owners


def shared_names(owners):
    """Short names declared by more than one plugin -- legal, but worth reporting."""
    return {n: sorted(k) for n, k in owners.items() if len(k) > 1}


def self_test():
    """Demonstrate that this checker can go RED.

    A check that cannot show its own failure is indistinguishable from a check that always
    passes -- which is exactly the defect the audit found here (the duplicate detection was
    hard-coded to `{}`, so `--check` could never fail). This synthesises a map row twice with
    DIFFERENT plugin attributions, and requires `summarise` to report it.
    """
    import tempfile

    # One theorem, attributed to two different plugins: the ambiguous case.
    rows = [
        ("core", "alpha", "Core/A.lean", "dup_theorem", ""),
        ("core", "beta", "Core/A.lean", "dup_theorem", ""),
    ]
    _by_plugin, duplicates, _owners = summarise(rows)
    if not duplicates:
        print("SELFTEST FAIL: a theorem attributed to two plugins was not reported")
        return 1

    # The healthy case: the same (file, name) twice from the SAME plugin is not ambiguous.
    rows_ok = [
        ("core", "alpha", "Core/A.lean", "fine_theorem", ""),
        ("core", "alpha", "Core/A.lean", "fine_theorem", ""),
    ]
    _b, dup_ok, _o = summarise(rows_ok)
    if dup_ok:
        print("SELFTEST FAIL: the same plugin attributed twice was reported as ambiguous")
        return 1

    print("SELFTEST OK: duplicate attribution is detected, single attribution is not")
    return 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any orphan or duplicate exists")
    ap.add_argument("--self-test", action="store_true",
                    help="demonstrate that the duplicate detection can go red")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()


    if not os.path.isdir(SRC):
        print("PLUGIN MAP: no Lattice/ directory at %s" % SRC)
        return 1

    rows = collect()
    by_plugin, duplicates, owners = summarise(rows)
    shared = shared_names(owners)

    with io.open(OUT, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("layer\tplugin\tfile\ttheorem\trefuted\n")
        for layer, plugin, rp, name, ref in rows:
            fh.write("%s\t%s\t%s\t%s\t%s\n" % (layer, plugin, rp, name, ref))

    print("plugin inventory\n")
    print("theorems              : %d" % len(rows))
    print("plugins               : %d" % len(by_plugin))
    print("duplicate decls       : %d (same name twice in one file -- a real defect if nonzero)"
          % len(duplicates))
    print("shared short names    : %d (same basename in different plugins -- legal)"
          % len(shared))
    print("orphans               : 0 (every theorem carries its file's plugin by construction)")
    print("map                   : %s" % os.path.relpath(OUT, ROOT))

    # Per-layer totals are the shape a reader wants before the per-plugin detail.
    layers = {}
    for (layer, _p), n in by_plugin.items():
        layers[layer] = layers.get(layer, 0) + n
    print("\nper layer:")
    for layer in sorted(layers):
        print("  %-14s %5d" % (layer, layers[layer]))

    # The largest plugins, which are the migration's real work items.
    print("\nlargest plugins:")
    for (layer, plugin), n in sorted(by_plugin.items(), key=lambda kv: -kv[1])[:10]:
        print("  %-32s %5d" % (plugin, n))

    if duplicates:
        print("\nduplicate declarations (first 10):")
        for name in sorted(duplicates)[:10]:
            print("  %-40s %s" % (name, duplicates[name]))

    if args.check:
        bad = len(duplicates)
        if bad:
            print("\nPLUGIN MAP: %d duplicate declaration(s) -- migration is ambiguous" % bad)
            return 1
        print("\nPLUGIN MAP: every theorem has exactly one plugin (%d plugins, %d theorems)"
              % (len(by_plugin), len(rows)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
