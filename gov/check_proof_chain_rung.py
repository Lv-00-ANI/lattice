"""Check that PROOF-CHAIN-RUNG.md still describes the tree it claims to describe.

The document's value is that its statements are checkable. That only holds if something
checks them: a manually maintained document about proof structure is exactly the kind of
artifact that silently drifts, and a drifted one is worse than none, because it is read as
authoritative.

Checks (all deterministic, no Lean build needed):
  1. every theorem/def the document names exists in the tree;
  2. the Ladder instance count it asserts (zero) is still zero;
  3. `geoCompiler` still has `encode := id` -- the claim that makes its `sound` field
     a definitional equality rather than an argument.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NEW = os.path.abspath(os.path.join(HERE, ".."))
DOC = os.path.join(NEW, "PROOF-CHAIN-RUNG.md")
LAT = os.path.join(NEW, "Lattice")


def decl_index():
    """name -> file, for every top-level declaration in the kernel."""
    idx = {}
    pat = re.compile(r"(?m)^\s*(?:(?:noncomputable|private|protected)\s+)*"
                     r"(theorem|lemma|def|structure|abbrev)\s+([A-Za-z0-9_.']+)")
    for root, _, files in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            t = io.open(p, "rb").read().decode("utf-8", errors="replace")
            for m in pat.finditer(t):
                idx.setdefault(m.group(2).split(".")[-1], os.path.relpath(p, NEW))
            # Structure fields count as named entities: the document cites `satW`,
            # `l2l3_sound`, `encode` as the obligations a rung carries, and none of those
            # is a top-level declaration. A field is `name : Type` at the start of a line.
            for m in re.finditer(r"(?m)^  ([a-zA-Z][A-Za-z0-9_']*) *:", t):
                idx.setdefault(m.group(1), os.path.relpath(p, NEW))
    return idx


def main():
    if not os.path.exists(DOC):
        print("PROOF-CHAIN-RUNG.md is missing")
        return 1
    doc = io.open(DOC, "rb").read().decode("utf-8", errors="replace")
    idx = decl_index()

    # 0. slot ids are cited in the document as `geo.loop.convergence_is_single_step`;
    #    they live in Slots.lean as string literals, not as declarations, so seed the
    #    index with every slot id on its own terms.
    slots_path = os.path.join(LAT, "Slots.lean")
    if os.path.exists(slots_path):
        stext = io.open(slots_path, "rb").read().decode("utf-8", errors="replace")
        for m in re.finditer(r'name := "([^"]+)"', stext):
            idx.setdefault(m.group(1), "Lattice/Slots.lean")
            idx.setdefault(m.group(1).split(".")[-1], "Lattice/Slots.lean")

    # 1. names cited in backticks that look like Lean identifiers
    cited = set()
    for span in re.findall(r"`([^`\n]+)`", doc):
        for m in re.finditer(r"[A-Za-z][A-Za-z0-9_'.]*", span):
            name = m.group(0).split(".")[-1].rstrip("'")
            if len(name) < 4:
                continue
            cited.add(name)

    known_missing = [n for n in sorted(cited) if n not in idx]

    # Backticked tokens that are prose, not Lean names. This list is deliberately explicit:
    # a name that SHOULD resolve but is missing will now be reported, so a bogus identifier
    # cannot hide behind a spelling heuristic.
    NOT_A_NAME = {
        "lakefile", "lean", "lake", "lakefile.toml", "lean-toolchain", "gov", "pipeline",
        "PROOF-CHAIN.md", "PROOF-CHAIN-GEO.md", "PROOF-CHAIN-RUNG.md", "CONVENTIONS.md",
        "README.md", "ROADMAP-v3.md", "Slots.lean", "p13_loadbearing.py",
        "p13_loadbearing2.py", "galois", "galois-connected", "converges", "unused",
        "Ring", "true", "false", "where", "exit", "ok", "tok", "sym", "data", "loss",
        "json", "md", "ps1", "py", "pycache",
        # Lean keywords / prose fragments that appear inside backticked spans.
        "else", "then", "variable", "section", "namespace", "private", "protected",
        "noncomputable", "def", "theorem", "lemma", "structure", "abbrev", "instance",
        "where", "exit", "true", "false", "import", "open", "end", "intro", "unfold",
        "ring", "simp", "rw", "exact", "apply", "have", "show", "from", "with",
        # prose words used as qualifiers
        "representable", "satisfied", "weakened", "hdec", "linear", "quadratic",
        # Mathlib / Lean type names and path fragments.
        "List", "Option", "Nat", "Real", "Int", "Functor", "Function", "Set", "Fin",
        "CharToken", "Char", "Data", "Tok", "Sym", "Lattice", "Lift", "Core", "Geo",
        "Slots", "Lib", "Ladder", "Compiler", "Representation", "Tokenizer",

        "PROOF", "agent", "CHAIN", "RUNG", "md", "toml", "lean", "lakefile",
        # partial identifiers written with a trailing underscore on purpose
        "compileProgram_", "tokenize_",

        "Pipeline", "none", "progress'",  # module segment; Option.none; the pre-rename name
        # the document cites on purpose, to record that the rename happened
    }
    suspicious = [n for n in known_missing if n not in NOT_A_NAME]
    failures = []

    print("cited identifiers: %d   unresolved: %d" % (len(cited), len(known_missing)))
    for n in suspicious[:20]:
        print("  UNRESOLVED: %s" % n)
        failures.append(n)

    # 2. Ladder instance count
    inst = []
    for root, _, files in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in files:
            if not f.endswith(".lean"):
                continue
            t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
            for m in re.finditer(r"(?m)^\s*(?:noncomputable\s+)?(?:def|instance|abbrev)\s+"
                                 r"([A-Za-z0-9_.']+)[^\n]*?:\s*(?:Lattice\.Lift\.)?Ladder\b"
                                 r"[^\n]*\bwhere\b", t):
                inst.append(m.group(1))
    zero_claimed = "**0**" in doc or "实例数为 0" in doc or "**0 个**" in doc
    print("Ladder instances: %d   (document claims zero: %s)" % (len(inst), zero_claimed))
    if zero_claimed and inst:
        print("  DRIFT: the document says zero, the tree has %s" % inst)
        failures.append("Ladder instance count")

    # 3. geoCompiler still definitional
    gc_path = os.path.join(LAT, "Geo", "Compile.lean")
    if os.path.exists(gc_path):
        gc = io.open(gc_path, "rb").read().decode("utf-8", errors="replace")
        has_id = "encode := id" in gc
        print("geoCompiler has `encode := id`: %s" % has_id)
        if not has_id:
            print("  DRIFT: the document's 'definitional equality' claim no longer holds")
            failures.append("geoCompiler encode")

    print("=" * 60)
    if failures:
        print("PROOF-CHAIN-RUNG: %d DRIFT(S)" % len(failures))
        return 1
    print("PROOF-CHAIN-RUNG: consistent with the tree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
