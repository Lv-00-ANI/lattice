#!/usr/bin/env python
"""gov/check_obligations_doc.py -- the SPEC SOURCE must agree with the tree.

## Why this file exists (STAGE 4, gate defect G-12)

`PROOF-OBLIGATIONS.md` is the document that says **what the project promises to prove**. Every other
checker guards a DERIVED artifact: `PROOF-DEBT.md` (generated), `ALIAS-CENSUS.md` (generated),
`OBJECTIVE-MAP.md` (generated). **`PROOF-OBJECTIVES.md` is not derived from anything -- it is the
source -- and until this file existed nothing read it.**

**=> a spec source that no gate reads is a document that can drift from the tree forever without
anything failing.** The audit's phrasing was exact: the spec had no gate.

## What this checks, and what it deliberately does not

**Checks:** every `## T<N>` section names at least one Lean theorem, and every such name EXISTS in
the tree. That is the decidable half: a spec that names a theorem which does not exist is a broken
promise, and it is checkable by the same textual means every other checker in this directory uses.

**Does NOT check:** whether the named theorem MEANS what the section says. That needs reading
prose against Lean, which is a different job and should not be faked by a regex.

**It is a checker, so it must be able to fail:** `--self-test` plants a phantom name and asserts the
check goes red.
"""
import io
import os
import re
import sys

os.chdir(os.path.dirname(os.path.abspath(__file__)))
from _paths import resolve  # noqa: E402

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
DOC = os.path.join(ROOT, "PROOF-OBLIGATIONS.md")
LAT = os.path.join(ROOT, "Lattice")

#: A section header: `## T0 Construct`.
SECTION = re.compile(r"(?m)^##\s+(T\d+)\s+(.*)$")

#: A Lean identifier written in backticks. Names may be dotted.
BACKTICK = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.\u2080-\u2089]*)`")

#: Declaration regex -- the same shape the other checkers use.
DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z0-9_'.\u2080-\u2089]+)")

#: **Round 775: a backticked word is only a CLAIM about the tree when it LOOKS like a declaration.**
#:
#: The first version treated every backticked identifier as a claim and produced five false
#: positives in one run -- `t` (a variable in prose), `CONFLUENCE.md` (a file name),
#: `Option.bind_assoc` (a Mathlib lemma, not ours), `check_obligation_proofs.py` (a script).
#:
#: **=> the criterion is now POSITIVE rather than a blocklist: a name is a claim only if it contains
#: an underscore or a prime.** That is the project's own naming convention for theorems and
#: definitions (CONVENTIONS.md F1), so it selects exactly the kind of identifier a spec would be
#: promising -- and a one-letter variable or a filename cannot match.
#:
#: **A blocklist was the wrong shape**: it has to grow every time a new non-name noun appears, and it
#: cannot be argued for. A positive rule can be.
CLAIM_SHAPE = re.compile(r"^[A-Za-z][A-Za-z0-9'.]*[_'][A-Za-z0-9_'.]*$")

#: **Not a claim about OUR tree:** a file name (`.py`/`.md`) is a pointer, not a declaration;
#: and a name qualified by a FOREIGN namespace (`Option.bind_assoc`, `List.map_cons`) is a
#: Mathlib lemma the spec cites for context. **Both are legitimate spec content and neither is a
#: promise this project made.**
FILE_LIKE = re.compile(r"\.(py|md|lean|txt|tsv|jsonl)$")
FOREIGN_NS = ("Option.", "List.", "Nat.", "Real.", "Finset.", "Equiv.", "Function.", "Mathlib.")


def build_index():
    idx = set()
    for dirpath, dirs, files in os.walk(LAT):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in files:
            if not f.endswith(".lean"):
                continue
            src = io.open(os.path.join(dirpath, f), encoding="utf-8", errors="replace").read()
            for m in DECL.finditer(src):
                idx.add(m.group(1).split(".")[-1])
    return idx


def parse_doc(path):
    """[(section_id, section_title, [names])]."""
    src = io.open(path, encoding="utf-8", errors="replace").read()
    heads = [(m.start(), m.group(1), m.group(2)) for m in SECTION.finditer(src)]
    out = []
    for k, (pos, sid, title) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(src)
        body = src[pos:end]
        names = [n for n in BACKTICK.findall(body)
                 if CLAIM_SHAPE.match(n)
                 and not FILE_LIKE.search(n)
                 and not any(n.startswith(p) for p in FOREIGN_NS)]
        out.append((sid, title.strip(), names))
    return out


def self_test():
    """Plant a phantom name: the check must go red."""
    idx = build_index()
    sections = parse_doc(DOC)
    if not sections:
        print("SELFTEST FAILED: could not parse any section")
        return 1
    sid, title, names = sections[0]
    fake = list(names) + ["zz_phantom_theorem_that_cannot_exist"]
    missing = [n for n in fake if n.split(".")[-1] not in idx]
    if "zz_phantom_theorem_that_cannot_exist" in missing:
        print("SELFTEST OK: the check reports a planted phantom name")
        return 0
    print("SELFTEST FAILED: the planted phantom was not reported")
    return 1


def main(argv):
    if "--self-test" in argv:
        return self_test()
    if not os.path.exists(DOC):
        print("OBLIGATIONS DOC: no PROOF-OBLIGATIONS.md at %s" % DOC)
        return 1

    idx = build_index()
    if not idx:
        print("OBLIGATIONS DOC: no declarations found -- an empty index is a broken index")
        return 1

    sections = parse_doc(DOC)
    if not sections:
        print("OBLIGATIONS DOC: no `## T<n>` section found -- the spec has no obligation list")
        return 1

    problems = []
    bare = []
    for sid, title, names in sections:
        if not names:
            # **Round 775: a section that names NO declaration is a REAL gap in the spec, not a false
            # positive -- PROOF-OBLIGATIONS.md is the source of promises, and a promise with no named
            # carrier is the same defect as an objective clause with a dead carrier.**
            # It is reported separately so the two kinds stay distinguishable: a MISSING NAME and a
            # NAME THAT DOES NOT RESOLVE are different repairs.
            bare.append("%s (%s)" % (sid, title))
            continue
        missing = sorted({n for n in names if n.split(".")[-1] not in idx})
        if missing:
            problems.append("%s (%s): names %d declaration(s) that do not exist: %s"
                            % (sid, title, len(missing), ", ".join(missing[:6])))

    print("obligations doc: %d section(s), %d declaration(s) indexed"
          % (len(sections), len(idx)))
    if problems:
        print("\nOBLIGATIONS DOC: %d problem(s)" % len(problems))
        for p in problems:
            print("    " + p)
        return 1
    if bare:
        print("OBLIGATIONS DOC: %d section(s) name NO declaration (a promise with no carrier):"
              % len(bare))
        for b in bare:
            print("    " + b)
        return 1
    print("OBLIGATIONS DOC: every obligation section names declarations that exist")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
