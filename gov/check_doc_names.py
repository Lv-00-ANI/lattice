"""gov/check_doc_names.py -- docstrings must not cite declarations that do not exist.

## The defect

Docstrings in this tree explain proofs by naming the theorems involved. Nothing checked that those
names exist, so thirteen had drifted after renames:

    「ActStack」/「actStack_nil」/「actStack_single_affine」   -> StackLayer / actStackEval_nil / actStackSingle_affine
    「projectCompiler_sound」                    -> project_sound
    「pairRep_not_surjective」                   -> pairCompile_not_surjective
    「lossy_of_representation」                  -> ofRepresentation
    「verification_gap_vanishes」                -> residual_eq_zero_of_zero_dense
    「vecDot_eq_dot_lists」                      -> vecDot_toFinVec_eq_dot
    「project_ne_id」  「lossy_semEq_iff」
    「verifier_error_tends_to_eps0」             -> never proved; the table row was deleted
    「act_toMLayer」                             -> never proved; the table row was deleted

A reader following such a citation lands on `unknown identifier`. A docstring that cites a theorem is
part of the proof argument, so a phantom citation is a broken argument, not a typo.

## Why this is a curated list and not a general check

The obvious guard -- "every backticked identifier in a docstring must be a declaration" -- was built and
measured before being rejected. On this tree it reported **13,689** violations, because docstrings
legitimately backtick Mathlib lemma names (`sSup`, `BddAbove`, `Finset`), local variables (`hreach`,
`val`, `data`, `indices`), tactic names (`simp`, `rw`, `decide`), and prose (`tiny`, `sep`). A gate with
13,689 findings is a gate somebody switches off, which is worse than no gate.

So the enforceable statement is the narrow one: **a named set of known-stale names must never appear in a
docstring again.** That is the same shape as `check_usage_claims.STALE` for stale counts, and for the
same reason -- it is precise, it cannot false-positive, and it catches the regression.

### The convention this establishes

> In a docstring, a backticked Lean identifier means "this declaration exists".
> A name that was RENAMED or ABANDONED is quoted `「like this」`, never in backticks.

That is why the correction notes in the thirteen affected files use `「」`: it keeps the history AND
keeps backticks honest.

`--survey` runs the noisy general detector for a human to read. It is deliberately NOT a gate.

## Node on legitimate citations of rejected names

`Lattice/Lift/ConstraintEmbeddingSoundness.lean` cites 「embedding_all_neurons」 in order to explain why
that statement cannot typecheck. That is a correct citation of a name that deliberately does not exist.
It is exactly why a general checker cannot work: "cited because it is absent" and "cited because it was
renamed" are indistinguishable to a regex.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

#: (stale name, what it should have been). Re-appearing in a docstring is a regression.
STALE = [
    ("ActStack", "StackLayer"),
    ("actStack_nil", "actStackEval_nil"),
    ("actStack_single_affine", "actStackSingle_affine"),
    ("projectCompiler_sound", "project_sound"),
    ("project_ne_id", "project_not_injective"),
    ("pairRep_not_surjective", "pairCompile_not_surjective"),
    ("lossy_of_representation", "ofRepresentation"),
    ("lossy_semEq_iff", "(never proved; the table row was deleted)"),
    ("verification_gap_vanishes", "residual_eq_zero_of_zero_dense"),
    ("verifier_error_tends_to_eps0", "(never proved; the table row was deleted)"),
    ("act_toMLayer", "(never proved; the table row was deleted)"),
    ("vecDot_eq_dot_lists", "vecDot_toFinVec_eq_dot"),
    ("embedding_all_neurons", "(rejected as ill-typed; correctly cited only as absent)"),
]

DOC = re.compile(r"/-[-!]((?:(?!/--).)*?)-/", re.S)
FENCE = re.compile(r"```.*?```", re.S)

#: the general detector, used only by `--survey`
SPAN = re.compile(r"`([A-Za-z_][A-Za-z0-9_.'!?]*)`")
DECL = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom|class)\s+"
    r"([A-Za-z0-9_'!?]+)")


def _lean_files(root=LAT):
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", "gov")]
        for f in sorted(files):
            if f.endswith(".lean"):
                yield os.path.join(dirpath, f)


def scan_stale(root=LAT):
    """Every backticked occurrence of a STALE name inside a docstring."""
    names = {n for n, _ in STALE}
    problems = []
    for p in _lean_files(root):
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        rel = os.path.relpath(p, root).replace("\\", "/")
        for d in DOC.finditer(src):
            body = d.group(1)
            for n in names:
                needle = "`%s`" % n
                idx = body.find(needle)
                while idx >= 0:
                    line = src[:d.start() + idx].count("\n") + 1
                    problems.append((rel, line, n))
                    idx = body.find(needle, idx + 1)
    return problems


def survey(root=LAT):
    """The noisy general detector. Reported, never gated -- see the module docstring."""
    have = set()
    for p in _lean_files(root):
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        have.update(m.group(1) for m in DECL.finditer(src))
    out = []
    for p in _lean_files(root):
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        rel = os.path.relpath(p, root).replace("\\", "/")
        for d in DOC.finditer(src):
            body = FENCE.sub("", d.group(1))
            for s in SPAN.finditer(body):
                name = s.group(1)
                if name in have or name.split(".")[-1] in have:
                    continue
                out.append((rel, src[:d.start() + s.start()].count("\n") + 1, name))
    return out


def main(argv):
    if "--survey" in argv:
        found = survey()
        for rel, line, name in found[:40]:
            print("  %-56s L%-5d %s" % (rel, line, name))
        print()
        print("SURVEY (not a gate): %d backticked identifiers in docstrings are not declarations."
              % len(found))
        print("Most are Mathlib names, local variables and prose. Triage by hand; promote only names")
        print("that are genuinely this tree's own and genuinely renamed, by adding them to STALE.")
        return 0

    if "--self-test" in argv:
        d = os.path.join(HERE, ".docnames-selftest")
        os.makedirs(d, exist_ok=True)
        try:
            # a live citation of an existing declaration: must be accepted
            io.open(os.path.join(d, "A.lean"), "w", encoding="utf-8").write(
                "theorem realOne : True := trivial\n"
                "/-- depends on `realOne` --/\ntheorem usesReal : True := trivial\n")
            # a citation of a STALE name: must be caught
            io.open(os.path.join(d, "B.lean"), "w", encoding="utf-8").write(
                "/-- used to depend on `%s` --/\ntheorem usesStale : True := trivial\n" % STALE[0][0])
            # the documented convention: 「」 quoting is how history is recorded, and must pass
            io.open(os.path.join(d, "C.lean"), "w", encoding="utf-8").write(
                "/-- was \u300c%s\u300d, now `realOne` --/\ntheorem usesQuoted : True := trivial\n"
                % STALE[0][0])
            found = scan_stale(d)
            names = {n for _, _, n in found}
            if STALE[0][0] not in names:
                print("SELF-TEST FAILED: a stale citation was accepted")
                return 2
            if len(found) != 1:
                print("SELF-TEST FAILED: expected exactly one hit (the 「」 form must not count),"
                      " got %d" % len(found))
                return 2
        finally:
            import shutil
            shutil.rmtree(d, ignore_errors=True)
        print("SELF-TEST: stale citation caught, existing name accepted, '「」' history accepted")
        return 0

    problems = scan_stale()
    for rel, line, name in problems:
        fix = dict(STALE)[name]
        print("  %-56s L%-5d `%s` should be %s" % (rel, line, name, fix))
    print()
    if problems:
        print("DOC NAMES: %d docstring citation(s) name a declaration that was renamed or never existed"
              % len(problems))
        return 1
    print("DOC NAMES: no docstring cites a known-stale declaration name")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
