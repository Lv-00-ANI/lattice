"""gov/check_objective_coverage.py -- guard the claim "every objective clause has a carrier".

## Why this checker exists

Rounds 73, 81, 82 and 84 each asserted something about how much of the objective was covered, and
each assertion was refuted by a fresh enumeration:

    73  "geometric repair coverage complete"     -> 5 of 12 constructors, not 5 of 5
    81  "parallel and ratioDivision are the two" -> ratioDivision does not exist
    82  "no decision-free work remains"          -> the polynomial group had only existence
    84  "28 camelCase theorems, 4 engine imports" -> 4 and 0, after applying the documented rules

Every one of those was a MEASUREMENT error, not a work error. The judgements were made by writing a
throwaway script each time, and each throwaway script had its own regex bug.

So the enumeration stops being throwaway. This checker fixes, once, the precise criterion for each
objective clause and fails on drift:

  A. each clause of the objective text must have at least one named carrier in the tree;
  B. the naming census must use the DOCUMENTED criterion (last dot-segment, not the full name);
  C. external engine/vendor imports must stay at zero -- imports of our OWN modules whose names
     happen to contain "Tensor" are not violations, and mixing the two up was round 84's error.

## The criteria are written down, which is the point

A criterion that lives only in a script's regex is re-invented (and re-broken) every time. Here the
rules are in prose next to the code that applies them, so the next reader can check the rule rather
than trust the number.

## It must be able to fail

`--self-test` plants a violation for each rule and asserts the checker reports it.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

# ---------------------------------------------------------------- corpus

def _corpus():
    out = {}
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            out[rel] = io.open(p, "rb").read().decode("utf-8", errors="replace")
    return out

# ---------------------------------------------------------------- rule A

#: Objective clause -> carrier names that must exist. A clause passes if ANY of its names is found.
#: The names are deliberately concrete declarations, not topic words: round 84 showed that topic
#: words ("loss", "token") are present everywhere and prove nothing.
CLAUSES = {
    "1.1 data -> token": ["tokenize_detok", "CharToken"],
    "1.2 token -> symbol": ["SymToken", "decodePayload"],
    "1.3 symbol -> weight": ["compileToLayer", "compileToLayerN"],
    "1.4 weight -> symbol": ["extract"],
    "2.1 forward: constraint loss": ["PenaltyEmbedding", "penaltyToLoss"],
    "2.2 forward: data synthesis": ["synth_coverage"],
    "2.3 forward: structured init": ["weightLadderN", "compile_sound_n"],
    "3.1 inverse: extraction": ["ApproxRepresentation", "ratRepresentation"],
    "3.2 inverse: verification": ["EpsSat", "geo_sampled_bound"],
    "3.3 inverse: repair": ["sqDistFix", "parallelFix", "midpointFix"],
    "3.4 inverse: re-injection": ["reinject_loss_eq_zero", "partial_reinject_bound"],
    "4 loop": ["converges_within", "bidirRepair"],
    "5 symbolic engine": ["evalPts", "derivation_sound"],
    "8 Lean guarantee": ["sound_not_exact", "decodePayload_encodeForm"],
}


def check_clauses(corpus):
    """Return [(clause, missing_list)] for clauses with NO carrier."""
    blob = "\n".join(corpus.values())
    bad = []
    for clause, names in CLAUSES.items():
        if not any(re.search(r"\b%s\b" % re.escape(n), blob) for n in names):
            bad.append((clause, names))
    return bad

# ---------------------------------------------------------------- rule B

THM = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                 r"noncomputable[ \t]+)*(?:theorem|lemma)[ \t]+([A-Za-z0-9_'!?.]+)")

#: camelCase theorems that are EXEMPT and why (CONVENTIONS §7.6). Kept as data so that adding one
#: requires a reason, not just a looser regex.
CAMEL_EXEMPT = {
    "IsStrictLocalMin.toIsLocalMin": "Mathlib-named predicate: `IsStrictLocalMin` is the Mathlib name",
    "IsStrictLocalMax.toIsLocalMax": "same",
    "IsClosedExtent.iInter": "`iInter` is the Mathlib name for an indexed intersection",
    "IsClosedExtent.sInf": "`sInf` is the Mathlib name for an infimum",
}

PRIME_EXEMPT = {
    "while'_true_id": "the object language's `while'` constructor carries the prime",
    "while'_true_stuck": "same",
    "GeneralizationBound.sound'": "namespace-prefixed variant of `sound`",
}


def _last_segment(full):
    """CONVENTIONS §7.5: judge the LAST dot-segment. Round 84 judged the FULL name and reported
    28 camelCase theorems where the documented rule gives 4."""
    return full.split(".")[-1]


def name_violations(corpus):
    """Return (camel, primes) beyond the exemption lists."""
    camel, primes = [], []
    for rel, src in corpus.items():
        for m in THM.finditer(src):
            full = m.group(1)
            last = _last_segment(full)
            if "_" not in last and re.search(r"[a-z][A-Z]", last):
                if full not in CAMEL_EXEMPT:
                    camel.append((rel, full))
            if "'" in full and full not in PRIME_EXEMPT:
                primes.append((rel, full))
    return camel, primes

# ---------------------------------------------------------------- rule D

#: The objective says the symbolic model runs DIRECTLY on the symbolic engine, with no intermediate
#: layer. Mechanically that means the symbolic satisfaction relation has exactly ONE definition --
#: a second one in another layer would BE the intermediate layer.
#:
#: Round 99 measured this: `GeoConstraint.Holds` is defined once, in Geo/Constraint.lean. The many
#: `eval*` in Lib/Compiler are the compiler's own semantics for its own object language, not a
#: re-encoding of the symbolic constraints, so they are not violations -- the distinction is written
#: here so it is not re-litigated.
CORPUS_ITEMS = []

SATISFACTION_OWNERS = {
    "GeoConstraint.Holds": "Geo/Constraint.lean",
}


def check_no_intermediate_layer():
    """Every canonical symbolic-semantics definition must exist in exactly one layer."""
    bad = []
    for name, expected_file in SATISFACTION_OWNERS.items():
        part = name.split(".")[0]
        owners = []
        for rel, src in CORPUS_ITEMS:
            if re.search(r"(?m)^[ \t]*(?:noncomputable[ \t]+)?def[ \t]+%s\b"
                         % re.escape(name.split(".")[-1]), src):
                # a definition of the same shape inside a namespace of the same name
                if re.search(r"(?m)^namespace[ \t]+%s\b" % re.escape(part), src):
                    owners.append(rel)
        if expected_file not in owners:
            bad.append((name, expected_file, owners))
        if len(owners) > 1:
            bad.append((name, expected_file, owners))
    return bad


# ---------------------------------------------------------------- rule C

VENDORS = ["torch", "pytorch", "tensorflow", "jax", "cuda", "onnx", "huggingface",
           "transformers", "openai", "anthropic", "vllm", "deepspeed"]


def external_vendor_imports(corpus):
    """Imports of FOREIGN vendor packages.

    Round 84 counted `import Lattice.Lib.Architectures.RealTensorNorm` as an "engine import". It is
    our own module; its NAME contains "Tensor". The objective forbids depending on an external
    framework, not on having a theorem about tensors. The `startswith("Lattice.")` test is what
    separates the two, and it is written here so it is not re-derived wrongly.
    """
    imports = set()
    for src in corpus.values():
        imports |= set(re.findall(r"(?m)^import (\S+)", src))
    bad = []
    for i in sorted(imports):
        if i.startswith("Lattice."):
            continue
        if any(v in i.lower() for v in VENDORS):
            bad.append(i)
    return bad

# ---------------------------------------------------------------- reporting

def report(corpus):
    global CORPUS_ITEMS
    CORPUS_ITEMS = list(corpus.items())
    ok = True

    bad = check_clauses(corpus)
    if bad:
        ok = False
        print("OBJECTIVE COVERAGE: %d clause(s) without a carrier" % len(bad))
        for clause, names in bad:
            print("  %-34s looked for %s" % (clause, ", ".join(names)))
    else:
        print("A  every objective clause has a named carrier          (%d clauses)"
              % len(CLAUSES))

    camel, primes = name_violations(corpus)
    if camel or primes:
        ok = False
        print("B  naming: %d camelCase, %d prime, beyond the exemption lists" % (len(camel), len(primes)))
        for rel, n in camel + primes:
            print("     %-46s %s" % (rel, n))
    else:
        print("B  naming: 0 violations beyond exemptions              "
              "(%d camel exempt, %d prime exempt)" % (len(CAMEL_EXEMPT), len(PRIME_EXEMPT)))

    inter = check_no_intermediate_layer()
    if inter:
        ok = False
        print("D  symbolic semantics defined in more than one place:")
        for name, exp, owners in inter:
            print("     %s expected only in %s, found in %s" % (name, exp, owners))
    else:
        print("D  symbolic semantics: each canonical relation defined exactly once "
              "(%d checked)" % len(SATISFACTION_OWNERS))

    ext = external_vendor_imports(corpus)
    if ext:
        ok = False
        print("C  vendor imports: %d" % len(ext))
        for i in ext:
            print("     %s" % i)
    else:
        print("C  vendor/framework imports: 0                          (own Lattice.* allowed)")

    return 0 if ok else 1

# ---------------------------------------------------------------- self test

def self_test():
    """Plant one violation per rule and assert it is caught."""
    corpus = _corpus()
    failures = []

    # A: an impossible clause name must be reported
    fake = dict(CLAUSES)
    fake["ZZ self-test"] = ["thisDeclarationDoesNotExistAnywhere"]
    saved = dict(CLAUSES)
    CLAUSES.clear()
    CLAUSES.update(fake)
    try:
        if not check_clauses(corpus):
            failures.append("rule A did not catch a missing carrier")
    finally:
        CLAUSES.clear()
        CLAUSES.update(saved)

    # B: plant a camelCase theorem
    planted = dict(corpus)
    planted["ZZ_planted.lean"] = "theorem badlyNamedTheorem : True := trivial\n"
    camel, _ = name_violations(planted)
    if not any(n == "badlyNamedTheorem" for _, n in camel):
        failures.append("rule B did not catch a planted camelCase theorem")

    # C: plant a vendor import
    planted2 = dict(corpus)
    planted2["ZZ_planted2.lean"] = "import TorchLean.Core\n"
    if not external_vendor_imports(planted2):
        failures.append("rule C did not catch a planted vendor import")

    # D: plant a SECOND definition of the symbolic relation, which would be an intermediate layer
    global CORPUS_ITEMS
    saved_items = CORPUS_ITEMS
    planted3 = dict(corpus)
    planted3["ZZ_planted3.lean"] = (
        "namespace GeoConstraint\nnoncomputable def Holds : Nat -> Prop := fun _ => True\nend GeoConstraint\n")
    CORPUS_ITEMS = list(planted3.items())
    try:
        if not check_no_intermediate_layer():
            failures.append("rule D did not catch a planted second definition")
    finally:
        CORPUS_ITEMS = saved_items

    if failures:
        for f in failures:
            print("SELF-TEST FAILED: %s" % f)
        return 2
    print("SELF-TEST: all four rules can fail")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(report(_corpus()))
