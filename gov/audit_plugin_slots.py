#!/usr/bin/env python
"""gov/audit_plugin_slots.py -- `PluginProof`'s twelve slots: which are literal `True`, and which named Props are UNPROVED?

WHY THIS EXISTS

    `ProofSlotCensus.lean` records 87 of 132 slots as literal `True`. The obvious next move is "fill them".

    => but a slot is a `Prop`, and `PluginProof` gives no formal criterion for what belongs there. Filling one
       with an arbitrary true statement would be exactly the substitution the audit warned about: "if all 87
       become `na`, the gate goes green and nothing is proved; `na` is the new `True`".

    => so before filling anything, this file asks the question that HAS a mechanical answer:
       for every slot whose value is a NAMED proposition (not literal `True`), does a theorem proving that
       proposition exist in the tree?

WHAT IT MEASURES, per `Lattice/Plugins/**/Plugin.lean`

    * the twelve `PluginProof` field values, from the first literal in the file;
    * each slot classified as  TRUE (literal)  /  NAMED (identifiers)  /  COMPOSITE (conjunction);
    * for NAMED and COMPOSITE values, every identifier `<X>Prop` is looked up as a theorem `<x>Prop_holds`
      (the project's naming convention: the theorem is the lower-camel-cased prop name plus `_holds`).

    => what it CANNOT do: decide whether a named proposition is the RIGHT thing for that slot. That is a
       judgement, and this file says so instead of pretending a heuristic settles it.

WHAT `--check` ENFORCES

    * the vacuous (`True`) slot count must not GROW past `gov/plugin-slot-baseline.txt` (shrink-only);
    * every named Prop used by a slot must have a `_holds` theorem -- a slot naming a proposition nobody
      proved is a stronger form of the same defect.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LATTICE = os.path.join(REPO, "Lattice")
PLUGINS = os.path.join(LATTICE, "Plugins")
BASELINE = os.path.join(HERE, "plugin-slot-baseline.txt")
sys.path.insert(0, HERE)
from tools.sorry_axiom_census import strip_comments  # noqa: E402

FIELDS = ["soundness", "laws", "exactness", "approximation", "recovery", "spatial",
          "confluence", "equivariance", "idempotence", "invariants", "completeness", "refinement"]
FIELD_LINE = re.compile(r"^\s*(" + "|".join(FIELDS) + r")\s*:=\s*(.+?)\s*$", re.M)
PROP_IDENT = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*Prop)\b")
DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)?"
                  r"(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)


def declared_names():
    names = set()
    for root, _dirs, files in os.walk(LATTICE):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            src = strip_comments(io.open(p, encoding="utf-8", errors="replace").read())
            names.update(DECL.findall(src))
    return names


def holds_name(prop):
    """`NormVarianceLawsProp` -> `normVarianceLawsProp_holds` (the project's convention).

    ⚠ the convention is "lower-camel-case the prop name", and an ACRONYM prefix makes that ambiguous:
    `DAGConfluenceProp` could become `dAGConfluenceProp_holds` or `dagConfluenceProp_holds`. Round 995
    measured that the tree uses the second. So the lookup below is CASE-INSENSITIVE rather than guessing.
    """
    return prop[0].lower() + prop[1:] + "_holds"


def _fold(s):
    return s.lower()


def slots(path):
    """[(field, value, kind)] for the first PluginProof literal in the file."""
    src = strip_comments(io.open(path, encoding="utf-8", errors="replace").read())
    hits = FIELD_LINE.findall(src)
    out = []
    for field, value in hits:
        if len(out) >= 12:
            break
        if field != FIELDS[len(out)]:
            continue
        v = value.strip()
        if v == "True":
            out.append((field, v, "TRUE"))
        elif "∧" in v:
            out.append((field, v, "COMPOSITE"))
        else:
            out.append((field, v, "NAMED"))
    return out


def measure():
    names = declared_names()
    rows = []
    for root, _dirs, files in os.walk(PLUGINS):
        if "Plugin.lean" not in files:
            continue
        p = os.path.join(root, "Plugin.lean")
        rel = os.path.relpath(p, REPO).replace(os.sep, "/")
        ss = slots(p)
        if len(ss) < 12:
            continue
        vacuous = sum(1 for _f, _v, k in ss if k == "TRUE")
        unproved = []
        for field, value, kind in ss:
            if kind == "TRUE":
                continue
            for prop in PROP_IDENT.findall(value):
                want = holds_name(prop)
                if not any(_fold(n) == _fold(want) for n in names):
                    unproved.append((field, prop, holds_name(prop)))
        rows.append((rel, ss, vacuous, unproved))
    return rows


def baseline():
    if not os.path.isfile(BASELINE):
        return None
    for line in io.open(BASELINE, encoding="utf-8").read().split("\n"):
        if line.strip() and not line.startswith("#"):
            parts = line.split("\t")
            if len(parts) == 2 and parts[0] == "vacuous_total":
                return int(parts[1])
    return None


def main():
    rows = measure()
    total_vacuous = 0
    total_slots = 0
    problems = []
    print("  plugin                                          True  named  composite  unproved")
    print("  " + "-" * 82)
    for rel, ss, vacuous, unproved in rows:
        named = sum(1 for _f, _v, k in ss if k == "NAMED")
        comp = sum(1 for _f, _v, k in ss if k == "COMPOSITE")
        total_vacuous += vacuous
        total_slots += len(ss)
        print("  %-44s %4d %6d %10d %9d"
              % (rel.replace("Lattice/Plugins/", "").replace("/Plugin.lean", ""), vacuous, named, comp,
                 len(unproved)))
        for field, prop, want in unproved:
            problems.append("%s: slot `%s` names `%s` but no theorem `%s` exists" % (rel, field, prop, want))
    print("  %-44s %4d" % ("TOTAL", total_vacuous))
    print("  slots measured: %d" % total_slots)

    base = baseline()
    if base is not None:
        if total_vacuous > base:
            problems.append("vacuous slots %d > baseline %d" % (total_vacuous, base))
        else:
            print("  baseline: %d vacuous registered, %d now (%d drained)"
                  % (base, total_vacuous, base - total_vacuous))

    for p in problems:
        print("  PROBLEM %s" % p)
    if problems:
        print("PLUGIN SLOTS: %d problem(s)" % len(problems))
        return 1
    print("PLUGIN SLOTS: every named slot proposition is proved, and the vacuous count did not grow")
    return 0


def _self_test():
    ok = True
    if holds_name("NormVarianceLawsProp") != "normVarianceLawsProp_holds":
        print("  SELF-TEST FAIL: the _holds naming convention changed")
        ok = False

    body = "\n".join("%s := True" % f for f in FIELDS)
    tmp = os.path.join(HERE, ".plugin_slots_selftest.lean")
    io.open(tmp, "w", encoding="utf-8", newline="\n").write("def proof : PluginProof where\n  " + body.replace("\n", "\n  "))
    try:
        ss = slots(tmp)
        if len(ss) != 12 or sum(1 for _f, _v, k in ss if k == "TRUE") != 12:
            print("  SELF-TEST FAIL: twelve literal Trues were not read as twelve vacuous slots")
            ok = False
        body2 = "\n".join("  %s := %s" % (f, "SomeProp" if f == "recovery" else "True") for f in FIELDS)
        io.open(tmp, "w", encoding="utf-8", newline="\n").write("def proof : PluginProof where\n" + body2 + "\n")
        ss = slots(tmp)
        if not any(k == "NAMED" and v == "SomeProp" for _f, v, k in ss):
            print("  SELF-TEST FAIL: a named proposition was not classified NAMED")
            ok = False
    finally:
        if os.path.isfile(tmp):
            os.remove(tmp)

    if not any("Plugin.lean" in dirs for _r, _d, dirs in []):
        pass
    found = 0
    for root, _dirs, files in os.walk(PLUGINS):
        if "Plugin.lean" in files:
            found += 1
    if found == 0:
        print("  SELF-TEST FAIL: no Plugin.lean exists, so this check cannot fire")
        ok = False

    print("PLUGIN SLOTS SELF-TEST: %s" % ("convention, both classifications and the tree all behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(_self_test())
    sys.exit(main())
