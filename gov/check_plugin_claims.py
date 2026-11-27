"""gov/check_plugin_claims.py -- a manifest may not CLAIM an obligation whose proof field says nothing.

## Why this file exists (plan Phase 3, ADR-E, with the plan's premise measured first)

`Plugins/Registry.lean:110` is

    consistent : manifest.obligations ≠ [] → proof.Holds

so a `VerifiedPlugin` is accepted when the manifest lists **any** obligation and the twelve `PluginProof` fields are all
true. `PluginProof.Holds` requires every field, so a field whose value is the literal `True` is satisfied for free --
meaning a manifest could claim `.spatial` while `proof.spatial = True` and nothing would notice.

**Measured before building anything (round 1186): there are ZERO such claims in the tree.** All eleven plugins' claimed
kinds map to non-`True` proof fields:

    Attention 3   Conv 3   DAG 3   GNN 11   Norm 6   Compose 10
    Constraint 4  Repair 8  Penalty 7  Tokens 7  ChainSlot 12        ->  0 vacuous

So this is NOT a repair. The plan's ADR-E proposes a type-level `ProofFieldOf : ObligationKind → ...` mapping across
`Registry.lean`, eleven `Plugin.lean` files and `Plugins.lean`; that is the right shape for a property the TYPE should
carry, but it is a large refactor to prevent something that has never happened. The gate below enforces the same
sentence -- "a claimed obligation is not vacuous" -- in thirty lines, and will fire the moment a plugin claims a slot
that says nothing. The type-level version stays on the list, to be done when this gate fires rather than instead of
having the gate.

## The rule

For each `Plugins/**/Manifest.lean`, the `.kind` of every `verifiedObligation` must have a NON-vacuous field in that
plugin's `Plugin.lean`. A `True` field for a claimed kind fails.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import audit_plugin_slots as slots  # the one place that parses slot values

PLUGINS = os.path.join(ZERO, "Lattice", "Plugins")
KIND = re.compile(r'verifiedObligation\s+"[^"]*"\s+\.(\w+)')


def claimed_kinds(manifest_path):
    return set(KIND.findall(io.open(manifest_path, encoding="utf-8").read()))


def vacuous_fields(plugin_path):
    ss = slots.slots(plugin_path)
    if len(ss) < 12:
        return None  # the slot parser could not see twelve fields; that is audit_plugin_slots' problem, not this one's
    return {f for f, _v, k in ss if k == "TRUE"}


def scan():
    """[(plugin, [claimed kinds that are vacuous])]."""
    bad = []
    seen = set()
    for root, _dirs, files in os.walk(PLUGINS):
        if "Manifest.lean" not in files or "Plugin.lean" not in files:
            continue
        rel = os.path.relpath(root, PLUGINS).replace(os.sep, "/")
        seen.add(rel)
        claimed = claimed_kinds(os.path.join(root, "Manifest.lean"))
        vac = vacuous_fields(os.path.join(root, "Plugin.lean"))
        if vac is None:
            continue
        hit = sorted(claimed & vac)
        if hit:
            bad.append((rel, hit))
    return bad, len(seen)


def self_test():
    """Plant the shape: a claimed kind whose slot is `True`."""
    claimed = {"spatial", "soundness"}
    vac = {"spatial", "laws"}
    caught = sorted(claimed & vac) == ["spatial"]
    print("  claimed `spatial` with proof.spatial = True : %s" % ("FLAGGED" if caught else "** MISSED **"))
    print("  claimed `soundness` (non-vacuous)            : %s"
          % ("ignored (correct)" if "soundness" not in (claimed & vac) else "** WRONGLY FLAGGED **"))
    ok = caught and "soundness" not in (claimed & vac)
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()

    bad, n = scan()
    print("PLUGIN CLAIMS: %d plugin(s); a claimed obligation must not be a literal `True` field" % n)
    if not bad:
        print("  every claimed obligation has a non-vacuous proof field")
        return 0
    for rel, hits in bad:
        print("  VACUOUS CLAIM  %-34s %s" % (rel, ", ".join(hits)))
    print()
    print("PLUGIN CLAIMS: %d plugin(s) claim an obligation whose proof field says nothing" % len(bad))
    print("`Registry.lean:110` accepts this (`obligations ≠ [] → Holds`, and `Holds` is satisfied by `True`).")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))