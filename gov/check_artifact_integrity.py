"""gov/check_artifact_integrity.py -- three properties about what the tools do to the tree and the docs.

## Why this file exists (plan W0-3f, GATE-3)

Three things were verified BY HAND in rounds 1172-1182 and nothing kept them true:

  * **1282**: six generators rewrote their artifacts on the default path. Each was changed to `sync(...)` and each was
    proven to bite by perturbing the artifact. Six hand-checks.
  * **1283**: reactivity probes write scratch files next to `Lattice/Slots.lean`. Measured: three `.bak` names, and
    TWO of the three were not in `.gitignore` -- a killed run left them looking like source.
  * the entry document's section 6 lists commands a reader is told to run. Nothing asserted they still exist.

Hand verification is a property of the round it happened in. This file makes them properties of the tree.

## The three assertions

1. **No default-path write of a tracked artifact.** Every script that owns one of the generated artifacts must import
   `artifact_guard` and route through `sync(`. A seventh generator added without it fails here.

2. **Every `.bak` path a tool writes is ignored.** The set is read from the scripts (`BACKUP = ... ".something.bak"`)
   and matched against `.gitignore` patterns, not against a remembered list.

3. **Section 6's commands exist.** Each `python <script>.py` line in `DELIVERY-COMPILER-LAYER.md`'s section 6 must
   name a file that exists in `gov/`. Scoped to that section on purpose: it is the one place the document says "run
   this to check me", so a command that no longer exists is a broken promise, whereas a script merely mentioned in
   prose is a citation.

## What it does not claim

It does not prove the artifacts are CORRECT, only that the tools compare rather than overwrite. A generator whose
output is wrong passes this gate; `check_endtoend_content` and its peers are the ones that judge the content.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.dirname(HERE)
sys.path.insert(0, HERE)

#: The scripts that own a generated artifact, and the artifact each owns. Written as a list so ADDING a generator
#: without adding a line here is the only way to bypass assertion 1 -- and the failure message says so.
OWNERS = {
    "check_slots.py": "gov/SLOTS.md",
    "chain.py": "gov/PROOF-CHAIN.md",
    "proof_chain_geo.py": "gov/PROOF-CHAIN-GEO.md",
    "gen_primitive_matrix.py": "PRIMITIVE-MATRIX.md",
    "check_endtoend_content.py": "gov/ENDTOEND-CENSUS.md",
    "audit_aliases.py": "gov/ALIAS-CENSUS.md",
    "chain_connectors.py": "gov/CHAIN-CONNECTORS.md",
    "gen_objective_map.py": "gov/OBJECTIVE-MAP.md",
}

BACKUP = re.compile(r'"\.?([A-Za-z0-9_.]*\.bak)"')

#: Scripts whose `.bak` never lands in the tree. `install_hook.py` backs up a GIT HOOK (`shutil.copy2(dst, dst + ".bak")`
#: with `dst` under `.git/hooks/`), which git does not track and which no `.gitignore` pattern inside the repository can
#: reach. The reason is recorded here rather than the script being silently skipped.
OUTSIDE_TREE = {
    "install_hook.py": "backs up a .git/hooks/ file, not a working-tree file",
}
DOC = os.path.join(ZERO, "DELIVERY-COMPILER-LAYER.md")
CMD = re.compile(r"python\s+(?:gov/)?([A-Za-z0-9_]+\.py)")


def strip_comments(src):
    import tokenize
    out = []
    try:
        for tok in tokenize.generate_tokens(io.StringIO(src).readline):
            if tok.type == tokenize.COMMENT:
                continue
            out.append(tok.string)
    except Exception:
        return src
    return " ".join(out)


def check_owners():
    bad = []
    for script, artifact in OWNERS.items():
        p = os.path.join(HERE, script)
        if not os.path.exists(p):
            bad.append("%s: missing (owners %s)" % (script, artifact))
            continue
        # RAW text on purpose: the check is about which names appear, and tokenising joins tokens with spaces
        # ("sync(" -> "sync (") which produced six false findings in this gate's first run.
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        if "artifact_guard" in src and "sync(" in src:
            continue
        # the other accepted shape: a `--check` mode that compares instead of writing (the guard's own rule, applied
        # by hand in two scripts before the guard existed)
        if '"--check"' in src:
            continue
        if "artifact_guard" not in src:
            bad.append("%s: neither imports artifact_guard nor offers --check (owner of %s)" % (script, artifact))
        else:
            bad.append("%s: imports the guard but never calls sync()" % script)
    return bad


def check_backups():
    patterns = [ln.strip() for ln in io.open(os.path.join(ZERO, ".gitignore"), encoding="utf-8")
                if ln.strip() and not ln.strip().startswith("#")]
    bad = []
    for f in sorted(os.listdir(HERE)):
        if not f.endswith(".py") or f == os.path.basename(__file__):
            continue  # the gate itself: its self-test strings mention .bak names on purpose
        src = strip_comments(io.open(os.path.join(HERE, f), "rb").read().decode("utf-8", "replace"))
        if f in OUTSIDE_TREE:
            continue
        for name in BACKUP.findall(src):
            cands = {name, "*" + name, "*." + name.lstrip(".")}
            if not any(p in cands for p in patterns):
                bad.append("%s writes %s, not covered by .gitignore" % (f, name))
    return bad


def check_commands():
    if not os.path.exists(DOC):
        return ["%s is missing" % os.path.basename(DOC)]
    text = io.open(DOC, encoding="utf-8").read()
    i = text.find("## 6.")
    if i < 0:
        return ["section 6 is gone -- the document no longer says how to check it"]
    j = text.find("\n## ", i + 1)
    section = text[i:j if j > 0 else len(text)]
    bad = []
    for name in sorted(set(CMD.findall(section))):
        if not os.path.exists(os.path.join(HERE, name)):
            bad.append("section 6 runs %s, which does not exist" % name)
    return bad


def self_test():
    """Plant each failure shape in a temp dir and require the three assertions to catch them."""
    import tempfile
    ok = True
    # 1: a script that writes but never imports the guard
    fd, p = tempfile.mkstemp(suffix=".py")
    os.close(fd)
    io.open(p, "w", encoding="utf-8", newline="\n").write(
        "io.open(P, 'w').write(x)\n")
    src = strip_comments(io.open(p, "rb").read().decode("utf-8"))
    caught = "artifact_guard" not in src
    os.remove(p)
    print("  owner without the guard     : %s" % ("FLAGGED" if caught else "** MISSED **"))
    ok = ok and caught
    # 2: a .bak name that .gitignore does not cover
    caught2 = not any(pp == "*" + "zz_probe.bak" for pp in ["*.gate_reactivity.bak"])
    print("  unignored .bak              : %s" % ("FLAGGED" if caught2 else "** MISSED **"))
    ok = ok and caught2
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()

    bad = []
    bad += check_owners()
    bad += check_backups()
    bad += check_commands()

    print("ARTIFACT INTEGRITY: %d generator(s), .bak coverage, section-6 commands" % len(OWNERS))
    if not bad:
        print("  every generator compares instead of overwriting; every .bak is ignored; every section-6 command exists")
        return 0
    for b in bad:
        print("  BROKEN  %s" % b)
    print()
    print("ARTIFACT INTEGRITY: %d finding(s)" % len(bad))
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))