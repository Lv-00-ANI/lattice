#!/usr/bin/env python
"""gov/check_plugin_yml.py -- the plugin capability index must agree with the Lean manifests.

WHY THIS EXISTS

    `PLUGIN-SYSTEM.md` specifies a `plugin.yml` capability index for every plugin. Until round 982 the
    repository had ZERO of them, so the specification's three stated purposes -- readable by a person,
    readable by an orchestrator, checkable by `run_cmd` -- had no artefact at all.

    Writing eleven YAML files would be worthless on its own: two descriptions of the same 74 obligations
    drift apart unless something compares them. This check IS that comparison.

WHAT IT ASSERTS, per plugin directory that has a `Manifest.lean` with obligations

    1. `id`            == the Lean manifest's `name` ("Compose", "Core.Repair", ...)
    2. `module`        == `Lattice.<path from Lattice/ to the Manifest.lean, dots for slashes>`
    3. `layer`         == the directory directly under `Lattice/Plugins/`
    4. `obligations`   == the Lean manifest's obligation list, SAME LENGTH, SAME ORDER, and for each entry
                          the same name, kind (Lean writes `.kind`, the YAML writes `kind`), theorem and file
    5. every `theorem` is DECLARED IN the `file` it names -- stronger than `check_obligation_proofs.py`,
       which only requires the name to exist somewhere under `Lattice/`
    6. every `file` exists on disk

    The comparison in (4) is what makes the pair worth having: the YAML is not generated on each run, it is
    committed, so a change to the Lean manifest WITHOUT a matching YAML edit fails here.

WHAT IT DOES NOT DO

    It does not parse YAML generally. It reads exactly the shape it writes: `id:`, `module:`, `layer:`,
    `obligations:` and then `- name:` / `kind:` / `theorem:` / `file:` at fixed indentation. A plugin.yml
    written in any other style is reported as unparseable rather than guessed at.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LATTICE = os.path.join(REPO, "Lattice")
PLUGINS = os.path.join(LATTICE, "Plugins")

VERIFIED = re.compile(r'verifiedObligation\s+"([^"]*)"\s*\.(\w+)\s*"([^"]*)"\s*"([^"]*)"', re.S)
BLOCKS = re.compile(r"obligations\s*:=\s*\[(.*?)\]", re.S)
MNAME = re.compile(r'name\s*:=\s*"([^"]+)"')
DECL = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)?"
                  r"(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)


def lean_obligations(path):
    """(lean name, [(name, kind, file, theorem)]) for one Manifest.lean."""
    text = io.open(path, encoding="utf-8").read()
    m = MNAME.search(text)
    body = "\n".join(BLOCKS.findall(text))
    return (m.group(1) if m else None), VERIFIED.findall(body)


def parse_yml(path):
    """(id, module, layer, [(name, kind, theorem, file)]) or None when the shape is not ours."""
    ident = mod = layer = None
    obs = []
    cur = None
    for raw in io.open(path, encoding="utf-8").read().split("\n"):
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line.startswith("id:"):
            ident = line.split(":", 1)[1].strip()
        elif line.startswith("module:"):
            mod = line.split(":", 1)[1].strip()
        elif line.startswith("layer:"):
            layer = line.split(":", 1)[1].strip()
        elif line.startswith("obligations:"):
            pass
        elif line.startswith("  - name:"):
            if cur is not None:
                obs.append(cur)
            cur = {"name": line.split(":", 1)[1].strip()}
        elif line.startswith("    ") and ":" in line and cur is not None:
            k, v = line.strip().split(":", 1)
            cur[k] = v.strip()
        else:
            return None
    if cur is not None:
        obs.append(cur)
    if ident is None or mod is None or layer is None:
        return None
    try:
        rows = [(o["name"], o["kind"], o["theorem"], o["file"]) for o in obs]
    except KeyError:
        return None
    return ident, mod, layer, rows


def declared_in(rel_file):
    p = os.path.join(REPO, rel_file)
    if not os.path.isfile(p):
        return set()
    return set(DECL.findall(io.open(p, encoding="utf-8", errors="replace").read()))


def main():
    problems = []
    plugins = 0
    obligations = 0
    for root, _dirs, files in os.walk(PLUGINS):
        if "plugin.yml" not in files:
            continue
        plugins += 1
        yml_path = os.path.join(root, "plugin.yml")
        man_path = os.path.join(root, "Manifest.lean")
        rel_dir = os.path.relpath(root, REPO).replace(os.sep, "/")
        if not os.path.isfile(man_path):
            problems.append("%s: plugin.yml has no sibling Manifest.lean" % rel_dir)
            continue

        parsed = parse_yml(yml_path)
        if parsed is None:
            problems.append("%s: plugin.yml is not in the expected shape" % rel_dir)
            continue
        ident, mod, layer, yml_obs = parsed

        lean_name, lean_obs = lean_obligations(man_path)
        obligations += len(yml_obs)

        if ident != lean_name:
            problems.append("%s: id %r but the Lean manifest calls itself %r" % (rel_dir, ident, lean_name))
        want_mod = "Lattice." + os.path.relpath(man_path, LATTICE).replace(os.sep, "/")[:-len(".lean")]
        want_mod = want_mod.replace("/", ".")
        if mod != want_mod:
            problems.append("%s: module %r but the file is %r" % (rel_dir, mod, want_mod))
        want_layer = rel_dir.split("/")[2]
        if layer != want_layer:
            problems.append("%s: layer %r but the directory says %r" % (rel_dir, layer, want_layer))

        if len(yml_obs) != len(lean_obs):
            problems.append("%s: %d obligations in the YAML, %d in the Lean manifest"
                            % (rel_dir, len(yml_obs), len(lean_obs)))
        for i, (y, l) in enumerate(zip(yml_obs, lean_obs)):
            yn, yk, yt, yf = y
            ln, lk, lf, lt = l
            lk = lk.lstrip(".")
            if (yn, yk, yt, yf) != (ln, lk, lt, lf):
                problems.append("%s[%d]: YAML %r != Lean %r"
                                % (rel_dir, i, (yn, yk, yt, yf), (ln, lk, lt, lf)))
        for _n, _k, thm, fil in yml_obs:
            if not os.path.isfile(os.path.join(REPO, fil)):
                problems.append("%s: obligation %r names file %r which does not exist" % (rel_dir, _n, fil))
                continue
            if thm not in declared_in(fil):
                problems.append("%s: obligation %r says the theorem is %r, which is not declared in %s"
                                % (rel_dir, _n, thm, fil))

    print("  plugins with a capability index: %d" % plugins)
    print("  obligations cross-checked:       %d" % obligations)
    for p in problems:
        print("  PROBLEM %s" % p)
    if problems:
        print("PLUGIN YML: %d problem(s)" % len(problems))
        return 1
    print("PLUGIN YML: every index agrees with its Lean manifest and names a declared theorem")
    return 0


def _self_test():
    """Every assertion must be able to fail, and an unparseable file must not be silently skipped."""
    ok = True

    good = ("id: X\nmodule: Lattice.A.B\nlayer: L\nobligations:\n"
            "  - name: n1\n    kind: laws\n    theorem: t1\n    file: Lattice/a.lean\n")
    tmp = os.path.join(HERE, ".plugin_yml_selftest.yml")
    io.open(tmp, "w", encoding="utf-8", newline="\n").write(good)
    try:
        parsed = parse_yml(tmp)
        if parsed is None or parsed[0] != "X" or len(parsed[3]) != 1:
            print("  SELF-TEST FAIL: a well-formed index did not parse")
            ok = False

        io.open(tmp, "w", encoding="utf-8", newline="\n").write("id: X\n")   # no module/layer
        if parse_yml(tmp) is not None:
            print("  SELF-TEST FAIL: an index missing `module`/`layer` was accepted")
            ok = False

        io.open(tmp, "w", encoding="utf-8", newline="\n").write(good.replace("    kind: laws\n", ""))
        if parse_yml(tmp) is not None:
            print("  SELF-TEST FAIL: an index whose obligation lacks `kind` was accepted")
            ok = False
    finally:
        if os.path.isfile(tmp):
            os.remove(tmp)

    # The tree must actually contain indices, or this check could pass by seeing nothing.
    found = 0
    for root, _dirs, files in os.walk(PLUGINS):
        if "plugin.yml" in files:
            found += 1
    if found == 0:
        print("  SELF-TEST FAIL: no plugin.yml exists, so this check cannot fire")
        ok = False

    # A theorem must really be findable in a real file, or `declared_in` is broken.
    if "roundtrip_determines_skeleton" not in declared_in("Lattice/Core/IR/Skeleton.lean"):
        print("  SELF-TEST FAIL: declared_in missed a declaration that is definitely there")
        ok = False

    print("PLUGIN YML SELF-TEST: %s" % ("parser, both rejections and the tree all behave" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(_self_test())
    sys.exit(main())
