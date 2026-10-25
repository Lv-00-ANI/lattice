#!/usr/bin/env python3
"""`lattice-new` invariant gate.

## What this is for

The legacy project kept its honesty in a 1.97 MB prose register (`CORRECTIONS.md`,
600+ numbered entries). That register was not wrong -- it was accurate and hard-won.
It was, however, *unenforced*: nothing stopped a new file from quietly introducing a
`sorry` or a second definition of `Sat`, because the only thing standing in the way
was that someone remembered to look.

This gate moves each of those promises into a machine check that REFUSES. The measure
of success is not "it reports 0"; it is "it reports 1 when a defect is planted".

## The invariants

  I1  no `axiom`                       -- an unproved assertion must be a hypothesis
  I2  no `sorry` / `admit`             -- comments stripped first (see below)
  I3  each semantic concept defined once
  I4  layering                        -- core must not import lib or lift
  I5  `EndToEnd` theorems must use every layer they claim
  I6  every explicit hole `(h : P)` is registered in `Lattice/Slots.lean`

## Two hard-won lessons baked in

* **Comment stripping.** A naive grep over the legacy tree reported 515 `sorry`
  occurrences; the true number was 0, because they were all inside comments such as
  "no sorry / axiom / admit". `--selftest` plants defects to prove the stripper errs
  in the safe direction.

* **Olean existence.** `lake build` printed "Build completed successfully" twice while
  compiling NOTHING, because no target was selected and because a module missing from
  the root aggregator is silently not built. A gate that trusts lake's exit status can
  therefore report success on an empty build. I7 checks artifacts directly.
"""
import argparse
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# The shared comment stripper lives in gov/tools. Importing it (rather than
# re-implementing it) is deliberate: three earlier defect reports disagreed only
# because each had its own notion of "what counts as a comment".
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

ZERO = os.path.abspath(os.path.join(HERE, ".."))
REF_DIR = os.path.join(ZERO, "Lattice", "Reference")
LIB = os.path.join(ZERO, ".lake", "build", "lib")

EXIT = {
    "OK": 0,
    "AXIOM": 1,
    "SORRY": 2,
    "DUP": 3,
    "LAYER": 4,
    "E2E": 5,
    "HOLE": 6,
    "SELFTEST": 7,
    "ARTIFACT": 8,
    "COMMENT": 9,
}


def lean_files(root=ZERO, scope=None):
    """Every Lean source under `zero/`, optionally restricted to one zone.

    The tree grew from ~30 kernel files to ~600 once the Lv-00 trees were migrated in, and every invariant
    walked all of them: `gate.py` went from under a second to 35 s, and the reactivity tests -- which run
    the gate several times -- past three minutes, which made `verify_all.py` unusable.

    `scope` restricts the walk. Set it to `"kernel"` for the fast path during development; leave it unset
    (or set `DSH_GATE_SCOPE=all`) for the full run that decides whether the tree is acceptable. The
    kernel invariants are identical in both modes; only the migrated trees are skipped, and those are
    additionally guarded by `gov/escape_baseline.py`.
    """
    if scope is None:
        scope = os.environ.get("DSH_GATE_SCOPE") or None
    explicit_all = scope == "all"
    if explicit_all:
        scope = None
    out = []
    for base, dirs, names in os.walk(root):
        parts = base.split(os.sep)
        if ".lake" in parts or "gov" in parts or "_archive" in parts:
            continue
        for n in names:
            if not n.endswith(".lean"):
                continue
            p = os.path.join(base, n)
            z = zone_of(rel(p))
            if scope is not None:
                if z != scope:
                    continue
            elif not explicit_all:
                # default scope is "the main line": everything except the reference material, which is
                # Lv-00's assets and can never pass the per-file invariants (`LvFormal` has 56 modules
                # that do not build at all). Green must mean "the chain is healthy".
                if z == "reference":
                    continue
            out.append(p)
    return sorted(out)


def rel(p):
    return os.path.relpath(p, ZERO).replace("\\", "/")


def module_of(p):
    return rel(p)[:-5].replace("/", ".")


class Report:
    def __init__(self):
        self.items = []

    def add(self, inv, msg, path="", line=0):
        self.items.append((inv, msg, path, line))

    def by(self, inv):
        return [i for i in self.items if i[0] == inv]

    def ok(self):
        return not self.items


# ---------------------------------------------------------------- I1 / I2
def check_no_axiom_no_sorry(rep):
    """I1/I2, scoped by zone.

    The kernel must be free of escapes: it is the code this project wrote. The intake tree carries
    historical escapes (`LvFormal`'s 68 `admit`s are in geometry and cryptography files that have
    nothing to do with the chain), so it is held to a **frozen baseline** instead: the total may not
    grow. Quarantine is not inspected at all -- it exists precisely because its contents are known
    not to pass.
    """
    base = intake_baseline()
    tally = {"intake": {"axiom": 0, "opaque": 0, "sorry": 0, "admit": 0}}
    for f in lean_files():
        r = rel(f)
        zone = zone_of(r)
        if zone == "quarantine":
            continue          # known not to pass; not inspected by design
        code = strip_comments(io.open(f, "rb").read().decode("utf-8", errors="replace"))
        def emit(inv, msg, pos):
            if zone == "intake":
                key = msg.split("`")[1] if "`" in msg else "?"
                if key in tally["intake"]:
                    tally["intake"][key] += 1
            else:
                rep.add(inv, msg, r, code[:pos].count("\n") + 1)
        for m in re.finditer(r"^\s*axiom\s+(\S+)", code, re.M):
            emit("I1", "axiom `%s`" % m.group(1), m.start())
        for m in re.finditer(r"^\s*opaque\s+(\S+)", code, re.M):
            emit("I1", "opaque `%s`" % m.group(1), m.start())
        for m in re.finditer(r"\b(sorry|admit)\b", code):
            emit("I2", "`%s` in code" % m.group(1), m.start())

    if base is None:
        return

    # ---------------------------------------------------------------------------------------
    # The frozen baseline covers `Lattice/Reference/`, which `lean_files()` deliberately omits
    # (that function describes the BUILD; Reference is not in the build). Because it was omitted,
    # the loop below compared 0 with 0 for dozens of rounds while Reference/ carried 111 `admit`s,
    # 10 `sorry`s and 1 `axiom`. Walk the reference tree explicitly.
    # ---------------------------------------------------------------------------------------
    ref_tally = {"axiom": 0, "opaque": 0, "sorry": 0, "admit": 0}
    if os.path.isdir(REF_DIR):
        for rroot, _dirs, rfiles in os.walk(REF_DIR):
            for rf in rfiles:
                if not rf.endswith(".lean"):
                    continue
                rpath = os.path.join(rroot, rf)
                rcode = strip_comments(io.open(rpath, "rb").read().decode("utf-8", "replace"))
                ref_tally["axiom"] += len(re.findall(r"^\s*axiom\s+", rcode, re.M))
                ref_tally["opaque"] += len(re.findall(r"^\s*opaque\s+", rcode, re.M))
                for m in re.finditer(r"\b(sorry|admit)\b", rcode):
                    ref_tally[m.group(1)] += 1

    # the intake total may not exceed the frozen baseline
    for key in ("axiom", "opaque", "sorry", "admit"):
        now = tally["intake"].get(key, 0) + ref_tally.get(key, 0)
        was = base.get(key, 0)
        if now > was:
            rep.add("I" + ("1" if key in ("axiom", "opaque") else "2"),
                    "intake `%s` grew from %d to %d (baseline is frozen; regenerate with "
                    "`python gov/gate_scope_measure.py` only after reviewing the new escapes)"
                    % (key, was, now), "Lattice/Reference/LvFormal, Lattice/Reference/Legacy")


# ---------------------------------------------------------------- I3
# A concept is "semantic" if it participates in stating meaning. Keeping the list
# explicit (rather than guessing from names) is what makes the report reproducible.
SEMANTIC_CONCEPTS = [
    "Expr", "eval", "Sat", "Satisfies", "Entails", "Models", "denote",
    "WeightSemantics", "BehaviourallyEquivalent", "LinearForm", "Constraint",
    "Program", "Compile", "Extract", "Repair",
]
DECL = r"(?:structure|inductive|def|abbrev|class|opaque)"


def _qualified_decls(code):
    """Yield `(qualified_name, short, line)` for every declaration, tracking the namespace stack.

    Comparing short names conflates `Lattice.Core.Point` with `Lattice.Point`, which are different
    constants. An earlier revision did exactly that and reported four "collisions" that Lean accepts.
    """
    stack = []
    out = []
    for i, line in enumerate(code.splitlines(), 1):
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        e = re.match(r"^end\s+(\S+)\s*$", line)
        if e and stack:
            stack.pop()
            continue
        d = re.match(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+"
                     r"|@\[[^\]]*\][ \t]*)*(?:abbrev|theorem|lemma|def|structure|inductive"
                     r"|instance|class)[ \t]+([A-Za-z0-9_'.]+)", line)
        if d:
            short = d.group(1)
            full = ".".join(stack + [short])
            out.append((full, short, i))
    return out


def check_abbrev_collisions(rep):
    """I3, second half: no `abbrev` is declared twice **under the same qualified name**.

    A whitelist only catches names someone thought to list; `Lattice.Lift.ZB` was declared in two files and
    Lean refused the combined import. So this scans exhaustively -- but by *qualified* name, because
    `Lattice.Star` and `Lattice.Core.Star` coexist happily.
    """
    seen = {}
    visited = set()
    for f in lean_files():
        r = rel(f)
        if r in visited:            # the file list can contain the same path twice
            continue
        visited.add(r)
        if zone_of(r) in ("reference", "quarantine"):
            continue
        code = strip_comments(io.open(f, "rb").read().decode("utf-8", errors="replace"))
        for line in code.splitlines():
            m = re.match(r"^[ \t]*abbrev[ \t]+([A-Za-z0-9_']+)", line)
            if not m:
                continue
            name = m.group(1)
            if name in seen:
                prev_file = seen[name]
                # Only an all-kernel collision is this project's problem. A name appearing in two
                # intake files is Lv-00's "no shared language" defect (`_archive/NAMESPACE-CONFLICT.md`);
                # a name appearing in a kernel file and an intake file is fine, because the two trees
                # live in different namespaces and are never imported together.
                both_kernel = zone_of(prev_file) in ("kernel", "root") and zone_of(r) in ("kernel", "root")
                if prev_file != r and both_kernel:
                    rep.add("I3", "`abbrev %s` declared twice (%s and %s)"
                            % (name, prev_file, r))
            else:
                seen[name] = r


def check_unique_definitions(rep):
    check_abbrev_collisions(rep)
    for name in SEMANTIC_CONCEPTS:
        # The trailing guard is what makes this check correct rather than noisy:
        # `def LinearForm.denote` and `def LinearForm.instWeightSemantics` EXTEND a
        # namespace, they do not introduce a second `LinearForm`. Without the guard
        # this check reported 3 sites for a concept that is in fact defined once.
        pat = re.compile(
            r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+|@\[[^\]]*\][ \t]*)*"
            + DECL + r"[ \t]+" + re.escape(name) + r"[ \t]*(\{|\(|\[|:|=|where|$)", re.M)
        sites = []
        for f in lean_files():
            code = strip_comments(io.open(f, "rb").read().decode("utf-8", errors="replace"))
            for m in pat.finditer(code):
                sites.append((rel(f), code[: m.start()].count("\n") + 1))
        if len(sites) > 1:
            if len({l[0] for l in sites if zone_of(l[0]) in ('kernel', 'root')}) > 1:
                rep.add("I3", "`%s` defined %d times: %s" %
                    (name, len(sites), ", ".join("%s:%d" % s for s in sites)))


# ---------------------------------------------------------------- I4
# Layer prefixes. Order matters only through `rank` below.
#
# `Geo` was missing here until the approximation work needed it, and its absence was not
# harmless: `layer_of` returned "top" for Geo files, `check_layering` skipped them, and a
# `Lift -> Geo` import -- the reverse of the intended direction -- was invisible.
#
# Measured before adding it (agent-tmp/geo_layer_probe2.py):
#   * Geo's outgoing imports: core 13, lift 7, lib 9 -- only downward;
#   * no non-Geo file imports Geo -- nothing below it needs it.
# So Geo sits above `lib` and below the aggregators.
LAYER_OF = {
    "Lattice/Core": "core",
    "Lattice/Lift": "lift",
    "Lattice/Lib": "lib",
    "Lattice/Slots": "slots",
    "Lattice/Geo": "geo",
    "Lattice/Audit": "audit",
}


def layer_of(p):
    r = rel(p)
    for pref, lay in LAYER_OF.items():
        if r.startswith(pref):
            return lay
    return "top"


def check_layering(rep):
    rank = {"core": 0, "slots": 1, "lift": 2, "lib": 3, "geo": 4, "audit": 5, "top": 99}
    for f in lean_files():
        lay = layer_of(f)
        if lay == "top":
            continue
        txt = io.open(f, "rb").read().decode("utf-8", errors="replace")
        for m in re.finditer(r"^import\s+(\S+)\s*$", txt, re.M):
            mod = m.group(1)
            tgt = mod.replace(".", "/")
            tlay = None
            for pref, l in LAYER_OF.items():
                if tgt.startswith(pref):
                    tlay = l
            if tlay and rank[tlay] > rank[lay]:
                rep.add("I4", "%s layer imports %s layer module `%s`" % (lay, tlay, mod),
                        rel(f), txt[: m.start()].count("\n") + 1)


# ---------------------------------------------------------------- I5
def _decl_index():
    """Index every kernel declaration: its layer and the identifiers its body mentions.

    Two earlier versions of this check were wrong in opposite directions:

    1. Match the literal prefixes `Core.` / `Lift.` / `Lib.` in the theorem body. The
       legacy code uses short names almost everywhere, so this scored real end-to-end
       statements as "0 layers".
    2. Resolve short names through their declaring module, but only one level deep. That
       still misses the composite case: `e2eF_eq_some` mentions `e2eF`, whose *definition*
       chains `tokenize` (L0->L1), `L1Bridge` (L1), `decode` (L1->L2) and `compileToLayer`
       (L2->L3). The theorem is end-to-end; its proof term is not, because it delegates.

    This version indexes bodies and walks the reference graph transitively, so "touches
    layer X" means "depends on a declaration that lives in layer X", however deep.
    """
    cache = getattr(_decl_index, "_cache", None)
    if cache is not None:
        return cache
    layer, body = {}, {}
    decl = re.compile(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+|"
                      r"@\[[^\]]*\][ \t]*)*(?:theorem|lemma|def|abbrev|structure|inductive|class)"
                      r"[ \t]+([A-Za-z0-9_']+)", re.M)
    split = re.compile(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+|"
                       r"@\[[^\]]*\][ \t]*)*(?:theorem|lemma|def|abbrev|structure|inductive|class)"
                       r"[ \t]+([A-Za-z0-9_']+)", re.M)
    for p in lean_files():
        r = rel(p)
        if zone_of(r) not in ("kernel", "root"):
            continue
        lay = layer_of(p)
        if lay == "top":
            continue
        code = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
        marks = list(split.finditer(code))
        for i, m in enumerate(marks):
            n = m.group(1)
            end = marks[i + 1].start() if i + 1 < len(marks) else len(code)
            layer.setdefault(n, set()).add(lay)
            body[n] = body.get(n, "") + code[m.start():end]
    _decl_index._cache = (layer, body)
    return layer, body


def _layers_touched(tokens, layer, body, _seen=None):
    seen = set() if _seen is None else _seen
    out = set()
    for t in tokens:
        if t in seen:
            continue
        seen.add(t)
        out |= layer.get(t, set())
        if t in body:
            out |= _layers_touched(set(re.findall(r"[A-Za-z0-9_']+", body[t])), layer, body, seen)
    return out


def check_endtoend(rep):
    layer, body = _decl_index()
    for f in lean_files():
        code = strip_comments(io.open(f, "rb").read().decode("utf-8", errors="replace"))
        for m in re.finditer(r"^\s*(?:theorem|lemma)\s+(\S*[Ee]nd[_]?[Tt]o[_]?[Ee]nd\S*|\S*e2e\S*)",
                             code, re.M):
            name = m.group(1)
            # body = up to the next top-level theorem/lemma/def
            nxt = re.search(r"^\s*(?:theorem|lemma|def|structure|end)\s", code[m.end():], re.M)
            span = code[m.start(): m.end() + (nxt.start() if nxt else 4000)]
            layers_used = {lay for lay, pref in
                           (("core", "Core."), ("lift", "Lift."), ("lib", "Lib."))
                           if pref in span}
            tokens = set(re.findall(r"[A-Za-z0-9_']+", span))
            layers_used |= _layers_touched(tokens, layer, body)
            layers_used.discard("lift") if False else None
            if len(layers_used) < 2 and zone_of(rel(f)) in ("kernel", "root"):
                rep.add("I5", "`%s` claims end-to-end but its body touches %d layer(s) %s"
                        % (name, len(layers_used), sorted(layers_used)), rel(f),
                        code[: m.start()].count("\n") + 1)


# ---------------------------------------------------------------- I6
def check_holes_registered(rep):
    """I6: the slot registry is internally consistent and its report is regenerated.

    Three failure modes are caught: a name that is not `<domain>.<object>.<property>`,
    two slots sharing a name, and a `discharged` status naming a declaration that does not
    exist. The last is the one that matters most -- a slot that claims to be paid by a
    proof which is not there is exactly the drift a prose register cannot detect.

    `gov/check_slots.py` also rewrites `gov/SLOTS.md`, so the owed list is generated from
    the code instead of being maintained by hand.
    """
    import importlib
    sys.path.insert(0, HERE)
    mod = importlib.import_module("check_slots")
    mod.check(rep)
    # and the registry's own contents must match the file's definitions in both directions --
    # a splice that deletes a definition leaves the comments intact and would otherwise pass.
    reg = importlib.import_module("check_registry")
    reg.check_registry(rep, os.path.join(ZERO, "Lattice", "Slots.lean"))


# ---------------------------------------------------------------- zone scope
# Invariants are written for the kernel; the migrated trees carry historical debt.
# `zone_of` decides which rule applies, so that "the gate is green" keeps meaning
# "nothing got worse" rather than "nothing was ever wrong".

ZONES = [
    ("kernel", ["Lattice/Core", "Lattice/Lift", "Lattice/Lib", "Lattice/Slots", "Lattice/Geo"]),
    ("reference", ["Lattice/Reference"]),
]


def known_unbuildable():
    """Modules documented as failing to build on this toolchain (see `_archive/LVFORMAL-BUILD-TRUTH.md`)."""
    path = os.path.join(HERE, "known-unbuildable.json")
    if not os.path.exists(path):
        return set()
    try:
        return set(json.load(io.open(path, encoding="utf-8"))["modules"])
    except (ValueError, KeyError):
        return set()


def _kernel_involved(paths):
    """True if any of the given files is in the kernel.

    Duplicate definitions are only this project's problem when the kernel is one of the declarers:
    the same name appearing in two `Legacy` files is the historical "no shared language" defect, not a
    regression. Keeping the test here rather than in each check means the policy is stated once.
    """
    for p in paths:
        try:
            if zone_of(rel(p)) in ("kernel", "root"):
                return True
        except (TypeError, OSError):
            return True
    return False


def zone_of(rel):
    """Match by directory segments, not by string prefix.

    `Zero/LegacyConflicted/x.lean` starts with `Lattice/Legacy` but belongs to the quarantine, not to the
    intake. A `startswith` test conflates them -- which is how an earlier revision of the scope analysis
    reported zero files in quarantine while its bytes were counted as intake.
    """
    parts = rel.replace("\\", "/").split("/")
    for z, prefixes in ZONES:
        for p in prefixes:
            seg = p.split("/")
            if parts[:len(seg)] == seg:
                return z
    return "root"


def intake_baseline():
    """The frozen escape budget for the reference zone, or `None` if unmeasured.

    The reference trees are Lv-00's assets: `LvFormal` carries 68 `admit`s in geometry and cryptography
    files that have nothing to do with the chain. They are recorded so that the tally stays visible, and
    the zone is excluded from the per-file invariants because those describe code this project wrote.
    """
    import json
    path = os.path.join(HERE, "intake-baseline.json")
    if not os.path.exists(path):
        return None
    try:
        return json.load(io.open(path, encoding="utf-8"))["intake"]
    except (ValueError, KeyError):
        return None


# ---------------------------------------------------------------- I7
def check_artifacts(rep):
    """I7: artifacts and sources correspond in BOTH directions.

    The forward direction (every source has an artifact) was the original check. The reverse direction
    (every artifact has a source) was added after round 30's re-verification found a stale
    `ProbeUnify.olean` whose source had been deleted -- an orphan that made the module count overstate the
    tree while I7 reported ok.
    """
    srcs = lean_files()
    known = set()
    for f in srcs:
        mod = module_of(f)
        known.add(mod)
        r = rel(f)
        out = os.path.join(LIB, mod.replace(".", os.sep) + ".olean")
        exists = os.path.exists(out)
        if zone_of(r) in ("quarantine", "reference"):
            # the quarantine exists precisely because its contents do not build; an artifact here
            # would mean it was wired into the build by accident
            if exists:
                rep.add("I7", "quarantined module `%s` was compiled -- it should not be in the build"
                        % mod, r)
            continue
        if not exists:
            if mod in known_unbuildable():
                continue          # documented as failing; see the JSON's rationale
            rep.add("I7", "module `%s` compiled to no olean" % mod, r)
        elif mod in known_unbuildable():
            # a module listed as unbuildable now builds: the list is stale and must be updated,
            # otherwise it silently excuses a real failure forever
            rep.add("I7", "module `%s` is listed as unbuildable but has an olean -- refresh "
                   "gov/known-unbuildable.json" % mod, r)

    # reverse direction: an artifact with no source is an orphan
    if os.path.isdir(LIB):
        scope = os.environ.get("DSH_GATE_SCOPE") or None
        if scope == "all":
            scope = None
        for base, _dirs, files in os.walk(LIB):
            for f in files:
                if not f.endswith(".olean"):
                    continue
                full = os.path.join(base, f)
                mod = os.path.relpath(full, LIB).replace("\\", ".").replace("/", ".")[:-len(".olean")]
                if mod in known:
                    continue
                if scope is not None:
                    srcpath = os.path.join(ZERO, mod.replace(".", os.sep) + ".lean")
                    if os.path.exists(srcpath) and zone_of(rel(srcpath)) != scope:
                        continue
                    if not os.path.exists(srcpath) and scope != "kernel":
                        continue
                rep.add("I7", "stale artifact `%s` has no source" % mod,
                        os.path.relpath(full, ZERO).replace("\\", "/"))


# ---------------------------------------------------------------- I8
def check_comments_integrity(rep):
    """I8: block-comment integrity.

    Six rounds produced splice damage that a lesson in a document failed to prevent five times over:
    a region replacement whose boundary was the *text* of a doc comment rather than a declaration
    keyword. The symptoms are always one of three: glued `/--` openers, an unclosed block, or a
    stray `-/`.

    `gov/check_comments.py` implements the scan and `gov/check_comments_reactivity.py` proves it fires.
    """
    import importlib
    sys.path.insert(0, HERE)
    mod = importlib.import_module("check_comments")
    mod.check_comments(rep)


# ---------------------------------------------------------------- selftest
SELFTESTS = [
    ("I1 axiom", "axiom cheat : False", "I1"),
    ("I1 opaque", "opaque cheat : False", "I1"),
    ("I2 sorry", "theorem t : 1 = 1 := sorry", "I2"),
    ("I2 admit", "lemma t : 1 = 1 := by admit", "I2"),
    ("I2 not in comment", "/- sorry -/\ntheorem t : 1 = 1 := rfl", None),
    ("I2 not in line comment", "theorem t : 1 = 1 := rfl -- sorry", None),
]


def selftest():
    print("=== gate self-test: each planted defect must be caught ===")
    bad = 0
    for name, src, want in SELFTESTS:
        code = strip_comments(src)
        got = None
        if re.search(r"^\s*axiom\s", code, re.M) or re.search(r"^\s*opaque\s", code, re.M):
            got = "I1"
        elif re.search(r"\b(sorry|admit)\b", code):
            got = "I2"
        ok = got == want
        if not ok:
            bad += 1
        print("  %-24s expect %-4s got %-4s %s" %
              (name, want, got, "OK" if ok else "** FAIL **"))
    print("=== %s ===" % ("ALL PASS" if bad == 0 else "%d FAILURE(S)" % bad))
    return 0 if bad == 0 else EXIT["SELFTEST"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--only", default=None)
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()

    if a.selftest:
        return selftest()

    rep = Report()
    checks = [
        ("I1/I2", lambda: check_no_axiom_no_sorry(rep)),
        ("I3", lambda: check_unique_definitions(rep)),
        ("I4", lambda: check_layering(rep)),
        ("I5", lambda: check_endtoend(rep)),
        ("I6", lambda: check_holes_registered(rep)),
        ("I7", lambda: check_artifacts(rep)),
        ("I8", lambda: check_comments_integrity(rep)),
    ]
    for name, fn in checks:
        if a.only and a.only != name:
            continue
        fn()

    if not a.quiet or not rep.ok():
        print("=" * 68)
        print("LATTICE invariant gate")
        print("=" * 68)
        per = {}
        for inv, msg, path, line in rep.items:
            per.setdefault(inv, []).append((msg, path, line))
        for inv in ["I1", "I2", "I3", "I4", "I5", "I6", "I7", "I8"]:
            hits = per.get(inv, [])
            status = "ok" if not hits else "%d finding(s)" % len(hits)
            print("%-4s %-20s %s" % (inv, INVARIANT_TITLE[inv], status))
            for msg, path, line in hits[:12]:
                loc = ("%s:%d" % (path, line)) if path else ""
                print("       %-46s %s" % (msg[:46], loc))

    for inv in ["I1", "I2", "I3", "I4", "I5", "I6", "I7", "I8"]:
        if rep.by(inv):
            # I8 (comment integrity) used to be missing from this table, so the first
            # time it fired the gate raised KeyError instead of returning COMMENT (9):
            # a traceback and exit 1, which a caller reads as "the gate crashed", not as
            # "a comment is damaged". It had never fired in practice, which is why the
            # hole survived. Reproduced in agent-tmp/repro_i8_keyerror.py.
            return EXIT[{"I1": "AXIOM", "I2": "SORRY", "I3": "DUP", "I4": "LAYER",
                         "I5": "E2E", "I6": "HOLE", "I7": "ARTIFACT",
                         "I8": "COMMENT"}[inv]]
    return EXIT["OK"]


INVARIANT_TITLE = {
    "I1": "no axiom/opaque",
    "I2": "no sorry/admit",
    "I3": "definitions unique",
    "I4": "layering respected",
    "I5": "end-to-end honest",
    "I6": "holes registered",
    "I7": "artifacts present",
    "I8": "comments intact",
}

if __name__ == "__main__":
    sys.exit(main())
