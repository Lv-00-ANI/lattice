#!/usr/bin/env python3
"""Which kernel theorems are never referenced outside their own file?

## Why this exists

Round 55 found that `Lattice.Geo.RepairBridge` spent several rounds reconstructing
`Lattice.Core.Repair.progress`, a theorem that already existed **and was already being called** by
`Lattice.Geo.Loop.loop_converges`. The cost was six rounds; the fix was a single `grep`.

That failure mode -- "a theorem exists, is correct, and nobody uses it" -- is invisible to
`gate.py` (which checks absence of escapes and layering) and to `audit_docs.py` (which checks that
documented names exist). This script looks for it directly.

## What counts as a reference

A theorem `T` defined in file `F` is *referenced* if its name appears in the body of some file
other than `F`. Mentions inside comments do not count, and neither do mentions in the same file --
a theorem used only by its own file's later theorems is still an entry point, but it is not
*dead*, so those are reported separately.

## Deliberate exclusions

* **Entry points by design**: theorems whose names encode a target (`T1`..`T4` carriers,
  `*_sound`, `*_iff`, `*_eq_zero_iff`, the `*_loop_*` closed-loop family, `*_roundtrip`,
  `*_reaches_*`, `*_compile_extract`, `*_agrees_with_*`) are meant to be cited by external
  readers, not by other Lean files. They are listed but not counted as suspicious.

  The closed-loop family was added in Round 97: `conj_loop_fixed_point` and its siblings were
  reported as "never used" because the pattern list did not know them. The classification gap was
  in this script, not in the proofs -- renaming the theorems to fit the list would have hidden it.

* **`instance`-only definitions**: not tracked here.

## Note on this file's own history

Round 97 rewrote it from scratch: an edit script truncated it to zero bytes, and the file is
untracked in git, so there was nothing to restore from. The rewrite reproduces the categories and
the interpretation note below, with the entry-point pattern extended as described. Recorded
because a reader comparing this file with an older copy would otherwise see unexplained
differences -- and because a survey tool that silently returned nothing would have been worse than
no survey tool at all.

Exit code 0: this is a survey, not a gate.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAYERS = ["Core", "Lift", "Lib", "Slots", "Geo"]

DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)

# A name whose shape says "cite me from outside": the project's target statements.
ENTRY = re.compile(r"(_sound|_iff|_eq_zero|_correct|_preserves|_converges|_exact"
                   r"|_loop_|_roundtrip|_reaches_|_compile_extract|_agrees_with_"
                   r"|^T[1-4]|^geo_|^compile|^token_)")


def strip_comments(src):
    """Remove `/- -/` (nested) and `--` comments, preserving newlines."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src.startswith("-/", i):
            i += 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def lean_files():
    found = []
    for layer in LAYERS:
        base = os.path.join(ZERO, "Lattice", layer)
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for f in fs:
                if f.endswith(".lean"):
                    found.append(os.path.join(root, f))
    return found


def main():
    paths = lean_files()

    defined = {}
    texts = {}
    for p in paths:
        mod = os.path.relpath(p, os.path.join(ZERO, "Lattice")).replace(os.sep, ".")
        if mod.endswith(".lean"):
            mod = mod[: -len(".lean")]
        src = io.open(p, "rb").read().decode("utf-8", "replace").replace("\r\n", "\n")
        body = strip_comments(src)
        texts[p] = body
        for m in DECL.finditer(body):
            defined.setdefault(m.group(1), (mod, p))

    compile_cache = {}
    elsewhere = {}
    own_later = {}
    for name, (mod, p) in defined.items():
        pat = compile_cache.get(name)
        if pat is None:
            pat = re.compile(r"\b" + re.escape(name) + r"\b")
            compile_cache[name] = pat
        hit_other = False
        for q, body in texts.items():
            if q == p:
                continue
            if pat.search(body):
                hit_other = True
                break
        elsewhere[name] = hit_other
        if not hit_other:
            body = texts[p]
            first = body.find(name)
            own_later[name] = bool(first >= 0 and pat.search(body, first + len(name)))

    never_outside = []
    never_anywhere = []
    design = []
    for name in sorted(defined, key=lambda n: (defined[n][0], n)):
        mod, p = defined[name]
        if elsewhere[name]:
            continue
        if ENTRY.search(name):
            design.append((mod, name))
        elif own_later.get(name):
            never_outside.append((mod, name))
        else:
            never_anywhere.append((mod, name))

    print("kernel theorem declarations: %d" % len(defined))
    print()
    for title, rows in [
        ("never referenced outside their own file -- %d" % len(never_outside), never_outside),
        ("NEVER used anywhere, not even later in their own file -- %d" % len(never_anywhere),
         never_anywhere),
        ("entry points by design (not suspicious) -- %d" % len(design), design),
    ]:
        print("=" * 78)
        print(title)
        print("=" * 78)
        by_mod = {}
        for mod, name in rows:
            by_mod.setdefault(mod, []).append(name)
        if not by_mod:
            print("  (none)")
        for mod in sorted(by_mod):
            print("  %-22s %s" % (mod, ", ".join(sorted(by_mod[mod]))))
        print()

    print("=" * 78)
    print("Note on interpretation")
    print("=" * 78)
    print("  Comments are stripped before matching, so a name mentioned only in a docstring")
    print("  does NOT count as a reference. Two categories above:")
    print()
    print("    'never referenced outside their own file'")
    print("        used by later declarations in the same file -- internal helpers, or terminal")
    print("        statements meant for readers. Normally fine.")
    print()
    print("    'NEVER used anywhere'")
    print("        the declaration is the last thing anyone would want to call, or it is a")
    print("        terminal statement. Distinguishing the two needs human reading: a terminal")
    print("        statement is fine, but a *step* that nothing consumes means the chain has a")
    print("        break.")
    print()
    print("  The Round-55 lesson: before proving a property 'of an interface', grep the")
    print("  interface's own file. `Core/Repair.progress` existed and was already being called")
    print("  while a new proof of it was attempted for six rounds.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
