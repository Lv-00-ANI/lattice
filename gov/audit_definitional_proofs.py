"""gov/audit_definitional_proofs.py -- measure how much of the proof chain is DEFINITIONAL.

## Why this file exists

`check_proof_strength.py` already catches three shapes of nominally-complete proof: reflexive
statements (`a = a`), bare-hypothesis proofs (`exact h`), and `True`-like `Prop`-valued defs. It
deliberately does NOT catch a fourth shape, which this project has now met TWICE IN TWO LAYERS:

    -- Core/IR/Compile.lean            (round 991)
    def ModelsIR (W : IRWeights) (k : IRSkeleton) : Prop := W = compileSkel k
    theorem compile_sound (h : Typable ...) : ModelsIR (compileSkel k) k := by
      have := h
      exact rfl

    -- Core/CIC/Compile.lean          (round 1026)
    def ModelsTerm (W : CICWeights) (t : Term) : Prop := W = compile t
    theorem compile_sound (h : Typable K Γ t) : ModelsTerm (compile t) t := by
      have := h
      exact rfl

The statement is not reflexive and the proof is not `exact h`, so neither existing rule fires. What is
actually happening is that the *named predicate pins its own argument* (`W = compile k`), so the
conclusion is true BY DEFINITION and the hypothesis is decorative. A theorem whose conclusion unfolds
to `t = t` cannot carry information no matter how it is written.

## The two shapes this file catches, and why only two

**P1 `rfl_only`** -- the whole proof is `rfl` / `Iff.rfl` / `trivial`. Pure syntax, zero false positives.

**P2 `haves_then_rfl`** -- the proof is a sequence of `have` lines closed by `exact rfl` / `rfl`. Also
pure syntax. This is the shape that hid `compile_sound` in both layers: the `have` disposes of a binder
so that the proof does not literally read `rfl`, but nothing else happens.

**Deliberately NOT caught**: a proof that ends in `rfl` after `unfold`/`simp`/`rw` steps. Those can be
doing real work (`weightCodeIR_compileSkel` ends in a `simp`, and it is arithmetic), and a detector that
flags them would be wrong often enough to be ignored -- which is the failure mode this project keeps
recording. Narrow and right beats broad and noisy.

## Interface

    python audit_definitional_proofs.py            # report; exit 0 unless NEW/STALE against baseline
    python audit_definitional_proofs.py --check    # gate: exit 1 on NEW or STALE
    python audit_definitional_proofs.py --write    # rewrite the baseline with today's findings
    python audit_definitional_proofs.py --self-test

A baseline that can only SHRINK is the point: `--write` is a deliberate act, and `--check` fails on a
stale entry so the file cannot quietly stop describing the tree.

## What the number means

`in_degree >= 1` is what makes a finding interesting: a definitional theorem that nobody reads is dead
weight, but one that other proofs lean on is a LOAD in the chain. The report splits the two.
"""

import argparse
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tools.sorry_axiom_census import strip_comments  # noqa: E402  (comment stripper is shared)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAT = os.path.join(ROOT, "Lattice")
BASELINE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "definitional-proof-baseline.txt")

# **The attribute group must be OPTIONAL. Writing `(?:@\[[^\]]*\]\s*)` without the `?` made the first
# version of this file scan ONLY attributed declarations -- 89 findings when the tree has thousands of
# theorems, and it silently missed both `compile_sound`s the file was written to catch.** A detector that
# undercounts by two orders of magnitude is worse than none: it reports a clean tree.
DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z0-9_'!?.]+)"
)

TRIVIAL_BODY = {"rfl", "Iff.rfl", "trivial"}
HAVE_LINE = re.compile(r"^(?:have|let)\b[^\n]*$")


def _statement_end(src, start):
    """Return the index just past the first top-level `:=` after `start`, or None.

    "Top-level" is bracket depth 0, so a `:=` inside `{f : α := ...}` or a default argument is not
    mistaken for the start of the proof. `:=` inside a `where` block cannot occur before the proof
    begins, so depth tracking is enough.
    """
    depth = 0
    i = start
    n = len(src)
    while i < n:
        c = src[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth = max(0, depth - 1)
        elif depth == 0 and src.startswith(":=", i):
            return i + 2
        i += 1
    return None


def classify(body):
    """Classify a proof body. Returns (kind, detail) or (None, None).

    `body` is everything after the statement's top-level `:=`.
    """
    text = body.strip()
    if text.startswith("by"):
        text = text[2:]
    lines = [ln.strip() for ln in text.split("\n") if ln.strip()]
    if not lines:
        return None, None
    # `exact rfl` and `rfl` are the same closer; normalize before comparing. Missing this made the
    # self-test fail on the very shape the file was written for (`have := h` / `exact rfl`).
    closer = lines[-1]
    if closer.startswith("exact "):
        closer = closer[len("exact "):].strip()
    if len(lines) == 1 and closer in TRIVIAL_BODY:
        return "rfl_only", closer
    # P2: `have` lines closed by a bare rfl. Anything else in the body disqualifies it.
    if closer in TRIVIAL_BODY and len(lines) >= 2:
        if all(HAVE_LINE.match(ln) for ln in lines[:-1]):
            return "haves_then_rfl", "%s -> %s" % (len(lines) - 1, closer)
    return None, None


def scan():
    """Return (findings, sources) where findings is {name: (rel, kind, detail)}."""
    findings = {}
    sources = {}
    for root, _, fs in os.walk(LAT):
        if "Reference" in root.split(os.sep):
            continue
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace(os.sep, "/")
            try:
                src = io.open(p, "rb").read().decode("utf-8", errors="replace")
            except OSError:
                continue
            code = strip_comments(src)
            sources[rel] = code
            for m in DECL.finditer(code):
                name = m.group(1).split(".")[-1]
                end = _statement_end(code, m.end())
                if end is None:
                    continue
                # proof runs to the next top-level declaration; a generous slice is enough because
                # `classify` only looks at the first lines and rejects anything unexpected.
                tail = code[end:]
                nxt = DECL.search(tail)
                body = tail[: nxt.start()] if nxt else tail
                kind, detail = classify(body)
                if kind:
                    # **Key on (file, name), not name. Two layers each have a theorem called
                    # `compile_sound` (Core/IR and Core/CIC) and keying by name let the second overwrite
                    # the first -- the baseline could not even represent both findings.**
                    findings.setdefault((rel, name), (kind, detail))
    return findings, sources


def in_degree(name, sources, definer):
    """Number of OTHER files whose code contains `name` as a whole word."""
    pat = re.compile(r"\b%s\b" % re.escape(name))
    return sum(1 for rel, code in sources.items() if rel != definer and pat.search(code))


def load_baseline():
    if not os.path.exists(BASELINE):
        return set()
    out = set()
    for line in io.open(BASELINE, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            out.add(line)
    return out


def write_baseline(findings):
    lines = ["# gov/audit_definitional_proofs.py -- definitional proofs (file\\tname)",
             "#",
             "# A definitional proof is one whose conclusion is true BY DEFINITION: either the whole proof",
             "# is `rfl`, or it is `have` lines closed by `rfl`. Such a theorem cannot carry information.",
             "# Entries can only be REMOVED (by making the statement non-definitional or deleting it);",
             "# `--check` fails on a stale entry so this file cannot stop describing the tree.",
             ""]
    lines += ["%s\t%s" % (rel, name) for (rel, name) in sorted(findings)]
    io.open(BASELINE, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")


def self_test():
    cases = [
        # (body, expected kind)
        ("rfl", "rfl_only"),
        ("by rfl", "rfl_only"),
        ("by\n  rfl", "rfl_only"),
        ("Iff.rfl", "rfl_only"),
        ("by trivial", "rfl_only"),
        ("by\n  have := h\n  exact rfl", "haves_then_rfl"),
        ("by\n  have h2 := h\n  have h3 := h2\n  rfl", "haves_then_rfl"),
        # must NOT fire: real work after the rfl, or a non-trivial closer
        ("by\n  unfold f\n  rfl", None),
        ("by\n  simp [g]\n  exact rfl", None),
        ("by\n  have := h\n  simp [this]", None),
        ("by\n  intro x\n  rfl", None),
        ("by\n  exact h", None),
        ("by\n  constructor\n  · rfl\n  · rfl", None),
    ]
    bad = 0
    for body, want in cases:
        got, _ = classify(body)
        if got != want:
            print("  SELF-TEST FAIL: %r -> %r, want %r" % (body[:40], got, want))
            bad += 1
    # the top-level `:=` finder must ignore `:=` inside brackets
    src = "theorem t (f : {a : Nat // a := 1} -> Nat) : True := by trivial"
    end = _statement_end(src, 0)
    ok = end is not None and src[end:].strip().startswith("by")
    if not ok:
        print("  SELF-TEST FAIL: _statement_end ignored bracket depth")
        bad += 1
    print("  definitional-proof self-test: %s" % ("ok" if bad == 0 else "%d FAILURES" % bad))
    return 0 if bad == 0 else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()

    findings, sources = scan()
    if args.write:
        write_baseline(findings)
        print("  wrote %s (%d finding(s))" % (os.path.basename(BASELINE), len(findings)))
        return 0

    base = load_baseline()
    today = set("%s\t%s" % (rel, name) for (rel, name) in findings)
    new = sorted(today - base)
    stale = sorted(base - today)

    kinds = {}
    loaded = []
    for (rel, name), (kind, detail) in sorted(findings.items()):
        kinds[kind] = kinds.get(kind, 0) + 1
        deg = in_degree(name, sources, rel)
        if deg >= 1:
            loaded.append((rel, name, kind, deg))

    print("  definitional proofs: %d (rfl_only %d, haves_then_rfl %d)"
          % (len(findings), kinds.get("rfl_only", 0), kinds.get("haves_then_rfl", 0)))
    print("  of which LOAD-BEARING (in-degree >= 1): %d" % len(loaded))
    for rel, name, kind, deg in loaded:
        print("    %-44s %-40s %-16s in=%d" % (rel, name, kind, deg))
    if new:
        print("  NEW (not in baseline):")
        for x in new:
            print("    " + x.replace("\t", " :: "))
    if stale:
        print("  STALE (baseline entry no longer found):")
        for x in stale:
            print("    " + x.replace("\t", " :: "))
    if args.check:
        if new or stale:
            print("  DEFINITIONAL PROOFS: %d new, %d stale -- decide each one" % (len(new), len(stale)))
            return 1
        print("  DEFINITIONAL PROOFS: baseline matches (%d)" % len(base))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())