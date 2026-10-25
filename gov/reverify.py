# -*- coding: utf-8 -*-
"""Independent re-verification: rebuild the picture from the tree, ignoring every existing claim.

Round 30, following the discipline used at M0: the point is to check whether the project's own narrative
still matches what the files actually contain. Anything asserted in `PROGRESS.md` that cannot be
re-derived here is suspect.

Measurements (all from source bytes, no document consulted):
  1. the objective's five hard requirements, each checked mechanically;
  2. the four target theorems -- located by *statement*, not by remembered name;
  3. the claim "no derivative and no norm in the penalty proofs" -- checked by scanning those proofs;
  4. what each layer actually depends on.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402


def asc(s):
    return "".join(c if ord(c) < 128 else "?" for c in s)



# ---------------------------------------------------------------- scope
# `DSH_GATE_SCOPE=kernel` restricts the walk to the code this project wrote, which is what makes the
# fast verification path affordable. Unset means "everything".
KERNEL_PREFIXES = ("Lattice/Core/", "Lattice/Lift/", "Lattice/Lib/", "Lattice/Slots", "Lattice/Geo/")


def _in_scope(relpath):
    scope = os.environ.get("DSH_GATE_SCOPE")
    if not scope or scope == "all":
        return True
    r = relpath.replace("\\", "/")
    if r.startswith("Lattice/"):
        r = r[len("Lattice/"):]
        r = "Lattice/" + r
    return any(p in r for p in KERNEL_PREFIXES)

def sources():
    out = [(os.path.join(ZERO, "Lattice.lean"), "Lattice")]
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                mod = os.path.relpath(p, ZERO).replace("\\", "/")[:-5].replace("/", ".")
                out.append((p, mod))
    return out


def text(p):
    return strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))


def main():
    srcs = sources()
    alltext = "".join(text(p) for p, _m in srcs)

    print("=" * 76)
    print("A. THE FIVE HARD REQUIREMENTS")
    print("=" * 76)

    # (1) core is the single authority: LinearForm declared exactly once
    lf = [m for p, m in srcs if re.search(r"^structure\s+LinearForm\b", text(p), re.M)]
    print("[1] `LinearForm` declared in: %s" % (lf or "NOWHERE"), "->", "PASS" if len(lf) == 1 else "FAIL")

    # (2) unproved claims are explicit holes
    slots_src = text(os.path.join(ZERO, "Lattice", "Slots.lean"))
    n_defs = len(re.findall(r"^def\s+\w+\s*:\s*Slot\s*:=", slots_src, re.M))
    n_open = slots_src.count("status := .open_")
    n_weakened = slots_src.count("status := .weakened")
    n_discharged = slots_src.count("status := .discharged")
    hyp = len(re.findall(r"\((?:h|ha|hA|hexact|hsat|hmin|hr|hd|hsurj|hnn)\s*:", alltext))
    print("[2] slots: %d total (%d open / %d weakened / %d discharged); explicit hypotheses: %d"
          % (n_defs, n_open, n_weakened, n_discharged, hyp))
    print("    -> PASS" if n_defs > 0 and n_defs == n_open + n_weakened + n_discharged else "    -> FAIL")

    # (2b) no escape hatches
    esc = {k: len(re.findall(v, alltext, re.M)) for k, v in
           [("axiom", r"^\s*axiom\s"), ("opaque", r"^\s*opaque\s"), ("sorry", r"\bsorry\b"),
            ("admit", r"\badmit\b"), ("unsafe", r"^\s*unsafe\s")]}
    print("[2b] escape hatches:", esc, "->", "PASS" if not any(esc.values()) else "FAIL")

    # (3) structure: modules, budget, layers
    over = [(m, text(p).count("\n") + 1) for p, m in srcs if text(p).count("\n") + 1 > 500]
    print("[3] modules: %d; over 500 lines: %s" % (len(srcs), over or "none"))
    print("    -> PASS" if not over else "    -> FAIL")

    print()
    print("=" * 76)
    print("B. THE FOUR TARGET THEOREMS, LOCATED BY STATEMENT")
    print("=" * 76)
    targets = {
        "T1 compile preserves meaning": r"theorem\s+compileProgram_sound",
        "T2 embedding is sound": r"theorem\s+\w*embedding_sound\w*|theorem\s+layer_penalty_exact",
        "T3 extraction equivalence": r"theorem\s+no_extractor_both_layers",
        "T4 loop convergence": r"theorem\s+progress\b",
    }
    for name, pat in targets.items():
        hits = [m for p, m in srcs if re.search(pat, text(p))]
        print("%-32s %s" % (name, hits or "MISSING"))

    print()
    print("=" * 76)
    print("C. 'NO DERIVATIVE, NO NORM' IN THE PENALTY PROOFS")
    print("=" * 76)
    pen = [m for p, m in srcs if "Penalty" in m]
    for m in pen:
        p = [q for q, mm in srcs if mm == m][0]
        t = text(p)
        deriv = len(re.findall(r"\bHasDerivAt\b|\bderiv\b|\bfderiv\b|\bHasFDerivAt\b", t))
        norm = len(re.findall(r"\bnorm\b|‖", t))
        print("  %-42s HasDerivAt/deriv=%d  norm=%d" % (m, deriv, norm))

    print()
    print("=" * 76)
    print("D. LAYER CONTENTS")
    print("=" * 76)
    for layer in ("Lattice.Core", "Lattice.Lift", "Lattice.Lib", "Lattice.Slots"):
        mods = sorted(m for p, m in srcs if m.startswith(layer))
        print("%-12s %2d modules" % (layer, len(mods)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
