#!/usr/bin/env python3
"""Objective self-audit: check each hard requirement against the tree, not against memory.

The point of a separate auditor (rather than a line in a progress note) is that requirements
drift: a claim verified in round 5 can become false by round 12 when a file moves. This prints
one line per requirement with the concrete evidence, and exits non-zero if any is unmet.
"""
import io
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
sys.path.insert(0, HERE)
from sorry_axiom_census import strip_comments  # noqa: E402


def lean_sources():
    out = [os.path.join(ZERO, "Lattice.lean")]
    for base, _d, fs in os.walk(os.path.join(ZERO, "Lattice")):
        for f in sorted(fs):
            if f.endswith(".lean"):
                out.append(os.path.join(base, f))
    return out


def all_text():
    return "".join(strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
                   for p in lean_sources())


def kernel_sources():
    """The BUILD GRAPH: everything except `Reference/`, which is frozen upstream evidence.

    Round 170, P1-9. The two scopes had been conflated: row (2b) below reported `axiom=1 sorry=68`
    because it measured `all_text()`, which includes `Reference/`, and then read as though the library
    itself used them. `README` already states the correct sentence -- "内核 0 逃逸，`Reference/` 冻结"
    and "「全树 0 逃逸」是错的说法" -- but the automated row did not follow it, so the audit showed
    5/7 with no way to see which failure was which.
    """
    return [p for p in lean_sources() if "Reference" not in p]


def kernel_text():
    return "".join(strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
                   for p in kernel_sources())


def ref_text():
    return "".join(strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
                   for p in lean_sources() if "Reference" in p)


def has(pattern, text=None):
    t = text if text is not None else all_text()
    return re.search(pattern, t, re.M) is not None


def main():
    rows = []
    txt = all_text()

    # (1) core/ is the sole authority
    ok1 = has(r"structure LinearForm") and has(r"def LinearForm\.denote")
    srcs = lean_sources()
    counts = {
        "LinearForm": sum(1 for p in srcs if has(r"^\s*structure\s+LinearForm\b",
                        strip_comments(io.open(p, "rb").read().decode("utf-8", "replace")))),
    }
    ok1 = ok1 and counts["LinearForm"] == 1
    rows.append(("(1) core is the single authority",
                 "LinearForm defined in %d file(s)" % counts["LinearForm"], ok1))

    # (2) slots exist and every unproved fact is an explicit hypothesis
    import check_slots
    slots = check_slots.collect()
    holes_as_params = len(re.findall(r"\((?:h|hexact|hsat|hmin)\s*:", txt))
    rows.append(("(2) unproved facts are explicit holes",
                 "%d slots, %d explicit (h : ...) parameters" % (len(slots), holes_as_params),
                 len(slots) >= 5 and holes_as_params >= 5))
    kt = kernel_text()
    rows.append(("(2b) no axiom / opaque / sorry / admit -- KERNEL (build graph)",
                 "axiom=%d opaque=%d sorry=%d" % (
                     len(re.findall(r"^\s*axiom\s", kt, re.M)),
                     len(re.findall(r"^\s*opaque\s", kt, re.M)),
                     len(re.findall(r"\b(sorry|admit)\b", kt))),
                 not re.search(r"^\s*(axiom|opaque)\s", kt, re.M)
                 and not re.search(r"\b(sorry|admit)\b", kt)))
    # The frozen region, reported so the two scopes are never mistaken for each other again. This row
    # is INFORMATIONAL: `Reference/` is upstream Lv-00 evidence kept verbatim, and its escapes are the
    # 69 baseline entries in gov/escape-baseline.json. Expecting zero here would mean editing frozen
    # evidence to make a number look better.
    rt = ref_text()
    rows.append(("(2c) frozen `Reference/` -- INFORMATIONAL, not a certification claim",
                 "axiom=%d opaque=%d sorry=%d (frozen; see gov/escape-baseline.json)" % (
                     len(re.findall(r"^\s*axiom\s", rt, re.M)),
                     len(re.findall(r"^\s*opaque\s", rt, re.M)),
                     len(re.findall(r"\b(sorry|admit)\b", rt))),
                 True))

    # (3) clean chain: every module under a layer, budget respected
    mods = [os.path.relpath(p, ZERO).replace("\\", "/") for p in srcs]
    bad_acc = [m for m in mods if re.search(r"[^\x00-\x7F]", m)]
    rows.append(("(3a) no module name outside the ASCII namespace",
                 "%d modules, %d offenders" % (len(mods), len(bad_acc)), not bad_acc))
    over = []
    over_ref = []
    for p in srcs:
        n = io.open(p, "rb").read().count(b"\n") + 1
        if n > 500:
            # Round 174: same scope bug as (2b). `srcs` includes `Reference/`, which is frozen upstream
            # evidence -- listing its 31 over-budget files inside a row that reads as a verdict on this
            # library makes the row unreadable and permanently red for a reason nobody can act on.
            (over_ref if "Reference" in p else over).append((os.path.basename(p), n))
    rows.append(("(3b) file budget 500 lines -- KERNEL (build graph)",
                 "%d over budget: %s" % (len(over), over[:6] or "none"), not over))
    rows.append(("(3c) file budget, frozen `Reference/` -- INFORMATIONAL",
                 "%d over budget (frozen, not a claim)" % len(over_ref), True))

    # (4) the four target theorems
    targets = {
        "T1": "compileProgram_sound",
        "T2": "embedding_sound_at_minimiser",
        "T3": "no_extractor_both_layers",
        "T4": "theorem progress",
    }
    missing = [k for k, v in targets.items() if not has(r"\b" + re.escape(v.split()[-1]) + r"\b")]
    rows.append(("(4) four target theorems",
                 "missing: %s" % (missing or "none"), not missing))

    # (5) reversibility stated by layer
    layered = ["compile_injective", "semantic_not_injective", "no_extractor_both_layers"]
    miss5 = [m for m in layered if not has(r"\b" + m + r"\b")]
    rows.append(("(5) reversibility by layer",
                 "missing: %s" % (miss5 or "none"), not miss5))

    print("=" * 74)
    print("OBJECTIVE SELF-AUDIT")
    print("=" * 74)
    bad = 0
    for name, evidence, ok in rows:
        print("%-12s %-46s %s" % ("PASS" if ok else "FAIL", name, evidence))
        if not ok:
            bad += 1
    print("=" * 74)
    print("%d/%d requirements met" % (len(rows) - bad, len(rows)))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
