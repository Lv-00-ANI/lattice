"""Round 160: does anything in the tree re-invent `ApproxRepresentation`?

Round 159 found the bounded-extraction line was an island. One reaction is "wire it up somewhere"; a
better first question is "does something ALREADY have this shape but wrote its own version?" -- that
is the abstraction-governance failure mode, and it is invisible to every existing check.

`ApproxRepresentation P W` has a specific fingerprint:

    compile : P -> W
    extract : W -> P
    dist    : P -> P -> R
    eps     : R
    bounded : forall p, dist (extract (compile p)) p <= eps

A duplicate is a structure (or a pair of defs) with `compile`-like and `extract`-like fields PLUS some
bounded-error obligation. A near-duplicate states the same thing about `Float`, or about a `Nat`
truncation, without the `dist`/`eps` packaging.

The scan looks for: structures whose fields mention both a forward map and a backward map, together
with a `<=`-shaped obligation somewhere in the same file.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))

STRUCT = re.compile(r"(?m)^structure\s+(\w+)([^\n]*?)where\n((?:\s+.*\n)+?)(?=^\S|\Z)", re.M)

FORWARD = re.compile(r"\b(compile|encode|toFloat|quantize|round|truncate|approx|cast)\w*\b", re.I)
BACKWARD = re.compile(r"\b(extract|decode|fromFloat|dequantize|unround|recover|ofFloat)\w*\b", re.I)
BOUND = re.compile(r"(<=|≤)\s*\w*ε|error.*(<=|≤)|(<=|≤).*eps|tolerance|bounded", re.I)


def corpus():
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            out[rel] = io.open(p, "rb").read().decode("utf-8", errors="replace")
    return out


def scan(C):
    hits = []
    for rel, src in sorted(C.items()):
        for m in STRUCT.finditer(src):
            name, _params, body = m.group(1), m.group(2), m.group(3)
            if name in ("ApproxRepresentation", "Representation", "LossyRepresentation"):
                continue
            fwd = FORWARD.search(body)
            bwd = BACKWARD.search(body)
            if not (fwd and bwd):
                continue
            # a bound obligation in the same file
            if not BOUND.search(src):
                continue
            hits.append((rel, name, fwd.group(0), bwd.group(0)))
    return hits


def main(argv):
    C = corpus()
    hits = scan(C)
    print("=" * 84)
    print("structures with a forward+backward pair AND a bounded-error obligation")
    print("=" * 84)
    for rel, name, fwd, bwd in hits:
        print("  %-52s %-24s %s / %s" % (rel, name, fwd, bwd))
    print()
    if hits:
        print("%d candidate(s). Each is either a genuine duplicate of `ApproxRepresentation` or a" % len(hits))
        print("different notion that happens to share words. Reading them is the work; this only")
        print("narrows the field.")
        return 0
    print("None. Nothing re-invents the bounded-round-trip shape.")
    print()
    print("So round 159's island is not a duplicate elsewhere -- `ApproxRepresentation` is the only")
    print("statement of bounded extraction in the tree, and it still has no consumer.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
