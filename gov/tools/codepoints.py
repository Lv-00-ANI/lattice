#!/usr/bin/env python3
"""Codepoint view: render a source file with every non-ASCII character as <U+XXXX>.

Why this exists
---------------
An earlier defect report (D2) was WRONG because the shell/console pipeline silently
replaced Lean unicode tokens (U+2194 ARROWS, U+2192, U+2208, U+27E8) with '?'. A
lemma that reads `(h : forall a, P a <-> Q (f a))` appeared to read
`(h : forall a, P a -> Q (f a))`, and a false defect was filed against a file that
actually compiles.

Rule (see 00-ZERO-framework.md E1-E4): any claim about what Lean source CONTAINS
must come from either `lake env lean` or a codepoint view produced by this tool.

Usage
-----
    python codepoints.py FILE [--lines A-B] [--find TOKEN]

Output is ASCII-only by construction, so it survives any console encoding.
"""
import argparse
import sys

TOKEN_NAMES = {
    0x2192: "ARROW ->",
    0x2194: "IFF <->",
    0x2190: "LEFT ARROW <-",
    0x2200: "FORALL",
    0x2208: "ELEMENT-OF",
    0x2209: "NOT-ELEMENT-OF",
    0x27E8: "LANGLE",
    0x27E9: "RANGLE",
    0x00B7: "DOT (tactic bullet)",
    0x2227: "AND",
    0x2228: "OR",
    0x2264: "LE",
    0x2265: "GE",
    0x2260: "NE",
    0x2211: "SUM",
    0x220F: "PRODUCT",
    0x27FA: "LONG-IFF",
    0x03B1: "alpha",
    0x03B2: "beta",
    0x03B3: "gamma",
    0x03BB: "lambda",
}


def render(line: str) -> str:
    out = []
    for c in line:
        cp = ord(c)
        out.append(c if cp < 128 else "<U+%04X>" % cp)
    return "".join(out)


def codepoint_census(text: str) -> dict:
    census = {}
    for c in text:
        cp = ord(c)
        if cp >= 128:
            census[cp] = census.get(cp, 0) + 1
    return census


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--lines", default=None, help="A-B, 1-based inclusive")
    ap.add_argument("--find", default=None, help="only lines containing this ASCII token")
    ap.add_argument("--census", action="store_true", help="also print a codepoint census")
    args = ap.parse_args()

    text = open(args.path, "rb").read().decode("utf-8", errors="replace")
    lines = text.splitlines()

    lo, hi = 1, len(lines)
    if args.lines:
        a, _, b = args.lines.partition("-")
        lo = int(a)
        hi = int(b) if b else int(a)

    print("file   : %s" % args.path)
    print("lines  : %d" % len(lines))
    print("bytes  : %d" % len(text.encode("utf-8")))
    print("bom    : %s" % (open(args.path, "rb").read(3) == b"\xef\xbb\xbf"))
    print("-" * 60)

    for i in range(lo - 1, min(hi, len(lines))):
        ln = lines[i]
        if args.find and args.find not in ln:
            continue
        marks = ""
        if any(ord(c) >= 128 for c in ln):
            marks = "   <<< has non-ASCII"
        print("%4d| %s%s" % (i + 1, render(ln), marks))

    if args.census:
        census = codepoint_census(text)
        print("-" * 60)
        print("codepoint census (non-ASCII):")
        for cp, n in sorted(census.items(), key=lambda kv: -kv[1]):
            name = TOKEN_NAMES.get(cp, "")
            try:
                glyph = chr(cp).encode("unicode_escape").decode("ascii")
            except Exception:
                glyph = "?"
            print("  U+%04X  x%-5d  %-24s %s" % (cp, n, glyph, name))
    return 0


if __name__ == "__main__":
    sys.exit(main())
