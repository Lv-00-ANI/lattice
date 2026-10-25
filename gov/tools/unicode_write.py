#!/usr/bin/env python3
"""Write Lean source containing unicode tokens, reliably.

Why this exists
---------------
Lean's mathematics depends on characters such as U+2208 (element of), U+27E8/9
(angle brackets), U+2192 (arrow) and U+2194 (iff). Passing those through a Windows
console (GBK codepage) or through a lossy text pipeline replaces them with '?'.

That is not a theoretical concern: a defect report against SymbolToWeightCorrectness
was filed because U+2194 arrived as '?' and the lemma appeared to say `->` where it
actually said `<->`. The file compiled cleanly; the report was wrong.

This tool takes a spec of plain-ASCII lines with `@TOKEN@` placeholders, expands them
to code points, writes the file, then RE-READS it and asserts every expansion
survived byte-for-byte before reporting success.

Usage
-----
    python unicode_write.py out.lean spec.txt [--via-python]

Simpler programmatic use: `from unicode_write import write_lean; write_lean(path, text)`
where `text` already contains the real characters (write_lean verifies them).
"""
import os
import sys

TOKENS = {
    "IN": "\u2208",       # element of
    "NOTIN": "\u2209",
    "FORALL": "\u2200",
    "EXISTS": "\u2203",
    "TO": "\u2192",       # arrow
    "IFF": "\u2194",      # iff
    "LARR": "\u2190",
    "LANGLE": "\u27e8",
    "RANGLE": "\u27e9",
    "BULLET": "\u00b7",
    "AND": "\u2227",
    "OR": "\u2228",
    "LE": "\u2264",
    "GE": "\u2265",
    "NE": "\u2260",
    "SUB": "\u2286",
    "SUPSET": "\u2287",
    "INTER": "\u2229",
    "UNION": "\u222a",
    "EMPTY": "\u2205",
    "SUM": "\u2211",
    "PROD": "\u220f",
    "IFFLONG": "\u27fa",
    "LAMBDA": "\u03bb",
    "ALPHA": "\u03b1",
    "BETA": "\u03b2",
    "GAMMA": "\u03b3",
    "DELTA": "\u03b4",
    "EPSILON": "\u03b5",
    "SIGMA": "\u03c3",
    "TOP": "\u22a4",
    "BOT": "\u22a5",
}


def expand(text: str) -> str:
    out = text
    for name, glyph in TOKENS.items():
        out = out.replace("@%s@" % name, glyph)
    return out


def write_lean(path: str, text: str, expand_tokens: bool = True) -> str:
    """Write text to path as UTF-8 (no BOM, LF endings) and verify byte fidelity."""
    if expand_tokens:
        text = expand(text)
    if not text.endswith("\n"):
        text += "\n"
    data = text.encode("utf-8")
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)

    back = open(path, "rb").read()
    if back != data:
        raise IOError("byte fidelity check FAILED for %s" % path)
    decoded = back.decode("utf-8")
    if decoded != text:
        raise IOError("round-trip decode mismatch for %s" % path)
    return path


def _selftest() -> int:
    import tempfile
    path = os.path.join(tempfile.gettempdir(), "_unicode_write_selftest.lean")
    src = "example {A : Type} (a : A) (s : List A) : a @IN@ s @TO@ Prop := fun _ => True\n"
    write_lean(path, src)
    back = open(path, encoding="utf-8").read()
    ok = ("\u2208" in back) and ("\u2192" in back) and ("?" not in back)
    print("selftest:", "PASS" if ok else "FAIL")
    print("  written:", repr(back))
    os.remove(path)
    return 0 if ok else 1


def main() -> int:
    if len(sys.argv) == 2 and sys.argv[1] == "--selftest":
        return _selftest()
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    out, spec = sys.argv[1], sys.argv[2]
    write_lean(out, open(spec, encoding="utf-8").read())
    print("wrote", out, "and verified byte fidelity")
    return 0


if __name__ == "__main__":
    sys.exit(main())
