"""C1: mechanical detection of non-load-bearing proofs.

Three shapes, each independently checkable:

  S1  proof body is a bare reference to another declaration
        theorem foo ... := other_bar
        theorem foo ... := other_bar a b c
      i.e. the whole proof is one application, with no tactic block.

  S2  declared hypotheses never appear in the body
      (`h0 : P` in the signature, `h0` absent from everything after `:=`/`by`)

  S3  conclusion is restated definitionally  (`:= rfl`, `by rfl`, `:= Iff.rfl`)

This is a report, not a verdict: S1 on a genuinely cleaner restatement is a defect,
S1 on an interface wrapper is fine. The output is meant to be read, and every hit carries
its file:line so the judgement can be re-derived.
"""
import io, os, re, sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _REPO


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if not depth:
            out.append(src[i])
        i += 1
    return "".join(out)


THM = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(theorem|lemma)[ \t]+([A-Za-z0-9_'.]+)(.*?)(:=| by)(.*?)(?=\n[ \t]*(?:@\[|theorem|lemma|def|abbrev|structure|inductive|instance|class|end\b|namespace)|\Z)",
    re.S)

s1, s2, s3 = [], [], []

for root, _, files in os.walk(os.path.join(NEW, "Lattice")):
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, NEW).replace("\\", "/")
        if "Reference" in rel:
            continue
        code = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
        for m in THM.finditer(code):
            kind, name, sig, sep, body = m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)
            line = code[: m.start()].count("\n") + 1
            b = body.strip()
            # S1: single application, no tactics
            if b and "by" not in b and not b.startswith("by"):
                if re.fullmatch(r"[A-Za-z0-9_'.]+(\s+[A-Za-z0-9_'().\[\]{}<>,]+)*", b) and len(b.split()) <= 8:
                    s1.append((rel, line, name, b[:80]))
            # S2: declared binders never used in body
            binders = re.findall(r"\(([a-zA-Z_][A-Za-z0-9_']*)\s*:", sig)
            for bd in binders:
                if bd and not re.search(r"(?<![\w.'])" + re.escape(bd) + r"(?![\w'])", body):
                    s2.append((rel, line, name, bd))
                    break
            # S3: rfl-level
            if re.fullmatch(r"\s*rfl\s*", b) or re.fullmatch(r"\s*by\s+rfl\s*", b):
                s3.append((rel, line, name))

print("=" * 70)
print("S1  proof body is a bare reference to another declaration: %d" % len(s1))
print("=" * 70)
for rel, line, name, b in s1[:40]:
    print("  %-46s:%-5d %-38s  := %s" % (rel, line, name, b))
if len(s1) > 40:
    print("  ... (%d more)" % (len(s1) - 40))

print()
print("=" * 70)
print("S2  a declared hypothesis never appears in the body: %d" % len(s2))
print("=" * 70)
for rel, line, name, bd in s2[:40]:
    print("  %-46s:%-5d %-38s  unused: %s" % (rel, line, name, bd))
if len(s2) > 40:
    print("  ... (%d more)" % (len(s2) - 40))

print()
print("=" * 70)
print("S3  conclusion proved by rfl: %d" % len(s3))
print("=" * 70)
for rel, line, name in s3[:40]:
    print("  %-46s:%-5d %s" % (rel, line, name))
if len(s3) > 40:
    print("  ... (%d more)" % (len(s3) - 40))
