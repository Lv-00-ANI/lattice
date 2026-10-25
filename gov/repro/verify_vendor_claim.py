"""Verify the two claims just written into STATE-2026-10 §2.3:

  * no file is named after a commercial model / vendor;
  * the counts 9 (chain-importing) and 194 (edges) are right.

A document that corrects one false claim must not introduce another.
"""
import io
import os
import re
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _REPO
LAT = os.path.join(NEW, "Lattice")

VENDORS = ["GPT", "Claude", "Gemini", "Llama", "BERT", "T5", "Mistral", "Qwen",
           "DeepSeek", "PaLM", "Chinchilla", "OpenAI", "Anthropic", "Google",
           "Transformer", "BERT", "ResNet", "VGG", "AlexNet"]

arch = []
for sec in ("Architectures", "Attention"):
    d = os.path.join(LAT, "Lib", sec)
    for root, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                arch.append(os.path.join(root, f))

hit_vendor = []
for p in arch:
    rel = os.path.basename(p)
    for v in VENDORS:
        if v.lower() in rel.lower():
            hit_vendor.append((os.path.relpath(p, LAT), v))
print("files named after a vendor/model: %d" % len(hit_vendor))
for rel, v in hit_vendor:
    print("  %-50s (%s)" % (rel, v))

# content scan: do any of them prove things about a named model?
content_hit = []
for p in arch:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for v in VENDORS:
        if re.search(r"\b" + re.escape(v) + r"\b", t):
            content_hit.append((os.path.relpath(p, LAT), v))
print("\nfiles MENTIONING a vendor/model in their text: %d" % len(content_hit))
for rel, v in content_hit[:10]:
    print("  %-50s (%s)" % (rel, v))

# recount the two numbers
CHAIN = ("Lattice.Core", "Lattice.Lift", "Lattice.Geo")
n_chain = 0
for p in arch:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    if any(i.startswith(CHAIN) for i in re.findall(r"(?m)^import\s+(Lattice\.\S+)$", t)):
        n_chain += 1
n_edges = 0
for root, _, fs in os.walk(LAT):
    rr = os.path.relpath(root, LAT).replace("\\", "/")
    if rr.startswith("Lib/Architectures") or rr.startswith("Lib/Attention"):
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
        n_edges += len(re.findall(
            r"(?m)^import\s+Lattice\.Lib\.(?:Architectures|Attention)\.\S+$", t))
print("\nchain-importing architecture files: %d (doc says 9)" % n_chain)
print("incoming import edges: %d (doc says 194)" % n_edges)
