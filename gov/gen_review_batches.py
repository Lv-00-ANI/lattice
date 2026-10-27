"""gov/gen_review_batches.py -- split theorems into review batches, highest in-degree first.

Ordering by in-degree is the operational form of 看用途: the theorems other theorems depend on are
reviewed first, because a wrong strength there propagates. A theorem nothing references is reviewed
last -- it can still be a placeholder, but it cannot mislead downstream.

Each batch is a JSONL file the reviewer reads and a verdicts file it writes. Returning verdicts in the
subagent's response would blow up the transcript, so the contract is file-to-file.
"""
import io
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
OUT = os.path.join(ZERO, "agent-tmp", "review")
BATCH_SIZE = 80

recs = [json.loads(l) for l in io.open(os.path.join(OUT, "inv.jsonl"), encoding="utf-8")]

# only proof-bearing declarations: a `def` has no proof to be weak
proofs = [r for r in recs if r["kind"] in ("theorem", "lemma")]
proofs.sort(key=lambda r: (-r["in_degree"], r["file"], r["line"]))

# clear old batches
for f in sorted(os.listdir(OUT)):
    if f.startswith("batch_") and f.endswith(".jsonl"):
        os.remove(os.path.join(OUT, f))

n = 0
for i in range(0, len(proofs), BATCH_SIZE):
    chunk = proofs[i:i + BATCH_SIZE]
    p = os.path.join(OUT, "batch_%03d.jsonl" % n)
    with io.open(p, "w", encoding="utf-8", newline="\n") as f:
        for r in chunk:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    n += 1

print("proof-bearing declarations: %d" % len(proofs))
print("batches: %d  (size %d)" % (n, BATCH_SIZE))
print("in-degree range: %d .. %d" % (proofs[0]["in_degree"], proofs[-1]["in_degree"]))
print("with in-degree >= 1: %d" % sum(1 for r in proofs if r["in_degree"] >= 1))
