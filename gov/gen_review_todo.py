"""Only review what has not been reviewed yet.

The first audit used batches ordered by the FLAWED in-degree, so its 1,360 theorems are a different
set from the corrected tier-1 of 880. Re-reviewing the overlap would waste subagents and, worse, could
produce two conflicting verdicts for the same theorem. So: compute T \\ R and batch only that.
"""
import io
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
REV = os.path.join(ZERO, "agent-tmp", "review")

# what has a verdict already
reviewed = set()
for f in os.listdir(REV):
    if f.startswith("verdicts_") and f.endswith(".jsonl"):
        for line in io.open(os.path.join(REV, f), encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            try:
                v = json.loads(line)
            except json.JSONDecodeError:
                continue
            reviewed.add((v.get("file"), v.get("name")))

# corrected tier 1 = every declaration with in-degree >= 1
tier1 = []
for line in io.open(os.path.join(REV, "inv.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    if r["kind"] in ("theorem", "lemma") and r["in_degree"] >= 1:
        tier1.append(r)

todo = [r for r in tier1 if (r["file"], r["name"]) not in reviewed]
todo.sort(key=lambda r: (-r["in_degree"], r["file"], r["line"]))

for f in sorted(os.listdir(REV)):
    if f.startswith("re_"):
        os.remove(os.path.join(REV, f))

BATCH = 80
n = 0
for i in range(0, len(todo), BATCH):
    chunk = todo[i:i + BATCH]
    p = os.path.join(REV, "re_%03d.jsonl" % n)
    with io.open(p, "w", encoding="utf-8", newline="\n") as f:
        for r in chunk:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    n += 1

print("corrected tier-1 (in-degree >= 1): %d" % len(tier1))
print("already reviewed:                  %d" % (len(tier1) - len(todo)))
print("still to review:                   %d" % len(todo))
print("batches:                           %d" % n)
print("in-degree range: %d .. %d" % (todo[0]["in_degree"], todo[-1]["in_degree"]) if todo else "")
