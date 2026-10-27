"""Extract the `delete` verdicts WITH their full source, for adversarial re-checking.

Deleting a theorem is destructive. A reviewer that mislabelled a real theorem as vacuous would make the
library worse, and the loss would be silent. So every `delete` verdict gets a second, adversarial pass:
the reviewer's job is to argue that the FIRST reviewer was WRONG.

The source is attached because a verdict without the statement and proof in front of it cannot be
checked -- and the first pass already showed that docstrings sometimes claim the opposite of what the
statement says.
"""
import io
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
REV = os.path.join(ZERO, "agent-tmp", "review")
LAT = os.path.join(ZERO, "Lattice")

inv = {}
for line in io.open(os.path.join(REV, "inv.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    inv[(r["file"], r["line"], r["name"])] = r

dels = []
for f in sorted(os.listdir(REV)):
    if not (f.startswith("verdicts_") and f.endswith(".jsonl")):
        continue
    for line in io.open(os.path.join(REV, f), encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        try:
            v = json.loads(line)
        except json.JSONDecodeError:
            continue
        if v.get("verdict") != "delete":
            continue
        rec = inv.get((v.get("file"), v.get("line"), v.get("name")), {})
        dels.append({
            "file": v.get("file"),
            "line": v.get("line"),
            "name": v.get("name"),
            "doc": rec.get("doc", ""),
            "stmt": rec.get("stmt", ""),
            "proof": rec.get("proof", ""),
            "in_degree": rec.get("in_degree", 0),
            "users": rec.get("users", []),
            "first_verdict_why": v.get("F_content", "") or v.get("note", ""),
        })

# attach neighbouring lines so the reviewer can see if a following theorem carries the content
for d in dels:
    p = os.path.join(LAT, d["file"])
    try:
        src = io.open(p, encoding="utf-8").read().split("\n")
    except OSError:
        continue
    lo = max(0, (d["line"] or 1) - 6)
    hi = min(len(src), (d["line"] or 1) + 12)
    d["context"] = "\n".join(src[lo:hi])

dels.sort(key=lambda d: (-d["in_degree"], d["file"] or ""))

for f in sorted(os.listdir(REV)):
    if f.startswith("verify_del_"):
        os.remove(os.path.join(REV, f))

BATCH = 11
n = 0
for i in range(0, len(dels), BATCH):
    chunk = dels[i:i + BATCH]
    p = os.path.join(REV, "verify_del_%02d.jsonl" % n)
    with io.open(p, "w", encoding="utf-8", newline="\n") as f:
        for d in chunk:
            f.write(json.dumps(d, ensure_ascii=False) + "\n")
    n += 1

print("delete verdicts: %d" % len(dels))
print("batches: %d (size %d)" % (n, BATCH))
print("with in-degree >= 1: %d" % sum(1 for d in dels if d["in_degree"] >= 1))
