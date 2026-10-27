"""Join the adversarial verdicts against the CURRENT inventory before touching any file.

Two things must be filtered out:

1. **Phantoms.** Five of the 45 `delete` verdicts name declarations that do not exist -- they came from
   the first inventory, which parsed docstring prose as declarations (`stated`, `rather`, `applies`,
   `eq_softThresh_of_is_min`, ...). The inventory bug is fixed; the VERDICTS are stale. Reviewer 04
   diagnosed this exactly: "stmt/proof 为空不是「陈述无信息量」，而是「此处没有陈述」".

2. **Items the adversarial pass kept.** 34 of 45 were overturned, mostly because deleting them breaks
   the build (they are passed as arguments to later theorems in the same file, or named in
   `#print axioms` audit lines, where an unknown constant is a hard error).

Only what survives both filters may be removed.
"""
import io
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
REV = os.path.join(ZERO, "agent-tmp", "review")

current = set()
for line in io.open(os.path.join(REV, "inv.jsonl"), encoding="utf-8"):
    r = json.loads(line)
    current.add((r["file"], r["name"]))

verdicts = []
for f in sorted(os.listdir(REV)):
    if not (f.startswith("delverdict_") and f.endswith(".jsonl")):
        continue
    for line in io.open(os.path.join(REV, f), encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        try:
            v = json.loads(line)
        except json.JSONDecodeError:
            continue
        verdicts.append(v)

phantom = [v for v in verdicts if (v.get("file"), v.get("name")) not in current]
real = [v for v in verdicts if (v.get("file"), v.get("name")) in current]

safe = [v for v in real if v.get("verdict") == "delete-safe"]
keep = [v for v in real if v.get("verdict") == "keep"]
rewrite = [v for v in real if v.get("verdict") == "rewrite"]

print("adversarial verdicts: %d" % len(verdicts))
print("  phantom (not in current inventory): %d" % len(phantom))
for v in phantom:
    print("    %s:%s  %s" % (v.get("file"), v.get("line"), v.get("name")))
print("  real: %d" % len(real))
print("    delete-safe: %d" % len(safe))
print("    keep:        %d" % len(keep))
print("    rewrite:     %d" % len(rewrite))
print()
print("=== SAFE TO DELETE ===")
for v in safe:
    print("  %s:%s  %s" % (v.get("file"), v.get("line"), v.get("name")))
    print("      %s" % (v.get("why", "")[:160]))
print()
print("=== REWRITE ===")
for v in rewrite:
    print("  %s:%s  %s" % (v.get("file"), v.get("line"), v.get("name")))
    print("      -> %s" % (v.get("new_stmt", "")[:160]))

out = os.path.join(REV, "delete_safe.json")
io.open(out, "w", encoding="utf-8", newline="\n").write(
    json.dumps({"safe": safe, "keep": keep, "rewrite": rewrite, "phantom": phantom},
               ensure_ascii=False, indent=1))
print()
print("written %s" % out)
