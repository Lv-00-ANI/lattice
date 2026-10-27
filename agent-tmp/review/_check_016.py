import json, io
HP = r"C:\Users\xingg\Desktop\agent\lattice-new\agent-tmp\review"
rows = [json.loads(l) for l in io.open(HP + r"\batch_016.jsonl", encoding="utf-8") if l.strip()]
vs = [json.loads(l) for l in io.open(HP + r"\verdicts_016.jsonl", encoding="utf-8") if l.strip()]
keys = ["file", "line", "name", "verdict", "A_strength", "B_missing", "C_hypotheses", "D_downgrade", "E_coverage", "F_content", "note"]
ok = ["keep", "strengthen", "downgrade", "delete", "register"]
assert len(rows) == len(vs) == 80, (len(rows), len(vs))
bad = []
for i, (r, v) in enumerate(zip(rows, vs), 1):
    if list(v.keys()) != keys: bad.append((i, "keys", list(v.keys())))
    if (v["file"], v["line"], v["name"]) != (r["file"], r["line"], r["name"]):
        bad.append((i, "id-mismatch", v["name"], r["name"]))
    if v["verdict"] not in ok: bad.append((i, "verdict"))
    if v["verdict"] == "keep":
        if any(str(v[k]).strip() for k in keys[4:9]): bad.append((i, "keep-fields-not-empty"))
    else:
        for k in keys[4:9]:
            if not str(v[k]).strip(): bad.append((i, "missing-" + k))
    if not v["note"].strip(): bad.append((i, "note-empty"))
print("problems:", bad)
from collections import Counter
print(Counter(v["verdict"] for v in vs))
for i, v in enumerate(vs, 1):
    if v["verdict"] != "keep":
        print(i, v["verdict"], v["file"] + ":" + str(v["line"]), v["name"])
