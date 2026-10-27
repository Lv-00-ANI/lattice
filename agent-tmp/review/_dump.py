import json, io
src="batch_000.jsonl"
rows=[]
bad=[]
for i,line in enumerate(open(src,encoding="utf-8"),1):
    line=line.strip()
    if not line: continue
    try:
        rows.append(json.loads(line))
    except Exception as e:
        bad.append((i,str(e)[:100], line[-200:]))
print("rows",len(rows),"bad",len(bad))
with open("_dump_000.txt","w",encoding="utf-8") as f:
    for i,r in enumerate(rows,1):
        doc=(r.get("doc") or "")
        if len(doc)>420: doc=doc[:420]+" ...[doc cut]"
        stmt=r.get("stmt") or ""
        if len(stmt)>600: stmt=stmt[:600]+" ...[cut]"
        f.write(f"=== #{i} {r['file']}:{r['line']} [{r['kind']}] {r['name']}  in_degree={r['in_degree']}\n")
        f.write("DOC: "+doc.replace("\n"," / ")+"\n")
        f.write("STMT: "+stmt.replace("\n"," ; ")+"\n")
        f.write("USERS: "+", ".join(r["users"])+"\n\n")
print("badlines:",bad[:3])
