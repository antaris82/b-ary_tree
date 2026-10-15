#!/usr/bin/env python3
"""Documentation tooling: write release/source_inventory.txt, release/module_dag.txt and
release/baseline_received_blobs.txt (git blob ids of the received Task 04 sources, commit
4cc0749).  Provenance column: `received, unchanged` / `received, modified (Task 05)` /
`new (Task 05)`, computed by comparing blob ids with the received commit."""
import os, re, subprocess
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASE = "4cc0749"
ls = subprocess.run(["git", "ls-tree", "-r", BASE], capture_output=True, text=True).stdout
base = {}
for line in ls.splitlines():
    meta, path = line.split("\t", 1)
    if path.endswith(".lean"):
        base[path] = meta.split()[2]
with open("release/baseline_received_blobs.txt", "w") as f:
    f.write(f"# git blob ids of the .lean files of the received repository (commit {BASE})\n")
    for p in sorted(base):
        f.write(f"{base[p]}\t{p}\n")
dirs = ["PrimitiveTree", "TreeNumbers", "TreeFoundation", "DimensionFoundation", "TreeAnalysis",
        "BoundaryTopology", "ReleaseAudit", "Audit"]
files = ["TreeFoundations.lean", "TreeAnalysis.lean"]
for d in dirs:
    files += [d + "/" + f for f in sorted(os.listdir(d)) if f.endswith(".lean")]
def lib(f):
    top = f.split("/")[0]
    if top in ("PrimitiveTree", "TreeNumbers", "TreeFoundation", "DimensionFoundation") or f == "TreeFoundations.lean":
        return "TreeFoundations"
    if top in ("TreeAnalysis", "BoundaryTopology") or f == "TreeAnalysis.lean":
        return "TreeAnalysis"
    return top
dag, inv = [], []
for f in files:
    s = open(f, encoding="utf-8").read()
    imps = re.findall(r"^(?:public\s+)?import\s+(\S+)", s, re.M)
    dag.append(f"{f[:-5].replace('/', '.')} <- {', '.join(imps) if imps else '(Init only)'}")
    blob = subprocess.run(["git", "hash-object", f], capture_output=True, text=True).stdout.strip()
    sha = subprocess.run(["sha256sum", f], capture_output=True, text=True).stdout.split()[0]
    prov = ("new (Task 05)" if f not in base else
            "received, unchanged" if base[f] == blob else "received, modified (Task 05)")
    inv.append(f"{f}\t{lib(f)}\t{s.count(chr(10))} lines\t{prov}\tsha256 {sha}")
open("release/module_dag.txt", "w").write("# Import DAG (module <- direct imports), generated from the sources\n" + "\n".join(dag) + "\n")
open("release/source_inventory.txt", "w").write("# file\tlibrary\tlines\tprovenance\tsha256\n" + "\n".join(inv) + "\n")
print(f"{len(files)} files inventoried")
