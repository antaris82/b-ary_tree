#!/usr/bin/env python3
from pathlib import Path
import csv,re
p=Path(__file__).resolve().parents[1]
docs=p/"docs"
tex=(p/"main.tex").read_text()
aux=(p/"main.aux").read_text()
lines=tex.splitlines()
def page(label):
    m=re.search(r'\\newlabel\{'+re.escape(label)+r'\}\{\{[^{}]*\}\{(\d+)\}',aux)
    if not m: raise RuntimeError("Missing aux label: "+label)
    return int(m.group(1))
with (docs/"scope_89.csv").open(newline="") as f: rows=list(csv.DictReader(f))
headings=re.findall(r'\\subsubsection\*\{([^}]*)\}\\phantomsection\\label\{(supp:[^}]+)\}',tex)
assert len(rows)==len(headings)==89
by={r["detail_label"]:r for r in rows}
assert set(by)=={l for _,l in headings}
for h,l in headings:
    r=by[l];assert r["detail_heading"]==h
    r["pdf_page"]=page(l);r["main_pdf_page"]=page(r["main_label"])
    assert r["pdf_page"]>=r["main_pdf_page"]
rows=[by[l] for _,l in headings]
with (docs/"scope_89.csv").open("w",newline="") as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
md=["# Integrated proof-location map — 89 mathematical treatments","","Generated from the current compiled LaTeX labels; this is navigation, not a new Lean kernel check.","","| In-text detail | Related main discussion | PDF page | Sources and claim status |","|---|---|---:|---|"]
for r in rows:
    md.append("| **{}** ({}) | {} ({}) | {} | {}; *{}* |".format(r["detail_heading"],r["detail_label"],r["main_discussion"],r["main_label"],r["pdf_page"],r["source_files"],r["mathematical_role"]))
(docs/"scope_89.md").write_text("\n".join(md)+"\n")
theorems=[n for n,l in enumerate(lines,1) if re.search(r'\\begin\{(theorem|proposition|lemma|corollary)\}',l)]
assert len(theorems)==25
for name in ("25_MAIN_RESULTS_CROSSWALK.md","MAIN_RESULT_PROOF_CHAINS.md"):
    f=docs/name;s=f.read_text(); it=iter(theorems)
    s,count=re.subn(r'main\.tex:\d+\)',lambda m:"main.tex:"+str(next(it))+")",s)
    assert count==25,(name,count)
    f.write_text(s)
old=(docs/"MAIN_TEXT_SUBSECTION_MAP.md").read_text()
topic={}
for l in old.splitlines():
    v=[x.strip() for x in l.strip().strip("|").split("|")]
    if len(v)>=6 and v[0].isdigit():topic[v[2]]=v[4]
sections=[];sec=None
for n,l in enumerate(lines,1):
    m=re.match(r'\\section\{([^}]+)\}',l)
    if m:sec=m.group(1)
    m=re.match(r'\\subsection\{([^}]+)\}',l)
    if m:sections.append((sec,m.group(1),n,"main:sub-" in l))
assert sum(t for *_,t in sections)==63
assert len(sections)==72,len(sections)
out=["# Main-text subsection map — current manuscript","","Includes 63 established numbered mathematical subsections, five motivation subsections, and four technical appendix subsections. The 89 inline treatments have a separate navigation map.","","| No. | Section | Subsection | main.tex line | Original plan topics | Status |","|---:|---|---|---:|---|---|"]
for i,(sec,title,n,tracked) in enumerate(sections,1):
    status="main mathematics" if tracked else ("motivation" if sec.startswith("Motivation") else "technical appendix")
    out.append("| {} | {} | {} | {} | {} | {} |".format(i,sec,title,n,topic.get(title,"—"),status))
(docs/"MAIN_TEXT_SUBSECTION_MAP.md").write_text("\n".join(out)+"\n")
print("PASS: 25 results, 72 subsections, 89 PDF destinations")
