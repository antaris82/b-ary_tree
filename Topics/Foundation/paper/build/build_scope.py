from pathlib import Path
import re,csv
folder=Path(__file__).resolve().parent
rows=list(csv.DictReader((folder/'scope_89.csv').open()))
source=(folder/'extended_proof_details.tex').read_text()
heads=dict(re.findall(r'\\subsection\{Plan (\d+\.\d+)\. ([^}]*)\}\\label\{supp:[^}]+\}',source))
aux=(folder/'main.aux').read_text()
pages={a.replace('-','.'):int(b) for a,b in re.findall(r'\\newlabel\{supp:(\d+-\d+)\}\{\{[^{}]*\}\{(\d+)\}',aux)}
assert len(rows)==len(heads)==len(pages)==89
for r in rows:
 n=r['section'];assert n in heads and n in pages
 r['appendix_heading']=heads[n];r['pdf_page']=pages[n]
with (folder/'scope_89.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print('Verified 89/89 Appendix B headings and PDF page labels. Regenerate the Markdown scope table from CSV before release if a future edit shifts pages.')
