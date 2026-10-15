from pathlib import Path
import csv, re

p=Path(__file__).resolve().parent
body=(p/'main.tex').read_text()
aux=(p/'main.aux').read_text()
with (p/'scope_89.csv').open(newline='') as f:
    rows=list(csv.DictReader(f))
assert len(rows)==89
heads=re.findall(r'\\subsubsection\*\{([^}]*)\}\\phantomsection\\label\{(supp:[^}]+)\}',body)
assert len(heads)==89, (len(heads),'detail headings')
by_label={row['detail_label']: row for row in rows}
assert len(by_label)==89
new_rows=[]
for i,(heading,label) in enumerate(heads,1):
    row=by_label[label]
    assert row['detail_heading']==heading, (i,row,heading,label)
    def newlabel(name):
        m=re.search(r'\\newlabel\{' + re.escape(name) + r'\}\{\{[^{}]*\}\{(\d+)\}',aux)
        assert m, ('not in compiled aux',i,name)
        return int(m.group(1))
    d=newlabel(label);main=newlabel(row['main_label'])
    assert d>=main, (i,d,main)
    row['pdf_page']=d
    row['main_pdf_page']=main
    new_rows.append(row)
rows=new_rows
with (p/'scope_89.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
print('Verified all 89 inline mathematical details and actual PDF pages.')
