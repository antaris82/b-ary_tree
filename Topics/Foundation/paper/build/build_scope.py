from pathlib import Path
import csv, re

p = Path(__file__).resolve().parent
with (p / 'scope_89.csv').open(newline='') as f:
    rows = list(csv.DictReader(f))
body = (p / 'extended_proof_details.tex').read_text()
aux = (p / 'main.aux').read_text()
heads = re.findall(r'\\subsection\{(.*?)\}\\label\{(supp:[^}]+)\}', body)
assert len(rows) == len(heads) == 89

for i, (row, (title, label)) in enumerate(zip(rows, heads), 1):
    assert row['appendix_section'] == f'B.{i}'
    assert row['appendix_heading'] == title
    needle = r'\\newlabel\{' + re.escape(label) + r'\}\{\{([^{}]+)\}\{(\d+)\}'
    match = re.search(needle, aux)
    assert match and match.group(1) == f'B.{i}', (i, match)
    link = re.search(r'\\hyperref\[' + re.escape(row['main_label']) + r'\]', body)
    assert link, (i, row['main_label'])
    mainneedle = r'\\newlabel\{' + re.escape(row['main_label']) + r'\}\{\{([^{}]+)\}\{(\d+)\}'
    main = re.search(mainneedle, aux)
    assert main, (i, row['main_label'])
    row['pdf_page'] = match.group(2)
    row['main_section_number'] = main.group(1)
    row['main_pdf_page'] = main.group(2)

with (p / 'scope_89.csv').open('w', newline='') as f:
    writer = csv.DictWriter(f, fieldnames=rows[0].keys())
    writer.writeheader()
    writer.writerows(rows)
print('Validated all 89 B headings, pages and main-text links.')
