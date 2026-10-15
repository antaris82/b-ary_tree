# Appendix-B numbering and back-reference repair — 15 October 2026

## Reader-facing change

- Removed the second visible numbering system ("Plan X.Y") from **all 89** Appendix-B headings. Canonical numbers are **B.1–B.89**.
- Inserted **89 clickable back-references** to actual main-text destinations, using newly labeled main-body subsections where appropriate.
- For B.1–B.4, B.87, and B.88–B.89, no one-to-one main-text subsection exists. These entries explicitly link to Introduction, Limitations, and Conclusion respectively rather than to a fictional §1.1 or §17.2.
- The Introduction now references Appendix B and explains the correspondence. The mapping is topical, not a claim that all 89 entries are distinct kernel theorems.
- Active coverage table and build helper have been converted to canonical B numbering; historical outline IDs remain only as internal stable LaTeX label identifiers for backward-compatible references.

## Audit criteria

- 89/89 unique B headings, 89/89 unique labels, 89/89 main-text targets, seven contextual links (no invented subsections).
- LaTeX compiles with no undefined hyperrefs, labels, or citations.
- No Lean statements, theorem signatures, hypotheses, or proofs were changed.
