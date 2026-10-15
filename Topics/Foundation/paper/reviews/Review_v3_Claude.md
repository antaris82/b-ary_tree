# Review v3: Fassung nach Einarbeitung von Review 2

Oct 15, 2026 · @antaris

Vorgänger: Review v2 (Langfassung)

## Ergebnis

Alle 15 Befunde aus Review v2 sind korrekt behoben, und die Korrekturen haben keine neuen Fehler eingeführt. Damit ist die Fassung mathematisch und dokumentarisch reif für eine externe fachliche Begutachtung; aus meiner Sicht steht dem nichts mehr entgegen. Es bleiben nur fünf kosmetische Punkte.

Geprüft habe ich jede geänderte Zeile: 5 Stellen in main.tex, 3 inhaltliche Stellen und 89 Überschriften in Anhang B, 16 geänderte und 9 neue Dateien. Das Lean-Quellarchiv ist byte-identisch mit dem in v1 neu gebauten; die Kernel-Befunde gelten unverändert.

| Prüfung | Ergebnis |
| --- | --- |
| Artefakt-Manifest | alle Hashes korrekt, keine fehlenden Dateien |
| Quellarchiv | identisch mit Review v1/v2 |
| Zeilenangaben der 25 Hauptresultate | 25 von 25 exakt (Kreuztabelle und Beweisketten) |
| Zeilenangaben der Unterabschnittszuordnung | 66 von 66 exakt |
| PDF-Seiten in scope\_89 | 89 von 89, `.md` und `.csv` deckungsgleich |
| compile.log | letzter Lauf ohne ungelöste Verweise und ohne überbreite Zeilen; PDF 46 Seiten |
| Neusatz in meiner Umgebung | keine ungelösten Verweise |

## Status der Befunde aus Review v2

Jede Korrektur habe ich am geänderten Text und, wo nötig, am Lean-Code nachgeprüft, nicht an der Selbstauskunft in SECOND\_REVIEW\_RESOLUTION.md.

| v2 | Befund | Status | Prüfung |
| --- | --- | --- | --- |
| M1 | Gleichung in B.5.2 | behoben | jetzt (s(m), s(n)) ∼ (m, n) wegen s(m)+n = m+s(n) = s(m+n); korrekt |
| M2 | Lean-Namen in §5.2 | behoben | `mkZ_pairEq`, `mkZ_sound`, `mkZ_exact` stimmen mit ihren Lean-Typen überein |
| M3 | Schranke in B.12.4 | behoben | eigene Schranke 2^{B\_{t′}}; Präzisionen k+1+B\_s und k+1+B\_{t′} ergeben je ε\_{k+1}, Summe ε\_k; nachgerechnet |
| M4 | DecidableEq beim Zusammenhang | behoben | §10.4 und B.10.5: koordinatenweise Entscheidung, Gegenfall liefert Trennung, dann Extensionalität; entspricht `Ray.connected_subsingleton` |
| M5 | Transport im Schluss | behoben | §17 nennt die transportierten Körperoperationen |
| M6 | drei Inversenfassungen | behoben | Haupttext, Anhang A und B.12.6 nutzen jetzt alle tₙ = (s\_{N+n})⁻¹ und unterscheiden das punktweise verschobene Produkt von der Äquivalenz mit dem unverschobenen; Modul μ\_s(k+2κ), Produkt-Präzision j+κ wie in Lean |
| D1 | fehlende Belegdateien | behoben | `projS_inS_check.log` liegt bei, SHA-256 `84e41297…dae` wie angegeben, Inhalt stimmt mit dem Kernel-Typ und der Axiomfreiheit überein; `compile.log` liegt bei |
| D2 | Zeilenangaben | behoben | 25 von 25 exakt |
| D3 | revision\_acceptance veraltet | behoben | M18 und Gate 4 beschreiben jetzt die 89-Themen-Fassung |
| D4 | Namensraum | behoben | `no_chart_into_real` |
| D5 | 27 vs. 26 Seiten | behoben | keine „27“ mehr außerhalb der Review-Akten |
| D6 | Rollenkriterium | behoben | klares Kriterium: Daten im Satz = bewiesen bei diesen Daten; Zusatzprinzip = bedingt; eigene Kategorie „Open issue“ |
| D7 | Unterabschnitte, Beweisketten, Anker | behoben | MAIN\_TEXT\_SUBSECTION\_MAP (66 Einträge), MAIN\_RESULT\_PROOF\_CHAINS, `trichotomy_iff_lpo` ergänzt |
| D8 | Anhangsnummerierung | behoben | „B.33. Plan 8.2.“ im PDF |
| D9 | Zitierstil Gilbert | behoben | „G. Gilbert“ |

Auch die Lubarsky-Formulierung aus v1 ist jetzt an das Abstract angeglichen („constructive set theory without Countable Choice“).

## Neue Dokumente und Evidenz

Die neuen Dokumente und Dateien sind inhaltlich korrekt.

- **SECOND\_REVIEW\_RESOLUTION.md** gibt alle 15 v2-Befunde und die sechs Punkte des zweiten ChatGPT-Reviews zutreffend wieder. Es behauptet keinen neuen Kernel-Lauf und trennt eigene von berichteten Prüfungen sauber.
- **MAIN\_RESULT\_PROOF\_CHAINS.md**: Alle 25 Ketten habe ich gegen die Beweise im Hauptteil gelesen; jede trifft die tatsächliche Beweisstruktur. Eine kleine Unschärfe steht bei Nr. 5 (siehe unten).
- **MAIN\_TEXT\_SUBSECTION\_MAP.md**: Alle 66 Zeilenangaben zeigen exakt auf die jeweilige `\subsection`. Die Themenzuordnung ist plausibel.
- **compile.log**: Der letzte von drei Läufen ist sauber; Warnungen gibt es nur in den ersten Läufen, wie bei LaTeX üblich.
- **build\_scope.py** liest `main.aux`, das nicht beiliegt. Das Skript läuft also erst nach einem eigenen Neusatz; das ist vertretbar, sollte aber im README stehen.

Alle in den neuen Dokumenten zitierten Lean-Namen existieren im Quelltext; die Signaturblöcke in proof\_correspondence.md sind unverändert und wurden in v2 bereits vollständig von Lean bestätigt.

## Verbleibende Kleinigkeiten und Empfehlung

Keiner dieser Punkte betrifft die Mathematik des Manuskripts.

| Nr. | Stelle | Punkt |
| --- | --- | --- |
| R1 | MAIN\_TEXT\_SUBSECTION\_MAP.md | Die Plan-Themen 6.7, 8.9, 13.3, 14.5 und 16.7 werden im Haupttext behandelt (z. B. 13.3 im zweiten Absatz von §13.2), sind in der Tabelle aber keinem Unterabschnitt zugeordnet. Plan 1.x und 17.x haben im Hauptteil keine Unterabschnitte; das ist folgerichtig |
| R2 | scope\_89, Plan 13.4 | UC ⇔ CA ist als „Proved with the explicit data/hypotheses“ eingeordnet; nach dem eigenen Kriterium passt „Proved equivalence; principle not asserted“ besser, wie bei 14.1–14.3 |
| R3 | MAIN\_RESULT\_PROOF\_CHAINS.md, Nr. 5 | „Integer-order compatibility … furnish the field laws“: für die Körpergesetze wird die Ordnung nicht gebraucht, nur Integrität und positive Nenner |
| R4 | build\_scope.py | benötigt `main.aux`; im README vermerken |
| R5 | Titelseite | Autor, Affiliation und E-Mail sind noch Platzhalter; vor einer Einreichung zu füllen |

Empfehlung: R1 bis R4 bei Gelegenheit nachziehen, R5 vor jeder Einreichung. Danach ist das Paket aus meiner Sicht abgeschlossen. Offen bleibt nur die bewusst optionale Formalisierung des Ausschlusses von −1 im unären Fall; sie ist für keinen der 25 Hauptsätze nötig.
