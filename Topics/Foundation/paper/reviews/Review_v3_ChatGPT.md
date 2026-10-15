# Dritter mathematischer Vollreview — Task 06 Foundation Long Form, Version 2

**Prüfdatum:** 15. Oktober 2026  
**Prüfgegenstand:** `TASK06_FOUNDATIONS_LONGFORM_V2_REVIEW_RESOLVED.zip`  
**Vergleich:** `TASK06_FOUNDATIONS_LONGFORM_89_PROOFS.zip` (vorherige Langfassung)  
**Formaler Referenzstand:** beigefügtes `evidence/task06_frozen_source.tar.gz`, Lean 4.28.0; unveränderter Quellenfingerabdruck `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.

## 0. Urteil und Reichweite

**ACCEPT WITH MINOR PUBLICATION REPAIRS — keine neue mathematische Fehlbehauptung in einem der 25 Hauptsätze festgestellt.** Die in den beiden Vorreviews konkret bezeichneten mathematischen Präzisionsfehler M1–M6 sind in der gelieferten Version **an den tatsächlichen Textstellen** korrigiert. Die neun dokumentarischen Punkte D1–D9 sind, soweit durch Paketinhalt und maschinelle Gegenproben überprüfbar, ebenfalls behoben. Für die vorliegenden, in ihren Voraussetzungen beschränkten Hauptsätze ist kein zusätzlicher verpflichtender Lean-Satz erkennbar.

**Wichtig:** Dies ist eine Quellen- und Manuskriptbegutachtung, **kein erneuter vollständiger Lean-Kernel-Build und keine externe fachliche Peer-Review**. Die vorhandenen Release-Logs belegen den gemeldeten historischen Lauf; ohne installierte Lean-Toolchain kann ich seine 3.014 Deklarationen hier nicht neu elaborieren oder vom Kernel prüfen. Ein erfolgreiches Lean-Theorem validiert zudem seinen elaborierten Typ, nicht automatisch jede frei formulierte Prosa.

**„Vollreview“ meint hier:** vollständiger Vergleich des gelieferten Manuskripts und sämtlicher Begleitdokumente gegen die Vorversion; systematische Prüfung der 25 Satzumgebungen, 62 Haupttext-Unterabschnitte, vier zusätzlichen Beweis-Unterabschnitte und 89 Appendix-B-Abschnitte, besonders der sämtlichen in Version 2 geänderten mathematischen Passagen; Einzelabgleich aller 289 benannten Deklarationsfundstellen mit dem unveränderten Code; technische Paket-, Verweis-, Textsatz- und Integritätskontrollen. Es bedeutet **nicht** die unabhängige, zeilenweise Neuentwicklung von 3.014 Kernelbeweisen oder eine satzgenaue vollständige Lektüre aller teilweise zugangsbeschränkten Literaturmonographien.

## 1. Reproduzierte Prüfungen

| Prüfung | Eigener Befund | Interpretation |
|---|---|---|
| ZIP-Inventar | 60 reguläre Dateien, sämtliche für den Bericht notwendigen Begleitunterlagen vorhanden | Tatsächlicher Lieferumfang, ohne Verzeichnisplätze |
| Integritätsmanifest | **60/60 SHA-256-Einträge korrekt** | Das ausgelieferte Verzeichnis stimmt bytegenau zu seinem eigenen Manifest |
| Eingebetteter Task-06-Quellstand | 107 TAR-Einträge; 75 vom Release-Fingerprint erfasste Dateien | Keine inhaltliche Veränderung gegenüber dem eingefrorenen mathematischen Fundament |
| Quellenfingerabdruck | **exakter Treffer** `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e` | Unabhängig mit dem im Release-Skript festgelegten SHA-256-Verfahren berechnet |
| Statischer Quellencheck | **PASS**; 64 mathematische Quellen, 64 vom Wurzelmodul erreichbar | Keine von diesem Prüfer erkannten verbotenen Tokens, Fremdimporte oder numerischen Literale; **kein** Kernelnachweis |
| Mathematische Hauptresultate | **25/25** ausgezeichnete `theorem`-/`proposition`-/`lemma`-/`corollary`-Umgebungen | Titel, mathematische Aussage, Voraussetzungen, informelle Beweisgänge und Quellenanker kontrolliert |
| Hauptsatz-Zeilenverweise | **25/25 korrekt** | Jetzt exakt die `\\begin{...}`-Zeilen aus `main.tex` |
| Haupttext-Unterabschnitte | **62/62** durch `MAIN_TEXT_SUBSECTION_MAP.md` verzeichnet | Dazu vier gesonderte technische Abschnitte in Appendix A |
| Originale Gliederung | **89/89** eindeutig gelabelte `Plan X.Y`-Themen | Das sind Themenbehandlungen, nicht 89 separat kernelgeprüfte Theoreme |
| Appendix-B-Seitenverweise | **89/89** im gelieferten PDF lokalisiert | Drei automatisierte exakte Textsuchanfragen scheiterten nur an Math- und Apostroph-Typografie; auf den genannten Seiten manuell gegengeprüft |
| Paper–Lean-Korrespondenz | **289/289** Referenzen mit Quelldatei, -zeile und Deklarationsbezeichner vereinbar | 252 unveränderte plus 37 neue Task-06-Referenzen; die Bedeutung des gesamten Theorems muss weiter über vollständige Signaturen gelesen werden |
| PDF | **46 Seiten**, Inhaltsdarstellung plausibel | Stichübergreifende visuelle Sichtung und PDF-Text-/Seitenkontrolle |
| Unabhängige LaTeX-Rekompilation | **PASS**, 46 Seiten | Keine undefinierten Querverweise, fehlenden Zitate, Overfull-Boxen oder unbekannten Befehle |
| Historischer Task-06-Kernelbericht | Im Paket, Konsistenz mit Fingerabdruck bestätigt | **Nicht selbst neu ausgeführt** |
| `compile.log`, `evidence/projS_inS_check.log` | **Beide enthalten** | Ehemaliger D1-Paketmangel behoben; `projS_inS_check.log` bleibt historischer Einzelnachweis |

Die neu kompilierten PDF-Bytes müssen wegen Metadaten/Build-Zeitstempeln nicht mit den gelieferten PDF-Bytes übereinstimmen; bei beiden sind 46 Seiten und dieselben mathematischen Quelldateien bestätigt.

## 2. Adversarialer Vergleich M1–M6

| ID | Originalbefund | Gegenprobe in Version 2 | Ergebnis |
|---|---|---|---|
| **M1** | Verunstaltete Nachfolgeridentität bei Ganzzahlnormalisierung | `extended_proof_details.tex:60`: `(s(m),s(n))\sim(m,n)` aus `s(m)+n=m+s(n)=s(m+n)`; korrekte Paaräquivalenz und Terminierung | **Behoben** |
| **M2** | Falsche Zuordnung der drei `mkZ`-Sätze | `main.tex:117`: `mkZ_pairEq` = ursprüngliches Paar äquivalent zur Normalform; `mkZ_sound` = verwandte Paare gleiche Normalform; `mkZ_exact` = gleiche Normalform verwandte Paare | **Behoben** |
| **M3** | Bei Produktkongruenz wurde Schranke von `t` unzulässig für `t'` benutzt | `extended_proof_details.tex:201–206`: unabhängige Faktorenbounds `B_s`, `B_{t'}`, getrennte Indizes `k+1+B_s` und `k+1+B_{t'}`; Summation ergibt `ε_k` | **Behoben; mathematisch wichtiger Reparaturpunkt** |
| **M4** | Versteckte `DecidableEq α`-Prämisse im Zusammenhangssatz | `main.tex:421` und `extended_proof_details.tex` Plan 10.5: Buchstaben-Gleichheit wird für jede Koordinate entschieden, negative Fälle geben explizite Zylindertrennung; erst dann Funktions-Extensionalität | **Behoben** |
| **M5** | Schluss suggerierte unmittelbar aus Pfaden definierte rationalen Körperoperationen | `main.tex:767` (Conclusion): expliziter Transport aus dem vorher aufgebauten Hilfsbruchkörper | **Behoben** |
| **M6** | Resampling-Inverses und Originalrepräsentant unpräzise vermischt | `main.tex:589` und Appendix A / Plan 12.6: `t_n=(s_{N+n})^{-1}`, punktweise nur `s_{N+n}t_n=1`; das ursprüngliche Produkt `s_nt_n` ist der konstanten Einsfolge **äquivalent** | **Behoben** |

### Mathematische Gegenrechnung zu M3

Bei `s∼s'` und `t∼t'` ist

`|s_n t_n - s'_n t'_n| ≤ |s_n| |t_n-t'_n| + |t'_n| |s_n-s'_n|`.

Für verschiedene Repräsentanten werden **zwei getrennt konstruierte** Eventualschranken gebraucht. Mit `|s_n|≤2^{B_s}`, `|t'_n|≤2^{B_{t'}}` und Präzisionsindizes `k+1+B_s`, `k+1+B_{t'}` werden beide Summanden `≤ε_{k+1}` und ihre Summe `≤ε_k`. Das ist in der Revision explizit und korrekt. Die alte Ableitung aus einem gemeinsamen `B_t` war unzureichend.

### Mathematische Gegenrechnung zu M6

Für einen positiv getrennten Repräsentanten `s_n≥ε_κ` ab `n≥N` gilt mit `t_n=(s_{N+n})^{-1}`: `|t_n|≤2^κ`; die Kehrwertdifferenz ist durch `2^{2κ}|s_{N+m}-s_{N+n}|` kontrolliert. Daher ist `μ_t(j)=μ_s(j+2κ)` ein zulässiger Cauchy-Modul. Für das Produkt mit dem alten Repräsentanten wird gesondert `s_n t_n-1=(s_n-s_{N+n})t_n` kontrolliert. Der Text macht daraus **keine falsche punktweise Einsgleichung** mehr.

## 3. Mathematisches Gesamturteil nach Themen

**Baumkombinatorik und Zahlenkonstruktionen.** Eindeutigkeit endlicher Wurzelpfade, ungerichtete Zyklenfreiheit mittels Schnittkante, Pfadsumme als Tiefe, unäre Induktion, geordneter Halbring, normalisierte ganzzahlige Differenzpaare und geordnete rationale Pfadtripelklassen sind korrekt spezifiziert. `TreeN` entsteht aus unären Wörtern; die volle Tripelrepräsentation jedes Bruchs benötigt zwei verschiedene Kinderbuchstaben. Die Körperoperationen werden aus dem internen Bruchquotienten transportiert, sie entstehen nicht direkt aus bloßer Adjazenz. Die Isomorphie der rationalen Körper über verschiedenen Alphabeten ist **keine** Isomorphie der entsprechenden Bäume.

**Algebraische Dimension.** Bei `b>0` ist `F_b=K^b`, `L_b=K u_b`, `S_b=ker Σ`. Die ausdrücklich konstruierten Basen beweisen den freien Rang `1` und `b−1`. Die Task-06-Module beweisen die Symmetrie/Bilinearität von `B(x,y)=Σ x_i y_i`, die komplementären linearen Projektionen, ihre Bild-/Kernbeziehungen und `B`-Orthogonalität der **Unterräume**. Keine Positivdefinitheit, kein kanonischer metrischer Abstand, keine topologische oder physikalische Dimension wird dadurch behauptet. Die Spezialfälle `b=0` (Bilinearität ohne Direktheit) und `b=1` (transversaler Nullraum) sind richtig abgegrenzt.

**Abzählbare Verzweigung.** Im endlich unterstützten Modul sind die Differenzvektoren `e_{i+1}−e_0` eine abzählbare algebraische Basis des transversalen Nullsummenraums. Der überall-eins-Vektor liegt nicht in diesem Modul; die Uniformlinien sind unter Zero-Padding nicht kompatibel. Das ist eine bewiesene **spezifische Obstruktion**, kein allgemeiner Nichtexistenzsatz über andere Grenzräume.

**Baumrand und Automorphismen.** Die Präfixtopologie, clopen Zylinder, die echte Differenz zwischen `⋃_{b<ω}∂T_b` und `∂T_ω`, fehlende lokale Kompaktheit im zählbar verzweigten Fall und die niveauweise transitive Wirkung sind passend dargestellt. `Ray.connected_subsingleton` wird nun mit der notwendigen `DecidableEq`-Prämisse erläutert. Der Kartenausschluss zur konstruierten reellen Geraden bleibt **bedingt** durch `IntervalsConnected K`. Die Behauptung, jeder Automorphismus sei niveauweise, wurde bereits formal widerlegt; die allgemeine Klassifikation wird nicht vorgetäuscht.

**Konstruktiver Cauchy-Quotient.** Der Text trennt Moduldaten von einer bloßen Cauchy-Eigenschaft. Er verwendet einen bestimmten Quotiententräger und das projektspezifische `TOField` mit Entscheidbarkeit rationaler Konusprädikate und `archBound`. Die unbedingte Ringstruktur, konstruktive Ordnung/Apartheit, Inversion aus positiver Trennung, Dichte, explizit getrackte Grenzwerte und Suprema mit `SupData` sind korrekt relativ zu den angegebenen Voraussetzungen. Vollständigkeit für **alle** Cauchy-Folgen mit Modul ist nicht ohne Zusatzbedingungen behauptet; `UC↔CauchyApprox` ist ein unbedingtes Äquivalenzergebnis, nicht ein Beweis von `UC`.

**Logische Prinzipien.** Die Äquivalenzen von bloßer Nichtequality-Invertierbarkeit und Markov-Prinzip, Zero-or-Apartness/Trichotomie und LPO sowie Zero-Entscheidbarkeit und WLPO sind mit ihren Booleschen Tests und Fehlerbudgets kenntlich. `UnrestrictedLUB⇒WLPO` und `BoundedMonotoneConvergence⇒LPO` sind nur **einseitige** Reduktionen. Keine der Konversen oder Unabhängigkeitsaussagen wird behauptet.

## 4. Verbleibende Hinweise und Freigabevorbehalte

### P2 — Mathematischer Veröffentlichungsstatus

1. **Nicht kernelgeprüfte Nebenfolgerung `-1` bei unären Tripeln.** Der informelle Beweis ist korrekt: `numer(t)=-denom(t)` erzwingt Gleichheit der Längen von `P_1` und `P_3`, im unären Fall also `P_1=P_3`, entgegen der Gültigkeitsbedingung. Der eigene Lean-Satz fehlt. Der Text kennzeichnet den Status bereits ehrlich. Für eine rein mathematische Facharbeit muss nicht jeder einfache Hilfssatz einen eigenen Lean-Namen erhalten; für eine ausdrücklich **vollständige Formalisierung aller im Paper neu als Theorem hervorgehobenen Aussagen** sollte er optional nachformalisiert werden. Eine Beschreibung als bereits kernelgeprüft bleibt verboten.
2. **Keine unabhängige neue Kernelprüfung durch den Dokumentationsautor oder diesen dritten Review.** Vor einer formalen Release-Behauptung auf Basis dieses Reviews mit Lean 4.28.0 `./scripts/verify_release.sh` auf dem extrahierten Source-Root ausführen; den historischen Report nicht als frischen Lauf ausgeben.
3. **Neuheitsgrad und Beitrag vorsichtig klassifizieren.** Die zugrunde liegenden Differenz-, Bruch-, Basis- und Cauchyverfahren sind weitgehend Standardmathematik. Die Arbeit demonstriert eine konkrete kohärente Konstruktion aus primitiven Pfaddaten und ihre präzise logische/formale Einordnung. Sie beweist weder einen neuen rationalen Isomorphietyp noch geometrische Dimension aus Baumadjazenz. Der Text übertreibt dies gegenwärtig nicht, aber eine Einreichung benötigt eine klare Gegenüberstellung mit den bekannten Konstruktionen und einen expliziten Zieljournal-/Beitragstyp (Originalarbeit, formalisierte Konstruktion, Expositionspaper).

### P3 — Redaktionelle und archivalische Reparaturen

4. **Autor und Affiliation fehlen im fertigen Satzspiegel.** `main.tex` und das PDF führen noch `[AUTHOR TO BE SUPPLIED]`. Vor öffentlicher Einreichung echten Autor, ggf. Institution und Datum eintragen.
5. **Appendix-B-Form: 89 `Plan X.Y`-Unterabschnitte.** Die explizite Vollständigkeitskontrolle ist hilfreich, wirkt in einer Standard-Fachzeitschrift aber wie ein Projektnachweis statt wie ein durchlaufender mathematischer Anhang. Für die Fachfassung empfiehlt sich entweder eine weniger schematische mathematische Gruppierung oder ein getrenntes *proof supplement*, ohne Inhalte bzw. Fundstellen zu verlieren.
6. **Literaturzugang.** Zehn Referenzen sind bibliografisch thematisch passend; manche Monographien wurden nur anhand von Verlagsinhaltsverzeichnissen/Metadaten verifiziert. Keine satzgenaue Primärbeweiskontrolle nicht zugänglicher Passagen behaupten. Die nachgeprüften Originalabstracts von Lubarsky/Gilbert behandeln andere logische Grundlagensysteme und dürfen **nicht** zu einer Unabhängigkeitsaussage für das Lean-Repository hochgestuft werden.
7. **Projektstatus.** Freigabe als mathematische **Begutachtungsfassung** vertretbar; kein Nachweis einer externen Peer Review, keiner Publikation oder Annahme in einer Zeitschrift. Auch weitere interne AI-Reviews ersetzen eine unabhängige fachkundige externe Begutachtung nicht.

### Kein Anlass für einen neuen grundlegenden Lean-Task

Die sechs reparierten Textstellen erfordern keine neue formale Theorie. Ein optionales Mini-Lemma für die unäre `-1`-Nichtdarstellbarkeit wäre eine Beweispräzisierung, aber kein Blocker für die 25 Hauptresultate. Im Übrigen sollte jetzt eher an der wissenschaftlichen Endredaktion und externen fachlichen Begutachtung gearbeitet werden als an immer neuen foundational Tasks.

## 5. Dokumentarische Reparaturen D1–D9: finale Bewertung

- **D1 (fehlende Logs):** `compile.log` und `evidence/projS_inS_check.log` nun tatsächlich vorhanden und im 60/60-MANIFEST erfasst.
- **D2 (25 falsche `main.tex`-Zeilen):** 25/25 neu aus den Satzumgebungen extrahierte Startzeilen stimmen mit `25_MAIN_RESULTS_CROSSWALK.md`.
- **D3 (altes Abnahmedokument):** `revision_acceptance.md` führt 89/89 als Themenabdeckung, nicht als 89 separate Lean-Sätze.
- **D4 (Namensraum):** `open_questions.md` verwendet `no_chart_into_real` und nicht das unzutreffende `Topology.no_chart_into_real`.
- **D5 (Seitenhistorie):** Der ältere Manuskriptstand ist als 26 statt irrtümlich 27 Seiten angegeben, wo die ältere Fassung behandelt wird.
- **D6 (Rollenklassifikation):** Datenbehaftete oder apartheitsbedingte *bewiesene* Sätze werden von logisch *unbewiesenen* zusätzlichen Prinzipien getrennt; `scope_89.csv` hat eine explizite Rolle pro Thema.
- **D7 (Abschnitts- und Kettennachweise):** `MAIN_TEXT_SUBSECTION_MAP.md` dokumentiert 62+4 Abschnitte, `MAIN_RESULT_PROOF_CHAINS.md` gibt für jeden der 25 Hauptsätze eine mehrstufige Beweiskette.
- **D8 (Anhangsnummerierung):** Die 89 Überschriften tragen das zusätzliche Wort `Plan` und sind von den Haupttextnummern unterscheidbar.
- **D9 (Literatur-Typografie):** Einheitliche Namensdarstellung `G. Gilbert` im gesetzten `references.tex`, Vollname im BibTeX-Metadatensatz.

**Anmerkung zu Dokumentenstatus:** Ein im ZIP vorhandener Prüfbericht, dessen Autor selbst `spot audit` sagt, bleibt ein selektiver Audit; die nun zusätzlich erzeugte 25er-Hauptsatzkreuztabelle/89er-Gliederungsmatrix ersetzt diesen selektiven Teil nicht durch einen neuen Kernelbeweis. Die historisch beigelegten Review-Dateien sind als Reviews dokumentiert, nicht als aktuelle mathematische Primärquelle.

---

## Anhang A — Methodik der Einzelprüfungen

- [A1] Mathematische Satzumgebungen wurden direkt aus `main.tex` extrahiert und gegen den begleitenden 25er-Crosswalk (reale Zeilennummer) kontrolliert.
- [A2] Die 89 `Plan X.Y`-Abschnittslabels wurden gegen `extended_proof_details.tex` und `scope_89.csv` abgeglichen; Seite, Abschnitt und Rolle geprüft.
- [A3] Die 289 ausdrücklich genannten Lean-Deklarationen wurden aus `proof_correspondence.md` extrahiert und jeweils mit Datei, Zielzeile und lokalem Deklarationsnamen im `task06_frozen_source.tar.gz` abgeglichen. Eine solche Fundstellenprüfung ist ein **Navigations-/Provenienznachweis**, keine unabhängige Re-Elaboration aller Terme.
- [A4] Ein vollständiger Dateidiff V1/V2 zeigt, dass die mathematischen Textänderungen auf die sechs benannten Reparaturfelder konzentriert sind. Im 89er-Anhang handelt es sich überwiegend um neue `Plan`-Präfixe für Überschriften; die materiell geänderten Beweispassagen betreffen insbesondere Normalisierung, konstruktive Strahlgleichheit und Produktkongruenz.
- [A5] Mathematik- und Logikgrenzen wurden mit Quelltexten und exakten Geltungsbereichen verglichen. Keine aus dem Nichtvorhandensein eines Leanbeweises abgeleitete Unbeweisbarkeitsbehauptung wurde übernommen.
- [A6] Dokumentenintegrität über separates ZIP-Datei-Inventar und Datei-Hashmanifest; selbst ausgeführte `source_check.py`-Prüfung, eigene LaTeX-Kompilation, PDF-Seitenzählung und visuelle Satzprüfung.


## Anhang B — Alle 25 benannten Hauptresultate: Satzmatrix

| Nr. | Satz, Fundstelle | Einstufung des geprüften Geltungsbereichs | Besondere Voraussetzung / Bewertung |
|---:|---|---|---|
| 1 | **Unique finite root path** — `main.tex:57` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Endliche Wörter, eindeutiger Elternschritt; Beweis durch Induktion. |
| 2 | **Path sum equals depth** — `main.tex:73` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Einheitskantensumme, nicht zusätzliche Zahlmarkierung. |
| 3 | **Natural semiring** — `main.tex:90` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Unärer Pfadträger, keine vorausgesetzte importierte Zahlentheorie. |
| 4 | **Transitivity and positive-denominator cancellation** — `main.tex:141` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Positive Nenner und Integritätsbereich-Kürzung. |
| 5 | **Fraction-field algebra** — `main.tex:166` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Bruchklassen des normalisierten Integer-Rings. |
| 6 | **Ordered-field comparison** — `main.tex:209` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | `TwoLetters α`; Operationstransport und Ordnungserhaltung. |
| 7 | **Arity independence** — `main.tex:223` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Jeweils zwei verschiedene Buchstaben, keine Baum-Isomorphie. |
| 8 | **Symmetric bilinearity of the finite coordinate form** — `main.tex:241` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Auch b=0; weder Positivdefinitheit noch Metrik. |
| 9 | **Explicit bases and ranks** — `main.tex:274` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | b>0; algebraisch frei, keine topologische Dimension. |
| 10 | **Finite decomposition** — `main.tex:293` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | b>0, im Koeffizientenkörper invertierbares b; Identitätsgleichung separat. |
| 11 | **Complementary projection operators** — `main.tex:309` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | b>0, Projektionsgesetze und Bild-Kern-Relationen. |
| 12 | **Algebraic orthogonal splitting** — `main.tex:345` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Orthogonalität der Unterräume bzgl. B, nicht der Basis untereinander. |
| 13 | **Countable transverse basis** — `main.tex:381` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Endlich unterstützter Nullsummenraum; keine ℓ²-Vervollständigung. |
| 14 | **Longitudinal incompatibility for zero-padding** — `main.tex:393` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Spezifische Zero-Padding-Obstruktion, kein universelles No-go. |
| 15 | **Separated rays** — `main.tex:413` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Bezeugte unterschiedliche Koordinate; kein Index allein aus ξ≠η. |
| 16 | **Noncompact countable cylinders** — `main.tex:424` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Abzählbare Verzweigung, projektspezifische Compact/LocallyCompactAt. |
| 17 | **Ray transitivity and invariant maps** — `main.tex:443` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | DecidableEq A; niveauweise Permutationen, nicht gesamte Automorphismengruppe. |
| 18 | **Product estimate and modulus** — `main.tex:499` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Getrennte Eventualschranken; k-abhängige Präzisionsverschiebungen. |
| 19 | **Constructive Cauchy ring** — `main.tex:524` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | TOField K, explizite Moduldaten und Quotientenkongruenz. |
| 20 | **Order and tight apartness** — `main.tex:552` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Keine klassische Totalordnung/Trichotomie vorausgesetzt. |
| 21 | **Separated inversion** — `main.tex:593` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | Apartheit x # 0; nicht bloß x ≠ 0. |
| 22 | **Modulated completeness characterization** — `main.tex:639` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | UC iff CauchyApprox; UC selbst nicht unbedingter Satz. |
| 23 | **Suprema from data** — `main.tex:659` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | SupData(S) verlangt rationale obere Schranken und Annäherungszeugen. |
| 24 | **Logical equivalences; conditional form** — `main.tex:711` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | MP/LPO/WLPO als Propositionen, nicht eingeführte Axiome. |
| 25 | **One-way logical lower bounds** — `main.tex:732` | **Formal gedecktes Hauptergebnis, mit exakten Bedingungen** | LUB -> WLPO; monotone Konvergenz -> LPO; keine Konversen. |

**Interpretation:** Die Tabelle gibt den Geltungsbereich wieder, nicht 25 neue Kernel-Prüfungen. Wo ein Hauptsatz mehrere Lean-Lemmata kombiniert, wurde die informelle Beweiskette gesondert kontrolliert.

## Anhang C — Vollständige 89-Punkte-Kontrollmatrix

| Planungspunkt | Appendix-B-Fundstelle | PDF-Seite | Math. Rolle aus Scope-Matrix | Ergebnis des dritten Reviews |
|---|---|---:|---|---|
| 1.1 | `extended_proof_details.tex:?` | 27 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 1.2 | `extended_proof_details.tex:?` | 27 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 1.3 | `extended_proof_details.tex:?` | 28 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 1.4 | `extended_proof_details.tex:?` | 28 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.1 | `extended_proof_details.tex:?` | 28 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.2 | `extended_proof_details.tex:?` | 28 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.3 | `extended_proof_details.tex:?` | 28 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.4 | `extended_proof_details.tex:?` | 28 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.5 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 2.6 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 3.1 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 3.2 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 3.3 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 4.1 | `extended_proof_details.tex:?` | 29 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 4.2 | `extended_proof_details.tex:?` | 30 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 4.3 | `extended_proof_details.tex:?` | 30 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 4.4 | `extended_proof_details.tex:?` | 30 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 5.1 | `extended_proof_details.tex:?` | 30 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 5.2 | `extended_proof_details.tex:?` | 30 | Proved mathematical argument / established definition | **M1 korrigiert**, Normalform und Paarrelation unterschieden |
| 5.3 | `extended_proof_details.tex:?` | 31 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 5.4 | `extended_proof_details.tex:?` | 31 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.1 | `extended_proof_details.tex:?` | 31 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.2 | `extended_proof_details.tex:?` | 31 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.3 | `extended_proof_details.tex:?` | 31 | Proved mathematical argument / established definition | Gültiger Zweibuchstaben-Zeuge; unäres −1 nur informell bewiesen |
| 6.4 | `extended_proof_details.tex:?` | 32 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.5 | `extended_proof_details.tex:?` | 32 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.6 | `extended_proof_details.tex:?` | 32 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 6.7 | `extended_proof_details.tex:?` | 32 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 7.1 | `extended_proof_details.tex:?` | 33 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 7.2 | `extended_proof_details.tex:?` | 33 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 7.3 | `extended_proof_details.tex:?` | 33 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.1 | `extended_proof_details.tex:?` | 33 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.2 | `extended_proof_details.tex:?` | 33 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.3 | `extended_proof_details.tex:?` | 33 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.4 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.5 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.6 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.7 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.8 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 8.9 | `extended_proof_details.tex:?` | 34 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 9.1 | `extended_proof_details.tex:?` | 34 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 9.2 | `extended_proof_details.tex:?` | 35 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 9.3 | `extended_proof_details.tex:?` | 35 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 9.4 | `extended_proof_details.tex:?` | 35 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 9.5 | `extended_proof_details.tex:?` | 35 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.1 | `extended_proof_details.tex:?` | 35 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.2 | `extended_proof_details.tex:?` | 35 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.3 | `extended_proof_details.tex:?` | 36 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.4 | `extended_proof_details.tex:?` | 36 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.5 | `extended_proof_details.tex:?` | 36 | Proved under DecidableEq alphabet | **M4 korrigiert**, DecidableEq ausdrücklich benutzt |
| 10.6 | `extended_proof_details.tex:?` | 36 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.7 | `extended_proof_details.tex:?` | 36 | Proved conditional theorem (extra premise) | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 10.8 | `extended_proof_details.tex:?` | 37 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 11.1 | `extended_proof_details.tex:?` | 37 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 11.2 | `extended_proof_details.tex:?` | 37 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 11.3 | `extended_proof_details.tex:?` | 37 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 11.4 | `extended_proof_details.tex:?` | 37 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 12.1 | `extended_proof_details.tex:?` | 38 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 12.2 | `extended_proof_details.tex:?` | 38 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 12.3 | `extended_proof_details.tex:?` | 38 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 12.4 | `extended_proof_details.tex:?` | 38 | Proved mathematical argument / established definition | **M3 korrigiert**, unabhängige Repräsentantenschranken |
| 12.5 | `extended_proof_details.tex:?` | 38 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 12.6 | `extended_proof_details.tex:?` | 39 | Proved with the explicit data/hypotheses | **M6 konsistent**, verschobenes Produkt vs. Quotientenäquivalenz |
| 12.7 | `extended_proof_details.tex:?` | 39 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.1 | `extended_proof_details.tex:?` | 39 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.2 | `extended_proof_details.tex:?` | 40 | Proved with the explicit data/hypotheses | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.3 | `extended_proof_details.tex:?` | 40 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.4 | `extended_proof_details.tex:?` | 40 | Proved with the explicit data/hypotheses | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.5 | `extended_proof_details.tex:?` | 41 | Proved conditional theorem (extra premise) | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.6 | `extended_proof_details.tex:?` | 41 | Proved with the explicit data/hypotheses | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 13.7 | `extended_proof_details.tex:?` | 41 | Proved with the explicit data/hypotheses | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 14.1 | `extended_proof_details.tex:?` | 41 | Proved equivalence; principle not asserted | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 14.2 | `extended_proof_details.tex:?` | 42 | Proved equivalence; principle not asserted | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 14.3 | `extended_proof_details.tex:?` | 42 | Proved equivalence; principle not asserted | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 14.4 | `extended_proof_details.tex:?` | 42 | Proved one-way implication | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 14.5 | `extended_proof_details.tex:?` | 42 | Proved mathematical argument / established definition | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 15.1 | `extended_proof_details.tex:?` | 43 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 15.2 | `extended_proof_details.tex:?` | 43 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 15.3 | `extended_proof_details.tex:?` | 43 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 15.4 | `extended_proof_details.tex:?` | 43 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 16.1 | `extended_proof_details.tex:?` | 43 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.2 | `extended_proof_details.tex:?` | 43 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.3 | `extended_proof_details.tex:?` | 44 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.4 | `extended_proof_details.tex:?` | 44 | Proved obstruction; broader case open | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.5 | `extended_proof_details.tex:?` | 44 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.6 | `extended_proof_details.tex:?` | 44 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 16.7 | `extended_proof_details.tex:?` | 44 | Open issue / scope boundary | Grenze oder offene Aussage erkennbar **nicht** als unbedingtes Theorem ausgegeben |
| 17.1 | `extended_proof_details.tex:?` | 44 | Definition / structural comparison | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |
| 17.2 | `extended_proof_details.tex:?` | 45 | Open issue / scope boundary | Inhalt mit Task-06-Geltungsbereich vereinbar; keine neue unbedingte Verstärkung festgestellt |

**Zur Quellenkontrolle:** Die 89 Abschnitte sind unterschiedlich gewichtet: In der ersten Spalte steht die ursprüngliche mathematische Gliederung, nicht 89 separate Lean-Sätze. Die genauen Quellfundstellen der einzelnen Themen stehen weiterhin im mitgelieferten `scope_89.csv` und der Hauptsatz-/Lean-Korrespondenz.

## Anhang D — Die 289 überprüften Deklarationsfundstellen

**Anzahl:** 289. Der nachfolgende Navigationsaudit bestätigt jeweils die physische Existenz des Source-Pfads, der angegebenen Zeile und des deklarierten lokalen Namens in der Umgebung.

| Bereich | Deklaration | Lean-Datei und Zeile | Navigation |
|---|---|---|---|
| Task-06 | `ChildModule.dot_addV_left` | `DimensionFoundation/BilinearForm.lean:27` | OK |
| Task-06 | `ChildModule.dot_addV_right` | `DimensionFoundation/BilinearForm.lean:33` | OK |
| Task-06 | `ChildModule.dot_smul_left` | `DimensionFoundation/BilinearForm.lean:39` | OK |
| Task-06 | `ChildModule.dot_smul_right` | `DimensionFoundation/BilinearForm.lean:45` | OK |
| Task-06 | `ChildModule.dot_bilinear_symmetric` | `DimensionFoundation/BilinearForm.lean:51` | OK |
| Task-06 | `ChildModule.dot_zeroV_left` | `DimensionFoundation/BilinearForm.lean:61` | OK |
| Task-06 | `ChildModule.dot_zeroV_right` | `DimensionFoundation/BilinearForm.lean:65` | OK |
| Task-06 | `ChildModule.dot_negV_left` | `DimensionFoundation/BilinearForm.lean:69` | OK |
| Task-06 | `ChildModule.dot_negV_right` | `DimensionFoundation/BilinearForm.lean:74` | OK |
| Task-06 | `ChildModule.zeroV_inL` | `DimensionFoundation/ProjectionLaws.lean:31` | OK |
| Task-06 | `ChildModule.addV_zeroV` | `DimensionFoundation/ProjectionLaws.lean:33` | OK |
| Task-06 | `ChildModule.proj_of_inL` | `DimensionFoundation/ProjectionLaws.lean:38` | OK |
| Task-06 | `ChildModule.proj_of_inS` | `DimensionFoundation/ProjectionLaws.lean:45` | OK |
| Task-06 | `ChildModule.projL_of_inL` | `DimensionFoundation/ProjectionLaws.lean:51` | OK |
| Task-06 | `ChildModule.projS_of_inL` | `DimensionFoundation/ProjectionLaws.lean:54` | OK |
| Task-06 | `ChildModule.projL_of_inS` | `DimensionFoundation/ProjectionLaws.lean:58` | OK |
| Task-06 | `ChildModule.projS_of_inS` | `DimensionFoundation/ProjectionLaws.lean:62` | OK |
| Task-06 | `ChildModule.projL_idem` | `DimensionFoundation/ProjectionLaws.lean:67` | OK |
| Task-06 | `ChildModule.projS_idem` | `DimensionFoundation/ProjectionLaws.lean:70` | OK |
| Task-06 | `ChildModule.projL_projS` | `DimensionFoundation/ProjectionLaws.lean:73` | OK |
| Task-06 | `ChildModule.projS_projL` | `DimensionFoundation/ProjectionLaws.lean:76` | OK |
| Task-06 | `ChildModule.projL_addV_projS` | `DimensionFoundation/ProjectionLaws.lean:79` | OK |
| Task-06 | `ChildModule.projections_idempotent_complementary` | `DimensionFoundation/ProjectionLaws.lean:82` | OK |
| Task-06 | `ChildModule.projL_addV` | `DimensionFoundation/ProjectionLaws.lean:92` | OK |
| Task-06 | `ChildModule.projL_smul` | `DimensionFoundation/ProjectionLaws.lean:96` | OK |
| Task-06 | `ChildModule.projS_addV` | `DimensionFoundation/ProjectionLaws.lean:100` | OK |
| Task-06 | `ChildModule.projS_smul` | `DimensionFoundation/ProjectionLaws.lean:107` | OK |
| Task-06 | `ChildModule.inL_iff_projL_eq` | `DimensionFoundation/ProjectionLaws.lean:116` | OK |
| Task-06 | `ChildModule.inS_iff_projS_eq` | `DimensionFoundation/ProjectionLaws.lean:120` | OK |
| Task-06 | `ChildModule.range_projL` | `DimensionFoundation/ProjectionLaws.lean:125` | OK |
| Task-06 | `ChildModule.range_projS` | `DimensionFoundation/ProjectionLaws.lean:130` | OK |
| Task-06 | `ChildModule.inS_iff_projL_eq_zero` | `DimensionFoundation/ProjectionLaws.lean:135` | OK |
| Task-06 | `ChildModule.inL_iff_projS_eq_zero` | `DimensionFoundation/ProjectionLaws.lean:144` | OK |
| Task-06 | `ChildModule.dot_inL_inS` | `DimensionFoundation/ProjectionLaws.lean:155` | OK |
| Task-06 | `ChildModule.dot_projL_projS` | `DimensionFoundation/ProjectionLaws.lean:160` | OK |
| Task-06 | `ChildModule.dot_projS_projL` | `DimensionFoundation/ProjectionLaws.lean:164` | OK |
| Task-06 | `ChildModule.dot_split` | `DimensionFoundation/ProjectionLaws.lean:171` | OK |
| Task-05 | `Ray.encode` | `BoundaryTopology/BinaryEncoding.lean:103` | OK |
| Task-05 | `Ray.encode_not_injective` | `BoundaryTopology/BinaryEncoding.lean:176` | OK |
| Task-05 | `Ray.Agree` | `BoundaryTopology/Cylinders.lean:53` | OK |
| Task-05 | `Ray.Cyl` | `BoundaryTopology/Cylinders.lean:56` | OK |
| Task-05 | `Ray.cyl_prefixAt` | `BoundaryTopology/Cylinders.lean:124` | OK |
| Task-05 | `Topology.Chart` | `BoundaryTopology/ManifoldConditions.lean:41` | OK |
| Task-05 | `Ray.no_zero_dim_chart` | `BoundaryTopology/ManifoldConditions.lean:117` | OK |
| Task-05 | `Ray.unaryChart` | `BoundaryTopology/ManifoldConditions.lean:127` | OK |
| Task-05 | `TreeR.IntervalsConnected` | `BoundaryTopology/ManifoldConditions.lean:208` | OK |
| Task-05 | `no_chart_into_real` | `BoundaryTopology/ManifoldConditions.lean:227` | OK |
| Task-05 | `Ray.PrefixOpen` | `BoundaryTopology/PrefixTopology.lean:39` | OK |
| Task-05 | `Ray.prefixTopology` | `BoundaryTopology/PrefixTopology.lean:42` | OK |
| Task-05 | `Ray.cyl_open` | `BoundaryTopology/PrefixTopology.lean:58` | OK |
| Task-05 | `Ray.cyl_compl_open` | `BoundaryTopology/PrefixTopology.lean:62` | OK |
| Task-05 | `Ray.separate_of_diff` | `BoundaryTopology/PrefixTopology.lean:83` | OK |
| Task-05 | `Ray.not_not_diff_of_ne` | `BoundaryTopology/PrefixTopology.lean:102` | OK |
| Task-05 | `TreeR.realIdChart` | `BoundaryTopology/RealLineManifold.lean:81` | OK |
| Task-05 | `Ray.no_isolated` | `BoundaryTopology/TopologicalObstructions.lean:81` | OK |
| Task-05 | `Ray.boundary_disconnected` | `BoundaryTopology/TopologicalObstructions.lean:119` | OK |
| Task-05 | `Ray.connected_subsingleton` | `BoundaryTopology/TopologicalObstructions.lean:133` | OK |
| Task-05 | `Ray.cyl_not_compact` | `BoundaryTopology/TopologicalObstructions.lean:162` | OK |
| Task-05 | `Ray.not_locallyCompactAt` | `BoundaryTopology/TopologicalObstructions.lean:219` | OK |
| Task-05 | `Longitudinal.allOnes_not_finSupp` | `DimensionFoundation/BoundaryLongitudinal.lean:35` | OK |
| Task-05 | `Longitudinal.no_finSupp_uniform_limit` | `DimensionFoundation/BoundaryLongitudinal.lean:40` | OK |
| Task-05 | `Longitudinal.padSucc_u_not_inL` | `DimensionFoundation/BoundaryLongitudinal.lean:50` | OK |
| Task-05 | `ChildModule.addV` | `DimensionFoundation/FiniteChildModule.lean:30` | OK |
| Task-05 | `ChildModule.smul` | `DimensionFoundation/FiniteChildModule.lean:32` | OK |
| Task-05 | `ChildModule.coordSum` | `DimensionFoundation/FiniteChildModule.lean:59` | OK |
| Task-05 | `ChildModule.InL` | `DimensionFoundation/FiniteChildModule.lean:65` | OK |
| Task-05 | `ChildModule.InS` | `DimensionFoundation/FiniteChildModule.lean:68` | OK |
| Task-05 | `ChildModule.dot` | `DimensionFoundation/FiniteChildModule.lean:71` | OK |
| Task-05 | `ChildModule.dot_u_of_inS` | `DimensionFoundation/FiniteChildModule.lean:110` | OK |
| Task-05 | `ChildModule.dot_comm` | `DimensionFoundation/FiniteChildModule.lean:114` | OK |
| Task-05 | `ChildModule.dot_comm` | `DimensionFoundation/FiniteChildModule.lean:114` | OK |
| Task-05 | `FinSum.sumC` | `DimensionFoundation/FiniteSums.lean:66` | OK |
| Task-05 | `longitudinal_basis_treeQ` | `DimensionFoundation/Instances.lean:24` | OK |
| Task-05 | `direct_sum_treeQ` | `DimensionFoundation/Instances.lean:29` | OK |
| Task-05 | `omega_indep` | `DimensionFoundation/Instances.lean:43` | OK |
| Task-05 | `omega_span` | `DimensionFoundation/Instances.lean:48` | OK |
| Task-05 | `OmegaModule.FO` | `DimensionFoundation/OmegaFiniteSupport.lean:26` | OK |
| Task-05 | `OmegaModule.FinSupp` | `DimensionFoundation/OmegaFiniteSupport.lean:38` | OK |
| Task-05 | `OmegaModule.InSO` | `DimensionFoundation/OmegaFiniteSupport.lean:41` | OK |
| Task-05 | `OmegaModule.tvO` | `DimensionFoundation/OmegaFiniteSupport.lean:113` | OK |
| Task-05 | `OmegaModule.tvO_indep` | `DimensionFoundation/OmegaFiniteSupport.lean:160` | OK |
| Task-05 | `OmegaModule.tvO_span` | `DimensionFoundation/OmegaFiniteSupport.lean:170` | OK |
| Task-05 | `OmegaModule.pad` | `DimensionFoundation/OmegaFiniteSupport.lean:217` | OK |
| Task-05 | `OmegaModule.pad_injective` | `DimensionFoundation/OmegaFiniteSupport.lean:236` | OK |
| Task-05 | `OmegaModule.pad_inSO` | `DimensionFoundation/OmegaFiniteSupport.lean:249` | OK |
| Task-05 | `OmegaModule.pad_tv` | `DimensionFoundation/OmegaFiniteSupport.lean:266` | OK |
| Task-05 | `OmegaModule.padSucc` | `DimensionFoundation/OmegaFiniteSupport.lean:283` | OK |
| Task-05 | `OmegaModule.padSucc_inS` | `DimensionFoundation/OmegaFiniteSupport.lean:294` | OK |
| Task-05 | `OmegaModule.padSucc_tv` | `DimensionFoundation/OmegaFiniteSupport.lean:304` | OK |
| Task-05 | `ChildModule.IsBasisOf` | `DimensionFoundation/TransverseBasis.lean:47` | OK |
| Task-05 | `ChildModule.longitudinal_basis` | `DimensionFoundation/TransverseBasis.lean:65` | OK |
| Task-05 | `ChildModule.tv` | `DimensionFoundation/TransverseBasis.lean:85` | OK |
| Task-05 | `ChildModule.tv_indep` | `DimensionFoundation/TransverseBasis.lean:134` | OK |
| Task-05 | `ChildModule.tv_span` | `DimensionFoundation/TransverseBasis.lean:141` | OK |
| Task-05 | `ChildModule.transverse_basis` | `DimensionFoundation/TransverseBasis.lean:155` | OK |
| Task-05 | `ChildModule.transverse_index_bijection` | `DimensionFoundation/TransverseBasis.lean:164` | OK |
| Task-05 | `ChildModule.projL` | `DimensionFoundation/TransverseBasis.lean:173` | OK |
| Task-05 | `ChildModule.projS` | `DimensionFoundation/TransverseBasis.lean:176` | OK |
| Task-05 | `ChildModule.decomposition` | `DimensionFoundation/TransverseBasis.lean:181` | OK |
| Task-05 | `ChildModule.decomposition_unique` | `DimensionFoundation/TransverseBasis.lean:194` | OK |
| Task-05 | `ChildModule.inL_inS_zero` | `DimensionFoundation/TransverseBasis.lean:211` | OK |
| Task-05 | `ChildModule.transverse_one_zero` | `DimensionFoundation/TransverseBasis.lean:218` | OK |
| Task-05 | `ChildModule.dot_perm` | `DimensionFoundation/TransverseBasis.lean:231` | OK |
| Task-05 | `ChildModule.inS_perm` | `DimensionFoundation/TransverseBasis.lean:237` | OK |
| Task-05 | `ChildModule.inL_perm` | `DimensionFoundation/TransverseBasis.lean:244` | OK |
| Task-05 | `Child` | `PrimitiveTree/FiniteChild.lean:18` | OK |
| Task-05 | `Child.inclSucc` | `PrimitiveTree/FiniteChild.lean:76` | OK |
| Task-05 | `Child.enum` | `PrimitiveTree/FiniteChild.lean:111` | OK |
| Task-05 | `Child.nodup_enum` | `PrimitiveTree/FiniteChild.lean:144` | OK |
| Task-05 | `Word` | `PrimitiveTree/FiniteWords.lean:22` | OK |
| Task-05 | `Word.root` | `PrimitiveTree/FiniteWords.lean:29` | OK |
| Task-05 | `Word.depth` | `PrimitiveTree/FiniteWords.lean:32` | OK |
| Task-05 | `Word.IsParent` | `PrimitiveTree/FiniteWords.lean:37` | OK |
| Task-05 | `Word.Edge` | `PrimitiveTree/FiniteWords.lean:40` | OK |
| Task-05 | `Word.root_no_parent` | `PrimitiveTree/FiniteWords.lean:69` | OK |
| Task-05 | `Word.nonroot_has_parent` | `PrimitiveTree/FiniteWords.lean:72` | OK |
| Task-05 | `Word.parent_unique` | `PrimitiveTree/FiniteWords.lean:75` | OK |
| Task-05 | `Word.ChildOf` | `PrimitiveTree/FiniteWords.lean:103` | OK |
| Task-05 | `Word.rootEdges` | `PrimitiveTree/FiniteWords.lean:133` | OK |
| Task-05 | `Word.dpath_root_unique` | `PrimitiveTree/FiniteWords.lean:142` | OK |
| Task-05 | `Word.connected` | `PrimitiveTree/FiniteWords.lean:187` | OK |
| Task-05 | `Word.no_cycle` | `PrimitiveTree/FiniteWords.lean:261` | OK |
| Task-05 | `Word.unbounded_depth` | `PrimitiveTree/FiniteWords.lean:288` | OK |
| Task-05 | `Word.edgeFold` | `PrimitiveTree/RootEdges.lean:22` | OK |
| Task-05 | `Word.unitSum` | `PrimitiveTree/RootEdges.lean:27` | OK |
| Task-05 | `Word.pathSum` | `PrimitiveTree/RootEdges.lean:30` | OK |
| Task-05 | `Word.unitSum_rootEdges` | `PrimitiveTree/RootEdges.lean:68` | OK |
| Task-05 | `Word.pathSum_eq_depth` | `PrimitiveTree/RootEdges.lean:75` | OK |
| Task-05 | `Word.pathSum_cons` | `PrimitiveTree/RootEdges.lean:77` | OK |
| Task-05 | `UnaryPath` | `PrimitiveTree/UnaryPaths.lean:16` | OK |
| Task-05 | `UnaryPath.extend` | `PrimitiveTree/UnaryPaths.lean:27` | OK |
| Task-05 | `UnaryPath.concat` | `PrimitiveTree/UnaryPaths.lean:30` | OK |
| Task-05 | `UnaryPath.iterate` | `PrimitiveTree/UnaryPaths.lean:35` | OK |
| Task-05 | `TreeR.mul_left_cancel_of_ne` | `TreeAnalysis/ApartnessStrength.lean:64` | OK |
| Task-05 | `TreeR.inv_iff_markov` | `TreeAnalysis/ApartnessStrength.lean:349` | OK |
| Task-05 | `TreeR.zeroOrApart_iff_lpo` | `TreeAnalysis/ApartnessStrength.lean:369` | OK |
| Task-05 | `TreeR.Tracked.converges` | `TreeAnalysis/ApproxClosure.lean:262` | OK |
| Task-05 | `TOField.IsModulus` | `TreeAnalysis/CauchyData.lean:40` | OK |
| Task-05 | `TOField.CSeq` | `TreeAnalysis/CauchyData.lean:47` | OK |
| Task-05 | `TOField.SeqEquiv` | `TreeAnalysis/CauchyData.lean:53` | OK |
| Task-05 | `TOField.isRegular_reg` | `TreeAnalysis/CauchyData.lean:130` | OK |
| Task-05 | `TOField.reg_equiv` | `TreeAnalysis/CauchyData.lean:144` | OK |
| Task-05 | `TOField.seqEquiv_trans` | `TreeAnalysis/CauchyData.lean:162` | OK |
| Task-05 | `TreeR.limit_unique` | `TreeAnalysis/CompletenessScope.lean:89` | OK |
| Task-05 | `TreeR.ofQ_seq_converges` | `TreeAnalysis/CompletenessScope.lean:108` | OK |
| Task-05 | `TreeR.rat_dense` | `TreeAnalysis/CompletenessScope.lean:127` | OK |
| Task-05 | `TreeR.tower_limit` | `TreeAnalysis/CompletenessScope.lean:271` | OK |
| Task-05 | `TreeR.ApproxData` | `TreeAnalysis/CompletenessStrength.lean:264` | OK |
| Task-05 | `TreeR.limit_of_approx` | `TreeAnalysis/CompletenessStrength.lean:306` | OK |
| Task-05 | `TreeR.UCMod` | `TreeAnalysis/CompletionCharacterization.lean:39` | OK |
| Task-05 | `TreeR.extendR` | `TreeAnalysis/CompletionCharacterization.lean:53` | OK |
| Task-05 | `TreeR.extendR_unique` | `TreeAnalysis/CompletionCharacterization.lean:94` | OK |
| Task-05 | `TreeR.extendR_comp` | `TreeAnalysis/CompletionCharacterization.lean:111` | OK |
| Task-05 | `TOField.eps` | `TreeAnalysis/DyadicPrecision.lean:73` | OK |
| Task-05 | `TOField.eps` | `TreeAnalysis/DyadicPrecision.lean:73` | OK |
| Task-05 | `TOField.eps_succ_add` | `TreeAnalysis/DyadicPrecision.lean:94` | OK |
| Task-05 | `TOField.three_eps_le` | `TreeAnalysis/DyadicPrecision.lean:141` | OK |
| Task-05 | `TOField.exists_eps_lt` | `TreeAnalysis/DyadicPrecision.lean:173` | OK |
| Task-05 | `TOField.exists_eps_lt` | `TreeAnalysis/DyadicPrecision.lean:173` | OK |
| Task-05 | `TreeR.realArityIso_comp` | `TreeAnalysis/FoundationsClosure.lean:146` | OK |
| Task-05 | `TreeR.decidableZero_iff_wlpo` | `TreeAnalysis/FoundationsClosure.lean:199` | OK |
| Task-05 | `TreeR.trichotomy_iff_lpo` | `TreeAnalysis/FoundationsClosure.lean:230` | OK |
| Task-05 | `TreeQ.mk_eq_of_depth_eq` | `TreeAnalysis/FractionCharacterization.lean:61` | OK |
| Task-05 | `FracQ` | `TreeAnalysis/FractionCharacterization.lean:74` | OK |
| Task-05 | `FracQ.instTField` | `TreeAnalysis/FractionCharacterization.lean:240` | OK |
| Task-05 | `TreeQ.ofFracQ_toFracQ` | `TreeAnalysis/FractionCharacterization.lean:281` | OK |
| Task-05 | `TreeQ.toFracQ_ofFracQ` | `TreeAnalysis/FractionCharacterization.lean:285` | OK |
| Task-05 | `TreeQ.orderedFieldIsoFracQ` | `TreeAnalysis/FractionCharacterization.lean:347` | OK |
| Task-05 | `TreeR.complete_iff_cauchyApprox` | `TreeAnalysis/LiftingPrinciples.lean:124` | OK |
| Task-05 | `TreeR.complete_of_choice` | `TreeAnalysis/LiftingPrinciples.lean:245` | OK |
| Task-05 | `TreeR.modulusFreeComplete_of_choice` | `TreeAnalysis/LiftingPrinciples.lean:249` | OK |
| Task-05 | `PrimitiveScope.prefixCount_eq` | `TreeAnalysis/PrimitiveDataScope.lean:51` | OK |
| Task-05 | `PrimitiveScope.prefixCount_not_isCauchy` | `TreeAnalysis/PrimitiveDataScope.lean:62` | OK |
| Task-05 | `PrimitiveScope.prefixCount_indep` | `TreeAnalysis/PrimitiveDataScope.lean:77` | OK |
| Task-05 | `Ray.encode_letter_choice_dependence` | `TreeAnalysis/PrimitiveDataScope.lean:144` | OK |
| Task-05 | `TreeQ.NonnegQ` | `TreeAnalysis/RationalOrder.lean:123` | OK |
| Task-05 | `TreeQ.archQ` | `TreeAnalysis/RationalOrder.lean:282` | OK |
| Task-05 | `TreeQ.instTOField` | `TreeAnalysis/RationalOrder.lean:299` | OK |
| Task-05 | `TreeR.RLt` | `TreeAnalysis/RealOrderApartness.lean:69` | OK |
| Task-05 | `TreeR.RLe` | `TreeAnalysis/RealOrderApartness.lean:71` | OK |
| Task-05 | `TreeR.RApart` | `TreeAnalysis/RealOrderApartness.lean:77` | OK |
| Task-05 | `TreeR.lt_trans` | `TreeAnalysis/RealOrderApartness.lean:172` | OK |
| Task-05 | `TreeR.le_antisymm` | `TreeAnalysis/RealOrderApartness.lean:187` | OK |
| Task-05 | `TreeR.eq_of_not_apart` | `TreeAnalysis/RealOrderApartness.lean:292` | OK |
| Task-05 | `TreeR.rinv` | `TreeAnalysis/RealOrderApartness.lean:330` | OK |
| Task-05 | `TreeR.mul_rinv` | `TreeAnalysis/RealOrderApartness.lean:335` | OK |
| Task-05 | `TreeR.exists_inv_of_apart` | `TreeAnalysis/RealOrderApartness.lean:375` | OK |
| Task-05 | `TreeR` | `TreeAnalysis/RealQuotient.lean:42` | OK |
| Task-05 | `TreeR.mkR` | `TreeAnalysis/RealQuotient.lean:51` | OK |
| Task-05 | `TreeR.instCRing` | `TreeAnalysis/RealQuotient.lean:161` | OK |
| Task-05 | `TreeR.ofQ_injective` | `TreeAnalysis/RealQuotient.lean:195` | OK |
| Task-05 | `TreeR.zero_ne_one` | `TreeAnalysis/RealQuotient.lean:204` | OK |
| Task-05 | `TreeR.SupData.isLUB` | `TreeAnalysis/SupremumScope.lean:65` | OK |
| Task-05 | `TreeR.SupData.ofList_isLUB` | `TreeAnalysis/SupremumScope.lean:152` | OK |
| Task-05 | `TreeR.tower_monotone_lub` | `TreeAnalysis/SupremumScope.lean:182` | OK |
| Task-05 | `TreeR.wlpo_of_unrestrictedLUB` | `TreeAnalysis/SupremumScope.lean:257` | OK |
| Task-05 | `TreeR.lpo_of_bmc` | `TreeAnalysis/SupremumScope.lean:312` | OK |
| Task-05 | `TreeR.TExpr.lim_tracked` | `TreeAnalysis/TrackedExpressions.lean:66` | OK |
| Task-05 | `TreeR.TExpr.converges_evalSeq` | `TreeAnalysis/TrackedExpressions.lean:85` | OK |
| Task-05 | `ArityEmbedding.mapWord_injective` | `TreeFoundation/ArityEmbeddings.lean:36` | OK |
| Task-05 | `ArityEmbedding.mapWord_isParent` | `TreeFoundation/ArityEmbeddings.lean:55` | OK |
| Task-05 | `ArityEmbedding.wordOmega_wordSucc` | `TreeFoundation/ArityEmbeddings.lean:105` | OK |
| Task-05 | `ArityEmbedding.vertex_union` | `TreeFoundation/ArityEmbeddings.lean:147` | OK |
| Task-05 | `ArityEmbedding.edge_union` | `TreeFoundation/ArityEmbeddings.lean:153` | OK |
| Task-05 | `RayAutomorphism.subtreeSwapAut` | `TreeFoundation/AutomorphismCounterexample.lean:105` | OK |
| Task-05 | `RayAutomorphism.subtreeSwapAut_not_levelwise` | `TreeFoundation/AutomorphismCounterexample.lean:189` | OK |
| Task-05 | `RayAutomorphism.levelwise_converse_false` | `TreeFoundation/AutomorphismCounterexample.lean:204` | OK |
| Task-05 | `ExtLevel.vertexLevel` | `TreeFoundation/ExtendedLevels.lean:50` | OK |
| Task-05 | `ExtLevel.rayLevel` | `TreeFoundation/ExtendedLevels.lean:54` | OK |
| Task-05 | `ExtLevel.root_level` | `TreeFoundation/ExtendedLevels.lean:57` | OK |
| Task-05 | `ExtLevel.first_edge_unit` | `TreeFoundation/ExtendedLevels.lean:60` | OK |
| Task-05 | `Ray` | `TreeFoundation/InfiniteRays.lean:19` | OK |
| Task-05 | `Ray.prefixAt` | `TreeFoundation/InfiniteRays.lean:30` | OK |
| Task-05 | `Ray.prefixAt_succ` | `TreeFoundation/InfiniteRays.lean:34` | OK |
| Task-05 | `Ray.pathSum_prefixAt` | `TreeFoundation/InfiniteRays.lean:44` | OK |
| Task-05 | `Ray.eq_of_prefixAt` | `TreeFoundation/InfiniteRays.lean:65` | OK |
| Task-05 | `Ray.depth_unbounded` | `TreeFoundation/InfiniteRays.lean:83` | OK |
| Task-05 | `RayOmega.ofFinite` | `TreeFoundation/InfiniteRays.lean:93` | OK |
| Task-05 | `RayOmega.identityRay_not_finite` | `TreeFoundation/InfiniteRays.lean:108` | OK |
| Task-05 | `RayOmega.union_proper` | `TreeFoundation/InfiniteRays.lean:116` | OK |
| Task-05 | `WordOmega` | `TreeFoundation/OmegaTree.lean:18` | OK |
| Task-05 | `OmegaTree.childOfIndex` | `TreeFoundation/OmegaTree.lean:23` | OK |
| Task-05 | `OmegaTree.children_distinct` | `TreeFoundation/OmegaTree.lean:33` | OK |
| Task-05 | `OmegaTree.infinitely_many_children` | `TreeFoundation/OmegaTree.lean:37` | OK |
| Task-05 | `OmegaTree.unbounded_depth` | `TreeFoundation/OmegaTree.lean:52` | OK |
| Task-05 | `RayAutomorphism.LevelPerm` | `TreeFoundation/RayAutomorphism.lean:33` | OK |
| Task-05 | `RayAutomorphism.TreeAut` | `TreeFoundation/RayAutomorphism.lean:101` | OK |
| Task-05 | `RayAutomorphism.treeAut` | `TreeFoundation/RayAutomorphism.lean:111` | OK |
| Task-05 | `RayAutomorphism.rayAct` | `TreeFoundation/RayAutomorphism.lean:123` | OK |
| Task-05 | `RayAutomorphism.swapPerm` | `TreeFoundation/RayAutomorphism.lean:190` | OK |
| Task-05 | `RayAutomorphism.rayAct_swapPerm` | `TreeFoundation/RayAutomorphism.lean:197` | OK |
| Task-05 | `RayAutomorphism.invariant_const` | `TreeFoundation/RayAutomorphism.lean:209` | OK |
| Task-05 | `RayAutomorphism.invariant_const` | `TreeFoundation/RayAutomorphism.lean:209` | OK |
| Task-05 | `RayAutomorphism.swapInvariant_const` | `TreeFoundation/RayAutomorphism.lean:214` | OK |
| Task-05 | `DepthQuotient.DepthRel` | `TreeNumbers/DepthQuotient.lean:40` | OK |
| Task-05 | `DepthQuotient.DepthClass` | `TreeNumbers/DepthQuotient.lean:62` | OK |
| Task-05 | `DepthQuotient.repeatW` | `TreeNumbers/DepthQuotient.lean:119` | OK |
| Task-05 | `DepthQuotient.OrderedSemiringIso` | `TreeNumbers/DepthQuotient.lean:281` | OK |
| Task-05 | `DepthQuotient.depthIso` | `TreeNumbers/DepthQuotient.lean:294` | OK |
| Task-05 | `DepthQuotient.depthIso_letter_indep` | `TreeNumbers/DepthQuotient.lean:307` | OK |
| Task-05 | `DepthQuotient.no_positive_count_of_noLetter` | `TreeNumbers/DepthQuotient.lean:331` | OK |
| Task-05 | `TreeN.induction` | `TreeNumbers/FoundationsLedger.lean:32` | OK |
| Task-05 | `TreeN.recN` | `TreeNumbers/FoundationsLedger.lean:42` | OK |
| Task-05 | `TreeN.recN_unique` | `TreeNumbers/FoundationsLedger.lean:51` | OK |
| Task-05 | `TreeN.le_iff_exists_add` | `TreeNumbers/FoundationsLedger.lean:83` | OK |
| Task-05 | `TreeZ.ofN_lt_ofN` | `TreeNumbers/FoundationsLedger.lean:124` | OK |
| Task-05 | `TreeZ.lt_trichotomy` | `TreeNumbers/FoundationsLedger.lean:140` | OK |
| Task-05 | `TriplePath.unary_numer_ne_zero` | `TreeNumbers/FoundationsLedger.lean:208` | OK |
| Task-05 | `TriplePath.unary_numer_ne_zero` | `TreeNumbers/FoundationsLedger.lean:208` | OK |
| Task-05 | `TriplePath.unary_no_universal_witness` | `TreeNumbers/FoundationsLedger.lean:216` | OK |
| Task-05 | `TreeQ.transfer_comp` | `TreeNumbers/FoundationsLedger.lean:272` | OK |
| Task-05 | `TreeQ.transfer_natCast` | `TreeNumbers/FoundationsLedger.lean:277` | OK |
| Task-05 | `TreeQ.arityIso_comp` | `TreeNumbers/FoundationsLedger.lean:284` | OK |
| Task-05 | `Frac.Eqv` | `TreeNumbers/PathFractions.lean:41` | OK |
| Task-05 | `Frac.eqv_trans` | `TreeNumbers/PathFractions.lean:49` | OK |
| Task-05 | `Frac.add_resp` | `TreeNumbers/PathFractions.lean:101` | OK |
| Task-05 | `Frac.mul_resp` | `TreeNumbers/PathFractions.lean:113` | OK |
| Task-05 | `Frac.mul_inv_cancel` | `TreeNumbers/PathFractions.lean:243` | OK |
| Task-05 | `TreeN.PairEq` | `TreeNumbers/PathIntegers.lean:23` | OK |
| Task-05 | `TreeN.pairEq_refl` | `TreeNumbers/PathIntegers.lean:25` | OK |
| Task-05 | `TreeN.pairEq_symm` | `TreeNumbers/PathIntegers.lean:27` | OK |
| Task-05 | `TreeN.pairEq_trans` | `TreeNumbers/PathIntegers.lean:29` | OK |
| Task-05 | `TreeN.normPair` | `TreeNumbers/PathIntegers.lean:37` | OK |
| Task-05 | `TreeN.normal_unique` | `TreeNumbers/PathIntegers.lean:64` | OK |
| Task-05 | `TreeZ` | `TreeNumbers/PathIntegers.lean:92` | OK |
| Task-05 | `TreeZ.mkZ_sound` | `TreeNumbers/PathIntegers.lean:113` | OK |
| Task-05 | `TreeZ.mkZ_exact` | `TreeNumbers/PathIntegers.lean:119` | OK |
| Task-05 | `TreeZ.instCRing` | `TreeNumbers/PathIntegers.lean:256` | OK |
| Task-05 | `TreeZ.mul_eq_zero` | `TreeNumbers/PathIntegers.lean:319` | OK |
| Task-05 | `TreeZ.mul_left_cancel` | `TreeNumbers/PathIntegers.lean:330` | OK |
| Task-05 | `TreeZ.mul_ne_zero` | `TreeNumbers/PathIntegers.lean:342` | OK |
| Task-05 | `TreeZ.ofN` | `TreeNumbers/PathIntegers.lean:351` | OK |
| Task-05 | `TreeZ.ofN_injective` | `TreeNumbers/PathIntegers.lean:366` | OK |
| Task-05 | `TreeN` | `TreeNumbers/PathNaturals.lean:17` | OK |
| Task-05 | `TreeN.add` | `TreeNumbers/PathNaturals.lean:34` | OK |
| Task-05 | `TreeN.mul` | `TreeNumbers/PathNaturals.lean:37` | OK |
| Task-05 | `TreeN.add_comm` | `TreeNumbers/PathNaturals.lean:79` | OK |
| Task-05 | `TreeN.mul_comm` | `TreeNumbers/PathNaturals.lean:117` | OK |
| Task-05 | `TreeN.right_distrib` | `TreeNumbers/PathNaturals.lean:126` | OK |
| Task-05 | `TreeN.mul_assoc` | `TreeNumbers/PathNaturals.lean:136` | OK |
| Task-05 | `TreeN.instCSR` | `TreeNumbers/PathNaturals.lean:156` | OK |
| Task-05 | `TreeN.le_antisymm` | `TreeNumbers/PathOrder.lean:141` | OK |
| Task-05 | `TreeN.lt_or_eq_or_gt` | `TreeNumbers/PathOrder.lean:167` | OK |
| Task-05 | `TriplePath` | `TreeNumbers/PathTriples.lean:32` | OK |
| Task-05 | `TriplePath.numer` | `TreeNumbers/PathTriples.lean:46` | OK |
| Task-05 | `TriplePath.denom` | `TreeNumbers/PathTriples.lean:49` | OK |
| Task-05 | `TriplePath.denom_pos` | `TreeNumbers/PathTriples.lean:56` | OK |
| Task-05 | `TriplePath.Rel` | `TreeNumbers/PathTriples.lean:64` | OK |
| Task-05 | `TriplePath.universal_witness` | `TreeNumbers/PathTriples.lean:194` | OK |

**Grenze der Navigation:** Diese 289/289-Zuordnung beweist nicht, dass sämtliche frei formulierten Manuskripttexte eigenständig elaborierte Lean-Typen sind. Sie macht jeden genannten formalisierten Baustein auffindbar und nachprüfbar. Für alle 25 Hauptsätze wurden deshalb zusätzlich die Voraussetzungen und die informelle Beweiskette begutachtet.
