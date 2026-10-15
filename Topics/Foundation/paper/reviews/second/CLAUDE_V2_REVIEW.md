# Review v2: Langfassung mit 89 Beweispunkten

Oct 15, 2026 · @antaris

Vorgänger: Review Task-06: Foundation-Manuskript und Lean-Quelle

## Ergebnis auf einen Blick

Die Langfassung ist mathematisch korrekt und behebt alle vier wesentlichen Befunde aus Review v1 sowie die meisten kleineren. Ich habe keinen falschen Satz und keinen fehlerhaften Beweisschritt gefunden. Alle neu eingeführten Konstanten (Inversenmodul j+2k, Diagonalmodul max(ν(k+2), M(k+2)), Konvergenzschwelle, Auswahlschritte, Schranken 1/2, 1/4, 1/8) stimmen exakt mit dem Lean-Code überein.

Als Grundlage für eine abschließende fachliche Begutachtung taugt das Paket. Vorher sollten aber einige Dokumentationsfehler behoben werden. Die wichtigsten: eine weiterhin fehlende Belegdatei, die als vorhanden gemeldet wird, durchgehend um eine Zeile verschobene Zeilenangaben in der 25er-Kreuztabelle und ein veraltetes Abnahmedokument, das der 89/89-Behauptung widerspricht.

| Prüfgegenstand | Umfang | Ergebnis |
| --- | --- | --- |
| Lean-Archiv im Paket | SHA-256 | identisch mit dem in v1 neu gebauten Archiv; Kernel-Befunde aus v1 gelten unverändert |
| Artefakt-Manifest | 51 Dateien | alle Hashes korrekt |
| Task-5-Logs | 602 Signaturen, 21 Dateien | alle 602 von Lean als exakt gleich bestätigt, Axiome identisch |
| Signaturen in proof\_correspondence.md | 289 | 274 exakt (Lean), 15 wörtlich im Quelltext |
| Anhang B | 89 Abschnitte | alle gelesen; alle Rechnungen nachvollzogen, Konstanten gegen Lean geprüft |
| PDF-Seitenangaben in scope\_89 | 89 | alle korrekt |
| Zeilenangaben der 25 Hauptresultate | 25 | alle 25 um eine Zeile verschoben |
| Neu kompiliert | 46 Seiten | keine ungelösten Verweise |
| Befunde |  | 0 mathematisch falsch, 6 mathematisch ungenau, 9 Dokumentation |

## Status der Befunde aus Review v1

Von 18 Befunden sind 16 vollständig behoben, einer teilweise und einer unverändert. Die Korrekturen habe ich jeweils am neuen Text geprüft, nicht an der Selbstauskunft in revision\_acceptance.md.

| v1 | Befund | Status | Wo behoben bzw. was fehlt |
| --- | --- | --- | --- |
| W1 | Körperstruktur auf Tripeln transportiert, nicht gesagt | behoben | Abstract; neuer Abschnitt 6.5 mit Transportgleichungen; Beweis Satz 7.1; Anhang B.6.4, B.6.6, B.6.7. Rest: Schluss (§17) nennt den Transport nicht |
| W2 | Unäre Obstruktion nur für 0 | behoben | §6.4 und B.6.3: 0 und −1 ausgeschlossen, −1 korrekt als informell markiert; exaktes Bild bewusst nicht behauptet |
| W3 | Voraussetzungen von TOField verdeckt | behoben | §12.1 nennt Entscheidungsverfahren und `archBound` als Daten; B.1.4, B.12.1 |
| W4 | Belegdateien fehlen | teilweise | Task-5-Logs und Quellarchiv jetzt enthalten; `projS_inS_check.log` fehlt weiter, siehe D1 |
| K1 | D(A)-Operationen undefiniert | behoben | §4.3 mit graft, repeatW, Ordnung; B.4.4 |
| K2 | nur gerichtete Zyklen | behoben | §2.2 und B.2.3 mit Schnittkanten-Argument |
| K3 | b ≤ c als Satz | behoben | §2.3 und B.2.6 als Iteration ausgewiesen |
| K4 | Komplement mit entscheidbarer Gleichheit | behoben | §10.3 und B.10.3 ohne diese Voraussetzung |
| K5 | Quantorenreihenfolge Nonneg | behoben | §12.4 mit RPos/RNonneg im Wortlaut |
| K6 | Ordnungstreue der Arität | behoben | Kor. 7.2 und Anhang D zitieren `transfer_le` |
| K7 | Zerlegung ohne b > 0 | behoben | Satz 8.3 unterscheidet Identität und Direktheit |
| K8 | 159 vs. 463 | behoben | verification\_report, proof\_correspondence |
| K9 | Anhang A unklar | behoben | Identität ausgeschrieben |
| F1 | `**conditional**` im PDF | behoben | \\emph |
| F2 | Lyons–Peres-DOI | behoben | references.tex |
| F3 | Gaëtan Gilbert | behoben | references.tex und .bib |
| F5 | Kernel-Status veraltet | behoben | Anhang C trennt Archiv, eigenen Lauf und berichteten Lauf sauber |
| – | Lubarsky-Formulierung „IZF“ | unverändert | PRIMARY\_SOURCE\_AUDIT.md, Z. 16 |

Korrektur an meinem eigenen v1-Bericht: Dort stand „252 Logdateien“. Richtig sind 252 Verweise auf neun Logdateien (`Check00` bis `Check08`). Alle neun liegen jetzt bei.

## Formale Ebene

Die formale Grundlage ist unverändert und vollständig belegt. Das eingebettete `evidence/task06_frozen_source.tar.gz` hat denselben SHA-256 wie das Archiv, das ich in v1 mit Lean 4.28.0 neu gebaut habe (`297848d2…f22f`). Build, Fail-closed-Audit, Negativ-Fixtures und leanchecker aus v1 gelten deshalb unverändert. Die mitgelieferten Release-Dateien (`verification_output.txt`, `declaration_signatures.txt`, Matrix, Skripte) sind byte-identisch mit denen im Archiv.

Neu prüfbar waren die historischen Task-5-Logs. Ich habe alle 602 dort abgedruckten Signaturen von Lean gegen den aktuellen Kernel elaborieren lassen: alle 602 exakt gleich, alle Axiomangaben identisch. Damit ist die Aussage, die Task-5-Module seien in Task 6 unverändert, auf Signaturebene bestätigt. Byte-Gleichheit der Dateien bleibt ohne das Task-5-Archiv unbelegt.

Die 289 Signaturblöcke in proof\_correspondence.md sind unverändert korrekt (274 per Lean exakt, 15 wörtlich im Quelltext). Alle neu zitierten Namen existieren im Quelltext, darunter `TreeQ.lift1`, `lift2`, `ofF`, `seqNonneg_resp`, `seqNonneg_of_rnonneg`, `invSeq_isMod`, `approxMod`, `approxSeq`, `seqApprox_of_choice`, `TOField.mulMod`. Nicht existent sind nur die zwei ausdrücklich als künftige Ziele markierten Namen `TriplePath.unary_numer_ne_neg_denom` und `FiniteWord.map_b_le_c`, sowie ein falscher Namensraum (siehe D4).

Die Hinweise auf die fehlenden Ausführungsrechte sind korrekt dokumentiert. `REPRODUCE_RELEASE.sh` setzt sie in einer Kopie, ohne das eingefrorene Archiv zu verändern; das ist die richtige Lösung.

## Neue mathematische Befunde

Keiner der sechs Punkte macht eine Aussage falsch; es sind Lücken oder Ungenauigkeiten in neu geschriebenen Beweisschritten.

**M1. Verstümmelte Gleichung in B.5.2.** Dort steht, ein Normalisierungsschritt erhalte die Relation, „since s(m)+n′ = m+s(n′) is equivalent to m+n′ = m+n′“. Gemeint ist: (s(m), s(n)) ∼ (m, n), weil s(m)+n = m+s(n), und beide Seiten sind s(m+n). Die Variable n′ gehört nicht hinein.

**M2. Soundness und Exactness in §5.2 vertauscht benannt.** Der Text nennt „die Normalform erhält die Relation“ Soundness. In Lean ist das `mkZ_pairEq`. `TreeZ.mkZ_sound` sagt dagegen: verwandte Paare haben dieselbe Normalform. Das steht im Text erst als „conversely … by uniqueness“. Die Mathematik stimmt, die Zuordnung zu den zitierten Lean-Namen nicht.

**M3. Produktkongruenz in B.12.4 mit falscher Schranke.** Für |t′ₙ| wird die Schranke 2^{B\_t} von t benutzt. Aus t ∼ t′ folgt aber nur |t′ₙ| ≤ 2^{B\_t} + ε, also eine um eins größere Zweierpotenz, und die Genauigkeitsindizes verschieben sich. Anhang A macht es richtig: eigene Schranke für t′. B.12.4 sollte dem folgen.

**M4. Entscheidbare Gleichheit im Zusammenhangssatz verschwiegen.** B.10.5 schließt, eine zusammenhängende Menge enthalte keine zwei „nachweislich verschiedenen“ Strahlen, und folgert daraus den Lean-Satz `Ray.connected_subsingleton` (x = y). Der Übergang von „keine Koordinate ist nachweislich verschieden“ zu „alle Koordinaten sind gleich“ braucht entscheidbare Gleichheit auf dem Alphabet. Genau deshalb trägt der Lean-Satz die Voraussetzung `[DecidableEq α]`. Weder §10.4 noch B.10.5 nennen sie.

**M5. Schluss (§17) ohne Transport-Vorbehalt.** Er spricht weiter von einer „literal path-sum account of … positive-denominator rational fraction classes“. Nach der W1-Korrektur sollte auch hier stehen, dass die Körperoperationen transportiert sind.

**M6. Drei Fassungen derselben Inversenkonstruktion.** Hauptteil §12.5: tₙ = 1/s\_{N+n}, Beweis von \[s\]\[t\] = 1 über das verschobene s, Produkt termweise exakt 1. Anhang B.12.6: dieselbe Folge, Beweis mit dem unverschobenen s und Modul μ\_s(j+k), wie in Lean (`mul_invSeq_equiv`). Anhang A: „tₙ = 1/sₙ on that tail“. Alle drei sind korrekt, aber der Changelog nennt nur die Lean-Fassung „source-exact“. Eine einheitliche Darstellung mit Verweis auf B.12.6 wäre sauberer.

## Abdeckung 89/89 und Begleitdokumente

Die Abdeckungsbehauptung stimmt: Anhang B hat genau 89 Abschnitte mit den Labels `supp:1-1` bis `supp:17-2`, in der Reihenfolge der Planungsgliederung, und alle 89 PDF-Seitenangaben in scope\_89.csv treffen die tatsächliche Seite. Das PDF hat 46 Seiten, und ein Neusatz ergibt keine ungelösten Verweise. Die Satzumgebungen zählen wie verlangt 11 Sätze, 11 Propositionen, 2 Lemmata und 1 Korollar.

In den Begleitdokumenten stecken dagegen neun Fehler:

| Nr. | Datei | Befund | Vorschlag |
| --- | --- | --- | --- |
| D1 | verification\_report.md Z. 24, revision\_acceptance.md Z. 39, proof\_correspondence.md Z. 18 | `evidence/projS_inS_check.log` wird als beigelegt gemeldet, fehlt aber. Ebenso fehlt das in verification\_report genannte `compile.log` | Dateien beilegen oder Verweise streichen |
| D2 | 25\_MAIN\_RESULTS\_CROSSWALK.md | alle 25 Zeilenangaben `main.tex:N` liegen eine Zeile vor dem jeweiligen `\begin{…}`; der Schlussvermerk behauptet ausdrücklich, sie seien aktualisiert | um +1 korrigieren, Vermerk anpassen |
| D3 | revision\_acceptance.md | M18 und Gate 4: „compact manuscript … does not fully transcribe … all 89 outline subsections“ widerspricht der neuen 89/89-Fassung | Dokument auf die Langfassung aktualisieren |
| D4 | open\_questions.md Z. 20 | `Topology.no_chart_into_real`; der Satz liegt im Wurzelnamensraum als `no_chart_into_real` | Namen korrigieren |
| D5 | README, CHANGELOG, PROOF\_EXPANSION\_AUDIT | Vorversion als „27 Seiten“ bezeichnet; das gelieferte PDF hatte 26 Seiten (so auch proof\_correspondence.md) | einheitlich 26 |
| D6 | scope\_89.csv/.md | Rollenzuordnung uneinheitlich: Inversion unter Apartness (12.6) und UC ⇔ CA (13.4) als „conditional“, obwohl open\_questions.md die Inversion unbedingt nennt und die Äquivalenz selbst unbedingt bewiesen ist; Diagonalsatz (13.2, braucht Tracking-Daten) als Beweis, SupData-Satz (13.6, braucht Daten) als bedingt. Eine eigene Kategorie „offene Frage“ gibt es nicht; offene Punkte stehen unter „context or limitation“ | Kriterium festlegen (Zusatzprinzip vs. Daten im Satz) und eine Kategorie „offen“ ergänzen |
| D7 | Korrekturauftrag Punkt 4 | verlangte Zuordnung aller Manuskript-Unterabschnitte fehlt (der Hauptteil hat 62, nicht 66); die „Beweiskette“ der 25er-Tabelle ist je eine Zeile; bei Nr. 24 fehlt der Anker `trichotomy_iff_lpo` | nachliefern oder Auftrag als teilweise erfüllt markieren |
| D8 | Anhang B, Nummerierung | „B.33. 8.2.“: die Plannummer 8.2 kollidiert mit §8.2 des Hauptteils, der ein anderes Thema hat | Plannummer als „Plan 8.2“ kennzeichnen |
| D9 | references.tex | „Gaëtan Gilbert“ ausgeschrieben, alle anderen Einträge mit Initialen | „G. Gilbert“ |

## Prüfung der 89 Anhangspunkte

Alle 89 Abschnitte habe ich vollständig gelesen. Die Tabelle fasst je Plankapitel zusammen, was nachgerechnet bzw. gegen Lean abgeglichen wurde.

| Plan | Punkte | Geprüft | Abgleich mit Lean | Befund |
| --- | --- | --- | --- | --- |
| 1 | 1.1–1.4 | Einordnung, keine Beweispflicht; Aussagen zu Interface und Axiomen korrekt | `TOField`, Audit-Policy | – |
| 2 | 2.1–2.6 | Konstruktor-Injektivität; Wurzelpfad E(a::v) = E(v)++\[(v,a::v)\]; Schnittkante: geschlossener Weg müsste e gerade oft kreuzen; Aufzählung Child(b); Iteration b ≤ c; Erschöpfung über obere Schranke | `dpath_root_unique`, `no_cycle`, `vertex_union`, `infinitely_many_children` | – |
| 3 | 3.1–3.3 | Faltungsgesetz S(es++fs) = S(es)+S(fs); Gegenbeispiel m = N, n = N+1 mit Differenz 1 > ε\_k | `pathSum_eq_depth`, `prefixCount_not_isCauchy` | – |
| 4 | 4.1–4.4 | Rekursionseindeutigkeit; Assoziativität (mn)s(p) = m(np)+mn; Antisymmetrie über p+q = 0; d(repeatW(w,v)) = d(w)d(v) | `instCSR`, `depthIso`, `repeatW` | – |
| 5 | 5.1–5.4 | Transitivität; Normalform-Eindeutigkeit (a,0) ∼ (0,b) ⇒ a = b = 0; (m,0)(n,0) = (mn,0) | `mkZ_sound`, `mkZ_exact`, Struktur `TreeZ` | M1, M2 |
| 6 | 6.1–6.7 | Zeugen-Längen p+2+D, q+2+D, q+2; P₁ ≠ P₃ auch bei gleicher Länge (Zähler −D); unär 0 und −1; Kreuzprodukt-Kongruenzen; Transport | `witness`, `lift1`, `lift2`, `ofF` | – |
| 7 | 7.1–7.3 | T\_{B,C}T\_{A,B} = T\_{A,C}, T\_{A,A} = id | `arityIso`, `transfer_le` | – |
| 8 | 8.1–8.9 | B(e\_j−e₀, e\_k−e₀) = 1 nachgerechnet; P\_S² = I − 2P\_L + P\_L² = P\_S; b = 1: P\_L = I | 37 Task-6-Sätze, `transverse_basis` | – |
| 9 | 9.1–9.5 | Spanning über Koordinaten 1..N; Nullkoordinate −Σxⱼ = x₀; Polsterungs-Widerspruch a = 1 und a = 0 | `tvO_span`, `padSucc_u_not_inL` | – |
| 10 | 10.1–10.8 | Präfixrekursion; Gegenbeispiel ξ(n) = n mit idx < b; Komplement offen ohne Entscheidbarkeit; Teilüberdeckung | `union_proper`, `cyl_compl_open`, `cyl_not_compact`, `no_chart_into_real` | M4 |
| 11 | 11.1–11.4 | T(a::w) = π\_{d(w)}(a)::T(w); Vertauschungsinvolution; Unterbaumtausch | `rayAct_swapPerm`, `subtreeSwapAut` | – |
| 12 | 12.1–12.7 | regulär ⇒ μ(k) = k+1; Resampling; Inversenmodul μ\_s(j+2k) und Produktabschätzung μ\_s(j+k); Dichte-Zeuge | `invSeq` (Modul `c.mod (j + (k+k))`), `mul_invSeq_equiv` (`c.mod (j+k)`), `mulMod` | M3, M6 |
| 13 | 13.1–13.7 | λ(k) = max(ν(k+2), M(k+2)), 3ε\_{k+2} ≤ ε\_k; Schwelle max(λ(k+1), M(k+1)); Rückrichtung M(k) = max(ν(k+1), k+1); zweifache ChoiceNN-Anwendung; Modulkomposition ω\_f∘ω\_g | `approxMod`, `approxSeq_converges`, `cauchyApprox_of_complete`, `choice_pair`, `extendR_comp` | – |
| 14 | 14.1–14.5 | Kodierung mit μ(k) = k; Gap-Test 3εₙ; Schranken 1/4 < 1/2 und 1/2 + 1/8 < 1 | `markovSeq_isMod`, `gapTest`, `wlpo_of_unrestrictedLUB`, `lpo_of_bmc` | – |
| 15 | 15.1–15.4 | Rangvergleich, Präfixzählung, Ebenenmarker | `ExtLevel.*` | – |
| 16–17 | 16.1–17.2 | Abgrenzungen und offene Punkte; keine Aussage überzieht den Lean-Stand | – | M5 (§17 Hauptteil) |

## Empfohlene Korrekturen

Nichts davon erfordert neue Lean-Beweise. Alle Punkte sind Text- oder Dateikorrekturen.

1. **D1:** `projS_inS_check.log` und `compile.log` beilegen oder die Verweise in drei Dateien streichen. Ein Paket, das eine fehlende Datei als vorhanden meldet, fällt jedem Gutachter zuerst auf.
2. **D2, D3:** Zeilenangaben der 25er-Tabelle um +1 korrigieren; revision\_acceptance.md auf die Langfassung aktualisieren.
3. **M4:** In §10.4 und B.10.5 die Voraussetzung `[DecidableEq α]` nennen und den Schritt zu x = y ausschreiben.
4. **M2, M1, M3:** Lean-Namen in §5.2 richtig zuordnen; Gleichung in B.5.2 korrigieren; in B.12.4 eigene Schranke für t′.
5. **M5, M6:** Transport-Vorbehalt in den Schluss; Inversenkonstruktion einheitlich darstellen.
6. **D4–D9:** Namensraum, Seitenzahl, Rollenkriterium, Abschnittszuordnung, Nummerierung, Zitierstil.
7. **Optional:** Den Satz `TriplePath.unary_numer_ne_neg_denom` (Ausschluss von −1) formal beweisen. Der Beweis ist kurz; die Lean-Toolchain steht in dieser Umgebung bereit.
