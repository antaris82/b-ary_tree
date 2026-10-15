# Review Task-06: Foundation-Manuskript und Lean-Quelle

Oct 15, 2026 · @antaris

## Ergebnis auf einen Blick

Ich habe keinen falschen Satz und keinen gebrochenen Beweis gefunden. Die formale Grundlage hält vollständig: Ich habe das Lean-Projekt mit Lean 4.28.0 selbst neu gebaut und alle Release-Prüfungen bestanden. Jede dokumentierte Signatur ist von Lean selbst gegen den echten Typ geprüft.

Das Manuskript hat aber vier wesentliche Schwachstellen. Die wichtigste ist eine Darstellungslücke: Die Körperoperationen auf den Pfad-Tripeln werden in Lean über den Bruchkörper transportiert, nicht aus Baumoperationen gewonnen. Das Manuskript sagt das nicht. Dazu kommen eine unvollständige mathematische Aussage im unären Fall und verdeckte Voraussetzungen der Analysis.

| Prüfgegenstand | Umfang | Ergebnis |
| --- | --- | --- |
| Quell-Hashes | 75 Dateien + Archiv | alle identisch |
| Neubau (lake build) | 67 Jobs | erfolgreich |
| Kernel-Audit | 64 Module, 3.014 Konstanten, 60 Pflichtdeklarationen | bestanden, nur `propext` und `Quot.sound` |
| Negativ-Fixtures, leanchecker | 10 Fixtures, 9 Replays | alle wie gefordert |
| Dokumentierte Signaturen | 334 Einträge | 318 von Lean als identisch bestätigt, 15 wörtlich im Quelltext, 1 nur Formatfehler |
| Signaturregister des Archivs | 463 Einträge | Typen und Axiome identisch |
| Zeilen-, Datei-, Axiomangaben | 334 Einträge | alle korrekt |
| Handrechnungen in main.tex | alle Beweise der Abschnitte 2 bis 14 und Anhang A | nachgerechnet, korrekt |
| Befunde |  | 4 wesentlich, 9 kleiner, 5 formal |

Das Fazit für die Einordnung: Die formalen Sätze stimmen, aber der Text verkauft an einer Stelle mehr Eigenständigkeit der Baumarithmetik, als der Lean-Code hergibt.

## Umfang und Methode

Geprüft wurden alle 17 Dateien des Doku-Pakets und das komplette Lean-Archiv (72 Lean-Dateien, 13.501 Zeilen in den 64 mathematischen Modulen). Das zweimal hochgeladene ZIP ist byte-identisch.

Die Prüfung lief auf drei Ebenen:

1. **Formale Ebene.** Lean 4.28.0 installiert, `scripts/verify_release.sh` vollständig ausgeführt, leanchecker auf allen Modulen. Damit sind die Beweise selbst geprüft; ich habe sie nicht Zeile für Zeile gelesen, weil der Kernel das leistet.
2. **Aussagen-Ebene.** Hier liegt das eigentliche Risiko: ob die Lean-Sätze das sagen, was Manuskript und Begleitdokumente behaupten. Ich habe alle 365 in den Dokumenten genannten Namen im Kernel aufgelöst, alle dokumentierten Typen von Lean elaborieren und mit dem echten Typ vergleichen lassen und alle tragenden Definitionen gelesen (Interfaces, Cauchy-Daten, Ordnung, Apartness, Topologie, Kompaktheit, Charts, Basis, logische Prinzipien).
3. **Mathematische Ebene.** Jede Rechnung in main.tex habe ich von Hand nachvollzogen, die dyadischen Fehlerbudgets zusätzlich exakt mit Brüchen nachgerechnet, den unären Sonderfall per Aufzählung geprüft und die Konstanten der Kernbeweise mit dem Lean-Code verglichen.

Nicht prüfbar waren Aussagen, die auf Dateien außerhalb des Pakets verweisen: das Task-5-Archiv, die 252 Logdateien `logs/CheckNN.txt`, `projS_inS_check.log` und `MATHEMATICAL_ARGUMENTS_ADDED.md`.

## Formale Verifikation

Alle archivierten Prüfergebnisse lassen sich unabhängig reproduzieren, mit einer Ausnahme beim Ausführen des Skripts. Die Formulierung „Kernel und leanchecker wurden nicht erneut ausgeführt“ in README, verification\_report.md, Anhang B des Manuskripts und den Audit-Dateien ist damit überholt.

| Schritt | Archiv behauptet | Neu ausgeführt |
| --- | --- | --- |
| Archiv-SHA-256 | `297848d2…f22f` | identisch |
| 75 Einzel-Hashes | Manifest | alle 75 identisch |
| Quell-Fingerprint | `7e126414…b0b7e` | identisch |
| `lake build TreeFoundations TreeAnalysis` | 67 Jobs | 67 Jobs, erfolgreich |
| `source_check.py` | 64 Module erreichbar | 64 von 64, keine Verstöße |
| Fail-closed-Audit | 3.014 Konstanten, 60 Pflichtdeklarationen | identisch |
| Axiomverteilung | 2.162 axiomfrei, 245 `propext`, 817 `Quot.sound` | identisch, kein anderes Axiom |
| Negativ-Fixtures | alle schlagen wie gefordert fehl | alle 10 wie gefordert |
| `leanchecker --fresh` + Präfix-Replays | bestanden | 2 + 7 Läufe, alle Exit 0 |

Die Ausgabe der Schritte 4 und 5 ist zeilengleich mit `release/verification_output.txt`.

**Reproduzierbarkeitsfehler:** Im Archiv fehlen allen Skripten die Ausführungsrechte (`-rw-r--r--`). `verify_release.sh` bricht deshalb nach frischem Entpacken in Schritt 6 mit Exit 126 ab, weil es `./scripts/negative_fixtures.sh` direkt aufruft. Ich habe Schritt 6 und 7 manuell mit `bash` ausgeführt. Abhilfe: Rechte im Archiv setzen oder im Skript `bash scripts/negative_fixtures.sh` aufrufen.

Was der Neubau nicht leistet: Er beweist die elaborierten Lean-Aussagen, nicht ihre Lesart in Prosa. Die Git-Revision `2897ec5e…` bleibt unbelegt, weil das Archiv kein `.git` enthält.

## Abgleich Dokumentation gegen Kernel

Jede in den Begleitdokumenten abgedruckte Signatur entspricht exakt der Aussage im Kernel. Ich habe dazu einen Lean-Befehl geschrieben, der jeden dokumentierten Typ neu elaboriert und mit dem Typ der Konstante vergleicht (Alpha-Äquivalenz, ersatzweise Definitionsgleichheit). Ein reiner Textvergleich wäre wegen Pretty-Printer-Unterschieden unzuverlässig gewesen.

| Quelle | Einträge | Exakt gleich (Lean) | Sonstiges |
| --- | --- | --- | --- |
| proof\_correspondence.md | 289 | 274 | 15 Quelltext-Signaturen, wörtlich an der angegebenen Zeile vorhanden |
| main\_45\_type\_verified\_claims.md | 45 | 44 | `projS_inS`: Block beginnt mit `@Name :`, nicht elaborierbar; Text identisch mit Kernel-Ausgabe |
| release/declaration\_signatures.txt | 463 | 400 per Elaboration | übrige 63: 62 nur im Default-Format druckbar, 1 ist die unten erklärte Tautologie-Darstellung; Text- und Axiomvergleich mit frischer Kernel-Ausgabe: alle 463 identisch |

Auch alle Datei- und Zeilenangaben (334) und alle Axiomangaben stimmen. Von den 365 in den Dokumenten genannten Namen fehlen im Kernel nur Nicht-Deklarationen (Axiome wie `propext`, Dateinamen, Werkzeuge) sowie drei falsch benannte:

- `Close` (main.tex §13.2) heißt im Quelltext `TreeR.RClose`.
- `Topology.compact_cyl_of_sub` (proof\_correspondence.md, Z. 3578) heißt `Ray.compact_cyl_of_sub`; die Datei warnt selbst, der Namensraum sei ungeprüft.
- `apart_of_mul_eq_one` (main.tex §14) existiert als `TreeR.apart_of_mul_eq_one`; nur unqualifiziert zitiert.

Ein Darstellungsproblem im Archivregister selbst: `TreeQ.transfer_letter_indep` erscheint dort als `transfer α β x = transfer α β x`, weil der Default-Druck die beiden verschiedenen Instanzen `I` und `J` verschluckt. Wer das Register liest, sieht eine Tautologie. Gleiches gilt abgeschwächt für `Ray.encode_letter_choice_dependence`.

## Wesentliche Befunde

### W1. Die Körperstruktur auf den Pfad-Tripeln ist transportiert, das Manuskript sagt es nicht

In `TreeNumbers/PathRationalField.lean` sind alle Operationen auf `TreeQ α` so definiert: Tripel in einen Bruch übersetzen (`toFrac`), dort rechnen (`Frac.add`, `Frac.mul`, `Frac.neg`, Inverse), Ergebnis über das Zeugen-Tripel zurückholen (`ofF`). Konkret `addQ := lift2 Frac.add …` mit `lift2 g t = ofF (g (toFrac t) …)`. Die Baumstruktur liefert also nur eine Menge von Repräsentanten; Addition, Multiplikation und Inversion stammen vollständig aus Frac(Z).

Daraus folgt: Satz 7.1 (geordneter Körperisomorphismus zu Frac(Z)) gilt im Wesentlichen per Konstruktion, und Korollar 7.2 (Aritätsunabhängigkeit) ist dann unmittelbar. Das ist mathematisch korrekt, aber eine andere Art Ergebnis, als der Text nahelegt.

Wo das Manuskript es verdeckt:

- Abschnitt 6 definiert die Operationen auf Q(A) nirgends. Er definiert sie auf rohen Brüchen und zeigt dann den Zeugen-Satz.
- Der Beweis von Satz 7.1 sagt nur, die Operationen beider Seiten seien „aus denselben Rohformeln geliftet“. Das ist zutreffend, aber gerade die entscheidende Information.
- Abstract und Einleitung sprechen davon, dass Pfad-Tripel einen geordneten rationalen Körper „liefern“ („yield“).

Korrekturvorschlag: In §6 eine Definition einfügen, x ⊕ y := Ψ(Φ(x) + Φ(y)) und entsprechend für ·, −, Inverse. Dazu eine Bemerkung, dass die Körperstruktur damit transportiert ist und Satz 7.1 deshalb strukturell ist. Als eigentlich baumspezifisches Resultat bleibt der Zeugen-Satz: Jeder Bruch hat einen Repräsentanten aus drei paarweise verschiedenen Wörtern, und dafür genügen zwei Buchstaben. Abschnitt 6.7 der Planungsgliederung („What branching contributes“) wäre der richtige Ort.

### W2. Die unäre Obstruktion ist unvollständig angegeben

Main.tex §6.4 und MATHEMATICAL\_PROOF\_AUDIT.md (Zeile 7) sagen, im unären Fall verhindere die Verschiedenheitsbedingung nur einen Zeugen für die Null. Tatsächlich fehlen genau zwei Werte: 0 und −1.

Begründung: Über einem Buchstaben sind Wörter genau dann gleich, wenn ihre Längen gleich sind. Paarweise verschiedene Wörter heißt also d1 ≠ d2, d1 ≠ d3, d2 ≠ d3. Mit a = d1 − d2 und D = d2 − d3 > 0 folgt aus d1 ≠ d2, dass a ≠ 0, und aus d1 ≠ d3, dass a ≠ −D, also a/D ≠ −1. Jeder andere Wert ist darstellbar (d3 groß genug wählen). Das Bild in Frac(Z) ist damit exakt Q \\ {0, −1}. Eine Aufzählung aller Tripel mit Längen unter 40 bestätigt das: Unter allen Brüchen p/q mit |p| ≤ 8, q ≤ 7 fehlen genau 0 und −1.

Der Lean-Satz `TriplePath.unary_toFracQ_ne_zero` behandelt nur die Null und ist korrekt. Falsch ist nur die Lesart „Obstruktion für die Null“ als vollständige Beschreibung. Korrekturvorschlag: Satz um −1 ergänzen, optional einen Lean-Satz `unary_toFracQ_ne_neg_one` nachziehen.

### W3. Die Analysis setzt mehr voraus, als „ordered-field interface“ verrät

Das Interface `TOField` (`TreeAnalysis/OrderedField.lean:28`) verlangt neben den Körper- und Ordnungsaxiomen zwei starke Zusatzdaten:

- `decNonneg`: Die Ordnung des Grundkörpers ist **entscheidbar**.
- `archBound` mit `arch_spec`: eine **explizite archimedische Schranke als Funktion**, nicht nur eine Existenzaussage.

Die Abschnitte 12 bis 14 hängen daran. Die Kotransitivität entscheidet die rationale Ordnung an einem Index (`TOField.le_or_lt`), die Injektivität von ι nutzt Archimedes, die Gap-Tests in §14 benutzen `decide`. Das Manuskript nennt die Voraussetzung nur als „the project's ordered-field interface“, und Sätze wie 14.1 lauten „for every base satisfying the project's ordered-field interface“.

Für die konstruktive Einordnung ist das wichtig: Ohne Ausschluss des Dritten auszukommen, ist hier nur möglich, weil die Entscheidbarkeit auf Ebene des Grundkörpers vorausgesetzt ist. Für K = Q(A) ist das erfüllt und legitim, muss aber dastehen. Korrekturvorschlag: Zu Beginn von §12 die vier Bestandteile ausdrücklich auflisten (Körper der Charakteristik 0, totale entscheidbare Ordnung, verträgliche Positivität, archimedische Schrankenfunktion).

### W4. Teile der Belegkette sind nicht im Paket

Mehrere Aussagen stützen sich auf Dateien, die weder im Doku-Paket noch im Lean-Archiv liegen: die 252 Verweise auf `logs/CheckNN.txt`, `projS_inS_check.log` (mit angegebenem SHA-256), das Task-5-Archiv und `MATHEMATICAL_ARGUMENTS_ADDED.md` (open\_questions.md, Z. 21). Damit sind drei Behauptungen aus dem Paket heraus nicht überprüfbar: die „603 individual elaborated-signature checks“, die Byte-Gleichheit aller Task-5-Module mit Task 6 und die genannte Ergänzungsdatei.

Inhaltlich ist der Schaden begrenzt, weil mein Neubau die Kernel-Ebene vollständig ersetzt. Als Belegpaket für Dritte sollte es aber in sich geschlossen sein. Korrekturvorschlag: Dateien beilegen oder die Verweise durch den Neubau-Befund ersetzen.

## Kleinere mathematische und Darstellungsbefunde

Keiner dieser Punkte macht eine Aussage falsch; sie betreffen Präzision und Übereinstimmung mit dem Lean-Text.

| Nr. | Stelle | Befund | Lean-Stand | Vorschlag |
| --- | --- | --- | --- | --- |
| K1 | main.tex §4.3 | Addition, Multiplikation und Ordnung auf D(A) werden benutzt, aber nicht definiert | `addD` = Verkettung (`graft`), `mulD` = `repeatW`, `LED` über `count` | drei Definitionszeilen ergänzen |
| K2 | §2.3 | Text schließt nur gerichtete Zyklen aus | `Word.no_cycle` zeigt mehr: keine ungerichtete Wanderung mit paarweise verschiedenen Kanten zurück zum Start | stärkere Aussage zitieren |
| K3 | §2.4 | „Für b ≤ c gibt es buchstabenweise Injektionen“ | nur b → b+1 (`wordSucc`) und b → ω (`wordOmega`) deklariert; b ≤ c folgt durch Iteration, ist aber kein Satz | so formulieren oder Satz ergänzen |
| K4 | §10.3 | Offenheit des Zylinderkomplements wird mit entscheidbarer Gleichheit begründet | `Ray.cyl_compl_open` braucht keine; Präfix der Länge \|w\| genügt | Voraussetzung streichen |
| K5 | §12.3 | „Für jede Präzision k ist ein Repräsentant schließlich ≥ −ε\_k“ (∀k ∃Repr.) | `RNonneg`: ∃ Repräsentant ∀k; gleichwertig nur wegen Repräsentantentransfer | Quantorenreihenfolge an Lean angleichen |
| K6 | Kor. 7.2, Anhang C | Aritätsisomorphismus „als geordnete Körper“, zitiert wird `TreeQ.arityIso` | `arityIso` ist nur `FieldIso`; Ordnungserhalt steht in `transfer_le` (ArityCompletionTransfer.lean), Reflexion folgt über die Inverse | `transfer_le` zitieren |
| K7 | Satz 8.3 | Zerlegung x = P\_L x + P\_S x unter b > 0 formuliert | `ChildModule.decomposition` gilt ohne b > 0; nur Eindeutigkeit und `projS_inS` brauchen es | Hypothese präzisieren |
| K8 | verification\_report, proof\_correspondence | „159-row signature register“ | die Signaturdatei hat 463 Einträge; 159 ist die Zeilenzahl der Matrix `FINAL_AXIOM_AND_LAW_MATRIX.md` | Begriffe trennen |
| K9 | Anhang A | „In the second identity the left and right denominators should be interpreted for …“ | Rechnung korrekt, Satz unklar | Identität ausschreiben: (ae+cd)de′ = (ae′+c′d)de aus ce′ = c′e |

Zu K2 und K4: Hier ist das Manuskript vorsichtiger als nötig. Das ist harmlos, verschenkt aber Stärke, die der Lean-Code bereits hat.

## Formales und Literatur

Das PDF entspricht dem Quelltext: Ich habe main.tex neu gesetzt und wortweise mit dem gelieferten PDF verglichen. Die Abweichungen sind nur Ligaturen und Seitenzahlen im Inhaltsverzeichnis (wegen einer Ersatzschrift in meiner Umgebung). Das gelieferte PDF hat 26 Seiten im Letter-Format, wie angegeben.

| Nr. | Stelle | Befund |
| --- | --- | --- |
| F1 | main.tex Z. 414, PDF S. 13 | Markdown-Fettdruck `**conditional**` steht wörtlich im PDF; gemeint ist `\emph{conditional}` |
| F2 | references.tex | Lyons–Peres ohne DOI, obwohl MATHEMATICAL\_PROOF\_AUDIT.md (Korrektur 6) behauptet, sie sei ergänzt. Nur references.bib hat sie; das PDF nutzt references.tex. DOI 10.1017/9781316672815 per Crossref bestätigt |
| F3 | references.bib/.tex | Vorname „Gaetan“ statt „Gaëtan“ Gilbert; OpenAlex führt den Tagungsband CPP 2017 mit Jahr 2016, S. 112–124 |
| F4 | open\_questions.md | zwei konkurrierende Hauptüberschriften, Stand „2026-10-14“ neben Paketdatum 15.10. |
| F5 | README, verification\_report, Anhang B, Audits | „Kernel nicht neu ausgeführt“ ist nach meinem Neubau überholt und sollte ersetzt werden |

Literaturmetadaten, geprüft:

- Lubarsky, Math. Logic Quart. 53(4–5), 396–414 (2007), DOI 10.1002/malq.200710007: per Crossref und Publikationsliste des Autors korrekt.
- Axler, 4. Aufl., DOI 10.1007/978-3-031-41026-0: korrekt.
- Bridges–Richman, LMS LNS 97, DOI 10.1017/CBO9780511565663: korrekt.
- Serre, Kechris, Bass et al., Bishop–Bridges: Reihen, Bände und Jahre stimmen.

Zu PRIMARY\_SOURCE\_AUDIT.md: Die Zusammenfassung von Lubarsky spricht von „IZF ohne Auswahl“. Das Abstract sagt allgemeiner „constructive set theory (without Countable Choice)“. Die Aussage ist damit etwas spezifischer als die geprüfte Quelle.

Sources: [Crossref Lubarsky](https://api.crossref.org/works/10.1002/malq.200710007), [Lubarsky Publikationsliste](https://www.math.fau.edu/people/faculty/lubarsky/publications.php), [Lubarsky arXiv-Abstract](https://arxiv.org/abs/1510.00639), [Crossref Lyons–Peres](https://api.crossref.org/works/10.1017/9781316672815), [OpenAlex Gilbert](https://api.openalex.org/works/doi:10.1145/3018610.3018614), [Springer Axler](https://link.springer.com/book/10.1007/978-3-031-41026-0)

## Abschnittsweise Prüfung von main.tex

Alle Rechnungen und Beweisschritte sind korrekt; die Spalte „Befund“ verweist auf die Punkte oben. „Lean“ nennt die Deklaration, deren Aussage ich gegen den Text gelesen habe.

| § | Aussagen | Prüfung | Lean | Befund |
| --- | --- | --- | --- | --- |
| 2 | eindeutiger Wurzelpfad, Zusammenhang, Azyklizität, unbeschränkte Tiefe, Vereinigung endlicher Aritäten | Induktion über Elternrelation nachvollzogen | `dpath_root_unique`, `connected`, `no_cycle`, `vertex_union`, `edge_union` | K2, K3 |
| 3 | Pfadsumme = Tiefe; n ↦ n nicht Cauchy | Nachfolgergleichung; Differenz 1 überschreitet jede Toleranz < 1 | `pathSum_eq_depth`, `prefixCount_not_isCauchy` | – |
| 4 | unärer Halbring, Ordnung, Kürzung, D(A) ≅ N | Rekursionsgleichungen, Distributivität; φ wohldefiniert, injektiv, Inverse \[a^n\] | `instCSR`, `depthIso` | K1 |
| 5 | Differenzpaare, Transitivität, Normalform, Produkt (mp+nq, mq+np), Nullteilerfreiheit | Transitivität aus Addition beider Gleichungen und Kürzen von p+q | `mkZ_exact`, `mul_eq_zero`, `instCRing` | – |
| 6 | Bruchrelation, Kongruenz von +, ·, Assoziativität, Distributivität, Inverse, Charakteristik 0, Zeugen-Tripel, Ordnung, Archimedes | alle Kreuzprodukt-Identitäten ausmultipliziert; Zeugen: Längen p+2+D, q+2+D, q+2, Verschiedenheit über 1. bzw. 2. Buchstaben; Ordnungs-Identität (c d′ − a′ e) d = (c d − a e) d′ | `universal_witness`, `FracQ.instTField`, `instTOField` | W1, W2 |
| 7 | geordneter Isomorphismus zu Frac(Z), Aritätsunabhängigkeit | Beweis korrekt, aber per Konstruktion (Transport) | `orderedFieldIsoFracQ`, `arityIso`, `transfer_le` | W1, K6 |
| 8 | Bilinearität, Basen {u\_b} und {e\_j − e\_0}, dim 1 und b−1, P\_L, P\_S linear, idempotent, komplementär, Bild/Kern, orthogonale Zerlegung, Permutationsinvarianz | Basis-Indexmenge in Lean geprüft: `Child one` bzw. `Child bp` mit b = bp+1; σ(P\_S x) = σ(x) − b·b⁻¹σ(x) = 0 | `longitudinal_basis`, `transverse_basis`, 37 Task-6-Sätze, `dot_perm` | K7 |
| 9 | abzählbare Basis e\_{i+1} − e\_0, Polsterung, Unvereinbarkeit der Linien, Einsfunktion nicht endlich getragen | Koordinaten 0 und b liefern a = 1 und a = 0 | `tvO_indep`, `tvO_span`, `padSucc_u_not_inL`, `allOnes_not_finSupp` | – |
| 10 | Strahlen, echte Vereinigung, Zylinder offen/abgeschlossen, Trennung, total unzusammenhängend, keine isolierten Punkte, Zylinder in N^N nicht kompakt, nicht lokal kompakt, Charts | Überdeckung durch C(a::w); Teilüberdeckung verfehlt größeren Buchstaben; abgeschlossener Teilraum kompakter Menge; Definitionen von Topologie, Kompaktheit, Zusammenhang, Chart gelesen | `union_proper`, `cyl_compl_open`, `connected_subsingleton`, `no_isolated`, `cyl_not_compact`, `not_locallyCompactAt`, `no_chart_into_real` | K4, F1 |
| 11 | Transitivität ebenenweiser Automorphismen, invariante Abbildungen konstant, Gegenbeispiel | Vertauschungs-Involution pro Ebene; `subtreeSwap` entspricht der Beschreibung | `rayAct_swapPerm`, `invariant_const`, `levelwise_converse_false` | – |
| 12 | Äquivalenz, Regularisierung ρ(n) = max μ(i+1), Summen- und Produktmodul, Ring, Positivität, Kotransitivität, Dichte, Inverse | alle dyadischen Budgets exakt nachgerechnet, u. a. ε\_{k+1} − 2ε\_{k+3} = ε\_{k+2}, ε\_k − ε\_{k+1} − 2ε\_{k+3} = ε\_{k+2}, 2^B ε\_{k+1+B} = ε\_{k+1}, 2^{2κ} ε\_{k+2κ} = ε\_k; Konstanten identisch mit `lt_cotrans` (k+3) und `exists_rat_between` (k+2, Zeuge a\_{n0} + ε\_{k+1}) | `instCRing`, `ofQ_injective`, `lt_cotrans`, `eq_of_not_apart`, `exists_inv_of_apart`, `exists_rat_between` | W3, K5 |
| 13 | Eindeutigkeit des Grenzwerts, Diagonalsatz mit 3ε\_{k+2} ≤ ε\_k, UC ⇔ CA, Auswahl, SupData, endlicher und monotoner Fall, gleichmäßig stetige Fortsetzung | Rückrichtung UC ⇒ CA braucht keine Auswahl: M(k) = max(ν(k+1), k+1) genügt; monotoner Fall: N\_k, u\_k, s\_k stimmen mit `SupData.ofMonotone` überein, 2ε\_{k+2} + ε\_{k+1} = ε\_k | `limit_unique`, `limit_of_approx`, `complete_iff_cauchyApprox`, `complete_of_choice`, `SupData.isLUB`, `extendR_unique` | – |
| 14 | MP, LPO, WLPO äquivalent zu Inversion, Null-oder-Apart, entscheidbarer Null; Untergrenzen für LUB und monotone Konvergenz | X\_p mit Modul μ(k) = k stimmt mit `markovSeq_isMod`; Gap-Test 3ε\_n < \|r\_n\| identisch mit `gapTest`; Mengen und Folgen der Untergrenzen identisch mit `wlpo_of_unrestrictedLUB`, `lpo_of_bmc` | `inv_iff_markov`, `zeroOrApart_iff_lpo`, `decidableZero_iff_wlpo`, `trichotomy_iff_lpo` | W3 |
| 15–16 | Einordnung, Ebenenmarker, offene Fragen | Ebenenmarker: Wurzel = finite 0, Strahl = posInfinity, negInfinity unbenutzt; Grenzen korrekt benannt | `ExtLevel.*` | – |
| A | Anhang-Rechnungen | alle Identitäten nachgerechnet | – | K9 |

## Empfohlene Korrekturen

Vordringlich sind W1 und W3, weil sie beeinflussen, wie ein Fachleser die Ergebnisse einordnet.

1. **W1:** In §6 die Operationen auf Q(A) als Transport über Φ/Ψ definieren; in §7 und im Abstract sagen, dass Satz 7.1 strukturell ist und der Zeugen-Satz der baumspezifische Beitrag.
2. **W3:** Zu Beginn von §12 die Bestandteile des Ordnungskörper-Interfaces ausschreiben, insbesondere entscheidbare Ordnung und archimedische Schrankenfunktion.
3. **W2:** Unäre Obstruktion auf {0, −1} korrigieren, in main.tex und MATHEMATICAL\_PROOF\_AUDIT.md.
4. **Status:** „Kernel nicht neu ausgeführt“ durch den reproduzierten Befund ersetzen; Ausführungsrechte der Skripte im Archiv setzen.
5. **W4:** Fehlende Belegdateien beilegen oder Verweise entfernen.
6. **F1, F2, F3:** `**conditional**`, Lyons–Peres-DOI in references.tex, Gaëtan Gilbert.
7. **K1 bis K9:** Präzisierungen laut Tabelle; vor allem K6 (`transfer_le` als Beleg der Ordnungstreue) und K3 (b ≤ c).
8. **Namen:** `RClose`, `Ray.compact_cyl_of_sub`, `TreeR.apart_of_mul_eq_one` voll qualifiziert zitieren.
