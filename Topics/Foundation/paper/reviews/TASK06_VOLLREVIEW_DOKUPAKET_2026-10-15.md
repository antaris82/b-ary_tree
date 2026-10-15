# Vollreview des Dokumentationspakets zur Baumgrundlagen-Mathematik (Task 6)

**Prüfdatum:** 15. Oktober 2026  
**Prüfobjekt:** `TASK06_FOUNDATION_CRITICAL_REVIEW.zip` (SHA-256 `11f5e64cd7f2b923f28e04a9ce9ecdbfe6cd5d79515051c3e7993824aa4ac86e`), 17 Paketdateien.  
**Gegenquelle:** Task-6-Repository `output-final_aristotle/`, Lean 4.28.0; Quellenfingerabdruck `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.  
**Abnahmeempfehlung:** **MAJOR EDITORIAL / MATHEMATICAL EXPOSITION REVISION; NO DEMONSTRATED FALSE PRINCIPAL THEOREM.** Einige exakt zu behebende Präzisions- und Dokumentationsmängel; keine nachgewiesene Inkonsistenz des Lean-Beweiskerns.

## 1. Vorgehen, Umfang und Evidenzstufen

1. Alle **17 ZIP-Einträge** inventarisiert und auf CRC-Lesbarkeit geprüft. `main.tex` (831 Quellzeilen), das vollständige 26-seitige `main.pdf`, beide Bibliografien, die 133-KB-Beweiskorrespondenz, das 89-Abschnitts-Crosswalk, die 45 Haupttypen, mathematische und primärquellenbezogene Audits sowie das offene Fragenregister gelesen und miteinander abgeglichen.
2. **Alle 25 ausdrücklich benannten Theoreme/Propositionen/Lemmata/Korollare** im Haupttext einzeln gegen die entsprechenden Lean-Definitionen und -Sätze sowie ihre Hypothesen gehalten; zusätzlich die übrigen mathematischen Aussagen der **66 Manuskript-Unterabschnitte** und der beiden Anhänge sachlich geprüft. Der Anhang dieses Reviews erfasst die **89 Abschnitte des ursprünglichen Arbeitsplans** einzeln. Keine Auswahl nur einiger Theoreme als Stellvertreter für alle.
3. Sämtliche **289** in `proof_correspondence.md` mit `*.lean:Zeile` bezeichneten Deklarationen (252 geerbte + 37 Task-6-Ergänzungen) automatisiert auf reale Datei, angegebene Zeilennummer und Deklarationsname geprüft: **289/289 Treffer, 0 falsche Pfade oder Zeilen**. Diese Prüfung bescheinigt die *Referenzintegrität*, nicht den Wahrheitsgehalt jeder informellen Umformulierung.
4. Die **75** in `SOURCE_MANIFEST_SHA256.txt` aufgeführten Dateihashes gegen den extrahierten eingefrorenen Task-6-Code berechnet: **75/75 korrekt**. Die projektspezifische statische Prüfung `scripts/source_check.py` im lokalen Task-6-Verzeichnis ausgeführt: **64/64 erreichbare mathematische Module, PASS**. ZIP-CRC: PASS.
5. `main.pdf` vollständig in **26 Seitenbilder** gerendert und mittels Kontaktblatt auf Seitenfolge, Tabellen, Formeln, Seitenumbruch, Inhaltsverzeichnis und Literatur kontrolliert. PDF ist lesbar und entspricht plausibel `main.tex`; archiviertes LaTeX-Protokoll bestätigt Kompilation. Keine unabhängige Neuerstellung des PDFs behauptet.
6. Primärliteratur-Bibliografie für zehn Einträge gesichtet und exemplarisch im vorliegenden Review nochmals gegen Verlags-/Originalquellen abgeglichen (Serre, Kechris, Axler, Bass u.a., Lubarsky, Bridges–Richman, Gilbert). Zugänglichkeitsstufen offengelegt.
7. **Nicht erfolgt:** Neuer Lean-/Lake-/`leanchecker`-Lauf in dieser Umgebung (Programme fehlen). Die Kernel-Aussagen beruhen auf den protokollierten Läufen des eingefrorenen Task-6-Repositories und auf dem Quelltextabgleich. Auch eine neue unabhängige formal-semantische Prüfung aller 3.014 kompilierten Konstanten ist hier nicht erfolgt. **Dieses Vollreview umfasst den gesamten Dokumentationsinhalt und seine 289 überprüften Deklarationsnachweise; es ist kein zweiter Beweis-Kernel.**

**Unterschiedliche Evidenzniveaus:** [F] Archivierte Lean-Deklaration samt dokumentierter Kernelprüfung; [Q] Quellcode direkt geprüft; [M] informeller mathematischer Beweis eigenständig rekonstruiert oder elementar geprüft; [B] bedingtes Resultat mit ausdrücklicher Prämisse; [O] offen/nicht im Quellstand bewiesen; [D] redaktionelle oder semantische Differenz.

## 2. Zusammenfassendes Fachurteil

**Positiv:** Das 26-seitige Manuskript behandelt nun die vollständige Themenfolge Bäume/Pfade, Zahlensysteme, endlichdimensionale Rang- und Projektionssätze, abzählbaren transversalen Grenzraum, Strahlenrand/Topologie, Automorphismen, Cauchy-Quotient und konstruktive logische Grenzen. Die Dimensionsanalyse und Task-6-Projektionen haben einen angemessenen mathematischen Hauptabschnitt. Alle 25 formell ausgezeichneten Hauptresultate sind der Quelle nach korrekt eingeschränkt oder auf nachvollziehbare Argumente zurückführbar; kein widerlegtes Haupttheorem wurde entdeckt. In der Mathematik werden algebraischer Rang, topologische Dimension, Kodierung, Cauchy-Vollständigkeit und physikalische Interpretation sauber auseinandergehalten.

**Nicht abschließend akzeptabel:** (a) Der tatsächlich gewählte ganzzahlige Träger wird als Quotient statt als normalisierter Paartyp beschrieben; (b) der informelle Beweis der ungerichteten Zyklenfreiheit fehlt, obwohl er im Code vorliegt; (c) eine Reihe komplexer Resultate wird nicht mit so vollständigen mathematischen Argumenten belegt, wie die Behauptung eines ausnahmslos autonomen Papers nahelegen könnte; (d) ein älteres, mit dem neuen Doku-Paket unvereinbar aktualisiertes Register enthält eine nicht mitgelieferte Beilage; (e) das Paket enthält keine eingefrorene Lean-Quelle und keine eigenständige Wiederholung der Kernelprüfung; (f) offene Proof-/Reproducibility-Statusangaben brauchen eine gemeinsame, datierte kanonische Fassung.

**Reparaturart:** Inhaltliche Überarbeitung des Papers und der Nachweisdokumentation, **nicht** ein neuer mathematischer Grundlagen-Task. Eine Änderung der bestehenden bewiesenen Lean-Strukturen ist nach den vorliegenden Befunden nicht erforderlich.

## 3. Konkrete Befunde und verbindliche Korrekturen

### K1 — Ungenaue Identifikation des ganzzahligen Zahlenträgers (P1: mathematisch-semantisch)

**Fundstelle:** `main.tex` Z. 102–106, besonders Z. 104 „Quotient classes form Z“.  
**Lean:** `TreeNumbers/PathIntegers.lean`, Z. 91–107: `structure TreeZ where pos : TreeN; neg : TreeN; normal : pos = zero ∨ neg = zero`. `mkZ` bildet rohe Paare auf ihren eindeutigen Normalformrepräsentanten ab; `mkZ_sound` und `mkZ_exact` zeigen die exakte Übereinstimmung der Normalformen mit `PairEq`.  
**Befund:** Der mathematische *Isomorphietyp* stimmt mit dem Differenzquotienten überein. Der **tatsächlich definierte Träger ist aber nicht `Quot PairEq`**, sondern ein Untertyp/Strukturtyp normalisierter Paare. Gerade bei einer Arbeit über die Fundierung der Konstruktion muss dies präzise stehen.  
**Reparatur:** „Die Gleichheitsklassen der Relation werden durch eindeutig normalisierte Paare repräsentiert; wir definieren `Z_T` als den Typ dieser Normalformen. Die Abbildung von rohen Paaren identifiziert genau die äquivalenten Daten.“ Ein eigener universeller Grothendieck-Satz darf daraus nicht abgeleitet werden.

### K2 — Ungerichtete Zyklenfreiheit im mathematischen Baumbeweis nicht vollständig dargestellt (P2: Beweisabdeckung)

**Fundstelle:** `main.tex` Z. 63–65 („A nontrivial directed cycle is excluded …“).  
**Lean:** `PrimitiveTree/FiniteWords.lean`, Z. 259–271, `Word.no_cycle`: Ein positiver, geschlossener **ungerichteter Walk mit paarweise verschiedenen Kanten** ist unmöglich; `bridge_out`/`bridge_in` verwenden den eindeutig überschrittenen Teilbaumrand.  
**Befund:** „Tiefe nimmt entlang gerichteter Kanten zu“ schließt gerichtete Zyklen aus, aber alleine nicht ungerichtete Zyklen. Der eigentliche ungerichtete Satz ist vorhanden, wird im Paper jedoch nicht ausgeführt.  
**Reparatur:** Einen Satz zur Zyklenfreiheit der ungerichteten Graphstruktur mit einem kurzen Teilbaum-/Brückenkantenargument hinzufügen, statt nur gerichtete Zyklen auszuschließen. Keine neue Lean-Arbeit.

### K3 — Schwierige informelle Beweisschritte bleiben teilweise source-dependent (P2: Exposition, KEIN fehlendes Lean-Theorem)

**Fundstellen:** `main.tex` Z. 89–97, 107–115, 155–165, 176–185, 449–565, 589–656, 661–710; dazu Anhang Z. 736–797.  
**Befund:** Einige Beweise sind solide Kurzbeweise; andere verweisen an ihren entscheidenden nichttrivialen Stellen auf vorhandene Quelllemmas, beispielsweise die logische Rational-Order-Dichotomie, die Quotientenverträglichkeit von Positivität/Nonnegativität, die Unabhängigkeit inverser Repräsentanten, die Modulusgewinnung und die Präzisionselimination. Als informelle Manuskriptbeweise sind sie nicht alle *ohne Heranziehung dieser Zwischenlemmata* vollständig.  
**Besondere Evidenz:** `main_45_type_verified_claims.md` enthält noch **elf ursprünglich als `O` oder `O/C` markierte Beweisexpositionspositionen** (fünf `O`, sechs `O/C`), darunter `TreeQ.instTField`, `TreeQ.instTOField`, der geordnete Bruchisomorphismus, die reelle Ringstruktur, apartheitsbasierte Inversion, Diagonallimit und MP/LPO/WLPO-Korrespondenzen. Diese **historischen** Markierungen bedeuten nicht, dass elf Lean-Beweise fehlen und auch nicht, dass nach den neu hinzugefügten mathematischen Erläuterungen jeder dieser elf Punkte weiterhin unbearbeitet ist. Sie müssen gegen den *neuen* Manuskriptstand neu klassifiziert werden.  
**Reparatur:** Den mathematischen Beweisanhang gezielt nach eigenständig formulierbaren Zwischenlemmata ordnen und jeden nichttrivialen „source proves“ Schritt als explizites Hilfslemma mit Beweis oder klarer Literatur-/Supplementreferenz nachführen. Keine Wiederholung sämtlicher elementarer Induktionen erforderlich; aber keine impliziten Auswahl-, Ordnungs- oder Kürzungsvoraussetzungen.

### K4 — Veraltete oder nicht ausgelieferte Audit-Beilage (P2: Dokumentationskonsistenz)

**Fundstelle:** `open_questions.md`: „Status 2026-10-14“ und Verweis auf `MATHEMATICAL_ARGUMENTS_ADDED.md`. Die Datei existiert **nicht** unter den 17 ZIP-Einträgen. Die aktuelle Fassung datiert überwiegend 2026-10-15, der neueste inhaltliche Audit heißt `MATHEMATICAL_PROOF_AUDIT.md`.  
**Reparatur:** Datum, Release-Status, Dateiname und Prüfmatrix aktualisieren; eine kanonische offene-Fragen-Liste statt teils historischer Task-5-Dokumentation herstellen. Nur nachweislich offene Aussagen in diesen Teil stellen.

### K5 — Doku-Paket ist nicht vollständig eigenständig reproduzierbar (P2: Release)

**Befund:** Das ZIP enthält Papier, `SOURCE_MANIFEST_SHA256.txt`, Auditberichte und Proof-Crosswalk, aber **keine** eingefrorenen `.lean`-Quellen bzw. originale Kernel-Ausgaben/Einzelprüfungslogs. Sie stehen im separaten Task-6-Archiv zur Verfügung. Die Einzelkorrespondenz zitiert `logs/Checkxx.txt` aus früheren Prüfläufen, die im Paper-ZIP ebenfalls nicht enthalten sind. Das ist für ein Dokumentationspaket legitim, doch als *alleinige* reproduzierbare Publikation nicht hinreichend.  
**Reparatur:** Dokumentierten, unveränderlichen Release-Link oder Archivanhang zum Task-6-Code mit SHA-256 und Ausführungsschritten hinzufügen. Alternativ vollständige Lean-Quelldateien als `formal/` der Veröffentlichung beilegen. Herkunft geerbter Task-5-Signaturen und Task-6-Ergänzungen separat ausweisen. Der aktuelle Fingerabdruck von 75 Quellen ist **inhaltlich korrekt**.

### K6 — Reichweite des eigenen Audits darf nicht mit „alle Proofs formal erneut geprüft“ verwechselt werden (P2: Prüftiefe)

**Fundstelle:** `MATHEMATICAL_PROOF_AUDIT.md` bezeichnet seine eigenen 24 Zeilen ausdrücklich als „spot audit“. `main_45_type_verified_claims.md` verzeichnet 45 priorisierte Typprüfungen, die Proof-Crosswalk-Tabelle umfasst 252 ältere und 37 neue benannte Deklarationen.  
**Befund:** Strukturintegrität, mathematische Prosa und Kernel-Replay sind unterschiedliche Prüfungen. Mein eigenständiger Abgleich der 289 Verweise deckt sämtliche *benannten Verweise* ab, nicht sämtliche 3.014 Kernelkonstanten und auch nicht eine neue 2.-Kernel-Korrektheitsgarantie.  
**Reparatur:** Diese Stufen in Titel und Summary konsistent kennzeichnen; nach Möglichkeit die 24 Zeilen als „kritische Auswahl vertieft rekonstruierter Beweise“ benennen und auf die externe Gesamttabelle der 25 benannten Haupttheoreme und die 89 Abschnittseinträge verweisen.

### K7 — Konzeptionelle Grenzziehungen sind richtig und müssen erhalten bleiben (P0: NICHT reparieren)

- Die rationalen Körper sind für Alphabete mit zwei verschiedenen Symbolen isomorph; das bedeutet nicht, dass jeder Vertex einen rationalen Wert trägt.
- `dim S_b=b−1` ist **algebraischer Rang**, keine topologische oder physikalische Dimension des Baums.
- Für `b=0` gilt das Bilinearitätslemma, aber **nicht** die positive-Arity-Rangzerlegung.
- Orthogonalität gilt für die **festgelegte symmetrische Bilinearform**; keine allgemeine positive Definitheit oder Hilbertstruktur behaupten.
- Im ω-Fall ist das Hindernis nur für **endlich unterstützte Funktionen und Nullergänzung** bewiesen.
- Finite-arity-Randkompaktheit, `IntervalsConnected K` und Kartenhindernisse bleiben unbewiesen oder bedingt.
- Der Ray-Rand und der Zahlen-Cauchy-Quotient sind **nicht kanonisch identifiziert**.
- Inversion aus `x # 0` ist bewiesen, aus `x≠0` nur unter der mit MP äquivalenten Zusatzstärke; LPO und WLPO nur logisch charakterisiert.
- Modullose Vollständigkeit und allgemeine LUB sind **nicht** ohne Auswahl-/Approximationsvoraussetzungen bewiesen.
- Die levelwise-only-Klassifikation aller Baumautomorphismen ist widerlegt, nicht offen.

## 4. Prüfung aller 25 ausdrücklich formulierten Hauptresultate

**Leseschlüssel:** **OK** = präzise formuliert und mit den Quellbeweisen unter der angegebenen Hypothese vereinbar; **OK–kurz** = gültiger Satz, aber nicht alle Zwischenlemmata informell gezeigt; **Korrektur** = zu berichtigen oder präzisieren. Bei allen bedeutet „mit Lean gedeckt“ Quellcode plus archivierte Kernelprotokolle, nicht mein eigener neuer Kernel-Lauf.

| Nr. | Manuskript, Zeile | Hauptsatz / Formel | Zentraler Quellnachweis | Urteil und genaue Grenze |
|---:|---|---|---|---|
| 1 | 56 | Eindeutiger gerichteter Wurzelpfad | `Word.dpath_root_unique` | **OK**. Nur gerichtete Pfadlisten; umgekehrte Wege nicht eingeschlossen. |
| 2 | 72 | Einheitskantensumme = Worttiefe | `Word.pathSum_eq_depth` | **OK**. Keine pfadadressabhängige Messung. |
| 3 | 89 | Natürliche unäre Zählungen als kommutativer Halbring mit Induktion und Rekursion | `TreeN.instCSR`, `TreeN.add_assoc`, `add_comm`, `mul_assoc`, `mul_comm`, `left_distrib`, `right_distrib` | **OK**. `TreeN = List UnitChild`; Beweise aus Wortrekursion, keine externe Peano-Arithmetik. |
| 4 | 130 | Transitivität positiver Bruchrelation | `Frac.eqv_trans` | **OK**; Integritätsbereich/Kürzbarkeit und positiver Nenner sichtbar. |
| 5 | 155 | Interner Quotient mit Körpergesetzen und Charakteristik null | `FracQ.instTField`; `TreeNumbers/PathFractions.lean` | **OK–kurz**; die Quellbeweiskette ist breiter als der zusammengezogene Manuskriptbeweis. Es wurde **keine allgemeine universelle Eigenschaft** bewiesen. |
| 6 | 189 | Ordnungs- und Körperisomorphismus der Pfadtripel mit positiven Brüchen | `TreeQ.orderedFieldIsoFracQ` | **OK–kurz**; `[TwoLetters α]` erforderlich; die Ordnung wird explizit erhalten/reflektiert. |
| 7 | 203 | Arity-Unabhängigkeit des rationalen Isomorphietyps | `TreeQ.arityIso`, `TreeQ.orderedFieldIsoFracQ` | **OK**. Die direkte alte `arityIso`-Struktur ist ein Körperisomorphismus, die Ordnungsverträglichkeit folgt über den gemeinsamen Bruchquotienten. |
| 8 | 221 | Symmetrische Bilinearität von `B_b` | `ChildModule.dot_*` in `BilinearForm.lean` | **OK**, sogar für `b=0`; keine Norm oder Positivität. |
| 9 | 254 | Basen für `L_b`, `S_b`; Ränge 1, `b−1` | `ChildModule.transverse_basis`, `longitudinal_basis` | **OK**, nur `b>0`, `[TField K]`. |
| 10 | 273 | Endliche direkte Summenzerlegung | `ChildModule.decomposition_unique`, `projS_inS` | **OK** bei positiver endlicher Arität und Charakteristik null. |
| 11 | 289 | Projektoren: linear, idempotent, komplementär; Bilder/Kerne | `ProjectionLaws.lean`, 37 neue Task-6-Deklarationen | **OK**; kein zusätzliches Axiom. |
| 12 | 325 | Orthogonale Zerlegung der Bilinearform | `ChildModule.dot_split` | **OK**, algebraisch, nicht positiv-definit/inner product. |
| 13 | 361 | Abzählbare Basis des endlich unterstützten ω-Nullsummenraums | `OmegaModule.tvO_indep`, `tvO_span` | **OK**; nur endliche Linearkombinationen. |
| 14 | 373 | Nullergänzung erhält uniforme Linien nicht | `Longitudinal.padSucc_u_not_inL`, `allOnes_not_finSupp` | **OK**; kein universelles Unmöglichkeitsresultat über andere Träger. |
| 15 | 393 | Getrennte Rays mittels clopener Zylinder | `Ray.separate_of_diff`, `cyl_open`, `cyl_compl_open` | **OK** bei gegebener Unterscheidungsstelle, `DecidableEq`. |
| 16 | 404 | Nichtkompaktheit aller ω-Zylinder und fehlende lokale Kompaktheit | `Ray.cyl_not_compact`, `not_locallyCompactAt` | **OK** in der Projekttopologie; noch keine finite-arity-Kompaktheit. |
| 17 | 423 | Transitive niveauweise Aktion / konstante invariante Funktionen | `RayAutomorphism.rayAct_swapPerm`, `invariant_const` | **OK** unter decidable letter equality; nicht alle Auto­morphismen levelwise. |
| 18 | 473 | Quantitativer Produktmodulus | `CauchyOps.lean`, `mulSeq` | **OK** bei eventualen Faktorgrenzen: jeweils **fremder Faktorbound** verschiebt den Modulus. |
| 19 | 498 | Quotient ist kommutativer Ring, konstante Einbettung injektiv | `TreeR.instCRing`, `ofQ_injective` | **OK–kurz**; hier **nicht** pauschal „klassischer Körper“ sagen. |
| 20 | 519 | Transitive Ordnungen, Cotransitivität, tight apartness | `TreeR.lt_cotrans`, `le_antisymm`, `eq_of_not_apart` | **OK–kurz**; nichttriviales `SeqNonneg_of_not_seqPos_neg` wird als Zwischensatz gebraucht. |
| 21 | 560 | Inverses unter Apartheit | `TreeR.exists_inv_of_apart` | **OK–kurz**; `x≠0` genügt gerade **nicht** ohne MP. |
| 22 | 606 | Modullierte Vollständigkeit genau dann, wenn rationale Approximation verfügbar | `TreeR.complete_iff_cauchyApprox` | **OK**; beide Seiten sind Prop-Prädikate, ohne dass eine von ihnen unbedingter Satz wäre. |
| 23 | 626 | Echte LUB unter `SupData` | `TreeR.SupData.isLUB` | **OK**; volle willkürliche Teilmengen-LUB nicht abgeleitet. |
| 24 | 678 | Inverse ↔ MP, Zero-or-Apart ↔ LPO, Entscheidbarkeit ↔ WLPO | `inv_iff_markov`, `zeroOrApart_iff_lpo`, `decidableZero_iff_wlpo`, `trichotomy_iff_lpo` | **OK–kurz**; Bool-Ströme über dem internen `TreeN`, keine importierten Prinzipien. |
| 25 | 699 | UnrestrictedLUB ⇒ WLPO; monotone Konvergenz ⇒ LPO | `wlpo_of_unrestrictedLUB`, `lpo_of_bmc` | **OK–kurz**. Nur Hinrichtungen, keine Unabhängigkeitsaussage. |
**Ergebnis:** In den 25 ausdrücklich als mathematische Sätze ausgezeichneten Resultaten **kein unbedingter Falschsatz** gegen die Quelle festgestellt. Mehrere informelle Beweise bleiben verkürzt; der klarste Konstruktionstextfehler ist außerhalb der eingerahmten Sätze in §5 (`TreeZ` als Quotient statt normalisierter Repräsentant).

## 5. Mathematische Einzelkontrolle der nicht separat gerahmten Aussagen

### §2 – Gewurzelte endliche Wörter (Z. 52–68)

`A^{<ω}=List A`, leerer Wortknoten, `a::w` als Kind, eindeutiger Elternknoten, Wurzel-Elternlosigkeit, explizite Kanten und eindeutige gerichtete Pfade: **richtig**. Die Zusammenhangskonstruktion über die Wurzel ist formal belegt. **Präzisionslücke K2:** Nur *gerichtete* Zyklen werden informell ausgeschlossen, obwohl `Word.no_cycle` einen stärkeren und relevanten ungerichteten Schluss beweist. Die Vereinigung der endlichen arity-Wörter deckt `T_ω` auf dem *endlichen Vertex-/Kantenniveau* ab, nicht den Ray-Rand: **korrekt**.

### §3 – Einheitskanten und Ray-Präfixzählungen (Z. 69–80)

Pfadsumme = Tiefe durch strukturelle Rekursion: **korrekt**. Die Werte jeder Strahlpräfixzählung sind `n`, daher nicht ray-unterscheidend; der unmodifizierte Zählstrom `n ↦ n` ist keine rationale Cauchy-Folge: **korrekt**. Daraus folgt *kein* allgemeines Verbot anderer rayabhängiger numerischer Kodierungen; korrekt eingeschränkt.

### §4 – Unary-Semiring und Tiefequotienten (Z. 81–101)

Null, Eins, Succ, assoziative kommutative Addition/Multiplikation, Verteilbarkeit, Induktion, Ordnung, Kürzbarkeit, Tiefenquotient für nichtleere Alphabete: **korrekt**. Für ein leeres Alphabet entsteht nur die Wurzelklasse; folglich keine Isomorphie zum gesamten `TreeN`: **korrekt**. Die Identifikation von unary words mit dem selbst definierten Naturtyp ist konstruktionsbedingt; kein eigener überraschender Standard-Nat-Satz.

### §5 – Ganze Zahlen (Z. 102–116)

Differenzrelation, Transitivität, Paar-Normalform, zweisortige Vorzeichenfälle, Ringgesetze, Integritätsbereich, Ordnung, naturtreue Einbettung: **mathematisch korrekt**. **K1:** Formulierung des Trägers als Quotient ist definitionsgenau falsch; der Code konstruiert normalisierte Paare und beweist Relationsexaktheit. Die generelle universelle Eigenschaft der Grothendieck-Gruppe wird nicht gezeigt und auch nicht beansprucht.

### §§6–7 – Bruchrelation, Pfadtripel, geordneter Körper, Arity-Transfer (Z. 117–212)

Positive Nenner, Kreuzmultiplikation, Kongruenz von Addition/Multiplikation, Inversion mit Vorzeichen, Charakteristik null, geordneter Bruchkörper, universelle Tripelzeugen bei `[TwoLetters]`, inverse Quotientenabbildungen und Ordnungserhaltung: **formal gedeckt; algebraische Hauptformeln gegengeprüft**. Die konkrete Triple-Zeugenfamilie in Z. 168–174 stimmt mit `TriplePath.wP1/wP2/wP3` überein. Bemerken: Die Pfadtripel sind **keine Vertexbeschriftung** und die zwei Symbole sind Zeugen für eine spezielle Repräsentation, nicht für jede denkbare Konstruktion von Q zwingend.

### §8 – Endliche algebraische Koordinaten, Dimension, Projektionen (Z. 213–352)

Für `[TField K]` und positive endliche Arität: `F_b=K^{Child b}`, `L_b=K u`, `S_b=ker Σ`, Basis `{u}` für L und `{e_j−e_0}` für S, Ränge 1 und `b−1`, Summe `L⊕S`, Projektoren mit `1/b`, Linearität, Idempotenz, gegenseitige Vernichtung, Bild-/Kernrelationen, bilineare Orthogonalität und Formzerlegung: **formal gedeckt; Task-6-Ergänzungen vollständig einbezogen**. Die Bilinearität gilt auch bei `b=0`, die Rang-/Projektionssätze in der dargestellten Form nur bei `b>0`: korrekt. 

Kein Satz leitet eine Baum-Mannigfaltigkeitsdimension, physikalische Signatur, kanonische Metrik, Norm oder positive Definitheit ab; diese ausdrücklichen Einschränkungen sind fachlich notwendig.

### §9 – ω-Nullsummenraum (Z. 353–382)

Endlich unterstützte Funktionen, stabilisierte Summe, Nullsummenbedingung, unabhängige/erzeugende Familie `e_{j+1}−e_0`, verträgliche Nullergänzungsinjektionen und longitudinales Hindernis: **korrekt**. Der all-ones-Vektor ist kein Element des *algebraischen* direkten Summenraums. Nicht bewiesen ist, dass in jedem anderen Funktionsraum ein longitudinaler Grenzvektor unmöglich wäre; das Paper behauptet das nicht.

### §10 – Ray-Rand, Präfixtopologie, Zusammenhang, Kompaktheit (Z. 383–418)

Ray als `TreeN→A`, eindeutige Präfixbestimmung, echte Randvergrößerung gegenüber der Vereinigung endlicher arity-Ränder durch die Identitätsray, clopene Zylinder, Punkttrennung mit benannter Abweichung, konstruktiv gesicherte verbundene Teilmengen und fehlende isolierte Punkte bei mindestens zwei Buchstaben: **korrekt im definierten topologischen Rahmen**. Nichtkompaktheit der ω-Zylinder und Nichtlokalkompaktheit anhand der next-letter-offenen Überdeckung: **korrekt**. Für finite Alphabete wird keine unbelegte allgemeine kompakte Konstruktion angeführt. Reelle Intervallzusammenhängigkeit bleibt explizite Zusatzannahme bei 1-dimensionalen Chart-No-gos; keine höheren Manifold-Claims. Nichtinjektive binäre Randkodierungen ergeben keine topologische Identität mit den Cauchy-Reellen.

### §11 – Automorphismen (Z. 419–432)

Niveauweise bijektive Kindervertauschungen liefern Baumautomorphismen, die Rays transitiv bewegen können; invarianten Werte sind konstant. Das von Task 5 reparierte Gegenbeispiel zeigt Nichtvollständigkeit der *niveauweisen* Untergruppe. **Korrekt**; der Text macht daraus keine Klassifikation der gesamten Automorphismengruppe.

### §12 – Modulierter Cauchy-Quotient und konstruktive Ordnung (Z. 433–579)

Cauchy-Daten *mit expliziter Modulusfunktion*, dyadische Präzision, Folgeäquivalenz, Regularisierung, Summen-/Negations- und quantitative Produktmoduli, Quotientenverträglichkeit, Ring und Einbettung, eventuelle Positivität, approximative Nichtnegativität, Ordnungsbeziehungen und enge Apartheit: **korrekt auf der Ebene der ausgesprochenen Resultate**. Die zentrale Produktabschätzung verschiebt jeweils um die **Schranke des jeweils anderen Faktors**; der ausführliche Manuskriptbeweis berücksichtigt das. `SeqNonneg` ist **nicht** punktweise Positivität. 

Das Apartheitsinversenlemma verlangt einen eventualen positiven oder negativen dyadischen Abstand von null. Das Paper vermeidet die verbotene Ersetzung durch bloßes `x≠0`; **korrekt**. Die informellen Ableitungen von Negiert-Positivität zu Nichtnegativität und Cotransitivität sind nachvollziehbar, aber für vollständige Eigenständigkeit sind ihre expliziten Hilfslemmata beizugeben (K3).

### §13 – Konvergenz und bedingte Vollständigkeit (Z. 580–656)

Grenzwertbegriff mit zwei rationalen Fehlerschranken, Eindeutigkeit, getrackte rationale Approximation, Diagonalmodulus `max(ν(k+2),M(k+2))`, stabile algebraische endliche Ausdrücke, `UnrestrictedCompleteness ↔ CauchyApprox` (jeweils **mit realem Modulus**), `ChoiceNN` als sichtbare Voraussetzung für stärkere Auswahlresultate und modullose Vollständigkeit: **korrekt**. 

`SupData` liefert **echte** least upper bounds für die konkret mit oberen und annähernd erreichbaren Rationalgrenzen versorgten Mengen, einschließlich der im Code erzeugten endlichen und getrackten monotonen Fälle. Es ist **kein Beweis** allgemeiner Dedekind-Vollständigkeit. Der Abschnitt zur gleichmäßig stetigen rationalen Selbstabbildung beschränkt das Ziel auf `K→K` und die Eindeutigkeit auf `RatSeqContinuous`; **korrekt**.

### §14 – MP, LPO, WLPO und logische Untergrenzen (Z. 657–710)

Bool-Stromkodierung über dem internen `TreeN`, Gap-Tests auf regularisierten rationalen Repräsentanten, `nonzero inverse ↔ MP`, `zero or apart ↔ LPO`, `trichotomy ↔ LPO`, `decidable zero ↔ WLPO`, `UnrestrictedLUB ⇒ WLPO`, `BoundedMonotoneConvergence ⇒ LPO`: **korrekt mit dem Quellstand vereinbar**. Die Expositionsbeweise arbeiten mit definierten booleschen Entscheidungsverfahren auf `K`, nicht mit einer heimlich importierten trichotomischen Realordnung. **Keine** der erwähnten logischen Zusatzprinzipien wird aus den Grundaxiomen abgeleitet oder als neues Axiom eingeführt. Ebenso wenig liefern die Hinrichtungen allein einen metatheoretischen Unabhängigkeitsbeweis.

### §§15–17 – Vergleich, Grenzen, Schluss (Z. 712–734)

Die kontrastierende Feststellung „isomorphe rationale Felder bei unterschiedlichen algebraischen Kinderraum-Rängen“ ist korrekt, ohne ein dimensionales Naturgesetz zu behaupten. Die einfachen Präfixzählungen klassifizieren keine Rays. Die drei Träger `K^{(N)}`, `A^N` und `R(K)` bleiben unterscheidbar. Wurzel-Level null/Infinitymarkierung sind bloße Hilfslabels; es gibt keine abgeleitete geodätische Achse. Offene universelle Abbildungseigenschaften, klassische reelle Vollständigkeit, Randkompaktheit und alternative longitudinale Grenzträger werden ausdrücklich offen gelassen. **Inhaltlich richtig**; einige der weiterführenden Fragen sind mangels allgemeiner Zieldefinition „nicht formalisiert“ statt „formal offen“.

### Anhang A – zusätzliche mathematische Beweise (Z. 736–797)

Die expliziten Bruchkongruenzidentitäten sind algebraisch korrekt; im Text müssen die gemeinsam eingebetteten positiven Nenner konsequent typmäßig identifiziert werden. Produktverschiebung, reziproke Abschätzung, reelle Cotransitivitäts-Dyadik, Diagonalabschätzung `3 ε_(k+2) ≤ ε_k` und Regularität der Supremumsdaten sind korrekt. Die Passage ergänzt wichtige Zwischenrechnungen, ist aber **keine lückenlose Ausformulierung aller Lean-Hilfsbeweise**.

### Anhang B – Verifikation und kurzer Nachweisindex (Z. 798–830)

Quellenfingerabdruck und Task-6-Audit werden richtig getrennt von nicht selbst ausgeführten Lean-Kernelläufen. Die Tabelle ist ausdrücklich eine *Auswahl* der Deklarationsabbildung; dafür ist die separate 289-Einträge-Korrespondenz vorgesehen. Die Original-Task-5-Audits und ZIP-Paket-Liefergrenzen sollten einmalig sauber in einem konsistenten Publikationsmanifest geklärt werden (K4–K6).

## 6. Status sämtlicher zentraler offener/bedingter Aussagen

| Frage | Beweisstand Task 6 | Zulässige mathematische Aussage |
|---|---|---|
| Allgemeine reelle Cauchy-Vollständigkeit bei gegebenem Modulus | `UC ↔ CA`; unter `ChoiceNN` | Offen ohne zusätzliche Annahme; bedingt bewiesen |
| Modullose Vollständigkeit und Auswahl von Moduln | Unter `ChoiceNN` | Offen ohne Annahme |
| Inversion aus `x≠0` für alle reellen Klassen | Äquivalent zu Bool-MP | Nicht unbedingter Satz |
| Volle Trichotomie / Zero-or-Apartness | Äquivalent zu Bool-LPO | Nicht unbedingter Satz |
| Entscheidbarkeit von `x=0` | Äquivalent zu Bool-WLPO | Nicht unbedingter Satz |
| Allgemeine LUB für alle nach oben beschränkten nichtleeren Prädikate | Impliziert WLPO | Nicht konstruiert; nicht durch `SupData` bewiesen |
| Allgemeine beschränkte monotone Konvergenz | Impliziert LPO | Nicht bewiesen |
| Nullprodukt-**Disjunktion** in `R(K)` | Aus Zero-or-Apart/LPO ableitbar | Ohne diese Zusatzstärke nicht nachgewiesen |
| Finite-arity-Randkompaktheit | Kein Quellbeweis | Offen im Source-Scope; nicht als falsch bewiesen |
| `IntervalsConnected K` | Als explizite Bedingung vorhanden | Unbewiesen; Chart-No-go konditional |
| Positive Dimensionen allgemeiner Mannigfaltigkeiten | Keine vollständigen passenden Zielräume | Nicht formalisiert; nicht mit algebraischem Rang verwechseln |
| Allgemeiner longitudinaler ω-Grenzvektor in anderen Trägern | Nicht formalisiert | Nur Nullergänzungsobstruktion bewiesen |
| Allgemeine Klassifikation der Automorphismengruppe | Nicht formalisiert | Ebeneweise-only-Hypothese widerlegt |
| Allgemeine universelle Eigenschaften der Zahlen-, Bruch- und Cauchy-Konstruktionen | Nur begrenzte konkrete Isomorphien | Nicht allgemein bewiesen |
| Kanonische Identifikation von Rays mit `R(K)` | Keine solche Abbildung/Isomorphie bewiesen | Nicht daraus universelle Unmöglichkeit folgern |
| Algebraische endliche Rangsätze und Task-6-Projektionsgesetze | **Bewiesen** | Nicht als offene Probleme nennen |
| Levelwise-only-Klassifikation aller Automorphismen | **Formal widerlegt** | Nicht mehr als offene Vermutung nennen |

## 7. Prüfung sämtlicher 17 Doku-Dateien

| Paketdatei | Prüfung | Urteil |
|---|---|---|
| `main.tex` | 831 Zeilen, 17 Hauptabschnitte, 66 Unterabschnitte, 25 benannte Hauptresultate und zwei Anhänge mathematisch geprüft | Tragfähiger Entwurf; K1–K3 bearbeiten |
| `main.pdf` | 26/26 Seiten gerendert/visuell übersichtet, Inhaltsverzeichnis, Formeln, Literatur | Lesbar und satztechnisch unauffällig; reflektiert `main.tex` |
| `references.bib` | 10 Einträge, Autoren/DOIs/Themen validiert soweit quellenzugänglich | Korrekt; Editionskonstanz vor Einreichung |
| `references.tex` | 10 manuelle Literaturangaben mit BibTeX-Liste abgeglichen | Aktuell konsistent; Doppelpflege ist wartungsanfällig |
| `proof_correspondence.md` | 289 deklarierte Pfad-/Zeilenreferenzen gegen gefrorenen Source-Tree kontrolliert: 289/289 korrekt | Sehr starkes Nachweisinstrument; Kernellogs extern |
| `verification_report.md` | Hash, Version, Kategorien, selbst reproduzierte vs berichtete Läufe geprüft | Ehrliche Provenienz; präzisieren, dass Audit-Kategorien überlappen |
| `open_questions.md` | Alle benannten offenen Fragen gegen Code und Manuskript geprüft | Mathematisch weitgehend korrekt, jedoch K4 veralteter Verweis/Datum |
| `MATHEMATICAL_PROOF_AUDIT.md` | 24-einträgen thematischen Prüfpfad und Rekonstruktionshinweise bewertet | Inhaltlich hilfreich; selbst ausdrücklich „spot audit“, nicht Vollbeweis |
| `PRIMARY_SOURCE_AUDIT.md` | 10 bibliografische Prüfvermerke/Originaltextniveaus abgeglichen | Sorgfältige Unterscheidung; Paywall-Lücken bleiben |
| `LEAN_PROOF_REQUIREMENTS.md` | Task-6-Gesetze vs ältere optionalen Lemmata und offene Ziele geprüft | Korrekt: Task-6-Hilfslemmata erledigt; stärkere Ziele nicht erzwingen |
| `scope_89.md` | Alle 89 geplanten Themenzeilen ihrem angegebenen Manuskriptabschnitt und Sourcefamilien zugeordnet | 89/89 abgedeckt, teils Kurztext/„scope“, **nicht** 89 voll ausgearbeitete Beweise |
| `main_45_type_verified_claims.md` | 45 archivierte Haupttypen und frühere Rekonstruktionslabels verglichen | 45 Typen; 11 historische O/O-C-Expositionsvermerke datiert neu bewerten |
| `README.md` | Inhalt/Aussagen/Limits gegen Dateien geprüft | Korrekt, sollte Release-Abhängigkeit expliziter erklären |
| `SOURCE_MANIFEST_SHA256.txt` | 75 Pfade und SHA-256 gegen Source verifiziert | 75/75 PASS |
| `source_check.log` | Meldung mit eigenständig erneut ausgeführtem Checker verglichen | Übereinstimmend, PASS |
| `source_fingerprint.txt` | Hash gegen Projektfingerabdruck verglichen | Übereinstimmend |
| `compile-final2.log` | pdflatex-Ausgabe auf Fehler, Warnungen, Seitezahl geprüft | PASS, 26 Seiten; normale Font-/Underfull-Warnungen, keine fatalen Fehler |

## 8. Primärliteraturprüfung – alle 10 Quellen

| Quelle | Belegter Kontext | Urteil / Vorsicht |
|---|---|---|
| Serre, *Trees* (1980) | Gewurzelte Bäume, Gruppeneinwirkungen; Springer Kap. I „Trees and Amalgams“ S. 1–68 | DOI/Buch/Abschnitt bestätigt; kein spezifischer Beweis für eigene Quotienten behauptet |
| Lyons–Peres, *Probability on Trees and Networks* (2016) | Baum- und Netzterminologie, Rays/Ends | Autorenquelle existiert, Editions-Paginierung beachten |
| Kechris, *Classical Descriptive Set Theory* (1995) | Trees S. 5–12, kompakte/metrisierbare Räume S. 18–28, lokale Kompaktheit S. 29–30, nulldimensionale Räume S. 35–40 | Kapitelseiten beim Verlag bestätigt; klassische Topologie als Hintergrund, nicht Quellbeweis der eigenen konstruktiven Topologie |
| Axler, *Linear Algebra Done Right*, 4. Aufl. | Direkte Summen, Basis/Dimension, symmetrische Bilinearformen §9A | Original-PDF und 2024er Buchmetadaten kompatibel; 2026 geänderte PDF-Seiten nicht mit 2024-Buchseiten vermengen |
| Bass–Otero-Espinar–Rockmore–Tresser (1996) | Gruppen von Baumautomorphismen | Vier Autoren, DOI und Springer LNM 1621 bestätigt; keine direkte Identität mit eigener levelwise-Untergruppe |
| Bishop–Bridges, *Constructive Analysis* (1985) | Konstruktive Cauchy-Begriffe / reelle Zahlen | Verlag/Kapitel, keine direkte formale Satzübernahme |
| Bridges–Richman, *Varieties of Constructive Mathematics* (1987) | Unterschiedliche konstruktive Prinzipien, MP/Auswahl | Bibliografie/Kapitel bestätigt; einzelne zugangsgeschützte Lehrsätze nicht originalgelesen |
| Lubarsky (2007) | Konstruktive Cauchy-Vollständigkeitsprobleme ohne abzählbare Auswahl | Originalveröffentlichung und DOI bestätigt; **keine** Unabhängigkeit für das eigene Lean-System daraus ableiten |
| Gilbert (CPP 2017) | Alternative Konstruktionen von Cauchy-Reellen in HoTT und Auswahlproblematik | DOI und Publikationskontext bestätigt; andere Beweisumgebung (Coq/HoTT) |
| Lean-Referenz, *Validating a Lean Proof* | #print axioms, Kernelprüfung, Interpretationsgrenzen | Primärdokumentation, keine unabhängige Neuverifikation |

## 9. Abnahmeentscheid und konkrete Reihenfolge

**Freigabe als vollständige, bereits formal verifizierte Mathematikbibliothek:** Der zugrunde liegende Task-6-Quellstand ist nach den mitgelieferten Verifikationsläufen und dem eigenständigen Quellcodeabgleich plausibel erfolgreich geprüft; **ich habe die Kernelprüfung nicht selbst erneut durchgeführt**.

**Freigabe des Dokupakets als endgültiges journalfertiges Paper:** **NOCH NICHT.** Vorher:

1. **P1:** Z. 102–106 Integerträger mathematisch exakt als eindeutig normalisierter Paartyp berichtigen und den Quotientenbezug durch `mkZ_sound/mkZ_exact` angeben.
2. **P2:** Z. 63–65 den formal bewiesenen ungerichteten no-cycle-Satz und sein Brückenkantenargument ergänzen.
3. **P2:** Die verbleibenden *nichttrivialen* Beweisverkürzungen anhand der 45-Satz-Flags und des neuen Textstands einzeln klassifizieren; keine Frage nach einer zusätzlichen Lean-„Lösung“ daraus machen.
4. **P2:** `open_questions.md` auf Task 6 / 15. Oktober aktualisieren; nicht ausgeliefertes `MATHEMATICAL_ARGUMENTS_ADDED.md` entfernen/ersetzen; widerspruchsfreie aktuelle Expositionsmatrix erzeugen.
5. **P2:** Immutable Task-6-Quellarchiv mit Hash als zitierbare Zusatzquelle beilegen oder verlinken und Kernel-/Audit-Logs eindeutig referenzieren.
6. **P3:** Autor/Institution (falls Veröffentlichung), unabhängige fachliche Prüfung, Zeitschriftenlayout und final reproduzierte LaTeX-Buildkette ergänzen.

**Nicht nötig:** Alle offenen Fragen zur realen Vollständigkeit, topologischen Mannigfaltigkeit oder longitudinalen Unendlichkeit gewaltsam zu beweisen, neue Axiome zu importieren oder den konstruktiven Kern umzubauen. Die offene-Grenzen-Abgrenzung ist ein tragender Teil des Papers.

---

## Anhang I — Lückenloser Abgleich mit den 89 vorgesehenen Themen

Die folgende Matrix führt **jedes** geplante Unterthema auf. `Integration` und `Presentation level` stammen aus `scope_89.md` und wurden mit den betreffenden Manuskriptabschnitten abgeglichen. `Scope` bedeutet eine methodische/bedingte Grenze, **kein zu beweisendes Theorem**. „Core proof“ bedeutet ein im Haupttext behandeltes Beweismotiv, nicht automatisch einen lückenlosen formal unabhängigen Komplettbeweis.


| Nr. | Geplanter Gegenstand | Manuskript | Tiefe der Darstellung | Zugehöriger Quellbereich |
|---|---|---|---|---|
| 1.1 | Mathematical objects and construction order | §1 | Scope | (no direct module named in subsection) |
| 1.2 | Related established mathematical frameworks | §1 | Scope | (no direct module named in subsection) |
| 1.3 | Main theorems and their scope | §1 | Scope | (no direct module named in subsection) |
| 1.4 | Logical framework and interpretative scope | §1 | Scope | (no direct module named in subsection) |
| 2.1 | Alphabets, finite words, root, and directed edges | §2 | Sketch | PrimitiveTree/FiniteWords.lean |
| 2.2 | Unique parent and unique finite root path | §2 | Core proof | PrimitiveTree/FiniteWords.lean |
| 2.3 | Connectedness, absence of cycles, and infinite depth | §2 | Sketch | PrimitiveTree/FiniteWords.lean |
| 2.4 | Finite arity as a derived indexing object | §2 | Sketch | PrimitiveTree/FiniteChild.lean ; TreeNumbers/PathNaturals.lean |
| 2.5 | The countably branching tree | §2 | Sketch | TreeFoundation/OmegaTree.lean |
| 2.6 | Inclusions and the directed arity union | §2 | Sketch | TreeFoundation/ArityEmbeddings.lean |
| 3.1 | Unit contribution and literal finite edge sum | §3 | Sketch | PrimitiveTree/RootEdges.lean |
| 3.2 | Equality of unit-edge sum and depth | §3 | Core proof | PrimitiveTree/RootEdges.lean |
| 3.3 | The unbounded path-count sequence along each ray | §3 | Sketch | TreeFoundation/InfiniteRays.lean ; TreeAnalysis/PrimitiveDataScope.lean |
| 4.1 | Unary paths as natural-count carrier | §4 | Sketch | PrimitiveTree/UnaryPaths.lean ; TreeNumbers/PathNaturals.lean |
| 4.2 | Addition and multiplication from word operations | §4 | Core proof | TreeNumbers/PathNaturals.lean |
| 4.3 | Induction, recursion, order, and cancellation | §4 | Sketch | TreeNumbers/FoundationsLedger.lean ; TreeNumbers/PathOrder.lean |
| 4.4 | Equal-depth quotient for arbitrary nonempty alphabets | §4 | Core proof | TreeNumbers/DepthQuotient.lean |
| 5.1 | Oriented pairs of nonnegative path counts | §5 | Sketch | TreeNumbers/PathIntegers.lean |
| 5.2 | Normal forms and equivalence classes | §5 | Core proof | TreeNumbers/PathIntegers.lean |
| 5.3 | Ring laws and absence of zero divisors | §5 | Sketch | TreeNumbers/PathIntegers.lean |
| 5.4 | Order and canonical embedding of natural counts | §5 | Sketch | TreeNumbers/PathOrder.lean ; TreeNumbers/FoundationsLedger.lean ; TreeNumbers/PathIntegers.lean |
| 6.1 | Valid configurations and the positive gap | §6 | Sketch | TreeNumbers/PathTriples.lean |
| 6.2 | Equivalence by cross multiplication | §6 | Sketch | TreeNumbers/PathTriples.lean ; TreeNumbers/PathFractions.lean |
| 6.3 | Universal representatives using two distinct child symbols | §6 | Core proof | TreeNumbers/PathTriples.lean ; TreeNumbers/FoundationsLedger.lean |
| 6.4 | Field operations and all field laws | §6 | Core proof | TreeNumbers/PathRationalField.lean ; TreeNumbers/PathFractions.lean ; TreeAnalysis/FractionCharacterization.lean |
| 6.5 | Ordering and Archimedean structure | §6 | Sketch | TreeAnalysis/RationalOrder.lean ; TreeAnalysis/DyadicPrecision.lean |
| 6.6 | Identification with internally defined fractions | §6 | Core proof | TreeAnalysis/FractionCharacterization.lean |
| 6.7 | What branching contributes to this representation | §6 | Sketch | TreeAnalysis/FractionCharacterization.lean ; TreeNumbers/FoundationsLedger.lean |
| 7.1 | Canonical algebraic comparisons across finite arities | §7 | Core proof | TreeNumbers/RationalArityIndependence.lean ; TreeNumbers/FoundationsLedger.lean |
| 7.2 | Compatibility and uniqueness | §7 | Sketch | TreeAnalysis/Canonicity.lean ; TreeNumbers/FoundationsLedger.lean |
| 7.3 | Representation versus primitive structure | §7 | Sketch | (no direct module named in subsection) |
| 8.1 | Coordinate module and algebraic operations | §8 | Sketch | DimensionFoundation/FiniteChildModule.lean |
| 8.2 | Coordinate sum and canonical bilinear form | §8 | Expanded mathematical proof | DimensionFoundation/FiniteChildModule.lean ; DimensionFoundation/FiniteSums.lean ; DimensionFoundation/BilinearForm.lean |
| 8.3 | Uniform line and zero-sum submodule | §8 | Sketch | DimensionFoundation/FiniteChildModule.lean |
| 8.4 | Orthogonality relative to the chosen bilinear form | §8 | Expanded mathematical proof | DimensionFoundation/FiniteChildModule.lean ; DimensionFoundation/ProjectionLaws.lean |
| 8.5 | Explicit basis of the uniform line | §8 | Core proof | DimensionFoundation/TransverseBasis.lean ; DimensionFoundation/Instances.lean |
| 8.6 | Basis of the zero-sum submodule | §8 | Core proof | DimensionFoundation/TransverseBasis.lean |
| 8.7 | Explicit projection and direct-sum theorem | §8 | Expanded mathematical proof | DimensionFoundation/TransverseBasis.lean ; DimensionFoundation/Instances.lean ; DimensionFoundation/ProjectionLaws.lean |
| 8.8 | Exceptional unary case and permutation invariance | §8 | Core proof | DimensionFoundation/TransverseBasis.lean |
| 8.9 | Interpretation of `b−1` | §8 | Scope | (no direct module named in subsection) |
| 9.1 | Finite-support sequences and the zero-sum condition | §9 | Core proof | DimensionFoundation/OmegaFiniteSupport.lean |
| 9.2 | A countable explicit basis | §9 | Core proof | DimensionFoundation/OmegaFiniteSupport.lean ; DimensionFoundation/Instances.lean |
| 9.3 | Canonical compatible inclusions | §9 | Core proof | DimensionFoundation/OmegaFiniteSupport.lean |
| 9.4 | Failure of the uniform line under zero-padding | §9 | Core proof | DimensionFoundation/BoundaryLongitudinal.lean |
| 9.5 | Precise scope of the omega result | §9 | Scope | (no direct module named in subsection) |
| 10.1 | Rays as infinite sequences and coherent prefixes | §10 | Sketch | TreeFoundation/InfiniteRays.lean |
| 10.2 | Boundary and arity union do not commute | §10 | Core proof | TreeFoundation/InfiniteRays.lean |
| 10.3 | Cylinders and prefix incidence | §10 | Sketch | BoundaryTopology/Cylinders.lean |
| 10.4 | Clopen cylinder basis and point separation | §10 | Core proof | BoundaryTopology/PrefixTopology.lean |
| 10.5 | Connected subsets and isolated points | §10 | Core proof | BoundaryTopology/TopologicalObstructions.lean |
| 10.6 | Countable arity and local compactness | §10 | Core proof | BoundaryTopology/TopologicalObstructions.lean |
| 10.7 | Exact status of manifold statements | §10 | Sketch; conditional premises essential | BoundaryTopology/ManifoldConditions.lean |
| 10.8 | Optional numerical encodings are noncanonical | §10 | Scope | BoundaryTopology/BinaryEncoding.lean ; TreeAnalysis/PrimitiveDataScope.lean |
| 11.1 | Levelwise child permutations and induced tree automorphisms | §11 | Sketch | TreeFoundation/RayAutomorphism.lean |
| 11.2 | Explicit transitive action on rays | §11 | Core proof | TreeFoundation/RayAutomorphism.lean |
| 11.3 | Invariant ray maps are constant | §11 | Core proof | TreeFoundation/RayAutomorphism.lean |
| 11.4 | General automorphisms are more numerous | §11 | Core proof | TreeFoundation/AutomorphismCounterexample.lean |
| 12.1 | Choice of base field and internally derived precision | §12 | Sketch | TreeAnalysis/OrderedField.lean ; TreeAnalysis/DyadicPrecision.lean |
| 12.2 | Rational Cauchy sequences with explicit modulus | §12 | Core proof | TreeAnalysis/CauchyData.lean |
| 12.3 | Equivalence relation, regularization and quotient carrier | §12 | Core proof | TreeAnalysis/CauchyData.lean ; TreeAnalysis/RealQuotient.lean |
| 12.4 | Commutative ring laws and rational embedding | §12 | Core proof | TreeAnalysis/RealQuotient.lean |
| 12.5 | Positive cone, weak order, strict order and apartness | §12 | Core proof | TreeAnalysis/RealOrderApartness.lean |
| 12.6 | Separated inversion versus ordinary non-equality | §12 | Core proof; conditional premises essential | TreeAnalysis/RealOrderApartness.lean ; TreeAnalysis/ApartnessStrength.lean |
| 12.7 | Density, Archimedean control, arity transfer | §12 | Scope | TreeAnalysis/CompletenessScope.lean ; TreeAnalysis/ArityCompletionTransfer.lean ; TreeAnalysis/FoundationsClosure.lean |
| 13.1 | Convergence of embedded rational Cauchy sequences | §13 | Core proof | TreeAnalysis/CompletenessScope.lean |
| 13.2 | Tracked real Cauchy sequences and the diagonal theorem | §13 | Core proof | TreeAnalysis/CompletenessStrength.lean ; TreeAnalysis/CompletenessScope.lean |
| 13.3 | Closure of tracked families under finite expressions | §13 | Sketch | TreeAnalysis/ApproxClosure.lean ; TreeAnalysis/TrackedExpressions.lean |
| 13.4 | Unrestricted modulated completeness and Cauchy approximation | §13 | Core proof; conditional premises essential | TreeAnalysis/LiftingPrinciples.lean |
| 13.5 | Choice principles and modulus-free completeness | §13 | Core proof; conditional premises essential | TreeAnalysis/LiftingPrinciples.lean |
| 13.6 | Least upper bounds with explicit approximation data | §13 | Core proof; conditional premises essential | TreeAnalysis/SupremumScope.lean |
| 13.7 | Continuation of uniformly continuous maps | §13 | Sketch; conditional premises essential | TreeAnalysis/CompletionCharacterization.lean |
| 14.1 | Markov principle and inverse existence | §14 | Core proof; conditional premises essential | TreeAnalysis/ApartnessStrength.lean |
| 14.2 | LPO and real trichotomy / zero-versus-apartness | §14 | Core proof; conditional premises essential | TreeAnalysis/ApartnessStrength.lean ; TreeAnalysis/FoundationsClosure.lean |
| 14.3 | WLPO and decidable zero | §14 | Core proof; conditional premises essential | TreeAnalysis/FoundationsClosure.lean |
| 14.4 | Logical lower bounds for global Suprema and monotone convergence | §14 | Core proof; conditional premises essential | TreeAnalysis/SupremumScope.lean |
| 14.5 | What “constructive” establishes and does not establish | §14 | Scope | (no direct module named in subsection) |
| 15.1 | Same arithmetic field, different finite child-space ranks | §15 | Core proof | (no direct module named in subsection) |
| 15.2 | Primitive path counts do not distinguish rays | §15 | Core proof | (no direct module named in subsection) |
| 15.3 | Boundary, algebraic direct limit, and numerical completion | §15 | Scope | (no direct module named in subsection) |
| 15.4 | Root and endpoint levels | §15 | Scope | TreeFoundation/ExtendedLevels.lean |
| 16.1 | Algebraic universal properties | §16 | Scope | (no direct module named in subsection) |
| 16.2 | Cauchy completeness without supplied representatives/moduli | §16 | Scope | (no direct module named in subsection) |
| 16.3 | Strong classical real-field and order axioms | §16 | Scope | (no direct module named in subsection) |
| 16.4 | Infinite-line compatibility obstruction | §16 | Scope | (no direct module named in subsection) |
| 16.5 | Boundary-topological limits and missing conditions | §16 | Scope | (no direct module named in subsection) |
| 16.6 | Full automorphism classification | §16 | Scope | (no direct module named in subsection) |
| 16.7 | Systematic separation of statuses | §16 | Scope | (no direct module named in subsection) |
| 17.1 | Statements established under the exact hypotheses | §17 | Scope | (no direct module named in subsection) |
| 17.2 | Delineation of open properties | §17 | Scope | (no direct module named in subsection) |

**Befund zur 89-Punkte-Matrix:** Alle 89 geplanten Gegenstände wurden einem konkreten Textabschnitt oder einem bewusst als Rahmen-/Grenzthema bezeichneten Abschnitt zugeordnet. „Sketch“ ist kein mathematischer Gegenbeweis, aber auch keine Zusicherung vollständiger informeller Herleitung; siehe K3. Für unbedingte Sätze dürfen keine bloßen Scope-Ziele als Beweise gelten.

## Anhang II — Individuelle Verifizierung aller 289 Paper–Lean-Deklarationsverweise

Neben der thematischen Vollständigkeitsprüfung wurden sämtliche folgenden 289 einzelnen Quellenverweise geprüft. Das Ergebnis „exakt“ bedeutet: Name der Deklaration und angegebenes Dateizeilenumfeld stimmen mit der eingefrorenen Quelle überein. **Es beweist nicht**, dass die im Paper gewählte englische Formulierung exakt die elaborierte Lean-Signatur wiedergibt; diese Semantik wird für die 25 Hauptsätze separat in Abschnitt 4 geprüft.

| Nr. | Deklaration laut Beweiskorrespondenz | Quellfundstelle | Abgleich |
|---:|---|---|---|
| 1 | `ChildModule.dot_addV_left` | `DimensionFoundation/BilinearForm.lean:27` | gefunden, Task 6 |
| 2 | `ChildModule.dot_addV_right` | `DimensionFoundation/BilinearForm.lean:33` | gefunden, Task 6 |
| 3 | `ChildModule.dot_smul_left` | `DimensionFoundation/BilinearForm.lean:39` | gefunden, Task 6 |
| 4 | `ChildModule.dot_smul_right` | `DimensionFoundation/BilinearForm.lean:45` | gefunden, Task 6 |
| 5 | `ChildModule.dot_bilinear_symmetric` | `DimensionFoundation/BilinearForm.lean:51` | gefunden, Task 6 |
| 6 | `ChildModule.dot_zeroV_left` | `DimensionFoundation/BilinearForm.lean:61` | gefunden, Task 6 |
| 7 | `ChildModule.dot_zeroV_right` | `DimensionFoundation/BilinearForm.lean:65` | gefunden, Task 6 |
| 8 | `ChildModule.dot_negV_left` | `DimensionFoundation/BilinearForm.lean:69` | gefunden, Task 6 |
| 9 | `ChildModule.dot_negV_right` | `DimensionFoundation/BilinearForm.lean:74` | gefunden, Task 6 |
| 10 | `ChildModule.zeroV_inL` | `DimensionFoundation/ProjectionLaws.lean:31` | gefunden, Task 6 |
| 11 | `ChildModule.addV_zeroV` | `DimensionFoundation/ProjectionLaws.lean:33` | gefunden, Task 6 |
| 12 | `ChildModule.proj_of_inL` | `DimensionFoundation/ProjectionLaws.lean:38` | gefunden, Task 6 |
| 13 | `ChildModule.proj_of_inS` | `DimensionFoundation/ProjectionLaws.lean:45` | gefunden, Task 6 |
| 14 | `ChildModule.projL_of_inL` | `DimensionFoundation/ProjectionLaws.lean:51` | gefunden, Task 6 |
| 15 | `ChildModule.projS_of_inL` | `DimensionFoundation/ProjectionLaws.lean:54` | gefunden, Task 6 |
| 16 | `ChildModule.projL_of_inS` | `DimensionFoundation/ProjectionLaws.lean:58` | gefunden, Task 6 |
| 17 | `ChildModule.projS_of_inS` | `DimensionFoundation/ProjectionLaws.lean:62` | gefunden, Task 6 |
| 18 | `ChildModule.projL_idem` | `DimensionFoundation/ProjectionLaws.lean:67` | gefunden, Task 6 |
| 19 | `ChildModule.projS_idem` | `DimensionFoundation/ProjectionLaws.lean:70` | gefunden, Task 6 |
| 20 | `ChildModule.projL_projS` | `DimensionFoundation/ProjectionLaws.lean:73` | gefunden, Task 6 |
| 21 | `ChildModule.projS_projL` | `DimensionFoundation/ProjectionLaws.lean:76` | gefunden, Task 6 |
| 22 | `ChildModule.projL_addV_projS` | `DimensionFoundation/ProjectionLaws.lean:79` | gefunden, Task 6 |
| 23 | `ChildModule.projections_idempotent_complementary` | `DimensionFoundation/ProjectionLaws.lean:82` | gefunden, Task 6 |
| 24 | `ChildModule.projL_addV` | `DimensionFoundation/ProjectionLaws.lean:92` | gefunden, Task 6 |
| 25 | `ChildModule.projL_smul` | `DimensionFoundation/ProjectionLaws.lean:96` | gefunden, Task 6 |
| 26 | `ChildModule.projS_addV` | `DimensionFoundation/ProjectionLaws.lean:100` | gefunden, Task 6 |
| 27 | `ChildModule.projS_smul` | `DimensionFoundation/ProjectionLaws.lean:107` | gefunden, Task 6 |
| 28 | `ChildModule.inL_iff_projL_eq` | `DimensionFoundation/ProjectionLaws.lean:116` | gefunden, Task 6 |
| 29 | `ChildModule.inS_iff_projS_eq` | `DimensionFoundation/ProjectionLaws.lean:120` | gefunden, Task 6 |
| 30 | `ChildModule.range_projL` | `DimensionFoundation/ProjectionLaws.lean:125` | gefunden, Task 6 |
| 31 | `ChildModule.range_projS` | `DimensionFoundation/ProjectionLaws.lean:130` | gefunden, Task 6 |
| 32 | `ChildModule.inS_iff_projL_eq_zero` | `DimensionFoundation/ProjectionLaws.lean:135` | gefunden, Task 6 |
| 33 | `ChildModule.inL_iff_projS_eq_zero` | `DimensionFoundation/ProjectionLaws.lean:144` | gefunden, Task 6 |
| 34 | `ChildModule.dot_inL_inS` | `DimensionFoundation/ProjectionLaws.lean:155` | gefunden, Task 6 |
| 35 | `ChildModule.dot_projL_projS` | `DimensionFoundation/ProjectionLaws.lean:160` | gefunden, Task 6 |
| 36 | `ChildModule.dot_projS_projL` | `DimensionFoundation/ProjectionLaws.lean:164` | gefunden, Task 6 |
| 37 | `ChildModule.dot_split` | `DimensionFoundation/ProjectionLaws.lean:171` | gefunden, Task 6 |
| 38 | `Word` | `PrimitiveTree/FiniteWords.lean:22` | gefunden, Vorherige Tasks |
| 39 | `Word.root` | `PrimitiveTree/FiniteWords.lean:29` | gefunden, Vorherige Tasks |
| 40 | `Word.depth` | `PrimitiveTree/FiniteWords.lean:32` | gefunden, Vorherige Tasks |
| 41 | `Word.IsParent` | `PrimitiveTree/FiniteWords.lean:37` | gefunden, Vorherige Tasks |
| 42 | `Word.Edge` | `PrimitiveTree/FiniteWords.lean:40` | gefunden, Vorherige Tasks |
| 43 | `Word.ChildOf` | `PrimitiveTree/FiniteWords.lean:103` | gefunden, Vorherige Tasks |
| 44 | `Word.root_no_parent` | `PrimitiveTree/FiniteWords.lean:69` | gefunden, Vorherige Tasks |
| 45 | `Word.nonroot_has_parent` | `PrimitiveTree/FiniteWords.lean:72` | gefunden, Vorherige Tasks |
| 46 | `Word.parent_unique` | `PrimitiveTree/FiniteWords.lean:75` | gefunden, Vorherige Tasks |
| 47 | `Word.rootEdges` | `PrimitiveTree/FiniteWords.lean:133` | gefunden, Vorherige Tasks |
| 48 | `Word.dpath_root_unique` | `PrimitiveTree/FiniteWords.lean:142` | gefunden, Vorherige Tasks |
| 49 | `Word.connected` | `PrimitiveTree/FiniteWords.lean:187` | gefunden, Vorherige Tasks |
| 50 | `Word.no_cycle` | `PrimitiveTree/FiniteWords.lean:261` | gefunden, Vorherige Tasks |
| 51 | `Word.unbounded_depth` | `PrimitiveTree/FiniteWords.lean:288` | gefunden, Vorherige Tasks |
| 52 | `Child` | `PrimitiveTree/FiniteChild.lean:18` | gefunden, Vorherige Tasks |
| 53 | `Child.inclSucc` | `PrimitiveTree/FiniteChild.lean:76` | gefunden, Vorherige Tasks |
| 54 | `Child.enum` | `PrimitiveTree/FiniteChild.lean:111` | gefunden, Vorherige Tasks |
| 55 | `Child.nodup_enum` | `PrimitiveTree/FiniteChild.lean:144` | gefunden, Vorherige Tasks |
| 56 | `WordOmega` | `TreeFoundation/OmegaTree.lean:18` | gefunden, Vorherige Tasks |
| 57 | `OmegaTree.childOfIndex` | `TreeFoundation/OmegaTree.lean:23` | gefunden, Vorherige Tasks |
| 58 | `OmegaTree.children_distinct` | `TreeFoundation/OmegaTree.lean:33` | gefunden, Vorherige Tasks |
| 59 | `OmegaTree.infinitely_many_children` | `TreeFoundation/OmegaTree.lean:37` | gefunden, Vorherige Tasks |
| 60 | `OmegaTree.unbounded_depth` | `TreeFoundation/OmegaTree.lean:52` | gefunden, Vorherige Tasks |
| 61 | `ArityEmbedding.mapWord_injective` | `TreeFoundation/ArityEmbeddings.lean:36` | gefunden, Vorherige Tasks |
| 62 | `ArityEmbedding.mapWord_isParent` | `TreeFoundation/ArityEmbeddings.lean:55` | gefunden, Vorherige Tasks |
| 63 | `ArityEmbedding.wordOmega_wordSucc` | `TreeFoundation/ArityEmbeddings.lean:105` | gefunden, Vorherige Tasks |
| 64 | `ArityEmbedding.vertex_union` | `TreeFoundation/ArityEmbeddings.lean:147` | gefunden, Vorherige Tasks |
| 65 | `ArityEmbedding.edge_union` | `TreeFoundation/ArityEmbeddings.lean:153` | gefunden, Vorherige Tasks |
| 66 | `Word.edgeFold` | `PrimitiveTree/RootEdges.lean:22` | gefunden, Vorherige Tasks |
| 67 | `Word.unitSum` | `PrimitiveTree/RootEdges.lean:27` | gefunden, Vorherige Tasks |
| 68 | `Word.pathSum` | `PrimitiveTree/RootEdges.lean:30` | gefunden, Vorherige Tasks |
| 69 | `Word.unitSum_rootEdges` | `PrimitiveTree/RootEdges.lean:68` | gefunden, Vorherige Tasks |
| 70 | `Word.pathSum_eq_depth` | `PrimitiveTree/RootEdges.lean:75` | gefunden, Vorherige Tasks |
| 71 | `Word.pathSum_cons` | `PrimitiveTree/RootEdges.lean:77` | gefunden, Vorherige Tasks |
| 72 | `Ray.pathSum_prefixAt` | `TreeFoundation/InfiniteRays.lean:44` | gefunden, Vorherige Tasks |
| 73 | `PrimitiveScope.prefixCount_eq` | `TreeAnalysis/PrimitiveDataScope.lean:51` | gefunden, Vorherige Tasks |
| 74 | `PrimitiveScope.prefixCount_not_isCauchy` | `TreeAnalysis/PrimitiveDataScope.lean:62` | gefunden, Vorherige Tasks |
| 75 | `PrimitiveScope.prefixCount_indep` | `TreeAnalysis/PrimitiveDataScope.lean:77` | gefunden, Vorherige Tasks |
| 76 | `UnaryPath` | `PrimitiveTree/UnaryPaths.lean:16` | gefunden, Vorherige Tasks |
| 77 | `UnaryPath.extend` | `PrimitiveTree/UnaryPaths.lean:27` | gefunden, Vorherige Tasks |
| 78 | `UnaryPath.concat` | `PrimitiveTree/UnaryPaths.lean:30` | gefunden, Vorherige Tasks |
| 79 | `UnaryPath.iterate` | `PrimitiveTree/UnaryPaths.lean:35` | gefunden, Vorherige Tasks |
| 80 | `TreeN` | `TreeNumbers/PathNaturals.lean:17` | gefunden, Vorherige Tasks |
| 81 | `TreeN.add` | `TreeNumbers/PathNaturals.lean:34` | gefunden, Vorherige Tasks |
| 82 | `TreeN.mul` | `TreeNumbers/PathNaturals.lean:37` | gefunden, Vorherige Tasks |
| 83 | `TreeN.add_comm` | `TreeNumbers/PathNaturals.lean:79` | gefunden, Vorherige Tasks |
| 84 | `TreeN.mul_comm` | `TreeNumbers/PathNaturals.lean:117` | gefunden, Vorherige Tasks |
| 85 | `TreeN.right_distrib` | `TreeNumbers/PathNaturals.lean:126` | gefunden, Vorherige Tasks |
| 86 | `TreeN.mul_assoc` | `TreeNumbers/PathNaturals.lean:136` | gefunden, Vorherige Tasks |
| 87 | `TreeN.instCSR` | `TreeNumbers/PathNaturals.lean:156` | gefunden, Vorherige Tasks |
| 88 | `TreeN.induction` | `TreeNumbers/FoundationsLedger.lean:32` | gefunden, Vorherige Tasks |
| 89 | `TreeN.recN` | `TreeNumbers/FoundationsLedger.lean:42` | gefunden, Vorherige Tasks |
| 90 | `TreeN.recN_unique` | `TreeNumbers/FoundationsLedger.lean:51` | gefunden, Vorherige Tasks |
| 91 | `TreeN.le_antisymm` | `TreeNumbers/PathOrder.lean:141` | gefunden, Vorherige Tasks |
| 92 | `TreeN.lt_or_eq_or_gt` | `TreeNumbers/PathOrder.lean:167` | gefunden, Vorherige Tasks |
| 93 | `TreeN.le_iff_exists_add` | `TreeNumbers/FoundationsLedger.lean:83` | gefunden, Vorherige Tasks |
| 94 | `DepthQuotient.DepthRel` | `TreeNumbers/DepthQuotient.lean:40` | gefunden, Vorherige Tasks |
| 95 | `DepthQuotient.DepthClass` | `TreeNumbers/DepthQuotient.lean:62` | gefunden, Vorherige Tasks |
| 96 | `DepthQuotient.repeatW` | `TreeNumbers/DepthQuotient.lean:119` | gefunden, Vorherige Tasks |
| 97 | `DepthQuotient.OrderedSemiringIso` | `TreeNumbers/DepthQuotient.lean:281` | gefunden, Vorherige Tasks |
| 98 | `DepthQuotient.depthIso` | `TreeNumbers/DepthQuotient.lean:294` | gefunden, Vorherige Tasks |
| 99 | `DepthQuotient.depthIso_letter_indep` | `TreeNumbers/DepthQuotient.lean:307` | gefunden, Vorherige Tasks |
| 100 | `DepthQuotient.no_positive_count_of_noLetter` | `TreeNumbers/DepthQuotient.lean:331` | gefunden, Vorherige Tasks |
| 101 | `TreeN.PairEq` | `TreeNumbers/PathIntegers.lean:23` | gefunden, Vorherige Tasks |
| 102 | `TreeN.pairEq_refl` | `TreeNumbers/PathIntegers.lean:25` | gefunden, Vorherige Tasks |
| 103 | `TreeN.pairEq_symm` | `TreeNumbers/PathIntegers.lean:27` | gefunden, Vorherige Tasks |
| 104 | `TreeN.pairEq_trans` | `TreeNumbers/PathIntegers.lean:29` | gefunden, Vorherige Tasks |
| 105 | `TreeN.normPair` | `TreeNumbers/PathIntegers.lean:37` | gefunden, Vorherige Tasks |
| 106 | `TreeN.normal_unique` | `TreeNumbers/PathIntegers.lean:64` | gefunden, Vorherige Tasks |
| 107 | `TreeZ` | `TreeNumbers/PathIntegers.lean:92` | gefunden, Vorherige Tasks |
| 108 | `TreeZ.mkZ_sound` | `TreeNumbers/PathIntegers.lean:113` | gefunden, Vorherige Tasks |
| 109 | `TreeZ.mkZ_exact` | `TreeNumbers/PathIntegers.lean:119` | gefunden, Vorherige Tasks |
| 110 | `TreeZ.instCRing` | `TreeNumbers/PathIntegers.lean:256` | gefunden, Vorherige Tasks |
| 111 | `TreeZ.mul_eq_zero` | `TreeNumbers/PathIntegers.lean:319` | gefunden, Vorherige Tasks |
| 112 | `TreeZ.mul_left_cancel` | `TreeNumbers/PathIntegers.lean:330` | gefunden, Vorherige Tasks |
| 113 | `TreeZ.mul_ne_zero` | `TreeNumbers/PathIntegers.lean:342` | gefunden, Vorherige Tasks |
| 114 | `TreeZ.ofN_lt_ofN` | `TreeNumbers/FoundationsLedger.lean:124` | gefunden, Vorherige Tasks |
| 115 | `TreeZ.lt_trichotomy` | `TreeNumbers/FoundationsLedger.lean:140` | gefunden, Vorherige Tasks |
| 116 | `TreeZ.ofN` | `TreeNumbers/PathIntegers.lean:351` | gefunden, Vorherige Tasks |
| 117 | `TreeZ.ofN_injective` | `TreeNumbers/PathIntegers.lean:366` | gefunden, Vorherige Tasks |
| 118 | `TriplePath` | `TreeNumbers/PathTriples.lean:32` | gefunden, Vorherige Tasks |
| 119 | `TriplePath.numer` | `TreeNumbers/PathTriples.lean:46` | gefunden, Vorherige Tasks |
| 120 | `TriplePath.denom` | `TreeNumbers/PathTriples.lean:49` | gefunden, Vorherige Tasks |
| 121 | `TriplePath.denom_pos` | `TreeNumbers/PathTriples.lean:56` | gefunden, Vorherige Tasks |
| 122 | `TriplePath.Rel` | `TreeNumbers/PathTriples.lean:64` | gefunden, Vorherige Tasks |
| 123 | `Frac.Eqv` | `TreeNumbers/PathFractions.lean:41` | gefunden, Vorherige Tasks |
| 124 | `Frac.eqv_trans` | `TreeNumbers/PathFractions.lean:49` | gefunden, Vorherige Tasks |
| 125 | `Frac.add_resp` | `TreeNumbers/PathFractions.lean:101` | gefunden, Vorherige Tasks |
| 126 | `Frac.mul_resp` | `TreeNumbers/PathFractions.lean:113` | gefunden, Vorherige Tasks |
| 127 | `TriplePath.universal_witness` | `TreeNumbers/PathTriples.lean:194` | gefunden, Vorherige Tasks |
| 128 | `TriplePath.unary_numer_ne_zero` | `TreeNumbers/FoundationsLedger.lean:208` | gefunden, Vorherige Tasks |
| 129 | `TriplePath.unary_no_universal_witness` | `TreeNumbers/FoundationsLedger.lean:216` | gefunden, Vorherige Tasks |
| 130 | `Frac.mul_inv_cancel` | `TreeNumbers/PathFractions.lean:243` | gefunden, Vorherige Tasks |
| 131 | `FracQ.instTField` | `TreeAnalysis/FractionCharacterization.lean:240` | gefunden, Vorherige Tasks |
| 132 | `TreeQ.NonnegQ` | `TreeAnalysis/RationalOrder.lean:123` | gefunden, Vorherige Tasks |
| 133 | `TreeQ.archQ` | `TreeAnalysis/RationalOrder.lean:282` | gefunden, Vorherige Tasks |
| 134 | `TreeQ.instTOField` | `TreeAnalysis/RationalOrder.lean:299` | gefunden, Vorherige Tasks |
| 135 | `TOField.eps` | `TreeAnalysis/DyadicPrecision.lean:73` | gefunden, Vorherige Tasks |
| 136 | `TOField.exists_eps_lt` | `TreeAnalysis/DyadicPrecision.lean:173` | gefunden, Vorherige Tasks |
| 137 | `FracQ` | `TreeAnalysis/FractionCharacterization.lean:74` | gefunden, Vorherige Tasks |
| 138 | `TreeQ.ofFracQ_toFracQ` | `TreeAnalysis/FractionCharacterization.lean:281` | gefunden, Vorherige Tasks |
| 139 | `TreeQ.toFracQ_ofFracQ` | `TreeAnalysis/FractionCharacterization.lean:285` | gefunden, Vorherige Tasks |
| 140 | `TreeQ.orderedFieldIsoFracQ` | `TreeAnalysis/FractionCharacterization.lean:347` | gefunden, Vorherige Tasks |
| 141 | `TreeQ.mk_eq_of_depth_eq` | `TreeAnalysis/FractionCharacterization.lean:61` | gefunden, Vorherige Tasks |
| 142 | `TriplePath.unary_numer_ne_zero` | `TreeNumbers/FoundationsLedger.lean:208` | gefunden, Vorherige Tasks |
| 143 | `TreeQ.arityIso_comp` | `TreeNumbers/FoundationsLedger.lean:284` | gefunden, Vorherige Tasks |
| 144 | `TreeQ.transfer_comp` | `TreeNumbers/FoundationsLedger.lean:272` | gefunden, Vorherige Tasks |
| 145 | `TreeQ.transfer_natCast` | `TreeNumbers/FoundationsLedger.lean:277` | gefunden, Vorherige Tasks |
| 146 | `ChildModule.addV` | `DimensionFoundation/FiniteChildModule.lean:30` | gefunden, Vorherige Tasks |
| 147 | `ChildModule.smul` | `DimensionFoundation/FiniteChildModule.lean:32` | gefunden, Vorherige Tasks |
| 148 | `ChildModule.coordSum` | `DimensionFoundation/FiniteChildModule.lean:59` | gefunden, Vorherige Tasks |
| 149 | `ChildModule.dot` | `DimensionFoundation/FiniteChildModule.lean:71` | gefunden, Vorherige Tasks |
| 150 | `ChildModule.dot_comm` | `DimensionFoundation/FiniteChildModule.lean:114` | gefunden, Vorherige Tasks |
| 151 | `FinSum.sumC` | `DimensionFoundation/FiniteSums.lean:66` | gefunden, Vorherige Tasks |
| 152 | `ChildModule.InL` | `DimensionFoundation/FiniteChildModule.lean:65` | gefunden, Vorherige Tasks |
| 153 | `ChildModule.InS` | `DimensionFoundation/FiniteChildModule.lean:68` | gefunden, Vorherige Tasks |
| 154 | `ChildModule.dot_u_of_inS` | `DimensionFoundation/FiniteChildModule.lean:110` | gefunden, Vorherige Tasks |
| 155 | `ChildModule.dot_comm` | `DimensionFoundation/FiniteChildModule.lean:114` | gefunden, Vorherige Tasks |
| 156 | `ChildModule.IsBasisOf` | `DimensionFoundation/TransverseBasis.lean:47` | gefunden, Vorherige Tasks |
| 157 | `ChildModule.longitudinal_basis` | `DimensionFoundation/TransverseBasis.lean:65` | gefunden, Vorherige Tasks |
| 158 | `longitudinal_basis_treeQ` | `DimensionFoundation/Instances.lean:24` | gefunden, Vorherige Tasks |
| 159 | `ChildModule.tv` | `DimensionFoundation/TransverseBasis.lean:85` | gefunden, Vorherige Tasks |
| 160 | `ChildModule.tv_indep` | `DimensionFoundation/TransverseBasis.lean:134` | gefunden, Vorherige Tasks |
| 161 | `ChildModule.tv_span` | `DimensionFoundation/TransverseBasis.lean:141` | gefunden, Vorherige Tasks |
| 162 | `ChildModule.transverse_basis` | `DimensionFoundation/TransverseBasis.lean:155` | gefunden, Vorherige Tasks |
| 163 | `ChildModule.transverse_index_bijection` | `DimensionFoundation/TransverseBasis.lean:164` | gefunden, Vorherige Tasks |
| 164 | `ChildModule.projL` | `DimensionFoundation/TransverseBasis.lean:173` | gefunden, Vorherige Tasks |
| 165 | `ChildModule.projS` | `DimensionFoundation/TransverseBasis.lean:176` | gefunden, Vorherige Tasks |
| 166 | `ChildModule.decomposition` | `DimensionFoundation/TransverseBasis.lean:181` | gefunden, Vorherige Tasks |
| 167 | `ChildModule.decomposition_unique` | `DimensionFoundation/TransverseBasis.lean:194` | gefunden, Vorherige Tasks |
| 168 | `ChildModule.inL_inS_zero` | `DimensionFoundation/TransverseBasis.lean:211` | gefunden, Vorherige Tasks |
| 169 | `direct_sum_treeQ` | `DimensionFoundation/Instances.lean:29` | gefunden, Vorherige Tasks |
| 170 | `ChildModule.transverse_one_zero` | `DimensionFoundation/TransverseBasis.lean:218` | gefunden, Vorherige Tasks |
| 171 | `ChildModule.dot_perm` | `DimensionFoundation/TransverseBasis.lean:231` | gefunden, Vorherige Tasks |
| 172 | `ChildModule.inS_perm` | `DimensionFoundation/TransverseBasis.lean:237` | gefunden, Vorherige Tasks |
| 173 | `ChildModule.inL_perm` | `DimensionFoundation/TransverseBasis.lean:244` | gefunden, Vorherige Tasks |
| 174 | `OmegaModule.FO` | `DimensionFoundation/OmegaFiniteSupport.lean:26` | gefunden, Vorherige Tasks |
| 175 | `OmegaModule.FinSupp` | `DimensionFoundation/OmegaFiniteSupport.lean:38` | gefunden, Vorherige Tasks |
| 176 | `OmegaModule.InSO` | `DimensionFoundation/OmegaFiniteSupport.lean:41` | gefunden, Vorherige Tasks |
| 177 | `OmegaModule.tvO` | `DimensionFoundation/OmegaFiniteSupport.lean:113` | gefunden, Vorherige Tasks |
| 178 | `OmegaModule.tvO_indep` | `DimensionFoundation/OmegaFiniteSupport.lean:160` | gefunden, Vorherige Tasks |
| 179 | `OmegaModule.tvO_span` | `DimensionFoundation/OmegaFiniteSupport.lean:170` | gefunden, Vorherige Tasks |
| 180 | `omega_indep` | `DimensionFoundation/Instances.lean:43` | gefunden, Vorherige Tasks |
| 181 | `omega_span` | `DimensionFoundation/Instances.lean:48` | gefunden, Vorherige Tasks |
| 182 | `OmegaModule.pad` | `DimensionFoundation/OmegaFiniteSupport.lean:217` | gefunden, Vorherige Tasks |
| 183 | `OmegaModule.pad_injective` | `DimensionFoundation/OmegaFiniteSupport.lean:236` | gefunden, Vorherige Tasks |
| 184 | `OmegaModule.pad_inSO` | `DimensionFoundation/OmegaFiniteSupport.lean:249` | gefunden, Vorherige Tasks |
| 185 | `OmegaModule.pad_tv` | `DimensionFoundation/OmegaFiniteSupport.lean:266` | gefunden, Vorherige Tasks |
| 186 | `OmegaModule.padSucc` | `DimensionFoundation/OmegaFiniteSupport.lean:283` | gefunden, Vorherige Tasks |
| 187 | `OmegaModule.padSucc_inS` | `DimensionFoundation/OmegaFiniteSupport.lean:294` | gefunden, Vorherige Tasks |
| 188 | `OmegaModule.padSucc_tv` | `DimensionFoundation/OmegaFiniteSupport.lean:304` | gefunden, Vorherige Tasks |
| 189 | `Longitudinal.allOnes_not_finSupp` | `DimensionFoundation/BoundaryLongitudinal.lean:35` | gefunden, Vorherige Tasks |
| 190 | `Longitudinal.no_finSupp_uniform_limit` | `DimensionFoundation/BoundaryLongitudinal.lean:40` | gefunden, Vorherige Tasks |
| 191 | `Longitudinal.padSucc_u_not_inL` | `DimensionFoundation/BoundaryLongitudinal.lean:50` | gefunden, Vorherige Tasks |
| 192 | `Ray` | `TreeFoundation/InfiniteRays.lean:19` | gefunden, Vorherige Tasks |
| 193 | `Ray.prefixAt` | `TreeFoundation/InfiniteRays.lean:30` | gefunden, Vorherige Tasks |
| 194 | `Ray.prefixAt_succ` | `TreeFoundation/InfiniteRays.lean:34` | gefunden, Vorherige Tasks |
| 195 | `Ray.eq_of_prefixAt` | `TreeFoundation/InfiniteRays.lean:65` | gefunden, Vorherige Tasks |
| 196 | `Ray.depth_unbounded` | `TreeFoundation/InfiniteRays.lean:83` | gefunden, Vorherige Tasks |
| 197 | `RayOmega.ofFinite` | `TreeFoundation/InfiniteRays.lean:93` | gefunden, Vorherige Tasks |
| 198 | `RayOmega.identityRay_not_finite` | `TreeFoundation/InfiniteRays.lean:108` | gefunden, Vorherige Tasks |
| 199 | `RayOmega.union_proper` | `TreeFoundation/InfiniteRays.lean:116` | gefunden, Vorherige Tasks |
| 200 | `Ray.Agree` | `BoundaryTopology/Cylinders.lean:53` | gefunden, Vorherige Tasks |
| 201 | `Ray.Cyl` | `BoundaryTopology/Cylinders.lean:56` | gefunden, Vorherige Tasks |
| 202 | `Ray.cyl_prefixAt` | `BoundaryTopology/Cylinders.lean:124` | gefunden, Vorherige Tasks |
| 203 | `Ray.PrefixOpen` | `BoundaryTopology/PrefixTopology.lean:39` | gefunden, Vorherige Tasks |
| 204 | `Ray.prefixTopology` | `BoundaryTopology/PrefixTopology.lean:42` | gefunden, Vorherige Tasks |
| 205 | `Ray.cyl_open` | `BoundaryTopology/PrefixTopology.lean:58` | gefunden, Vorherige Tasks |
| 206 | `Ray.cyl_compl_open` | `BoundaryTopology/PrefixTopology.lean:62` | gefunden, Vorherige Tasks |
| 207 | `Ray.separate_of_diff` | `BoundaryTopology/PrefixTopology.lean:83` | gefunden, Vorherige Tasks |
| 208 | `Ray.not_not_diff_of_ne` | `BoundaryTopology/PrefixTopology.lean:102` | gefunden, Vorherige Tasks |
| 209 | `Ray.no_isolated` | `BoundaryTopology/TopologicalObstructions.lean:81` | gefunden, Vorherige Tasks |
| 210 | `Ray.connected_subsingleton` | `BoundaryTopology/TopologicalObstructions.lean:133` | gefunden, Vorherige Tasks |
| 211 | `Ray.boundary_disconnected` | `BoundaryTopology/TopologicalObstructions.lean:119` | gefunden, Vorherige Tasks |
| 212 | `Ray.cyl_not_compact` | `BoundaryTopology/TopologicalObstructions.lean:162` | gefunden, Vorherige Tasks |
| 213 | `Ray.not_locallyCompactAt` | `BoundaryTopology/TopologicalObstructions.lean:219` | gefunden, Vorherige Tasks |
| 214 | `Topology.Chart` | `BoundaryTopology/ManifoldConditions.lean:41` | gefunden, Vorherige Tasks |
| 215 | `Ray.no_zero_dim_chart` | `BoundaryTopology/ManifoldConditions.lean:117` | gefunden, Vorherige Tasks |
| 216 | `Ray.unaryChart` | `BoundaryTopology/ManifoldConditions.lean:127` | gefunden, Vorherige Tasks |
| 217 | `TreeR.IntervalsConnected` | `BoundaryTopology/ManifoldConditions.lean:208` | gefunden, Vorherige Tasks |
| 218 | `no_chart_into_real` | `BoundaryTopology/ManifoldConditions.lean:227` | gefunden, Vorherige Tasks |
| 219 | `TreeR.realIdChart` | `BoundaryTopology/RealLineManifold.lean:81` | gefunden, Vorherige Tasks |
| 220 | `Ray.encode` | `BoundaryTopology/BinaryEncoding.lean:103` | gefunden, Vorherige Tasks |
| 221 | `Ray.encode_not_injective` | `BoundaryTopology/BinaryEncoding.lean:176` | gefunden, Vorherige Tasks |
| 222 | `Ray.encode_letter_choice_dependence` | `TreeAnalysis/PrimitiveDataScope.lean:144` | gefunden, Vorherige Tasks |
| 223 | `RayAutomorphism.LevelPerm` | `TreeFoundation/RayAutomorphism.lean:33` | gefunden, Vorherige Tasks |
| 224 | `RayAutomorphism.TreeAut` | `TreeFoundation/RayAutomorphism.lean:101` | gefunden, Vorherige Tasks |
| 225 | `RayAutomorphism.treeAut` | `TreeFoundation/RayAutomorphism.lean:111` | gefunden, Vorherige Tasks |
| 226 | `RayAutomorphism.rayAct` | `TreeFoundation/RayAutomorphism.lean:123` | gefunden, Vorherige Tasks |
| 227 | `RayAutomorphism.swapPerm` | `TreeFoundation/RayAutomorphism.lean:190` | gefunden, Vorherige Tasks |
| 228 | `RayAutomorphism.rayAct_swapPerm` | `TreeFoundation/RayAutomorphism.lean:197` | gefunden, Vorherige Tasks |
| 229 | `RayAutomorphism.invariant_const` | `TreeFoundation/RayAutomorphism.lean:209` | gefunden, Vorherige Tasks |
| 230 | `RayAutomorphism.invariant_const` | `TreeFoundation/RayAutomorphism.lean:209` | gefunden, Vorherige Tasks |
| 231 | `RayAutomorphism.swapInvariant_const` | `TreeFoundation/RayAutomorphism.lean:214` | gefunden, Vorherige Tasks |
| 232 | `RayAutomorphism.subtreeSwapAut` | `TreeFoundation/AutomorphismCounterexample.lean:105` | gefunden, Vorherige Tasks |
| 233 | `RayAutomorphism.subtreeSwapAut_not_levelwise` | `TreeFoundation/AutomorphismCounterexample.lean:189` | gefunden, Vorherige Tasks |
| 234 | `RayAutomorphism.levelwise_converse_false` | `TreeFoundation/AutomorphismCounterexample.lean:204` | gefunden, Vorherige Tasks |
| 235 | `TOField.eps` | `TreeAnalysis/DyadicPrecision.lean:73` | gefunden, Vorherige Tasks |
| 236 | `TOField.eps_succ_add` | `TreeAnalysis/DyadicPrecision.lean:94` | gefunden, Vorherige Tasks |
| 237 | `TOField.three_eps_le` | `TreeAnalysis/DyadicPrecision.lean:141` | gefunden, Vorherige Tasks |
| 238 | `TOField.exists_eps_lt` | `TreeAnalysis/DyadicPrecision.lean:173` | gefunden, Vorherige Tasks |
| 239 | `TOField.CSeq` | `TreeAnalysis/CauchyData.lean:47` | gefunden, Vorherige Tasks |
| 240 | `TOField.IsModulus` | `TreeAnalysis/CauchyData.lean:40` | gefunden, Vorherige Tasks |
| 241 | `TOField.SeqEquiv` | `TreeAnalysis/CauchyData.lean:53` | gefunden, Vorherige Tasks |
| 242 | `TOField.isRegular_reg` | `TreeAnalysis/CauchyData.lean:130` | gefunden, Vorherige Tasks |
| 243 | `TOField.seqEquiv_trans` | `TreeAnalysis/CauchyData.lean:162` | gefunden, Vorherige Tasks |
| 244 | `TOField.reg_equiv` | `TreeAnalysis/CauchyData.lean:144` | gefunden, Vorherige Tasks |
| 245 | `TreeR` | `TreeAnalysis/RealQuotient.lean:42` | gefunden, Vorherige Tasks |
| 246 | `TreeR.mkR` | `TreeAnalysis/RealQuotient.lean:51` | gefunden, Vorherige Tasks |
| 247 | `TreeR.instCRing` | `TreeAnalysis/RealQuotient.lean:161` | gefunden, Vorherige Tasks |
| 248 | `TreeR.ofQ_injective` | `TreeAnalysis/RealQuotient.lean:195` | gefunden, Vorherige Tasks |
| 249 | `TreeR.zero_ne_one` | `TreeAnalysis/RealQuotient.lean:204` | gefunden, Vorherige Tasks |
| 250 | `TreeR.RLt` | `TreeAnalysis/RealOrderApartness.lean:69` | gefunden, Vorherige Tasks |
| 251 | `TreeR.RLe` | `TreeAnalysis/RealOrderApartness.lean:71` | gefunden, Vorherige Tasks |
| 252 | `TreeR.RApart` | `TreeAnalysis/RealOrderApartness.lean:77` | gefunden, Vorherige Tasks |
| 253 | `TreeR.lt_trans` | `TreeAnalysis/RealOrderApartness.lean:172` | gefunden, Vorherige Tasks |
| 254 | `TreeR.le_antisymm` | `TreeAnalysis/RealOrderApartness.lean:187` | gefunden, Vorherige Tasks |
| 255 | `TreeR.eq_of_not_apart` | `TreeAnalysis/RealOrderApartness.lean:292` | gefunden, Vorherige Tasks |
| 256 | `TreeR.rinv` | `TreeAnalysis/RealOrderApartness.lean:330` | gefunden, Vorherige Tasks |
| 257 | `TreeR.mul_rinv` | `TreeAnalysis/RealOrderApartness.lean:335` | gefunden, Vorherige Tasks |
| 258 | `TreeR.exists_inv_of_apart` | `TreeAnalysis/RealOrderApartness.lean:375` | gefunden, Vorherige Tasks |
| 259 | `TreeR.mul_left_cancel_of_ne` | `TreeAnalysis/ApartnessStrength.lean:64` | gefunden, Vorherige Tasks |
| 260 | `TreeR.rat_dense` | `TreeAnalysis/CompletenessScope.lean:127` | gefunden, Vorherige Tasks |
| 261 | `TreeR.realArityIso_comp` | `TreeAnalysis/FoundationsClosure.lean:146` | gefunden, Vorherige Tasks |
| 262 | `TreeR.limit_unique` | `TreeAnalysis/CompletenessScope.lean:89` | gefunden, Vorherige Tasks |
| 263 | `TreeR.ofQ_seq_converges` | `TreeAnalysis/CompletenessScope.lean:108` | gefunden, Vorherige Tasks |
| 264 | `TreeR.ApproxData` | `TreeAnalysis/CompletenessStrength.lean:264` | gefunden, Vorherige Tasks |
| 265 | `TreeR.limit_of_approx` | `TreeAnalysis/CompletenessStrength.lean:306` | gefunden, Vorherige Tasks |
| 266 | `TreeR.tower_limit` | `TreeAnalysis/CompletenessScope.lean:271` | gefunden, Vorherige Tasks |
| 267 | `TreeR.Tracked.converges` | `TreeAnalysis/ApproxClosure.lean:262` | gefunden, Vorherige Tasks |
| 268 | `TreeR.TExpr.lim_tracked` | `TreeAnalysis/TrackedExpressions.lean:66` | gefunden, Vorherige Tasks |
| 269 | `TreeR.TExpr.converges_evalSeq` | `TreeAnalysis/TrackedExpressions.lean:85` | gefunden, Vorherige Tasks |
| 270 | `TreeR.complete_iff_cauchyApprox` | `TreeAnalysis/LiftingPrinciples.lean:124` | gefunden, Vorherige Tasks |
| 271 | `TreeR.complete_of_choice` | `TreeAnalysis/LiftingPrinciples.lean:245` | gefunden, Vorherige Tasks |
| 272 | `TreeR.modulusFreeComplete_of_choice` | `TreeAnalysis/LiftingPrinciples.lean:249` | gefunden, Vorherige Tasks |
| 273 | `TreeR.SupData.isLUB` | `TreeAnalysis/SupremumScope.lean:65` | gefunden, Vorherige Tasks |
| 274 | `TreeR.SupData.ofList_isLUB` | `TreeAnalysis/SupremumScope.lean:152` | gefunden, Vorherige Tasks |
| 275 | `TreeR.tower_monotone_lub` | `TreeAnalysis/SupremumScope.lean:182` | gefunden, Vorherige Tasks |
| 276 | `TreeR.UCMod` | `TreeAnalysis/CompletionCharacterization.lean:39` | gefunden, Vorherige Tasks |
| 277 | `TreeR.extendR` | `TreeAnalysis/CompletionCharacterization.lean:53` | gefunden, Vorherige Tasks |
| 278 | `TreeR.extendR_unique` | `TreeAnalysis/CompletionCharacterization.lean:94` | gefunden, Vorherige Tasks |
| 279 | `TreeR.extendR_comp` | `TreeAnalysis/CompletionCharacterization.lean:111` | gefunden, Vorherige Tasks |
| 280 | `TreeR.inv_iff_markov` | `TreeAnalysis/ApartnessStrength.lean:349` | gefunden, Vorherige Tasks |
| 281 | `TreeR.zeroOrApart_iff_lpo` | `TreeAnalysis/ApartnessStrength.lean:369` | gefunden, Vorherige Tasks |
| 282 | `TreeR.trichotomy_iff_lpo` | `TreeAnalysis/FoundationsClosure.lean:230` | gefunden, Vorherige Tasks |
| 283 | `TreeR.decidableZero_iff_wlpo` | `TreeAnalysis/FoundationsClosure.lean:199` | gefunden, Vorherige Tasks |
| 284 | `TreeR.wlpo_of_unrestrictedLUB` | `TreeAnalysis/SupremumScope.lean:257` | gefunden, Vorherige Tasks |
| 285 | `TreeR.lpo_of_bmc` | `TreeAnalysis/SupremumScope.lean:312` | gefunden, Vorherige Tasks |
| 286 | `ExtLevel.vertexLevel` | `TreeFoundation/ExtendedLevels.lean:50` | gefunden, Vorherige Tasks |
| 287 | `ExtLevel.rayLevel` | `TreeFoundation/ExtendedLevels.lean:54` | gefunden, Vorherige Tasks |
| 288 | `ExtLevel.root_level` | `TreeFoundation/ExtendedLevels.lean:57` | gefunden, Vorherige Tasks |
| 289 | `ExtLevel.first_edge_unit` | `TreeFoundation/ExtendedLevels.lean:60` | gefunden, Vorherige Tasks |

**Abschluss Anhang II:** 289/289 deklarierte Fundstellen vorhanden; davon 37 Task-6-Ergänzungen und 252 ältere Deklarationen. Kein fehlender Quellpfad und keine inkonsistente Deklarationsposition ermittelt. Wiederholte Hinweise auf frühere Elaborationssignaturen sind nicht mit einer neuen Kernel-Nachprüfung gleichzusetzen.

## Schlussfolgerung

Die **mathematischen Hauptsätze** des Gesamtwerks sind nach dem vorhandenen Lean-Beweisstand und dieser Vollprüfung sachlich begründet; besonders die Dimensions-, Grenzraum- und konstruktiven Analyse-Resultate werden jetzt adäquat abgedeckt. Das Manuskript ist jedoch aufgrund der präzisen Integer-Trägerbeschreibung, des unvollständig erläuterten ungerichteten Zyklenfreiheitsarguments, anspruchsvoller noch zu glättender informeller Beweise sowie der Release-Dokumentationskonsistenz **vor Einreichung zu überarbeiten**. Es besteht **kein sachlicher Anlass**, fehlende allgemeine Vollständigkeit durch stärkere Logik oder neue Datenträger im Lean-Code zu erzwingen.
