# Vollreview der 46-seitigen Task-06-Langfassung

**Prüfdatum:** 15. Oktober 2026  
**Input:** `TASK06_FOUNDATIONS_LONGFORM_89_PROOFS.zip`  
**Referenz:** eingebetteter eingefrorener Task-06-Quellstand, Lean 4.28.0.  
**SHA-256-Quellenfingerabdruck:** `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.

## 1. Ergebnis und Geltungsbereich

**Entscheidung: ACCEPT WITH DOCUMENTARY CORRECTIONS; nicht als bereits extern referiertes Journal-Paper ausgeben.** Gegenüber der 26/27-seitigen Vorversion sind die wesentlichen mathematischen Darstellungsdefizite behoben. Für die **25 namentlich formulierten Hauptsätze** wurde keine falsche mathematische Aussage oder unterdrückte wesentliche Lean-Voraussetzung gefunden. Die **89 zusätzlich ausgezeichneten Abschnitte** wurden einzeln nach Status und Quellenzuordnung geprüft: es sind 89 mathematische Themenbehandlungen, ausdrücklich **nicht 89 neue Lean-Theoreme und auch nicht 89 ausschließlich vollständige Beweise**. Die neu ausgeschriebenen aufwendigeren Argumente sind wesentlich besser und stimmen bei den geprüften Rechen- und Auswahlkonstruktionen mit dem Code überein.

**Wesentliche Einschränkung der Evidenz:** Ich habe das vollständige Paper, alle 89 Anhangsabschnitte, alle 25 ausgezeichneten Resultate, die mathematischen Quellanker sowie die mathematischen Hauptbeweise anhand ihres tatsächlichen Codeinhalts geprüft. Ich habe die 64 mathematischen Module statisch geprüft, aber **keine neue Lean-Kernelprüfung der 3014 Konstanten durchgeführt**, da `lean`/`lake` hier nicht installiert sind. Die Aussagen „Kernel akzeptiert“ beruhen auf den mitgelieferten und fremdberichteten Release- und Replay-Protokollen. Die **Fehlerfreiheit beliebiger künftiger Interpretationen** folgt aus keinem dieser Checks. Literaturangaben und Publikationsspezifika werden getrennt beurteilt.

### Abnahmevorschlag

- **Mathematischer Gehalt der 25 Hauptresultate:** ACCEPT in der angegebenen streng qualifizierten Lesart.
- **Langform/Beweisexposition:** ACCEPT WITH MINOR REFINEMENTS; keine neue Lean-Grundlagenentwicklung nötig.
- **Archiv- und Nachweisqualität:** MINOR REPAIR vor Weitergabe als reproduzierbares Dokumentationsrelease.
- **Formaler Beweisstatus des informellen Zusatzsatzes zu unären Tripeln und −1:** separat markieren; nicht kernelgeprüft.
- **Externe Peer-Review-/Journalreife:** noch nicht bescheinigt.

## 2. Vollständigkeits- und Integritätsprüfungen

| Prüfung | Eigener Befund | Aussagekraft |
|---|---|---|
| ZIP-Inventar | 52 Dateien einschließlich des SHA-Manifests | alle ausgelieferten Dateien erfasst |
| SHA-Manifest | 51/51 Prüfwerte bestanden; das Manifest referenziert nicht sich selbst | vollständige Dateiintegrität |
| PDF | 46 Seiten, sämtliche Seiten als Bildkontaktsheets gesichtet | redaktionelle/Layout-Sichtkontrolle |
| Frische LaTeX-Kompilation | `latexmk -pdf -interaction=nonstopmode -halt-on-error`: Erfolg, wieder 46 Seiten | LaTeX-Vollständigkeit, kein Mathematikbeweis |
| 89 Zusatzabschnitte | 89 eindeutige `supp:i-j`-Labels und 89 CSV-Zeilen; kein Abschnitt fehlt | vollständige *thematische* Abdeckung |
| 25 Hauptresultate | 25/25 (11 Theoreme, 11 Propositionen, 2 Lemmata, 1 Korollar) | Satz-für-Satz-Beurteilung unten |
| Lean-Fundstellen | 252 historische + 37 Task-6 = **289/289** Deklarationsnamen stimmen auf den angegebenen Quellzeilen | Quellenzuordnung, kein erneuter Kernel-Lauf |
| Zusätzliche Quellverweise | 290 Pfad:Zeile-Vorkommnisse, 285 eindeutige Positionen; alle existieren und sind im Dateibereich | die Zählung unterscheidet Erwähnungen und Deklarationsregister |
| CSV-Quellpfade | sämtliche auslesbaren Modulpfade vorhanden | Navigation plausibel |
| TeX-Labels/Referenzen | 150 Labels; keine Dopplungen und keine ungelösten TeX-Querverweise | interne Verlinkung |
| Literatur | 10/10 BibTeX/`thebibliography`-Schlüssel verwendbar | formale Konsistenz, Inhaltsprüfung s. §6 |
| Eingebetteter Lean-Quellbaum | neu berechneter 75-Dateien-Fingerabdruck identisch | eingefrorene Basis stimmt |
| Statischer Projektcheck | PASS: 64 zugängliche mathematische Modulwurzeln/-dateien laut Prüfer | keine verbotenen Syntax-/Importmuster im Prüferumfang |
| Lean-Kernel/Build | nur aus archiviertem bzw. getrennt berichtetem Task-6-Lauf | **nicht** unabhängig neu ausgeführt |

**Aufgelistete, aber im ZIP fehlende Dateien:** `verification_report.md` verweist auf `compile.log`; `proof_correspondence.md` und `revision_acceptance.md` erwähnen `evidence/projS_inS_check.log`. Beide Pfade fehlen. Dies ändert nicht die Mathematik, schwächt aber die Reproduktions- und Belegvollständigkeit. Falls die Dateien nicht nachgeliefert werden, diese Stellen präzisieren („im Arbeitslauf vorhanden, nicht Teil des Releases“) statt einen nicht existierenden Paketinhalt zu behaupten.

## 3. Mathematische Einzelbefunde und Korrekturen

### B1 — Informell bewiesener Satz über das unäre Tripelbild (P2: formalen Status beibehalten)

**Ort:** `main.tex`, Abschnitt *Universal triple witnesses* (Zeilen ca. 178–186); `extended_proof_details.tex`, §6.3; `LEAN_PROOF_REQUIREMENTS.md`.

Für ein unäres Alphabet sind verschiedene Wörter durch unterschiedliche Längen ausgezeichnet. Die Admissibilität fordert `P₁≠P₂`, `P₁≠P₃` und `d(P₂)>d(P₃)`. Daraus folgt mit `A=d(P₁)−d(P₂)` und `D=d(P₂)−d(P₃)>0`: `A≠0` und `A≠−D`. Also sind **0 und −1** nicht darstellbar. Der zweite Ausschluss ist rechnerisch korrekt; **nur 0 ist derzeit eigens als Lean-Theorem benannt** (`TriplePath.unary_numer_ne_zero`). Die Langfassung kennzeichnet das erfreulicherweise ausdrücklich. Es darf **nicht** behauptet werden, das exakte Bild aller unären Tripelklassen sei formal charakterisiert. Wenn ein Journal oder der Masterprompt eine Kernel-Deklaration *für jede gesonderte negative mathematische Aussage* fordert, wäre ein kleiner optionaler zusätzlicher Lean-Satz sinnvoll, aber **nicht zur Rettung des Haupttheorems nötig**.

### B2 — Inversion im Haupttext präziser formulieren (P2: redaktionelle Präzisierung)

**Ort:** `main.tex`, §12.6, um Zeilen 585–599; deutlich besser in `extended_proof_details.tex`, §12.6.

Der Haupttext spricht davon, dass das termweise Produkt „nach der Verschiebung eins“ sei. Genau gelten zwei Aussagen: `(s_{N+n})·(s_{N+n})⁻¹=1` **punktweise**; das für den **unverschobenen** Repräsentanten tatsächlich verwendete Produkt `s_n·(s_{N+n})⁻¹` ist im Allgemeinen **nicht punktweise 1**, sondern lediglich äquivalent zur konstanten Einsfolge. Das Supplement beweist bereits die korrekte Abschätzung

`|s_n(s_{N+n})⁻¹−1|≤2^κ|s_n−s_{N+n}|`.

Eine bessere Haupttextformulierung wäre: „The shifted product is pointwise one; the product with the original representative is equivalent to the constant-one sequence by the Cauchy-tail estimate.“ **Kein Fehler des Lean-Beweises.**

### B3 — Konstruktive Randtrennung/Hypothesen lokal sichtbar halten (P2: Satzumfeld)

**Ort:** `main.tex`, §10.4–10.5; `extended_proof_details.tex`, §10.5; `BoundaryTopology/TopologicalObstructions.lean`.

Die explizite Zylindertrennung benötigt einen **gegebenen** Unterschiedsindex; aus `ξ≠η` gewinnt man konstruktiv nicht ohne Weiteres einen solchen Index. Die Quelle `Ray.connected_subsingleton` arbeitet unter `[DecidableEq α]` (nicht unter einem stillschweigenden globalen Entscheidbarkeitsaxiom für die Ray-Gleichheit). Der Haupttext deutet die Einschränkung korrekt an; der Zusatzabschnitt sagt nur „unter den angegebenen konstruktiven Voraussetzungen“. Für mathematische Eigenständigkeit diese lokale Bedingung ausdrücklich wiederholen. Die Kompaktheit des endlich verzweigenden Randes wurde nicht bewiesen und wird nicht behauptet.

### B4 — „89 Beweise“ als Verpackungsbezeichnung irreführend (P3: Terminologie)

89/89 **Themen** besitzen eigenständige Anhangsabschnitte. Mehrere betreffen Definitionen, Forschungsstand, Quellenkontext, bedingte Sätze, präzise negative Resultate oder offene Fragen. Aus `TASK06_FOUNDATIONS_LONGFORM_89_PROOFS.zip` darf daher nicht auf **89 formal geprüfte Sätze** geschlossen werden. Das `README.md` und `PROOF_EXPANSION_AUDIT.md` vermeiden eine solche Verwechslung bereits weitgehend; für öffentliche Releases wäre eine neutralere Bezeichnung wie `FOUNDATIONS_LONGFORM_89_TOPICS` besser.

### B5 — Zwei fehlerhafte/überholte Release-Dateiverweise (P2: beheben)

- `verification_report.md`: Verweis auf `compile.log` (fehlt).
- `proof_correspondence.md`, `revision_acceptance.md`: Verweis auf `evidence/projS_inS_check.log` (fehlt).

Im Paket enthalten sind dafür vollständige Quelldateien, 21 ältere Task-5-Logs, Task-6-Verifikationstext und Signaturregister. Die fehlenden beiden Dateien sind **kein Hinweis auf einen fehlenden mathematischen Satz**. Nachliefern oder Verweise als historische externe Artefakte kennzeichnen.

### B6 — Letzte Publikationsschritte (P3: keine mathematischen Reparaturen)

Autoren-/Institutionsangaben stehen noch als Platzhalter. Eine zitierfähige dauerhafte Quelle für den eingefrorenen Task-6-Stand (Release/DOI oder fixierter Git-Commit) wäre für eine Veröffentlichung hilfreich. Die bibliografischen Bücher sind teils nur über Verlagstable-of-contents statt durchgängige Volltextlektüre verifiziert; dies wird im Quellen-Audit korrekt begrenzt. Die Feststellung, dass keine unabhängige externe Fachbegutachtung stattgefunden hat, bleibt richtig.

### Kein bestätigter schwerer mathematischer Defekt

Ich habe insbesondere **keine falsche Ableitung von allgemeiner Vollständigkeit aus `SupData`**, **keine stillschweigende Identifikation von Algebra-Rang und topologischer Dimension**, **keine falsche Annahme, alle Baumautomorphismen seien niveauweise**, und **kein Einschleusen von MP/LPO/WLPO oder `ChoiceNN` als bewiesene globale Prinzipien** gefunden.

## 4. Alle 25 Hauptsätze: Einzelfallmatrix

Die nachfolgenden Befunde betreffen jeweils den **mathematischen Wortlaut und seine Hypothesen**; die referenzierte Kernel-Akzeptanz stammt aus dem eingefrorenen Release-Protokoll. Die Liste enthält auch die ursprünglich nur knapp behandelten Hilfsaussagen, sofern sie als eigene Sätze im Haupttext erscheinen.
| Nr. | Titel | Urteil | Mathematischer Prüfpunkt |
|---:|---|---|---|
| 01 | Unique finite root path (proposition, main.tex:56) | FORMAL GEDECKT / korrekt qualifiziert | Eindeutige *gerichtete* Wurzelkantefolge; nicht beliebige Walks. |
| 02 | Path sum equals depth (proposition, main.tex:72) | FORMAL GEDECKT / korrekt qualifiziert | Tatsächlicher Kantenfold, nicht externe Kantengewichte. |
| 03 | Natural semiring (proposition, main.tex:89) | FORMAL GEDECKT / korrekt qualifiziert | Unäres Listenzählen; die Semiring-Axiome im Code vorhanden. |
| 04 | Transitivity and positive-denominator cancellation (lemma, main.tex:140) | FORMAL GEDECKT / korrekt qualifiziert | Positiver Nenner gewährleistet Kürzbarkeit im Integritätsbereich. |
| 05 | Fraction-field algebra (proposition, main.tex:165) | FORMAL GEDECKT / korrekt qualifiziert | Unabhängige Hilfsbruchdarstellung, nicht durch Adjazenz induzierte Multiplikation. |
| 06 | Ordered-field comparison (theorem, main.tex:208) | FORMAL GEDECKT / korrekt qualifiziert | Die Tripeloperationen werden von den Hilfsbrüchen transportiert; zwei unterscheidbare Buchstaben. |
| 07 | Arity independence (corollary, main.tex:222) | FORMAL GEDECKT / korrekt qualifiziert | Geordnete Körperisomorphie; keine Gleichheit der Bäume. |
| 08 | Symmetric bilinearity of the finite coordinate form (proposition, main.tex:240) | FORMAL GEDECKT / korrekt qualifiziert | Bilinearität/Symmetrie ohne positive Arität oder Positivdefinitheit. |
| 09 | Explicit bases and ranks (theorem, main.tex:273) | FORMAL GEDECKT / korrekt qualifiziert | Explizite unabhängige Erzeuger; Rang = algebraische Basislänge. |
| 10 | Finite decomposition (theorem, main.tex:292) | FORMAL GEDECKT / korrekt qualifiziert | Direkte Summe nur bei b>0 und Charakteristik null. |
| 11 | Complementary projection operators (theorem, main.tex:308) | FORMAL GEDECKT / korrekt qualifiziert | Linearität, Idempotenz, Kern-/Bild-Identitäten; Task-6-Erweiterung. |
| 12 | Algebraic orthogonal splitting (theorem, main.tex:344) | FORMAL GEDECKT / korrekt qualifiziert | Orthogonalität ausschließlich bezüglich der ausdrücklich definierten symmetrischen Bilinearform. |
| 13 | Countable transverse basis (theorem, main.tex:380) | FORMAL GEDECKT / korrekt qualifiziert | Abzählbar freie Basis für den *endlich unterstützten* Nullsummenraum. |
| 14 | Longitudinal incompatibility for zero-padding (theorem, main.tex:392) | FORMAL GEDECKT / korrekt qualifiziert | Negative Aussage nur für Nullauffüllung und diesen algebraischen Träger. |
| 15 | Separated rays (proposition, main.tex:412) | FORMAL GEDECKT / Punkt-Hypothesen ausdrücklich beachten | Trennung setzt eine konkrete verschiedene Koordinate voraus. |
| 16 | Noncompact countable cylinders (proposition, main.tex:423) | FORMAL GEDECKT / Punkt-Hypothesen ausdrücklich beachten | Konstruktiv konkrete offene Überdeckung; betrifft ChildOmega, nicht endliche Alphabete. |
| 17 | Ray transitivity and invariant maps (proposition, main.tex:442) | FORMAL GEDECKT / korrekt qualifiziert | Levelweise Transitivität bei entscheidbarer Buchstabengleichheit; keine Gesamtklassifikation. |
| 18 | Product estimate and modulus (lemma, main.tex:498) | FORMAL GEDECKT / korrekt qualifiziert | Produktabschätzungen mit eventuellen Schranken und verschobenen Moduli. |
| 19 | Constructive Cauchy ring (proposition, main.tex:523) | FORMAL GEDECKT / korrekt qualifiziert | Quotient ist Ring mit injektiver rationaler Einbettung, nicht bedingungslos Körper. |
| 20 | Order and tight apartness (proposition, main.tex:551) | FORMAL GEDECKT / korrekt qualifiziert | Konstruktive Apartheit und schwache Ordnung; keine vollständige Trichotomie. |
| 21 | Separated inversion (theorem, main.tex:592) | FORMAL GEDECKT / Haupttext-Präzisierung B2 | Apartheitszeuge garantiert Inversion; x≠0 alleine nicht. |
| 22 | Modulated completeness characterization (theorem, main.tex:638) | FORMAL GEDECKT / bedingte oder einseitige Form exakt beibehalten | Modulierte Folgen; Äquivalenz mit gelieferten Approximationsdaten. |
| 23 | Suprema from data (theorem, main.tex:658) | FORMAL GEDECKT / bedingte oder einseitige Form exakt beibehalten | SupData trägt die notwendigen rationalen oberen und erreichbaren Schranken. |
| 24 | Logical equivalences; conditional form (theorem, main.tex:710) | FORMAL GEDECKT / bedingte oder einseitige Form exakt beibehalten | MP/LPO/WLPO sind exakt als Propositionen formuliert, nicht als Axiome eingeschleust. |
| 25 | One-way logical lower bounds (proposition, main.tex:731) | FORMAL GEDECKT / bedingte oder einseitige Form exakt beibehalten | Nur Implikationen UnrestrictedLUB⇒WLPO und BMC⇒LPO; keine Umkehrung. |

## 5. Alle 89 Gliederungspunkte: Einzelabgleich

Die Bewertung „behandelt“ besagt: Definition, Beweisidee, Folgerung oder Status stehen explizit und sachlich qualifiziert im Anhang. **Sie besagt nicht**: ein eigener Kernel-Satz ist vorhanden. Die Originalpfade aus `scope_89.csv` wurden alle auf Existenz geprüft. Mehrere Einträge haben naturgemäß keinen eigenen Source-Anker, weil sie Interpretationen und Grenzen bündeln.

### 1. Wissenschaftlicher Rahmen und Definitionen (4 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 1.1 | Mathematical objects and construction order | Einordnung/Definition/offene Grenze | 27 | — |
| 1.2 | Related established mathematical frameworks | Einordnung/Definition/offene Grenze | 27 | — |
| 1.3 | Main theorems and their scope | Einordnung/Definition/offene Grenze | 27 | — |
| 1.4 | Logical framework and interpretative scope | Einordnung/Definition/offene Grenze | 28 | — |

### 2. Wortbäume und Inzidenz (6 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 2.1 | Alphabets, finite words, root, and directed edges | Beweis/abgeleiteter Befund | 28 | `PrimitiveTree/FiniteWords.lean` |
| 2.2 | Unique parent and unique finite root path | Beweis/abgeleiteter Befund | 28 | `PrimitiveTree/FiniteWords.lean` |
| 2.3 | Connectedness, absence of cycles, and infinite depth | Beweis/abgeleiteter Befund | 28 | `PrimitiveTree/FiniteWords.lean` |
| 2.4 | Finite arity as a derived indexing object | Beweis/abgeleiteter Befund | 28 | `PrimitiveTree/FiniteChild.lean, TreeNumbers/PathNaturals.lean` |
| 2.5 | The countably branching tree | Beweis/abgeleiteter Befund | 28 | `TreeFoundation/OmegaTree.lean` |
| 2.6 | Inclusions and the directed arity union | Beweis/abgeleiteter Befund | 29 | `TreeFoundation/ArityEmbeddings.lean` |

### 3. Pfadsummen und Ray-Präfixe (3 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 3.1 | Unit contribution and literal finite edge sum | Beweis/abgeleiteter Befund | 29 | `PrimitiveTree/RootEdges.lean` |
| 3.2 | Equality of unit-edge sum and depth | Beweis/abgeleiteter Befund | 29 | `PrimitiveTree/RootEdges.lean` |
| 3.3 | The unbounded path-count sequence along each ray | Beweis/abgeleiteter Befund | 29 | `TreeFoundation/InfiniteRays.lean, TreeAnalysis/PrimitiveDataScope.lean` |

### 4. Unäre natürliche Zahlen (4 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 4.1 | Unary paths as natural-count carrier | Beweis/abgeleiteter Befund | 29 | `PrimitiveTree/UnaryPaths.lean, TreeNumbers/PathNaturals.lean` |
| 4.2 | Addition and multiplication from word operations | Beweis/abgeleiteter Befund | 29 | `TreeNumbers/PathNaturals.lean` |
| 4.3 | Induction, recursion, order, and cancellation | Beweis/abgeleiteter Befund | 30 | `TreeNumbers/FoundationsLedger.lean, TreeNumbers/PathOrder.lean` |
| 4.4 | Equal-depth quotient for arbitrary nonempty alphabets | Beweis/abgeleiteter Befund | 30 | `TreeNumbers/DepthQuotient.lean` |

### 5. Normalisierte ganze Zahlen (4 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 5.1 | Oriented pairs of nonnegative path counts | Beweis/abgeleiteter Befund | 30 | `TreeNumbers/PathIntegers.lean` |
| 5.2 | Normal forms and equivalence classes | Beweis/abgeleiteter Befund | 30 | `TreeNumbers/PathIntegers.lean` |
| 5.3 | Ring laws and absence of zero divisors | Beweis/abgeleiteter Befund | 30 | `TreeNumbers/PathIntegers.lean` |
| 5.4 | Order and canonical embedding of natural counts | Beweis/abgeleiteter Befund | 31 | `TreeNumbers/PathOrder.lean, TreeNumbers/FoundationsLedger.lean, TreeNumbers/PathI…` |

### 6. Rationale Tripel/Feld (7 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 6.1 | Valid configurations and the positive gap | Beweis/abgeleiteter Befund | 31 | `TreeNumbers/PathTriples.lean` |
| 6.2 | Equivalence by cross multiplication | Beweis/abgeleiteter Befund | 31 | `TreeNumbers/PathTriples.lean, TreeNumbers/PathFractions.lean` |
| 6.3 | Universal representatives using two distinct child symbols | Beweis/abgeleiteter Befund | 31 | `TreeNumbers/PathTriples.lean, TreeNumbers/FoundationsLedger.lean` |
| 6.4 | Field operations and all field laws | Beweis/abgeleiteter Befund | 31 | `TreeNumbers/PathRationalField.lean, TreeNumbers/PathFractions.lean, TreeAnalysis/…` |
| 6.5 | Ordering and Archimedean structure | Beweis/abgeleiteter Befund | 32 | `TreeAnalysis/RationalOrder.lean, TreeAnalysis/DyadicPrecision.lean` |
| 6.6 | Identification with internally defined fractions | Beweis/abgeleiteter Befund | 32 | `TreeAnalysis/FractionCharacterization.lean` |
| 6.7 | What branching contributes to this representation | Beweis/abgeleiteter Befund | 32 | `TreeAnalysis/FractionCharacterization.lean, TreeNumbers/FoundationsLedger.lean` |

### 7. Geordnete Isomorphismen verschiedener Alphabettypen (3 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 7.1 | Canonical algebraic comparisons across finite arities | Beweis/abgeleiteter Befund | 32 | `TreeNumbers/RationalArityIndependence.lean, TreeNumbers/FoundationsLedger.lean` |
| 7.2 | Compatibility and uniqueness | Beweis/abgeleiteter Befund | 32 | `TreeAnalysis/Canonicity.lean, TreeNumbers/FoundationsLedger.lean` |
| 7.3 | Representation versus primitive structure | Beweis/abgeleiteter Befund | 33 | — |

### 8. Endliche Kinderkoordinatenräume (9 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 8.1 | Coordinate module and algebraic operations | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/FiniteChildModule.lean` |
| 8.2 | Coordinate sum and canonical bilinear form | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/FiniteChildModule.lean, DimensionFoundation/FiniteSums.lean, …` |
| 8.3 | Uniform line and zero-sum submodule | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/FiniteChildModule.lean` |
| 8.4 | Orthogonality relative to the chosen bilinear form | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/FiniteChildModule.lean, DimensionFoundation/ProjectionLaws.lean` |
| 8.5 | Explicit basis of the uniform line | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/TransverseBasis.lean, DimensionFoundation/Instances.lean` |
| 8.6 | Basis of the zero-sum submodule | Beweis/abgeleiteter Befund | 33 | `DimensionFoundation/TransverseBasis.lean` |
| 8.7 | Explicit projection and direct-sum theorem | Beweis/abgeleiteter Befund | 34 | `DimensionFoundation/TransverseBasis.lean, DimensionFoundation/Instances.lean, Dim…` |
| 8.8 | Exceptional unary case and permutation invariance | Beweis/abgeleiteter Befund | 34 | `DimensionFoundation/TransverseBasis.lean` |
| 8.9 | Interpretation of `b−1` | Einordnung/Definition/offene Grenze | 34 | — |

### 9. Abzählbare algebraische Koordinaten (5 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 9.1 | Finite-support sequences and the zero-sum condition | Beweis/abgeleiteter Befund | 34 | `DimensionFoundation/OmegaFiniteSupport.lean` |
| 9.2 | A countable explicit basis | Beweis/abgeleiteter Befund | 34 | `DimensionFoundation/OmegaFiniteSupport.lean, DimensionFoundation/Instances.lean` |
| 9.3 | Canonical compatible inclusions | Beweis/abgeleiteter Befund | 34 | `DimensionFoundation/OmegaFiniteSupport.lean` |
| 9.4 | Failure of the uniform line under zero-padding | Beweis/abgeleiteter Befund | 35 | `DimensionFoundation/BoundaryLongitudinal.lean` |
| 9.5 | Precise scope of the omega result | Einordnung/Definition/offene Grenze | 35 | — |

### 10. Strahlenrand und Präfixtopologie (8 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 10.1 | Rays as infinite sequences and coherent prefixes | Beweis/abgeleiteter Befund | 35 | `TreeFoundation/InfiniteRays.lean` |
| 10.2 | Boundary and arity union do not commute | Beweis/abgeleiteter Befund | 35 | `TreeFoundation/InfiniteRays.lean` |
| 10.3 | Cylinders and prefix incidence | Beweis/abgeleiteter Befund | 35 | `BoundaryTopology/Cylinders.lean` |
| 10.4 | Clopen cylinder basis and point separation | Beweis/abgeleiteter Befund | 35 | `BoundaryTopology/PrefixTopology.lean` |
| 10.5 | Connected subsets and isolated points | Beweis/abgeleiteter Befund | 36 | `BoundaryTopology/TopologicalObstructions.lean` |
| 10.6 | Countable arity and local compactness | Beweis/abgeleiteter Befund | 36 | `BoundaryTopology/TopologicalObstructions.lean` |
| 10.7 | Exact status of manifold statements | Bedingter Satz | 36 | `BoundaryTopology/ManifoldConditions.lean` |
| 10.8 | Optional numerical encodings are noncanonical | Einordnung/Definition/offene Grenze | 36 | `BoundaryTopology/BinaryEncoding.lean, TreeAnalysis/PrimitiveDataScope.lean` |

### 11. Automorphismen (4 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 11.1 | Levelwise child permutations and induced tree automorphisms | Beweis/abgeleiteter Befund | 36 | `TreeFoundation/RayAutomorphism.lean` |
| 11.2 | Explicit transitive action on rays | Beweis/abgeleiteter Befund | 37 | `TreeFoundation/RayAutomorphism.lean` |
| 11.3 | Invariant ray maps are constant | Beweis/abgeleiteter Befund | 37 | `TreeFoundation/RayAutomorphism.lean` |
| 11.4 | General automorphisms are more numerous | Beweis/abgeleiteter Befund | 37 | `TreeFoundation/AutomorphismCounterexample.lean` |

### 12. Rationaler Cauchy-Quotient (7 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 12.1 | Choice of base field and internally derived precision | Beweis/abgeleiteter Befund | 37 | `TreeAnalysis/OrderedField.lean, TreeAnalysis/DyadicPrecision.lean` |
| 12.2 | Rational Cauchy sequences with explicit modulus | Beweis/abgeleiteter Befund | 37 | `TreeAnalysis/CauchyData.lean` |
| 12.3 | Equivalence relation, regularization and quotient carrier | Beweis/abgeleiteter Befund | 37 | `TreeAnalysis/CauchyData.lean, TreeAnalysis/RealQuotient.lean` |
| 12.4 | Commutative ring laws and rational embedding | Beweis/abgeleiteter Befund | 38 | `TreeAnalysis/RealQuotient.lean` |
| 12.5 | Positive cone, weak order, strict order and apartness | Beweis/abgeleiteter Befund | 38 | `TreeAnalysis/RealOrderApartness.lean` |
| 12.6 | Separated inversion versus ordinary non-equality | Bedingter Satz | 38 | `TreeAnalysis/RealOrderApartness.lean, TreeAnalysis/ApartnessStrength.lean` |
| 12.7 | Density, Archimedean control, arity transfer | Einordnung/Definition/offene Grenze | 39 | `TreeAnalysis/CompletenessScope.lean, TreeAnalysis/ArityCompletionTransfer.lean, T…` |

### 13. Konvergenz und Vollständigkeit (7 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 13.1 | Convergence of embedded rational Cauchy sequences | Beweis/abgeleiteter Befund | 39 | `TreeAnalysis/CompletenessScope.lean` |
| 13.2 | Tracked real Cauchy sequences and the diagonal theorem | Beweis/abgeleiteter Befund | 39 | `TreeAnalysis/CompletenessStrength.lean, TreeAnalysis/CompletenessScope.lean` |
| 13.3 | Closure of tracked families under finite expressions | Beweis/abgeleiteter Befund | 39 | `TreeAnalysis/ApproxClosure.lean, TreeAnalysis/TrackedExpressions.lean` |
| 13.4 | Unrestricted modulated completeness and Cauchy approximation | Bedingter Satz | 40 | `TreeAnalysis/LiftingPrinciples.lean` |
| 13.5 | Choice principles and modulus-free completeness | Bedingter Satz | 40 | `TreeAnalysis/LiftingPrinciples.lean` |
| 13.6 | Least upper bounds with explicit approximation data | Bedingter Satz | 40 | `TreeAnalysis/SupremumScope.lean` |
| 13.7 | Continuation of uniformly continuous maps | Bedingter Satz | 41 | `TreeAnalysis/CompletionCharacterization.lean` |

### 14. Logische Prinzipien (5 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 14.1 | Markov principle and inverse existence | Bedingter Satz | 41 | `TreeAnalysis/ApartnessStrength.lean` |
| 14.2 | LPO and real trichotomy / zero-versus-apartness | Bedingter Satz | 41 | `TreeAnalysis/ApartnessStrength.lean, TreeAnalysis/FoundationsClosure.lean` |
| 14.3 | WLPO and decidable zero | Bedingter Satz | 41 | `TreeAnalysis/FoundationsClosure.lean` |
| 14.4 | Logical lower bounds for global Suprema and monotone convergence | Bedingter Satz | 41 | `TreeAnalysis/SupremumScope.lean` |
| 14.5 | What “constructive” establishes and does not establish | Einordnung/Definition/offene Grenze | 42 | — |

### 15. Strukturvergleiche (4 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 15.1 | Same arithmetic field, different finite child-space ranks | Beweis/abgeleiteter Befund | 42 | — |
| 15.2 | Primitive path counts do not distinguish rays | Beweis/abgeleiteter Befund | 42 | — |
| 15.3 | Boundary, algebraic direct limit, and numerical completion | Einordnung/Definition/offene Grenze | 42 | — |
| 15.4 | Root and endpoint levels | Einordnung/Definition/offene Grenze | 42 | `TreeFoundation/ExtendedLevels.lean` |

### 16. Grenzen/offene Fragen (7 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 16.1 | Algebraic universal properties | Einordnung/Definition/offene Grenze | 43 | — |
| 16.2 | Cauchy completeness without supplied representatives/moduli | Einordnung/Definition/offene Grenze | 43 | — |
| 16.3 | Strong classical real-field and order axioms | Einordnung/Definition/offene Grenze | 43 | — |
| 16.4 | Infinite-line compatibility obstruction | Einordnung/Definition/offene Grenze | 43 | — |
| 16.5 | Boundary-topological limits and missing conditions | Einordnung/Definition/offene Grenze | 43 | — |
| 16.6 | Full automorphism classification | Einordnung/Definition/offene Grenze | 43 | — |
| 16.7 | Systematic separation of statuses | Einordnung/Definition/offene Grenze | 44 | — |

### 17. Schlussfolgerungen (2 Unterpunkte)
| Gliederung | Gegenstand | Status / Art | PDF-Seite | Quellanker |
|---|---|---|---:|---|
| 17.1 | Statements established under the exact hypotheses | Einordnung/Definition/offene Grenze | 44 | — |
| 17.2 | Delineation of open properties | Einordnung/Definition/offene Grenze | 44 | — |

## 6. Konkrete Nachprüfung der nichttrivialen Beweisketten

| Thema | Im Anhang tatsächlich dargelegte Mechanik | Vergleich mit Task-6-Code | Ergebnis |
|---|---|---|---|
| Ungerichtete Zyklenfreiheit | Jede Elternkante ist eine Schnittkante zwischen Nachkommengebiet und Restbaum; geschlossener kantenverschiedener Weg unmöglich | `PrimitiveTree/FiniteWords.lean`, `Word.no_cycle` | korrekt; früherer Darstellungsfehler behoben |
| Normalisierte Ganze | Quotient der Rohpaare nur als mathematische Äquivalenz; Carrier sind eindeutige Normalpaare | `TreeNumbers/PathIntegers.lean`, `mkZ_sound`, `mkZ_exact` | korrekt; früherer Typfehler im Paper behoben |
| Bruchrelation | Kreuzmultiplikation plus Kürzung positiver Zwischennenner, Kongruenz beider Argumente | `TreeNumbers/PathFractions.lean` | korrekt |
| Drei Pfade | Explizite Wortmuster `a0^(p+2+D)`, `a1^(q+2+D)`, `a0::a1^(q+1)` | `TreeNumbers/PathTriples.lean`, `wP1/wP2/wP3`, `witness_numer`, `witness_denom` | die konkreten Längen und Paarverschiedenheiten stimmen |
| Feldstruktur auf Tripeln | Transport über Hilfsbruchträger, nicht neu aus Adjazenz gegeben | `TreeNumbers/PathRationalField.lean`, `TreeAnalysis/FractionCharacterization.lean` | korrekt differenziert |
| Rang b−1 | Explizite `e_j−e_0`-Basis, Unabhängigkeit durch Koordinatenvergleich, Erzeugung durch Nullsummengleichung | `DimensionFoundation/TransverseBasis.lean` | korrekt; reine algebraische Dimension |
| Projektionsalgebra | `P_L=(1/b)σ_b u_b`, `P_S=I-P_L`, idempotente und komplementäre Abbildungen; Kern/Bild | `DimensionFoundation/BilinearForm.lean`, `ProjectionLaws.lean` | korrekt, benötigt b>0 bei Zerlegungsresultaten |
| Orthogonalität | Summe der Komponenten, Bilinearität und Wegfall der beiden Kreuzterme | `DimensionFoundation/ProjectionLaws.lean`, `dot_split` | korrekt, keine Positivdefinitheit |
| Omega-Transversalraum | Endlich unterstützte Folgen, Basis `e_{i+1}−e_0`, Summennull-Bedingung | `DimensionFoundation/OmegaFiniteSupport.lean` | korrekt, keine unendliche Summationsannahme |
| Longitudinal-Obstruktion | Altkoordinate 1 vs. neue Auffüllkoordinate 0 in der nächsten Arität | `DimensionFoundation/BoundaryLongitudinal.lean` | korrekt; keine universale Negation anderer Umgebungsräume |
| Countable noncompact | Überdeckung eines Zylinders durch alle nächsten Buchstaben, endliche Auswahl durch Maximalindex widerlegt | `BoundaryTopology/TopologicalObstructions.lean`, `cyl_not_compact` | korrekt; ausdrücklich nur omega |
| Nicht-Lokalkompaktheit | Abgeschlossenes Zylinder-Teilset einer hypothetisch kompakten Umgebung, endliche Subüberdeckung würde folgen | `Ray.compact_cyl_of_sub`, `not_locallyCompactAt` | korrekt |
| Transitive Automorphismen | Pro Ebene Vertauschung der beiden Ray-Zeichen; umkehrbare Bijektion | `TreeFoundation/RayAutomorphism.lean` | korrekt bei `DecidableEq` |
| Nicht-niveauweiser Automorphismus | Vertauscht Zweige nur unter einem bestimmten Elternwort | `TreeFoundation/AutomorphismCounterexample.lean` | korrekt, Gegenbeispiel zu behaupteter Vollständigkeit |
| Cauchy-Produkt | Eventuelle Schranken `2^A,2^B`; Präzisionen `k+1+B`,`k+1+A` | `TreeAnalysis/CauchyOps.lean`, `RealQuotient.lean` | korrektes Fehlerbudget |
| Inversion | `t_n=(s_{N+n})^{-1}`, Modul `μ_s(j+2κ)`, asymptotisches Produkt mit ursprünglichem `s` | `TreeAnalysis/CauchyOps.lean:220–281` | **Anhang korrekt**, Haupttext B2 präzisieren |
| Diagonal-Limit | Eine einzige `q : N→K`, `M`; `λ(k)=max(ν(k+2),M(k+2))` | `TreeAnalysis/CompletenessStrength.lean`, `approxMod`/`approxSeq`/`limit_of_approx` | exakt am Source orientiert |
| Umkehrung UC⇒CA | Ein Repräsentant des *einen* Grenzwerts, `q_i=approxAt(c,i)` und `M(k)=max(ν(k+1),k+1)` | `TreeAnalysis/LiftingPrinciples.lean` | korrekt; keine abzählbare Auswahl versteckt |
| Daten-Suprema | `u_k` rationale Obergrenze und `s_k∈S` fast erreichbar; Regularität der Obergrenzen | `TreeAnalysis/SupremumScope.lean`, `SupData` | korrekt; nicht allgemeine LUB |
| MP/LPO/WLPO | Bool-Kodierung und endliche rationelle Abstandstests, Quotient mit enger Null-/Apartheits-Logik | `TreeAnalysis/ApartnessStrength.lean`, `FoundationsClosure.lean` | korrekt bedingte Prinzipien |
| WLPO/LPO-Untergrenzen | Schranken mit `1/4`,`1/2`,`1/8` an LUB bzw. monotone Grenzfolge | `TreeAnalysis/SupremumScope.lean` | nur die bewiesenen Implikationen |

**Sorgfaltsgrenze:** „stimmt mit dem Code überein“ bedeutet hier Definitionen, Hypothesen, angegebene Zwischenidentitäten und relevante Proof-Bodies gegengeprüft; es ist **keine eigene vollständige formale Re-Elaboration jeder Hilfsaussage**.

## 7. Wissenschaftliche Grenzen: Statuskontrolle

1. **Allgemeine Folgenvollständigkeit:** für reale Sequenzen mit *geliefertem* Cauchy-Modul äquivalent zu `CauchyApprox`, unter `ChoiceNN` bewiesen. Ohne Voraussetzung weiterhin nicht bedingungslos bewiesen.
2. **Modulusfreie Vollständigkeit:** nur unter zusätzlichem Modulus-/Auswahlprinzip; keine Umkehrung zu `ChoiceNN` belegt.
3. **Inversion aus `x≠0`:** äquivalent zum projektinternen Boolean-Markov-Prinzip; nur Inversion bei Apartheit ist unbedingt vorhanden.
4. **Trichotomie und `ZeroOrApart`:** genau mit LPO verknüpft, nicht global konstruiert.
5. **Entscheidbarkeit von null:** an WLPO gekoppelt; nicht als automatisch gegeben dargestellt.
6. **Unbeschränkte LUB / monotone Konvergenz:** nur einzelne Implikationen `⇒WLPO` bzw. `⇒LPO`; Suprema mit `SupData` gesichert.
7. **Alternative omega-Längsrichtung:** Träger/Einbettungen unbestimmt; nur Scheitern der konkret verwendeten Nullauffüllungen bewiesen.
8. **Kompaktheit endlicher Ray-Grenzen:** nicht als Task-6-Satz formalisiert; omega-Zylinder hingegen formal nichtkompakt.
9. **Mannigfaltigkeitskarten in reelle Linie:** nur unter `IntervalsConnected K`; keine beliebige positive geometrische Dimension ausgeschlossen.
10. **Automorphismen:** Transitivität niveauweiser Aktion bewiesen, vollständige Klassifikation offen, gegenteilige Levelwise-Behauptung widerlegt.
11. **Baumrand vs. Zahlenquotient:** keine kanonische topologische Identifikation; das ist nicht automatisch ein allgemeines Nichtexistenztheorem.
12. **Universelle Eigenschaften:** spezifische Isomorphismen und Selbstabbildungserweiterungen reichen nicht für allgemeine universelle Eigenschaften sämtlicher Carriers.
13. **Algebraischer Rang:** b−1 ist der bewiesene Rang des Nullsummenkoordinatenmoduls und ausdrücklich **keine** physikalische, Hausdorff- oder topologische Dimension des Baums.

## 8. Primärliteratur und redaktionelle Reproduzierbarkeit

Im Text sind alle zehn Schlüssel aus `references.tex` benutzt und definiert; die parallele Datei `references.bib` ist kein tatsächlich verwendeter BibTeX-Buildschritt. Primärreferenzen werden als **etablierter fachlicher Kontext** verwendet, nicht als Ersatz für Lean- oder mathematische Beweise. Unabhängig online plausibilisiert wurden u. a. Axler, *Linear Algebra Done Right* (4. Aufl., Bilinearformen §9A), Lubarsky, *On the Cauchy completeness…* (MLQ 53 (2007), 396–414), und Gilbert, *Formalising Real Numbers in Homotopy Type Theory*; die wissenschaftliche Darstellung beansprucht **keine** Unabhängigkeit für die konkrete Task-6-Logik allein aufgrund dieser externen Arbeiten. Das bestehende `PRIMARY_SOURCE_AUDIT.md` dokumentiert die Grenzen der zugänglichen Monographien richtig.

Die Datei `revision_acceptance.md` stammt aus einem früheren Dokumentationspass. Sie beschreibt M18 noch als nur teilweise geheilt, weil sie die kompakte Hauptfassung betrachtet; die neue 89-Themen-Ergänzung sollte als weiterer Nachtrag mit endgültiger Langform-Bilanz erfasst werden. Der Release-Helfer `REPRODUCE_RELEASE.sh` erklärt korrekt den Workaround für verlorene TAR-Ausführungsbits. Der aktuelle Manuskript-Check liefert **keinen** zusätzlichen Kernel-Verifikationslauf; dieser darf auch künftig nicht impliziert werden.

## 9. Konkreter Korrekturauftrag für den Dokumentationschat

**Keine neuen primitiven Strukturen, kein verpflichtender Task 07.** Der nächste Durchlauf soll nur:

1. Die fehlenden Nachweispfade `compile.log` und `evidence/projS_inS_check.log` entweder **mit exakt den gemeinten Daten** ergänzen oder entsprechende Dateiverweise berichtigen.
2. Die Formulierung zur Inversion im Haupttext exakt zwischen *punktweiser Identität der verschobenen Folge* und *asymptotischer Äquivalenz für den ursprünglichen Vertreter* unterscheiden.
3. Die `[DecidableEq A]`-Voraussetzung beim `connected_subsingleton`-Argument in der mathematischen Prosa lokal explizit machen.
4. Den informell bewiesenen Ausschluss des unären Wertes `−1` in Zusammenfassung, Korrespondenz und ggf. Versionsnotiz eindeutig als **nicht separat kernelgeprüften Zusatzschluss** markieren (bereits weitgehend korrekt).
5. Das Release nicht als „89 Lean-Proofs“, sondern „89 mathematisch behandelte Gliederungspunkte“ bezeichnen und die Akzeptanztabellen auf die 46-seitige Langfassung aktualisieren.
6. Die LaTeX-Fassung neu bauen und Manifest/SHA-Werte anschließend erneut aus den unveränderten Lean-Quellen und den korrigierten Dokumentationsdateien erzeugen.

## 10. Schlussurteil

Die jetzige Fassung ist **inhaltlich erheblich besser** als die frühere kompakte Darstellung: Die Mathematisierung der 89 Gliederungspunkte, die Quellen-Korrespondenz und die konstruktiven Fehlerabschätzungen sind tatsächlich ergänzt. Es gibt **keinen nachgewiesenen Sachfehler unter den 25 Hauptresultaten** und keinen gefundenen Grund, die Lean-Grundlagen erneut zu öffnen. Die abweichenden Nachweispfade und die kleinen Formulierungsfragen sind vor einem wissenschaftlichen Repository-Release zu beheben. Für eine **externe mathematische Fachbegutachtung** ist die Langfassung nun geeignet; eine formale *Einreichungsreife* oder externe Begutachtung wird damit nicht vorweggenommen.

