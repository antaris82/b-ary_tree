# Redaktionsauftrag nach vollständigem Task-6-Paper-Review

## Verbindliche Quelle

Manuskript aus `TASK06_FOUNDATION_CRITICAL_REVIEW.zip` und unveränderter Task-6-Quellstand (`output-final_aristotle`, Lean 4.28.0, Fingerabdruck `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`). Ausführlicher Befund: `TASK06_VOLLREVIEW_DOKUPAKET_2026-10-15.md`. Das Ziel ist die Überarbeitung der **mathematischen Darstellung**, nicht ein neuer numerischer oder logischer Formalisierungsstrang.

1. `main.tex` §5, Zeilen 102–115: Ersetze „Quotient classes form Z“ durch die tatsächliche Konstruktion als eindeutig normalisierte Paare. Beweise/expliziere die exakte Relation zu den Äquivalenzklassen durch `mkZ_sound` und `mkZ_exact`. Bewahre die normierten Paarformeln.
2. `main.tex` §2, Zeilen 63–65: Ergänze einen vollständigen informellen Beweis der **ungerichteten** Zyklenfreiheit des Wortbaums, gestützt auf `Word.no_cycle` und die Unterbaum-Brückenkanten. Keine nur gerichtete Zyklenfreiheit als Ersatz.
3. Ergänze diejenigen mathematischen Zwischenlemmata, die für Quotientenverträglichkeit, Ordnung, Apartheitsinversion, Produktmoduli, Diagonallimit, SupData und MP/LPO/WLPO-Kodierungen notwendig sind, ohne explizit dargelegte Voraussetzungen zu löschen. Quellenzeiger gehören sekundär in `proof_correspondence.md`.
4. Erzeuge eine aktuelle 25-Satz-Matrix (11 Theoreme, 11 Propositionen, 2 Lemmata, 1 Korollar) mit jeder tatsächlichen Paper-Satzformulierung, detaillierter Beweiskette, Lean-Name, Präzision der Voraussetzungen und Status. Ordne alle 66 Manuskript-Unterabschnitte und 89 Plan-Unterthemen zu. Prüfe alle 289 bisherigen Quellverweise auf fortbestehende Korrektheit.
5. Aktualisiere `open_questions.md` und entferne den Link auf die nicht beigefügte `MATHEMATICAL_ARGUMENTS_ADDED.md`. Unterscheide **bewiesen / bedingt bewiesen / formal widerlegt / offen / nicht formalisiert**. `MATHEMATICAL_PROOF_AUDIT.md` ist nur ein 24-Claims-Spot-Audit; nicht als vollständigen Beweis-Audit ausgeben.
6. Ergänze ein vollständiges Publikationsmanifest, das den eingefrorenen Quellstand, Dateihashes, Release-URL oder beigefügtes Archiv, Lean/Lake-Version, Auditprotokolle und die tatsächlich unabhängig ausgeführten Prüfungen präzise angibt. Unterscheide berichteten Kernel-Lauf von selbst ausgeführtem Kernel-Lauf.
7. Lass alle mathematisch korrekten Hauptaussagen, insbesondere Dimensionssätze, Omega-Transversalbasis, nichtkompakte Omega-Randzylinder, Automorphismen-No-go sowie konstruktive reelle Grenzen unverändert. Vermeide Positivdefinitheit, geometrische Dimension, ungeprüfte Dedekind-Vollständigkeit, heimliche Markov-/LPO-/WLPO-/Choice-Annahmen.
8. Erzeuge ein neues PDF und prüfe Satznummerierung, Formelnotation, Tabelle aller 25 Hauptresultate, Bibliografielinks, Crosswalk und Anhang. Kein neuer Lean-Task, solange keine tatsächlich falsche formal beweisbare Aussage nachgewiesen wird.

**Erforderliche Ausgabe:** überarbeitetes mathematisches Manuskript, PDF, aktuelle `proof_correspondence.md`, `open_questions.md`, `verification_report.md`, Quellenmanifest und detaillierte Änderungsübersicht. Kein Projektchronik- oder Code-Review-Stil im mathematischen Haupttext.
