# Nacharbeit für den Dokumentationschat – Task-06-Langfassung (15.10.2026)

**Ausgangsstand:** `TASK06_FOUNDATIONS_LONGFORM_89_PROOFS.zip`, 46 Seiten, 25 hervorgehobene Resultate, 89 eigenständig referenzierbare Themenabschnitte, eingefrorener Task-06-Lean-Quellstand, Fingerabdruck `7e12641454b9d2e387eee0c034d02f834836829c2e7d2926da5e8f63554b0b7e`.

## Verbindliche kleine Korrekturen

1. **Reziproke Cauchy-Folge:** In `main.tex`, §12.6, unterscheiden zwischen dem *verschobenen* punktweisen Produkt `s_(N+n) · (s_(N+n))⁻¹ = 1` und dem tatsächlich mit der ursprünglichen Folge gebildeten Produkt `s_n · (s_(N+n))⁻¹`, das nur asymptotisch äquivalent zur konstanten Einsfolge ist. Die mathematische Abschätzung steht bereits richtig im Anhang. Keine Änderung der Konstruktion oder der Lean-Sätze.
2. **Konstruktive Randtrennung:** In §10.4–10.5 und dem korrespondierenden Beweisanhang alle erforderlichen Bedingungen lokal angeben, insbesondere einen expliziten Trennindex bzw. die tatsächliche `[DecidableEq α]`-Voraussetzung des einschlägigen Lean-Satzes. Keine konstruktiv unzulässige Schlussfolgerung `ξ ≠ η ⇒ ∃ n, ξ(n) ≠ η(n)` ohne zusätzliche Voraussetzung.
3. **Unäre Tripel:** Die informell hergeleitete Nichtdarstellbarkeit von `−1` ist mathematisch plausibel und im Manuskript als **nicht gesondert kernelgeprüfter Nebenbefund** zu kennzeichnen. Nur die Nichtdarstellbarkeit von `0` hat derzeit einen eigenen benannten Lean-Beweis. Keine behauptete vollständige Bildklassifikation; ein kleiner neuer Lean-Beweis ist optional, nicht Voraussetzung der 25 Hauptresultate.
4. **Provenienz-Artefakte:** `verification_report.md` verweist auf das im ZIP fehlende `compile.log`; `proof_correspondence.md` und `revision_acceptance.md` auf das fehlende `evidence/projS_inS_check.log`. Entweder die tatsächlich vorhandenen Originalprotokolle nachliefern und ins Hashmanifest aufnehmen oder diese Referenzen ausdrücklich als *nicht im Release enthaltene historische Arbeitsartefakte* korrigieren. Keine Protokolle erfinden.
5. **89-Themen-Kennzeichnung:** 89 Abschnitte sind nicht 89 neue oder separat kernelgeprüfte Theoreme. Den Release-Namen und eine mögliche öffentliche Beschreibung von „89 proofs“ auf „89 topics“ oder „89 mathematical treatments“ ändern.
6. **Aktuellen Status konsolidieren:** Historisch offene Punkte in `revision_acceptance.md` gegen die neuen Anhangsbeweise aktualisieren; Autorenplatzhalter für eine spätere Einreichung ersetzen. Keine neuen Axiome, keine Erweiterung der Zahlengrundlagen.

## Nicht verändern

- Die 25 formal gedeckten Hauptresultate, ihre präzisen Voraussetzungen und die vorhandene Paper–Lean-Korrespondenz (289 Anker) unverändert lassen, sofern die redaktionellen Anpassungen keine Nummerierung ändern.
- Algebraische Dimension niemals als geometrische/topologische/physikalische Dimension behandeln.
- Die konstruktiven Grenzen bei `TreeR` (MP, LPO, WLPO, ChoiceNN, `SupData`, `IntervalsConnected`) und das Scheitern der longitudinalen Nullergänzung unverändert qualifizieren.
- Kein neuer Lean-Task zur Reparatur des Beweiskerns erforderlich.

## Abschlusschecks

`latexmk` erfolgreich; genau die aktualisierte LaTeX-Fassung und das PDF ausliefern; sämtliche 89 Abschnittsanker/Querverweise und 25 Hauptsätze erneut zählen; Proof-Correspondence und SHA-Manifest für alle vorhandenen Artefakte prüfen; dokumentieren, ob Lean-Build und Kernelprüfung selbst erneut durchgeführt oder nur vom eingefrorenen Task-06-Release übernommen wurden.

**Grundlage:** [Vollständiger Reviewbericht](sandbox:/mnt/data/TASK06_LANGFASSUNG_VOLLREVIEW_2026-10-15.md).
