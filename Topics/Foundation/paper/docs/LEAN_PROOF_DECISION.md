# Lean-Beweisbedarf — Entscheidung aus beiden Reviews

## A. Zwingend neue Lean-Beweise für die bereits geprüften Task-06-Hauptsätze

**Keine nachgewiesen.** Das ist ein *Befund aus zwei Reviews und Stichproben gegen den Originalquelltext*, keine metamathematische Garantie, dass kein künftiges Problem existiert.

Die wichtigen vorhandenen Lean-Beweise: `TreeZ.mkZ_sound`, `TreeZ.mkZ_exact`, `FracQ.instTField`, `TreeQ.orderedFieldIsoFracQ`, `Word.no_cycle`, `TreeQ.transfer_le`, `Ray.cyl_compl_open`, `ChildModule.dot_bilinear_symmetric`, `ChildModule.projL_idem`, `ChildModule.projS_idem`, `ChildModule.dot_split`, `TreeR.complete_iff_cauchyApprox`, `TreeR.inv_iff_markov`, die bewiesenen `SupData`-Sätze. Einige Typen brauchen implizite Voraussetzungen; das Paper muss diese offenlegen.

## B. Ein klar umrissener neuer mathematischer Satz, wenn die stärkere Behauptung im Paper erscheinen soll

### B1. Unäre Tripel können `−1` nicht repräsentieren

**Bereits formal bewiesen:** `TriplePath.unary_numer_ne_zero : ∀ t : TriplePath UnitChild, numer t ≠ 0` (`TreeNumbers/FoundationsLedger.lean:208`).

**Noch kein identifizierter eigenständiger Lean-Satz:** Für jedes gültige unäre Tripel `t`, `numer t ≠ − ofN (denom t)`. Notwendig ist dabei die streng positive Denominatorbedingung aus der Definition `TriplePath`, nicht ein frei gewählter Nenner.

**Empfohlenes zu elaborierendes Lean-Ziel** (Orientierung; **keine** hier typgeprüfte Lean-Datei):

```lean
-- zu ergänzen z. B. in TreeNumbers/FoundationsLedger.lean
-- volle Namen und Notation vor Lean-Lauf abgleichen
-- namespace TriplePath
-- theorem unary_numer_ne_neg_denom (t : TriplePath UnitChild) :
--    numer t ≠ -(TreeZ.ofN (denom t)) := by
--   ...
```

**Mathematischer Beweis:** Unäre Worte sind durch ihre Länge eindeutig. Sei `d_i=|P_i|`, `D=d_2−d_3>0`, `a=d_1−d_2`. Wäre `a=−D`, dann wäre `d_1=d_3`; über einem unären Alphabet folgt `P_1=P_3`, im Widerspruch zu `ne13`. Die vorhandene Nullobstruktion benutzt analog `ne12`.

**Akzeptanzkriterien:** (1) keine neuen Axiome, kein `Classical`, `sorry`, `admit` oder nichtprojektgebundene Importe; (2) neuer Satz mit `#print axioms` ohne unerlaubte Axiome; (3) Erklärung, weshalb `numer(t)/denom(t)≠−1` aus dem Integritätsbereich mit positivem Nenner folgt; (4) Quellfingerabdruck nach Modifikation **neu** bestimmen.

### B2. Exakte Bildcharakterisierung (größerer optionaler Satz)

Sei `FracQ` der bereits konstruierte rationale Bruchquotient. Definiere

`UnaryRepresentable(r) :⇔ ∃ t : TriplePath UnitChild, FracQ.mk (TriplePath.toFrac t)=r`.

Ziel:

`∀ r : FracQ, UnaryRepresentable(r) ↔ r≠0 ∧ r≠−1`.

**Die Richtung `→`:** B1 plus `unary_numer_ne_zero`, Positivität und Kürzbarkeit des positiven Nenners.

**Die Richtung `←`:** Wähle für `r` einen positiven Bruchnenner `D` und Zähler `a` mit `a≠0`, `a≠−D`. Wähle eine unäre Länge `d_3=N` so groß, dass `d_2=N+D` und `d_1=N+D+a` alle nichtnegativ sind. Dann sind `d_1,d_2,d_3` paarweise verschieden. Die zugehörigen drei unären Wörter bilden einen zulässigen Zeugen für `r`. Im projektinternen Typ `TreeZ` kann man statt formaler Subtraktion normalisierte positive/negative Paare und eine explizite `TreeN`-Verschiebung verwenden.

**Akzeptanzkriterien:** Echtes `FracQ`-Gleichheitsprädikat und Positivität, vollständige konstruktive Fallunterscheidung des `TreeZ`-Normalformträgers, keine importierten `Int/Rat/Nat`, keine klassische Wahl; globaler Release-Audit und Neuerzeugung aller deklarationsbezogenen Logs. Nicht als bereits formalisiert ausgeben.

**Paper-Entscheidung:** Die kritische Präzisierung „mindestens 0 und −1 fehlen“ kann als informell bewiesene Bemerkung eingefügt werden. Die **volle** Bildgleichheit sollte nur als zentraler *formal verifizierter* Satz angekündigt werden, wenn B2 implementiert und verifiziert wurde. Sonst optional als klar markierte mathematische, noch nicht Lean-formalisierte Aussage oder ganz weglassen.

## C. Weitere optional neue Lean-Ziele — nur bei Verschärfung des Papers

1. Expliziter `TreeZ`-Quotientenisomorphismus, falls die Arbeit behaupten soll, dass *der Lean-Träger selbst* eine `Quot`-Konstruktion ist (die zutreffende Manuskriptkorrektur benötigt ihn nicht).
2. Eigenes `FiniteWord.map_b_le_c`-Lemma für jedes `b≤c`, falls die Iteration der Nachfolgereinbettungen als eigenständiges formales Hauptresultat dargestellt werden soll (im Manuskript genügt die begründete Iteration).
3. `TreeQ`-Arity-**geordnetes** Isomorphie-Zertifikat als ein einziges Theorem, falls eine direkte Eins-zu-eins-Referenz erwünscht ist. Ordnungserhalt ist bereits separat bewiesen, u. a. `TreeQ.transfer_le`; kein neuer Beweis zur Korrektheit nötig.

## D. Nicht zu „fehlenden Beweisen“ erklären

Unbedingte allgemeine Cauchy-Vollständigkeit, modulfreie Modulwahl, Inversion aller `x≠0` ohne MP, Trichotomie ohne LPO, Null-Entscheidbarkeit ohne WLPO, unbeschränkte LUB/monotone Konvergenz, `IntervalsConnected K`, universelle longitudinale ω-Grenzräume und Rand–Zahlen-Homöomorphismen. Das sind **andere/strengere Fragestellungen**, bei denen das vorhandene Paper die bereits bewiesenen bedingten Aussagen korrekt einschränken muss. „Nicht formalisiert“ ist nicht „unmöglich“.
