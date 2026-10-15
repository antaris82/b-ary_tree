# Source and provenance policy

**Allowed imported mathematical code:** existing `Topics/Foundation/lean` only. Keep the original Foundation sources and historical release evidence unchanged. All new mathematical Lean declarations under `Topics/Local_Star/lean` must be independently written from scratch. Historical `FloatingStar` archive is read-only research evidence, **never** a permitted source tree.

For mathematical Lean sources, adopt Foundation's actual enforced source restrictions after verifying them against `Topics/Foundation/lean/scripts/source_check.py`: no `Nat`, `Int`, `Rat`, `Fin`, `Mathlib`, `Classical`, `noncomputable`, `sorry`, `admit`, new `axiom` declarations, decimal literals or forbidden automation/tactics. No implicit dependency via aliases or wrappers. No duplicative numerical carriers.

Generic `TField` and `TOField` are permissible **interfaces with law fields** only when their concrete Foundation instances discharge every requirement. An abstract law-field assumption must not be reported as proof for a concrete carrier.

The rules restrict handwritten mathematical source, not the Lean kernel's internal implementation. Quotient soundness, propositional extensionality, classical choice, bespoke axioms and sorry axioms must be reported separately when found in transitive axiom audits. Use documented Lean 4.28.0 and package-local `TreeFoundations` dependency.
