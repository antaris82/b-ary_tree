# TASK 01 — Embedded Local Stars, Intrinsic Unit-Edge Network, and Exact Port Measurements

**Target repository:** https://github.com/antaris82/b-ary_tree  
**Authoritative upstream Foundation:** https://github.com/antaris82/b-ary_tree/tree/main/Topics/Foundation  
**Existing upstream Lean sources:** https://github.com/antaris82/b-ary_tree/tree/main/Topics/Foundation/lean  
**Work directory:** `Topics/Local_Star/lean`  
**Research plan:** `Topics/Local_Star/_formalization/MASTER_PLAN.md`  
**Toolchain:** Lean `leanprover/lean4:v4.28.0`.

## OBJECTIVE

**Implement and prove actual mathematical results**, not just a project scaffold.

Starting from the existing Foundation word-tree vertices, child symbols, primitive edges, intrinsic path numbers and intrinsic rational field, construct the **outward local star at an arbitrary word** and derive the elementary electrical response of its **unit-conductance** primitive edges.

This task must deliver:

1. A globally addressed embedded local star, with exact parent/child overlap and unique primitive-edge ownership.
2. An independently defined local unit-conductance Kirchhoff/Laplacian operator and its finite quadratic energy.
3. Proved symmetry, constant kernel, positive semidefiniteness, and positive definiteness after grounding the center.
4. **Explicit unit-current port experiments**, proving a two-terminal resistance of one from center to any child and two between any distinct children.
5. The **resistance-polarization Gram identity** `G(i,j)=δ(i,j)` for the child ports, derived **after** (not assumed before) the current measurements.

This is a substantial first formalization of the local electrical object. The full nonempty-boundary DtN family, 31/27 census, coupled-block elimination and infinite-boundary limits belong to subsequent tasks.

## SOURCE OF TRUTH AND PERMITTED DEPENDENCIES

Use the EXISTING, unmodified `Topics/Foundation/lean` implementation as the **only mathematical dependency**. Import its modules directly from the new local Lake package; it already declares `[[require]] name = "TreeFoundations", path = "../../Foundation/lean"`. Preserve the one-way dependency `Foundation → Local_Star`; never modify any Foundation file.

**No legacy-code reuse.** Older `FloatingStar` material, if available, is mathematical historical evidence only. Do not import, copy, translate, rename, port, or adapt its Lean definitions, proof scripts, matrix utilities, number carriers, or architecture. Write every new Local_Star mathematical declaration independently against the current Foundation interfaces.

Open and inspect the actual source, checking elaborated signatures and implicit assumptions before coding:

- `PrimitiveTree.FiniteWords`: `Word α := List α`, `Word.root`, `Word.IsParent`, `Word.Edge`, `Word.edgeTo`, `Word.child_injective`, `Word.parent_unique`, `Word.Edge.eq_of_child`.
- `PrimitiveTree.FiniteChild`: `Child b`, `Child.ext`, `Child.decEq`, `Child.one_unique`, `Child.zero_empty`, `Child.enum`.
- `PrimitiveTree.RootEdges`: `Word.unitSum_single`, `Word.pathSum`, `Word.pathSum_eq_depth`, `Word.pathSum_cons`.
- `TreeNumbers.PathNaturals`: `TreeN`, `TreeN.zero`, `TreeN.one`, `TreeN.succ`, path-defined addition/multiplication.
- `TreeNumbers.PathIntegers`: `TreeZ`, `TreeZ.ofN`, the existing signed arithmetic.
- `TreeNumbers.PathRationalField`: `TreeQ`, `TreeQOmega`, `TreeQb`, and their existing rational field instance, with its prerequisites.
- `TreeNumbers.FieldInterface`: `TField`, `TField.natCast`, `TField.inv`.
- `TreeAnalysis.RationalOrder` and `TreeAnalysis.OrderedField`: `QStar := TreeQOmega`, `TOField` ordered-rational instance, `TreeQ.ofZ`, `TreeQ.natCast_eq_ofZ`, positivity/order lemmas.
- `DimensionFoundation.FiniteSums`: existing finite sum over `Child b` (`FinSum.sumC`), use for star energies and currents; no second finite-index arithmetic.
- `DimensionFoundation.FiniteChildModule`: child potential functions and finite dot/sum operators if useful, without creating a parallel module theory.

Links to inspect:
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/PrimitiveTree/FiniteWords.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/PrimitiveTree/RootEdges.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/TreeNumbers/PathNaturals.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/TreeNumbers/PathIntegers.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/TreeNumbers/PathRationalField.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/TreeAnalysis/RationalOrder.lean  
https://github.com/antaris82/b-ary_tree/blob/main/Topics/Foundation/lean/DimensionFoundation/FiniteSums.lean

## EXCLUSIVE NUMERICAL CARRIERS — NONNEGOTIABLE

Use **only the already constructed intrinsic carriers** for all mathematical arithmetic:

- `N_T := TreeN`: arity, depth, counts, finite iteration, indices and discrete path arithmetic;
- `Z_T := TreeZ`: signed integral differences, using the Foundation embedding `TreeZ.ofN`;
- `Q_T := QStar = TreeQOmega`: electrical potentials, current, conductance, energies, Laplacians, resistances and Gram coefficients.

These symbols `N_T, Z_T, Q_T` describe the existing Foundation carriers; **do not create a new copy, wrapper carrier or alternative arithmetic**. If local notation is desired, use established declarations unchanged. An embedding of a path count into the rational field must use the established `TField.natCast (K := QStar)`, or the proved `TreeQ.ofZ (α := ChildOmega) (TreeZ.ofN n)` and their existing equality theorem. All signed scalar arithmetic, including negatives, must be in the existing `TreeZ`/`QStar` operations.

**Important arity-one fact:** `TreeQ (Child b)` only has the relevant proven field instance when the alphabet supplies two distinct letters. **Do not try to instantiate this field on `Child TreeN.one`.** Use the already established `QStar = TreeQOmega` with its `TOField QStar` instance **uniformly for all arities**, including `b=1` (and handle `b=0` explicitly if admitted). This does not introduce an external field. If needed later, use the proved arity-transfer isomorphism for `b≥2`, not a new numerical carrier.

No `Nat`, `Int`, `Rat`, `Fin`, `Real`, `OfNat`-based numeric computations, Mathlib-based sums/matrices, machine-word arithmetic, or decimal mathematical literals in handwritten Lean sources. Existing ordinary logical/type constructors are allowed subject to Foundation's exact source policy; they must not hide foreign number arithmetic. Numeric examples must be expressed with `TreeN.zero/one/two/succ`, `CSR.zero/one`, `TField.natCast`, finite sums and intrinsic field operations. Python arithmetic or other external diagnostics **cannot** count as the implemented numerical construction or its proof.

## PRECISE MATHEMATICAL MODEL

Let `b : TreeN` and `v : Word (Child b)`. Each child symbol `c : Child b` determines the ambient child `c :: v` and existing primitive edge `Word.edgeTo v c`. The outward star is

`V_v = {v} ∪ {c :: v | c : Child b}`,  
`E_v = {Word.edgeTo v c | c : Child b}`.

The center is an **arbitrary** tree node, not necessarily the global root. The incoming parent edge of a nonroot center is NOT part of its outward star. The global address of every local vertex must be its actual Foundation word. The local star has exactly one center and `b` distinct children.

For adjacent centers `w = c :: v`, prove:
- vertex intersection of `S(v)` and `S(w)` is **exactly `{w}`**;
- no primitive edges are shared;
- each ambient primitive parent→child edge is owned by exactly one outward local star (its parent center).

Avoid using an artificial disconnected collection of stars, or identifying distinct global nodes solely because their local index is the same.

### Electrical normalization, made explicit

The Foundation theorem `Word.unitSum_single` proves a primitive edge contributes **one path unit**, not Ohm's law. Define, explicitly as a **new constitutive model**, the primitive conductance of every outward star edge to be `(𝟙 : QStar)`. Then for potentials `U : local vertex → QStar` use the signed convention

`edgeVoltage(c) = U(child c) + -U(center)`,  
`edgeCurrent(c) = edgeVoltage(c)` (positive from child toward center),  
`energy(U) = sumC b (fun c => edgeVoltage(c) * edgeVoltage(c))`.

The local Kirchhoff current vector is

`(L U)(child c) = U(child c) - U(center)`,  
`(L U)(center) = Σ_c (U(center) - U(child c))`.

Choose and use **one consistent sign convention** so that a unit-current injection at a child gives positive child voltage relative to the grounded center. The local operator depends on `b` and intrinsic field operations, not on the absolute address `v`.

Derive (do not assume as fields in a synthetic interface):
- finite row sums `L(1)=0`;
- exact net injected current `Σ_{x∈V_v}(LU)(x)=0`;
- symmetry under the canonical finite coordinate pairing;
- exact identity `⟨U,LU⟩ = Σ_c (U(child c)-U(center))²`;
- `energy(U) ≥ 0` over the established `TOField QStar`;
- `energy(U)=0 ↔ ∀ c, U(child c)=U(center)`;
- with `U(center)=0`, `energy(U)=0 ↔ U=0` (grounded positive definiteness).

The **full** Laplacian is **positive semidefinite**, not strictly positive definite, because constant potentials are in its kernel. Grounding removes that constant direction. Do not call the bare response form an identity metric.

### Required **explicit port-current measurements**

Define a local port experiment mathematically: a current injection vector `J` on the actual local vertices, a chosen ground potential `U(center)=0`, Kirchhoff equation `L U=J`, and measured voltage difference/total current defining the two-terminal resistance. Construct and verify the solutions **without assuming an effective-resistance metric** in advance.

**Case A — root/center to one child:** for arbitrary `c : Child b`, inject `+𝟙` at child c, extract `-𝟙` at center, zero at other children; construct `U(center)=𝟘`, `U(child c)=𝟙`, `U(child d)=𝟘` for d≠c. Prove `L U=J`, uniqueness under the grounding, voltage drop `𝟙`, total injected current `𝟙`, and **measured resistance `R(center,c)=𝟙`**. At `v=Word.root`, this is exactly the proposed global-root grounding experiment; the same algebra must work at every addressed center.

**Case B — two different children:** for `c ≠ d`, inject `+𝟙` at c, extract `-𝟙` at d and zero at center/other children; construct `U(center)=𝟘`, `U(c)=𝟙`, `U(d)=-𝟙`, all other child potentials zero. Prove `L U=J`, uniqueness after grounding, voltage difference `𝟙+𝟙`, and **measured resistance `R(c,d)=𝟙+𝟙`**. The latter must be a `QStar` value, NOT a foreign literal. For b=1, this case is empty, not a fictitious second port.

Only after these measurements, define polarization for child ports:

`G(c,d) = (R(center,c)+R(center,d)-R(c,d)) * inv(𝟙+𝟙)`

where `R(c,c)=𝟘` by the distance/resistance convention when the endpoints coincide and division is used only with a proof that `𝟙+𝟙 ≠ 𝟘`. Prove `G(c,d)=𝟙` if `c=d`, else `G(c,d)=𝟘`, i.e. the **identity Gram matrix**. Prove `Σ_{c,d} a(c)G(c,d)a(d)>0` for each nonzero coefficient function `a : Child b → QStar` when the child set is nonempty. State exact hypotheses, including a witnessed nonzero coefficient if that is the more constructive formulation.

This identity Gram **is not** the whole-star DtN/Laplacian matrix. The distinct ambient coordinate Gram `I+J`, full DtN family and simplex classification remain later steps.

## IMPLEMENTATION AND MODULE BOUNDARIES

Implement real Lean definitions and proofs in small files; a sensible nonbinding structure is:

- `LocalStar/Primitive.lean`: addressed vertex/edge carriers, embeddings, intersections, unique edge ownership.
- `LocalStar/Electrical.lean`: finite child sums, potentials, currents, local Laplacian, Kirchhoff/energy/PSD/grounded-PD proofs.
- `LocalStar/PortMeasurements.lean`: explicit unit-current constructions, solved Kirchhoff equations, unit/two-unit resistance, identity Gram.

Reuse the Foundation `FinSum.sumC` and its lemmas; do not develop a general matrix library. Put generic helper lemmas where needed, not in a large serialized module chain. Update the existing entry file `LocalStar.lean` to import precisely the finished mathematical modules and keep `lakefile.toml`'s `LocalStar` target working.

Avoid replacing required proofs with an abstract structure that merely **assumes** symmetry, PSD, invertibility, resistance, or Gram identity.

## MANDATORY ACCEPTANCE TESTS

All requested checks must be performed on the finished source, not just planned:

1. A real successful `lake build LocalStar` with the unchanged Foundation dependency on Lean 4.28.0; record upstream Foundation commit SHA and the new Local_Star commit SHA.
2. Exact elaborated declaration signatures for the embedding, overlap, unit-edge law, energy, Laplacian, PSD/grounded-PD, both port measurements and identity Gram.
3. `#print axioms` for the main theorem endpoints and their actual transitive imported requirements; explicitly distinguish `Quot.sound`, `propext`, `Classical.choice`, `sorryAx` and any custom axioms.
4. Apply the **actual** Foundation mathematical-source restrictions (`Topics/Foundation/lean/scripts/source_check.py`), adapted as needed to cover all new `LocalStar/*.lean` and `LocalStar.lean` without weakening the prohibition list or modifying Foundation. Report how the check was executed.
5. Lean-level constructive tests for `b=1` and `b=2`, plus at least one `b=4` port/Gram test; also test center `Word.root` and a nonroot center. No external numerical carriers anywhere in these tests.
6. A direct consistency check that energy `0` forces constant potentials, yet nonconstant grounded potentials give positive energy; and that two-child port current satisfies zero injection at the center.
7. Show a concise final inventory of created/modified files and direct imports, with any genuinely unresolved statements listed as OPEN. Do not replace failed proofs by additional assumptions or silently change their types/quantifiers.

**STOP CONDITION:** Do not implement the full DtN `31/27` census, general coupled-block gluing, arbitrary global root-to-depth resistance, infinite-network boundary values, exterior algebras, Clifford/spin structures, or physical interpretations in Task 01. These require their own later, interface-checked tasks. Deliver the actual complete locally measured unit-star construction first.
