# Task 01 — Strict tree-internal foundations: report

Standalone Lean 4 project (Lean `v4.28.0`). **It does not depend on Mathlib** (the Mathlib requirement was
removed from `lakefile.toml` and `lake-manifest.json`). Everything is built from Lean core logic
(inductive types, `Prop`, `Eq`, structures, `List` as a plain data constructor, `Quot`).

Build: `lake build` builds the library `TreeFoundations` (all modules below).
`lake build Audit` builds `Audit/AxiomAudit.lean`, which prints `#print axioms` for the central results.

All four checkpoints are **fully proved**: there is no `sorry`, `admit`, `axiom`, `unsafe`, `partial`,
`implemented_by`, `native_decide`, `simp`, `simpa`, `omega`, `ring`, `linarith`, `norm_num`, `aesop`,
`Classical`, `classical` or `noncomputable` anywhere in the sources.

## Module layout (dependency order)

| Module | Content |
|---|---|
| `PrimitiveTree/UnitChild` | the one-element child-symbol type `UnitChild` |
| `PrimitiveTree/UnaryPaths` | `UnaryPath := List UnitChild`, `zeroPath`, `onePath`, `extend`, `concat`, `iterate` |
| `TreeNumbers/AlgebraInterface` | interface classes `CSR`, `CRing` (no content; only filled by the project's own constructions) + derived rearrangement lemmas |
| `TreeNumbers/PathNaturals` | `TreeN := UnaryPath`; `add` = concatenation, `mul` = repeated concatenation; semiring laws |
| `TreeNumbers/PathOrder` | inductive `PathLT`, `PathLE`; trichotomy `compare`, decidability, compatibility, cancellation, `diff` |
| `PrimitiveTree/ListOps` | structural `appL`, `mapL`, `InL`, `NodupL` (no library list API) |
| `PrimitiveTree/FiniteChild` | `Child b` (index `i : TreeN` + proof `PathLT i b`), inclusions, enumeration `Child.enum` |
| `PrimitiveTree/FiniteWords` | words, edge records, parents, directed root paths, walks, connectedness, no cycles |
| `PrimitiveTree/RootEdges` | unit-edge fold `unitSum`, `pathSum`, `unitSum (rootEdges w) = depth w`; unary tree |
| `TreeNumbers/PathIntegers` | `TreeZ` (normalized path pairs), ring laws, no zero divisors, cancellation, sign, order |
| `TreeNumbers/PathFractions` | auxiliary fraction data `(TreeZ, positive TreeN)` used to build witnesses |
| `TreeNumbers/PathTriples` | `TriplePath α`, numerator/denominator, universal witnesses `0^m, 1^n, 0·1^(k−1)` |
| `TreeNumbers/FieldInterface` | interface class `TField` (field + characteristic zero) |
| `TreeNumbers/PathRationalField` | `TreeQ α := Quot TriplePath.Rel`; operations; field laws; `TField` instance |
| `TreeNumbers/RationalArityIndependence` | field isomorphisms between all arities ≥ 2 and omega |
| `TreeFoundation/ArityEmbeddings` | letter/word/edge inclusions; vertex and edge union into the omega tree |
| `TreeFoundation/OmegaTree` | omega children ↔ `TreeN`; infinitely many children |
| `TreeFoundation/InfiniteRays` | rays `TreeN → α`, prefixes, properness of the finite-ray union |
| `TreeFoundation/ExtendedLevels` | conventional labels `negInfinity / finite n / posInfinity` |
| `DimensionFoundation/FiniteSums` | recursive sums over `Child b`, deltas, sifting, interchange, permutation invariance |
| `DimensionFoundation/FiniteChildModule` | `F K b := Child b → K`, module laws, `u_b`, `L_b`, `S_b`, `dot` |
| `DimensionFoundation/TransverseBasis` | bases of `L_b` and `S_b`, `F_b = L_b ⊕ S_b`, `b = one`, permutations |
| `DimensionFoundation/OmegaFiniteSupport` | `S_omega` (finitely supported, sum zero), basis, zero padding |
| `DimensionFoundation/BoundaryLongitudinal` | longitudinal limitations at omega arity |
| `DimensionFoundation/Instances` | the dimension results specialised to `TreeQ(b)` and `TreeQOmega` |

## Design decisions to be aware of

* **Words store the most recent step at the head.** The edge from parent `w` along child symbol `c` goes to
  `c :: w`. So the list `c₀ :: c₁ :: …` lists the steps from the deepest one back to the root. The witness
  address `0·1^(k−1)` is therefore the list `l0 :: rep l1 (q+1)`. (`0^m` and `1^n` are `rep l0 m` and
  `rep l1 n`, where `rep` is the local repeated-word constructor and its exponent is a unary path.)
* **`TreeZ` uses an explicitly proved canonical normalization, not a kernel quotient.** The spec allows this.
  `normPair` strips common unit steps. `TreeZ` is the structure of normalized path pairs (one component is the
  root path). `mkZ_sound` and `mkZ_exact` prove that two raw pairs have the same normal form exactly when
  `m + q = p + n`. Every ring law is proved on raw pairs and transported this way. Decidable equality and zero
  detection come out directly.
* **`TreeQ α` is the kernel quotient** `Quot (TriplePath.Rel)` of valid triple-path configurations. Its
  relation is exactly `A·D' = A'·D` in `TreeZ`. Operations build **new triple-path witnesses**
  (`TriplePath.ofFrac`) from the derived cross formulas, and lift with explicit compatibility proofs. The
  auxiliary `Frac` type is only a proof device: it is never the carrier of the field.
  `TreeQ (Child b)` (written `TreeQb b`) is a field whenever `b` has at least two children (class
  `AtLeastTwo b`, letters `⟨zero⟩`, `⟨one⟩`). `TreeQOmega := TreeQ TreeN`.
* **Exactness without `propext`.** `TreeQ.exact` is proved by lifting a Boolean reflection of the locally
  constructed decision procedure, not a `Prop`-valued function.
* **Section 6 is generic over the field.** `F K b := Child b → K` is stated for any `K` with the project's
  `TField` interface, and that interface is only populated by `TreeQ`. This lets `b = one` be treated with
  `K = TreeQOmega`: over a one-letter alphabet, triple paths do not support the field operations. By
  `finiteOmegaIso`, `TreeQOmega` is isomorphic to every `TreeQb b`. `DimensionFoundation/Instances` restates
  the main results with `K = TreeQb b` and `K = TreeQOmega`.
* **Rank `b − 1`.** A positive arity is written `b = c :: bp`, so `bp` is the predecessor unary path
  (`TreeN.pred`, `TreeN.succ_pred`). `transverse_basis c bp` gives the basis `e_{j+1} − e_0` indexed by
  `Child bp`. `transverse_index_bijection` shows that `j ↦ j+1` is a bijection onto the nonzero children.
  Independence and spanning are proved directly.
* **Acyclicity** is stated as: there is no closed walk of positive length whose traversed edges are pairwise
  distinct (`Word.no_cycle`). Every edge is a bridge (`bridge_out`, `bridge_in`).
* **Colimits:** `vertex_union` and `edge_union` prove that the omega tree is the *directed union* of the
  finite-arity trees. No abstract category-theoretic universal property is formalized, so this is not a proof
  of a colimit in an arbitrary category.
* **Longitudinal labels** (`ExtLevel`) are purely conventional. No geometric end, geodesic, midpoint or
  boundary hypersurface is inferred.

## Checkpoint I — primitive tree and `TreeN` (fully proved)

* Unary paths: `UnaryPath.extend_injective`, `extend_ne_zero`, `zero_or_extend`, `iterate_extend_zero`, `ne_cons_self`;
  the unary tree: `UnaryTree.pathSum_self`, `unique_child`, `count_realized`, `count_unique`.
* Semiring: `TreeN.add_zero`, `add_assoc`, `add_comm`, `add_succ`, `add_left_cancel`, `add_right_cancel`, `mul_zero`,
  `mul_succ`, `mul_comm`, `mul_assoc`, `left_distrib`, `right_distrib`, `one_mul`, `mul_one`, `instCSR`,
  `mul_eq_zero`, `decEq`.
* Order: `lt_irrefl`, `lt_trans`, `le_refl`, `le_trans`, `le_antisymm`, `compare` (constructive trichotomy),
  `decLT`, `decLE`, `exists_of_lt`, `exists_of_le`, `add_lt_add_left/right`, `lt_of_add_lt_add_left`,
  `mul_pos`, `mul_lt_mul_left`, `mul_left_cancel`, `mul_right_cancel`, `diff`, `add_diff`, `diff_add`, `diff_pos`.
* Finite arity: `Child`, `Child.zero_empty`, `one_unique`, `two_cases`, `first_ne_second`, `incl`, `inclSucc`,
  `incl_injective`, `decomp`, `enum`, `mem_enum`, `nodup_enum`.
* Trees: `Word.parent_unique`, `root_no_parent`, `children_eq`, `child_injective`, `symToChild`/`childToSym`
  (bijection with the alphabet), `rootEdges_dpath`, `dpath_root_unique`, `connected`, `bridge_out`, `bridge_in`,
  `no_cycle`, `depth_rep`, `unbounded_depth`.
* Unit-edge sums: `unitSum` (left fold, accumulator in `TreeN`, increment `one`), `unitSum_nil`, `unitSum_single`,
  `unitSum_snoc`, `unitSum_rootEdges : unitSum (rootEdges w) = depth w`.

## Checkpoint II — `TreeZ` (fully proved)

`PairEq` (`pairEq_refl/symm/trans`), `normPair`, `normal_unique`, `TreeZ.mkZ_sound`, `mkZ_exact`, `mkZ_self`,
`add_mk`, `neg_mk`, `mul_mk` (well-definedness), `add_comm'`, `add_assoc'`, `zero_add'`, `neg_add_cancel'`,
`mul_comm'`, `mul_assoc'`, `one_mul'`, `zero_mul'`, `left_distrib'`, `instCRing`, `zero_ne_one`, `decEq`,
`raw_no_zero_divisors`, `mul_eq_zero` (no zero divisors), `mul_left_cancel`, `mul_right_cancel`, `ofN` with
`ofN_add`, `ofN_mul`, `ofN_injective`, `ofN_ne_zero`, `sign` (constructive sign classification), `absN`,
`absN_pos`, order `LE` with `le_refl`, `le_trans`, `le_antisymm`, `le_total`, `add_le_add_left`,
`mul_le_mul_of_nonneg`, `ofN_le_ofN`, decidability.

## Checkpoint III — `TreeQ` (fully proved)

* Triples: `TriplePath`, `numer`, `denom`, `denom_spec` (gap equation), `denom_pos`, `denom_unique`, `Rel`,
  `rel_refl/symm/trans`.
* Universal witnesses: `wk' wk wn wm` (`k := q+two`, `n := k+D`, `m := p+two+D`, predecessor `k' := q+one`),
  `wP1 wP2 wP3`, `w_ne12`, `w_ne13`, `w_ne23`, `w_gt`, `witness_numer`, `witness_denom`, `toFrac_ofFrac`,
  `universal_witness`. These hold for every alphabet with two distinct letters: finite `b ≥ 2` and omega.
* Field: `TreeQ.sound`, `TreeQ.exact`, `ofF_sound`, `ofF_exact`, `ind_ofF`, `add_ofF`, `mul_ofF`, `neg_ofF`,
  `inv_ofF`, `add_comm'`, `add_assoc'`, `zero_add'`, `neg_add_cancel'`, `mul_comm'`, `mul_assoc'`, `one_mul'`,
  `zero_mul'`, `left_distrib'`, `zero_ne_one'`, `mul_inv_cancel''`, `inv_zero'` (the convention `inv 0 = 0`),
  `charZero'`, `instCRing`, `instTField`, `mk_eq_mk_iff`, `ofF_eq_ofF_iff`, `exists_ofF`.
  Compatibility of the raw operations: `Frac.add_resp`, `mul_resp`, `neg_resp`, `inv_resp`.
* Arity independence: `TreeQ.transfer`, `transfer_add/mul/neg/inv/zero/one`, `transfer_transfer`, `arityIso`,
  `finiteArityIso`, `finiteOmegaIso`.

## Checkpoint IV — tree limits and algebraic dimensions (fully proved)

* Embeddings: `ArityEmbedding.letterSucc_injective`, `letterOmega_injective`, `letterOmega_letterSucc`,
  `wordSucc_injective`, `wordOmega_injective`, `wordOmega_wordSucc`, `mapEdge_rootEdges`, `depth_mapWord`,
  `mapWord_isParent`, `vertex_union`, `edge_union`.
* Omega tree: `OmegaTree.indexOfChild_childOfIndex`, `childOfIndex_indexOfChild`, `children_distinct`,
  `infinitely_many_children`, `child_outside`, `unbounded_depth`.
* Rays: `Ray.prefixAt`, `depth_prefixAt`, `prefixAt_isParent`, `prefixAt_isDesc`, `eq_of_prefixAt`,
  `prefixAt_root_path_unique`, `depth_strictMono`, `depth_unbounded`, `RayOmega.prefixAt_ofFinite`,
  `identityRay_not_finite`, `union_proper`.
* Labels: `ExtLevel`, `root_level`, `first_edge_unit`, `vertex_lt_ray`, `ray_levels_unbounded`.
* Finite module: `ChildModule.addV_assoc`, `addV_comm`, `zero_addV`, `negV_addV`, `smul_addV`, `add_smul`,
  `mul_smul`, `one_smul`, `dot_u_of_inS`, `dot_comm`, `longitudinal_basis` (rank one), `transverse_basis`
  (rank `b − 1`), `transverse_index_bijection`, `tv_indep`, `tv_span`, `decomposition`, `projL_inL`,
  `projS_inS`, `decomposition_unique`, `inL_inS_zero`, `transverse_one_zero`, `transverse_one_index_empty`,
  `dot_perm`, `inS_perm`, `inL_perm`. Sums: `FinSum.sumC_perm`, `sumC_swap`, `sumC_delta`, `sumC_one`,
  `sumC_eq_fold`.
* Omega: `OmegaModule.sumUpTo_indep`, `tvO_indep`, `tvO_span`, `lincombO_inSO`, `positive_index`, `pad_inSO`,
  `pad_injective`, `pad_tv`, `pad_padSucc`, `padSucc_inS`, `padSucc_tv`.
* Limitations: `Longitudinal.allOnes_not_finSupp`, `no_finSupp_uniform_limit`, `padSucc_u_not_inL`.
  These are proved. What is **not** claimed: no canonical omega-dimensional longitudinal line and no limiting
  longitudinal vector along rays. Either would need an additional transport or limit structure, and that is a
  possible extension only.

## Audit (A): source firewall

* A textual screen over every project `.lean` file found these identifiers **only inside comments**: `Nat`,
  `Int`, `Rat`, `Fin`, `PNat`, `UInt*`, `BitVec`, `List.length`, `List.range`, `List.replicate`, `List.get`,
  `Classical`, `classical`, `noncomputable`, `omega`, `norm_num`, `ring`, `linarith`, `simp`, `simpa`, `sorry`,
  `admit`, `axiom`, `unsafe`, `partial`, `decide`. The word `omega` appears as the name of the countably
  branching tree, and "ring" as English text. No numeral literal occurs in code: `zero`, `one` and `two` are
  named unary paths, and `𝟘`, `𝟙` are the project's own notation for the interface fields.
* **Elaborated-dependency scan.** A Lean metaprogram (tooling, kept outside the library and reproduced below)
  walked all 1271 elaborated constants of the project. It looked for direct references to `Nat*`, `Int*`,
  `Rat*`, `Fin*`, `UInt*`, `USize*`, `BitVec*`, `Classical*`, `OfNat*`, `List.length/range/replicate/get`,
  `propext` and `Decidable.em`. After excluding compiler-generated auxiliaries, **no project declaration
  references any of them**. The excluded auxiliaries are `sizeOf` specifications, `ctorIdx`/`toCtorIdx`,
  `noConfusion`/`noConfusionType`, `ctorElim*`, constructor `.elim`, and the syntax/macro declarations of the
  notations `𝟘` and `𝟙`.
  Disclosure: these auxiliaries are generated automatically by Lean for every inductive type. Lean `v4.28`
  implements constructor discrimination (`noConfusion`, used by `injection`, `nomatch` and dependent `cases`)
  through constructor indices in the built-in `Nat`. This is internal elaboration machinery of the toolchain,
  not an arithmetic theory used by the project.
* Uses of Core definitions, and why each is purely structural or logical: `List` (constructors and recursor
  only), `Prod`/`Exists`/`Or`/`And`/`Iff` (logic), `Bool` (target of the Boolean reflection `boolOf`),
  `Decidable` (instances are all hand-written by structural recursion), `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`/
  `Quot.sound`, `funext` (a theorem derived in Lean from `Quot.sound`), and the notation classes `Add`, `Mul`,
  `Neg`, populated only by the project's operations.

## Audit (B): `#print axioms` (output of `lake build Audit`)

Every central result depends on **no axioms**, or on **`Quot.sound` only**. `Quot.sound` comes from the
quotient `TreeQ` and from function extensionality, which Lean derives from `Quot.sound`; extensionality is
used for vectors `Child b → K` and for the binary lift on `TreeQ`. No result uses `propext`,
`Classical.choice` or any project-added axiom.

    'TreeN.instCSR' does not depend on any axioms
    'TreeN.add_comm' does not depend on any axioms
    'TreeN.mul_comm' does not depend on any axioms
    'TreeN.mul_assoc' does not depend on any axioms
    'TreeN.left_distrib' does not depend on any axioms
    'TreeN.add_left_cancel' does not depend on any axioms
    'TreeN.mul_left_cancel' does not depend on any axioms
    'TreeN.lt_irrefl' does not depend on any axioms
    'TreeN.lt_trans' does not depend on any axioms
    'TreeN.compare' does not depend on any axioms
    'TreeN.decLT' does not depend on any axioms
    'TreeN.decEq' does not depend on any axioms
    'UnaryTree.count_realized' does not depend on any axioms
    'UnaryTree.count_unique' does not depend on any axioms
    'Word.parent_unique' does not depend on any axioms
    'Word.dpath_root_unique' does not depend on any axioms
    'Word.connected' does not depend on any axioms
    'Word.no_cycle' does not depend on any axioms
    'Word.symToChild_childToSym' does not depend on any axioms
    'Word.unbounded_depth' does not depend on any axioms
    'Word.unitSum_rootEdges' does not depend on any axioms
    'Word.unitSum_snoc' does not depend on any axioms
    'Child.mem_enum' does not depend on any axioms
    'Child.nodup_enum' does not depend on any axioms
    'Child.incl_injective' does not depend on any axioms
    'TreeZ.instCRing' does not depend on any axioms
    'TreeZ.mkZ_sound' does not depend on any axioms
    'TreeZ.mkZ_exact' does not depend on any axioms
    'TreeZ.zero_ne_one' does not depend on any axioms
    'TreeZ.mul_eq_zero' does not depend on any axioms
    'TreeZ.mul_left_cancel' does not depend on any axioms
    'TreeZ.ofN_injective' does not depend on any axioms
    'TreeZ.sign' does not depend on any axioms
    'TreeZ.le_total' does not depend on any axioms
    'TreeZ.le_antisymm' does not depend on any axioms
    'TreeZ.le_trans' does not depend on any axioms
    'TreeZ.add_le_add_left' does not depend on any axioms
    'TreeZ.absN_pos' does not depend on any axioms
    'TriplePath.denom_spec' does not depend on any axioms
    'TriplePath.denom_pos' does not depend on any axioms
    'TriplePath.rel_trans' does not depend on any axioms
    'TriplePath.universal_witness' does not depend on any axioms
    'TriplePath.toFrac_ofFrac' does not depend on any axioms
    'TreeQ.exact' does not depend on any axioms
    'TreeQ.sound' depends on axioms: [Quot.sound]
    'TreeQ.add_comm'' depends on axioms: [Quot.sound]
    'TreeQ.add_assoc'' depends on axioms: [Quot.sound]
    'TreeQ.neg_add_cancel'' depends on axioms: [Quot.sound]
    'TreeQ.mul_assoc'' depends on axioms: [Quot.sound]
    'TreeQ.mul_comm'' depends on axioms: [Quot.sound]
    'TreeQ.left_distrib'' depends on axioms: [Quot.sound]
    'TreeQ.zero_ne_one'' does not depend on any axioms
    'TreeQ.mul_inv_cancel''' depends on axioms: [Quot.sound]
    'TreeQ.inv_zero'' depends on axioms: [Quot.sound]
    'TreeQ.instTField' depends on axioms: [Quot.sound]
    'TreeQ.arityIso' depends on axioms: [Quot.sound]
    'finiteArityIso' depends on axioms: [Quot.sound]
    'finiteOmegaIso' depends on axioms: [Quot.sound]
    'ArityEmbedding.vertex_union' does not depend on any axioms
    'ArityEmbedding.edge_union' does not depend on any axioms
    'ArityEmbedding.wordOmega_wordSucc' does not depend on any axioms
    'OmegaTree.childOfIndex_indexOfChild' does not depend on any axioms
    'OmegaTree.infinitely_many_children' does not depend on any axioms
    'Ray.prefixAt_isDesc' does not depend on any axioms
    'Ray.eq_of_prefixAt' does not depend on any axioms
    'Ray.depth_unbounded' does not depend on any axioms
    'RayOmega.union_proper' does not depend on any axioms
    'ExtLevel.root_level' does not depend on any axioms
    'FinSum.sumC_perm' does not depend on any axioms
    'FinSum.sumC_eq_fold' does not depend on any axioms
    'ChildModule.longitudinal_basis' depends on axioms: [Quot.sound]
    'ChildModule.transverse_basis' depends on axioms: [Quot.sound]
    'ChildModule.transverse_index_bijection' does not depend on any axioms
    'ChildModule.dot_u_of_inS' does not depend on any axioms
    'ChildModule.decomposition' depends on axioms: [Quot.sound]
    'ChildModule.projS_inS' does not depend on any axioms
    'ChildModule.decomposition_unique' depends on axioms: [Quot.sound]
    'ChildModule.transverse_one_zero' depends on axioms: [Quot.sound]
    'ChildModule.dot_perm' does not depend on any axioms
    'ChildModule.inS_perm' does not depend on any axioms
    'ChildModule.inL_perm' does not depend on any axioms
    'OmegaModule.sumUpTo_indep' does not depend on any axioms
    'OmegaModule.tvO_indep' does not depend on any axioms
    'OmegaModule.tvO_span' depends on axioms: [Quot.sound]
    'OmegaModule.lincombO_inSO' does not depend on any axioms
    'OmegaModule.pad_inSO' does not depend on any axioms
    'OmegaModule.pad_tv' depends on axioms: [Quot.sound]
    'OmegaModule.pad_padSucc' depends on axioms: [Quot.sound]
    'OmegaModule.padSucc_tv' depends on axioms: [Quot.sound]
    'Longitudinal.allOnes_not_finSupp' does not depend on any axioms
    'Longitudinal.no_finSupp_uniform_limit' does not depend on any axioms
    'Longitudinal.padSucc_u_not_inL' does not depend on any axioms
    'transverse_basis_treeQ' depends on axioms: [Quot.sound]
    'direct_sum_treeQ' depends on axioms: [Quot.sound]
    'omega_span' depends on axioms: [Quot.sound]

## Elaborated-dependency scan script (tooling, not part of the library)

Run with `LEAN_PATH=.lake/build/lib/lean lean <file>` after `lake build`; output: `scanned 1271 project constants` and no hits.

    import Lean
    import TreeFoundations
    open Lean Meta Elab Command
    
    def forbiddenPrefixes : List Name := [`Nat, `Int, `Rat, `Fin, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Classical, `OfNat, `List.length, `List.range, `List.replicate, `List.get, `List.get!, `propext, `Decidable.em]
    
    def isForbidden (n : Name) : Bool :=
      forbiddenPrefixes.any fun p => p == n || p.isPrefixOf n
    
    elab "#audit" : command => do
      let env ← getEnv
      let ourMods := #[`PrimitiveTree, `TreeNumbers, `TreeFoundation, `DimensionFoundation]
      let mut total := 0
      let mut hits : Array (Name × Array Name) := #[]
      for (n, ci) in env.constants.toList do
        match env.getModuleIdxFor? n with
        | none => continue
        | some idx =>
          let modName := env.header.moduleNames[idx.toNat]!
          unless ourMods.any (fun m => m.isPrefixOf modName) do continue
          total := total + 1
          let auto := n.components.any fun c =>
            let str := c.toString
            str == "sizeOf_spec" || str == "ctorIdx" || str == "toCtorIdx" || str == "noConfusionType" ||
            str == "noConfusion" || str == "ctorElim" || str == "ctorElimType" || str == "elim" ||
            str.startsWith "_sizeOf" || str.startsWith "«_aux" || str.startsWith "_aux" || str.startsWith "«term" || str.startsWith "term"
          if auto then continue
          let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
          let bad := used.filter isForbidden
          unless bad.isEmpty do
            hits := hits.push (n, bad.toList.eraseDups.toArray)
      logInfo m!"scanned {total} project constants"
      for (n, bad) in hits do
        logInfo m!"{n} uses {bad}"
    
    #audit

## Remaining gaps

None of the required objectives is open. The points to keep in mind are the formulation choices listed above:
* normalization instead of a kernel quotient for `TreeZ`;
* head-first word storage;
* a generic field parameter in Sections 6–7, so that `b = one` is handled with `TreeQOmega`;
* a directed-union formulation of the colimit statements;
* the compiler-generated auxiliaries disclosed in Audit (A).
