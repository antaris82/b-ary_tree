#!/usr/bin/env python3
"""Documentation tooling: regenerate FINAL_AXIOM_AND_LAW_MATRIX.md and
release/declaration_signatures.txt.

Rows 1-131 are taken from the Task 04 matrix (FINAL_PROPERTY_MATRIX.md); rows 132ff are the
Task 05 additions listed in NEW_ROWS below.  For every cited declaration, the existence, the
elaborated type and the kernel-axiom closure are computed by Lean itself (a temporary Lean file
run with `lake env lean`); a cited name that does not resolve to exactly one constant makes
this script fail.  The axiom column of the matrix is therefore mechanical.
Usage: python3 scripts/gen_matrix.py   (requires the libraries to be built)
"""
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

STATUS = {
    "PROVED_UNCONDITIONALLY": "PROVED",
    "PROVED_CONDITIONALLY": "CONDITIONAL",
    "PROVED_OBSTRUCTION": "OBSTRUCTION",
    "OPEN": "OPEN",
    "DEFINITION_ONLY": "DEFINITION_ONLY",
    "NOT_APPLICABLE": "NOT_APPLICABLE",
}

# Rows of the Task 04 matrix whose status is re-labelled for the Task 05 vocabulary.
# Row 46: `[TwoLetters α]` is the typing premise of the carrier, satisfied by every finite
# arity b ≥ two and by omega; the universal witness is PROVED under that stated hypothesis.
RELABEL = {46: "PROVED"}

NEW_ROWS = [
    # carrier, claim, formula, module, names, hypotheses, status
    ("TreeN (provenance)", "depth relation on words is an equivalence relation",
     "`pathSum w = pathSum v` is reflexive, symmetric, transitive; equivalently `depth w = depth v`",
     "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.depthRel_refl", "DepthQuotient.depthRel_symm", "DepthQuotient.depthRel_trans",
      "DepthQuotient.depthRel_iff_depth"], "any alphabet `α`", "PROVED"),
    ("TreeN (provenance)", "class of a word depends only on its unit-edge sum (exactness)",
     "`cls w = cls v ↔ pathSum w = pathSum v` (both directions)", "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.cls_eq_iff", "DepthQuotient.count_cls", "DepthQuotient.count_injective"],
     "any alphabet `α`", "PROVED"),
    ("TreeN (provenance)", "`count` and `realize a` are mutually inverse",
     "`count (realize a n) = n`, `realize a (count x) = x`", "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.count_realize", "DepthQuotient.realize_count", "DepthQuotient.count_surjective"],
     "a letter `a : α`", "PROVED"),
    ("TreeN (provenance)", "letter independence at class level; representative words depend on the letter",
     "`realize a n = realize b n`; `a ≠ b → rep a (succ n) ≠ rep b (succ n)`",
     "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.realize_letter_indep", "DepthQuotient.oneD_letter_indep",
      "DepthQuotient.depthIso_letter_indep", "DepthQuotient.rep_letter_dependent"],
     "letters `a b : α`", "PROVED"),
    ("TreeN (provenance)", "ordered-semiring isomorphism `TreeN ≅ DepthClass α`",
     "bijection preserving `zero`, `one`, `+` (grafting), `·` (repetition), and `≤` in both directions",
     "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.depthIso", "DepthQuotient.realize_add", "DepthQuotient.realize_mul",
      "DepthQuotient.realize_le", "DepthQuotient.count_add", "DepthQuotient.count_mul",
      "DepthQuotient.csr"], "a letter `a : α`", "PROVED"),
    ("TreeN (provenance)", "transferred order = existence of a grafted extension",
     "`LED x y ↔ ∃ z, y = x + z`", "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.led_iff_graft"], "a letter `a : α` (for `→`)", "PROVED"),
    ("TreeN (provenance)", "letter-free alphabets represent no positive count; quotient is the root class",
     "`(α → False) → ¬ ∃ x, count x = succ n`; `x = zeroD`", "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.no_positive_count_of_noLetter", "DepthQuotient.eq_zeroD_of_noLetter",
      "DepthQuotient.empty_no_one", "DepthQuotient.word_eq_root_of_noLetter"],
     "`α → False` (e.g. `Empty`)", "OBSTRUCTION"),
    ("TreeN (provenance)", "on `T₁` the depth quotient identifies nothing",
     "`cls w = cls v ↔ w = v` for `w v : Word UnitChild`; `count (cls p) = p`",
     "TreeNumbers/DepthQuotient.lean",
     ["DepthQuotient.unary_cls_eq_iff", "DepthQuotient.unary_count_cls"], "—", "PROVED"),
    ("TreeQ", "classes depend only on the three path sums (not on addresses)",
     "equal `pathSum` of `p1`, `p2`, `p3` ⟹ `mk t = mk t'` (also via depths)",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TreeQ.mk_eq_of_pathSum_eq", "TreeQ.mk_eq_of_depth_eq", "TreeQ.numer_eq_of_pathSum_eq",
      "TreeQ.denom_eq_of_pathSum_eq"], "—", "PROVED"),
    ("FracQ", "internal fraction quotient is a field of characteristic zero",
     "`FracQ := Quot Frac.Eqv`; all `TField` laws incl. `0 ≠ 1`, inverses, `inv 0 = 0`",
     "TreeAnalysis/FractionCharacterization.lean",
     ["FracQ.instTField", "FracQ.instCRing", "FracQ.exact", "FracQ.mul_inv_cancel''",
      "FracQ.inv_zero'", "FracQ.charZero'"], "— (no alphabet)", "PROVED"),
    ("TreeQ ↔ FracQ", "mutually inverse comparison maps",
     "`ofFracQ (toFracQ x) = x`, `toFracQ (ofFracQ y) = y`; `toFracQ` injective",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TreeQ.toFracQ", "TreeQ.ofFracQ", "TreeQ.ofFracQ_toFracQ", "TreeQ.toFracQ_ofFracQ",
      "TreeQ.toFracQ_injective"], "`[TwoLetters α]` (for `ofFracQ`)", "PROVED"),
    ("TreeQ ↔ FracQ", "ordered-field isomorphism",
     "preserves `0, 1, +, -, ·, inv` (incl. `inv 0 = 0`), preserves and reflects `≤` and `<`",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TreeQ.orderedFieldIsoFracQ", "TreeQ.toFracQ_add", "TreeQ.toFracQ_mul", "TreeQ.toFracQ_neg",
      "TreeQ.toFracQ_inv", "TreeQ.toFracQ_inv_zero", "TreeQ.toFracQ_le", "TreeQ.le_of_toFracQ_le",
      "TreeQ.lt_iff_toFracQ"], "`[TwoLetters α]`", "PROVED"),
    ("TreeQ ↔ FracQ", "independence of the witness letters (class level)",
     "`@ofFracQ α I y = @ofFracQ α J y`; raw triples differ (`ofFrac_letter_dependent`)",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TreeQ.ofFracQ_letter_indep", "TreeQ.ofFrac_letter_dependent"], "`I J : TwoLetters α`",
     "PROVED"),
    ("TreeQ ↔ FracQ", "coherence with `transfer`, `arityIso`, `fieldIso_unique`, `realArityIso`, `realIso_unique`",
     "`toFracQ ∘ transfer = toFracQ`; `toFracQ ∘ φ = toFracQ` for every field iso; completions act as identity on fraction classes",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TreeQ.toFracQ_transfer", "TreeQ.toFracQ_fieldIso", "TreeQ.transfer_eq_ofFracQ_toFracQ",
      "TreeQ.arityIso_fracQ", "TreeR.realArityIso_ofFracQ", "TreeR.realIso_ofFracQ"],
     "`[TwoLetters α] [TwoLetters β]`", "PROVED"),
    ("TreeQ (scope)", "unary obstruction concerns the triple presentation only",
     "`toFracQ x ≠ 0` for every `x : TreeQ UnitChild`, while `FracQ` is a field",
     "TreeAnalysis/FractionCharacterization.lean",
     ["TriplePath.unary_toFracQ_ne_zero", "TriplePath.unary_obstruction_scope"], "—",
     "OBSTRUCTION"),
    ("rays", "levelwise permutations induce root- and incidence-preserving tree automorphisms",
     "`wordAct P` preserves root, depth, `IsParent` (both directions); inverse `wordAct P.symm`",
     "TreeFoundation/RayAutomorphism.lean",
     ["RayAutomorphism.treeAut", "RayAutomorphism.depth_wordAct", "RayAutomorphism.wordAct_isParent",
      "RayAutomorphism.isParent_of_wordAct", "RayAutomorphism.wordAct_symm_wordAct",
      "RayAutomorphism.wordAct_wordAct_symm", "RayAutomorphism.edgeAct"], "any alphabet", "PROVED"),
    ("rays", "ray action is compatible with finite prefixes",
     "`prefixAt (rayAct P r) n = wordAct P (prefixAt r n)`", "TreeFoundation/RayAutomorphism.lean",
     ["RayAutomorphism.prefixAt_rayAct", "RayAutomorphism.rayAct_symm_rayAct"], "any alphabet",
     "PROVED"),
    ("rays", "homogeneity: explicit levelwise swaps send any ray to any ray",
     "`rayAct (swapPerm ξ η) ξ = η`; prefixes of `ξ` go to prefixes of `η`",
     "TreeFoundation/RayAutomorphism.lean",
     ["RayAutomorphism.rayAct_swapPerm", "RayAutomorphism.treeAut_swapPerm_prefix",
      "RayAutomorphism.swap_swap", "finiteRay_homogeneous", "omegaRay_homogeneous"],
     "`DecidableEq α` (finite arity: any `b`; omega)", "PROVED"),
    ("rays", "automorphism-invariant functions on rays are constant",
     "`(∀ P r, F (rayAct P r) = F r) → F ξ = F η` (swap invariance suffices)",
     "TreeFoundation/RayAutomorphism.lean",
     ["RayAutomorphism.invariant_const", "RayAutomorphism.swapInvariant_const"], "`DecidableEq α`",
     "PROVED"),
    ("TreeR", "recursively composed tracked approximations",
     "for an expression tree `e` over tracked atoms: `(tracked fs Ts e).lim = eval (lim ∘ Ts) e` and convergence",
     "TreeAnalysis/TrackedExpressions.lean",
     ["TreeR.TExpr.tracked", "TreeR.TExpr.lim_tracked", "TreeR.TExpr.converges_evalSeq"],
     "tracking data for every atom", "PROVED"),
    ("TreeR", "unrestricted completeness with modulus (`UnrestrictedCompleteness K`) unconditionally",
     "`∀ f ν, RCauchyMod f ν → ∃ L, ConvergesTo f L` without premise", "TreeAnalysis/CompletenessScope.lean",
     ["UnrestrictedCompleteness"], "—", "OPEN"),
    ("TreeR", "modulus-free completeness (`ModulusFreeCompleteness K`) unconditionally",
     "`∀ f, RCauchy f → ∃ L, ConvergesTo f L` without premise", "TreeAnalysis/LiftingPrinciples.lean",
     ["ModulusFreeCompleteness"], "—", "OPEN"),
    ("TreeR", "linearly ordered field (decidable/total order and conventional inverses)",
     "not stated as a Lean structure for `TreeR`; would imply `Trichotomy` (⇔ `LPO`) and `NeImpliesApart` (⇔ Markov)",
     "—", [], "—", "OPEN"),
    ("TreeR", "Dedekind (order-)completeness",
     "not formulated in the project; `UnrestrictedLUB K` is the closest formulated statement (row 118)",
     "—", [], "—", "OPEN"),
    # Task 05 Q14 repair: the levelwise converse of row 147 is false (appended, numbering stable).
    ("rays", "Q14: not every tree automorphism is levelwise (counterexample to the converse of row 147)",
     "`subtreeSwapAut a b` swaps the subtrees at `a :: [a]` and `b :: [a]` (inverse: itself); "
     "`(treeAut P).toFun ≠ (subtreeSwapAut a b).toFun` for every `P : LevelPerm α`; instances `Child two`, `TreeN`",
     "TreeFoundation/AutomorphismCounterexample.lean",
     ["RayAutomorphism.subtreeSwapAut", "RayAutomorphism.subtreeSwap_isParent",
      "RayAutomorphism.subtreeSwap_subtreeSwap", "RayAutomorphism.subtreeSwap_append",
      "RayAutomorphism.subtreeSwapAut_not_levelwise", "RayAutomorphism.levelwise_converse_false",
      "binary_levelwise_converse_false", "omega_levelwise_converse_false"],
     "`DecidableEq α`, `a ≠ b`", "PROVED"),
    # Task 06: finite bilinear and projection laws (appended, numbering stable).
    ("F_b", "bilinearity and symmetry of the finite coordinate form `dot`",
     "`dot (x+y) z = dot x z + dot y z`, `dot x (y+z) = dot x y + dot x z`, `dot (a•x) y = a·dot x y`, "
     "`dot x (a•y) = a·dot x y`, `dot x y = dot y x`; no positivity/definiteness claimed",
     "DimensionFoundation/BilinearForm.lean",
     ["ChildModule.dot_addV_left", "ChildModule.dot_addV_right", "ChildModule.dot_smul_left",
      "ChildModule.dot_smul_right", "ChildModule.dot_bilinear_symmetric"],
     "`[TField K]`, any `b : TreeN`", "PROVED"),
    ("F_b", "projections `projL`, `projS` are complementary idempotents with identity action on `L_b`, `S_b`",
     "`projL ∘ projL = projL`, `projS ∘ projS = projS`, `projL ∘ projS = 0`, `projS ∘ projL = 0`, "
     "`projL x + projS x = x`; `projL x = x` on `InL`, `projS x = x` on `InS` (from `decomposition_unique`)",
     "DimensionFoundation/ProjectionLaws.lean",
     ["ChildModule.proj_of_inL", "ChildModule.proj_of_inS", "ChildModule.projL_idem",
      "ChildModule.projS_idem", "ChildModule.projL_projS", "ChildModule.projS_projL",
      "ChildModule.projections_idempotent_complementary"],
     "`[TField K]`, `PathLT zero b`", "PROVED"),
    ("F_b", "linearity, images, kernels and `dot`-orthogonality of the projections",
     "additive and homogeneous; image of `projL` = `L_b` = kernel of `projS`, image of `projS` = `S_b` = "
     "kernel of `projL`; `dot (projL x) (projS y) = 0` and `dot x y = dot (projL x) (projL y) + dot (projS x) (projS y)`",
     "DimensionFoundation/ProjectionLaws.lean",
     ["ChildModule.projL_addV", "ChildModule.projL_smul", "ChildModule.projS_addV", "ChildModule.projS_smul",
      "ChildModule.range_projL", "ChildModule.range_projS", "ChildModule.inS_iff_projL_eq_zero",
      "ChildModule.inL_iff_projS_eq_zero", "ChildModule.dot_projL_projS", "ChildModule.dot_split"],
     "`[TField K]`; `PathLT zero b` except for linearity", "PROVED"),
]


def parse_old():
    rows = []
    for line in open("FINAL_PROPERTY_MATRIX.md", encoding="utf-8"):
        if not line.startswith("| ") or line.startswith("| #") or line.startswith("|---"):
            continue
        c = [x.strip() for x in line.strip().strip("|").split(" | ")]
        num = int(c[0])
        names = re.findall(r"`([^`\s]+)`", c[5])
        status = STATUS[c[6].strip("*")]
        status = RELABEL.get(num, status)
        rows.append((num, c[1], c[2], c[3], c[4], names, c[7], status))
    return rows


def lean_info(names):
    lean = ["import Lean", "import TreeFoundations", "import TreeAnalysis",
            "open Lean Elab Command",
            "#eval show CommandElabM Unit from do",
            "  let env ← getEnv",
            "  let all := env.constants.toList.map (·.1)",
            f"  let names : List String := {json_list(names)}",
            "  let mut out := \"\"",
            "  for s in names do",
            "    let n := s.toName",
            "    let cands := if env.contains n then [n] else all.filter (fun c => n.isSuffixOf c && !c.isInternal)",
            "    match cands with",
            "    | [c] =>",
            "      let axs ← liftCoreM (collectAxioms c)",
            "      let ci := (env.find? c).get!",
            "      let ty ← liftTermElabM (Meta.ppExpr ci.type)",
            "      let tys := (toString ty).replace \"\\n\" \" \"",
            "      out := out ++ s ++ \"\\t\" ++ toString c ++ \"\\t\" ++ toString axs ++ \"\\t\" ++ tys ++ \"\\n\"",
            "    | cs => out := out ++ s ++ \"\\tUNRESOLVED\\t\" ++ toString cs ++ \"\\t-\\n\"",
            "  IO.FS.writeFile \"/tmp/gen_matrix_out.tsv\" out",
            ]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir="/tmp") as f:
        f.write("\n".join(lean) + "\n")
        path = f.name
    r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout, r.stderr)
        sys.exit(1)
    info = {}
    for line in open("/tmp/gen_matrix_out.tsv", encoding="utf-8"):
        s, c, axs, ty = line.rstrip("\n").split("\t", 3)
        info[s] = (c, axs, ty)
    return info


def json_list(xs):
    return "[" + ", ".join('"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"' for x in xs) + "]"


def main():
    old = parse_old()
    rows = list(old)
    n = len(old)
    for i, (car, claim, formula, module, names, hyp, status) in enumerate(NEW_ROWS, 1):
        rows.append((n + i, car, claim, formula, module, names, hyp, status))
    allnames = sorted({x for r in rows for x in r[5]})
    info = lean_info(allnames)
    bad = [s for s in allnames if info[s][0] == "UNRESOLVED"]
    if bad:
        print("UNRESOLVED NAMES:", bad)
        sys.exit(1)
    os.makedirs("release", exist_ok=True)
    with open("release/declaration_signatures.txt", "w", encoding="utf-8") as f:
        f.write("# Elaborated types and kernel-axiom closures of every declaration cited in\n"
                "# FINAL_AXIOM_AND_LAW_MATRIX.md (generated by scripts/gen_matrix.py).\n"
                "# cited name\tresolved constant\taxioms\ttype\n")
        for s in allnames:
            c, axs, ty = info[s]
            f.write(f"{s}\t{c}\t{axs}\t{ty}\n")
    counts = {}
    for r in rows:
        counts[r[7]] = counts.get(r[7], 0) + 1
    out = []
    out.append("# FINAL AXIOM AND LAW MATRIX\n")
    out.append("One row per concrete claim about `TreeN`, `TreeZ`, `TreeQ α`, `TreeR K` (and the derived\n"
               "comparison objects of Task 05).  Generated by `scripts/gen_matrix.py`; rows 1–131 carry over\n"
               "the Task 04 matrix (`FINAL_PROPERTY_MATRIX.md`) with the Task 05 status vocabulary, rows\n"
               f"132–{len(rows)} are new.\n")
    out.append("**Status vocabulary.** `PROVED`: a kernel-checked theorem/definition with exactly the listed\n"
               "hypotheses. `CONDITIONAL`: proved only under a named, unproved principle that appears as a\n"
               "hypothesis (`MarkovPrinciple`, `LPO`, `WLPO`, `ChoiceNN`, `SequenceLifting K`, …).\n"
               "`OBSTRUCTION`: a proved negative result about a *specific* construction or map (not a general\n"
               "impossibility). `OPEN`: not proved and not refuted in this project (no independence claim).\n"
               "`DEFINITION_ONLY`: a definition, no proof content.\n")
    out.append("**Hypotheses.** `[TwoLetters α]` is the typing premise of the carrier `TreeQ α` as a field\n"
               "(two distinct letters for witness triples); it is discharged by `Child b` for every `b ≥ two`\n"
               "(`AtLeastTwo b`) and by the omega alphabet. `TreeR` rows hold for every `[TOField K]`, concretely\n"
               "`K = QStar = TreeQ ChildOmega`; the `Task04.*` certificates are stated for `TreeRStar := TreeR QStar`.\n"
               "Interface lemmas (`CSR.*`, `TField.*`, `TOField.*`) count for a carrier only through its proved\n"
               "concrete instance.\n")
    out.append("**Axiom column.** Union of `Lean.collectAxioms` over the cited declarations, computed by Lean\n"
               "when this file was generated (`release/declaration_signatures.txt` lists every cited\n"
               "declaration with its elaborated type and axioms). `[]` means no axiom. The enforcing check\n"
               "over *all* project constants is `ReleaseAudit/Run.lean`.\n")
    out.append("Status counts: " + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + ".\n")
    out.append("| # | carrier | claim | exact Lean declaration(s) | hypotheses | status | axioms | formulation / remark |")
    out.append("|---|---|---|---|---|---|---|---|")
    for (num, car, claim, formula, module, names, hyp, status) in rows:
        decls = ", ".join(f"`{info[x][0]}`" for x in names) if names else "—"
        axset = set()
        for x in names:
            for a in re.findall(r"[A-Za-z_.]+", info[x][1]):
                axset.add(a)
        ax = ("`[" + ", ".join(sorted(axset)) + "]`") if names else "—"
        mod = f" ({module})" if module and module != "—" else ""
        out.append(f"| {num} | {car} | {claim} | {decls} | {hyp} | **{status}** | {ax} | {formula}{mod} |")
    out.append("")
    open("FINAL_AXIOM_AND_LAW_MATRIX.md", "w", encoding="utf-8").write("\n".join(out) + "\n")
    print(f"wrote FINAL_AXIOM_AND_LAW_MATRIX.md ({len(rows)} rows) and release/declaration_signatures.txt "
          f"({len(allnames)} declarations)")


if __name__ == "__main__":
    main()
