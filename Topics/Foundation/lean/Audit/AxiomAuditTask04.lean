import Lean
import TreeFoundations
import TreeAnalysis

/-! Task 04 proof-dependency audit.

1. `#print axioms` for **every** declaration added in Task 04 (Part 1) and for every earlier
   result cited in `FINAL_PROPERTY_MATRIX.md` (Part 2), covering all four carriers.
2. Effective dependency closure (`#closure_audit4`) of the central instances and headline
   results: every constant reachable from the type and value is collected, and the audit
   reports `Classical` constants, axioms, and built-in number constants (with their direct users).

Raw output: `Audit/axioms_task04.txt` (produced by `lake env lean Audit/AxiomAuditTask04.lean`). -/

-- Part 1: every declaration added in Task 04
-- TreeNumbers/FoundationsLedger.lean
#print axioms TreeN.induction
#print axioms TreeN.recN
#print axioms TreeN.recN_zero
#print axioms TreeN.recN_succ
#print axioms TreeN.recN_unique
#print axioms TreeN.zero_ne_one
#print axioms TreeN.le_total
#print axioms TreeN.mul_le_mul_right
#print axioms TreeN.mul_le_mul'
#print axioms TreeN.lt_iff_succ_le
#print axioms TreeN.le_iff_exists_add
#print axioms TreeZ.ofN_pos'
#print axioms TreeZ.not_nonNeg_neg_ofN_succ
#print axioms TreeZ.le_of_ofN_le
#print axioms TreeZ.LT
#print axioms TreeZ.ofN_lt_ofN
#print axioms TreeZ.lt_of_ofN_lt
#print axioms TreeZ.lt_irrefl
#print axioms TreeZ.le_of_lt
#print axioms TreeZ.lt_trichotomy
#print axioms TreeZ.zero_le_one
#print axioms TreeZ.zero_lt_one
#print axioms TreeZ.le_of_add_le_add_left
#print axioms TreeZ.add_le_add_right
#print axioms TreeZ.neg_le_neg
#print axioms TreeZ.nonNeg_mul_of_nonpos
#print axioms TreeZ.nonpos_mul_of_nonNeg_of_nonpos
#print axioms TreeZ.nonNeg_mul_self
#print axioms TreeZ.le_of_mul_le_mul_pos
#print axioms TriplePath.unary_numer_ne_zero
#print axioms TriplePath.unary_no_universal_witness
#print axioms TreeQ.ofF_letter_indep
#print axioms TreeQ.swapLetters
#print axioms TreeQ.ofFrac_letter_dependent
#print axioms TreeQ.transfer_letter_indep
#print axioms TreeQ.transfer_self
#print axioms TreeQ.transfer_comp
#print axioms TreeQ.transfer_natCast
#print axioms TreeQ.arityIso_comp
-- TreeAnalysis/FoundationsClosure.lean
#print axioms TOField.mul_lt_mul_of_pos_left
#print axioms TOField.mul_lt_mul_of_pos_right
#print axioms TreeQ.ofZ_zero
#print axioms TreeQ.ofZ_one
#print axioms TreeQ.ofZ_neg
#print axioms TreeQ.ofZ_lt
#print axioms TreeQ.lt_of_ofZ_lt
#print axioms TreeQ.transfer_ofZ
#print axioms TreeR.ofZRα
#print axioms TreeR.ofZRα_injective
#print axioms TreeR.ofZRα_zero
#print axioms TreeR.ofZRα_one
#print axioms TreeR.ofZRα_add
#print axioms TreeR.ofZRα_mul
#print axioms TreeR.ofZRα_neg
#print axioms TreeR.ofZRα_le
#print axioms TreeR.le_of_ofZRα_le
#print axioms TreeR.ofZRα_lt
#print axioms TreeR.natR_eq_ofZRα
#print axioms TreeR.natR_le_iff
#print axioms TreeR.natR_zero
#print axioms TreeR.mapR_congr
#print axioms TreeR.realArityIso_self
#print axioms TreeR.realArityIso_comp
#print axioms TreeR.realArityIso_ofZRα
#print axioms TreeR.realArityIso_natR
#print axioms TreeR.DecidableZero
#print axioms TreeR.Trichotomy
#print axioms TreeR.wlpo_of_decidableZero
#print axioms TreeR.decidableZero_of_wlpo
#print axioms TreeR.decidableZero_iff_wlpo
#print axioms TreeR.zeroOrApart_of_trichotomy
#print axioms TreeR.trichotomy_of_zeroOrApart
#print axioms TreeR.trichotomy_iff_lpo
#print axioms TreeR.decidableZero_of_lpo
-- TreeAnalysis/ApproxClosure.lean
#print axioms TreeR.cring_four
#print axioms TreeR.cring_trick
#print axioms TreeR.cring_two_terms
#print axioms TreeR.rnonneg_half
#print axioms TreeR.rclose_zero_iff
#print axioms TreeR.rclose_mul_zero
#print axioms TreeR.rclose_sub_iff
#print axioms TreeR.rclose_add
#print axioms TreeR.rclose_neg
#print axioms TreeR.rclose_zero_of_abs
#print axioms TreeR.rclose_mul
#print axioms TreeR.twoPow_mul_eps_shift
#print axioms TreeR.double_shift
#print axioms TreeR.natCast_le_twoPow_of_le
#print axioms TreeR.rclose_zero_of_bounds
#print axioms TreeR.converges_add
#print axioms TreeR.converges_neg
#print axioms TreeR.converges_mul
#print axioms TreeR.Tracked
#print axioms TreeR.Tracked.cseq
#print axioms TreeR.Tracked.lim
#print axioms TreeR.Tracked.converges
#print axioms TreeR.Tracked.lim_eq_of_converges
#print axioms TreeR.Tracked.lim_indep
#print axioms TreeR.Tracked.approx_seqEquiv
#print axioms TreeR.Tracked.rcauchyMod_of_approx
#print axioms TreeR.Tracked.ofApproxMod
#print axioms TreeR.Tracked.constQ
#print axioms TreeR.Tracked.ofCSeq
#print axioms TreeR.Tracked.ofRat
#print axioms TreeR.Tracked.ofTower
#print axioms TreeR.Tracked.lim_constQ
#print axioms TreeR.Tracked.lim_ofCSeq
#print axioms TreeR.Tracked.lim_ofRat
#print axioms TreeR.Tracked.add
#print axioms TreeR.Tracked.neg
#print axioms TreeR.Tracked.mulShift
#print axioms TreeR.Tracked.mulM
#print axioms TreeR.Tracked.mul_approx
#print axioms TreeR.Tracked.mul
#print axioms TreeR.Tracked.smulQ
#print axioms TreeR.Tracked.smulRep
#print axioms TreeR.Tracked.lim_add
#print axioms TreeR.Tracked.lim_neg
#print axioms TreeR.Tracked.lim_mul
#print axioms TreeR.Tracked.lim_smulQ
#print axioms TreeR.Tracked.lim_smulRep
#print axioms TreeR.Tracked.exists_tracked_smul
-- TreeAnalysis/Canonicity.lean
#print axioms TreeQ.ofZ_den_mul_ofF
#print axioms TreeQ.ofZ_ofN_ne_zero
#print axioms TreeQ.fieldIso_natCast
#print axioms TreeQ.fieldIso_ofZ
#print axioms TreeQ.fieldIso_unique
#print axioms TreeQ.fieldIso_ext
#print axioms TreeR.natR_cons
#print axioms TreeR.realIso_natR
#print axioms TreeR.realIso_ofZRα
#print axioms TreeR.realIso_ofQ
#print axioms TreeR.realIso_unique
-- TreeAnalysis/Task04Summary.lean
#print axioms Task04.em_of_dec
#print axioms Task04.treeN_certificate
#print axioms Task04.treeZ_certificate
#print axioms Task04.treeQ_certificate
#print axioms Task04.treeR_unconditional_certificate
#print axioms Task04.treeR_conditional_certificate
#print axioms Task04.treeR_convergence_certificate

-- Part 2: earlier results cited in FINAL_PROPERTY_MATRIX.md (all four carriers)
#print axioms UnaryPath.zero_or_extend
#print axioms UnaryPath.extend_injective
#print axioms UnaryTree.count_realized
#print axioms UnaryTree.count_unique
#print axioms UnaryTree.pathSum_self
#print axioms Word.unitSum_rootEdges
#print axioms Word.unitSum_nil
#print axioms Word.unitSum_snoc
#print axioms Word.pathSum_cons
#print axioms TreeN.add_assoc
#print axioms TreeN.add_comm
#print axioms TreeN.zero_add
#print axioms TreeN.add_zero
#print axioms TreeN.mul_assoc
#print axioms TreeN.mul_comm
#print axioms TreeN.one_mul
#print axioms TreeN.mul_one
#print axioms TreeN.zero_mul
#print axioms TreeN.mul_zero
#print axioms TreeN.left_distrib
#print axioms TreeN.right_distrib
#print axioms TreeN.instCSR
#print axioms TreeN.add_left_cancel
#print axioms TreeN.add_right_cancel
#print axioms TreeN.mul_left_cancel
#print axioms TreeN.mul_right_cancel
#print axioms TreeN.mul_eq_zero
#print axioms TreeN.succ_ne_zero
#print axioms TreeN.succ_injective
#print axioms TreeN.le_refl
#print axioms TreeN.le_trans
#print axioms TreeN.le_antisymm
#print axioms TreeN.lt_irrefl
#print axioms TreeN.lt_trans
#print axioms TreeN.compare
#print axioms TreeN.lt_or_eq_or_gt
#print axioms TreeN.decEq
#print axioms TreeN.decLE
#print axioms TreeN.decLT
#print axioms TreeN.add_le_add_left
#print axioms TreeN.add_lt_add_left
#print axioms TreeN.lt_of_add_lt_add_left
#print axioms TreeN.le_of_add_le_add_left
#print axioms TreeN.mul_le_mul_left
#print axioms TreeN.mul_lt_mul_left
#print axioms TreeN.mul_pos
#print axioms TreeN.add_diff
#print axioms TreeN.diff_add
#print axioms TreeN.pairEq_refl
#print axioms TreeN.pairEq_symm
#print axioms TreeN.pairEq_trans
#print axioms TreeN.normPair_normal
#print axioms TreeN.normPair_pairEq
#print axioms TreeN.normal_unique
#print axioms TreeZ.mkZ_sound
#print axioms TreeZ.mkZ_exact
#print axioms TreeZ.mkZ_self
#print axioms TreeZ.ind_mk
#print axioms TreeZ.add_mk
#print axioms TreeZ.neg_mk
#print axioms TreeZ.mul_mk
#print axioms TreeZ.instCRing
#print axioms TreeZ.zero_ne_one
#print axioms TreeZ.decEq
#print axioms TreeZ.mul_eq_zero
#print axioms TreeZ.mul_ne_zero
#print axioms TreeZ.mul_left_cancel
#print axioms TreeZ.mul_right_cancel
#print axioms TreeZ.ofN_injective
#print axioms TreeZ.ofN_add
#print axioms TreeZ.ofN_mul
#print axioms TreeZ.ofN_le_ofN
#print axioms TreeZ.sign
#print axioms TreeZ.absN_pos
#print axioms TreeZ.nonNeg_or_neg_nonNeg
#print axioms TreeZ.nonNeg_mul
#print axioms TreeZ.le_refl
#print axioms TreeZ.le_trans
#print axioms TreeZ.le_antisymm
#print axioms TreeZ.le_total
#print axioms TreeZ.add_le_add_left
#print axioms TreeZ.mul_le_mul_of_nonneg
#print axioms TriplePath.rel_refl
#print axioms TriplePath.rel_symm
#print axioms TriplePath.rel_trans
#print axioms TriplePath.denom_spec
#print axioms TriplePath.denom_pos
#print axioms TriplePath.witness_numer
#print axioms TriplePath.witness_denom
#print axioms TriplePath.toFrac_ofFrac
#print axioms TriplePath.universal_witness
#print axioms Frac.add_resp
#print axioms Frac.mul_resp
#print axioms Frac.neg_resp
#print axioms Frac.inv_resp
#print axioms Frac.eqv_trans
#print axioms TreeQ.sound
#print axioms TreeQ.exact
#print axioms TreeQ.mk_eq_ofF
#print axioms TreeQ.exists_ofF
#print axioms TreeQ.ofF_sound
#print axioms TreeQ.ofF_exact
#print axioms TreeQ.add_assoc'
#print axioms TreeQ.add_comm'
#print axioms TreeQ.zero_add'
#print axioms TreeQ.neg_add_cancel'
#print axioms TreeQ.mul_assoc'
#print axioms TreeQ.mul_comm'
#print axioms TreeQ.one_mul'
#print axioms TreeQ.zero_mul'
#print axioms TreeQ.left_distrib'
#print axioms TreeQ.zero_ne_one'
#print axioms TreeQ.mul_inv_cancel''
#print axioms TreeQ.inv_zero'
#print axioms TreeQ.charZero'
#print axioms TreeQ.instCRing
#print axioms TreeQ.instTField
#print axioms TreeQ.instTOField
#print axioms TreeQ.nonnegQ_add
#print axioms TreeQ.nonnegQ_mul
#print axioms TreeQ.nonnegQ_total
#print axioms TreeQ.nonnegQ_antisymm
#print axioms TreeQ.archQ_spec
#print axioms TreeQ.le_ofF_of_lef
#print axioms TreeQ.lef_of_le_ofF
#print axioms TreeQ.ofZ_injective
#print axioms TreeQ.ofZ_add
#print axioms TreeQ.ofZ_mul
#print axioms TreeQ.ofZ_le
#print axioms TreeQ.le_of_ofZ_le
#print axioms TreeQ.natCast_eq_ofZ
#print axioms TreeQ.pathLE_of_natCast_le
#print axioms TreeQ.transfer_add
#print axioms TreeQ.transfer_mul
#print axioms TreeQ.transfer_transfer
#print axioms TreeQ.arityIso
#print axioms TreeQ.transfer_le
#print axioms TreeQ.transferHom
#print axioms finiteArityIso
#print axioms finiteOmegaIso
#print axioms TField.mul_left_cancel'
#print axioms TField.mul_ne_zero'
#print axioms TField.eq_zero_of_mul_eq_zero_left
#print axioms TOField.natCast_injective
#print axioms TOField.le_archBound
#print axioms TOField.exists_eps_lt
#print axioms TOField.abs_add
#print axioms TOField.abs_mul
#print axioms TOField.abs_neg
#print axioms TOField.abs_nonneg
#print axioms TOField.eq_zero_of_abs_eq_zero
#print axioms TOField.mul_pos
#print axioms TOField.add_lt_add_left
#print axioms TOField.le_total
#print axioms TOField.le_antisymm
#print axioms TOField.inv_pos
#print axioms TOField.seqEquiv_refl
#print axioms TOField.seqEquiv_symm
#print axioms TOField.seqEquiv_trans
#print axioms TOField.reg_equiv
#print axioms TOField.isRegular_reg
#print axioms TOField.add_resp
#print axioms TOField.neg_resp
#print axioms TOField.mulSeq_resp
#print axioms TOField.mulMod_isMod
#print axioms TOField.invSeq_isMod
#print axioms TreeR.mkR_sound
#print axioms TreeR.mkR_exact
#print axioms TreeR.mkR_eq_iff
#print axioms TreeR.exists_rep
#print axioms TreeR.mkR_reg
#print axioms TreeR.exists_regular_rep
#print axioms TreeR.instCRing
#print axioms TreeR.zero_ne_one
#print axioms TreeR.ofQ_injective
#print axioms TreeR.ofQ_add
#print axioms TreeR.ofQ_mul
#print axioms TreeR.ofQ_neg
#print axioms TreeR.ofQ_le_ofQ
#print axioms TreeR.le_of_ofQ_le
#print axioms TreeR.ofQ_lt_ofQ
#print axioms TreeR.lt_of_ofQ_lt
#print axioms TreeR.natR_injective
#print axioms TreeR.lt_irrefl
#print axioms TreeR.lt_trans
#print axioms TreeR.le_refl
#print axioms TreeR.le_trans
#print axioms TreeR.le_antisymm
#print axioms TreeR.le_iff_not_lt
#print axioms TreeR.lt_cotrans
#print axioms TreeR.eq_of_not_apart
#print axioms TreeR.apart_cotrans
#print axioms TreeR.ne_of_apart
#print axioms TreeR.not_not_apart_of_ne
#print axioms TreeR.add_lt_add_right
#print axioms TreeR.add_le_add
#print axioms TreeR.mul_pos
#print axioms TreeR.mul_le_mul_of_nonneg_left
#print axioms TreeR.mul_lt_mul_of_pos_left
#print axioms TreeR.zero_lt_one
#print axioms TreeR.archimedean
#print axioms TreeR.archimedean_abs
#print axioms TreeR.exists_rat_between
#print axioms TreeR.rat_dense
#print axioms TreeR.ofQ_seq_converges
#print axioms TreeR.limit_unique
#print axioms TreeR.mul_rinv
#print axioms TreeR.rinv_indep
#print axioms TreeR.exists_inv_of_apart
#print axioms TreeR.apart_of_mul_eq_one
#print axioms TreeR.inv_unique
#print axioms TreeR.eq_zero_of_mul_eq_zero_of_apart
#print axioms TreeR.eq_zero_of_mul_eq_zero_of_ne
#print axioms TreeR.mul_left_cancel_of_ne
#print axioms TreeR.mul_ne_zero'
#print axioms TreeR.not_not_exists_inv
#print axioms TreeR.eq_of_not_not_eq
#print axioms TreeR.inv_iff_neImpliesApart
#print axioms TreeR.neImpliesApart_iff_markov
#print axioms TreeR.inv_iff_markov
#print axioms TreeR.zeroOrApart_iff_lpo
#print axioms TreeR.zeroProduct_of_zeroOrApart
#print axioms TreeR.markov_of_lpo
#print axioms TreeR.wlpo_of_lpo
#print axioms TreeR.TrackedCauchyTower.tower_converges
#print axioms TreeR.tower_limit
#print axioms TreeR.limit_of_approx
#print axioms TreeR.approxSeq_converges
#print axioms TreeR.close_of_cauchy_of_converges
#print axioms TreeR.rcauchyMod_iff_close
#print axioms TreeR.rcauchy_of_rcauchyMod
#print axioms TreeR.isModulus_of_rcauchyMod_ofQ
#print axioms TreeR.complete_iff_cauchyApprox
#print axioms TreeR.complete_of_lifting
#print axioms TreeR.complete_of_cauchyLifting
#print axioms TreeR.complete_of_choice
#print axioms TreeR.modulusFreeComplete_of_choice
#print axioms TreeR.modulusSelection_of_choice
#print axioms TreeR.ratModulusSelection_of_choice
#print axioms TreeR.complete_of_modulusFree
#print axioms TreeR.exists_rat_close
#print axioms TreeR.SupData.isLUB
#print axioms TreeR.SupData.sup_least
#print axioms TreeR.lub_unique
#print axioms TreeR.SupData.ofList_isLUB
#print axioms TreeR.SupData.ofMonotone
#print axioms TreeR.lub_of_monotone_converges
#print axioms TreeR.tower_monotone_lub
#print axioms TreeR.monotone_lub_of_choice
#print axioms TreeR.wlpo_of_unrestrictedLUB
#print axioms TreeR.lpo_of_bmc
#print axioms TreeR.extendR_unique
#print axioms TreeR.mapR_lt
#print axioms realArityIso
#print axioms realArityIso_ofQ
#print axioms natR_eq_ofZR
#print axioms ofZR_injective
#print axioms PrimitiveScope.provenance_chain
#print axioms PrimitiveScope.prefixCount_eq
#print axioms PrimitiveScope.prefixCount_indep
#print axioms PrimitiveScope.prefixCount_not_isCauchy
#print axioms PrimitiveScope.prefixCount_not_rcauchy
#print axioms Ray.encode_letter_choice_dependence

open Lean Elab Command

def closureOf4 (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let cs := ci.type.getUsedConstants ++ (match ci.value? with
          | some v => v.getUsedConstants
          | none => #[])
        for c in cs do
          if !seen.contains c then todo := c :: todo
  return seen

def numRoots4 : List Name :=
  [`Nat, `Int, `Rat, `Fin, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Real, `PNat]

elab "#closure_audit4 " ids:ident* : command => do
  let env ← getEnv
  for id in ids do
    let n := id.getId
    let cl := closureOf4 env [n]
    let classical := cl.toList.filter (fun c => c.components.any (· == `Classical))
    let axs := cl.toList.filter (fun c => match env.find? c with
      | some (ConstantInfo.axiomInfo _) => true
      | _ => false)
    let nums := cl.toList.filter (fun c => numRoots4.contains c.getRoot)
    let users := cl.toList.filter (fun c => !numRoots4.contains c.getRoot && (match env.find? c with
      | some ci => (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])).any
          (fun d => numRoots4.contains d.getRoot)
      | none => false))
    logInfo m!"{n}: closure size {cl.size}; Classical constants: {classical}; axioms: {axs}; \
      built-in number constants: {nums.length}; direct users of them: {users}"

#closure_audit4 TreeN.instCSR TreeZ.instCRing TreeQ.instTField TreeQ.instTOField TreeR.instCRing
  Task04.treeN_certificate Task04.treeZ_certificate Task04.treeQ_certificate
  Task04.treeR_unconditional_certificate Task04.treeR_conditional_certificate
  Task04.treeR_convergence_certificate TreeR.inv_iff_markov TreeR.decidableZero_iff_wlpo
  TreeR.trichotomy_iff_lpo TreeR.complete_iff_cauchyApprox TreeR.Tracked.mul
  TreeR.Tracked.lim_mul TreeR.converges_mul TreeQ.ofF_letter_indep TreeR.realArityIso_comp
  TreeQ.fieldIso_unique TreeR.realIso_unique
