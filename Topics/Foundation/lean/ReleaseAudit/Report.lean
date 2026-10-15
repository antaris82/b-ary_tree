import TreeFoundations
import TreeAnalysis
import ReleaseAudit.Command

/-!
# Axiom report for the central results (informational)

This file only *prints* the kernel-axiom closure of the results cited in
`FINAL_AXIOM_AND_LAW_MATRIX.md`.  Enforcement over **all** project constants is done by
`ReleaseAudit/Run.lean` (`#fail_closed_audit`), which fails the build on any violation.
-/

#axiom_report
  TreeN.instCSR Task04.treeN_certificate TreeN.recN_unique TreeN.mul_left_cancel
  TreeZ.instCRing Task04.treeZ_certificate TreeZ.mul_eq_zero TreeZ.mkZ_exact
  TreeQ.instTField TreeQ.instTOField Task04.treeQ_certificate TreeQ.exact
  TriplePath.universal_witness TreeQ.arityIso TreeQ.fieldIso_unique
  TreeR.instCRing Task04.treeR_unconditional_certificate Task04.treeR_conditional_certificate
  Task04.treeR_convergence_certificate TreeR.realIso_unique
  DepthQuotient.depthIso DepthQuotient.cls_eq_iff DepthQuotient.realize_letter_indep
  DepthQuotient.no_positive_count_of_noLetter DepthQuotient.eq_zeroD_of_noLetter
  DepthQuotient.unary_cls_eq_iff DepthQuotient.led_iff_graft
  TreeQ.mk_eq_of_pathSum_eq FracQ.instTField TreeQ.orderedFieldIsoFracQ TreeQ.lt_iff_toFracQ
  TreeQ.toFracQ_inv_zero TreeQ.ofFracQ_letter_indep TreeQ.toFracQ_transfer TreeQ.toFracQ_fieldIso
  TreeQ.arityIso_fracQ TreeR.realArityIso_ofFracQ TreeR.realIso_ofFracQ
  TriplePath.unary_toFracQ_ne_zero TriplePath.unary_obstruction_scope
  RayAutomorphism.treeAut RayAutomorphism.prefixAt_rayAct RayAutomorphism.rayAct_swapPerm
  RayAutomorphism.treeAut_swapPerm_prefix RayAutomorphism.invariant_const
  RayAutomorphism.swapInvariant_const finiteRay_homogeneous omegaRay_homogeneous
  TreeR.TExpr.lim_tracked TreeR.TExpr.converges_evalSeq
