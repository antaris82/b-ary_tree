import TreeFoundations
import TreeAnalysis
import ReleaseAudit.Command

/-!
# Release audit entry point

Building this module (`lake build ReleaseAudit`) or checking it directly
(`lake env lean ReleaseAudit/Run.lean`) runs the fail-closed audit over every constant of every
project module imported by the two library roots.  Any violation is an elaboration error, so the
build fails with a nonzero exit status.  This file declares no constants of its own.
-/

#fail_closed_audit

/-! Central results that the release documentation cites; their absence fails the audit. -/
#require_decls
  TreeN.instCSR TreeZ.instCRing TreeQ.instTField TreeQ.instTOField TreeR.instCRing
  Task04.treeN_certificate Task04.treeZ_certificate Task04.treeQ_certificate
  Task04.treeR_unconditional_certificate Task04.treeR_conditional_certificate
  Task04.treeR_convergence_certificate
  Word.unitSum_rootEdges UnaryTree.count_unique TriplePath.universal_witness TreeQ.exact
  TreeQ.arityIso TreeQ.fieldIso_unique TreeR.realIso_unique realArityIso
  TreeQ.ofF_letter_indep TreeQ.ofFrac_letter_dependent TriplePath.unary_no_universal_witness
  DepthQuotient.depthIso DepthQuotient.cls_eq_iff DepthQuotient.realize_letter_indep
  DepthQuotient.no_positive_count_of_noLetter DepthQuotient.unary_cls_eq_iff
  TreeQ.mk_eq_of_pathSum_eq FracQ.instTField TreeQ.orderedFieldIsoFracQ
  TreeQ.ofFracQ_letter_indep TreeQ.toFracQ_fieldIso TreeR.realIso_ofFracQ
  TriplePath.unary_obstruction_scope
  RayAutomorphism.treeAut RayAutomorphism.prefixAt_rayAct RayAutomorphism.rayAct_swapPerm
  RayAutomorphism.invariant_const RayAutomorphism.subtreeSwapAut
  RayAutomorphism.subtreeSwapAut_not_levelwise RayAutomorphism.levelwise_converse_false
  binary_levelwise_converse_false
  TreeR.TExpr.lim_tracked TreeR.TExpr.converges_evalSeq
  ChildModule.transverse_basis ChildModule.decomposition RayOmega.union_proper
  ChildModule.dot_addV_left ChildModule.dot_addV_right ChildModule.dot_smul_left
  ChildModule.dot_smul_right ChildModule.projL_idem ChildModule.projS_idem ChildModule.projL_projS
  ChildModule.projS_projL ChildModule.projL_of_inL ChildModule.projS_of_inS
  ChildModule.dot_projL_projS ChildModule.range_projL ChildModule.range_projS
