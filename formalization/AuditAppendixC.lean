import DPCut.ImplementedApplications
import DPCut.KLProjection
import DPCut.CappedWaterfill
import DPCut.CappedProgress
import DPCut.CappedRetirement
import DPCut.Theorem30
import DPCut.CCResidual
import DPCut.Theorem32
import DPCut.Theorem34
import DPCut.Remark33
import DPCut.Lemma35
import DPCut.Theorem36
import DPCut.AppendixRuntime
import DPCut.PrivateBisection

/-! Appendix C proofs and real-arithmetic runtime certificates. External
algorithms and LSW are explicit theorem arguments. The application runtime
certificates use the implemented approximate solvers.
Expected transitive axioms: propext, Classical.choice, Quot.sound only. -/
#print axioms DPCut.lemma28
#print axioms DPCut.kl_projection_support
#print axioms DPCut.kl_projection_distance
#print axioms DPCut.kl_projection_existsUnique
#print axioms DPCut.normalized_mask_mem_cappedSimplex
#print axioms DPCut.normalized_target_mem_cappedSimplex
#print axioms DPCut.capped_projection_positive
#print axioms DPCut.capped_projection_waterfill
#print axioms DPCut.lowerBiasedMass_good
#print axioms DPCut.capped_continuing_mass
#print axioms DPCut.capped_minus_normalized_gap
#print axioms DPCut.capped_plus_normalized_gap
#print axioms DPCut.capped_residual_contraction
#print axioms DPCut.expect_blockCut
#print axioms DPCut.label_cut_transfer
#print axioms DPCut.partition_transfer
#print axioms DPCut.ccResidual_distance
#print axioms DPCut.cc_residual_identity
#print axioms DPCut.cc_residual_transfer
#print axioms DPCut.cc_baseline_transfer
#print axioms DPCut.cc_surrogate_transfer
#print axioms DPCut.cc_approximation_transfer
#print axioms DPCut.DP.postprocess
#print axioms DPCut.HighProbability.bind
#print axioms DPCut.bestOf_failure
#print axioms DPCut.expected_approximation_success
#print axioms DPCut.amplifiedMaxK_success
#print axioms DPCut.application_release
#print axioms DPCut.max_k_transfer
#print axioms DPCut.theorem32
#print axioms DPCut.private_max_cut
#print axioms DPCut.theorem34_transfer
#print axioms DPCut.theorem34

#print axioms DPCut.finiteCappedProjection_minimizes
#print axioms DPCut.measurable_finiteCappedProjection
#print axioms DPCut.maskedCappedProjection_decreases
#print axioms DPCut.cappedEstimate_potential_le
#print axioms DPCut.cappedNext_progress
#print axioms DPCut.cappedInnerLoop_privacy
#print axioms DPCut.cappedInnerLoop_release_of_potential
#print axioms DPCut.cappedOuterLoop_release_failure
#print axioms DPCut.cappedOuterLoop_belowCap
#print axioms DPCut.capped_retirement_output
#print axioms DPCut.cappedRelease_private
#print axioms DPCut.lemma29_explicit
#print axioms DPCut.lemma29
#print axioms DPCut.bernoulli_relative_tail
#print axioms DPCut.cc_bernoulli_rounding
#print axioms DPCut.amplifiedCC_success
#print axioms DPCut.ccPrivateKernel_private
#print axioms DPCut.ccPrivateKernel_utility
#print axioms DPCut.private_cc_reduction
#print axioms DPCut.theorem30
#print axioms DPCut.corollary31
#print axioms DPCut.private_correlation_clustering

#print axioms DPCut.remark33
#print axioms DPCut.hcCost_boundary
#print axioms DPCut.hc_uniform_transfer
#print axioms DPCut.hc_balanced_transfer
#print axioms DPCut.hierarchy_balanced_candidate
#print axioms DPCut.hierarchy_one_split
#print axioms DPCut.edge_charge_bound
#print axioms DPCut.lemma35

#print axioms DPCut.hierarchyLaw_quality
#print axioms DPCut.balanced_comparator
#print axioms DPCut.hierarchySplitKernel_quality
#print axioms DPCut.nonprivateHierarchy_quality
#print axioms DPCut.hierarchy_calibrated_transfer
#print axioms DPCut.theorem36

#print axioms DPCut.normalized_cut_transfer
#print axioms DPCut.expansion_transfer
#print axioms DPCut.uniformSparsity_transfer
#print axioms DPCut.private_balanced_objectives
#print axioms DPCut.cut_addIsolatedVertex
#print axioms DPCut.allCuts_addIsolatedVertex
#print axioms DPCut.restrict_exact_bisection
#print axioms DPCut.lift_near_bisection
#print axioms DPCut.odd_bisection_optimum
#print axioms DPCut.odd_bisection_solver
#print axioms DPCut.private_bisection
#print axioms DPCut.costedCappedRelease_law
#print axioms DPCut.costedCappedRelease_cost
#print axioms DPCut.cappedCostBound_polynomial
#print axioms DPCut.costedBestOf_law
#print axioms DPCut.costedBestOf_cost
#print axioms DPCut.LSWApplications.costedCC_law
#print axioms DPCut.LSWApplications.costedCC_cost
#print axioms DPCut.costedHierarchy_law
#print axioms DPCut.costedHierarchy_cost
#print axioms DPCut.hierarchy_reduction_runtime
#print axioms DPCut.cc_reduction_runtime
#print axioms DPCut.max_k_reduction_runtime
#print axioms DPCut.constrained_reduction_runtime

#print axioms DPCut.ConfiguredLSW.solve_failure
#print axioms DPCut.ConfiguredLSW.solve_cost
#print axioms DPCut.CappedReplacement.innerLoop_bounded_eq
#print axioms DPCut.CappedReplacement.outerLoop_bounded_eq
#print axioms DPCut.CappedReplacement.outerLoop_tv
#print axioms DPCut.CappedReplacement.costedRelease_law
#print axioms DPCut.CappedReplacement.costedRelease_cost
#print axioms DPCut.CappedLSW.witness_tv
#print axioms DPCut.CappedLSW.run_tv
#print axioms DPCut.CappedLSW.run_capped
#print axioms DPCut.CappedLSW.run_private
#print axioms DPCut.CappedLSW.run_utility
#print axioms DPCut.CappedLSW.run_cost
#print axioms DPCut.CappedLSW.cc_cost_polynomial
#print axioms DPCut.LSWApplications.ccPrivateKernel_private
#print axioms DPCut.LSWApplications.ccPrivateKernel_utility
#print axioms DPCut.LSWApplications.costedPostprocess_law
#print axioms DPCut.LSWApplications.postprocess_private
#print axioms DPCut.LSWApplications.postprocess_tv
#print axioms DPCut.LSWApplications.constrained_utility
#print axioms DPCut.LSWApplications.max_k_utility
#print axioms DPCut.LSWApplications.hierarchy_utility

#print axioms DPCut.CappedLSW.cost_polynomial
#print axioms DPCut.CappedLSW.capped_release_of_lsw
#print axioms DPCut.LSWApplications.private_cc_reduction
#print axioms DPCut.LSWApplications.theorem30
#print axioms DPCut.LSWApplications.corollary31
#print axioms DPCut.LSWApplications.private_correlation_clustering
#print axioms DPCut.LSWApplications.theorem32
#print axioms DPCut.LSWApplications.private_max_cut
#print axioms DPCut.LSWApplications.constrained_cut_general
#print axioms DPCut.LSWApplications.theorem34
#print axioms DPCut.LSWApplications.theorem36

/-! Regression check: the public runtime proofs must not depend on either
legacy SDP-oracle contract, including through helper proofs or definitions. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[``DPCut.hierarchy_reduction_runtime,
    ``DPCut.cc_reduction_runtime, ``DPCut.max_k_reduction_runtime,
    ``DPCut.constrained_reduction_runtime,
    ``DPCut.CappedLSW.cost_polynomial,
    ``DPCut.CappedLSW.capped_release_of_lsw,
    ``DPCut.LSWApplications.private_cc_reduction,
    ``DPCut.LSWApplications.theorem30,
    ``DPCut.LSWApplications.corollary31,
    ``DPCut.LSWApplications.private_correlation_clustering,
    ``DPCut.LSWApplications.theorem32,
    ``DPCut.LSWApplications.private_max_cut,
    ``DPCut.LSWApplications.constrained_cut_general,
    ``DPCut.LSWApplications.theorem34,
    ``DPCut.LSWApplications.theorem36]
  let forbidden : Array Name := #[``DPCut.ExactSDPOracleCost, ``DPCut.ApproxSDPOracle]
  let mut pending := roots
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless visited.contains name do
      visited := visited.insert name
      if forbidden.contains name then
        throwError "Application runtime depends on a legacy SDP oracle: {name}"
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet do
          -- Imported Lean/mathlib declarations cannot depend on this project.
          if Name.isPrefixOf `DPCut (privateToUserName dep) then
            pending := pending.push dep
  logInfo "Application runtime dependency audit passed: no legacy SDP-oracle contracts."
