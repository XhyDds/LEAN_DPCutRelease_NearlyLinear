import DPCut.Theorem1LSW

/-! LSW is a proposition parameter, never an axiom or an admitted theorem.
The reduction and full release/assigned-cost theorem are audited. This does
not establish that the cost model captures actual running time. -/
#check DPCut.LSWStatement
#check DPCut.LinearAlgebraPrimitives
#check DPCut.theorem1_of_lsw
#print axioms DPCut.TimedAlgorithm.timeout_failure_le_half
#print axioms DPCut.TimedAlgorithm.restart_failure_le
#print axioms DPCut.objective_tangent_upper
#print axioms DPCut.objective_concaveOn
#print axioms DPCut.objective_range_bound
#print axioms DPCut.SDPCoordinates.inner_ball
#print axioms DPCut.SDPCoordinates.encode_mem
#print axioms DPCut.SDPCoordinates.answer_correct
#print axioms DPCut.lsw_sdp
#print axioms DPCut.SDPCoordinates.safeMatrix_val_primitive
#print axioms DPCut.SDPCoordinates.solve_failure
#print axioms DPCut.SDPCoordinates.solve_law
#print axioms DPCut.SDPCoordinates.solve_cost
#print axioms DPCut.cuttingPlaneFamily_implementation
#print axioms DPCut.CuttingPlaneFamily.solve_failure
#print axioms DPCut.full_sdp_magnitude_bounds
#print axioms DPCut.solverCost_polynomial
#print axioms DPCut.OracleReplacement.outerLoop_bounded_eq
#print axioms DPCut.LSWRelease.bounded_fullRelease_eq
#print axioms DPCut.LSWRelease.witness_tv
#print axioms DPCut.LSWRelease.run_tv
#print axioms DPCut.LSWRelease.run_private
#print axioms DPCut.LSWRelease.run_utility
#print axioms DPCut.LSWRelease.costBound_polynomial
#print axioms DPCut.theorem1_of_lsw
