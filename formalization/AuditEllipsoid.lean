import DPCut.EllipsoidFeasibility
import DPCut.MassClipping

/-! These are proved algorithmic/geometric statements, with the separation
oracle as an explicit input. Only the standard foundational axioms are used. -/
#print axioms DPCut.clipNoisyMass_eq_on_good
#print axioms DPCut.clipped_mass_bounds
#print axioms DPCut.clipNoisyMass_le_cap
#print axioms DPCut.initialEstimate_mass_le
#print axioms DPCut.mwUpdate_mass_le
#print axioms DPCut.clipped_discrepancy_bound
#print axioms DPCut.EllipsoidMethod.centralCut_contains
#print axioms DPCut.EllipsoidMethod.det_axialMap
#print axioms DPCut.EllipsoidMethod.log_det_axial_update_le
#print axioms DPCut.EllipsoidMethod.Ellipsoid.volume_region
#print axioms DPCut.EllipsoidMethod.Ellipsoid.size_ge_of_ball_subset
#print axioms DPCut.EllipsoidMethod.Ellipsoid.log_size_cut_le
#print axioms DPCut.EllipsoidMethod.Ellipsoid.unitNormal_valid
#print axioms DPCut.EllipsoidMethod.run_failure_invariant
#print axioms DPCut.EllipsoidMethod.run_iterationBudget_success
#print axioms DPCut.EllipsoidMethod.feasible_of_balls
#print axioms DPCut.EllipsoidMethod.oracleCalls_le
#print axioms DPCut.EllipsoidMethod.ballIterationBudget_le
