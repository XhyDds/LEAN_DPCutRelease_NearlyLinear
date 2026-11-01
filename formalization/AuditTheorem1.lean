import DPCut.Theorem1Oracle

/-! The oracle cost contract is an explicit theorem parameter, not an axiom.
Only propext, Classical.choice, and Quot.sound are expected transitively. -/
#check DPCut.theorem1_statistical
#check DPCut.theorem1_statistical_exists
#check DPCut.theorem1
#check DPCut.theorem1_exact_oracle
#print axioms DPCut.cutRelease_shared_private
#print axioms DPCut.parameter_choice
#print axioms DPCut.Adjacent.clipWeights
#print axioms DPCut.preprocessingThreshold_one_le
#print axioms DPCut.full_release_log_bound
#print axioms DPCut.full_release_error_bound
#print axioms DPCut.measurable_fullReleaseLaw
#print axioms DPCut.fullReleaseLaw_probability
#print axioms DPCut.fullReleaseLaw_nonnegative
#print axioms DPCut.fullRelease_private
#print axioms DPCut.fullRelease_accuracy_add
#print axioms DPCut.fullRelease_utility
#print axioms DPCut.theorem1_statistical
#print axioms DPCut.theorem1_statistical_exists
#print axioms DPCut.costedFindTrials_law
#print axioms DPCut.costedAggregateLoop_law
#print axioms DPCut.costedInnerLoop_law
#print axioms DPCut.costedOuterLoop_law
#print axioms DPCut.costedFullRelease_law
#print axioms DPCut.costedFullRelease_cost
#print axioms DPCut.oracle_sample_sizes_bound
#print axioms DPCut.full_runtime_parameter_bounds
#print axioms DPCut.fullCostBound_polynomial
#print axioms DPCut.theorem1_exact_oracle
#print axioms DPCut.objective_gap
#print axioms DPCut.approximate_gaussian
#print axioms DPCut.tvClose_of_klDiv_bound
#print axioms DPCut.approximateFindWitness_tv
#print axioms DPCut.precision_error_le
#print axioms DPCut.OracleReplacement.fullRelease_exact
#print axioms DPCut.OracleReplacement.fullRelease_tv
#print axioms DPCut.ApproxSDPOracle.witnessKernel_tv
#print axioms DPCut.ApproxSDPCosted.trials_law
#print axioms DPCut.ApproxSDPCosted.witness_cost
#print axioms DPCut.approximationBudget_error
#print axioms DPCut.polynomial_approximateSolve
#print axioms DPCut.costedApproxRelease_law
#print axioms DPCut.approxRelease_tv
#print axioms DPCut.approxRelease_nonnegative
#print axioms DPCut.approxRelease_private
#print axioms DPCut.approxRelease_utility
#print axioms DPCut.costedApproxRelease_cost
#print axioms DPCut.approxReleaseCostBound_polynomial
#print axioms DPCut.theorem1
