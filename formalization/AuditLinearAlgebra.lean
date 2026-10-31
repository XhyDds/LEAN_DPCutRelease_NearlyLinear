import DPCut.Theorem1LSW

/-! The implementation record is constructed; only LSW remains a hypothesis.
The global audit also traverses every helper and generated declaration. -/
#check DPCut.theorem1_of_lsw
#check DPCut.verifiedLinearAlgebra
#print axioms DPCut.MatrixElimination.psdWitness_correct
#print axioms DPCut.MatrixElimination.totalPSD_measurable
#print axioms DPCut.MatrixElimination.solve_correct
#print axioms DPCut.MatrixElimination.inverse_eq
#print axioms DPCut.MatrixElimination.factor_correct
#print axioms DPCut.MatrixElimination.determinant_correct
#print axioms DPCut.MatrixElimination.Counted.totalPSD_steps
#print axioms DPCut.MatrixElimination.Counted.inverse_steps
#print axioms DPCut.MatrixElimination.Counted.factor_steps
#print axioms DPCut.MatrixElimination.Counted.determinant_steps
#print axioms DPCut.SDPCoordinates.normal_formula
#print axioms DPCut.SDPCoordinates.Counted.answer_value
#print axioms DPCut.SDPCoordinates.Counted.answer_steps
#print axioms DPCut.SDPCoordinates.Counted.decode_value
#print axioms DPCut.SDPCoordinates.Counted.decode_steps
#print axioms DPCut.scalarProduct_law
#print axioms DPCut.scalarProduct_cost
#print axioms DPCut.verifiedGaussianBatch_law
#print axioms DPCut.verifiedGaussianBatch_cost
#print axioms DPCut.verifiedLinearAlgebra
#print axioms DPCut.theorem1_of_lsw
