import DPCut.Definitions
import DPCut.Algorithms
import DPCut.Privacy
import DPCut.Statements
import DPCut.Utility
import DPCut.Applications
import DPCut.Lemma10
import DPCut.Lemma11
import DPCut.Lemma12
import DPCut.Lemma13
import DPCut.Lemma14
import DPCut.Lemma15
import DPCut.Lemma16
import DPCut.Lemma17
import DPCut.Lemma18
import DPCut.Lemma19
import DPCut.Lemma20
import DPCut.Lemma21
import DPCut.Lemma22
import DPCut.Lemma23
import DPCut.MassClipping
import DPCut.EllipsoidFeasibility
import DPCut.CovarianceApproximation
import DPCut.OptimizerTV
import DPCut.Theorem1
import DPCut.Theorem1Machine
import DPCut.Theorem1LSW
import DPCut.Theorem1Oracle
import DPCut.Theorem38
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
import DPCut.PrivateBisection
import DPCut.AppendixRuntime
import DPCut.ImplementedApplications

/-!
# Private cut release

Root module of the Lean formalization of the paper "Polynomial-Time Differentially
Private Synthetic Graph Release with Nearly-Linear Additive Error". It imports every
module of the library. The main results are `DPCut.theorem1_machine` (Theorem 1),
`DPCut.theorem38` (Theorem 38), `DPCut.lemma10` to `DPCut.lemma23`, and the
Appendix C results; see `README.md`. `Audit.lean` checks their axioms and dependencies.
-/
