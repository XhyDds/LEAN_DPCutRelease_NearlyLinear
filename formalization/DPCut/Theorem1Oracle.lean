import DPCut.ApproxSDPRuntime

/-!
Theorem 1 in the explicitly requested costed real-arithmetic oracle model.
The main entry point uses a feasible approximate optimizer with a requested
objective gap and an explicit polynomial cost in dimension and logarithmic
inverse accuracy. Gaussian/vector block costs remain those of `CostedProgram`.
The former exact-oracle result is retained as `theorem1_exact_oracle`.
Neither version asserts a finite-bit or arithmetic-only SDP implementation.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- One uniform program, rather than a different program for each input size. -/
inductive RealReleaseProgram where
  | fullRelease

def RealReleaseProgram.runExact {n : ℕ} (sdp : ExactSDPOracleCost) (_program : RealReleaseProgram)
    (p : Parameters) (w : Weights n) : CostedLaw (Weights n) := costedFullRelease sdp p w

/-- Assigned cost is the costed program's supremum over all intermediate values.
Realization is exact equality to its interpreted probability law. -/
def realArithmeticExactOracleModel (sdp : ExactSDPOracleCost) : ComputationalModel where
  Program := RealReleaseProgram
  realizes n program p M := ∀ w : Weights n, M w = (program.runExact sdp p w).law
  cost _ program p w := (program.runExact sdp p w).cost

/-- **Theorem 1**, relative to the explicit costed exact-SDP oracle contract.
Privacy and accuracy are unconditional; the cost clause uses assigned oracle prices, not execution steps. -/
theorem theorem1_exact_oracle (sdp : ExactSDPOracleCost) :
    MainTheoremStatement (realArithmeticExactOracleModel sdp) := by
  obtain ⟨Ctime, hCtime, degree, htime⟩ := fullCostBound_polynomial sdp
  refine ⟨(2 : ℝ) ^ 166, Ctime, degree, RealReleaseProgram.fullRelease, by positivity, hCtime, ?_⟩
  intro n hn p hp
  refine ⟨fullReleaseKernel hn p hp, ?_, inferInstance, ?_, fullRelease_private hn hp, ?_⟩
  · intro w
    exact (costedFullRelease_law sdp p w).symm
  · intro w _
    exact fullReleaseLaw_nonnegative hn hp w
  · intro w hw
    exact ⟨(costedFullRelease_cost sdp p w).trans (htime n hn p hp), fullRelease_utility hn hp w hw⟩

def RealReleaseProgram.run {n : ℕ} (sdp : ApproxSDPOracle) (_program : RealReleaseProgram)
    (p : Parameters) (w : Weights n) : CostedLaw (Weights n) := costedApproxRelease sdp p w

/-- The same real-arithmetic block model, with an accuracy-dependent approximate
optimization primitive. The cost is a supremum over all intermediate values. -/
def realArithmeticOracleModel (sdp : ApproxSDPOracle) : ComputationalModel where
  Program := RealReleaseProgram
  realizes n program p M := ∀ w : Weights n, M w = (program.run sdp p w).law
  cost _ program p w := (program.run sdp p w).cost

/-- **Theorem 1 with approximate optimization.** The mechanism actually samples
from the approximate covariance. Both its statistical guarantees and its uniform
polynomial assigned-cost bound are proved relative to the explicit primitive contract. -/
theorem theorem1 (sdp : ApproxSDPOracle) : MainTheoremStatement (realArithmeticOracleModel sdp) := by
  obtain ⟨Ctime, hCtime, degree, htime⟩ := approxReleaseCostBound_polynomial sdp
  refine ⟨(2 : ℝ) ^ 178, Ctime, degree, RealReleaseProgram.fullRelease, by positivity, hCtime, ?_⟩
  intro n hn p hp
  refine ⟨approxReleaseKernel sdp hn p hp, ?_, inferInstance, ?_, approxRelease_private sdp hn p hp, ?_⟩
  · intro w
    rfl
  · intro w _
    exact approxRelease_nonnegative sdp hn p hp w
  · intro w hw
    exact ⟨(costedApproxRelease_cost sdp p w).trans (htime n hn p hp),
      approxRelease_utility sdp hn p hp w hw⟩

end DPCut
