import DPCut.ApproxSDPRelease

/-! Polynomial assigned-cost bounds, including the requested optimizer accuracy.
The primitive contract does not connect these costs to execution steps. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

def approxReleaseCostBound (sdp : ApproxSDPOracle) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  2 * vectorBlockCost n + OracleReplacement.fullCostBound
    (ApproxSDPCosted.witnessBound sdp (approximationRadius n p) n
      (fullRunConfig n (precisionParameters p)).oracle) n (precisionParameters p)

theorem costedApproxRelease_cost {n : ℕ} (sdp : ApproxSDPOracle) (p : Parameters) (w : Weights n) :
    (costedApproxRelease sdp p w).cost ≤ approxReleaseCostBound sdp n p := by
  let q := precisionParameters p
  let o := (fullRunConfig n q).oracle
  let μ := approximationRadius n p
  have h := OracleReplacement.costedFullRelease_cost (ApproxSDPCosted.witness sdp μ o)
    (ApproxSDPCosted.witnessBound sdp μ n o) (ApproxSDPCosted.witness_cost sdp μ o) q w
  calc
    _ ≤ vectorBlockCost n + (OracleReplacement.fullCostBound
        (ApproxSDPCosted.witnessBound sdp μ n o) n q + vectorBlockCost n) :=
      add_le_add_left (add_le_add_right h _) _
    _ = _ := by dsimp [approxReleaseCostBound, o, μ, q]; ring

theorem approxReleaseCostBound_polynomial (sdp : ApproxSDPOracle) :
    PolynomialRuntimeBound (approxReleaseCostBound sdp) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h2 : PolynomialRuntimeBound (fun _ _ => (2 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 2 (by norm_num)
  have h3 : PolynomialRuntimeBound (fun _ _ => (3 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 3 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100 : ℝ≥0∞)) := by
    simpa using PolynomialRuntimeBound.constant 100 (by norm_num)
  obtain ⟨hT1, hT2, hK, hk⟩ := polynomial_full_parameters
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := by
    simpa only [vectorBlockCost, pow_two] using h100.mul (polynomial_vertices.mul polynomial_vertices)
  have hG : PolynomialRuntimeBound (fun n p =>
      gaussianBatchCost n (fullRunConfig n (precisionParameters p)).oracle.k) :=
    (hB.mul polynomial_vertices).mul (hk.precision.add h1)
  have hTrial : PolynomialRuntimeBound (fun n p =>
      trialCostBound n (fullRunConfig n (precisionParameters p)).oracle) := (hG.add h1).add hB
  have hWitness : PolynomialRuntimeBound (fun n p =>
      ApproxSDPCosted.witnessBound sdp (approximationRadius n p) n
        (fullRunConfig n (precisionParameters p)).oracle) :=
    (hB.add (polynomial_approximateSolve sdp)).add (hK.precision.mul hTrial)
  have hAggregate := polynomial_edges.mul (hB.add (h2.mul hWitness))
  have hInner := hT2.precision.mul (hAggregate.add hB)
  have hOuter := hT1.precision.mul ((h1.add hB).add hInner)
  exact (h2.mul hB).add (((h3.mul hB).add polynomial_edges).add hOuter)

end DPCut
