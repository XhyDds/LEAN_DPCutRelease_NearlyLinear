import DPCut.SDPRuntimeData
import DPCut.ApproxSDPRelease

/-! A uniform family of approximate solvers derived from the explicit LSW
hypothesis. Public timeouts turn expected runtime into worst-case runtime. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

structure CuttingPlaneFamily where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  degree : ℕ
  algorithm : ∀ (n : ℕ) (_hn : 2 ≤ n) (lam B ε : ℝ) (_hlam : 0 ≤ lam) (_hB : 0 ≤ B),
    0 < ε → ε ≤ 1/2 → TimedAlgorithm (Weights n) (SDPCoordinates.Space n)
  accurate : ∀ n hn lam B ε hlam hB hε hεhalf D,
    ∀ᵐ z ∂(algorithm n hn lam B ε hlam hB hε hεhalf).completed D,
      LSW.Accurate (SDPCoordinates.problem hn hlam hB) ε D z.2
  expected : ∀ n hn lam B ε hlam hB hε hεhalf D,
    (algorithm n hn lam B ε hlam hB hε hεhalf).expectedCost D ≤
      ENNReal.ofReal (coefficient * sdpLSWScale n lam B ε ^ degree)

/-- This family is constructed from LSW and the allowed linear-algebra
primitives; it is not an additional external solver assumption. -/
theorem cuttingPlaneFamily_exists (hLSW : LSWStatement) (P : LinearAlgebraPrimitives) :
    Nonempty CuttingPlaneFamily := by
  obtain ⟨C,hC,d,h⟩ := lsw_sdp hLSW P
  choose A ha hc using h
  exact ⟨⟨C,hC,d,A,ha,hc⟩⟩

def cuttingPlaneFamily (hLSW : LSWStatement) (P : LinearAlgebraPrimitives) : CuttingPlaneFamily :=
  Classical.choice (cuttingPlaneFamily_exists hLSW P)

def solverScale (n : ℕ) (p : Parameters) : ℝ :=
  sdpLSWScale n (fullRunConfig n (precisionParameters p)).oracle.lam
    (publicObjectiveBound n (precisionParameters p)) (solverAccuracy n p)

def solverFuel (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : ℕ :=
  ⌈2 * F.coefficient * solverScale n p ^ F.degree⌉₊ + 1

def solverCost (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  solverRestarts n p * (solverFuel F n p + 1) + SDPCoordinates.oracleCharge n

lemma solverFuel_pos (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : 0 < solverFuel F n p := by
  unfold solverFuel; omega

lemma solverFuel_mean (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) :
    ENNReal.ofReal (F.coefficient * solverScale n p ^ F.degree) ≤ (solverFuel F n p : ℝ≥0∞)/2 := by
  have hceil : 2 * F.coefficient * solverScale n p ^ F.degree ≤ (solverFuel F n p : ℝ) :=
    (Nat.le_ceil _).trans (by simp [solverFuel])
  have hh : F.coefficient * solverScale n p ^ F.degree ≤ (solverFuel F n p : ℝ)/2 := by linarith
  have h := ENNReal.ofReal_le_ofReal hh
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat] using h

namespace CuttingPlaneFamily
variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def releaseAlgorithm : TimedAlgorithm (Weights n) (SDPCoordinates.Space n) :=
  F.algorithm n hn (fullRunConfig n (precisionParameters p)).oracle.lam
    (publicObjectiveBound n (precisionParameters p)) (solverAccuracy n p)
    (by linarith [(approxConfig_bounds hn hp).lam_lower])
    (publicObjectiveBound_nonneg hn (precisionParameters_valid hp))
    (solverAccuracy_bounds hn hp).1 (solverAccuracy_bounds hn hp).2

def solve (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  SDPCoordinates.solve hn (F.releaseAlgorithm hn p hp) (solverFuel F n p) (solverRestarts n p) D

lemma measurable_solve : Measurable (fun D => (F.solve hn p hp D).law) :=
  SDPCoordinates.measurable_solve hn _ _ _

instance solve_probability (D : Weights n) : IsProbabilityMeasure (F.solve hn p hp D).law :=
  SDPCoordinates.solve_probability hn _ _ _ _

lemma solve_cost (D : Weights n) : (F.solve hn p hp D).cost ≤ solverCost F n p :=
  SDPCoordinates.solve_cost hn _ _ _ _

lemma solve_failure (D : Weights n) :
    (F.solve hn p hp D).law {X |
      (fullRunConfig n (precisionParameters p)).oracle.lam * (approximationRadius n p/2)^2 / (2*(n:ℝ)^4) <
        optimum (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) -
        objective (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) X.val}
      ≤ ENNReal.ofReal (approximationRadius n p/2) := by
  have hm : (F.releaseAlgorithm hn p hp).expectedCost D ≤ (solverFuel F n p : ℝ≥0∞)/2 :=
    (F.expected n hn (fullRunConfig n (precisionParameters p)).oracle.lam
      (publicObjectiveBound n (precisionParameters p)) (solverAccuracy n p)
      _ _ _ _ D).trans (solverFuel_mean F n p)
  have ha := F.accurate n hn (fullRunConfig n (precisionParameters p)).oracle.lam
    (publicObjectiveBound n (precisionParameters p)) (solverAccuracy n p)
    (by linarith [(approxConfig_bounds hn hp).lam_lower])
    (publicObjectiveBound_nonneg hn (precisionParameters_valid hp))
    (solverAccuracy_bounds hn hp).1 (solverAccuracy_bounds hn hp).2
  have hf := SDPCoordinates.solve_failure hn _ _ (F.releaseAlgorithm hn p hp) ha
    (solverFuel_pos F n p) (solverRestarts n p) D hm
  have hg := solverAccuracy_le_gap (n:=n) (p:=p)
    (show 1 ≤ (fullRunConfig n (precisionParameters p)).oracle.lam by linarith [(approxConfig_bounds hn hp).lam_lower])
  exact (measure_mono (fun X hX => lt_of_le_of_lt hg hX)).trans
    (hf.trans (solverRestarts_failure hp))

end CuttingPlaneFamily
end DPCut
