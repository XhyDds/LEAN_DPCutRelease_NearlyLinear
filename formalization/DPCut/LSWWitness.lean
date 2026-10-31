import DPCut.RandomizedOracleTV
import DPCut.LSWPolynomialRuntime

/-! The derived LSW solver is used in the actual witness program. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut.LSWRelease

variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def witness (D r : Weights n) : CostedLaw (Option (Weights n)) :=
  RandomizedWitness.run (fullRunConfig n (precisionParameters p)).oracle (F.solve hn p hp)
    (publicObjectiveBound n (precisionParameters p)) D r

def witnessKernel : OracleReplacement.WitnessKernel n :=
  ⟨fun q => (witness F hn p hp q.1 q.2).law,
    RandomizedWitness.measurable_run hn _ (approxConfig_bounds hn hp).eps_pos
      _ (F.measurable_solve hn p hp) _⟩

instance witnessKernel_markov : IsMarkovKernel (witnessKernel F hn p hp) := by
  constructor
  intro q
  exact RandomizedWitness.run_probability hn _ (approxConfig_bounds hn hp).eps_pos _ _ q.1 q.2

def witnessCost (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  vectorBlockCost n + solverCost F n p + (fullRunConfig n (precisionParameters p)).oracle.K *
    trialCostBound n (fullRunConfig n (precisionParameters p)).oracle

lemma witness_cost (D r : Weights n) : (witness F hn p hp D r).cost ≤ witnessCost F n p :=
  RandomizedWitness.run_cost _ _ (F.solve_cost hn p hp) D r

include hn hp in
lemma fullConfig_trials_pos : 0 < (fullRunConfig n (precisionParameters p)).oracle.K := by
  have hd := (approxConfig_bounds hn hp).delta_pos
  have heq : (fullRunConfig n (precisionParameters p)).oracle.delta1 =
      (fullRunConfig n (precisionParameters p)).deltaGE /
        (20*(n:ℝ)^2*(fullRunConfig n (precisionParameters p)).oracle.K) := rfl
  rw [heq] at hd
  by_contra h
  have hz : (fullRunConfig n (precisionParameters p)).oracle.K = 0 := by omega
  simp [hz] at hd

lemma witness_tv (D r : Weights n) :
    TVClose (witness F hn p hp D r).law
      (findWitness (fullRunConfig n (precisionParameters p)).oracle
        (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) r)
      ((fullRunConfig n (precisionParameters p)).oracle.K *
        (2 * Real.sqrt (fullRunConfig n (precisionParameters p)).oracle.k * approximationRadius n p)) := by
  let c := fullRunConfig n (precisionParameters p)
  have ho : OraclePrivacyBounds n c.oracle := approxConfig_bounds hn hp
  obtain ⟨hr, hrhalf⟩ := approximationRadius_bounds (n:=n) hp
  have ht := RandomizedWitness.law_tv hn c.oracle ho.eps_pos
    (by linarith [ho.lam_lower]) ho.batch_pos
    (show 0 < approximationRadius n p/2 by linarith)
    (show approximationRadius n p/2 ≤ 1/2 by linarith)
    (show 0 ≤ approximationRadius n p/2 by linarith)
    (F.solve hn p hp) (F.solve_failure hn p hp) D r
  apply ht.mono
  have hK : (1:ℝ) ≤ c.oracle.K := by exact_mod_cast fullConfig_trials_pos hn p hp
  have hk : (1:ℝ) ≤ c.oracle.k := by exact_mod_cast ho.batch_pos
  have hsqrt : 1 ≤ Real.sqrt c.oracle.k := by
    have := Real.sqrt_le_sqrt hk
    simpa using this
  have hprod : 1 ≤ (c.oracle.K:ℝ)*Real.sqrt c.oracle.k := hK.trans (le_mul_of_one_le_right (by linarith) hsqrt)
  nlinarith [mul_le_mul_of_nonneg_right hprod hr.le]

lemma witnessCost_polynomial : PolynomialRuntimeBound (witnessCost F) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 100 (by norm_num)
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := h100.mul (polynomial_vertices.pow 2)
  obtain ⟨_,_,hK,hk⟩ := polynomial_full_parameters
  have hG := (hB.mul polynomial_vertices).mul (hk.precision.add h1)
  have hTrial : PolynomialRuntimeBound (fun n p => trialCostBound n (fullRunConfig n (precisionParameters p)).oracle) :=
    (hG.add h1).add hB
  exact (hB.add (solverCost_polynomial F)).add (hK.precision.mul hTrial)

end DPCut.LSWRelease
