import DPCut.ConfiguredLSWSolver
import DPCut.CappedReplacementCost

/-! A bounded-cost LSW witness implementation for the capped release.
Privacy/failure reserves are allocated before all adaptive calls. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut.CappedLSW

def config (n : ℕ) (p : Parameters) : RunConfig := cappedRunConfig n (precisionParameters p)
def objectiveBound (n : ℕ) : ℝ := 3 * Fintype.card (Edge n)
def errorBudget (n : ℕ) (p : Parameters) : ℕ :=
  let c := config n p
  4 * Fintype.card (Edge n) * c.T1 * c.T2 * (c.oracle.K+1) * (c.oracle.k+1)
def precisionIndex (n : ℕ) (p : Parameters) : ℕ :=
  ⌈16/(p.beta*p.delta)⌉₊ * (1+errorBudget n p) + 2

lemma precisionIndex_two_le (n : ℕ) (p : Parameters) : 2 ≤ precisionIndex n p := by
  unfold precisionIndex; omega

lemma oracle_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    OraclePrivacyBounds n (config n p).oracle :=
  (cappedConfig_inner_utility_bounds hn _ (precisionParameters_valid hp)).oracle_privacy

lemma product_budget_le {p : Parameters} (hp : p.Valid) : p.beta*p.delta/16 ≤ implementationTV p := by
  have hb := hp.2.2.2.2.2.2.1
  have hd := hp.2.2.2.2.1
  have hb1 : p.beta ≤ 1 := by linarith [hp.2.2.2.2.2.2.2]
  have hd1 : p.delta ≤ 1 := by linarith [hp.2.2.2.2.2.1]
  have he : Real.exp p.epsilon ≤ 3 :=
    (Real.exp_le_exp.mpr hp.2.2.2.1).trans (by linarith [Real.exp_one_lt_d9])
  unfold implementationTV
  apply le_min
  · nlinarith [mul_le_mul_of_nonneg_left hd1 hb.le]
  · apply (le_div_iff₀ (by positivity : 0 < 2*(1+Real.exp p.epsilon))).mpr
    have hprod : p.beta*p.delta ≤ p.delta := mul_le_of_le_one_left hd.le hb1
    nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hb.le hd.le)]

lemma precision_budget {n : ℕ} {p : Parameters} (hp : p.Valid) :
    (errorBudget n p:ℝ) * (precisionIndex n p:ℝ)⁻¹ ≤ implementationTV p := by
  have hp0 : 0 < p.beta*p.delta := mul_pos hp.2.2.2.2.2.2.1 hp.2.2.2.2.1
  have hN : (0:ℝ) < precisionIndex n p := by
    exact_mod_cast (show 0 < precisionIndex n p from lt_of_lt_of_le (by omega) (precisionIndex_two_le n p))
  have hc := Nat.le_ceil (16/(p.beta*p.delta))
  have hpre : 16/(p.beta*p.delta) * (1+(errorBudget n p:ℝ)) ≤ (precisionIndex n p:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 1+errorBudget n p by positivity)
    simp only [precisionIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hpre hp0.le
  have heq : (p.beta*p.delta)*(16/(p.beta*p.delta)*(1+(errorBudget n p:ℝ))) =
      16*(1+(errorBudget n p:ℝ)) := by
      field_simp [hp.2.2.2.2.2.2.1.ne', hp.2.2.2.2.1.ne']
  rw [heq] at hh
  apply le_trans _ (product_budget_le hp)
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hN).mpr
  nlinarith

variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def solve (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  ConfiguredLSW.solve F hn (precisionIndex_two_le n p)
    (show 0 ≤ (config n p).oracle.lam by linarith [(oracle_bounds hn hp).lam_lower])
    (show 0 ≤ objectiveBound n by unfold objectiveBound; positivity) D

lemma measurable_solve : Measurable (fun D => (solve F hn p hp D).law) :=
  ConfiguredLSW.measurable_solve F hn _ _ _
instance solve_probability (D : Weights n) : IsProbabilityMeasure (solve F hn p hp D).law :=
  ConfiguredLSW.solve_probability F hn _ _ _ D

def witness (D r : Weights n) : CostedLaw (Option (Weights n)) :=
  RandomizedWitness.run (config n p).oracle (solve F hn p hp) (objectiveBound n) D r

def witnessKernel : OracleReplacement.WitnessKernel n :=
  ⟨fun q => (witness F hn p hp q.1 q.2).law,
    RandomizedWitness.measurable_run hn _ (oracle_bounds hn hp).eps_pos _
      (measurable_solve F hn p hp) _⟩
instance witnessKernel_markov : IsMarkovKernel (witnessKernel F hn p hp) :=
  ⟨fun q => RandomizedWitness.run_probability hn _ (oracle_bounds hn hp).eps_pos _ _ q.1 q.2⟩

def witnessCost (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  vectorBlockCost n + ConfiguredLSW.cost F n (precisionIndex n p) (config n p).oracle.lam (objectiveBound n) +
    (config n p).oracle.K * trialCostBound n (config n p).oracle

lemma witness_cost (D r : Weights n) : (witness F hn p hp D r).cost ≤ witnessCost F n p :=
  RandomizedWitness.run_cost _ _ (ConfiguredLSW.solve_cost F hn _ _ _) D r

def witnessError (n : ℕ) (p : Parameters) : ℝ :=
  ((config n p).oracle.K+1) * ((config n p).oracle.k+1) * (precisionIndex n p:ℝ)⁻¹

lemma witnessError_nonneg (n : ℕ) (p : Parameters) : 0 ≤ witnessError n p := by
  unfold witnessError; positivity

lemma witness_tv (D r : Weights n) : TVClose (witness F hn p hp D r).law
    (findWitness (config n p).oracle (boundedObjective (objectiveBound n) D) r) (witnessError n p) := by
  have ho := oracle_bounds hn hp
  obtain ⟨hμ, hμh⟩ := ConfiguredLSW.radius_bounds (precisionIndex_two_le n p)
  have hbad := ConfiguredLSW.solve_failure F hn (precisionIndex_two_le n p)
    (show 0 ≤ (config n p).oracle.lam by linarith [ho.lam_lower])
    (show 0 ≤ objectiveBound n by unfold objectiveBound; positivity)
    (show 1 ≤ (config n p).oracle.lam by linarith [ho.lam_lower])
  have ht := RandomizedWitness.law_tv hn (config n p).oracle ho.eps_pos
    (by linarith [ho.lam_lower]) ho.batch_pos
    (show 0 < (precisionIndex n p:ℝ)⁻¹/2 by positivity)
    (show (precisionIndex n p:ℝ)⁻¹/2 ≤ 1/2 by linarith) (by positivity : 0 ≤ (precisionIndex n p:ℝ)⁻¹/2)
    (solve F hn p hp) hbad D r
  apply ht.mono
  have hs : Real.sqrt (config n p).oracle.k ≤ (config n p).oracle.k+1 := by
    have := Real.sq_sqrt (Nat.cast_nonneg (config n p).oracle.k)
    have := Real.sqrt_nonneg ((config n p).oracle.k:ℝ)
    nlinarith [sq_nonneg (Real.sqrt (config n p).oracle.k - 1)]
  unfold witnessError
  nlinarith [mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ((config n p).oracle.K:ℝ) * (precisionIndex n p:ℝ)⁻¹ by positivity)]

lemma total_error {n : ℕ} {p : Parameters} (hp : p.Valid) :
    (config n p).T1 * ((config n p).T2 * ((Fintype.card (Edge n):ℝ)*(2*witnessError n p))) ≤ implementationTV p := by
  apply le_trans _ (precision_budget (n:=n) hp)
  have h0 := witnessError_nonneg n p
  dsimp [errorBudget, witnessError]
  push_cast
  nlinarith [show 0 ≤ (Fintype.card (Edge n):ℝ) * (config n p).T1 * (config n p).T2 *
    (((config n p).oracle.K:ℝ)+1) * (((config n p).oracle.k:ℝ)+1) * (precisionIndex n p:ℝ)⁻¹ by positivity]

end DPCut.CappedLSW
