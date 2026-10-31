import DPCut.GaussianDensity
import DPCut.LaplaceDensity
import DPCut.OracleGoodEvent
import DPCut.ConditioningPrivacy
import Mathlib.MeasureTheory.Group.Prod

/-! Joint law of a Gaussian batch and its noisy score for Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut

abbrev TrialSample (n k : ℕ) := (Fin k → Fin n → ℝ) × ℝ

lemma measurable_witness_score {n k : ℕ} (D : Weights n) :
    Measurable (fun z : Fin k → Fin n → ℝ => pairing D (clippedWitness z)) := by
  exact Finset.measurable_sum _ fun e _ => (measurable_clippedWitness e).const_mul _

def scoreShear {n k : ℕ} (D : Weights n) : TrialSample n k ≃ᵐ TrialSample n k where
  toFun := fun p => (p.1, pairing D (clippedWitness p.1) + p.2)
  invFun := fun p => (p.1, p.2 - pairing D (clippedWitness p.1))
  left_inv := by intro p; simp
  right_inv := by intro p; simp
  measurable_toFun := measurable_fst.prodMk
    (((measurable_witness_score D).comp measurable_fst).add measurable_snd)
  measurable_invFun := measurable_fst.prodMk
    (measurable_snd.sub ((measurable_witness_score D).comp measurable_fst))

lemma scoreShear_preserves_volume {n k : ℕ} (D : Weights n) :
    MeasurePreserving (scoreShear (k := k) D) volume volume := by
  exact (MeasurePreserving.id (volume : Measure (Fin k → Fin n → ℝ))).skew_product
    (show Measurable (Function.uncurry (fun z y => pairing D (clippedWitness z) + y)) from
      ((measurable_witness_score D).comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall fun z =>
      (measurePreserving_add_left volume (pairing D (clippedWitness z))).map_eq)

def trialLaw {n : ℕ} (o : OracleConfig) (D : Weights n) : Measure (TrialSample n o.k) :=
  ((gaussianBatch (optimizer o.lam D) o.k).prod (laplace (1 / o.eps1))).map (scoreShear D)

def trialDensity {n : ℕ} (o : OracleConfig) (D : Weights n) (p : TrialSample n o.k) : ℝ :=
  (∏ j, gaussianDensity (optimizer o.lam D) (p.1 j)) *
    laplaceDensity (1 / o.eps1) (p.2 - pairing D (clippedWitness p.1))

lemma trialLaw_probability {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1) (D : Weights n) :
    IsProbabilityMeasure (trialLaw o D) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  exact Measure.isProbabilityMeasure_map (scoreShear D).measurable.aemeasurable

theorem trialLaw_withDensity {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (_hl : 0 < o.lam)
    (D : Weights n) :
    trialLaw o D = volume.withDensity (fun p => ENNReal.ofReal (trialDensity o D p)) := by
  have hp := feasible_posDef hn (optimizer_isOptimizer hn o.lam D).1
  have hg : Measurable (fun z : Fin o.k → Fin n → ℝ =>
      ENNReal.ofReal (∏ j, gaussianDensity (optimizer o.lam D) (z j))) := by
    fun_prop
  have hn' : Measurable (fun y => ENNReal.ofReal (laplaceDensity (1 / o.eps1) y)) :=
    (continuous_laplaceDensity _).measurable.ennreal_ofReal
  have hv : ((volume : Measure (Fin o.k → Fin n → ℝ)).prod volume).map (scoreShear D) =
      volume := (scoreShear_preserves_volume D).map_eq
  rw [trialLaw, gaussianBatch_withDensity hp, laplace, prod_withDensity hg hn',
    map_withDensity_equiv _ (scoreShear D) (show Measurable (fun p : TrialSample n o.k =>
      ENNReal.ofReal (∏ j, gaussianDensity (optimizer o.lam D) (p.1 j)) *
      ENNReal.ofReal (laplaceDensity (1 / o.eps1) p.2)) from
        (hg.comp measurable_fst).mul (hn'.comp measurable_snd)),
    hv]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact (ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _)).symm

lemma trialDensity_ratio {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D D' ζ r : Weights n) (hr : IsMask r)
    (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e)
    (p : TrialSample n o.k)
    (hg : CommonTrialGood (optimizer o.lam D) (optimizer o.lam D')
      (o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) p.1) :
    trialDensity o D p ≤
      Real.exp (5 * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) *
        trialDensity o D' p := by
  let W := oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')
  have hb := ((batch_density_bound_iff _ _ p.1 (o.eps1 * W)).mpr hg.1).2
  have hs := score_sensitivity_le_charge D D' ζ r (clippedWitness p.1)
    (queryMax (optimizer o.lam D) (optimizer o.lam D')) hr hξ
    (fun e => ⟨(clippedWitness_bounds p.1 e).1, (hg.2 e).2⟩)
  have hl := laplaceDensity_shift_le (one_div_pos.mpr he)
    (pairing D (clippedWitness p.1)) (pairing D' (clippedWitness p.1)) p.2
  have he' : |pairing D (clippedWitness p.1) - pairing D' (clippedWitness p.1)| /
      (1 / o.eps1) ≤ 4 * o.eps1 * W := by
    dsimp [W, oracleSensitivity]
    simpa only [div_eq_mul_inv, one_mul, inv_inv, mul_comm _ o.eps1, mul_assoc] using
      mul_le_mul_of_nonneg_left hs he.le
  have hn := laplaceDensity_pos (one_div_pos.mpr he)
    (p.2 - pairing D' (clippedWitness p.1))
  have hll := hl.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he') hn.le)
  have h := mul_le_mul hb hll (laplaceDensity_pos (one_div_pos.mpr he)
    (p.2 - pairing D (clippedWitness p.1))).le
    (mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _))
  dsimp [trialDensity]
  convert h using 1
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

def trialGood {n : ℕ} (o : OracleConfig) (D D' ζ r : Weights n) : Set (TrialSample n o.k) :=
  {p | CommonTrialGood (optimizer o.lam D) (optimizer o.lam D')
    (o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) p.1}

lemma measurableSet_trialGood {n : ℕ} (o : OracleConfig) (D D' ζ r : Weights n) :
    MeasurableSet (trialGood o D D' ζ r) :=
  measurable_fst (measurableSet_CommonTrialGood _ _ _)

lemma trialLaw_map_fst {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1) (D : Weights n) :
    (trialLaw o D).map Prod.fst = gaussianBatch (optimizer o.lam D) o.k := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  rw [trialLaw, Measure.map_map measurable_fst (scoreShear D).measurable]
  exact Measure.map_fst_prod.trans (by rw [measure_univ, one_smul])

lemma trialGood_swap {n : ℕ} (o : OracleConfig) (D D' ζ r : Weights n) :
    trialGood o D' D ζ r = trialGood o D D' ζ r := by
  ext p
  have hw : oracleSensitivity ζ r (optimizer o.lam D') (optimizer o.lam D) =
      oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D') := by
    simp only [oracleSensitivity, queryMax, max_comm]
  simp only [trialGood, Set.mem_setOf_eq, hw]
  exact commonTrialGood_symm _ _ _ _

theorem trialLaw_restricted_private {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (D D' ζ r : Weights n) (hr : IsMask r)
    (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    Indistinguishable ((trialLaw o D).restrict (trialGood o D D' ζ r))
      ((trialLaw o D').restrict (trialGood o D D' ζ r))
      (5 * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) 0 := by
  rw [trialLaw_withDensity hn o hl, trialLaw_withDensity hn o hl]
  apply restricted_density_private _ _ _ (measurableSet_trialGood o D D' ζ r)
  intro p hp
  refine ⟨trialDensity_ratio o he D D' ζ r hr hξ p hp, ?_⟩
  have hp' : p ∈ trialGood o D' D ζ r := by rwa [trialGood_swap]
  have h := trialDensity_ratio o he D' D ζ r hr
    (fun e => by simpa only [abs_sub_comm] using hξ e) p hp'
  simpa only [oracleSensitivity, queryMax, max_comm] using h

theorem conditional_trial_private {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (D D' ζ r : Weights n) (hr : IsMask r)
    (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e)
    (h0 : trialLaw o D (trialGood o D D' ζ r) ≠ 0)
    (h1 : trialLaw o D' (trialGood o D D' ζ r) ≠ 0) :
    Indistinguishable ((trialLaw o D)[|trialGood o D D' ζ r])
      ((trialLaw o D')[|trialGood o D D' ζ r])
      (10 * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) 0 := by
  letI := trialLaw_probability o he D
  letI := trialLaw_probability o he D'
  convert conditioning_private (measurableSet_trialGood o D D' ζ r) h0 h1
    (trialLaw_restricted_private hn o hl he D D' ζ r hr hξ) using 1
  ring

end DPCut
