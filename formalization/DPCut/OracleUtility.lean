import DPCut.Lemma11
import DPCut.UtilityCertificate
import DPCut.LaplaceTail
import DPCut.FailureProbability
import DPCut.WitnessRetirement

/-! Utility of the actual finite-trial FindWitness oracle. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

structure OracleUtilityBounds (n : ℕ) (o : OracleConfig) : Prop where
  eps_pos : 0 < o.eps1
  lam_nonneg : 0 ≤ o.lam
  beta_pos : 0 < o.beta1
  beta_half : o.beta1 ≤ 1 / 2
  tau_eq : o.tau1 = Real.log (1 / o.beta1) / o.eps1
  k_pos : 0 < o.k
  k_size : 512 * Real.log (n : ℝ) ≤ o.k

lemma OracleUtilityBounds.tau_pos {n : ℕ} {o : OracleConfig} (ho : OracleUtilityBounds n o) :
    0 < o.tau1 := by
  rw [ho.tau_eq]
  exact (laplace_calibrated_tails ho.eps_pos ho.beta_pos (by linarith [ho.beta_half])).1

def WitnessSign {n : ℕ} (v : Weights n) (y : Option (Weights n)) : Prop :=
  y.elim True (fun g => 0 ≤ pairing v g)

lemma measurableSet_witnessSign {n : ℕ} (v : Weights n) :
    MeasurableSet {y | WitnessSign v y} :=
  measurableSet_option_elim (measurableSet_le measurable_const
    (show Measurable (fun g : Weights n => pairing v g) by unfold pairing; fun_prop))

lemma pairing_normalize_mask {n : ℕ} (r v g : Weights n) :
    pairing v (normalizeWitness r g) = pairing (hadamard r v) g / activeMaximum r g := by
  simp only [pairing, normalizeWitness, hadamard, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma activeMaximum_pos_of_score {n : ℕ} {r v g : Weights n} (hr : IsMask r)
    (hg : ∀ e, 0 ≤ g e) (hs : 0 < pairing (hadamard r v) g) : 0 < activeMaximum r g := by
  by_contra hp
  have hp' : activeMaximum r g ≤ 0 := le_of_not_gt hp
  have hz : pairing (hadamard r v) g = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : 0 < r e
    · have hg0 : g e = 0 := le_antisymm ((le_activeMaximum r g e he).trans hp') (hg e)
      simp [hg0]
    · have hr0 : r e = 0 := le_antisymm (le_of_not_gt he) (hr e).1
      simp [hadamard, hr0]
  linarith

lemma trial_wrong_sign_bound {n : ℕ} (o : OracleConfig) (ho : OracleUtilityBounds n o)
    (r v : Weights n) :
    trialLaw o (hadamard r v) {p | ¬WitnessSign v (acceptTrial o r p)} ≤
      ENNReal.ofReal (o.beta1 / 2) := by
  let D := hadamard r v
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr ho.eps_pos)
  have hP : MeasurableSet {p | ¬WitnessSign v (acceptTrial o r p)} :=
    ((measurable_acceptTrial_fixed o r) (measurableSet_witnessSign v)).compl
  have htail := (laplace_calibrated_tails ho.eps_pos ho.beta_pos
    (by linarith [ho.beta_half])).2.1
  rw [← ho.tau_eq] at htail
  have hsub : (scoreShear D) ⁻¹' {p | ¬WitnessSign v (acceptTrial o r p)} ⊆
      Set.univ ×ˢ Ioi o.tau1 := by
    rintro ⟨z, noise⟩ hp
    refine ⟨mem_univ _, ?_⟩
    change ¬WitnessSign v (acceptTrial o r (scoreShear D (z, noise))) at hp
    dsimp [acceptTrial, scoreShear] at hp
    split_ifs at hp with hs
    · have hb : pairing (hadamard r v) (clippedWitness z) < 0 := by
        change ¬0 ≤ pairing v (normalizeWitness r (clippedWitness z)) at hp
        rw [pairing_normalize_mask] at hp
        by_contra hb
        exact hp (div_nonneg (le_of_not_gt hb) hs.2.le)
      change o.tau1 < noise
      have hs1 : o.tau1 ≤ pairing (hadamard r v) (clippedWitness z) + noise := hs.1
      linarith
    · exact False.elim (hp trivial)
  change trialLaw o D _ ≤ _
  rw [trialLaw, Measure.map_apply (scoreShear D).measurable hP]
  calc
    _ ≤ ((gaussianBatch (optimizer o.lam D) o.k).prod (laplace (1 / o.eps1)))
        (Set.univ ×ˢ Ioi o.tau1) := measure_mono hsub
    _ = ENNReal.ofReal (o.beta1 / 2) := by
      rw [Measure.prod_prod, measure_univ, one_mul]
      letI := laplace_isProbabilityMeasure (one_div_pos.mpr ho.eps_pos)
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact congrArg ENNReal.ofReal htail

lemma trial_success_bound {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OracleUtilityBounds n o) (r v : Weights n) (hr : IsMask r)
    (hF : 4 * o.tau1 ≤ optimum o.lam (hadamard r v)) :
    (3 / 8192 : ℝ) ≤ prob (trialLaw o (hadamard r v)) {p | acceptTrial o r p ≠ none} := by
  let D := hadamard r v
  let X := optimizer o.lam D
  let G := {z : Fin o.k → Fin n → ℝ | ChiGood X z ∧
    pairing D (fractionalQuery X) / 2 ≤ pairing D (clippedWitness z)}
  have hg : (1 / 2048 : ℝ) ≤ prob (gaussianBatch X o.k) G :=
    chaos_joint_success hn o.k ho.k_pos ho.k_size D (optimizer_isOptimizer hn o.lam D).1
  have ht := (laplace_calibrated_tails ho.eps_pos ho.beta_pos
    (by linarith [ho.beta_half])).2.2
  rw [← ho.tau_eq] at ht
  have ht' : (3 / 4 : ℝ) ≤ prob (laplace (1 / o.eps1)) (Ici (-o.tau1)) := by
    linarith [ho.beta_half]
  have hsub : G ×ˢ Ici (-o.tau1) ⊆
      (scoreShear D) ⁻¹' {p | acceptTrial o r p ≠ none} := by
    rintro ⟨z, noise⟩ ⟨hz, hnoise⟩
    have hscore := optimum_le_optimizer_score hn ho.lam_nonneg D
    have hp : 0 < pairing D (clippedWitness z) := by
      have := ho.tau_pos
      dsimp [G, X] at hz
      change 4 * o.tau1 ≤ optimum o.lam D at hF
      linarith [hz.2]
    have ha : 0 < activeMaximum r (clippedWitness z) :=
      activeMaximum_pos_of_score hr (fun e => (clippedWitness_bounds z e).1) hp
    have hs : o.tau1 ≤ pairing D (clippedWitness z) + noise := by
      change -o.tau1 ≤ noise at hnoise
      change 4 * o.tau1 ≤ optimum o.lam D at hF
      dsimp [G, X] at hz
      linarith [hz.2]
    simp [acceptTrial, scoreShear, hs, ha]
  have hN : MeasurableSet {p : TrialSample n o.k | acceptTrial o r p ≠ none} :=
    ((measurable_acceptTrial_fixed o r) measurableSet_option_none).compl
  change (3 / 8192 : ℝ) ≤ prob (trialLaw o D) _
  rw [prob, trialLaw, Measure.map_apply (scoreShear D).measurable hN]
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr ho.eps_pos)
  have hm := measureReal_mono (μ := (gaussianBatch X o.k).prod (laplace (1 / o.eps1))) hsub
  rw [measureReal_prod_prod] at hm
  have hprod := mul_le_mul hg ht' (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (show 0 ≤ prob (gaussianBatch X o.k) G from ENNReal.toReal_nonneg)
  exact (show (3 / 8192 : ℝ) = (1 / 2048) * (3 / 4) by norm_num).trans_le (hprod.trans hm)

lemma findTrials_none_bound {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OracleUtilityBounds n o) (r v : Weights n) (hr : IsMask r)
    (hF : 4 * o.tau1 ≤ optimum o.lam (hadamard r v)) (t : ℕ) :
    findTrials o (hadamard r v) r t {none} ≤
      ENNReal.ofReal ((1 - 3 / 8192 : ℝ) ^ t) := by
  letI := trialLaw_probability o ho.eps_pos (hadamard r v)
  have hs := trial_success_bound hn o ho r v hr hF
  have hN : MeasurableSet {p : TrialSample n o.k | acceptTrial o r p = none} :=
    (measurable_acceptTrial_fixed o r) measurableSet_option_none
  have hc := measureReal_add_measureReal_compl (μ := trialLaw o (hadamard r v)) hN
  rw [measureReal_univ_eq_one] at hc
  have hb : prob (trialLaw o (hadamard r v)) {p | acceptTrial o r p = none} ≤ 1 - 3 / 8192 := by
    change prob _ _ + prob _ {p | acceptTrial o r p ≠ none} = 1 at hc
    linarith
  rw [findTrials_eq_repeatUntil o ho.eps_pos, repeatUntil_none (measurable_acceptTrial_fixed o r)]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 - 3 / 8192)]
  exact pow_le_pow_left' ((prob_le_iff_measure_le (by norm_num)).mp hb) t

def WitnessUseful {n : ℕ} (o : OracleConfig) (r v : Weights n) (y : Option (Weights n)) : Prop :=
  y.elim (optimum o.lam (hadamard r v) < 4 * o.tau1)
    (fun g => Retires r g ∧ 0 ≤ pairing v g)

lemma measurableSet_witnessUseful {n : ℕ} (o : OracleConfig) (r v : Weights n) :
    MeasurableSet {y | WitnessUseful o r v y} := by
  have hsome : MeasurableSet {y : Option (Weights n) | y.elim True
      (fun g => Retires r g ∧ 0 ≤ pairing v g)} := measurableSet_option_elim ((measurableSet_retires r).inter
    (measurableSet_le measurable_const
      (show Measurable (fun g : Weights n => pairing v g) by unfold pairing; fun_prop)))
  by_cases hF : optimum o.lam (hadamard r v) < 4 * o.tau1
  · simpa [WitnessUseful, hF] using hsome
  · have heq : {y | WitnessUseful o r v y} =
        {y : Option (Weights n) | y.elim True (fun g => Retires r g ∧ 0 ≤ pairing v g)} ∩ {none}ᶜ := by
      ext y
      cases y <;> simp [WitnessUseful, hF]
    rw [heq]
    exact hsome.inter measurableSet_option_none.compl

/-- A call is useful except for a geometric failure and accumulated one-sided noise tails. -/
theorem findWitness_utility {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OracleUtilityBounds n o) (r v : Weights n) (hr : IsMask r) (hr0 : r ≠ 0) :
    findWitness o (hadamard r v) r {y | ¬WitnessUseful o r v y} ≤
      ENNReal.ofReal (o.K * (o.beta1 / 2) + (1 - 3 / 8192 : ℝ) ^ o.K) := by
  have hb := ho.beta_pos
  let μ := findWitness o (hadamard r v) r
  letI := findWitness_probability o ho.eps_pos (hadamard r v) r
  letI := trialLaw_probability o ho.eps_pos (hadamard r v)
  have hsign : μ {y | ¬WitnessSign v y} ≤ ENNReal.ofReal (o.K * (o.beta1 / 2)) := by
    dsimp [μ]
    rw [findWitness, if_neg hr0, findTrials_eq_repeatUntil o ho.eps_pos]
    exact repeatUntil_failure (measurable_acceptTrial_fixed o r)
      (measurableSet_witnessSign v) trivial (by positivity)
      (trial_wrong_sign_bound o ho r v) o.K
  let N : Set (Option (Weights n)) := {y | y = none ∧ ¬optimum o.lam (hadamard r v) < 4 * o.tau1}
  have hnone : μ N ≤ ENNReal.ofReal ((1 - 3 / 8192 : ℝ) ^ o.K) := by
    by_cases hF : optimum o.lam (hadamard r v) < 4 * o.tau1
    · simp [N, hF]
    · have hNeq : N = {none} := by ext y; simp [N, hF]
      rw [hNeq]
      dsimp [μ]
      rw [findWitness, if_neg hr0]
      exact findTrials_none_bound hn o ho r v hr (le_of_not_gt hF) o.K
  have hsub : ∀ᵐ y ∂μ, y ∈ {y | ¬WitnessUseful o r v y} →
      y ∈ {y | ¬WitnessSign v y} ∪ N := by
    filter_upwards [findWitness_retires o ho.eps_pos (hadamard r v) r hr] with y hy
    cases y with
    | none => simp [WitnessUseful, WitnessSign, N]
    | some g =>
      change Retires r g at hy
      simp [WitnessUseful, WitnessSign, N, hy]
  calc
    _ ≤ μ ({y | ¬WitnessSign v y} ∪ N) := measure_mono_ae hsub
    _ ≤ μ {y | ¬WitnessSign v y} + μ N := measure_union_le _ _
    _ ≤ ENNReal.ofReal (o.K * (o.beta1 / 2)) +
        ENNReal.ofReal ((1 - 3 / 8192 : ℝ) ^ o.K) := add_le_add hsign hnone
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end DPCut
