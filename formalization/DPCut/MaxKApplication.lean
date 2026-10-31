import DPCut.ApplicationCalibration
import DPCut.ApplicationOptima
import DPCut.ExpectedApproximation

/-! Theorem 32: weighted Max-k-Cut, expected approximation amplification, and
an additive error constant uniform in k and in the supplied approximation ratio. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

lemma maxKOptimum_nonneg {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) {w : Weights n}
    (hw : Nonnegative w) : 0 ≤ maxKOptimum w k := by
  obtain ⟨π, _, he⟩ := maxKOptimum_exists (k := k) hn hk w
  rw [← he]
  exact labelCut_nonneg hw π

lemma measurable_partitionCut {n : ℕ} (π : Partition n) :
    Measurable (fun w : Weights n => partitionCut w π) := by
  unfold partitionCut pairing
  fun_prop

def amplifiedMaxK {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    (t : ℕ) (seed : Partition n) : Kernel (Weights n) (Partition n) :=
  bestOfKernel K partitionCut measurable_partitionCut t seed

instance amplifiedMaxK_markov {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    (t : ℕ) (seed : Partition n) : IsMarkovKernel (amplifiedMaxK K t seed) :=
  bestOfKernel_markov K partitionCut measurable_partitionCut t seed

lemma amplifiedMaxK_success {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] {w : Weights n} (hw : Nonnegative w)
    {ρ s τ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ)
    (hfeas : ∀ᵐ π ∂K w, clusterCount π ≤ k)
    (hmean : ρ * maxKOptimum w k ≤ ∫ π, partitionCut w π ∂K w)
    (t : ℕ) (ht : Real.log (1 / τ) / s ≤ t) (seed : Partition n) (hseed : clusterCount seed ≤ k) :
    HighProbability (amplifiedMaxK K t seed w) τ (fun π => clusterCount π ≤ k ∧
      (ρ - s) * maxKOptimum w k ≤ partitionCut w π) := by
  have hscore : ∀ᵐ π ∂K w, 0 ≤ partitionCut w π ∧ partitionCut w π ≤ maxKOptimum w k :=
    hfeas.mono fun π hπ => ⟨labelCut_nonneg hw π, partitionCut_le_maxKOptimum w hπ⟩
  have hgood := expected_approximation_success (maxKOptimum_nonneg hn hk hw) hs.le hs1 hscore hmean
  have hb := (bestOf_success (partitionCut w) ((ρ - s) * maxKOptimum w k) hs.le hs1 hgood t seed).weaken
    (repetition_failure_bound hs hs1 hτ t ht)
  have hf := bestOf_ae (K w) (partitionCut w) t seed hseed hfeas
  exact (hb.and_ae (Set.toFinite _ |>.measurableSet) hf).mono _ (Set.toFinite _ |>.measurableSet)
    (fun _ h => ⟨h.2, h.1⟩)

lemma maxK_ratio_slack {ρ s ξ : ℝ} (hs : 0 ≤ s) (hρ : ρ ≤ 1) (hξ : 3 * s ≤ ξ) :
    ρ - ξ ≤ (ρ - s) * (1 - s) / (1 + s) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + s)).mpr
  have hh := mul_nonneg hs (sub_nonneg.mpr hρ)
  have hh' := mul_le_mul_of_nonneg_right hξ (by positivity : 0 ≤ 1 + s)
  nlinarith [sq_nonneg s]

lemma inverse_tenth_le_inverse_square {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ)⁻¹ ^ 10 ≤ 1 / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hi : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hn1
  simpa only [one_div, inv_pow] using pow_le_pow_of_le_one (by positivity : 0 ≤ (n : ℝ)⁻¹) hi (by norm_num : 2 ≤ 10)

theorem private_max_k : PrivateMaxKStatement := by
  intro ξ ε hξ hε
  let s := min (ξ / 3) (1 / 4)
  have hs : 0 < s := lt_min (by positivity) (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsξ : 3 * s ≤ ξ := by have hh := min_le_left (ξ / 3) (1 / 4 : ℝ); dsimp [s]; linarith
  obtain ⟨C, hC, hrelease⟩ := application_release hs hs4 hε
  refine ⟨4 * C, 2, 7, by positivity, by norm_num, ?_⟩
  intro k hk ρ hρ hρ1 algorithm hMarkov hAlg n hn
  obtain ⟨seed, hseed⟩ := partitions_le_nonempty (n := n) (by omega) (show 1 ≤ k by omega)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  by_cases htriv : ρ ≤ ξ
  · let M : Kernel (Weights n) (Partition n) := Kernel.const _ (Measure.dirac seed)
    refine ⟨M, inferInstance, ?_, fun w hw => ?_⟩
    · intro w w' _ S hS
      have hh := Indistinguishable.of_eq (μ := M w) (ν := M w') rfl hε.le
        (by positivity : 0 ≤ (n : ℝ)⁻¹ ^ 10)
      exact hh.1 S hS
    · have hval : (ρ - ξ) * maxKOptimum w k - 4 * C * n * Real.log n ^ 7 ≤ partitionCut w seed := by
        have hopt := maxKOptimum_nonneg (by omega) (by omega) hw (k := k)
        have hnon : 0 ≤ partitionCut w seed := labelCut_nonneg hw seed
        have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htriv) hopt
        have ha : 0 ≤ 4 * C * n * Real.log n ^ 7 := by positivity
        linarith
      refine ⟨Set.toFinite _ |>.measurableSet, ?_⟩
      have he : M w {π | clusterCount π ≤ k ∧
          (ρ - ξ) * maxKOptimum w k - 4 * C * n * Real.log n ^ 7 ≤ partitionCut w π} = 1 := by
        change Measure.dirac seed _ = 1
        rw [Measure.dirac_apply' _ (Set.toFinite _ |>.measurableSet),
          Set.indicator_of_mem (show seed ∈ {π | clusterCount π ≤ k ∧
            (ρ - ξ) * maxKOptimum w k - 4 * C * n * Real.log n ^ 7 ≤ partitionCut w π}
              from ⟨hseed, hval⟩)]
        rfl
      rw [prob, he, ENNReal.toReal_one]
      have hh : 0 ≤ 2 / (n : ℝ) ^ 2 := by positivity
      linarith
  · have hρs : 0 ≤ ρ - s := by have := lt_of_not_ge htriv; linarith
    have hρs1 : ρ - s ≤ 1 := by linarith
    obtain ⟨M, hM, hg, hDP, hu⟩ := hrelease n hn
    letI := hM
    letI := hMarkov n
    let τ : ℝ := (n : ℝ)⁻¹ ^ 10
    have hτ : 0 < τ := (inverse_tenth_small hn).1
    let t := ⌈Real.log (1 / τ) / s⌉₊
    let K := amplifiedMaxK (algorithm n) t seed
    let R : Kernel (Weights n) (Partition n) :=
      ⟨fun w => (M w).bind K, measurable_bind_kernel M.measurable (K.measurable.comp measurable_snd)⟩
    haveI : IsMarkovKernel R := ⟨fun w => probability_bind (M w) K K.measurable⟩
    refine ⟨R, inferInstance, EdgeDP.postprocess hε.le hτ.le hDP K, fun w hw => ?_⟩
    have hgood := (hu w hw).and_ae (measurableSet_nonnegative measurable_id) (hg w hw)
    have hb : HighProbability (R w) (τ + τ) (fun π => clusterCount π ≤ k ∧
        (ρ - ξ) * maxKOptimum w k - 4 * C * n * Real.log n ^ 7 ≤ partitionCut w π) := by
      apply hgood.bind K hτ.le hτ.le (Set.toFinite _ |>.measurableSet)
      intro h hh
      have ha := hAlg n hn h hh.2
      have hp := amplifiedMaxK_success (by omega) (show 1 ≤ k by omega) (algorithm n) hh.2
        hs (by linarith) hτ ha.1 ha.2 t (Nat.le_ceil _) seed hseed
      apply hp.mono _ (Set.toFinite _ |>.measurableSet)
      intro π hπ
      refine ⟨hπ.1, ?_⟩
      have ht := max_k_transfer n k hn hk w h s (C * n * Real.log n ^ 7) (ρ - s) π
        hw hh.2 hs.le (by linarith) (by positivity) hρs hρs1 hh.1 hπ.1 hπ.2
      have hratio := mul_le_mul_of_nonneg_right (maxK_ratio_slack hs.le hρ1 hsξ)
        (maxKOptimum_nonneg (by omega) (by omega) hw (k := k))
      have hfactor : 2 * (ρ - s + 1) / (1 + s) ≤ 4 := by
        apply (div_le_iff₀ (by positivity : 0 < 1 + s)).mpr
        linarith
      have hadd := mul_le_mul_of_nonneg_right hfactor
        (by positivity : 0 ≤ C * n * Real.log n ^ 7)
      nlinarith
    apply hb.weaken
    have hh := inverse_tenth_le_inverse_square hn
    dsimp [τ]
    convert add_le_add hh hh using 1
    ring

end DPCut
