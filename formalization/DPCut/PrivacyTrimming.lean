import DPCut.ProbabilityProgramming

/-! Measurable subkernels obtained by clipping a pair of likelihoods. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
  [StandardBorelSpace Y]

def privacyTrim (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (ε : ℝ) : Kernel A Y :=
  (K + H).withDensity (fun h y =>
    min (K.rnDeriv (K + H) h y)
      (ENNReal.ofReal (Real.exp ε) * H.rnDeriv (K + H) h y))

lemma measurable_privacyTrim_density (K H : Kernel A Y) (ε : ℝ) :
    Measurable (fun p : A × Y => min (K.rnDeriv (K + H) p.1 p.2)
      (ENNReal.ofReal (Real.exp ε) * H.rnDeriv (K + H) p.1 p.2)) :=
  (K.measurable_rnDeriv _).min (measurable_const.mul (H.measurable_rnDeriv _))

lemma privacyTrim_le (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (ε : ℝ) (h : A) : privacyTrim K H ε h ≤ K h := by
  have hd := Kernel.withDensity_rnDeriv_eq
    (κ := K) (η := K + H) (a := h)
    (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right bot_le))
  rw [← hd, privacyTrim, Kernel.withDensity_apply _ (measurable_privacyTrim_density K H ε),
    Kernel.withDensity_apply _ (K.measurable_rnDeriv _)]
  exact withDensity_mono (Filter.Eventually.of_forall fun y => min_le_left _ _)

instance privacyTrim_finite (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (ε : ℝ) : IsFiniteKernel (privacyTrim K H ε) :=
  ⟨⟨1, ENNReal.one_lt_top, fun h => (privacyTrim_le K H ε h univ).trans (by simp)⟩⟩

lemma privacyTrim_swap (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (ε : ℝ) (h : A) :
    privacyTrim H K ε h = ((K + H) h).withDensity (fun y =>
      min (H.rnDeriv (K + H) h y)
        (ENNReal.ofReal (Real.exp ε) * K.rnDeriv (K + H) h y)) := by
  rw [privacyTrim, Kernel.withDensity_apply _ (measurable_privacyTrim_density H K ε)]
  simp only [add_comm H K]

lemma privacyTrim_private (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    {ε : ℝ} (hε : 0 ≤ ε) (h : A) :
    Indistinguishable (privacyTrim K H ε h) (privacyTrim H K ε h) ε 0 := by
  have hb (P Q : Kernel A Y) [IsMarkovKernel P] [IsMarkovKernel Q] :
      privacyTrim P Q ε h ≤ ENNReal.ofReal (Real.exp ε) • privacyTrim Q P ε h := by
    rw [privacyTrim_swap P Q ε h]
    rw [privacyTrim, Kernel.withDensity_apply _ (measurable_privacyTrim_density P Q ε),
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    apply withDensity_mono
    apply Filter.Eventually.of_forall
    intro y
    change min _ _ ≤ ENNReal.ofReal (Real.exp ε) * min _ _
    rw [mul_min]
    apply le_min (min_le_right _ _)
    apply (min_le_left _ _).trans
    have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp ε) :=
      ENNReal.one_le_ofReal.mpr (Real.one_le_exp hε)
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_right' (one_le_mul_of_one_le_of_one_le he he) (P.rnDeriv (P + Q) h y)
  constructor <;> intro s hs
  · simpa using (hb K H) s
  · simpa using (hb H K) s

/-- Approximate privacy removes at most `δ` mass when the likelihood is clipped. -/
lemma privacyTrim_mass (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (h : A) {ε δ : ℝ} (hp : Indistinguishable (K h) (H h) ε δ) :
    1 ≤ privacyTrim K H ε h univ + ENNReal.ofReal δ := by
  let p := K.rnDeriv (K + H) h
  let q := H.rnDeriv (K + H) h
  let E := ENNReal.ofReal (Real.exp ε)
  let G := {y | p y ≤ E * q y}
  have hG : MeasurableSet G := measurableSet_le
    ((K.measurable_rnDeriv _).comp measurable_prodMk_left)
    (measurable_const.mul ((H.measurable_rnDeriv _).comp measurable_prodMk_left))
  have hK : K h ≪ (K + H) h :=
    Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right bot_le)
  have hH : H h ≪ (K + H) h :=
    Measure.absolutelyContinuous_of_le (le_add_of_nonneg_left bot_le)
  have hg : privacyTrim K H ε h G = K h G := by
    rw [privacyTrim, Kernel.withDensity_apply' _ (measurable_privacyTrim_density K H ε)]
    calc
      _ = ∫⁻ y in G, p y ∂(K + H) h := by
        apply setLIntegral_congr_fun hG
        intro y hy
        exact min_eq_left hy
      _ = _ := Kernel.setLIntegral_rnDeriv hK hG
  have hgc : privacyTrim K H ε h Gᶜ = E * H h Gᶜ := by
    rw [privacyTrim, Kernel.withDensity_apply' _ (measurable_privacyTrim_density K H ε)]
    calc
      _ = ∫⁻ y in Gᶜ, E * q y ∂(K + H) h := by
        apply setLIntegral_congr_fun hG.compl
        intro y hy
        exact min_eq_right (le_of_not_ge hy)
      _ = _ := by
        rw [lintegral_const_mul E (show Measurable q from
          (H.measurable_rnDeriv _).comp measurable_prodMk_left),
          Kernel.setLIntegral_rnDeriv hH hG.compl]
  have hsum : privacyTrim K H ε h univ = K h G + E * H h Gᶜ := by
    rw [← measure_add_measure_compl hG, hg, hgc]
  rw [hsum]
  calc
    1 = K h G + K h Gᶜ := by rw [measure_add_measure_compl hG]; simp
    _ ≤ K h G + (E * H h Gᶜ + ENNReal.ofReal δ) :=
      add_le_add_left (hp.1 Gᶜ hG.compl) _
    _ = _ := (add_assoc _ _ _).symm

end DPCut
