import DPCut.Sequential
import DPCut.KernelLikelihood

/-! Likelihood multiplication and exponential-moment induction for finite adaptive laws. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut

variable {Y : Type*} [MeasurableSpace Y] [Inhabited Y]

/-- The density chain rule, formulated as an equality of measures. -/
theorem sequential_withDensity (K H : Sequential Y)
    [∀ t, IsMarkovKernel (K t)] [∀ t, IsMarkovKernel (H t)]
    (bottom : Y) {z : ℕ → List Y → Y → ℝ}
    (hz : ∀ t, Measurable (Function.uncurry (z t))) (k : ℕ)
    (hs : ∀ t < k, ∀ᵐ h ∂sequentialLaw H t,
      (H t h).withDensity (fun y => ENNReal.ofReal (Real.exp (z t h y))) = K t h) :
    (sequentialLaw H k).withDensity
      (fun h => ENNReal.ofReal (Real.exp (transcriptSum bottom z h))) = sequentialLaw K k := by
  have hm := (measurable_transcriptSum bottom hz).exp.ennreal_ofReal
  induction k with
  | zero =>
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_withDensity_eq_lintegral_mul _ hm hf]
    simp only [Pi.mul_apply]
    simp only [sequentialLaw]
    rw [lintegral_dirac' _ (hm.mul hf), lintegral_dirac' _ hf]
    simp [transcriptSum]
  | succ k ih =>
    have hi := ih (fun t ht => hs t (by omega))
    apply Measure.ext_of_lintegral
    intro f hf
    rw [lintegral_withDensity_eq_lintegral_mul _ hm hf]
    simp only [Pi.mul_apply]
    rw [lintegral_sequentialLaw_succ H k (hm.mul hf), lintegral_sequentialLaw_succ K k hf]
    have hfm : Measurable (fun p : List Y × Y => f (p.1 ++ [p.2])) :=
      hf.comp (measurable_list_append_one bottom)
    calc
      _ = ∫⁻ h, ENNReal.ofReal (Real.exp (transcriptSum bottom z h)) *
          (∫⁻ y, f (h ++ [y]) ∂K k h) ∂sequentialLaw H k := by
        apply lintegral_congr_ae
        filter_upwards [hs k (by omega), sequentialLaw_length H k] with h hh hl
        simp only [transcriptSum_append, hl, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
        have hzm : Measurable (fun y => ENNReal.ofReal (Real.exp (z k h y))) :=
          ((hz k).comp measurable_prodMk_left).exp.ennreal_ofReal
        have hfmh : Measurable (fun y => f (h ++ [y])) := hfm.comp measurable_prodMk_left
        rw [lintegral_const_mul _ (hzm.mul hfmh)]
        congr 1
        exact (lintegral_withDensity_eq_lintegral_mul _ hzm hfmh).symm.trans
          (congrArg (fun μ : Measure Y => ∫⁻ y, f (h ++ [y]) ∂μ) hh)
      _ = _ := by
        have hg : Measurable (fun h => ∫⁻ y, f (h ++ [y]) ∂K k h) :=
          hfm.lintegral_kernel_prod_right
        exact (lintegral_withDensity_eq_lintegral_mul _ hm hg).symm.trans
          (congrArg (fun μ : Measure (List Y) => ∫⁻ h, ∫⁻ y, f (h ++ [y]) ∂K k h ∂μ) hi)

/-- Conditional moment bounds multiply along the sequential process. -/
theorem sequential_exp_moment (K : Sequential Y) [∀ t, IsMarkovKernel (K t)]
    (bottom : Y) {v : ℕ → List Y → Y → ℝ}
    (hv : ∀ t, Measurable (Function.uncurry (v t))) (k : ℕ)
    (hs : ∀ t < k, ∀ᵐ h ∂sequentialLaw K t,
      ∫⁻ y, ENNReal.ofReal (Real.exp (v t h y)) ∂K t h ≤ 1) :
    ∫⁻ h, ENNReal.ofReal (Real.exp (transcriptSum bottom v h)) ∂sequentialLaw K k ≤ 1 := by
  have hm := (measurable_transcriptSum bottom hv).exp.ennreal_ofReal
  induction k with
  | zero =>
    rw [sequentialLaw, lintegral_dirac' _ hm]
    simp [transcriptSum]
  | succ k ih =>
    apply le_trans _ (ih (fun t ht => hs t (by omega)))
    rw [lintegral_sequentialLaw_succ K k hm]
    apply lintegral_mono_ae
    filter_upwards [hs k (by omega), sequentialLaw_length K k] with h hh hl
    simp only [transcriptSum_append, hl, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have hvm : Measurable (fun y => ENNReal.ofReal (Real.exp (v k h y))) :=
      ((hv k).comp measurable_prodMk_left).exp.ennreal_ofReal
    rw [lintegral_const_mul _ hvm]
    simpa using mul_le_mul_left' hh (ENNReal.ofReal (Real.exp (transcriptSum bottom v h)))

end DPCut
