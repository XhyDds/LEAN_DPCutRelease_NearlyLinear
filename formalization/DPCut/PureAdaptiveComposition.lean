import DPCut.PurePrivacyMoment
import DPCut.SequentialLikelihood
import DPCut.MomentPrivacy

/-! Adaptive composition of pure-private kernels via exponential moments. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut

variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Inhabited Y]

/-- A Chernoff-parameter form of adaptive composition. It avoids choosing square roots
until the public privacy budget is calibrated. -/
theorem pure_adaptive_composition (K H : Sequential Y)
    [∀ t, IsMarkovKernel (K t)] [∀ t, IsMarkovKernel (H t)]
    (k : ℕ) {ε₀ ε δ a : ℝ} (hε₀ : 0 ≤ ε₀) (hδ : 0 < δ) (ha : 0 < a)
    (hbudget : Real.log (1 / δ) ≤ a * ε - (a + a ^ 2) * k * ε₀ ^ 2 / 2)
    (hp : ∀ t < k, ∀ h, Indistinguishable (K t h) (H t h) ε₀ 0) :
    Indistinguishable (sequentialLaw K k) (sequentialLaw H k) ε δ := by
  have bound (P Q : Sequential Y) [∀ t, IsMarkovKernel (P t)]
      [∀ t, IsMarkovKernel (Q t)]
      (hpq : ∀ t < k, ∀ h, Indistinguishable (P t h) (Q t h) ε₀ 0)
      (s : Set (List Y)) (hs : MeasurableSet s) :
      sequentialLaw P k s ≤ ENNReal.ofReal (Real.exp ε) * sequentialLaw Q k s +
        ENNReal.ofReal δ := by
    let z : ℕ → List Y → Y → ℝ := fun t => kernelLogRatio (P t) (Q t)
    let v : ℕ → List Y → Y → ℝ := fun t h y => a * z t h y - (a + a ^ 2) * ε₀ ^ 2 / 2
    let L : ℝ := (a + 1) * k * ε₀ ^ 2 / 8
    have hz (t : ℕ) : Measurable (Function.uncurry (z t)) := measurable_kernelLogRatio _ _
    have hv (t : ℕ) : Measurable (Function.uncurry (v t)) :=
      (measurable_const.mul (hz t)).sub measurable_const
    have hd : (sequentialLaw Q k).withDensity
        (fun h => ENNReal.ofReal (Real.exp (transcriptSum default z h))) = sequentialLaw P k := by
      apply sequential_withDensity P Q default hz k
      intro t ht
      exact Filter.Eventually.of_forall fun h =>
        withDensity_exp_kernelLogRatio (P t) (Q t) h (hpq t ht h).ac (hpq t ht h).symm.ac
    have hm := sequential_exp_moment P default hv k (fun t ht =>
      Filter.Eventually.of_forall fun h =>
        kernel_privacy_exp_moment (P t) (Q t) h hε₀ ha.le (hpq t ht h))
    have hm' : ∫⁻ h, ENNReal.ofReal (Real.exp
        (a * (transcriptSum default z h - 4 * L))) ∂sequentialLaw P k ≤ 1 := by
      apply le_trans (le_of_eq (lintegral_congr_ae ?_)) hm
      filter_upwards [sequentialLaw_length P k] with h hh
      congr 2
      simp only [transcriptSum, v, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, hh]
      dsimp [L]
      ring
    apply privacy_of_charged_moment (measurable_transcriptSum default hz)
      measurable_const hd ha hδ ?_ (Filter.Eventually.of_forall fun _ => le_rfl) hm' s hs
    convert hbudget using 1
    dsimp [L]
    ring
  exact ⟨bound K H hp, bound H K (fun t ht h => (hp t ht h).symm)⟩

end DPCut
