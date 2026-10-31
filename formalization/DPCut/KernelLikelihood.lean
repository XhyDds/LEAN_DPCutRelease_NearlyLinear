import DPCut.SuccessChargedMoment
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-! Pure privacy bounds and jointly measurable kernel log-likelihood ratios. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut

variable {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]

lemma Indistinguishable.symm {μ ν : Measure Y} {ε δ : ℝ}
    (h : Indistinguishable μ ν ε δ) : Indistinguishable ν μ ε δ := ⟨h.2, h.1⟩

lemma Indistinguishable.le {μ ν : Measure Y} {ε : ℝ}
    (h : Indistinguishable μ ν ε 0) : μ ≤ ENNReal.ofReal (Real.exp ε) • ν := by
  apply Measure.le_iff.mpr
  intro s hs
  simpa using h.1 s hs

lemma Indistinguishable.ac {μ ν : Measure Y} {ε : ℝ}
    (h : Indistinguishable μ ν ε 0) : μ ≪ ν :=
  (Measure.absolutelyContinuous_of_le h.le).trans Measure.smul_absolutelyContinuous

lemma Indistinguishable.zero_eq {μ ν : Measure Y}
    (h : Indistinguishable μ ν 0 0) : μ = ν := by
  apply le_antisymm
  · simpa using h.le
  · simpa using h.symm.le

lemma llr_le_of_measure_le {μ ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ell : ℝ} (h : μ ≤ ENNReal.ofReal (Real.exp ell) • ν) :
    ∀ᵐ y ∂μ, llr μ ν y ≤ ell := by
  have hac : μ ≪ ν :=
    (Measure.absolutelyContinuous_of_le h).trans Measure.smul_absolutelyContinuous
  have hr : μ.rnDeriv ν ≤ᵐ[ν] fun _ => ENNReal.ofReal (Real.exp ell) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
    intro s hs _
    exact (Measure.setLIntegral_rnDeriv_le s).trans (by simpa using h s)
  filter_upwards [hac.ae_le hr, exp_llr_of_ac μ ν hac, hac.ae_le (μ.rnDeriv_ne_top ν)]
    with y hy he ht
  apply Real.exp_le_exp.mp
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hy).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_nonneg _))

lemma Indistinguishable.llr_bounds {μ ν : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ell : ℝ}
    (h : Indistinguishable μ ν ell 0) :
    ∀ᵐ y ∂μ, -ell ≤ llr μ ν y ∧ llr μ ν y ≤ ell := by
  filter_upwards [llr_le_of_measure_le h.le,
    h.ac.ae_le (llr_le_of_measure_le h.symm.le), neg_llr h.ac] with y h1 h2 hn
  exact ⟨by change -llr μ ν y = llr ν μ y at hn; linarith, h1⟩

/-- Mathlib's kernel Radon--Nikodym derivative supplies joint measurability in history
and next output; arbitrary independently chosen versions of measure densities would not. -/
def kernelLogRatio [StandardBorelSpace Y] (K H : Kernel α Y)
    (h : α) (y : Y) : ℝ := Real.log ((K.rnDeriv H h y).toReal)

@[fun_prop] lemma measurable_kernelLogRatio [StandardBorelSpace Y]
    (K H : Kernel α Y) : Measurable (Function.uncurry (kernelLogRatio K H)) :=
  (K.measurable_rnDeriv H).ennreal_toReal.log

lemma kernelLogRatio_eq_llr [StandardBorelSpace Y]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H] (h : α) :
    kernelLogRatio K H h =ᵐ[H h] llr (K h) (H h) := by
  filter_upwards [K.rnDeriv_eq_rnDeriv_measure (η := H) (a := h)] with y hy
  simp only [kernelLogRatio, llr, hy]

lemma kernelLogRatio_bounds [StandardBorelSpace Y]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H] (h : α)
    {ell : ℝ} (hp : Indistinguishable (K h) (H h) ell 0) :
    ∀ᵐ y ∂K h, -ell ≤ kernelLogRatio K H h y ∧ kernelLogRatio K H h y ≤ ell := by
  filter_upwards [hp.ac.ae_le (kernelLogRatio_eq_llr K H h), hp.llr_bounds]
    with y he hb using he ▸ hb

lemma integral_exp_neg_kernelLogRatio [StandardBorelSpace Y]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H] (h : α)
    (hKH : K h ≪ H h) (hHK : H h ≪ K h) :
    ∫ y, Real.exp (-kernelLogRatio K H h y) ∂K h = 1 := by
  calc
    _ = ∫ y, ((H h).rnDeriv (K h) y).toReal ∂K h := by
      apply integral_congr_ae
      filter_upwards [hKH.ae_le (kernelLogRatio_eq_llr K H h), exp_neg_llr hKH]
        with y he hex using by rw [he, hex]
    _ = 1 := by rw [Measure.integral_toReal_rnDeriv hHK]; simp

lemma withDensity_exp_kernelLogRatio [StandardBorelSpace Y]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H] (h : α)
    (hKH : K h ≪ H h) (hHK : H h ≪ K h) :
    (H h).withDensity (fun y => ENNReal.ofReal (Real.exp (kernelLogRatio K H h y))) = K h := by
  rw [← Measure.withDensity_rnDeriv_eq (K h) (H h) hKH]
  apply withDensity_congr_ae
  filter_upwards [kernelLogRatio_eq_llr K H h, exp_llr_of_ac' (K h) (H h) hHK,
    (K h).rnDeriv_ne_top (H h)] with y he hex ht
  rw [he, hex, ENNReal.ofReal_toReal ht]

lemma kernel_success_charged_one_step [StandardBorelSpace Y]
    (K H : Kernel α Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (bottom : Y) (h : α) {a ell : ℝ}
    (ha : 1 ≤ a) (he : 0 ≤ ell) (he1 : ell ≤ 1 / 10) (hae : a * ell ≤ 1 / 4)
    (hp : Indistinguishable (K h) (H h) ell 0) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (a *
      (kernelLogRatio K H h y - 4 * stepCharge bottom ell y))) ∂K h ≤ 1 := by
  exact success_charged_one_step (K h) bottom
    ((measurable_kernelLogRatio K H).comp measurable_prodMk_left) ha he he1 hae
    (kernelLogRatio_bounds K H h hp)
    (integral_exp_neg_kernelLogRatio K H h hp.ac hp.symm.ac)

end DPCut
