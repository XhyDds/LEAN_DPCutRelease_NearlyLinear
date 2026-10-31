import DPCut.OracleReplacementLaw

/-! Explicit approximate optimization primitive for the existing real-arithmetic
model. Accuracy is requested through a normalized objective-gap tolerance.
The cost contract remains uniform in the real objective data, as in the former
exact-oracle model, and now charges for log inverse accuracy. It is not an
assertion that LSW supplies this uniform contract or a finite-bit implementation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

structure ApproxSDPOracle where
  solve : ∀ n : ℕ, ℝ → ℝ → Weights n → Mat n
  measurable_solve : ∀ n lam μ, Measurable (solve n lam μ)
  feasible : ∀ n, 2 ≤ n → ∀ lam μ, 0 < lam → 0 < μ → μ ≤ 1 / 2 →
    ∀ D, solve n lam μ D ∈ DPCut.feasible n
  objective_gap : ∀ n, 2 ≤ n → ∀ lam μ, 0 < lam → 0 < μ → μ ≤ 1 / 2 →
    ∀ D, optimum lam D - objective lam D (solve n lam μ D) ≤ lam * μ ^ 2 / (2 * (n : ℝ) ^ 4)
  charge : ℕ → ℝ → ℝ≥0∞
  coefficient : ℝ
  degree : ℕ
  coefficient_pos : 0 < coefficient
  charge_le : ∀ n μ, 0 < μ → μ ≤ 1 / 2 →
    charge n μ ≤ ENNReal.ofReal (coefficient * (1 + n + |Real.log μ|) ^ degree)

namespace ApproxSDPOracle
variable (sdp : ApproxSDPOracle) {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
  (hl : 0 < o.lam) (he : 0 < o.eps1) {μ : ℝ} (hμ : 0 < μ) (hμhalf : μ ≤ 1 / 2)
include hn hl hμ hμhalf

lemma measurable_gaussianBatch :
    Measurable (fun D : Weights n => gaussianBatch (sdp.solve n o.lam μ D) o.k) := by
  have hpos (D) := feasible_posDef hn (sdp.feasible n hn o.lam μ hl hμ hμhalf D)
  have hd : Measurable (fun p : Weights n × (Fin o.k → Fin n → ℝ) =>
      ENNReal.ofReal (∏ j, gaussianDensity (sdp.solve n o.lam μ p.1) (p.2 j))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro j _
    exact ((measurable_gaussianLogDensity_pair n).comp
      (((sdp.measurable_solve n o.lam μ).comp measurable_fst).prodMk (by fun_prop))).exp
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [gaussianBatch_withDensity (hpos _), withDensity_apply _ hs]
  exact Measurable.lintegral_prod_right hd

include he in
lemma measurable_trial :
    Measurable (fun D : Weights n => approximateTrialLaw o D (sdp.solve n o.lam μ D)) := by
  let G : Kernel (Weights n) (Fin o.k → Fin n → ℝ) :=
    ⟨_, sdp.measurable_gaussianBatch hn o hl hμ hμhalf⟩
  letI : IsMarkovKernel G := ⟨fun _ => gaussianBatch_isProbabilityMeasure _ _⟩
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  have hprod : Measurable (fun D : Weights n =>
      (gaussianBatch (sdp.solve n o.lam μ D) o.k).prod (laplace (1 / o.eps1))) := by
    have hh := (G.prod (Kernel.const (Weights n) (laplace (1 / o.eps1)))).measurable
    change Measurable (fun D => (G.prod (Kernel.const (Weights n) (laplace (1 / o.eps1)))) D) at hh
    simpa only [Kernel.prod_apply, Kernel.const_apply, G, Kernel.coe_mk] using hh
  apply measurable_map_kernel hprod
  change Measurable (fun p : Weights n × TrialSample n o.k =>
    (p.2.1, pairing p.1 (clippedWitness p.2.1) + p.2.2))
  exact (measurable_fst.comp measurable_snd).prodMk
    ((measurable_pairing measurable_fst
      ((measurable_pi_lambda _ measurable_clippedWitness).comp
        (measurable_fst.comp measurable_snd))).add (measurable_snd.comp measurable_snd))

include he in
lemma measurable_witness : Measurable (fun q : Weights n × Weights n =>
    approximateFindWitness o q.1 q.2 (sdp.solve n o.lam μ q.1)) := by
  letI (q : Weights n × Weights n) :=
    approximateTrialLaw_probability o he q.1 (sdp.solve n o.lam μ q.1)
  have hm := measurable_repeatUntil
    (μ := fun q : Weights n × Weights n => approximateTrialLaw o q.1 (sdp.solve n o.lam μ q.1))
    ((sdp.measurable_trial hn o hl he hμ hμhalf).comp measurable_fst)
    ((measurable_acceptTrial o).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) o.K
  unfold approximateFindWitness
  exact Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_const hm

def witnessKernel : OracleReplacement.WitnessKernel n :=
  ⟨fun q => approximateFindWitness o q.1 q.2 (sdp.solve n o.lam μ q.1),
    sdp.measurable_witness hn o hl he hμ hμhalf⟩

instance witnessKernel_markov : IsMarkovKernel (sdp.witnessKernel hn o hl he hμ hμhalf) := by
  constructor
  intro q
  change IsProbabilityMeasure (approximateFindWitness o q.1 q.2 (sdp.solve n o.lam μ q.1))
  unfold approximateFindWitness
  split_ifs
  · infer_instance
  · letI := approximateTrialLaw_probability o he q.1 (sdp.solve n o.lam μ q.1)
    exact repeatUntil_probability _ (measurable_acceptTrial_fixed o q.2) _

theorem witnessKernel_tv (hk : 0 < o.k) (q : Weights n × Weights n) :
    TVClose (sdp.witnessKernel hn o hl he hμ hμhalf q)
      (OracleReplacement.exactKernel hn o hl he q) (o.K * (2 * Real.sqrt o.k * μ)) :=
  approximateFindWitness_tv hn o he hl hk q.1 q.2
    (sdp.feasible n hn o.lam μ hl hμ hμhalf q.1) hμ hμhalf
    (sdp.objective_gap n hn o.lam μ hl hμ hμhalf q.1)

end ApproxSDPOracle
end DPCut
