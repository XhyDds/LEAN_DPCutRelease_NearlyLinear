import DPCut.ApproxSDPCosted
import DPCut.SDPLSWAlgorithm

/-! Feasible randomized SDP outputs can be used by the witness mechanism.
Solver failure and covariance approximation contribute separately to TV error. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut

lemma TVClose.bind_good {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f g : α → Measure β}
    [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    (hf : Measurable f) (hg : Measurable g) {G : Set α} (hG : MeasurableSet G)
    {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hbad : μ Gᶜ ≤ ENNReal.ofReal ρ)
    (hgood : ∀ x ∈ G, TVClose (f x) (g x) η) :
    TVClose (μ.bind f) (μ.bind g) (ρ+η) := by
  letI := probability_bind μ f hf
  letI := probability_bind μ g hg
  have bound (F H : α → Measure β) [∀ x, IsProbabilityMeasure (F x)]
      [∀ x, IsProbabilityMeasure (H x)] (hF : Measurable F) (hH : Measurable H)
      (hb : ∀ x ∈ G, TVClose (F x) (H x) η) (s : Set β) (hs : MeasurableSet s) :
      μ.bind F s ≤ μ.bind H s + ENNReal.ofReal (ρ+η) := by
    rw [Measure.bind_apply hs hF.aemeasurable, Measure.bind_apply hs hH.aemeasurable]
    calc
      _ ≤ ∫⁻ x, (H x s + ENNReal.ofReal η) + Gᶜ.indicator (fun _ => 1) x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ G
        · simpa [hx] using (hb x hx).le_apply s hs
        · simpa [hx] using (prob_le_one (μ := F x) (s := s)).trans
            (le_add_self : (1 : ℝ≥0∞) ≤ (H x s + ENNReal.ofReal η) + 1)
      _ = ((∫⁻ x, H x s ∂μ) + ENNReal.ofReal η) + μ Gᶜ := by
        rw [lintegral_add_left (show Measurable (fun x => H x s + ENNReal.ofReal η) from
            ((Measure.measurable_coe hs).comp hH).add measurable_const),
          lintegral_add_left (show Measurable (fun x => H x s) from (Measure.measurable_coe hs).comp hH), lintegral_indicator hG.compl]
        simp
      _ ≤ ((∫⁻ x, H x s ∂μ) + ENNReal.ofReal η) + ENNReal.ofReal ρ := add_le_add_left hbad _
      _ = _ := by rw [ENNReal.ofReal_add hρ hη]; ring
  exact TVClose.of_event_bounds (add_nonneg hρ hη) (bound f g hf hg hgood)
    (bound g f hg hf (fun x hx => (hgood x hx).symm))

namespace RandomizedWitness

variable {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (he : 0 < o.eps1)

include hn in
lemma measurable_gaussianBatch :
    Measurable (fun X : FeasibleMatrix n => gaussianBatch X.val o.k) := by
  have hpos (X : FeasibleMatrix n) := feasible_posDef hn X.property
  have hd : Measurable (fun p : FeasibleMatrix n × (Fin o.k → Fin n → ℝ) =>
      ENNReal.ofReal (∏ j, gaussianDensity p.1.val (p.2 j))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro j _
    exact ((measurable_gaussianLogDensity_pair n).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk (by fun_prop))).exp
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [gaussianBatch_withDensity (hpos _), withDensity_apply _ hs]
  exact Measurable.lintegral_prod_right hd

include hn he in
lemma measurable_trial : Measurable (fun q : Weights n × FeasibleMatrix n =>
    approximateTrialLaw o q.1 q.2.val) := by
  let G : Kernel (Weights n × FeasibleMatrix n) (Fin o.k → Fin n → ℝ) :=
    ⟨_, (measurable_gaussianBatch hn o).comp measurable_snd⟩
  letI : IsMarkovKernel G := ⟨fun _ => gaussianBatch_isProbabilityMeasure _ _⟩
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  have hprod : Measurable (fun q : Weights n × FeasibleMatrix n =>
      (gaussianBatch q.2.val o.k).prod (laplace (1 / o.eps1))) := by
    have hh := (G.prod (Kernel.const (Weights n × FeasibleMatrix n) (laplace (1 / o.eps1)))).measurable
    change Measurable (fun q => (G.prod (Kernel.const _ (laplace (1 / o.eps1)))) q) at hh
    simpa only [Kernel.prod_apply, Kernel.const_apply, G, Kernel.coe_mk] using hh
  apply measurable_map_kernel hprod
  change Measurable (fun p : (Weights n × FeasibleMatrix n) × TrialSample n o.k =>
    (p.2.1, pairing p.1.1 (clippedWitness p.2.1) + p.2.2))
  exact (measurable_fst.comp measurable_snd).prodMk
    ((measurable_pairing (measurable_fst.comp measurable_fst)
      ((measurable_pi_lambda _ measurable_clippedWitness).comp
        (measurable_fst.comp measurable_snd))).add (measurable_snd.comp measurable_snd))

include hn he in
lemma measurable_repeated (t : ℕ) : Measurable (fun q : (Weights n × Weights n) × FeasibleMatrix n =>
    repeatUntil (approximateTrialLaw o q.1.1 q.2.val) (acceptTrial o q.1.2) t) := by
  let A := (Weights n × Weights n) × FeasibleMatrix n
  let μ : A → Measure (TrialSample n o.k) := fun q => approximateTrialLaw o q.1.1 q.2.val
  let f : A × TrialSample n o.k → Option (Weights n) := fun q => acceptTrial o q.1.1.2 q.2
  have ht : Measurable μ := (measurable_trial hn o he).comp (f := fun q : A => (q.1.1,q.2))
    (show Measurable (fun q : A => (q.1.1,q.2)) from
      (measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hf : Measurable f := (measurable_acceptTrial o).comp (f := fun q : A × TrialSample n o.k => (q.1.1.2,q.2))
    (show Measurable (fun q : A × TrialSample n o.k => (q.1.1.2,q.2)) from
      (measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  letI (q : A) : IsProbabilityMeasure (μ q) := approximateTrialLaw_probability o he q.1.1 q.2.val
  exact measurable_repeatUntil ht hf t

include hn he in
lemma measurable_witness : Measurable (fun q : (Weights n × Weights n) × FeasibleMatrix n =>
    approximateFindWitness o q.1.1 q.1.2 q.2.val) := by
  unfold approximateFindWitness
  exact Measurable.ite ((measurable_snd.comp measurable_fst) (measurableSet_singleton 0))
    measurable_const (measurable_repeated hn o he o.K)

include he in
lemma witness_probability (D r : Weights n) (X : FeasibleMatrix n) :
    IsProbabilityMeasure (approximateFindWitness o D r X.val) := by
  unfold approximateFindWitness
  split_ifs
  · infer_instance
  · letI := approximateTrialLaw_probability o he D X.val
    exact repeatUntil_probability _ (measurable_acceptTrial_fixed o r) _

/-- Sample an approximate covariance once, then use the original finite witness
trials. Failure still returns a feasible fallback covariance. -/
def run (S : Weights n → CostedLaw (FeasibleMatrix n)) (B : ℝ) (D r : Weights n) :
    CostedLaw (Option (Weights n)) :=
  .charge (vectorBlockCost n) (if r = 0 then .pure none else
    (S D).bind fun X => ApproxSDPCosted.trials o X.val (boundedObjective B D) r o.K)

include he in
lemma run_law (S : Weights n → CostedLaw (FeasibleMatrix n)) (B : ℝ) (D r : Weights n)
    [IsProbabilityMeasure (S D).law] :
    (run o S B D r).law = (S D).law.bind (fun X => approximateFindWitness o (boundedObjective B D) r X.val) := by
  simp only [run, CostedLaw.charge_law]
  by_cases hr : r = 0
  · simp [hr, approximateFindWitness, Measure.bind_const]
  · simp only [if_neg hr, CostedLaw.bind_law, approximateFindWitness,
      ApproxSDPCosted.trials_law o he]

include hn he in
lemma measurable_run (S : Weights n → CostedLaw (FeasibleMatrix n))
    (hS : Measurable (fun D => (S D).law)) [∀ D, IsProbabilityMeasure (S D).law] (B : ℝ) :
    Measurable (fun q : Weights n × Weights n => (run o S B q.1 q.2).law) := by
  simp_rw [run_law o he]
  let f : (Weights n × Weights n) × FeasibleMatrix n → (Weights n × Weights n) × FeasibleMatrix n :=
    fun q => ((boundedObjective B q.1.1,q.1.2),q.2)
  have hf : Measurable f :=
    (((measurable_boundedObjective n B).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hinput : Measurable (fun q : Weights n × Weights n => (S q.1).law) := hS.comp measurable_fst
  letI (q : Weights n × Weights n) : IsProbabilityMeasure (S q.1).law := inferInstance
  exact measurable_bind_kernel hinput ((measurable_witness hn o he).comp (f:=f) hf)

include hn he in
lemma run_probability (S : Weights n → CostedLaw (FeasibleMatrix n))
    [∀ D, IsProbabilityMeasure (S D).law] (B : ℝ) (D r : Weights n) :
    IsProbabilityMeasure (run o S B D r).law := by
  rw [run_law o he]
  letI (X : FeasibleMatrix n) := witness_probability o he (boundedObjective B D) r X
  apply probability_bind
  exact (measurable_witness hn o he).comp
    (f:=fun X : FeasibleMatrix n => ((boundedObjective B D,r),X))
    (measurable_const.prodMk measurable_id)


lemma run_cost (S : Weights n → CostedLaw (FeasibleMatrix n)) {B : ℝ} {cost : ℝ≥0∞}
    (hc : ∀ D, (S D).cost ≤ cost) (D r : Weights n) :
    (run o S B D r).cost ≤ vectorBlockCost n + cost + o.K * trialCostBound n o := by
  rw [add_assoc]
  apply CostedLaw.charge_cost_le
  split_ifs
  · exact zero_le _
  · exact CostedLaw.bind_cost_le _ _ (hc D) (fun X => ApproxSDPCosted.trials_cost o X.val _ r o.K)

include hn he in
lemma law_tv (hl : 0 < o.lam) (hk : 0 < o.k) {μ ρ B : ℝ}
    (hμ : 0 < μ) (hμhalf : μ ≤ 1/2) (hρ : 0 ≤ ρ)
    (S : Weights n → CostedLaw (FeasibleMatrix n))
    [∀ D, IsProbabilityMeasure (S D).law]
    (hbad : ∀ D, (S D).law {X | o.lam * μ^2 / (2*(n:ℝ)^4) <
      optimum o.lam (boundedObjective B D) - objective o.lam (boundedObjective B D) X.val} ≤ ENNReal.ofReal ρ)
    (D r : Weights n) :
    TVClose (run o S B D r).law (findWitness o (boundedObjective B D) r)
      (ρ + o.K * (2 * Real.sqrt o.k * μ)) := by
  rw [run_law o he]
  letI (X : FeasibleMatrix n) := witness_probability o he (boundedObjective B D) r X
  letI := findWitness_probability o he (boundedObjective B D) r
  have hm : Measurable (fun X : FeasibleMatrix n => approximateFindWitness o (boundedObjective B D) r X.val) :=
    (measurable_witness hn o he).comp (f := fun X : FeasibleMatrix n => ((boundedObjective B D,r),X))
    (measurable_const.prodMk measurable_id : Measurable (fun X : FeasibleMatrix n => ((boundedObjective B D,r),X)))
  have hG : MeasurableSet {X : FeasibleMatrix n |
      optimum o.lam (boundedObjective B D) - objective o.lam (boundedObjective B D) X.val ≤ o.lam * μ^2 / (2*(n:ℝ)^4)} :=
    measurableSet_le (measurable_const.sub ((SDPCoordinates.measurable_objective o.lam _).comp measurable_subtype_coe)) measurable_const
  have hb : (S D).law {X : FeasibleMatrix n |
      optimum o.lam (boundedObjective B D) - objective o.lam (boundedObjective B D) X.val ≤ o.lam * μ^2 / (2*(n:ℝ)^4)}ᶜ ≤ ENNReal.ofReal ρ := by
    simpa only [Set.compl_setOf, not_le] using hbad D
  have ht := TVClose.bind_good hm (measurable_const (a := findWitness o (boundedObjective B D) r)) hG hρ
    (by positivity : 0 ≤ o.K * (2 * Real.sqrt o.k * μ)) hb
    (fun X hX => approximateFindWitness_tv hn o he hl hk _ r X.property hμ hμhalf hX)
  simpa only [Measure.bind_const, measure_univ, one_smul] using ht

end RandomizedWitness
end DPCut
