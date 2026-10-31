import DPCut.FindWitnessSupport

/-! Joint measurability of the real oracle and its neighboring-pair auxiliary law. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable
variable {A : Type*} [MeasurableSpace A] {n : ℕ}

lemma measurable_fractionalQuery {X : A → Mat n} (hX : Measurable X) (e : Edge n) :
    Measurable (fun a => fractionalQuery (X a) e) :=
  (measurable_const.sub ((measurable_pi_apply e.val.2).comp
    ((measurable_pi_apply e.val.1).comp hX))).div_const 2

lemma measurable_queryMax {X Y : A → Mat n} (hX : Measurable X) (hY : Measurable Y)
    (e : Edge n) : Measurable (fun a => queryMax (X a) (Y a) e) :=
  (measurable_fractionalQuery hX e).max (measurable_fractionalQuery hY e)

lemma measurable_oracleSensitivity {X Y : A → Mat n} {ζ r : A → Weights n}
    (hX : Measurable X) (hY : Measurable Y) (hζ : Measurable ζ) (hr : Measurable r) :
    Measurable (fun a => oracleSensitivity (ζ a) (r a) (X a) (Y a)) := by
  exact Finset.measurable_sum _ fun e _ =>
    (((measurable_pi_apply e).comp hζ).abs.mul ((measurable_pi_apply e).comp hr)).mul
      (measurable_queryMax hX hY e)

lemma measurableSet_commonTrialGood_joint {k : ℕ} {X Y : A → Mat n} {ε : A → ℝ}
    {z : A → Fin k → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hε : Measurable ε) (hz : Measurable z) :
    MeasurableSet {a | CommonTrialGood (X a) (Y a) (ε a) (z a)} := by
  have hg (X : A → Mat n) (hX : Measurable X) (j : Fin k) :
      Measurable (fun a => gaussianLogDensity (X a) (z a j)) := by
    have harg : Measurable (fun a => (X a, z a j)) :=
      hX.prodMk ((measurable_pi_apply j).comp hz)
    change Measurable ((fun p : Mat n × (Fin n → ℝ) => gaussianLogDensity p.1 p.2) ∘
      (fun a => (X a, z a j)))
    exact (measurable_gaussianLogDensity_pair n).comp harg
  have hb : Measurable (fun a => batchLogRatio (X a) (Y a) (z a)) := by
    unfold batchLogRatio
    exact Finset.measurable_sum _ fun j _ => (hg X hX j).sub (hg Y hY j)
  simp only [CommonTrialGood, Set.setOf_and, Set.setOf_forall]
  refine (measurableSet_le hb.abs hε).inter (MeasurableSet.iInter fun e => ?_)
  exact (measurableSet_le ((measurable_queryMax hX hY e).div_const 8)
    ((measurable_clippedWitness e).comp hz)).inter
      (measurableSet_le ((measurable_clippedWitness e).comp hz)
        ((measurable_queryMax hX hY e).const_mul 2))

lemma measurable_trialDensity (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam) :
    Measurable (fun p : Weights n × TrialSample n o.k => trialDensity o p.1 p.2) := by
  have hopt : Measurable (fun p : Weights n × TrialSample n o.k => optimizer o.lam p.1) :=
    (measurable_optimizer hn hl).comp measurable_fst
  have hgauss : Measurable (fun p : Weights n × TrialSample n o.k =>
      ∏ j, gaussianDensity (optimizer o.lam p.1) (p.2.1 j)) := by
    apply Finset.measurable_prod
    intro j _
    exact ((measurable_gaussianLogDensity_pair n).comp
      (hopt.prodMk (by fun_prop))).exp
  have hscore : Measurable (fun p : Weights n × TrialSample n o.k =>
      pairing p.1 (clippedWitness p.2.1)) :=
    Finset.measurable_sum _ fun e _ =>
      ((measurable_pi_apply e).comp measurable_fst).mul
        ((measurable_clippedWitness e).comp (measurable_fst.comp measurable_snd))
  exact hgauss.mul ((continuous_laplaceDensity _).measurable.comp
    ((measurable_snd.comp measurable_snd).sub hscore))

lemma measurable_trialLaw (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam) :
    Measurable (trialLaw (n := n) o) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [trialLaw_withDensity hn o hl, withDensity_apply _ hs]
  exact Measurable.lintegral_prod_right
    (show Measurable (Function.uncurry (fun D p => ENNReal.ofReal (trialDensity o D p))) from
      (measurable_trialDensity hn o hl).ennreal_ofReal)

lemma measurable_findWitness (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam)
    (he : 0 < o.eps1) :
    Measurable (fun p : Weights n × Weights n => findWitness o p.1 p.2) := by
  letI : ∀ p : Weights n × Weights n, IsProbabilityMeasure (trialLaw o p.1) :=
    fun p => trialLaw_probability o he p.1
  have hm := measurable_repeatUntil
    (show Measurable (fun p : Weights n × Weights n => trialLaw o p.1) from
      (measurable_trialLaw hn o hl).comp measurable_fst)
    ((measurable_acceptTrial o).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) o.K
  simp only [findWitness, findTrials_eq_repeatUntil o he]
  exact Measurable.ite (measurable_snd (measurableSet_singleton 0)) measurable_const hm

lemma measurableSet_trialGood_joint (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam)
    {D D' ζ r : A → Weights n} (hD : Measurable D) (hD' : Measurable D')
    (hζ : Measurable ζ) (hr : Measurable r) {p : A → TrialSample n o.k} (hp : Measurable p) :
    MeasurableSet {a | p a ∈ trialGood o (D a) (D' a) (ζ a) (r a)} := by
  have hX := (measurable_optimizer hn hl).comp hD
  have hY := (measurable_optimizer hn hl).comp hD'
  exact measurableSet_commonTrialGood_joint hX hY
    ((measurable_oracleSensitivity hX hY hζ hr).const_mul o.eps1) (measurable_fst.comp hp)

lemma measurable_auxiliaryFindWitness (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam)
    (he : 0 < o.eps1) {D D' ζ r : A → Weights n}
    (hD : Measurable D) (hD' : Measurable D') (hζ : Measurable ζ) (hr : Measurable r) :
    Measurable (fun a => auxiliaryFindWitness o (D a) (D' a) (ζ a) (r a)) := by
  letI : ∀ a : A, IsProbabilityMeasure (trialLaw o (D a)) :=
    fun a => trialLaw_probability o he (D a)
  have hc := measurable_conditional (G := fun a => trialGood o (D a) (D' a) (ζ a) (r a))
    (show Measurable (fun a => trialLaw o (D a)) from (measurable_trialLaw hn o hl).comp hD)
    (measurableSet_trialGood_joint hn o hl (hD.comp measurable_fst) (hD'.comp measurable_fst)
      (hζ.comp measurable_fst) (hr.comp measurable_fst) measurable_snd)
  have hm := measurable_repeatUntil_bounded hc (by norm_num : (1 : ℝ≥0∞) < ∞)
    (fun a => prob_le_one)
    ((measurable_acceptTrial o).comp ((hr.comp measurable_fst).prodMk measurable_snd)) o.K
  exact Measurable.ite (hr (measurableSet_singleton 0)) measurable_const hm

end DPCut
