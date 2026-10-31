import DPCut.SDPLSWProblem
import DPCut.OracleReplacementTV
import DPCut.MassClipping
import DPCut.ReleaseNonnegative

/-! The public objective guard is inactive along the actual release execution.
This is a deterministic invariant, including on noisy-mass failure events. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.OracleReplacement
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (hl : 0 < o.lam) (he : 0 < o.eps1)

def boundedInput (B : ℝ) (q : Weights n × Weights n) : Weights n × Weights n :=
  (boundedObjective B q.1, q.2)

lemma measurable_boundedInput (B : ℝ) : Measurable (boundedInput (n := n) B) :=
  ((measurable_boundedObjective n B).comp measurable_fst).prodMk measurable_snd

include hn hl he in
lemma measurable_boundedLaw (B : ℝ) :
    Measurable (fun q : Weights n × Weights n => findWitness o (boundedObjective B q.1) q.2) :=
  (measurable_findWitness hn o hl he).comp (f := boundedInput B) (measurable_boundedInput B)

def boundedKernel (B : ℝ) : WitnessKernel n :=
  ⟨fun q : Weights n × Weights n => findWitness o (boundedObjective B q.1) q.2,
    measurable_boundedLaw hn o hl he B⟩

instance boundedKernel_markov (B : ℝ) : IsMarkovKernel (boundedKernel hn o hl he B) := by
  constructor
  intro q
  change IsProbabilityMeasure (findWitness o (boundedObjective B q.1) q.2)
  exact findWitness_probability o he _ _

lemma boundedKernel_eq {B : ℝ} {D r : Weights n} (hD : l1 D ≤ B) :
    boundedKernel hn o hl he B (D,r) = findWitness o D r := by
  change findWitness o (boundedObjective B D) r = _
  rw [boundedObjective_eq hD]

lemma bounded_discrepancies {γ U cap B : ℝ} (hγ : 0 ≤ γ)
    (hB : cap + (1+γ) * Fintype.card (Edge n) * U ≤ B)
    {w h r : Weights n} (hw : Bounded U w) (hh : Nonnegative h)
    (hm : mass h ≤ cap) (hr : IsMask r) :
    l1 (plusDiscrepancy γ w h r) ≤ B ∧ l1 (minusDiscrepancy γ w h r) ≤ B := by
  have hw0 : Nonnegative w := fun e => (hw e).1
  have hwM : mass w ≤ Fintype.card (Edge n) * U := by
    calc
      _ ≤ ∑ _e : Edge n, U := Finset.sum_le_sum (fun e _ => (hw e).2)
      _ = _ := by simp
  have hu := mul_le_mul_of_nonneg_left hwM (by linarith : 0 ≤ 1+γ)
  have hp := plusDiscrepancy_l1_le hγ hw0 hh hr
  have hn := minusDiscrepancy_l1_le hγ hw0 hh hr
  constructor <;> nlinarith

include he in
lemma witness_bind_congr {α : Type} [MeasurableSpace α] (D r : Weights n) (hr : IsMask r)
    (P Q : Measure α) (f g : Weights n → Measure α) (hPQ : P = Q)
    (hfg : ∀ x, WitnessSupported r 0 (some x) → f x = g x) :
    (findWitness o D r).bind (fun x => x.elim P f) =
      (findWitness o D r).bind (fun x => x.elim Q g) := by
  apply Measure.bind_congr_right
  filter_upwards [findWitness_supported o he D r hr] with x hx
  cases x with
  | none => exact hPQ
  | some x => exact hfg x hx

include hn hl he

lemma aggregateLoop_bounded_eq_kernel (K : WitnessKernel n) {γ U cap B : ℝ} (hγ : 0 ≤ γ)
    (hB : cap + (1+γ) * Fintype.card (Edge n) * U ≤ B)
    (hK : ∀ D r, l1 D ≤ B → K (D,r) = findWitness o D r)
    {w h : Weights n} (hw : Bounded U w) (hh : Nonnegative h) (hm : mass h ≤ cap)
    (t : ℕ) (a : Aggregate n) (ha : IsMask a.residual) :
    aggregateLoop K γ w h t a = aggregateLoop (exactKernel hn o hl he) γ w h t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    by_cases hz : a.residual = 0
    · simp only [aggregateLoop, hz, if_true]
    · obtain ⟨hp, hm'⟩ := bounded_discrepancies hγ hB hw hh hm ha
      have hminus :
          (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind
            (fun g => g.elim (Measure.dirac a) (fun x => aggregateLoop K γ w h t (aggregateMinusStep a x))) =
          (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind
            (fun g => g.elim (Measure.dirac a) (fun x => aggregateLoop (exactKernel hn o hl he) γ w h t (aggregateMinusStep a x))) := by
        exact witness_bind_congr o he _ _ ha _ _ _ _ rfl
          (fun x hx => ih _ (witness_supported_residual _ _ _ ha hx))
      have hplus := witness_bind_congr o he (plusDiscrepancy γ w h a.residual) a.residual ha
        _ _ (fun x => aggregateLoop K γ w h t (aggregatePlusStep a x))
        (fun x => aggregateLoop (exactKernel hn o hl he) γ w h t (aggregatePlusStep a x)) hminus
        (fun x hx => ih _ (witness_supported_residual _ _ _ ha hx))
      simpa only [aggregateLoop, if_neg hz, hK _ _ hp, hK _ _ hm', exactKernel, Kernel.coe_mk] using hplus

lemma aggregateLoop_bounded_eq (K : WitnessKernel n) {γ U cap B : ℝ} (hγ : 0 ≤ γ)
    (hB : cap + (1+γ) * Fintype.card (Edge n) * U ≤ B)
    (hK : ∀ D r, l1 D ≤ B → K (D,r) = findWitness o D r)
    {w h : Weights n} (hw : Bounded U w) (hh : Nonnegative h) (hm : mass h ≤ cap)
    (t : ℕ) (a : Aggregate n) (ha : IsMask a.residual) :
    aggregateLoop K γ w h t a = DPCut.aggregateLoop o γ w h t a := by
  calc
    _ = aggregateLoop (exactKernel hn o hl he) γ w h t a :=
      aggregateLoop_bounded_eq_kernel hn o hl he K hγ hB hK hw hh hm t a ha
    _ = _ := aggregateLoop_exact hn o hl he γ w h t a

lemma innerLoop_bounded_eq (K : WitnessKernel n) (p : Parameters) (c : RunConfig) (hc : c.oracle = o)
    {U cap B : ℝ} (hγ : 0 ≤ p.gamma)
    (hB : cap + (1+p.gamma) * Fintype.card (Edge n) * U ≤ B)
    (hK : ∀ D r, l1 D ≤ B → K (D,r) = findWitness o D r)
    {w : Weights n} (hw : Bounded U w) {M : ℝ} (hM : 0 ≤ M) (hMc : M ≤ cap)
    (t : ℕ) (h : Weights n) (hh : Nonnegative h) (hm : mass h ≤ cap) :
    innerLoop K p c w M t h = DPCut.innerLoop p c w M t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    rw [innerLoop, DPCut.innerLoop_succ_eq]
    have hag : aggregateLaw K p.gamma w h =
        DPCut.aggregateLaw c.oracle p.gamma w h := by
      rw [hc]
      exact aggregateLoop_bounded_eq hn o hl he K hγ hB hK hw hh hm _ _ (by intro e; simp)
    rw [hag]
    congr 1
    funext a
    split_ifs
    · rfl
    · apply ih _ (innerNext_nonnegative c hh hM a)
      unfold innerNext
      split_ifs <;> exact (mwUpdate_mass_le hM _ _ _ _).trans hMc

lemma outerLoop_bounded_eq (K : WitnessKernel n) (p : Parameters) (c : RunConfig) (hc : c.oracle = o)
    (ho : OraclePrivacyBounds n c.oracle) {U B : ℝ} (hγ : 0 ≤ p.gamma)
    (hcap : 0 ≤ c.massCap)
    (hB : c.massCap + (1+p.gamma) * Fintype.card (Edge n) * U ≤ B)
    (hK : ∀ D r, l1 D ≤ B → K (D,r) = findWitness o D r)
    {w : Weights n} (hw : Bounded U w) (t : ℕ) (a out : Weights n) (ha : IsMask a) :
    outerLoop K p c w t a out = DPCut.outerLoop p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    rw [outerLoop, DPCut.outerLoop_succ_raw]
    congr 1
    funext noise
    dsimp only [DPCut.outerAfterMass]
    split_ifs
    · rfl
    · let M := clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2
      have hM : 0 ≤ M := clipNoisyMass_nonneg _ _ _ _
      have hMc : M ≤ c.massCap := clipNoisyMass_le_cap hcap _ _ _
      have hwi : Bounded U (hadamard a w) := fun e =>
        ⟨mul_nonneg (ha e).1 (hw e).1,
          (mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2⟩
      rw [innerLoop_bounded_eq hn o hl he K p c hc hγ hB hK hwi hM hMc _ _
        (initialEstimate_nonnegative ha hM) ((initialEstimate_mass_le hM a).trans hMc)]
      apply Measure.bind_congr_right
      filter_upwards [innerLoop_supported hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)] with r hr
      cases r with
      | none => exact ih a out ha
      | some hr' => exact ih _ _ (residualUpdate_isMask ha hr)

end DPCut.OracleReplacement
