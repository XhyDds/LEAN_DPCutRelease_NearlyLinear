import DPCut.CutReleaseInvariant

/-! Nonnegative synthetic weights, including on utility failures and fallback branches. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma mwUpdate_nonnegative {n : ℕ} {h : Weights n} (hh : Nonnegative h)
    {M : ℝ} (hM : 0 ≤ M) (θ η : ℝ) (g : Weights n) :
    Nonnegative (mwUpdate M θ η h g) := by
  intro e
  exact div_nonneg (mul_nonneg hM (mul_nonneg (hh e) (Real.exp_pos _).le))
    (Finset.sum_nonneg fun f _ => mul_nonneg (hh f) (Real.exp_pos _).le)

lemma innerNext_nonnegative {n : ℕ} (c : RunConfig) {h : Weights n} (hh : Nonnegative h)
    {M : ℝ} (hM : 0 ≤ M) (a : Aggregate n) : Nonnegative (innerNext c M h a) := by
  unfold innerNext
  split_ifs <;> exact mwUpdate_nonnegative hh hM _ _ _

def InnerNonnegative {n : ℕ} (result : Option (Weights n × Weights n)) : Prop :=
  result.elim True (fun hr => Nonnegative hr.1)

lemma measurableSet_innerNonnegative {n : ℕ} :
    MeasurableSet {r : Option (Weights n × Weights n) | InnerNonnegative r} :=
  measurableSet_option_elim (measurableSet_nonnegative measurable_fst)

theorem innerLoop_nonnegative {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) {M : ℝ} (hM : 0 ≤ M)
    (t : ℕ) (h : Weights n) (hh : Nonnegative h) :
    ∀ᵐ r ∂innerLoop p c w M t h, InnerNonnegative r := by
  induction t generalizing h with
  | zero => exact (ae_dirac_iff measurableSet_innerNonnegative).mpr trivial
  | succ t ih =>
    rw [innerLoop_succ_eq]
    apply ae_bind_of_ae_ae (measurable_inner_continuation hn p c ho w h M t) measurableSet_innerNonnegative
    apply Filter.Eventually.of_forall
    intro a
    split_ifs
    · exact (ae_dirac_iff measurableSet_innerNonnegative).mpr hh
    · exact ih _ (innerNext_nonnegative c hh hM a)

lemma initialEstimate_nonnegative {n : ℕ} {a : Weights n} (ha : IsMask a)
    {M : ℝ} (hM : 0 ≤ M) : Nonnegative (initialEstimate M a) := by
  intro e
  exact div_nonneg (mul_nonneg hM (ha e).1) (Finset.sum_nonneg fun f _ => (ha f).1)

theorem outerLoop_nonnegative {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (w : Weights n)
    (t : ℕ) (a out : Weights n) (ha : IsMask a) (hout : Nonnegative out) :
    ∀ᵐ h ∂outerLoop p c w t a out, Nonnegative h := by
  have hN : MeasurableSet {h : Weights n | Nonnegative h} := measurableSet_nonnegative measurable_id
  induction t generalizing a out with
  | zero => exact (ae_dirac_iff hN).mpr hout
  | succ t ih =>
    rw [outerLoop_succ_raw]
    apply ae_bind_of_ae_ae
      ((measurable_outerAfterMass hn p c ho he w a out t).comp
        (show Measurable (fun z : ℝ => clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2) by fun_prop)) hN
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [Function.comp_def]
    unfold outerAfterMass
    split_ifs
    · exact (ae_dirac_iff hN).mpr hout
    · apply ae_bind_of_ae_ae (measurable_outerResult hn p c ho he w a out t) hN
      filter_upwards [innerLoop_nonnegative hn p c ho (hadamard a w) (clipNoisyMass_nonneg _ _ _ _) c.T2 _
        (initialEstimate_nonnegative ha (clipNoisyMass_nonneg _ _ _ _)),
        innerLoop_supported hn p c ho (hadamard a w) _ c.T2
          (initialEstimate (clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2) a)] with r hr hmask
      cases r with
      | none => exact ih a out ha hout
      | some pair =>
        exact ih _ _ (residualUpdate_isMask ha hmask)
          (fun e => add_nonneg (hout e) (mul_nonneg (hr e) (hmask e).1))

theorem cutRelease_nonnegative {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∀ᵐ h ∂cutReleaseLaw U p outerUtilityConstants w, Nonnegative h := by
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  exact outerLoop_nonnegative hn p _ hc.oracle_privacy hc.eps2_pos w _ 1 0
    (by intro e; norm_num) (by intro e; simp)

end DPCut
