import DPCut.OracleMeasurable
import DPCut.OptionStandardBorel
import DPCut.Lemma16

/-! Residual masks and privacy accounting along witness transcripts. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

abbrev WitnessHistory (n : ℕ) := List (Option (Weights n))

def witnessResidual {n : ℕ} (h : WitnessHistory n) : Weights n :=
  fun e => 1 - transcriptSum none (fun _ _ (y : Option (Weights n)) => y.getD 0 e) h

lemma witnessResidual_nil (n : ℕ) : witnessResidual ([] : WitnessHistory n) = 1 := by
  ext e
  simp [witnessResidual, transcriptSum]

lemma witnessResidual_append {n : ℕ} (h : WitnessHistory n) (y : Option (Weights n)) :
    witnessResidual (h ++ [y]) = witnessResidual h - y.getD 0 := by
  ext e
  simp only [witnessResidual, transcriptSum_append, Pi.sub_apply]
  ring

lemma measurable_witnessResidual {n : ℕ} : Measurable (witnessResidual (n := n)) := by
  apply measurable_pi_lambda
  intro e
  exact measurable_const.sub (measurable_transcriptSum none fun _ =>
    (measurable_pi_apply e).comp ((measurable_option_getD (0 : Weights n)).comp measurable_snd))

lemma measurableSet_isMask {A : Type*} [MeasurableSpace A] {n : ℕ}
    {r : A → Weights n} (hr : Measurable r) : MeasurableSet {a | IsMask (r a)} := by
  simp only [IsMask, Bounded, Set.setOf_forall, Set.setOf_and]
  exact MeasurableSet.iInter fun e =>
    (measurableSet_le measurable_const ((measurable_pi_apply e).comp hr)).inter
      (measurableSet_le ((measurable_pi_apply e).comp hr) measurable_const)

def witnessPotential {n : ℕ} (ζ : Weights n) (h : WitnessHistory n) : ℝ :=
  pairing (fun e => |ζ e|) (1 - witnessResidual h)

lemma measurable_witnessPotential {n : ℕ} (ζ : Weights n) :
    Measurable (witnessPotential ζ) := by
  exact Finset.measurable_sum _ fun e _ =>
    (measurable_const.sub ((measurable_pi_apply e).comp measurable_witnessResidual)).const_mul _

lemma witnessPotential_nil {n : ℕ} (ζ : Weights n) : witnessPotential ζ [] = 0 := by
  simp [witnessPotential, witnessResidual_nil, pairing]

lemma witnessPotential_append {n : ℕ} (ζ : Weights n) (h : WitnessHistory n)
    (y : Option (Weights n)) : witnessPotential ζ (h ++ [y]) =
      witnessPotential ζ h + pairing (fun e => |ζ e|) (y.getD 0) := by
  simp only [witnessPotential, witnessResidual_append, pairing, Pi.sub_apply, Pi.one_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma witnessPotential_le {n : ℕ} (ζ : Weights n) {h : WitnessHistory n}
    (hr : IsMask (witnessResidual h)) : witnessPotential ζ h ≤ l1 ζ := by
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_of_le_one_right (abs_nonneg _) (by dsimp; linarith [(hr e).1])

lemma witnessSupported_none_residual {n : ℕ} (r q : Weights n)
    (hr : IsMask r) (y : Option (Weights n)) (hy : WitnessSupported r q y) :
    IsMask (r - y.getD 0) := by
  cases y with
  | none => simpa using hr
  | some g => exact witness_supported_residual r q g hr hy

/-- A successful local charge pays for a decrease in the residual potential. -/
lemma witnessSupported_stepCharge {n : ℕ} (o : OracleConfig) (he : 0 ≤ o.eps1)
    (ζ r q : Weights n) (y : Option (Weights n)) (hy : WitnessSupported r q y) :
    stepCharge none (10 * o.K * o.eps1 * (∑ e, |ζ e| * r e * q e)) y ≤
      80 * o.K * o.eps1 * pairing (fun e => |ζ e|) (y.getD 0) := by
  cases y with
  | none => simp [stepCharge, pairing]
  | some g => simpa [stepCharge] using witness_success_charge o he ζ r q g hy

/-- Generic finite transcript accounting, including padding and failed attempts. -/
theorem witnessTranscript_budget {n : ℕ} (P : Sequential (Option (Weights n)))
    [∀ t, IsMarkovKernel (P t)] (ell : ℕ → WitnessHistory n → ℝ)
    (hm : ∀ t, Measurable (ell t)) (ζ : Weights n) {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ t h, IsMask (witnessResidual h) → ∀ᵐ y ∂P t h,
      IsMask (witnessResidual h - y.getD 0) ∧
      stepCharge none (ell t h) y ≤ C * pairing (fun e => |ζ e|) (y.getD 0))
    (k : ℕ) :
    ∀ᵐ h ∂sequentialLaw P k,
      IsMask (witnessResidual h) ∧ successCharge none ell h ≤ C * l1 ζ := by
  have hmeas : MeasurableSet {h : WitnessHistory n |
      IsMask (witnessResidual h) ∧ successCharge none ell h ≤ C * witnessPotential ζ h} :=
    (measurableSet_isMask measurable_witnessResidual).inter
      (measurableSet_le (measurable_successCharge none hm)
        ((measurable_witnessPotential ζ).const_mul C))
  have hi (t : ℕ) : ∀ᵐ h ∂sequentialLaw P t,
      IsMask (witnessResidual h) ∧ successCharge none ell h ≤ C * witnessPotential ζ h := by
    induction t with
    | zero =>
      apply (ae_dirac_iff hmeas).mpr
      simp [witnessResidual_nil, IsMask, Bounded, successCharge, witnessPotential_nil]
    | succ t ih =>
      rw [sequentialLaw_succ (none : Option (Weights n))]
      apply (ae_map_iff (measurable_list_append_one none).aemeasurable hmeas).mpr
      apply Measure.ae_compProd_of_ae_ae
      · exact hmeas.preimage (measurable_list_append_one none)
      · filter_upwards [ih, sequentialLaw_length P t] with h hh hlen
        filter_upwards [hstep t h hh.1] with y hy
        rw [witnessResidual_append, successCharge_append, hlen, witnessPotential_append]
        refine ⟨hy.1, ?_⟩
        nlinarith [hh.2, hy.2]
  exact (hi k).mono fun h hh => ⟨hh.1, hh.2.trans
    (mul_le_mul_of_nonneg_left (witnessPotential_le ζ hh.1) hC)⟩

end DPCut
