import DPCut.SequentialLikelihood
import DPCut.MomentPrivacy
import DPCut.TotalVariation

/-! The auxiliary adaptive process in Lemma 16 stays on common histories. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {Y : Type*} [MeasurableSpace Y] [Inhabited Y]

/-- Absolute continuity is propagated simultaneously on both inputs. In particular, the
auxiliary laws put zero mass on histories where the conditional hypotheses are unavailable. -/
theorem auxiliary_sequential_ac (P₀ P₁ N₀ N₁ : Sequential Y)
    [∀ t, IsMarkovKernel (P₀ t)] [∀ t, IsMarkovKernel (P₁ t)]
    [∀ t, IsMarkovKernel (N₀ t)] [∀ t, IsMarkovKernel (N₁ t)]
    (k : ℕ) {ell : ℕ → List Y → ℝ}
    (hs : ∀ t < k, ∀ h, CommonPrefix P₀ P₁ t h →
      N₀ t h ≪ P₀ t h ∧ N₁ t h ≪ P₁ t h ∧
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0) :
    (sequentialLaw N₀ k ≪ sequentialLaw P₀ k ∧ sequentialLaw N₀ k ≪ sequentialLaw P₁ k) ∧
    (sequentialLaw N₁ k ≪ sequentialLaw P₀ k ∧ sequentialLaw N₁ k ≪ sequentialLaw P₁ k) := by
  induction k with
  | zero => exact ⟨⟨.rfl, .rfl⟩, ⟨.rfl, .rfl⟩⟩
  | succ k ih =>
    obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ := ih (fun t ht => hs t (by omega))
    have hc0 := ae_commonPrefix P₀ P₁ k (sequentialLaw N₀ k) h00 h01
    have hc1 := ae_commonPrefix P₀ P₁ k (sequentialLaw N₁ k) h10 h11
    refine ⟨⟨sequentialLaw_ac_succ P₀ N₀ k h00 ?_,
      sequentialLaw_ac_succ P₁ N₀ k h01 ?_⟩,
      ⟨sequentialLaw_ac_succ P₀ N₁ k h10 ?_, sequentialLaw_ac_succ P₁ N₁ k h11 ?_⟩⟩
    · exact hc0.mono fun h hh => (hs k (by omega) h hh).1
    · exact hc0.mono fun h hh =>
        (hs k (by omega) h hh).2.2.ac.trans (hs k (by omega) h hh).2.1
    · exact hc1.mono fun h hh =>
        (hs k (by omega) h hh).2.2.symm.ac.trans (hs k (by omega) h hh).1
    · exact hc1.mono fun h hh => (hs k (by omega) h hh).2.1

/-- The case of zero conditional pure-privacy loss gives equality of transcript laws. -/
theorem sequential_eq_of_zero_loss (N₀ N₁ : Sequential Y)
    [∀ t, IsMarkovKernel (N₀ t)] [∀ t, IsMarkovKernel (N₁ t)] (k : ℕ)
    (hs : ∀ t < k, ∀ᵐ h ∂sequentialLaw N₁ t,
      Indistinguishable (N₀ t h) (N₁ t h) 0 0) :
    sequentialLaw N₀ k = sequentialLaw N₁ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sequentialLaw_succ (default : Y), sequentialLaw_succ (default : Y),
      ih (fun t ht => hs t (by omega))]
    congr 1
    exact Measure.compProd_congr ((hs k (by omega)).mono fun _ hh => hh.zero_eq)

/-- The auxiliary process's one-sided guarantee, before the TV transfer. -/
theorem success_charged_aux_direction [StandardBorelSpace Y] (N₀ N₁ : Sequential Y)
    [∀ t, IsMarkovKernel (N₀ t)] [∀ t, IsMarkovKernel (N₁ t)]
    (bottom : Y) (k : ℕ) {ell : ℕ → List Y → ℝ} (hell : ∀ t, Measurable (ell t))
    {ellStar L δ : ℝ} (hstar : 0 < ellStar) (hstar1 : ellStar < 1 / 10) (hδ : 0 < δ)
    (h₀ : ∀ t < k, ∀ᵐ h ∂sequentialLaw N₀ t,
      0 ≤ ell t h ∧ ell t h ≤ ellStar ∧
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0)
    (h₁ : ∀ t < k, ∀ᵐ h ∂sequentialLaw N₁ t,
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0)
    (hbudget : ∀ᵐ h ∂sequentialLaw N₀ k, successCharge bottom ell h ≤ L)
    (s : Set (List Y)) (hs : MeasurableSet s) :
    sequentialLaw N₀ k s ≤ ENNReal.ofReal (Real.exp (4 * L + 4 * ellStar * Real.log (1 / δ))) *
      sequentialLaw N₁ k s + ENNReal.ofReal δ := by
  let a : ℝ := 1 / (4 * ellStar)
  let z : ℕ → List Y → Y → ℝ := fun t => kernelLogRatio (N₀ t) (N₁ t)
  let v : ℕ → List Y → Y → ℝ := fun t h y => a * (z t h y - 4 * stepCharge bottom (ell t h) y)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by positivity : 0 < 4 * ellStar)).mpr
    linarith
  have haStar : a * ellStar = 1 / 4 := by dsimp [a]; field_simp
  have hz (t : ℕ) : Measurable (Function.uncurry (z t)) := measurable_kernelLogRatio _ _
  have hv (t : ℕ) : Measurable (Function.uncurry (v t)) := by
    have hc : Measurable (fun p : List Y × Y => stepCharge bottom (ell t p.1) p.2) :=
      Measurable.ite (measurable_snd (measurableSet_singleton bottom))
        measurable_const ((hell t).comp measurable_fst)
    exact measurable_const.mul ((hz t).sub (measurable_const.mul hc))
  have hd : (sequentialLaw N₁ k).withDensity
      (fun h => ENNReal.ofReal (Real.exp (transcriptSum bottom z h))) = sequentialLaw N₀ k := by
    apply sequential_withDensity N₀ N₁ bottom hz k
    intro t ht
    exact (h₁ t ht).mono fun h hh => withDensity_exp_kernelLogRatio (N₀ t) (N₁ t) h hh.ac hh.symm.ac
  have hm : ∫⁻ h, ENNReal.ofReal (Real.exp (transcriptSum bottom v h)) ∂sequentialLaw N₀ k ≤ 1 := by
    apply sequential_exp_moment N₀ bottom hv k
    intro t ht
    filter_upwards [h₀ t ht] with h hh
    exact kernel_success_charged_one_step (N₀ t) (N₁ t) bottom h ha1 hh.1
      (hh.2.1.trans hstar1.le)
      ((mul_le_mul_of_nonneg_left hh.2.1 ha.le).trans_eq haStar) hh.2.2
  have hvsum (h : List Y) : transcriptSum bottom v h =
      a * (transcriptSum bottom z h - 4 * successCharge bottom ell h) := by
    simp only [transcriptSum, v, successCharge_eq_transcriptSum,
      mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  simp_rw [hvsum] at hm
  apply privacy_of_charged_moment (measurable_transcriptSum bottom hz)
    (measurable_successCharge bottom hell) hd ha hδ ?_ hbudget hm s hs
  dsimp [a]
  field_simp
  ring_nf
  exact le_rfl

end DPCut
