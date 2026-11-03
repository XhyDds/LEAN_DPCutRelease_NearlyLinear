import DPCut.SuccessChargedComposition

/-!
Lemma 16 (`lem:pay-what-you-get`): success-charged composition, `SuccessChargedStatement`.
The auxiliary processes are used directly: their absolute continuity keeps them on common
histories, and TV accumulation integrates conditional errors under the auxiliary histories.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut

/-- Success-charged composition, with the paper's exact constants:
`epsilon = 4 L + 4 ellStar log (1 / delta'')` and
`delta = delta'' + (1 + exp epsilon) k delta'`. -/
theorem lemma16 : SuccessChargedStatement := by
  intro Y _ _ _ bottom P₀ P₁ N₀ N₁ k ell ellStar L δ' δ''
    hmarkov hell hstar hstar1 hL hδ' hδ'' _ hlocal hbudget0 hbudget1
  letI (t : ℕ) : IsMarkovKernel (P₀ t) := (hmarkov t).1
  letI (t : ℕ) : IsMarkovKernel (P₁ t) := (hmarkov t).2.1
  letI (t : ℕ) : IsMarkovKernel (N₀ t) := (hmarkov t).2.2.1
  letI (t : ℕ) : IsMarkovKernel (N₁ t) := (hmarkov t).2.2.2
  have hcommon (t : ℕ) (ht : t < k) :
      (∀ᵐ h ∂sequentialLaw N₀ t, CommonPrefix P₀ P₁ t h) ∧
      (∀ᵐ h ∂sequentialLaw N₁ t, CommonPrefix P₀ P₁ t h) := by
    have hac := auxiliary_sequential_ac P₀ P₁ N₀ N₁ t (ell := ell) (by
      intro j hj h hc
      obtain ⟨_, _, h0, h1, _, _, hp⟩ := hlocal j (by omega) h hc
      exact ⟨h0, h1, hp⟩)
    exact ⟨ae_commonPrefix P₀ P₁ t _ hac.1.1 hac.1.2,
      ae_commonPrefix P₀ P₁ t _ hac.2.1 hac.2.2⟩
  have ht0 : TVClose (sequentialLaw P₀ k) (sequentialLaw N₀ k) (k * δ') := by
    apply sequential_tv P₀ N₀ k hδ'
    intro t ht
    filter_upwards [(hcommon t ht).1] with h hh
    exact (hlocal t ht h hh).2.2.2.2.1
  have ht1 : TVClose (sequentialLaw P₁ k) (sequentialLaw N₁ k) (k * δ') := by
    apply sequential_tv P₁ N₁ k hδ'
    intro t ht
    filter_upwards [(hcommon t ht).2] with h hh
    exact (hlocal t ht h hh).2.2.2.2.2.1
  have hc0 (t : ℕ) (ht : t < k) : ∀ᵐ h ∂sequentialLaw N₀ t,
      0 ≤ ell t h ∧ ell t h ≤ ellStar ∧
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0 := by
    filter_upwards [(hcommon t ht).1] with h hh
    obtain ⟨he, he', _, _, _, _, hp⟩ := hlocal t ht h hh
    exact ⟨he, he', hp⟩
  have hc1 (t : ℕ) (ht : t < k) : ∀ᵐ h ∂sequentialLaw N₁ t,
      0 ≤ ell t h ∧ ell t h ≤ ellStar ∧
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0 := by
    filter_upwards [(hcommon t ht).2] with h hh
    obtain ⟨he, he', _, _, _, _, hp⟩ := hlocal t ht h hh
    exact ⟨he, he', hp⟩
  have hp : Indistinguishable (sequentialLaw N₀ k) (sequentialLaw N₁ k)
      (4 * L + 4 * ellStar * Real.log (1 / δ'')) δ'' := by
    rcases eq_or_lt_of_le hstar with rfl | hstar
    · have heq : sequentialLaw N₀ k = sequentialLaw N₁ k := by
        apply sequential_eq_of_zero_loss N₀ N₁ k
        intro t ht
        filter_upwards [hc1 t ht] with h hh
        have he : ell t h = 0 := le_antisymm hh.2.1 hh.1
        simpa only [he] using hh.2.2
      apply Indistinguishable.of_eq heq _ hδ''.le
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hL
    · constructor
      · exact success_charged_aux_direction N₀ N₁ bottom k hell hstar hstar1 hδ'' hc0
          (fun t ht => (hc1 t ht).mono fun _ hh => hh.2.2) hbudget0
      · exact success_charged_aux_direction N₁ N₀ bottom k hell hstar hstar1 hδ''
          (fun t ht => (hc1 t ht).mono fun _ hh => ⟨hh.1, hh.2.1, hh.2.2.symm⟩)
          (fun t ht => (hc0 t ht).mono fun _ hh => hh.2.2.symm) hbudget1
  simpa only [mul_assoc] using hp.tv_transfer hδ''.le ht0 ht1

end DPCut
