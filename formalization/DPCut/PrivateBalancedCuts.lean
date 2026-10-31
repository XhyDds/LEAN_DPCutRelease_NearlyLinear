import DPCut.BalancedObjectives

/-! The three balanced-cut consequences of Appendix C.4, with explicit errors. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def BalancedObjectiveGuarantee {n : ℕ} (w : Weights n) (b c ρ η E : ℝ) (S : Finset (Fin n)) : Prop :=
  Balanced c S ∧
  cut w S ≤ (ρ / b) * (1 + η) / (1 - η) * constrainedOptimum w {R | Balanced b R} +
    (ρ / b + 1) / (1 - η) * E ∧
  expansion w S ≤ ρ * (1 + η) / (1 - η) * sInf (expansion w '' {R | Balanced b R}) +
    (ρ * (E / (b * n)) + E / (c * n)) / (1 - η) ∧
  uniformSparsity w S ≤ (2 * ρ) * (1 + η) / (1 - η) * sInf (uniformSparsity w '' {R | Balanced b R}) +
    ((2 * ρ) * (E / (b * (1 - b) * (n : ℝ) ^ 2)) + E / (c * (1 - c) * (n : ℝ) ^ 2)) / (1 - η)

lemma balanced_family_nonempty {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : b ≤ 1 / 3) :
    {S : Finset (Fin n) | Balanced b S}.Nonempty := by
  have hhalf := halfSubset_balanced (A := Finset.univ) (by simpa using hn) hb
  refine ⟨halfSubset Finset.univ, ?_⟩
  constructor
  · simpa using hhalf.2.1
  · have he : (((Finset.univ : Finset (Fin n)) \ halfSubset Finset.univ).card : ℝ) =
        n - ((halfSubset (Finset.univ : Finset (Fin n))).card : ℝ) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Nat.cast_sub (Finset.card_le_card (Finset.subset_univ _))]
      simp
    simpa only [Finset.card_univ, Fintype.card_fin, he] using hhalf.2.2

lemma balanced_objectives_transfer {n : ℕ} (hn : 2 ≤ n) {w h : Weights n} (hh : Nonnegative h)
    {b c ρ η E : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 3) (hc : 0 < c) (hc₁ : c ≤ 1 / 3)
    (hρ : 0 ≤ ρ) (hη : η < 1) (hE : 0 ≤ E) (hcuts : AllCuts w h η E)
    {S : Finset (Fin n)} (hS : Balanced c S)
    (happrox : expansion h S ≤ ρ * sInf (expansion h '' {R | Balanced b R})) :
    BalancedObjectiveGuarantee w b c ρ η E S := by
  have hF := balanced_family_nonempty hn hb₁
  have hnpos : 0 < n := by omega
  refine ⟨hS, ?_, ?_, ?_⟩
  · exact constrained_cut_transfer hF hη (div_nonneg hρ hb.le) hcuts
      (expansion_to_cut hnpos hh hb hc hρ hF hS happrox)
  · exact expansion_transfer hnpos hb hc hη hE hρ hF hcuts hS happrox
  · exact uniformSparsity_transfer hnpos hb (by linarith) hc (by linarith) hη hE
      (by positivity) hF hcuts hS (expansion_to_sparsity hnpos hh hρ hF happrox)

/-- Weighted ARV (or any balanced expansion solver) yields all three private
objectives. At fixed balances and relative error, the additive terms have orders
E, E/n, and E/n², respectively, with the displayed approximation factors. -/
theorem private_balanced_objectives : ∃ CA : ℝ, 0 < CA ∧ ∀ n, 2 ≤ n →
    ∀ p : Parameters, p.Valid → ∀ b c ρ τ : ℝ,
      0 < b → b ≤ 1 / 3 → 0 < c → c ≤ 1 / 3 → 0 ≤ ρ → 0 ≤ τ →
      ∀ K : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel K →
      (∀ h, Nonnegative h → HighProbability (K h) τ (fun S => Balanced c S ∧
        expansion h S ≤ ρ * sInf (expansion h '' {R | Balanced b R}))) →
      ∃ M : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel M ∧ EdgeDP M p.epsilon p.delta ∧
        ∀ w, Nonnegative w → HighProbability (M w) (p.beta + τ)
          (BalancedObjectiveGuarantee w b c ρ p.gamma (CA * mainError n p)) := by
  obtain ⟨CA, hCA, hrelease⟩ := theorem1_statistical
  refine ⟨CA, hCA, ?_⟩
  intro n hn p hp b c ρ τ hb hb₁ hc hc₁ hρ hτ K hK hAlg
  obtain ⟨M, hM, hgraph, hDP, hu⟩ := hrelease n hn p hp
  letI := hM
  letI := hK
  let R : Kernel (Weights n) (Finset (Fin n)) :=
    ⟨fun w => (M w).bind K, measurable_bind_kernel M.measurable (K.measurable.comp measurable_snd)⟩
  letI : IsMarkovKernel R := ⟨fun w => probability_bind (M w) K K.measurable⟩
  refine ⟨R, inferInstance, hDP.postprocess hp.2.2.1.le hp.2.2.2.2.1.le K, ?_⟩
  intro w hw
  have hE : 0 ≤ CA * mainError n p := by
    have hlog := (core_log_bounds hn (le_refl (1 : ℝ)) p hp).one_le
    have hγ := hp.1
    have hε := hp.2.2.1
    unfold mainError
    positivity
  apply ((hu w hw).and_ae (measurableSet_nonnegative measurable_id) (hgraph w hw)).bind K
    hp.2.2.2.2.2.2.1.le hτ (Set.toFinite _ |>.measurableSet)
  intro h hh
  apply (hAlg h hh.2).mono _ (Set.toFinite _ |>.measurableSet)
  intro S hS
  exact balanced_objectives_transfer hn hh.2 hb hb₁ hc hc₁ hρ (by linarith [hp.2.1]) hE hh.1 hS.1 hS.2

end DPCut
