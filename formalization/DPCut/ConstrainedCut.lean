import DPCut.ApplicationOptima
import DPCut.ApplicationPostprocessing

/-! Appendix C: private bicriteria cut minimization, with exact constants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

lemma constrained_cut_transfer {n : ℕ} {w h : Weights n} {F : Set (Finset (Fin n))}
    (hF : F.Nonempty) {η A ρ : ℝ} (hη : η < 1) (hρ : 0 ≤ ρ)
    (hc : AllCuts w h η A) {S : Finset (Fin n)}
    (hS : cut h S ≤ ρ * constrainedOptimum h F) :
    cut w S ≤ ρ * (1 + η) / (1 - η) * constrainedOptimum w F + (ρ + 1) / (1 - η) * A := by
  obtain ⟨Sstar, hstar, hopt⟩ := constrainedOptimum_exists w hF
  have h₁ := (abs_le.mp (hc S)).2
  have h₂ := (abs_le.mp (hc Sstar)).1
  rw [hopt] at h₂
  have hs := mul_le_mul_of_nonneg_left (constrainedOptimum_le h hstar) hρ
  have hr := mul_le_mul_of_nonneg_left h₂ hρ
  have hpos : 0 < 1 - η := by linarith
  have hh : cut w S ≤ (ρ * (1 + η) * constrainedOptimum w F + (ρ + 1) * A) / (1 - η) :=
    (le_div_iff₀ hpos).mpr (by nlinarith)
  convert hh using 1
  ring

theorem constrained_cut : ConstrainedCutStatement := by
  intro n _hn F F' hF _hF' η ε δ β ρ τ A hη hη1 hε _hε1 hδ _hδ1 hβ _hβ1 hρ hτ _hτ1
    _hA M K hM hK hgraph hDP hrelease halgorithm
  letI : IsMarkovKernel M := hM
  letI : IsMarkovKernel K := hK
  refine ⟨EdgeDP.postprocess hε.le hδ.le hDP K, ?_⟩
  intro w hw
  have hg := (hrelease w hw).and_ae (measurableSet_nonnegative measurable_id) (hgraph w hw)
  apply hg.bind K hβ.le hτ (Set.toFinite _ |>.measurableSet)
  intro h hh
  apply (halgorithm h hh.2).mono (K h) (Set.toFinite _ |>.measurableSet)
  intro S hS
  exact ⟨hS.1, constrained_cut_transfer hF (by linarith) (by linarith) hh.1 hS.2⟩

end DPCut
