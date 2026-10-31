import DPCut.NoisyMassPrivacy

/-! Joint Laplace privacy for a finite vector with unit ℓ₁ sensitivity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DPCut

lemma shifted_laplace_pi_density {ι : Type*} [Fintype ι] {b : ℝ}
    (hb : 0 < b) (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => laplace b)).map (fun z => a + z) =
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))).withDensity
        (fun y => ENNReal.ofReal (∏ i, laplaceDensity b (y i - a i))) := by
  letI := laplace_isProbabilityMeasure hb
  have hm : (Measure.pi (fun _ : ι => laplace b)).map (fun z => a + z) =
      Measure.pi (fun i => (laplace b).map (fun x => a i + x)) :=
    Measure.pi_map_pi (fun _ => (measurable_const.add measurable_id).aemeasurable)
  rw [hm]
  simp_rw [shifted_laplace_density]
  apply pi_withDensity_ofReal
  · intro i
    have hi : Integrable (laplaceDensity b) :=
      (laplace_exp_integrable hb).const_mul (2 * b)⁻¹
    exact (measurePreserving_sub_right volume (a i)).integrable_comp_of_integrable hi
  · exact fun _ _ => (laplaceDensity_pos hb _).le

lemma laplace_pi_density_shift_le {ι : Type*} [Fintype ι] {ε : ℝ}
    (hε : 0 < ε) (a c y : ι → ℝ) (hac : ∑ i, |a i - c i| ≤ 1) :
    (∏ i, laplaceDensity (1 / ε) (y i - a i)) ≤
      Real.exp ε * ∏ i, laplaceDensity (1 / ε) (y i - c i) := by
  calc
    _ ≤ ∏ i, (Real.exp (|a i - c i| / (1 / ε)) *
        laplaceDensity (1 / ε) (y i - c i)) :=
      Finset.prod_le_prod (fun _ _ => (laplaceDensity_pos (by positivity) _).le)
        (fun i _ => laplaceDensity_shift_le (by positivity) (a i) (c i) (y i))
    _ = Real.exp ((∑ i, |a i - c i|) * ε) *
        ∏ i, laplaceDensity (1 / ε) (y i - c i) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith))
      (Finset.prod_nonneg fun _ _ => (laplaceDensity_pos (by positivity) _).le)

theorem shifted_laplace_pi_private {ι : Type*} [Fintype ι] {ε : ℝ}
    (hε : 0 < ε) (a c : ι → ℝ) (hac : ∑ i, |a i - c i| ≤ 1) :
    Indistinguishable
      ((Measure.pi (fun _ : ι => laplace (1 / ε))).map (fun z => a + z))
      ((Measure.pi (fun _ : ι => laplace (1 / ε))).map (fun z => c + z)) ε 0 := by
  rw [shifted_laplace_pi_density (by positivity), shifted_laplace_pi_density (by positivity)]
  simpa only [Measure.restrict_univ] using restricted_density_private
    (Measure.pi (fun _ : ι => (volume : Measure ℝ)))
    (fun y => ∏ i, laplaceDensity (1 / ε) (y i - a i))
    (fun y => ∏ i, laplaceDensity (1 / ε) (y i - c i))
    MeasurableSet.univ ε (fun y _ =>
      ⟨laplace_pi_density_shift_le hε a c y hac,
        laplace_pi_density_shift_le hε c a y (by simpa only [abs_sub_comm] using hac)⟩)

end DPCut
