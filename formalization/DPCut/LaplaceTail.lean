import DPCut.LaplaceDensity

/-! Exact one-sided Laplace tail bounds used by Lemma 20. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DPCut

lemma prob_laplace_eq_integral {b : ℝ} (hb : 0 < b) {s : Set ℝ}
    (hs : MeasurableSet s) : prob (laplace b) s = ∫ x in s, laplaceDensity b x := by
  have hi : Integrable (laplaceDensity b) := (laplace_exp_integrable hb).const_mul _
  rw [prob, laplace, withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
    hi.integrableOn (Filter.Eventually.of_forall fun x => (laplaceDensity_pos hb x).le),
    ENNReal.toReal_ofReal (integral_nonneg fun x => (laplaceDensity_pos hb x).le)]

lemma laplace_upper_tail {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    prob (laplace b) (Ioi t) = Real.exp (-t / b) / 2 := by
  rw [prob_laplace_eq_integral hb measurableSet_Ioi]
  have he : (∫ x in Ioi t, Real.exp (-|x| / b)) = b * Real.exp (-t / b) := by
    calc
      _ = ∫ x in Ioi t, Real.exp (-(b⁻¹) * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp
        rw [abs_of_nonneg (ht.trans hx.le)]
        congr 1
        ring
      _ = _ := by rw [integral_exp_mul_Ioi (neg_neg_of_pos (inv_pos.mpr hb))]; simp [div_eq_mul_inv, mul_comm, neg_mul, mul_neg]
  simp only [laplaceDensity, integral_const_mul, he]
  field_simp

lemma laplace_lower_tail {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    prob (laplace b) (Iic (-t)) = Real.exp (-t / b) / 2 := by
  rw [prob_laplace_eq_integral hb measurableSet_Iic]
  have he : (∫ x in Iic (-t), Real.exp (-|x| / b)) = b * Real.exp (-t / b) := by
    calc
      _ = ∫ x in Iic (-t), Real.exp (b⁻¹ * x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        dsimp
        rw [abs_of_nonpos (hx.trans (neg_nonpos.mpr ht))]
        congr 1
        ring
      _ = _ := by rw [integral_exp_mul_Iic (inv_pos.mpr hb)]; simp [div_eq_mul_inv, mul_comm, mul_neg]
  simp only [laplaceDensity, integral_const_mul, he]
  field_simp

lemma laplace_calibrated_tails {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    let τ := Real.log (1 / β) / ε
    0 < τ ∧ prob (laplace (1 / ε)) (Ioi τ) = β / 2 ∧
      1 - β / 2 ≤ prob (laplace (1 / ε)) (Ici (-τ)) := by
  dsimp
  let τ := Real.log (1 / β) / ε
  have hτ : 0 < τ := div_pos (Real.log_pos ((one_lt_div hβ).mpr hβ1)) hε
  have he : Real.exp (-τ / (1 / ε)) = β := by
    have heq : -τ / (1 / ε) = Real.log β := by
      dsimp [τ]
      rw [Real.log_div (by norm_num) hβ.ne', Real.log_one]
      field_simp
      ring
    rw [heq, Real.exp_log hβ]
  have hu := laplace_upper_tail (one_div_pos.mpr hε) hτ.le
  have hl := laplace_lower_tail (one_div_pos.mpr hε) hτ.le
  rw [he] at hu hl
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hε)
  have hc := measureReal_add_measureReal_compl (μ := laplace (1 / ε))
    (s := Iic (-τ)) measurableSet_Iic
  rw [measureReal_univ_eq_one, compl_Iic] at hc
  have hm := measureReal_mono (μ := laplace (1 / ε)) (Ioi_subset_Ici_self (a := -τ))
  change prob (laplace (1 / ε)) (Ioi (-τ)) ≤ prob (laplace (1 / ε)) (Ici (-τ)) at hm
  change prob (laplace (1 / ε)) (Iic (-τ)) + prob (laplace (1 / ε)) (Ioi (-τ)) = 1 at hc
  exact ⟨hτ, hu, by linarith⟩

end DPCut
