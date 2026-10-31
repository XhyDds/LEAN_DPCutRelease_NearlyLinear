import DPCut.OracleTrial
import DPCut.ConditioningPrivacy

/-! Masking contracts edge adjacency, and the noisy-mass release is pure private. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut

lemma Adjacent.mask {n : ℕ} {w w' a : Weights n} (h : Adjacent w w') (ha : IsMask a) :
    Adjacent (hadamard a w) (hadamard a w') := by
  apply le_trans _ h
  unfold l1
  apply Finset.sum_le_sum
  intro e _
  change |a e * w e - a e * w' e| ≤ |w e - w' e|
  rw [← mul_sub, abs_mul, abs_of_nonneg (ha e).1]
  exact (mul_le_mul_of_nonneg_right (ha e).2 (abs_nonneg _)).trans_eq (one_mul _)

lemma mass_sensitivity {n : ℕ} {w w' : Weights n} (h : Adjacent w w') :
    |mass w - mass w'| ≤ 1 := by
  apply le_trans _ h
  simp only [mass, l1, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

lemma residualUpdate_isMask {n : ℕ} {a r : Weights n} (ha : IsMask a) (hr : IsMask r) :
    IsMask (residualUpdate a r) := by
  intro e
  change 0 ≤ a e * (1 - r e) ∧ a e * (1 - r e) ≤ 1
  refine ⟨mul_nonneg (ha e).1 (by linarith [(hr e).2]), ?_⟩
  nlinarith only [(ha e).1, (ha e).2, (hr e).1, mul_nonneg (ha e).1 (hr e).1]

def shiftReal (a : ℝ) : ℝ ≃ᵐ ℝ where
  toFun x := a + x
  invFun x := x - a
  left_inv := by intro x; ring
  right_inv := by intro x; ring
  measurable_toFun := measurable_const.add measurable_id
  measurable_invFun := measurable_id.sub_const a

lemma shifted_laplace_density (b a : ℝ) :
    (laplace b).map (fun x => a + x) =
      volume.withDensity (fun y => ENNReal.ofReal (laplaceDensity b (y - a))) := by
  change (laplace b).map (shiftReal a) = _
  rw [laplace, map_withDensity_equiv volume (shiftReal a)
    (continuous_laplaceDensity b).measurable.ennreal_ofReal]
  have hm : (volume : Measure ℝ).map (shiftReal a) = volume :=
    (measurePreserving_add_left volume a).map_eq
  rw [hm]
  rfl

lemma shifted_laplace_private {ε a b : ℝ} (hε : 0 < ε) (hab : |a - b| ≤ 1) :
    Indistinguishable ((laplace (1 / ε)).map (fun x => a + x))
      ((laplace (1 / ε)).map (fun x => b + x)) ε 0 := by
  rw [shifted_laplace_density, shifted_laplace_density]
  have hb (c d : ℝ) (hcd : |c - d| ≤ 1) (y : ℝ) :
      laplaceDensity (1 / ε) (y - c) ≤ Real.exp ε * laplaceDensity (1 / ε) (y - d) := by
    apply (laplaceDensity_shift_le (by positivity) c d y).trans
    apply mul_le_mul_of_nonneg_right _ (laplaceDensity_pos (by positivity) _).le
    apply Real.exp_le_exp.mpr
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcd hε.le
  simpa only [Measure.restrict_univ] using restricted_density_private volume
    (fun y => laplaceDensity (1 / ε) (y - a)) (fun y => laplaceDensity (1 / ε) (y - b))
    MeasurableSet.univ ε (fun y _ => ⟨hb a b hab y, hb b a (by rwa [abs_sub_comm]) y⟩)

@[fun_prop] lemma measurable_clipNoisyMass {A : Type*} [MeasurableSpace A]
    {cap M z τ : A → ℝ} (hc : Measurable cap) (hM : Measurable M)
    (hz : Measurable z) (hτ : Measurable τ) :
    Measurable (fun a => clipNoisyMass (cap a) (M a) (z a) (τ a)) := by
  unfold clipNoisyMass
  fun_prop

lemma clipNoisyMass_nonneg (cap M z τ : ℝ) : 0 ≤ clipNoisyMass cap M z τ :=
  le_min (le_max_left _ _) (le_max_left _ _)

lemma clipNoisyMass_le (cap M z τ : ℝ) : clipNoisyMass cap M z τ ≤ max 0 cap :=
  min_le_left _ _

def noisyMassLaw {n : ℕ} (ε τ cap : ℝ) (w : Weights n) : Measure ℝ :=
  (laplace (1 / ε)).map (fun noise => clipNoisyMass cap (mass w) noise τ)

lemma noisyMassLaw_probability {n : ℕ} {ε : ℝ} (hε : 0 < ε) (τ cap : ℝ) (w : Weights n) :
    IsProbabilityMeasure (noisyMassLaw ε τ cap w) := by
  letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / ε)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma noisyMassLaw_private {n : ℕ} {ε : ℝ} (hε : 0 < ε) (τ cap : ℝ)
    {w w' : Weights n} (hw : Adjacent w w') :
    Indistinguishable (noisyMassLaw ε τ cap w) (noisyMassLaw ε τ cap w') ε 0 := by
  have hp := (shifted_laplace_private hε (mass_sensitivity hw)).map
    (show Measurable (fun x : ℝ => min (max 0 cap) (max 0 (x + τ))) by fun_prop)
  have hm : Measurable (fun x : ℝ => min (max 0 cap) (max 0 (x + τ))) := by fun_prop
  rw [Measure.map_map hm (show Measurable (fun x : ℝ => mass w + x) by fun_prop),
    Measure.map_map hm (show Measurable (fun x : ℝ => mass w' + x) by fun_prop)] at hp
  exact hp

end DPCut
