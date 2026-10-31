import DPCut.MassEstimateUtility
import DPCut.NoisyMassPrivacy

/-! Public mass clipping is inactive on the existing utility good event and
provides a deterministic bound for the numerical optimization instances. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace DPCut

lemma clipNoisyMass_le_cap {cap : ℝ} (hcap : 0 ≤ cap) (M z τ : ℝ) :
    clipNoisyMass cap M z τ ≤ cap := by
  simpa [max_eq_right hcap] using clipNoisyMass_le cap M z τ

/-- The mass bound holds even for the totalized zero-denominator branch. -/
lemma initialEstimate_mass_le {n : ℕ} {H : ℝ} (hH : 0 ≤ H) (a : Weights n) :
    mass (initialEstimate H a) ≤ H := by
  simp only [mass, initialEstimate, ← Finset.sum_div, ← Finset.mul_sum]
  by_cases ha : (∑ e, a e) = 0
  · simpa [ha] using hH
  · simp [ha]

/-- Every update has mass at most its fixed public mass parameter, regardless
of the score vector. A zero normalizer produces mass zero. -/
lemma mwUpdate_mass_le {n : ℕ} {H : ℝ} (hH : 0 ≤ H)
    (θ η : ℝ) (h g : Weights n) : mass (mwUpdate H θ η h g) ≤ H := by
  simp only [mass, mwUpdate, ← Finset.sum_div, ← Finset.mul_sum]
  by_cases hZ : (∑ e, h e * Real.exp (-(θ * η * g e))) = 0
  · simpa [hZ] using hH
  · simp [hZ]

lemma masked_mass_le_public_bound {n : ℕ} {U : ℝ} {w a : Weights n}
    (hw : Bounded U w) (ha : IsMask a) :
    mass (hadamard a w) ≤ Fintype.card (Edge n) * U := by
  calc
    _ ≤ ∑ _e : Edge n, U := Finset.sum_le_sum fun e _ =>
      (mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2
    _ = _ := by simp

lemma clipNoisyMass_eq_on_good {cap M z τ : ℝ} (hM : 0 ≤ M)
    (hcap : M + 2 * τ ≤ cap) (hz : z ∈ Icc (-τ) τ) :
    clipNoisyMass cap M z τ = max 0 (M + z + τ) := by
  exact min_eq_right ((shifted_mass_bounds hM hz).2.trans (hcap.trans (le_max_right _ _)))

lemma clipped_mass_bounds {cap M z τ : ℝ} (hM : 0 ≤ M)
    (hcap : M + 2 * τ ≤ cap) (hz : z ∈ Icc (-τ) τ) :
    M ≤ clipNoisyMass cap M z τ ∧ clipNoisyMass cap M z τ ≤ M + 2 * τ := by
  rw [clipNoisyMass_eq_on_good hM hcap hz]
  exact shifted_mass_bounds hM hz

lemma plusDiscrepancy_l1_le {n : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    {w h r : Weights n} (hw : Nonnegative w) (hh : Nonnegative h) (hr : IsMask r) :
    l1 (plusDiscrepancy γ w h r) ≤ mass h + (1 + γ) * mass w := by
  calc
    _ ≤ ∑ e, (h e + (1 + γ) * w e) := by
      apply Finset.sum_le_sum
      intro e _
      change |r e * (h e - (1 + γ) * w e)| ≤ _
      rw [abs_mul, abs_of_nonneg (hr e).1]
      have hab : |h e - (1 + γ) * w e| ≤ h e + (1 + γ) * w e := by
        apply abs_le.mpr
        constructor <;> nlinarith [hw e, hh e, mul_nonneg hγ (hw e)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hr e).2).trans hab
    _ = _ := by simp [mass, Finset.sum_add_distrib, Finset.mul_sum]

lemma minusDiscrepancy_l1_le {n : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    {w h r : Weights n} (hw : Nonnegative w) (hh : Nonnegative h) (hr : IsMask r) :
    l1 (minusDiscrepancy γ w h r) ≤ mass h + (1 + γ) * mass w := by
  calc
    _ ≤ ∑ e, (h e + (1 + γ) * w e) := by
      apply Finset.sum_le_sum
      intro e _
      change |r e * ((1 - γ) * w e - h e)| ≤ _
      rw [abs_mul, abs_of_nonneg (hr e).1]
      have hab : |(1 - γ) * w e - h e| ≤ h e + (1 + γ) * w e := by
        apply abs_le.mpr
        constructor <;> nlinarith [hw e, hh e, mul_nonneg hγ (hw e)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hr e).2).trans hab
    _ = _ := by simp [mass, Finset.sum_add_distrib, Finset.mul_sum]

theorem clipped_discrepancy_bound {n : ℕ} {U γ τ : ℝ}
    (hγ : 0 ≤ γ) {w h r : Weights n}
    (hw : Bounded U w) (hh : Nonnegative h) (hr : IsMask r)
    (hcap : mass h ≤ Fintype.card (Edge n) * U + 2 * τ) :
    l1 (plusDiscrepancy γ w h r) ≤ (2 + γ) * Fintype.card (Edge n) * U + 2 * τ ∧
    l1 (minusDiscrepancy γ w h r) ≤ (2 + γ) * Fintype.card (Edge n) * U + 2 * τ := by
  have hw0 : Nonnegative w := fun e => (hw e).1
  have hm : mass w ≤ Fintype.card (Edge n) * U := by
    calc
      _ ≤ ∑ _e : Edge n, U := Finset.sum_le_sum fun e _ => (hw e).2
      _ = _ := by simp
  have hp := plusDiscrepancy_l1_le hγ hw0 hh hr
  have hn := minusDiscrepancy_l1_le hγ hw0 hh hr
  have hb := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 1 + γ)
  constructor <;> nlinarith

end DPCut
