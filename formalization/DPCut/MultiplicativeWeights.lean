import DPCut.FiniteKL
import DPCut.InnerLoopMeasurable

/-! Normalization, support, and exact KL decrease for multiplicative weights. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DPCut

def EstimateValid {n : ℕ} (w : Weights n) (H : ℝ) (h : Weights n) : Prop :=
  Nonnegative h ∧ mass h = H ∧ ∀ e, 0 < w e → 0 < h e

def mwNormalizer {n : ℕ} (θ η : ℝ) (h g : Weights n) : ℝ :=
  ∑ e, h e * Real.exp (-θ * η * g e)

lemma mwNormalizer_pos {n : ℕ} {h g : Weights n} {H : ℝ}
    (hh : Nonnegative h) (hm : mass h = H) (hH : 0 < H) (θ η : ℝ) :
    0 < mwNormalizer θ η h g := by
  have hmpos : 0 < ∑ e, h e := by change 0 < mass h; rwa [hm]
  obtain ⟨e, he, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun e _ => hh e)).mp hmpos
  exact Finset.sum_pos' (fun e _ => mul_nonneg (hh e) (Real.exp_pos _).le)
    ⟨e, he, mul_pos hp (Real.exp_pos _)⟩

lemma EstimateValid.update {n : ℕ} {w h g : Weights n} {H : ℝ}
    (hh : EstimateValid w H h) (hH : 0 < H) (θ η : ℝ) :
    EstimateValid w H (mwUpdate H θ η h g) := by
  have hZ := mwNormalizer_pos hh.1 hh.2.1 hH θ η (g := g)
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact div_nonneg (mul_nonneg hH.le (mul_nonneg (hh.1 e) (Real.exp_pos _).le)) hZ.le
  · change (∑ e, H * (h e * Real.exp (-θ * η * g e)) / mwNormalizer θ η h g) = H
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change H * mwNormalizer θ η h g / mwNormalizer θ η h g = H
    exact mul_div_cancel_right₀ _ hZ.ne'
  · intro e he
    exact div_pos (mul_pos hH (mul_pos (hh.2.2 e he) (Real.exp_pos _))) hZ

lemma pairing_normalized_difference {n : ℕ} (w h g : Weights n) (M H : ℝ) :
    pairing (fun e => h e / H - w e / M) g = pairing h g / H - pairing w g / M := by
  simp only [pairing, sub_mul, div_mul_eq_mul_div, Finset.sum_sub_distrib, Finset.sum_div]

lemma mw_potential_difference {n : ℕ} {w h g : Weights n} {M H : ℝ}
    (hw : Nonnegative w) (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M)
    (hh : EstimateValid w H h) (θ η : ℝ) :
    potential w h M H - potential w (mwUpdate H θ η h g) M H =
      -θ * η * pairing w g - M * Real.log (mwNormalizer θ η h g / H) := by
  have hZ := mwNormalizer_pos hh.1 hh.2.1 hH θ η (g := g)
  have hh' := hh.update hH θ η (g := g)
  rw [(normalizedKL_finite_formula hw hh.1 hM hH hmw hh.2.1 hh.2.2).2,
    (normalizedKL_finite_formula hw hh'.1 hM hH hmw hh'.2.1 hh'.2.2).2,
    ← Finset.sum_sub_distrib]
  have he (e : Edge n) : w e * Real.log ((w e / M) / (h e / H)) -
      w e * Real.log ((w e / M) / (mwUpdate H θ η h g e / H)) =
      -θ * η * (w e * g e) - w e * Real.log (mwNormalizer θ η h g / H) := by
    by_cases hz : w e = 0
    · simp [hz]
    · have hwpos := lt_of_le_of_ne (hw e) (Ne.symm hz)
      have hhe := hh.2.2 e hwpos
      have hup : mwUpdate H θ η h g e = H * (h e * Real.exp (-θ * η * g e)) /
          mwNormalizer θ η h g := rfl
      rw [hup]
      simp [Real.log_div, Real.log_mul, hz, hM.ne', hH.ne', hhe.ne', hZ.ne']
      ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show ∑ e, w e = M from hmw]
  rfl

lemma mw_logNormalizer_le {n : ℕ} {h g : Weights n} {H η θ : ℝ}
    (hh : Nonnegative h) (hm : mass h = H) (hH : 0 < H) (hg : IsMask g)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hθ : θ = 1 ∨ θ = -1) :
    Real.log (mwNormalizer θ η h g / H) ≤ -θ * η * (pairing h g / H) + η ^ 2 := by
  have hZ := mwNormalizer_pos hh hm hH θ η (g := g)
  have hpoint (e : Edge n) : Real.exp (-θ * η * g e) ≤ 1 - θ * η * g e + η ^ 2 := by
    have ha : |-θ * η * g e| ≤ η := by
      rcases hθ with rfl | rfl <;> simp [abs_mul, abs_of_nonneg hη, abs_of_nonneg (hg e).1] <;>
        nlinarith [(hg e).2]
    have hb := Real.abs_exp_sub_one_sub_id_le (ha.trans hη1)
    have hc : (-θ * η * g e) ^ 2 ≤ η ^ 2 := by
      have hc := (sq_le_sq₀ (abs_nonneg (-θ * η * g e)) hη).mpr ha
      simpa only [sq_abs] using hc
    nlinarith [le_abs_self (Real.exp (-θ * η * g e) - 1 - (-θ * η * g e))]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => mul_le_mul_of_nonneg_left (hpoint e) (hh e))
  have heq : (∑ e, h e * (1 - θ * η * g e + η ^ 2)) =
      H - θ * η * pairing h g + H * η ^ 2 := by
    simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, show ∑ e, h e = H from hm]
    congr 2
    simp only [pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq] at hs
  have hlog := Real.log_le_sub_one_of_pos (div_pos hZ hH)
  have hd : mwNormalizer θ η h g / H ≤ 1 - θ * η * (pairing h g / H) + η ^ 2 := by
    apply (div_le_iff₀ hH).mpr
    convert hs using 1
    field_simp
  linarith

theorem mw_potential_progress : MWProgressStatement := by
  intro n w h g M H γ θ hw hh hg hM hH hmw hmh hs hγ hγ1 hθ hgap
  have hv : EstimateValid w H h := ⟨hh, hmh, hs⟩
  let η := stepSize γ
  have hη : 0 < η := by dsimp [η, stepSize]; positivity
  have hη1 : η ≤ 1 := by
    change γ / (8 * (1 + γ)) ≤ 1
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [mw_potential_difference hw hM hH hmw hv θ η]
  have hl := mw_logNormalizer_le hh hmh hH hg hη.le hη1 hθ
  have hl' := mul_le_mul_of_nonneg_left hl hM.le
  rw [pairing_normalized_difference] at hgap
  have hg' := mul_le_mul_of_nonneg_left hgap (mul_nonneg hη.le hM.le)
  have heq : η * M * (γ / (4 * (1 + γ))) - M * η ^ 2 = γ ^ 2 * M / (64 * (1 + γ) ^ 2) := by
    dsimp [η, stepSize]
    field_simp
    ring
  rw [← heq]
  have hid : η * M * (θ * (pairing h g / H - pairing w g / M)) =
      M * (θ * η * (pairing h g / H)) - θ * η * pairing w g := by
    field_simp
  rw [hid] at hg'
  nlinarith only [hl', hg']

end DPCut
