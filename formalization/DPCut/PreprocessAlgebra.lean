import DPCut.CutBasics

/-! Clipping and the deterministic good-noise argument for Lemma 12. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DPCut

lemma clipWeights_bounded {n : ℕ} {U : ℝ} (hU : 0 ≤ U) {w : Weights n}
    (hw : Nonnegative w) : Bounded U (clipWeights U w) :=
  fun e => ⟨le_min (hw e) hU, min_le_right _ _⟩

lemma clipWeights_add_excess {n : ℕ} (U : ℝ) (w : Weights n) :
    clipWeights U w + excess U w = w := by
  funext e
  change min (w e) U + max (w e - U) 0 = w e
  rcases le_total (w e) U with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]; ring

lemma excess_nonnegative {n : ℕ} (U : ℝ) (w : Weights n) : Nonnegative (excess U w) :=
  fun _ => le_max_right _ _

lemma Adjacent.excess {n : ℕ} {w w' : Weights n} (h : Adjacent w w') (U : ℝ) :
    Adjacent (excess U w) (excess U w') := by
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro e _
  simpa [excess] using abs_max_sub_max_le_abs (w e - U) (w' e - U) 0

@[fun_prop] lemma measurable_noisyExcess {n : ℕ} (U V : ℝ) (w : Weights n) :
    Measurable (noisyExcess U V w) := by unfold noisyExcess; fun_prop

lemma noisyExcess_nonnegative {n : ℕ} (U V : ℝ) (w z : Weights n) :
    Nonnegative (noisyExcess U V w z) := fun _ => le_max_left _ _

lemma clipThreshold_eq {n : ℕ} (ε β γ : ℝ) :
    clipThreshold n ε β γ = 4 * noiseShift n ε β / γ := by
  unfold clipThreshold noiseShift
  ring

lemma noiseShift_pos {n : ℕ} (hn : 2 ≤ n) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) : 0 < noiseShift n ε β := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold noiseShift
  exact mul_pos (div_pos (by norm_num) hε)
    (Real.log_pos ((lt_div_iff₀ hβ).mpr (by linarith)))

lemma clipThreshold_pos {n : ℕ} (hn : 2 ≤ n) {ε β γ : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) :
    0 < clipThreshold n ε β γ := by
  rw [clipThreshold_eq]
  exact div_pos (mul_pos (by norm_num) (noiseShift_pos hn hε hβ hβ1)) hγ

lemma noisyExcess_coordinate_error {n : ℕ} {U V γ : ℝ}
    (hγ : 0 < γ) (hUV : U = 4 * V / γ) {w z : Weights n}
    (hw : Nonnegative w) (hz : ∀ e, |z e| ≤ V) (e : Edge n) :
    |w e - (noisyExcess U V w z + clipWeights U w) e| ≤ γ / 2 * w e := by
  have hze := abs_le.mp (hz e)
  have hV : 0 ≤ V := (abs_nonneg (z e)).trans (hz e)
  have hid := congrFun (clipWeights_add_excess U w) e
  simp only [Pi.add_apply] at hid ⊢
  have hv := excess_nonnegative U w e
  have hy : 0 ≤ noisyExcess U V w z e := noisyExcess_nonnegative U V w z e
  have hyv : noisyExcess U V w z e ≤ excess U w e := by
    exact max_le hv (by linarith [hze.2])
  have hlow : excess U w e - 2 * V ≤ noisyExcess U V w z e := by
    exact (by linarith [hze.1] : excess U w e - 2 * V ≤ excess U w e + z e - V).trans
      (le_max_right _ _)
  rw [abs_of_nonneg (by linarith)]
  by_cases he : excess U w e = 0
  · have : noisyExcess U V w z e = 0 := le_antisymm (by simpa [he] using hyv) hy
    rw [this]
    have : w e = clipWeights U w e := by linarith
    rw [this, zero_add, sub_self]
    exact mul_nonneg (by positivity) (by rw [← this]; exact hw e)
  · have hUw : U < w e := by
      have : 0 < excess U w e := lt_of_le_of_ne hv (Ne.symm he)
      have : 0 < w e - U := (lt_max_iff.mp this).resolve_right (lt_irrefl 0)
      linarith
    have hUγ : U * γ = 4 * V := by rw [hUV]; field_simp
    have hmul := mul_le_mul_of_nonneg_right hUw.le hγ.le
    nlinarith

lemma allCuts_of_coordinate_error {n : ℕ} {w h : Weights n} {γ : ℝ}
    (he : ∀ e, |w e - h e| ≤ γ * w e) : AllCuts w h γ 0 := by
  intro S
  rw [← cut_sub]
  calc
    |cut (w - h) S| ≤ ∑ e, |(w e - h e) * cutQuery S e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, γ * (w e * cutQuery S e) := by
      apply Finset.sum_le_sum
      intro e _
      unfold cutQuery
      split
      · simp
      · simpa using he e
    _ = γ * cut w S + 0 := by simp [cut, pairing, Finset.mul_sum]

lemma noisyExcess_allCuts {n : ℕ} {U V γ : ℝ} (hγ : 0 < γ)
    (hUV : U = 4 * V / γ) {w z : Weights n} (hw : Nonnegative w)
    (hz : ∀ e, |z e| ≤ V) :
    AllCuts w (noisyExcess U V w z + clipWeights U w) (γ / 2) 0 :=
  allCuts_of_coordinate_error (noisyExcess_coordinate_error hγ hUV hw hz)

end DPCut
