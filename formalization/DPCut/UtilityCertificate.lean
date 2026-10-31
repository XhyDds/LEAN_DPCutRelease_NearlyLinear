import DPCut.Lemma19
import DPCut.Algorithms
import DPCut.EdgeCard

/-! Deterministic SDP and cut certificates needed by Lemma 20. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace DPCut

lemma feasible_logdet_nonpos {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) : Real.log X.det ≤ 0 := by
  have hp := feasible_posDef hn hX
  rw [hp.1.det_eq_prod_eigenvalues]
  change Real.log (∏ i, hp.1.eigenvalues i) ≤ 0
  rw [Real.log_prod _ _ (fun i _ => (hp.eigenvalues_pos i).ne')]
  have ht : (∑ i, hp.1.eigenvalues i) = (n : ℝ) := by
    have ht0 := hp.1.trace_eq_sum_eigenvalues
    change X.trace = ∑ i, hp.1.eigenvalues i at ht0
    rw [← ht0]
    simp [Matrix.trace, hX.2.1]
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hp.eigenvalues_pos i))
  simpa [Finset.sum_sub_distrib, ht] using hb

lemma optimum_le_optimizer_score {n : ℕ} (hn : 2 ≤ n) {lam : ℝ}
    (hlam : 0 ≤ lam) (D : Weights n) :
    optimum lam D ≤ pairing D (fractionalQuery (optimizer lam D)) := by
  rw [optimum_eq_objective_optimizer hn, objective]
  have := mul_nonpos_of_nonneg_of_nonpos hlam
    (feasible_logdet_nonpos hn (optimizer_isOptimizer hn lam D).1)
  linarith

lemma pairing_add_right {n : ℕ} (v a b : Weights n) :
    pairing v (a + b) = pairing v a + pairing v b := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

lemma pairing_plus_discrepancy {n : ℕ} (γ : ℝ) (w h r : Weights n) :
    mass (plusDiscrepancy γ w h r) = pairing h r - (1 + γ) * pairing w r := by
  simp only [mass, plusDiscrepancy, pairing, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma cut_plus_discrepancy {n : ℕ} (γ : ℝ) (w h r : Weights n) (S : Finset (Fin n)) :
    cut (plusDiscrepancy γ w h r) S =
      cut (hadamard h r) S - (1 + γ) * cut (hadamard w r) S := by
  simp only [cut, pairing, plusDiscrepancy, hadamard, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma cut_minus_discrepancy {n : ℕ} (γ : ℝ) (w h r : Weights n) (S : Finset (Fin n)) :
    cut (minusDiscrepancy γ w h r) S =
      (1 - γ) * cut (hadamard w r) S - cut (hadamard h r) S := by
  simp only [cut, pairing, minusDiscrepancy, hadamard, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma masked_mass_le {n : ℕ} {U : ℝ} (hU : 0 ≤ U) {w r : Weights n}
    (hw : Bounded U w) (hr : IsMask r) : pairing w r ≤ (n : ℝ) ^ 2 * U := by
  calc
    _ ≤ ∑ _ : Edge n, U := Finset.sum_le_sum fun e _ =>
      (mul_le_of_le_one_right (hw e).1 (hr e).2).trans (hw e).2
    _ = (Fintype.card (Edge n) : ℝ) * U := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (edge_card_le_square n) hU

lemma discrepancy_l1_le {n : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {w h r : Weights n} (hw : Nonnegative w) (hh : Nonnegative h) (hr : IsMask r) :
    l1 (plusDiscrepancy γ w h r) ≤ pairing h r + (1 + γ) * pairing w r ∧
    l1 (minusDiscrepancy γ w h r) ≤ pairing h r + (1 + γ) * pairing w r := by
  have hp (e : Edge n) : |r e * (h e - (1 + γ) * w e)| ≤
      h e * r e + (1 + γ) * (w e * r e) := by
    rw [abs_mul, abs_of_nonneg (hr e).1]
    have ha := abs_sub (h e) ((1 + γ) * w e)
    rw [abs_of_nonneg (hh e), abs_of_nonneg (mul_nonneg (by linarith) (hw e))] at ha
    nlinarith [mul_le_mul_of_nonneg_left ha (hr e).1]
  have hm (e : Edge n) : |r e * ((1 - γ) * w e - h e)| ≤
      h e * r e + (1 + γ) * (w e * r e) := by
    rw [abs_mul, abs_of_nonneg (hr e).1]
    have ha := abs_sub ((1 - γ) * w e) (h e)
    rw [abs_of_nonneg (mul_nonneg (by linarith) (hw e)), abs_of_nonneg (hh e)] at ha
    have hb := mul_le_mul_of_nonneg_left ha (hr e).1
    nlinarith [mul_nonneg hγ (mul_nonneg (hw e) (hr e).1)]
  constructor
  · simpa [l1, plusDiscrepancy, pairing, Finset.sum_add_distrib, Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  · simpa [l1, minusDiscrepancy, pairing, Finset.sum_add_distrib, Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun e _ => hm e)

/-- Both failed-oracle SDP bounds imply the common cut error, with constant 16. -/
theorem residual_cut_certificate {n : ℕ} (hn : 2 ≤ n) {U γ lam τ : ℝ}
    (hU : 0 ≤ U) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hlam : 0 ≤ lam) (hτ : 0 ≤ τ)
    {w h r : Weights n} (hw : Bounded U w) (hh : Nonnegative h) (hr : IsMask r)
    (hp : optimum lam (plusDiscrepancy γ w h r) ≤ 4 * τ)
    (hm : optimum lam (minusDiscrepancy γ w h r) ≤ 4 * τ) :
    AllCuts (hadamard w r) (hadamard h r) γ
      (16 * (τ + lam * n * Real.log n + n * U)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hw0 : 0 ≤ pairing w r := Finset.sum_nonneg fun e _ => mul_nonneg (hw e).1 (hr e).1
  have hmass := mass_le_twice_optimum hn lam (plusDiscrepancy γ w h r)
  rw [pairing_plus_discrepancy] at hmass
  have hwm := masked_mass_le hU hw hr
  have hnorm := discrepancy_l1_le hγ hγ1 (fun e => (hw e).1) hh hr
  have hb : pairing h r + (1 + γ) * pairing w r ≤ 8 * τ + 4 * n ^ 2 * U := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) hw0]
  have hlog : 0 ≤ lam * n * Real.log n := by positivity
  have hnu : 0 ≤ (n : ℝ) * U := by positivity
  have hbound (D : Weights n) (hF : optimum lam D ≤ 4 * τ)
      (hD : l1 D ≤ 8 * τ + 4 * n ^ 2 * U) (S : Finset (Fin n)) :
      cut D S ≤ 16 * (τ + lam * n * Real.log n + n * U) := by
    have hc := sdp_cut_bound hn hlam D S
    have hmax : max (optimum lam D) 0 ≤ 4 * τ := max_le hF (by positivity)
    have hd : l1 D / n ≤ 4 * τ + 4 * n * U := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith [mul_nonneg hτ (show 0 ≤ (n : ℝ) - 2 by linarith)]
    nlinarith
  intro S
  have hpS := hbound _ hp (hnorm.1.trans hb) S
  have hmS := hbound _ hm (hnorm.2.trans hb) S
  rw [cut_plus_discrepancy] at hpS
  rw [cut_minus_discrepancy] at hmS
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end DPCut
