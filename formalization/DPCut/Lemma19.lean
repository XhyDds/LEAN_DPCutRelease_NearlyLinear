import DPCut.ShrunkenCut

/-!
Lemma 19 (`lem:sdp_error`). The asymptotic error is made
explicit with universal constant 2, for arbitrary signed edge weights.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace DPCut

lemma objective_le_optimum {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n)
    {X : Mat n} (hX : X ∈ feasible n) : objective lam D X ≤ optimum lam D := by
  rw [optimum_eq_objective_optimizer hn]
  exact (optimizer_isOptimizer hn lam D).2 X hX

@[simp] lemma fractionalQuery_one {n : ℕ} (e : Edge n) :
    fractionalQuery (1 : Mat n) e = 1 / 2 := by
  simp [fractionalQuery, Matrix.one_apply_ne (ne_of_lt e.property)]

lemma objective_one {n : ℕ} (lam : ℝ) (D : Weights n) :
    objective lam D (1 : Mat n) = mass D / 2 := by
  simp [objective, pairing, mass, Finset.sum_mul, div_eq_mul_inv]

/-- The identity-matrix test yields the second conclusion, even for signed weights. -/
theorem mass_le_twice_optimum {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) (D : Weights n) :
    mass D ≤ 2 * optimum lam D := by
  have h := objective_le_optimum hn lam D (feasible_one hn)
  rw [objective_one] at h
  linarith

lemma abs_mass_le_l1 {n : ℕ} (D : Weights n) : |mass D| ≤ l1 D :=
  Finset.abs_sum_le_sum_abs D Finset.univ

lemma l1_nonneg {n : ℕ} (D : Weights n) : 0 ≤ l1 D :=
  Finset.sum_nonneg fun e _ => abs_nonneg (D e)

/-- The exact separation inequality before bounding the determinant penalty. -/
theorem shrunken_cut_certificate {n : ℕ} (hn : 2 ≤ n) (lam : ℝ)
    (D : Weights n) (S : Finset (Fin n)) :
    (1 - 1 / (n : ℝ)) * cut D S ≤ optimum lam D +
      lam * ((n - 1 : ℝ) * Real.log n - Real.log (n - 1 + 1 / (n : ℝ))) -
      mass D / (2 * n) := by
  have h := objective_le_optimum hn lam D (shrunkenCut_feasible hn S)
  rw [objective, pairing_shrunkenCut, shrunkenCut_logdet hn S] at h
  nlinarith

theorem lemma19_shrunken : ShrunkenCutCertificateStatement := by
  intro n hn lam _ D S
  exact ⟨shrunkenCut_feasible hn S, shrunken_cut_certificate hn lam D S⟩

/-- A sharper explicit cut bound than the common-constant form of Lemma 19. -/
theorem sdp_cut_bound {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam)
    (D : Weights n) (S : Finset (Fin n)) :
    cut D S ≤ 2 * max (optimum lam D) 0 +
      2 * lam * n * Real.log n + l1 D / n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn := Real.log_natCast_nonneg n
  have hl1 := l1_nonneg D
  have hF : 0 ≤ max (optimum lam D) 0 := le_max_right _ _
  have hF' : optimum lam D ≤ max (optimum lam D) 0 := le_max_left _ _
  have hdet := (shrunkenCut_neg_logdet_bounds hn S).2
  rw [shrunkenCut_logdet hn S] at hdet
  have hpenalty := mul_le_mul_of_nonneg_left hdet hlam
  have hmass : -mass D ≤ l1 D := (neg_le_abs _).trans (abs_mass_le_l1 D)
  have hmass' := div_le_div_of_nonneg_right hmass (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hcert := shrunken_cut_certificate hn lam D S
  have hhalf : l1 D / (2 * n) = (l1 D / n) / 2 := by ring
  have hbound : (1 - 1 / (n : ℝ)) * cut D S ≤
      max (optimum lam D) 0 + lam * n * Real.log n + (l1 D / n) / 2 := by
    rw [hhalf, neg_div] at hmass'
    nlinarith
  have hcoef : 1 / 2 ≤ 1 - 1 / (n : ℝ) := by
    have hi : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnR
    linarith
  by_cases hcut : 0 ≤ cut D S
  · nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hcut]
  · exact (le_of_not_ge hcut).trans (by positivity)

/-- Lemma 19, with the universal choice `C = 2`. -/
theorem lemma19 : SDPCertificateStatement := by
  refine ⟨2, by norm_num, ?_⟩
  intro n hn lam hlam D
  refine ⟨?_, mass_le_twice_optimum hn lam D⟩
  intro S
  have h := sdp_cut_bound hn hlam.le D S
  have hl : 0 ≤ l1 D / (n : ℝ) := div_nonneg (l1_nonneg D) (Nat.cast_nonneg n)
  nlinarith

end DPCut
